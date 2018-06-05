#include <utility>
#include "cell_tracking.h"
#include "visitors/standard_visitor.hxx"
#include "LP_external_interface.hxx"
#include "gurobi_interface.hxx"

namespace LP_MP {

template<typename CHECK> struct get_type;

template<class T>
std::string demangled_name(T &object)
{
  int status;
  char *demangled = abi::__cxa_demangle(typeid(object).name(), 0, 0, &status);
  if (status != 0)
    throw std::runtime_error("Demangling failed.");
  std::string result(demangled);
  free(demangled);
  return result;
}

template<typename ITERATOR>
struct print_iterator_helper
{
  print_iterator_helper(ITERATOR begin, ITERATOR end)
  : begin(begin)
  , end(end)
  { }

  ITERATOR begin;
  ITERATOR end;
};

template<typename ITERATOR>
print_iterator_helper<ITERATOR> print_iterator(ITERATOR begin, ITERATOR end)
{
  return print_iterator_helper<ITERATOR>(begin, end);
}

template<typename ITERATOR>
std::ostream& operator<<(std::ostream& o, const print_iterator_helper<ITERATOR> &pi)
{
  bool first = true;
  o << "[";
  for (ITERATOR it = pi.begin; it != pi.end; ++it) {
    if (!first)
      o << ", ";
    o << *it;
    first = false;
  }
  o << "]";
  return o;
}

template<typename CONTAINER>
auto print_container(const CONTAINER& c)
{
  return print_iterator(c.begin(), c.end());
}

class binary_factor : public std::array<REAL, 2> {
public:
  binary_factor(REAL cost_on = 0, REAL cost_off = 0)
  : primal_()
  {
    (*this)[0] = cost_off;
    (*this)[1] = cost_on;
    // TODO: init_primal()?
  }

  REAL LowerBound() const
  {
    return *std::min_element(begin(), end());
  }

  REAL EvaluatePrimal() const
  {
    if (primal_ >= size()) {
      return std::numeric_limits<REAL>::infinity();
    } else {
      return (*this)[primal_];
    }
  }

  void init_primal()
  {
    primal_ = std::numeric_limits<INDEX>::max();
  }

  void MaximizePotentialAndComputePrimal()
  {
    if (primal_ >= size())
      primal_ = std::min_element(this->begin(), this->end()) - this->begin();
  }

  auto export_variables() { return std::tie(*static_cast<std::array<REAL, 2>*>(this)); }

  template<typename SOLVER>
  void construct_constraints(SOLVER& solver, typename SOLVER::vector vars) const
  {
    solver.add_simplex_constraint(vars.begin(), vars.end());
  }

  template<typename SOLVER>
  void convert_primal(SOLVER& s, typename SOLVER::vector vars)
  {
    assert(s.solution(vars[0]) != s.solution(vars[1]));
    primal_ = s.first_active(vars);
  }

  template<typename ARCHIVE>
  void serialize_primal(ARCHIVE& ar) { ar(primal_); }

  template<typename ARCHIVE>
  void serialize_dual(ARCHIVE& ar) { ar(*static_cast<std::array<REAL, 2>*>(this)); };

  INDEX primal() const { return primal_; }

private:
  INDEX primal_;
};

class exactly_one_factor {
public:
  exactly_one_factor(INDEX no_binaries)
  : no_binaries_(no_binaries)
  , duals_(no_binaries * 2)
  { }

  REAL LowerBound() const
  {
    return std::get<1>(compute_min());
  }

  REAL EvaluatePrimal() const
  {
    if (primal_ >= no_binaries_)
      return std::numeric_limits<REAL>::infinity();
    else
      return compute(primal_);
  }

  void init_primal()
  {
    primal_ = std::numeric_limits<INDEX>::max();
  }

  void MaximizePotentialAndComputePrimal()
  {
    if (primal_ >= no_binaries_) {
      primal_ = std::get<0>(compute_min());
    }
  }

  auto export_variables() { return std::tie(duals_); }

  template<typename SOLVER>
  void construct_constraints(SOLVER& solver, typename SOLVER::vector vars) const
  {
    assert(duals_.size() == vars.size());

    for (auto it = vars.begin(); it != vars.end(); ++it, ++it)
      solver.add_simplex_constraint(it, it+2);

    std::vector<typename SOLVER::variable> ons(no_binaries_);
    for (INDEX i = 0; i < no_binaries_; ++i)
      ons[i] = vars[dual_idx(i, true)];
    solver.add_simplex_constraint(ons.begin(), ons.end());
  }

  template<typename SOLVER>
  void convert_primal(SOLVER& s, typename SOLVER::vector vars)
  {
    init_primal();
    for (INDEX i = 0; i < no_binaries_; ++i)
      if (s.solution(vars[dual_idx(i, true)]))
        primal_ = i;

#ifndef NDEBUG
    for (INDEX i = 0; i < no_binaries_; ++i) {
      assert(s.solution(vars[dual_idx(i, primal_ == i)]));
      assert(!s.solution(vars[dual_idx(i, primal_ != i)]));
    }
#endif
  }

  template<typename ARCHIVE>
  void serialize_primal(ARCHIVE& ar) { ar(primal_); }

  template<typename ARCHIVE>
  void serialize_dual(ARCHIVE& ar) { ar(duals_); };

  INDEX primal() const { return primal_; }
  const REAL& dual(INDEX binary, bool flag) const { return duals_[dual_idx(binary, flag)]; }

//protected:
  INDEX dual_idx(INDEX binary, bool flag) const
  {
    assert(binary >= 0); assert(binary < no_binaries_);
    return binary * 2 + (flag ? 1 : 0);
  }

  REAL& dual(INDEX binary, bool flag) { return duals_[dual_idx(binary, flag)]; }

  REAL compute(INDEX on) const
  {
    assert(on >= 0); assert(on < no_binaries_);
    REAL sum = 0;
    for (INDEX i = 0; i < no_binaries_; ++i)
      sum += dual(i, i == on);
    return sum;
  }

  std::tuple<INDEX, REAL> compute_min() const
  {
    INDEX argmin = std::numeric_limits<INDEX>::max();
    REAL min = std::numeric_limits<REAL>::infinity();
    for (INDEX on = 0; on < no_binaries_; ++on) {
      REAL current = compute(on);
      if (current < min) {
        min = current;
        argmin = on;
      }
    }
    assert(argmin >= 0 && argmin < no_binaries_);
    return std::make_tuple(argmin, min);
  }

  INDEX no_binaries_;
  INDEX primal_;
  vector<REAL> duals_;

  friend class exactly_one_message;
};

class exactly_one_minorant_factor : public exactly_one_factor {
public:
  exactly_one_minorant_factor(INDEX no_binaries)
  : exactly_one_factor(no_binaries)
  , indicator_(no_binaries * 2)
  , minorant_(no_binaries * 2)
  , tmp_(no_binaries_ * 2)
  { }

  void MaximizePotential()
  {
    // This method computes the maximal minorant. FIXME: It implements a rather
    // generic scheme and could possibly be optimized for this very specific
    // case of binary variables with simplex constraint. For example, we know
    // the number of iterations beforehand, because we basically just try out
    // very specific configurations.

    for (INDEX i = 0; i < no_binaries_ * 2; ++i) {
      indicator_[i] = 1;
      minorant_[i] = 0;
      tmp_[i] = duals_[i];
    }

    for (int iteration = 0; std::find(indicator_.begin(), indicator_.end(), 1) != indicator_.end(); ++iteration) {
      INDEX argmin = std::numeric_limits<INDEX>::max();
      REAL min = std::numeric_limits<REAL>::infinity();
      for (INDEX i = 0; i < no_binaries_; ++i) {
        if (indicator_[dual_idx(i, true)]) {
          REAL current = 0;
          for (INDEX j = 0; j < no_binaries_; ++j)
            current += tmp_[dual_idx(j, i == j)];
          if (current < min) {
            min = current;
            argmin = i;
          }
        }
      }

      INDEX h_x = 0;
      for (INDEX i = 0; i < no_binaries_; ++i)
        if (indicator_[dual_idx(i, i == argmin)])
          ++h_x;

      REAL epsilon = min / h_x;

      if (debug())
        std::cout << "[MINORANT] iteration = " << iteration << "  ->  argmin = " << argmin << " / h_x = " << h_x << " / epsilon = " << epsilon << std::endl;

      for (INDEX i = 0; i < no_binaries_ * 2; ++i) {
        minorant_[i] += epsilon * indicator_[i];
        tmp_[i]      -= epsilon * indicator_[i];
      }

      for (INDEX i = 0; i < no_binaries_; ++i)
        indicator_[dual_idx(i, i == argmin)] = 0;

      if (debug()) {
        std::cout << "indicator_ = [";
        for (INDEX i = 0; i < no_binaries_ * 2; ++i)
          std::cout << " " << indicator_[i];
        std::cout << " ];" << std::endl;

        std::cout << "tmp_ = [";
        for (INDEX i = 0; i < no_binaries_ * 2; ++i)
          std::cout << " " << tmp_[i];
        std::cout << " ];" << std::endl;

        std::cout << "minorant_ = [";
        for (INDEX i = 0; i < no_binaries_ * 2; ++i)
          std::cout << " " << minorant_[i];
        std::cout << " ];" << std::endl;
      }
    }
  }

  void MaximizePotentialAndComputePrimal()
  {
    MaximizePotential();
    exactly_one_factor::MaximizePotentialAndComputePrimal();
  }

  const REAL& minorant(INDEX binary, bool flag) const { return minorant_[dual_idx(binary, flag)]; }

protected:
  REAL& minorant(INDEX binary, bool flag) { return minorant_[dual_idx(binary, flag)]; }

  vector<int> indicator_; // FIXME: bool does not work with this class
  vector<REAL> minorant_, tmp_;

  friend class exactly_one_minorant_message;
};

class implication_factor {
public:
  REAL LowerBound() const
  {
    REAL result = duals_left_[1] + duals_right_[1];
    for (INDEX i = 0; i < 2; ++i)
      result = std::min(result, duals_left_[0] + duals_right_[i]);
    return result;
  }

  REAL EvaluatePrimal() const
  {
    if ((primal_left_ >= 2 || primal_right_ >= 2) || (primal_left_ == 1 && primal_right_ == 0))
      return std::numeric_limits<REAL>::infinity();
    else
      return duals_left_[primal_left_] + duals_right_[primal_right_];
  }

  void init_primal()
  {
    primal_left_ = primal_right_ = std::numeric_limits<INDEX>::max();
  }

  void MaximizePotentialAndComputePrimal()
  {
    // TODO: This is complicated as fuck... :/
    if (primal_left_ >= 2 && primal_right_ >= 2) {
      primal_left_ = primal_right_ = 1;
      REAL min = duals_left_[1] + duals_right_[1];
      for (INDEX i = 0; i < 2; ++i) {
        REAL current = duals_left_[0] + duals_right_[i];
        if (current <= min) {
          primal_left_ = 0;
          primal_right_ = i;
        }
      }
    } else if (primal_right_ >= 2) {
      if (primal_left_ == 1)
        primal_right_ = 1;
      else
        primal_right_ = std::min_element(duals_right_.begin(), duals_right_.end()) - duals_right_.begin();
    } else if (primal_left_ >= 2) {
      primal_right_ = std::min_element(duals_right_.begin(), duals_right_.end()) - duals_right_.begin();
    }
  }

  auto export_variables() { return std::tie(duals_left_, duals_right_); }

  template<typename SOLVER>
  void construct_constraints(SOLVER& solver,
    typename SOLVER::vector left_vars, typename SOLVER::vector right_vars) const
  {
    solver.add_simplex_constraint(left_vars.begin(), left_vars.end());
    solver.add_simplex_constraint(right_vars.begin(), right_vars.end());
    solver.add_implication(left_vars[1], right_vars[1]);
  }

  template<typename SOLVER>
  void convert_primal(SOLVER& s,
    typename SOLVER::vector left_vars, typename SOLVER::vector right_vars)
  {
    init_primal();
    primal_left_ = s.first_active(left_vars);
    primal_right_ = s.first_active(right_vars);
    assert(!(s.solution(left_vars[1]) && s.solution(right_vars[0])));
  }

  template<typename ARCHIVE>
  void serialize_primal(ARCHIVE& ar) { ar(primal_left_); ar(primal_right_); }

  template<typename ARCHIVE>
  void serialize_dual(ARCHIVE& ar) {
    ar(duals_left_);
    ar(duals_right_);
  }

  std::pair<INDEX, INDEX> primal() const { return std::make_pair(primal_left_, primal_right_); }

protected:
  INDEX primal_left_, primal_right_;
  std::array<REAL, 2> duals_left_, duals_right_;

  template<Chirality CHIRALITY> friend class implication_message;
};

// LEFT_FACTOR = binary
// RIGHT_FACTOR = exactly_one
class exactly_one_message {
public:
  exactly_one_message(INDEX binary_idx)
  : binary_idx_(binary_idx)
  { }

  template<typename LEFT_FACTOR, typename G2>
  void send_message_to_right(LEFT_FACTOR& l, G2& msg, const REAL omega)
  {
    msg[0] -= l[0] * omega;
    msg[1] -= l[1] * omega;
  }

  template<typename RIGHT_FACTOR, typename G2>
  void send_message_to_left(RIGHT_FACTOR& r, G2& msg, const REAL omega)
  {
    assert(binary_idx_ >= 0 && binary_idx_ < r.no_binaries_);
    // FIXME: This omega computation is error-prone.
    msg[0] -= r.dual(binary_idx_, 0) * omega * r.no_binaries_;
    msg[1] -= r.dual(binary_idx_, 1) * omega * r.no_binaries_;
  }

  template<typename LEFT_FACTOR>
  void RepamLeft(LEFT_FACTOR& l, const REAL msg, const INDEX msg_dim)
  {
    assert(msg_dim >= 0 && msg_dim < 2);
    l[msg_dim] += msg;
  }

  template<typename RIGHT_FACTOR>
  void RepamRight(RIGHT_FACTOR& r, const REAL msg, const INDEX msg_dim)
  {
    assert(binary_idx_ >= 0 && binary_idx_ < r.no_binaries_);
    assert(msg_dim >= 0 && msg_dim < 2);
    r.dual(binary_idx_, msg_dim == 1) += msg;
  }

  template<typename SOLVER, typename LEFT_FACTOR, typename RIGHT_FACTOR>
  void construct_constraints(SOLVER& s,
    LEFT_FACTOR& l, typename SOLVER::vector left_vars,
    RIGHT_FACTOR& r, typename SOLVER::vector right_vars) const
  {
    assert(r.duals_.size() == right_vars.size());
    s.make_equal(left_vars[0], right_vars[binary_idx_*2]);
    s.make_equal(left_vars[1], right_vars[binary_idx_*2+1]);
  }

  template<typename LEFT_FACTOR, typename RIGHT_FACTOR>
  bool CheckPrimalConsistency(const LEFT_FACTOR& l, const RIGHT_FACTOR& r) const
  {
    assert(binary_idx_ >= 0 && binary_idx_ < r.no_binaries_);
    return l.primal() == (r.primal() == binary_idx_ ? 1 : 0);
  }

protected:
  INDEX binary_idx_;
};

// LEFT_FACTOR = binary
// RIGHT_FACTOR = exactly_one_minorant
class exactly_one_minorant_message : public exactly_one_message {
public:
  using exactly_one_message::exactly_one_message;

  template<typename LEFT_FACTOR, typename G2>
  void send_message_to_right(LEFT_FACTOR& l, G2& msg, const REAL omega)
  {
    msg[0] -= l[0] * omega;
    msg[1] -= l[1] * omega;
  }

  template<typename RIGHT_FACTOR, typename G2>
  void send_message_to_left(RIGHT_FACTOR& r, G2& msg, const REAL omega)
  {
    assert(binary_idx_ >= 0 && binary_idx_ < r.no_binaries_);
    // FIXME: This omega computation is error-prone.
    msg[0] -= r.dual(binary_idx_, 0) * omega * r.no_binaries_;
    msg[1] -= r.dual(binary_idx_, 1) * omega * r.no_binaries_;
  }

  template<typename LEFT_FACTOR>
  void RepamLeft(LEFT_FACTOR& l, const REAL msg, const INDEX msg_dim)
  {
    assert(msg_dim >= 0 && msg_dim < 2);
    l[msg_dim] += msg;
  }

  template<typename RIGHT_FACTOR>
  void RepamRight(RIGHT_FACTOR& r, const REAL msg, const INDEX msg_dim)
  {
    assert(msg_dim >= 0 && msg_dim < 2);
    assert(binary_idx_ >= 0 && binary_idx_ < r.no_binaries_);
    r.dual(binary_idx_, msg_dim == 1) += msg;
    r.minorant(binary_idx_, msg_dim == 1) += msg; // send_message could be called multiple times, so we keep current minorant up to date
  }
};

template<Chirality CHIRALITY>
class implication_message {
public:
  template<typename LEFT_FACTOR, typename G2>
  void send_message_to_right(LEFT_FACTOR& l, G2& msg, const REAL omega)
  {
    msg[0] -= l[0] * omega;
    msg[1] -= l[1] * omega;
  }

  template<typename RIGHT_FACTOR, typename G2>
  void send_message_to_left(RIGHT_FACTOR& r, G2& msg, const REAL omega)
  {
    if constexpr (CHIRALITY == Chirality::left) {
      msg[0] -= r.duals_left_[0] + r.duals_right_[0];
      msg[1] -= r.duals_left_[1] + std::min(r.duals_right_[0], r.duals_right_[1]);
    } else {
      static_assert(CHIRALITY == Chirality::right);
      msg[0] -= r.duals_right_[0] + std::min(r.duals_left_[0], r.duals_left_[1]);
      msg[1] -= r.duals_right_[0] + r.duals_left_[1];
    }
  }

  template<typename LEFT_FACTOR>
  void RepamLeft(LEFT_FACTOR& l, const REAL msg, const INDEX msg_dim)
  {
    l[msg_dim] += msg;
  }

  template<typename RIGHT_FACTOR>
  void RepamRight(RIGHT_FACTOR& r, const REAL msg, const INDEX msg_dim)
  {
    if constexpr (CHIRALITY == Chirality::left) {
      r.duals_left_[msg_dim] += msg;
    } else {
      static_assert(CHIRALITY == Chirality::right);
      r.duals_right_[msg_dim] += msg;
    }
  }

  template<typename SOLVER, typename LEFT_FACTOR, typename RIGHT_FACTOR>
  void construct_constraints(SOLVER& s,
    LEFT_FACTOR& l, typename SOLVER::vector left_vars,
    RIGHT_FACTOR& r, typename SOLVER::vector right_left_vars, typename SOLVER::vector right_right_vars) const
  {
    if constexpr (CHIRALITY == Chirality::left) {
      s.make_equal(left_vars[0], right_left_vars[0]);
      s.make_equal(left_vars[1], right_left_vars[1]);
    } else {
      static_assert(CHIRALITY == Chirality::right);
      s.make_equal(left_vars[0], right_right_vars[0]);
      s.make_equal(left_vars[1], right_right_vars[1]);
    }
  }

  template<typename LEFT_FACTOR, typename RIGHT_FACTOR>
  bool CheckPrimalConsistency(const LEFT_FACTOR& l, const RIGHT_FACTOR& r) const
  {
    if constexpr (CHIRALITY == Chirality::left) {
      return l.primal() == r.primal().first;
    } else {
      static_assert(CHIRALITY == Chirality::right);
      return l.primal() == r.primal().second;
    }
  }
};

enum class graph_direction { forward, backward };

template<typename FMC_T>
class my_tracking_constructor {
public:
  using FMC = FMC_T;
  using binary_factor_container = typename FMC::binary_factor_container;
  using exactly_one_factor_container = typename FMC::exactly_one_factor_container;
  using exactly_one_minorant_factor_container = typename FMC::exactly_one_minorant_factor_container;
  using implication_factor_container = typename FMC::implication_factor_container;
  using exactly_one_message_container = typename FMC::exactly_one_message_container;
  using exactly_one_minorant_message_container = typename FMC::exactly_one_minorant_message_container;
  using implication_left_message_container = typename FMC::implication_left_message_container;
  using implication_right_message_container = typename FMC::implication_right_message_container;

  template<typename SOLVER>
  my_tracking_constructor(SOLVER& solver)
  : lp_(&solver.GetLP())
  {}

  void set_number_of_timesteps(const INDEX t)
  {
    assert(segmentation_infos_.size() == 0);
    segmentation_infos_.resize(t);
  }

  void add_detection_hypothesis(LP<FMC>& lp,
    const INDEX timestep, const INDEX hypothesis_id,
    const REAL detection_cost, const REAL appearance_cost, const REAL disappearance_cost,
    const INDEX no_incoming_transition_edges, const INDEX no_incoming_division_edges,
    const INDEX no_outgoing_transition_edges, const INDEX no_outgoing_division_edges)
  {
#if 1
    if (! (timestep >= 0 && timestep <= 1))
      return;
#endif

    assert(timestep < segmentation_infos_.size());
    if (hypothesis_id >= segmentation_infos_[timestep].size())
      segmentation_infos_[timestep].resize(hypothesis_id+1);
    assert(segmentation_infos_[timestep][hypothesis_id].detection == nullptr);
    if (hypothesis_id > 0)
      assert(segmentation_infos_[timestep][hypothesis_id-1].detection != nullptr);

    auto& fs = segmentation_infos_[timestep][hypothesis_id];
    fs.detection = lp.template add_factor<binary_factor_container>(detection_cost);
    fs.appearance.binary = lp.template add_factor<binary_factor_container>(appearance_cost);
    fs.disappearance.binary = lp.template add_factor<binary_factor_container>(disappearance_cost);

    fs.appearance.implication = lp.template add_factor<implication_factor_container>();
    lp.template add_message<implication_left_message_container>(fs.appearance.binary, fs.appearance.implication);
    lp.template add_message<implication_right_message_container>(fs.detection, fs.appearance.implication);

    fs.disappearance.implication = lp.template add_factor<implication_factor_container>();
    lp.template add_message<implication_left_message_container>(fs.disappearance.binary, fs.disappearance.implication);
    lp.template add_message<implication_right_message_container>(fs.detection, fs.disappearance.implication);

    lp.AddFactorRelation(fs.appearance.binary, fs.appearance.implication);
    lp.AddFactorRelation(fs.appearance.implication, fs.detection);
    lp.AddFactorRelation(fs.detection, fs.disappearance.implication);
    lp.AddFactorRelation(fs.disappearance.implication, fs.disappearance.binary);

#ifndef NDEBUG
    fs.no_incoming_divisions = no_incoming_division_edges;
    fs.no_incoming_transitions = no_incoming_transition_edges;
    fs.no_outgoing_divisions = no_outgoing_division_edges;
    fs.no_outgoing_transitions = no_outgoing_transition_edges;
#endif
  }

  void add_cell_transition(LP<FMC>& lp,
    const INDEX timestep_prev, const INDEX prev_cell,
    const INDEX timestep_next, const INDEX next_cell,
    const REAL cost)
  {
#if 1
    if (! (timestep_prev >= 0 && timestep_next <= 1))
      return;
#endif

    auto& prev_factors = segmentation_infos_[timestep_prev][prev_cell];
    auto& next_factors = segmentation_infos_[timestep_next][next_cell];

    auto* f_transition = lp.template add_factor<binary_factor_container>(cost);
    auto* f_left_implication = lp.template add_factor<implication_factor_container>();
    auto* f_right_implication = lp.template add_factor<implication_factor_container>();

    lp.template add_message<implication_left_message_container>(f_transition, f_left_implication);
    lp.template add_message<implication_right_message_container>(prev_factors.detection, f_left_implication);

    lp.template add_message<implication_left_message_container>(f_transition, f_right_implication);
    lp.template add_message<implication_right_message_container>(next_factors.detection, f_right_implication);

    prev_factors.outgoing_transitions.emplace_back(f_transition, f_left_implication);
    next_factors.incoming_transitions.emplace_back(f_transition, f_right_implication);

    lp.AddFactorRelation(prev_factors.detection, f_left_implication);
    lp.AddFactorRelation(f_left_implication, f_transition);
    lp.AddFactorRelation(f_transition, f_right_implication);
    lp.AddFactorRelation(f_right_implication, next_factors.detection);
  }

  void add_cell_division(LP<FMC>& lp,
    const INDEX timestep_prev, const INDEX prev_cell,
    const INDEX timestep_next_1, const INDEX next_cell_1,
    const INDEX timestep_next_2, const INDEX next_cell_2,
    const REAL cost)
  {
#if 1
    if (! (timestep_prev >= 0 && std::max(timestep_next_1, timestep_next_2) <= 1))
      return;
#endif

    auto& prev_factors = segmentation_infos_[timestep_prev][prev_cell];
    auto& next_factors_1 = segmentation_infos_[timestep_next_1][next_cell_1];
    auto& next_factors_2 = segmentation_infos_[timestep_next_2][next_cell_2];

    auto* f_division = lp.template add_factor<binary_factor_container>(cost);

    auto* f_left_implication = lp.template add_factor<implication_factor_container>();
    lp.template add_message<implication_left_message_container>(f_division, f_left_implication);
    lp.template add_message<implication_right_message_container>(prev_factors.detection, f_left_implication);

    auto* f_right_implication_1 = lp.template add_factor<implication_factor_container>();
    lp.template add_message<implication_left_message_container>(f_division, f_right_implication_1);
    lp.template add_message<implication_right_message_container>(next_factors_1.detection, f_right_implication_1);

    auto* f_right_implication_2 = lp.template add_factor<implication_factor_container>();
    lp.template add_message<implication_left_message_container>(f_division, f_right_implication_2);
    lp.template add_message<implication_right_message_container>(next_factors_2.detection, f_right_implication_2);

    prev_factors.outgoing_divisions.emplace_back(f_division, f_left_implication);
    next_factors_1.incoming_divisions.emplace_back(f_division, f_right_implication_1);
    next_factors_2.incoming_divisions.emplace_back(f_division, f_right_implication_2);

    lp.AddFactorRelation(prev_factors.detection, f_left_implication);
    lp.AddFactorRelation(f_left_implication, f_division);
    lp.AddFactorRelation(f_division, f_right_implication_1);
    lp.AddFactorRelation(f_right_implication_1, next_factors_1.detection);
    lp.AddFactorRelation(f_division, f_right_implication_2);
    lp.AddFactorRelation(f_right_implication_2, next_factors_2.detection);
  }

  template<typename ITERATOR>
  void add_exclusion_constraint(LP<FMC>& lp, ITERATOR begin, ITERATOR end) // iterator points to std::array<INDEX,2>
  {
    const INDEX timestep = (*begin)[0];
#if 1
    if (! (timestep >= 0 && timestep <= 1))
      return;
#endif

    exclusion_infos_.resize(segmentation_infos_.size());
    exclusion_infos_[timestep].emplace_back();
    auto& exclusion = exclusion_infos_[timestep].back();

    const INDEX n = std::distance(begin, end) + 1;
    exclusion.dummy = lp.template add_factor<binary_factor_container>();
    exclusion.exactly_one = lp.template add_factor<exactly_one_minorant_factor_container>(n);

    INDEX idx = 0;
    lp.template add_message<exactly_one_minorant_message_container>(exclusion.dummy, exclusion.exactly_one, idx++);
    for (auto it = begin; it != end; ++it) {
      assert(timestep == (*it)[0]);
      const INDEX hypothesis_id = (*it)[1];

      auto* f = segmentation_infos_[timestep][hypothesis_id].detection;
      lp.template add_message<exactly_one_minorant_message_container>(f, exclusion.exactly_one, idx++);
      exclusion.segmentations.push_back(std::make_tuple(timestep, hypothesis_id));
    }
    assert(idx == n);

    lp.AddFactorRelation(exclusion.exactly_one, exclusion.dummy);
    for (auto s : exclusion.segmentations) {
      auto* f = segmentation_infos_[std::get<0>(s)][std::get<1>(s)].detection;
      lp.AddFactorRelation(exclusion.exactly_one, f);
    }
  }

  void begin(LP<FMC>& lp, const std::size_t no_cell_detection_hypotheses, const std::size_t no_transitions, const std::size_t no_divisions)
  {
  }

  void end(LP<FMC>& lp)
  {
    for (auto& timestep : segmentation_infos_) {
      for (auto& segmentation : timestep) {
        /*
         * FIXME: Comment in again.
        assert(segmentation.incoming_divisions.size() == segmentation.no_incoming_divisions);
        assert(segmentation.incoming_transitions.size() == segmentation.no_incoming_transitions);
        assert(segmentation.outgoing_divisions.size() == segmentation.no_outgoing_divisions);
        assert(segmentation.outgoing_transitions.size() == segmentation.no_outgoing_transitions);
        */

        auto incoming_uniqueness = [&]() {
          INDEX size = 2 + segmentation.incoming_transitions.size() + segmentation.incoming_divisions.size();

          segmentation.dummy_incoming = lp.template add_factor<binary_factor_container>();
          segmentation.exactly_one_incoming = lp.template add_factor<exactly_one_minorant_factor_container>(size);

          INDEX idx = 0;
          segmentation.for_each_incoming([&](auto* binary, auto* _) {
            lp.template add_message<exactly_one_minorant_message_container>(binary, segmentation.exactly_one_incoming, idx++);
          });
          assert(idx == size);

          segmentation.exactly_one_incoming_additional = lp.template add_factor<exactly_one_factor_container>(2);
          lp.template add_message<exactly_one_message_container>(segmentation.dummy_incoming, segmentation.exactly_one_incoming_additional, 0);
          lp.template add_message<exactly_one_message_container>(segmentation.detection, segmentation.exactly_one_incoming_additional, 1);
        };

        auto outgoing_uniqueness = [&]() {
          INDEX size = 2 + segmentation.outgoing_transitions.size() + segmentation.outgoing_divisions.size();

          segmentation.dummy_outgoing = lp.template add_factor<binary_factor_container>();
          segmentation.exactly_one_outgoing = lp.template add_factor<exactly_one_minorant_factor_container>(size);

          INDEX idx = 0;
          segmentation.for_each_outgoing([&](auto* binary, auto* _) {
            lp.template add_message<exactly_one_minorant_message_container>(binary, segmentation.exactly_one_outgoing, idx++);
          });
          assert(idx == size);

          segmentation.exactly_one_outgoing_additional = lp.template add_factor<exactly_one_factor_container>(2);
          lp.template add_message<exactly_one_message_container>(segmentation.detection, segmentation.exactly_one_outgoing_additional, 0);
          lp.template add_message<exactly_one_message_container>(segmentation.dummy_outgoing, segmentation.exactly_one_outgoing_additional, 1);
        };

        auto order = [&]() {
          lp.AddFactorRelation(segmentation.dummy_incoming, segmentation.exactly_one_incoming_additional);
          lp.AddFactorRelation(segmentation.exactly_one_incoming_additional, segmentation.detection);
          segmentation.for_each_incoming([&](FactorTypeAdapter* binary, FactorTypeAdapter* connector) {
            lp.AddFactorRelation(segmentation.exactly_one_incoming, binary);
          });

          lp.AddFactorRelation(segmentation.detection, segmentation.exactly_one_outgoing_additional);
          lp.AddFactorRelation(segmentation.exactly_one_outgoing_additional, segmentation.dummy_outgoing);
          segmentation.for_each_outgoing([&](FactorTypeAdapter* binary, FactorTypeAdapter* connector) {
            lp.AddFactorRelation(segmentation.exactly_one_outgoing, binary);
            lp.AddFactorRelation(connector, segmentation.exactly_one_outgoing);
          });
        };

        incoming_uniqueness();
        outgoing_uniqueness();
        order();
      }
    }

    for (auto& timestep : exclusion_infos_) {
      for (auto& exclusion : timestep) {
        for (auto s : exclusion.segmentations) {
          auto [timestep, hypothesis_id] = s;
          auto& segmentation = segmentation_infos_[timestep][hypothesis_id];
          segmentation.for_each_incoming([&](FactorTypeAdapter* binary, FactorTypeAdapter* connector) {
            lp.AddFactorRelation(connector, exclusion.exactly_one);
            lp.AddFactorRelation(exclusion.exactly_one, segmentation.detection);
          });
        }
      }
    }

    for (INDEX timestep = 1; timestep < segmentation_infos_.size(); ++timestep) {
      for (auto& segmentation_right : segmentation_infos_[timestep]) {
        for (auto& segmentation_left : segmentation_infos_[timestep-1]) {
          segmentation_left.for_each_outgoing([&](FactorTypeAdapter* binary, FactorTypeAdapter* connector) {
            lp.AddFactorRelation(connector, segmentation_right.exactly_one_incoming);
          });
        }
      }
    }
  }

  void debug() const
  {
    int timestep_idx = 0;
    for (const auto& timestep : segmentation_infos_) {
      std::cout << std::endl << ":: Timestep " << timestep_idx++ << std::endl << std::endl;
      int segmentation_idx = 0;
      for (const auto& segmentation : timestep) {
        std::cout << "segmentation " << segmentation_idx++ << ": " << segmentation.detection->GetFactor()->primal() << std::endl;
      }
    }
  }

  template<graph_direction DIRECTION = graph_direction::forward>
  void output_graphviz(LP<FMC>& lp, const std::string& filename)
  {
    const auto& omega = lp.get_omega();

    //
    // Useless template metaprogramming shizzle.
    //

    auto get_update_ordering = [&lp]()constexpr -> auto& {
      if constexpr (DIRECTION == graph_direction::forward)
        return lp.forwardUpdateOrdering_;
      else
        return lp.backwardUpdateOrdering_;
    };

    auto get_ordering = [&lp]() constexpr -> auto& {
      if constexpr (DIRECTION == graph_direction::forward)
        return lp.forwardOrdering_;
      else
        return lp.backwardOrdering_;
    };

    auto get_omega_send = [&omega]() constexpr -> auto& {
      if constexpr (DIRECTION == graph_direction::forward)
        return omega.forward;
      else
        return omega.backward;
    };

    auto get_omega_recv = [&omega]() constexpr -> auto&{
      if constexpr (DIRECTION == graph_direction::forward)
        return omega.receive_mask_forward;
      else
        return omega.receive_mask_backward;
    };

    //
    // Extract intrinsicts out of LP class.
    //

    std::map<const FactorTypeAdapter*, INDEX> factor_index;
    for (INDEX i = 0; i < lp.GetNumberOfFactors(); ++i) {
      assert(factor_index.find(lp.GetFactor(i)) == factor_index.end());
      factor_index.insert(std::make_pair(lp.GetFactor(i), i));
    }

    int i = 0;
    std::map<const FactorTypeAdapter*, INDEX> update_index;
    for (const auto* f : get_update_ordering()) {
      assert(update_index.find(f) == update_index.end());
      update_index.insert(std::make_pair(f, i++));
    }

    i = 0;
    std::map<const FactorTypeAdapter*, INDEX> ordered_index;
    for (const auto* f : get_ordering()) {
      assert(ordered_index.find(f) == ordered_index.end());
      ordered_index.insert(std::make_pair(f, i++));
    }

    //
    // Helpers for drawing.
    //

    auto f_name = [&](auto* f) {
      std::stringstream s;
      s << "\"f_" << f << "\"";
      return s.str();
    };

    auto tooltip = [&](auto* f) {
      std::stringstream s;

      auto it = update_index.find(f);
      if (it != update_index.end())
        s << "s_fw=" << print_container(get_omega_send()[it->second]) << "\\n"
          << "r_fw=" << print_container(get_omega_recv()[it->second]);

      return s.str();
    };

    auto format_node = [&](auto* f, std::string label) {
      std::stringstream s;
      s << f_name(f) << " [label=\"";

      auto it = update_index.find(f);
      if (it != update_index.end())
        s << "[" << it->second << "]\\n";

      s << label << "\",tooltip=\"" << tooltip(f) << "\"];\n";
      return s.str();
    };

    auto get_s_fw = [&](FactorTypeAdapter* f_left, FactorTypeAdapter* f_right) {
      bool found = false;
      INDEX idx = 0;
      for (auto msg : f_left->get_messages()) {
        if (msg.sends_to_adjacent_factor) {
          if (msg.adjacent_factor == f_right) {
            found = true;
            break;
          }
          ++idx;
        }
      }

      if (!found)
        return 0.0;

      return get_omega_send()[update_index.at(f_left)][idx];
    };

    auto get_r_fw = [&](FactorTypeAdapter* f_left, FactorTypeAdapter* f_right) {
      bool found = false;
      INDEX idx = 0;
      for (auto msg : f_right->get_messages()) {
        if (msg.receives_from_adjacent_factor) {
          if (msg.adjacent_factor == f_left) {
            found = true;
            break;
          }
          ++idx;
        }
      }

      if (!found)
        return 0;

      return get_omega_recv()[update_index.at(f_right)][idx];
    };

    auto format_edge = [&](FactorTypeAdapter* f_left, FactorTypeAdapter* f_right) {
      auto s_fw = get_s_fw(f_left, f_right);
      auto r_fw = get_r_fw(f_left, f_right);

      std::stringstream s;
      s << f_name(f_left) << " -> " << f_name(f_right) << " [label=\"";

      if (s_fw > eps)
        s << "s=" << s_fw;

      if (s_fw > eps && r_fw > eps)
        s << " ";

      if (r_fw > eps)
        s << "r=" << r_fw;

      s  << "\"];\n";
      return s.str();
    };

    auto draw_all_factors = [&](std::ostream& o) {
      for (size_t timestep = 0; timestep < segmentation_infos_.size(); ++timestep) {
        for (size_t hypothesis_id = 0; hypothesis_id < segmentation_infos_[timestep].size(); ++hypothesis_id) {
          auto det_label = [&]() {
            std::stringstream s;
            s << "det(" << timestep << "," << hypothesis_id << ")";
            return s.str();
          };

          auto app_label = [&]() {
            std::stringstream s;
            s << "app(" << timestep << "," << hypothesis_id << ")";
            return s.str();
          };

          auto disapp_label = [&]() {
            std::stringstream s;
            s << "disapp(" << timestep << "," << hypothesis_id << ")";
            return s.str();
          };

          auto& segmentation = segmentation_infos_[timestep][hypothesis_id];
          o << format_node(segmentation.detection, det_label())
            << format_node(segmentation.exactly_one_incoming, "=1 in")
            << format_node(segmentation.dummy_incoming, "dummy in")
            << format_node(segmentation.exactly_one_incoming_additional, "=1 in+")
            << format_node(segmentation.exactly_one_outgoing, "=1 out")
            << format_node(segmentation.dummy_outgoing, "dummy out")
            << format_node(segmentation.exactly_one_outgoing_additional, "=1 out+")
            << format_node(segmentation.appearance.binary, app_label())
            << format_node(segmentation.appearance.implication, "→")
            << format_node(segmentation.disappearance.binary, disapp_label())
            << format_node(segmentation.disappearance.implication, "→");

          for (auto e : segmentation.incoming_transitions) {
            o << format_node(e.binary, "trans")
              << format_node(e.implication, "→");
          }

          for (auto e : segmentation.incoming_divisions) {
            o << format_node(e.binary, "div")
              << format_node(e.implication, "→");
          }

          for (auto e : segmentation.outgoing_transitions) {
            o << format_node(e.binary, "trans")
              << format_node(e.implication, "→");
          }

          for (auto e : segmentation.outgoing_divisions) {
            o << format_node(e.binary, "div")
              << format_node(e.implication, "→");
          }
        }
      }

      for (const auto& timestep : exclusion_infos_) {
        for (const auto& exclusion : timestep) {
          o << format_node(exclusion.exactly_one, "=1")
            << format_node(exclusion.dummy, "ex dummy");
        }
      }
    };

    auto draw_all_messages = [&](std::ostream& o) {
      lp.for_each_message([&](auto* msg) {
        FactorTypeAdapter* f_left = msg->GetLeftFactor();
        FactorTypeAdapter* f_right = msg->GetRightFactor();

        if (ordered_index.at(f_left) > ordered_index.at(f_right))
          std::swap(f_left, f_right);

        o << format_edge(f_left, f_right);
      });
    };

    std::ofstream file(filename);
    file << "digraph {\n";
    draw_all_factors(file);
    draw_all_messages(file);

    file << "}";
  }

protected:

public: // FIXME: We don't need this, but dictated by interface for now.
  std::vector<std::size_t> cumulative_sum_cell_detection_factors;

protected:
  struct edge_info {
    edge_info() = default;

    edge_info(binary_factor_container* b, implication_factor_container* i)
    : binary(b), implication(i) { }

    binary_factor_container* binary;
    implication_factor_container* implication;
  };

  struct segmentation_info {
    binary_factor_container* detection;
    edge_info appearance;
    edge_info disappearance;
    std::vector<edge_info> incoming_transitions;
    std::vector<edge_info> incoming_divisions;
    std::vector<edge_info> outgoing_transitions;
    std::vector<edge_info> outgoing_divisions;
    binary_factor_container* dummy_incoming;
    binary_factor_container* dummy_outgoing;
    exactly_one_minorant_factor_container* exactly_one_incoming;
    exactly_one_factor_container* exactly_one_incoming_additional;
    exactly_one_minorant_factor_container* exactly_one_outgoing;
    exactly_one_factor_container* exactly_one_outgoing_additional;
    // FIXME: Information about "=1" factors is missing.

    template<typename FUNCTOR>
    void for_each_incoming(FUNCTOR func) {
      func(dummy_incoming, exactly_one_incoming_additional);
      func(appearance.binary, appearance.implication);
      for (auto e : incoming_transitions)
        func(e.binary, e.implication);
      for (auto e : incoming_divisions)
        func(e.binary, e.implication);
    };

    template<typename FUNCTOR>
    void for_each_outgoing(FUNCTOR func) {
      func(dummy_outgoing, exactly_one_outgoing_additional);
      func(disappearance.binary, disappearance.implication);
      for (auto e : outgoing_transitions)
        func(e.binary, e.implication);
      for (auto e : outgoing_divisions)
        func(e.binary, e.implication);
    };

#ifndef NDEBUG
    INDEX no_incoming_transitions, no_incoming_divisions, no_outgoing_transitions, no_outgoing_divisions;
#endif
  };
  using segmentation_info_storage = std::vector<std::vector<segmentation_info>>;
  segmentation_info_storage segmentation_infos_;

  struct exclusion_info {
    exactly_one_minorant_factor_container* exactly_one;
    binary_factor_container* dummy;
    std::vector<std::tuple<INDEX, INDEX>> segmentations;
  };

  using exclusion_info_storage = std::vector<std::vector<exclusion_info>>;
  exclusion_info_storage exclusion_infos_;

  LP<FMC>* lp_;
};

struct FMC_MY {
  constexpr static const char* name = "My Cell Tracking";
  using FMC = FMC_MY;

  using binary_factor_container = FactorContainer<binary_factor, FMC, 0, /* true */ false>;
  using exactly_one_factor_container = FactorContainer<exactly_one_factor, FMC, 1, false>;
  using exactly_one_minorant_factor_container = FactorContainer<exactly_one_minorant_factor, FMC, 2, false>;
  using implication_factor_container = FactorContainer<implication_factor, FMC, 3, false>;
  using FactorList = meta::list<
    binary_factor_container,
    exactly_one_factor_container,
    exactly_one_minorant_factor_container,
    implication_factor_container>;

  using exactly_one_message_container = MessageContainer<exactly_one_message, 0, 1, message_passing_schedule::right, variableMessageNumber, variableMessageNumber, FMC, 0>;
  using exactly_one_minorant_message_container = MessageContainer<exactly_one_minorant_message, 0, 2, message_passing_schedule::right, variableMessageNumber, variableMessageNumber, FMC, 1>;
  using implication_left_message_container = MessageContainer<implication_message<Chirality::left>, 0, 3, message_passing_schedule::only_send, variableMessageNumber, 1, FMC, 2>;
  using implication_right_message_container = MessageContainer<implication_message<Chirality::right>, 0, 3, message_passing_schedule::only_send, variableMessageNumber, 1, FMC, 3>;
  using MessageList = meta::list<
    exactly_one_message_container,
    exactly_one_minorant_message_container,
    implication_left_message_container,
    implication_right_message_container>;

  using ProblemDecompositionList = meta::list<my_tracking_constructor<FMC>>;
};

}

using namespace LP_MP;

int main(int argc, char** argv) {
#if 1
  using BaseSolver = Solver<LP<FMC_MY>, StandardVisitor>;
  MpRoundingSolver<BaseSolver> solver(argc, argv);
  solver.ReadProblem(cell_tracking_parser_2d::ParseProblem<BaseSolver>);

  auto& lp = solver.GetLP();
  lp.set_reparametrization(LPReparametrizationMode::Anisotropic2);
  solver.GetProblemConstructor<0>().output_graphviz<graph_direction::backward>(lp, "debug.dot");
#elif 0
  using BaseSolver = Solver<LP_external_solver<DD_ILP::gurobi_interface, LP<FMC_MY>>, StandardVisitor>;
  BaseSolver solver(argc, argv);
  solver.ReadProblem(cell_tracking_parser_2d::ParseProblem<BaseSolver>);
  solver.GetLP().write_to_file("/tmp/my.lp");
  solver.GetLP().solve();
#else
  using BaseSolver = Solver<LP<FMC_MY>, StandardVisitor>;
  MpRoundingSolver<BaseSolver> solver(argc, argv);

  auto& lp = solver.GetLP();
  auto* f0 = lp.template add_factor<FMC_MY::binary_factor_container>(1);
  auto* f1 = lp.template add_factor<FMC_MY::exactly_one_minorant_factor_container>(1);
  auto* f2 = lp.template add_factor<FMC_MY::exactly_one_minorant_factor_container>(1);

  lp.template add_message<FMC_MY::exactly_one_minorant_message_container>(f0, f1, 0);
  lp.template add_message<FMC_MY::exactly_one_minorant_message_container>(f0, f2, 0);

  lp.AddFactorRelation(f0, f1);
  lp.AddFactorRelation(f0, f2);

  lp.Begin();
  lp.set_reparametrization(LPReparametrizationMode::Anisotropic2);
  lp.ComputeForwardPass();

  std::cout << print_container(*(f0->GetFactor())) << std::endl;
  std::cout << f1->GetFactor()->dual(0, false) << " " << f1->GetFactor()->dual(0, true) << std::endl;
  std::cout << f2->GetFactor()->dual(0, false) << " " << f2->GetFactor()->dual(0, true) << std::endl;
#endif
}
