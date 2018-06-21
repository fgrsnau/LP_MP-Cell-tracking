#include <random>
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

template<typename VECTOR1, typename VECTOR2>
void redistribute_duals(VECTOR1& duals, const VECTOR2& active, size_t from)
{
  assert(duals.size() == active.size() * 2);
  assert(from >= 0 && from < active.size());
  assert(!active[from]);

#ifndef NDEBUG
  using vector1_element = std::decay_t<decltype(duals[0])>;
  std::vector<vector1_element> old(duals.begin(), duals.end());
#endif

  auto id = [](const auto& x) -> bool { return x; };
  const auto no_active = std::count_if(active.begin(), active.end(), id);
  if (no_active >= 1) {
    auto on_diff = duals[from*2 + 1] + duals[from*2];
    auto add_to_on = - on_diff * (1.0 - 1.0 / no_active);
    auto add_to_off = on_diff * (1.0 / no_active);

    duals[from*2 + 1] = duals[from*2];
    for (size_t i = 0; i < active.size(); ++i) {
      if (active[i]) {
        duals[i*2] += add_to_off;
        duals[i*2 + 1] += add_to_on;
      }
    }
  }

#ifndef NDEBUG
  assert(std::abs(duals[from*2+1] - duals[from*2]) < eps);
  for (size_t i = 0; i < active.size(); ++i) {
    auto old_val = old[i*2+1];
    auto new_val = duals[i*2+1];
    for (size_t j = 0; j < active.size(); ++j) {
      if (i != j) {
        old_val += old[j*2];
        new_val += old[j*2];
      }
    }
    assert(std::abs(old_val - new_val) < eps);
  }
#endif
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
  using redistribute_functor = std::function<bool(INDEX i)>;

  exactly_one_minorant_factor(INDEX no_binaries, redistribute_functor rf = redistribute_functor())
  : exactly_one_factor(no_binaries)
  , indicator_(no_binaries * 2)
  , minorant_(no_binaries * 2)
  , tmp_(no_binaries_ * 2)
  , redistribute_functor_(std::move(rf))
  { }

  void MaximizePotential()
  {
    // This method computes the maximal minorant. FIXME: It implements a rather
    // generic scheme and could possibly be optimized for this very specific
    // case of binary variables with simplex constraint. For example, we know
    // the number of iterations beforehand, because we basically just try out
    // very specific configurations.

    for (INDEX i = 0; i < no_binaries_; ++i) {
      for (bool on : { false, true }) {
        const INDEX idx = dual_idx(i, on);

        if (redistribute_functor_)
          indicator_[idx] = redistribute_functor_(i) ? 1 : 0;
        else
          indicator_[idx] = 1;

        minorant_[idx] = 0;
        tmp_[idx] = duals_[idx];
      }
    }
    check();

    for (int iteration = 0; std::find(indicator_.begin(), indicator_.end(), 1) != indicator_.end(); ++iteration) {
      INDEX argmin = std::numeric_limits<INDEX>::max();
      REAL min = std::numeric_limits<REAL>::infinity();
      for (INDEX i = 0; i < no_binaries_; ++i) {
        INDEX h_x = 0;
        REAL current = 0;
        for (INDEX j = 0; j < no_binaries_; ++j) {
          current += tmp_[dual_idx(j, i == j)];
          if (indicator_[dual_idx(j, i == j)])
            ++h_x;
        }
        current /= h_x;
        if (h_x != 0 && current < min) {
          min = current;
          argmin = i;
        }
      }

      INDEX h_x = 0;
      for (INDEX i = 0; i < no_binaries_; ++i)
        if (indicator_[dual_idx(i, i == argmin)])
          ++h_x;

      const REAL& epsilon = min;

      if (debug())
        std::cout << "[MINORANT] iteration = " << iteration << "  ->  argmin = " << argmin << " / h_x = " << h_x << " / epsilon = " << epsilon << std::endl;

      for (INDEX i = 0; i < no_binaries_ * 2; ++i) {
        minorant_[i] += epsilon * indicator_[i];
        tmp_[i]      -= epsilon * indicator_[i];
      }
      check();

      for (INDEX i = 0; i < no_binaries_; ++i)
        indicator_[dual_idx(i, i == argmin)] = 0;

      if (debug())
        std::cout << "indicator_ = " << print_container(indicator_) << "\n"
                  << "tmp_ = " << print_container(tmp_) << "\n"
                  << "minorant_ = " << print_container(minorant_) << std::endl;
    }
  }

  void MaximizePotentialAndComputePrimal()
  {
    MaximizePotential();
    exactly_one_factor::MaximizePotentialAndComputePrimal();
    check();
  }

  void check() const
  {
    for (INDEX i = 0; i < no_binaries_*2; ++i) {
      assert(std::abs(tmp_[i] - (duals_[i] - minorant_[i]) < eps));
    }
  }

  const REAL& minorant(INDEX binary, bool flag) const { return minorant_[dual_idx(binary, flag)]; }

protected:
  REAL& minorant(INDEX binary, bool flag) { return minorant_[dual_idx(binary, flag)]; }

  vector<int> indicator_; // FIXME: bool does not work with this class
  vector<REAL> minorant_, tmp_;
  redistribute_functor redistribute_functor_;

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
    if (debug())
      std::cout << __PRETTY_FUNCTION__ << std::endl;
    msg[0] -= l[0] * omega;
    msg[1] -= l[1] * omega;
  }

  template<typename RIGHT_FACTOR, typename G2>
  void send_message_to_left(RIGHT_FACTOR& r, G2& msg, const REAL omega)
  {
    if (debug())
      std::cout << __PRETTY_FUNCTION__ << std::endl;

    assert(binary_idx_ >= 0 && binary_idx_ < r.no_binaries_);
    // Compute min-marginal
    REAL min_marginal_0 = std::numeric_limits<REAL>::infinity();
    for (INDEX i = 0; i < r.no_binaries_; ++i)
      if (i != binary_idx_)
        min_marginal_0 = std::min(min_marginal_0, r.compute(i));
    msg[0] -= min_marginal_0;

    // Min-marginal of "1" state is simpler.
    msg[1] -= r.compute(binary_idx_) * omega;
  }

  template<typename LEFT_FACTOR>
  void RepamLeft(LEFT_FACTOR& l, const REAL msg, const INDEX msg_dim)
  {
    if (debug())
      std::cout << __PRETTY_FUNCTION__ << std::endl;
    assert(msg_dim >= 0 && msg_dim < 2);
    l[msg_dim] += msg;
  }

  template<typename RIGHT_FACTOR>
  void RepamRight(RIGHT_FACTOR& r, const REAL msg, const INDEX msg_dim)
  {
    if (debug())
      std::cout << __PRETTY_FUNCTION__ << std::endl;
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
    if (debug())
      std::cout << __PRETTY_FUNCTION__ << std::endl;
    msg[0] -= l[0] * omega;
    msg[1] -= l[1] * omega;
  }

  template<typename RIGHT_FACTOR, typename G2>
  void send_message_to_left(RIGHT_FACTOR& r, G2& msg, const REAL omega)
  {
    if (debug())
      std::cout << __PRETTY_FUNCTION__ << " -> r=" << &r << " msg=" << &msg << "  omega=" << omega << std::endl;
    assert(binary_idx_ >= 0 && binary_idx_ < r.no_binaries_);

    // We have a the strict assumption, that we always push 100% out of the
    // exactly_one factor.
    assert(std::abs(omega * r.no_binaries_ - 1) < eps);

    if (debug())
      std::cout << "minorant_=" << print_container(r.minorant_) << std::endl;

    msg[0] -= r.minorant(binary_idx_, false);
    msg[1] -= r.minorant(binary_idx_, true);
  }

  template<typename LEFT_FACTOR>
  void RepamLeft(LEFT_FACTOR& l, const REAL msg, const INDEX msg_dim)
  {
    if (debug())
      std::cout << __PRETTY_FUNCTION__ << std::endl;
    assert(msg_dim >= 0 && msg_dim < 2);

    if (debug()) {
      std::cout << "l_before=" << print_container(l) << std::endl;
      std::cout << "msg=" << msg << " msg_dim=" << msg_dim << std::endl;
    }

    l[msg_dim] += msg;

    if (debug())
      std::cout << "l_after=" << print_container(l) << std::endl;
  }

  template<typename RIGHT_FACTOR>
  void RepamRight(RIGHT_FACTOR& r, const REAL msg, const INDEX msg_dim)
  {
    if (debug())
      std::cout << __PRETTY_FUNCTION__ << std::endl;
    assert(msg_dim >= 0 && msg_dim < 2);
    assert(binary_idx_ >= 0 && binary_idx_ < r.no_binaries_);

    if (debug()) {
      bool first = true;
      std::cout << "r_before=[";
      for (int i = 0; i < r.no_binaries_; ++i) {
        if (!first)
          std::cout << ", ";
        std::cout << r.dual(i, false) << ", " << r.dual(i, true);
        first = false;
      }
      std::cout << "]" << std::endl;
    }

    r.dual(binary_idx_, msg_dim == 1) += msg;
    r.minorant(binary_idx_, msg_dim == 1) += msg; // send_message could be called multiple times, so we keep current minorant up to date
    r.check();

    if (debug()) {
      std::cout << "r_after=[";
      bool first = true;
      for (int i = 0; i < r.no_binaries_; ++i) {
        if (!first)
          std::cout << ", ";
        std::cout << r.dual(i, false) << ", " << r.dual(i, true);
        first = false;
      }
      std::cout << "]" << std::endl;
    }
  }
};

template<Chirality CHIRALITY>
class implication_message {
public:
  template<typename LEFT_FACTOR, typename G2>
  void send_message_to_right(LEFT_FACTOR& l, G2& msg, const REAL omega)
  {
    if (debug())
      std::cout << __PRETTY_FUNCTION__ << std::endl;
    msg[0] -= l[0] * omega;
    msg[1] -= l[1] * omega;
  }

  template<typename RIGHT_FACTOR, typename G2>
  void send_message_to_left(RIGHT_FACTOR& r, G2& msg, const REAL omega)
  {
    if (debug())
      std::cout << __PRETTY_FUNCTION__ << std::endl;
    if constexpr (CHIRALITY == Chirality::left) {
      msg[0] -= r.duals_left_[0] + std::min(r.duals_right_[0], r.duals_right_[1]);
      msg[1] -= r.duals_left_[1] + r.duals_right_[1];
    } else {
      static_assert(CHIRALITY == Chirality::right);
      msg[0] -= r.duals_right_[0] + r.duals_left_[0];
      msg[1] -= r.duals_right_[1] + std::min(r.duals_left_[0], r.duals_left_[1]);
    }
  }

  template<typename LEFT_FACTOR>
  void RepamLeft(LEFT_FACTOR& l, const REAL msg, const INDEX msg_dim)
  {
    if (debug())
      std::cout << __PRETTY_FUNCTION__ << std::endl;
    l[msg_dim] += msg;
  }

  template<typename RIGHT_FACTOR>
  void RepamRight(RIGHT_FACTOR& r, const REAL msg, const INDEX msg_dim)
  {
    if (debug())
      std::cout << __PRETTY_FUNCTION__ << std::endl;
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

enum class direction { forward, backward };

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

  constexpr bool accept(INDEX timestep, INDEX hypothesis_id)
  {
#if 0
    if (! (timestep >= 0 && timestep <= 0))

      return false;

    if (! (hypothesis_id >= 0 && hypothesis_id <= 0))
      return false;
#endif

    return true;
  }

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
    if (!accept(timestep, hypothesis_id))
      return;

    assert(timestep < segmentation_infos_.size());
    if (hypothesis_id >= segmentation_infos_[timestep].size())
      segmentation_infos_[timestep].resize(hypothesis_id+1);
    assert(segmentation_infos_[timestep][hypothesis_id].detection == nullptr);
    if (hypothesis_id > 0)
      assert(segmentation_infos_[timestep][hypothesis_id-1].detection != nullptr);

    auto& fs = segmentation_infos_[timestep][hypothesis_id];
    fs.detection = lp.template add_factor<binary_factor_container>(detection_cost);
    fs.dummy = lp.template add_factor<binary_factor_container>();
    fs.appearance.binary = lp.template add_factor<binary_factor_container>(appearance_cost);
    fs.disappearance.binary = lp.template add_factor<binary_factor_container>(disappearance_cost);

    fs.exactly_one = lp.template add_factor<exactly_one_minorant_factor_container>(2);
    lp.template add_message<exactly_one_minorant_message_container>(fs.dummy, fs.exactly_one, 0);
    lp.template add_message<exactly_one_minorant_message_container>(fs.detection, fs.exactly_one, 1);

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
    if (!accept(timestep_prev, prev_cell) || !accept(timestep_next, next_cell))
      return;

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
    if (!accept(timestep_prev, prev_cell) || !accept(timestep_next_1, next_cell_1) || !accept(timestep_next_2, next_cell_2))
      return;

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
    for (auto it = begin; it != end; ++it)
      if (!accept(it->operator[](0), it->operator[](1)))
        return;

    const INDEX timestep = (*begin)[0];
    exclusion_infos_.resize(segmentation_infos_.size());
    exclusion_infos_[timestep].emplace_back();
    auto& exclusion = exclusion_infos_[timestep].back();

    auto redistribute_function = [](INDEX i) {
      return i == 0 ? false : true;
    };

    const INDEX n = std::distance(begin, end) + 1;
    exclusion.dummy = lp.template add_factor<binary_factor_container>();
    exclusion.exactly_one = lp.template add_factor<exactly_one_minorant_factor_container>(n, redistribute_function);

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

    lp.AddAsymmetricFactorRelation(exclusion.exactly_one, exclusion.dummy);
    for (auto s : exclusion.segmentations) {
      auto* f = segmentation_infos_[std::get<0>(s)][std::get<1>(s)].detection;
      lp.AddAsymmetricFactorRelation(exclusion.exactly_one, f);
    }
  }

  void begin(LP<FMC>& lp, const std::size_t no_cell_detection_hypotheses, const std::size_t no_transitions, const std::size_t no_divisions)
  {
  }

  void end(LP<FMC>& lp)
  {
    const auto& captured_direction = direction_;
    auto incoming_redistribute_functor = [&captured_direction](INDEX i) {
      if (captured_direction == direction::forward) {
        return true;
      } else {
        assert(captured_direction == direction::backward);
        return i < 2 ? false : true;
      }
    };
    auto outgoing_redistribute_functor = [&captured_direction](INDEX i) {
      if (captured_direction == direction::forward) {
        return i < 2 ? false : true;
      } else {
        assert(captured_direction == direction::backward);
        return true;
      }
    };


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

          segmentation.exactly_one_incoming = lp.template add_factor<exactly_one_minorant_factor_container>(size, incoming_redistribute_functor);

          INDEX idx = 0;
          segmentation.for_each_incoming([&](auto* binary, auto* _) {
            lp.template add_message<exactly_one_minorant_message_container>(binary, segmentation.exactly_one_incoming, idx++);
          });
          assert(idx == size);
        };

        auto outgoing_uniqueness = [&]() {
          INDEX size = 2 + segmentation.outgoing_transitions.size() + segmentation.outgoing_divisions.size();

          segmentation.exactly_one_outgoing = lp.template add_factor<exactly_one_minorant_factor_container>(size, outgoing_redistribute_functor);

          INDEX idx = 0;
          segmentation.for_each_outgoing([&](auto* binary, auto* _) {
            lp.template add_message<exactly_one_minorant_message_container>(binary, segmentation.exactly_one_outgoing, idx++);
          });
          assert(idx == size);
        };

        auto order = [&]() {
          segmentation.for_each_incoming([&](FactorTypeAdapter* binary, FactorTypeAdapter* connector) {
            lp.AddAsymmetricFactorRelation(segmentation.exactly_one_incoming, binary);
            lp.BackwardPassFactorRelation(connector, segmentation.exactly_one_incoming);

            if (connector != segmentation.exactly_one)
              lp.ForwardPassFactorRelation(connector, segmentation.exactly_one);
          });

          lp.AddAsymmetricFactorRelation(segmentation.exactly_one, segmentation.detection);

          segmentation.for_each_outgoing([&](FactorTypeAdapter* binary, FactorTypeAdapter* connector) {
            lp.AddAsymmetricFactorRelation(segmentation.exactly_one_outgoing, binary);
            lp.ForwardPassFactorRelation(connector, segmentation.exactly_one_outgoing);

            if (connector != segmentation.exactly_one)
              lp.BackwardPassFactorRelation(connector, segmentation.exactly_one);
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
            lp.ForwardPassFactorRelation(connector, exclusion.exactly_one);
            lp.ForwardPassFactorRelation(exclusion.exactly_one, segmentation.detection);
          });
          segmentation.for_each_outgoing([&](FactorTypeAdapter* binary, FactorTypeAdapter* connector) {
            lp.BackwardPassFactorRelation(connector, exclusion.exactly_one);
            lp.BackwardPassFactorRelation(exclusion.exactly_one, segmentation.detection);
          });
        }
      }
    }

    for (INDEX timestep = 1; timestep < segmentation_infos_.size(); ++timestep) {
      for (auto& segmentation_right : segmentation_infos_[timestep]) {
        for (auto& segmentation_left : segmentation_infos_[timestep-1]) {
          segmentation_left.for_each_outgoing([&](FactorTypeAdapter* binary, FactorTypeAdapter* connector) {
            lp.ForwardPassFactorRelation(connector, segmentation_right.exactly_one_incoming);
          });
          segmentation_right.for_each_outgoing([&](FactorTypeAdapter* binary, FactorTypeAdapter* connector) {
            lp.BackwardPassFactorRelation(connector, segmentation_left.exactly_one_outgoing);
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

  template<direction DIRECTION = direction::forward>
  void output_graphviz(LP<FMC>& lp, const std::string& filename)
  {
#ifdef NDEBUG
    return;
#endif

    const auto& omega = lp.get_omega();

    //
    // Useless template metaprogramming shizzle.
    //

    auto get_update_ordering = [&lp]()constexpr -> auto& {
      if constexpr (DIRECTION == direction::forward)
        return lp.forwardUpdateOrdering_;
      else
        return lp.backwardUpdateOrdering_;
    };

    auto get_ordering = [&lp]() constexpr -> auto& {
      if constexpr (DIRECTION == direction::forward)
        return lp.forwardOrdering_;
      else
        return lp.backwardOrdering_;
    };

    auto get_omega_send = [&omega]() constexpr -> auto& {
      if constexpr (DIRECTION == direction::forward)
        return omega.forward;
      else
        return omega.backward;
    };

    auto get_omega_recv = [&omega]() constexpr -> auto& {
      if constexpr (DIRECTION == direction::forward)
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

    INDEX i = 0;
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
      if (it != update_index.end()) {
        std::vector<int> tmp_container; // convert `unsigned char` to `int`
        tmp_container.assign(get_omega_send()[it->second].begin(), get_omega_send()[it->second].end());
        s << "s_fw=" << print_container(tmp_container) << "\\n";
        tmp_container.assign(get_omega_recv()[it->second].begin(), get_omega_recv()[it->second].end());
        s << "r_fw=" << print_container(tmp_container) << "\\n";
      }

      s << "θ=";
      if constexpr (std::is_same_v<decltype(f), binary_factor_container*>) {
        s << print_container(*f->GetFactor());
      } else if constexpr (std::is_same_v<decltype(f), exactly_one_factor_container*> || std::is_same_v<decltype(f), exactly_one_minorant_factor_container*>) {
        auto [duals] = f->GetFactor()->export_variables();
        s << print_container(duals);
      } else if constexpr (std::is_same_v<decltype(f), implication_factor_container*>) {
        auto [duals_left, duals_right] = f->GetFactor()->export_variables();
        s << print_container(duals_left) << " + " << print_container(duals_right);
      } else {
        struct assert_not_reached;
        static_assert(std::is_same_v<decltype(f), assert_not_reached>);
      }
      s << "\\n";

      s << "lb=" << f->LowerBound();

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

      return found ? get_omega_send()[update_index.at(f_left)][idx] : 0.0;
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

      return found ? get_omega_recv()[update_index.at(f_right)][idx] : 0.0;
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
            << format_node(segmentation.exactly_one, "=1")
            << format_node(segmentation.exactly_one_incoming, "=1 in")
            << format_node(segmentation.dummy, "dummy seg")
            << format_node(segmentation.exactly_one_outgoing, "=1 out")
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
          o << format_node(exclusion.exactly_one, "=1 ex")
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

#if 0
  enum class factor_type { binary, implication, uniqueness, simple_uniqueness };

  std::map<const FactorTypeAdapter*, factor_type> get_factor_types() const
  {
    std::map<const FactorTypeAdapter*, factor_type> mapping;

    for (auto& timestep : segmentation_infos_) {
      for (auto& segmentation : timestep) {
        mapping[segmentation.detection] = factor_type::binary;
        mapping[segmentation.appearance] = factor_type::binary;
        mapping[segmentation.disappearance] = factor_type::binary;
        mapping[segmentation.dummy_incoming] = factor_type::binary;
        mapping[segmentation.dummy_outgoing] = factor_type::binary;
        mapping[segmentation.exactly_one_incoming] = factor_type::uniqueness;
        mapping[segmentation.exactly_one_incoming_additional] = factor_type::simple_uniqueness;
        mapping[segmentation.exactly_one_outgoing] = factor_type::uniqueness;
        mapping[segmentation.exactly_one_outgoing_additional] = factor_type::simple_uniqueness;

        segmentation.for_each_incoming([&mapping](const FactorTypeAdapter* binary, const FactorTypeAdapter* connector) {
          mapping[binary] = factor_type::binary;
          mapping[connector] = factor_type::implication;
        });

        segmentation.for_each_outgoing([&mapping](const FactorTypeAdapter* binary, const FactorTypeAdapter* connector) {
          mapping[binary] = factor_type::binary;
          mapping[connector] = factor_type::implication;
        });
      }
    }

#ifndef NDEBUG
    for (INDEX i = 0; i < lp_->GetNumberOfFactors(); ++i)
      assert(mapping.find(lp_->GetFactor(i)) != mapping.end());
#endif
  }
#endif

  void fix_omegas()
  {
    lp_->set_reparametrization(LPReparametrizationMode::Anisotropic2);
    auto omegas = lp_->get_omega();
    auto forward_update_indices = lp_->get_forward_update_indices();
    auto backward_update_indices = lp_->get_backward_update_indices();

    lp_->for_each_factor([&](auto* f) {
      if constexpr (std::is_same_v<decltype(f), exactly_one_minorant_factor_container*>) {
        for (auto& x : omegas.receive_mask_forward[forward_update_indices.at(f)])
          x = 1;
        for (auto& x : omegas.receive_mask_backward[backward_update_indices.at(f)])
          x = 1;
      }
    });
  }

  void set_direction(direction d)
  {
    direction_ = d;
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
    binary_factor_container* dummy;
    exactly_one_minorant_factor_container* exactly_one;
    edge_info appearance;
    edge_info disappearance;
    std::vector<edge_info> incoming_transitions;
    std::vector<edge_info> incoming_divisions;
    std::vector<edge_info> outgoing_transitions;
    std::vector<edge_info> outgoing_divisions;
    exactly_one_minorant_factor_container* exactly_one_incoming;
    exactly_one_minorant_factor_container* exactly_one_outgoing;

    template<typename FUNCTOR>
    void for_each_incoming(FUNCTOR func) {
      func(dummy, exactly_one);
      func(appearance.binary, appearance.implication);
      for (auto e : incoming_transitions)
        func(e.binary, e.implication);
      for (auto e : incoming_divisions)
        func(e.binary, e.implication);
    };

    template<typename FUNCTOR>
    void for_each_outgoing(FUNCTOR func) {
      func(dummy, exactly_one);
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
  direction direction_;
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

#if 0
class My_LP : public LP<FMC_MY> {
private:
  using Parent = LP<FMC_MY>;

public:
  using Parent::Parent;

  omega_storage get_omega3() // override
  {
    std::cout << __PRETTY_FUNCTION__ << std::endl;

    SortFactors();
    switch (repamMode_) {
      case LPReparametrizationMode::Anisotropic:
        if(!omega_anisotropic_valid_) {
          ComputeAnisotropicWeights();
          omega_anisotropic_valid_ = true;
        }
        return omega_storage{omegaForwardAnisotropic_, omegaBackwardAnisotropic_, anisotropic_receive_mask_forward_, anisotropic_receive_mask_backward_};
      case LPReparametrizationMode::DampedUniform:
        if(!omega_isotropic_damped_valid_) {
          ComputeDampedUniformWeights();
          omega_isotropic_damped_valid_ = true;
        }
        if(!full_receive_mask_valid_) {
          compute_full_receive_mask();
          full_receive_mask_valid_ = true;
        }
        return omega_storage{omegaForwardIsotropicDamped_, omegaBackwardIsotropicDamped_, full_receive_mask_forward_, full_receive_mask_backward_};
      default:
        throw std::runtime_error("Unknown reparametrization");
    }
  }

  void ComputeAnisotropicWeights3()
  {
    std::cout << __PRETTY_FUNCTION__ << std::endl;

    ComputeAnisotropicWeights(forwardOrdering_.begin(), forwardOrdering_.end(), omegaForwardAnisotropic_, anisotropic_receive_mask_forward_);
    ComputeAnisotropicWeights(backwardOrdering_.begin(), backwardOrdering_.end(), omegaBackwardAnisotropic_, anisotropic_receive_mask_backward_);

    omega_valid(omegaForwardAnisotropic_);
    omega_valid(omegaBackwardAnisotropic_);
  }

  template<typename FACTOR_ITERATOR>
  void ComputeAnisotropicWeights3( FACTOR_ITERATOR factorIt, FACTOR_ITERATOR factorEndIt, weight_array& omega, receive_array& receive_mask)
  {
    std::cout << __PRETTY_FUNCTION__ << std::endl;

    //const auto n = std::distance(factorIt,factorEndIt);
    //assert(n <= f_.size());

    auto factor_address_to_sorted_index = get_factor_indices(factorIt, factorEndIt); 
    //auto factor_types = this->GetProblemConstructor<0>().get_factor_types();

    omega = allocate_omega(factorIt, factorEndIt);
    receive_mask = allocate_receive_mask(factorIt, factorEndIt);
  }
};
#endif

}

using namespace LP_MP;

int main(int argc, char** argv) {
#if 1
  using BaseSolver = Solver<LP<FMC_MY>, StandardVisitor>;
  //MpRoundingSolver<BaseSolver> solver(argc, argv);
  BaseSolver solver(argc, argv);
  solver.ReadProblem(cell_tracking_parser_2d::ParseProblem<BaseSolver>);
  solver.GetProblemConstructor<0>().fix_omegas();
  auto& lp = solver.GetLP();

#if 1
  lp.Begin();
  lp.set_reparametrization(LPReparametrizationMode::Anisotropic2);
  for (int i = 0; i < 100; ++i) {
    std::cout << "iteration " << i << ": ";
    std::cout << "fw -> ";
    solver.GetProblemConstructor<0>().set_direction(direction::forward);
    lp.ComputeForwardPass();
    std::cout << lp.LowerBound() << " / bw -> ";
    solver.GetProblemConstructor<0>().set_direction(direction::backward);
    lp.ComputeBackwardPass();
    std::cout << lp.LowerBound() << std::endl;
  }
#else
  // DOES NOT WORK, AS Ctor.set_direction IS NOT CALLED.
  solver.Solve();
#endif
#elif 0
  using BaseSolver = Solver<LP_external_solver<DD_ILP::gurobi_interface, LP<FMC_MY>>, StandardVisitor>;
  BaseSolver solver(argc, argv);
  solver.ReadProblem(cell_tracking_parser_2d::ParseProblem<BaseSolver>);
  solver.GetLP().write_to_file("/tmp/my.lp");
  solver.GetLP().solve();
#else
  std::mt19937 rng;
  rng.seed(std::random_device()());
  std::uniform_real_distribution<double> dist(-200.0, 200.0);

  using BaseSolver = Solver<LP<FMC_MY>, StandardVisitor>;
  MpRoundingSolver<BaseSolver> solver(argc, argv);

  auto& lp = solver.GetLP();
  auto* f0 = lp.template add_factor<FMC_MY::binary_factor_container>();
  auto* f1 = lp.template add_factor<FMC_MY::binary_factor_container>();
  auto* f2 = lp.template add_factor<FMC_MY::binary_factor_container>();
  auto* f3 = lp.template add_factor<FMC_MY::exactly_one_minorant_factor_container>(3, [](INDEX i) {
    std::cout << "lambda(" << i << ")" << std::endl;
    return i == 0 ? false : true;
  });

  (*f0->GetFactor())[0] = dist(rng);
  (*f0->GetFactor())[1] = dist(rng);

  (*f1->GetFactor())[0] = dist(rng);
  (*f1->GetFactor())[1] = dist(rng);

  (*f2->GetFactor())[0] = dist(rng);
  (*f2->GetFactor())[1] = dist(rng);

  f3->GetFactor()->dual(0, false) = dist(rng);
  f3->GetFactor()->dual(0, true)  = dist(rng);
  f3->GetFactor()->dual(1, false) = dist(rng);
  f3->GetFactor()->dual(1, true)  = dist(rng);
  f3->GetFactor()->dual(2, false) = dist(rng);
  f3->GetFactor()->dual(2, true)  = dist(rng);

  std::cout << print_container(*(f0->GetFactor())) << std::endl;
  std::cout << print_container(*(f1->GetFactor())) << std::endl;
  std::cout << print_container(*(f2->GetFactor())) << std::endl;
  std::cout << print_container(f3->GetFactor()->duals_) << std::endl;

  lp.template add_message<FMC_MY::exactly_one_minorant_message_container>(f0, f3, 0);
  lp.template add_message<FMC_MY::exactly_one_minorant_message_container>(f1, f3, 1);
  lp.template add_message<FMC_MY::exactly_one_minorant_message_container>(f2, f3, 2);

  lp.AddAsymmetricFactorRelation(f3, f0);
  lp.AddAsymmetricFactorRelation(f3, f1);
  lp.AddAsymmetricFactorRelation(f3, f2);
  lp.AddFactorRelation(f0, f1);
  lp.AddFactorRelation(f1, f2);

  lp.Begin();
  lp.set_reparametrization(LPReparametrizationMode::Anisotropic2);
  auto omega = lp.get_omega();
  omega.receive_mask_forward[0][0] = 1;
  omega.receive_mask_forward[0][1] = 1;
  omega.receive_mask_forward[0][2] = 1;
  lp.ComputeForwardPass();

  std::cout << print_container(*(f0->GetFactor())) << std::endl;
  std::cout << print_container(*(f1->GetFactor())) << std::endl;
  std::cout << print_container(*(f2->GetFactor())) << std::endl;
  std::cout << print_container(f3->GetFactor()->duals_) << std::endl;
#endif
}
