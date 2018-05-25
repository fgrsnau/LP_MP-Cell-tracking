#include "cell_tracking.h"
#include "visitors/standard_visitor.hxx"
#include "LP_external_interface.hxx"
#include "gurobi_interface.hxx"

namespace LP_MP {

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

protected:
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

  template<typename LP_TYPE>
  void add_detection_hypothesis(LP_TYPE& lp,
    const INDEX timestep, const INDEX hypothesis_id,
    const REAL detection_cost, const REAL appearance_cost, const REAL disappearance_cost,
    const INDEX no_incoming_transition_edges, const INDEX no_incoming_division_edges,
    const INDEX no_outgoing_transition_edges, const INDEX no_outgoing_division_edges)
  {
    assert(timestep < segmentation_infos_.size());
    if (hypothesis_id >= segmentation_infos_[timestep].size())
      segmentation_infos_[timestep].resize(hypothesis_id+1);
    assert(segmentation_infos_[timestep][hypothesis_id].detection == nullptr);
    if (hypothesis_id > 0)
      assert(segmentation_infos_[timestep][hypothesis_id-1].detection != nullptr);

    auto& fs = segmentation_infos_[timestep][hypothesis_id];
    fs.detection = lp.template add_factor<binary_factor_container>(detection_cost);
    fs.appearance = lp.template add_factor<binary_factor_container>(appearance_cost);
    fs.disappearance = lp.template add_factor<binary_factor_container>(disappearance_cost);

    auto* f_appearance_implication = lp.template add_factor<implication_factor_container>();
    lp.template add_message<implication_left_message_container>(fs.appearance, f_appearance_implication);
    lp.template add_message<implication_right_message_container>(fs.detection, f_appearance_implication);

    auto* f_disappearance_implication = lp.template add_factor<implication_factor_container>();
    lp.template add_message<implication_left_message_container>(fs.disappearance, f_disappearance_implication);
    lp.template add_message<implication_right_message_container>(fs.detection, f_disappearance_implication);

#ifndef NDEBUG
    fs.no_incoming_divisions = no_incoming_division_edges;
    fs.no_incoming_transitions = no_incoming_transition_edges;
    fs.no_outgoing_divisions = no_outgoing_division_edges;
    fs.no_outgoing_transitions = no_outgoing_transition_edges;
#endif
  }

  template<typename LP_TYPE>
  void add_cell_transition(LP_TYPE& lp,
    const INDEX timestep_prev, const INDEX prev_cell,
    const INDEX timestep_next, const INDEX next_cell,
    const REAL cost)
  {
    auto& prev_factors = segmentation_infos_[timestep_prev][prev_cell];
    auto& next_factors = segmentation_infos_[timestep_next][next_cell];

    auto* f_transition = lp.template add_factor<binary_factor_container>(cost);
    auto* f_left_implication = lp.template add_factor<implication_factor_container>();
    auto* f_right_implication = lp.template add_factor<implication_factor_container>();

    lp.template add_message<implication_left_message_container>(f_transition, f_left_implication);
    lp.template add_message<implication_right_message_container>(prev_factors.detection, f_left_implication);

    lp.template add_message<implication_left_message_container>(f_transition, f_right_implication);
    lp.template add_message<implication_right_message_container>(next_factors.detection, f_right_implication);

    prev_factors.outgoing_transitions.push_back(f_transition);
    next_factors.incoming_transitions.push_back(f_transition);
  }

  template<typename LP_TYPE>
  void add_cell_division(LP_TYPE& lp,
    const INDEX timestep_prev, const INDEX prev_cell,
    const INDEX timestep_next_1, const INDEX next_cell_1,
    const INDEX timestep_next_2, const INDEX next_cell_2,
    const REAL cost)
  {
    auto& prev_factors = segmentation_infos_[timestep_prev][prev_cell];
    auto& next_factors_1 = segmentation_infos_[timestep_next_1][next_cell_1];
    auto& next_factors_2 = segmentation_infos_[timestep_next_2][next_cell_2];

    auto* f_division = lp.template add_factor<binary_factor_container>(cost);
    auto* f_left_implication = lp.template add_factor<implication_factor_container>();
    auto* f_right_implication_1 = lp.template add_factor<implication_factor_container>();
    auto* f_right_implication_2 = lp.template add_factor<implication_factor_container>();

    lp.template add_message<implication_left_message_container>(f_division, f_left_implication);
    lp.template add_message<implication_right_message_container>(prev_factors.detection, f_left_implication);

    lp.template add_message<implication_left_message_container>(f_division, f_right_implication_1);
    lp.template add_message<implication_right_message_container>(next_factors_1.detection, f_right_implication_1);

    lp.template add_message<implication_left_message_container>(f_division, f_right_implication_2);
    lp.template add_message<implication_right_message_container>(next_factors_2.detection, f_right_implication_2);

    prev_factors.outgoing_divisions.push_back(f_division);
    next_factors_1.incoming_divisions.push_back(f_division);
    next_factors_2.incoming_divisions.push_back(f_division);
  }

  template<typename LP_TYPE, typename ITERATOR>
  void add_exclusion_constraint(LP_TYPE& lp, ITERATOR begin, ITERATOR end) // iterator points to std::array<INDEX,2>
  {
    auto* f_dummy = lp.template add_factor<binary_factor_container>();
    const INDEX n = std::distance(begin, end) + 1;
    const INDEX timestep = (*begin)[0];

    auto* f_eq_1 = lp.template add_factor<exactly_one_minorant_factor_container>(n);

    INDEX idx = 0;
    lp.template add_message<exactly_one_minorant_message_container>(f_dummy, f_eq_1, idx++);
    for (auto it = begin; it != end; ++it) {
      assert(timestep == (*it)[0]);
      const INDEX hypothesis_id = (*it)[1];
      auto* f = segmentation_infos_[timestep][hypothesis_id].detection;
      lp.template add_message<exactly_one_minorant_message_container>(f, f_eq_1, idx++);
    }
    assert(idx == n);
  }

  void begin(LP<FMC>& lp, const std::size_t no_cell_detection_hypotheses, const std::size_t no_transitions, const std::size_t no_divisions)
  {
  }

  void end(LP<FMC>& lp)
  {
    for (auto& timestep : segmentation_infos_) {
      for (auto& segmentation : timestep) {
        assert(segmentation.incoming_divisions.size() == segmentation.no_incoming_divisions);
        assert(segmentation.incoming_transitions.size() == segmentation.no_incoming_transitions);
        assert(segmentation.outgoing_divisions.size() == segmentation.no_outgoing_divisions);
        assert(segmentation.outgoing_transitions.size() == segmentation.no_outgoing_transitions);

        // All incoming appearances, transitions, division + 1 dummy must sum up to 1.
        INDEX idx = 0, size = 2 + segmentation.incoming_transitions.size() + segmentation.incoming_divisions.size();
        auto* f_dummy_in = lp.template add_factor<binary_factor_container>();
        auto* f_in_eq_1 = lp.template add_factor<exactly_one_minorant_factor_container>(size);
        lp.template add_message<exactly_one_minorant_message_container>(f_dummy_in, f_in_eq_1, idx++);
        lp.template add_message<exactly_one_minorant_message_container>(segmentation.appearance, f_in_eq_1, idx++);
        for (auto* f : segmentation.incoming_transitions)
          lp.template add_message<exactly_one_minorant_message_container>(f, f_in_eq_1, idx++);
        for (auto* f : segmentation.incoming_divisions)
          lp.template add_message<exactly_one_minorant_message_container>(f, f_in_eq_1, idx++);
        assert(idx == size);

        // Incoming dummy + segmenation must sum up to 1.
        auto f_dummy_in_eq_1 = lp.template add_factor<exactly_one_factor_container>(2);
        lp.template add_message<exactly_one_message_container>(f_dummy_in, f_dummy_in_eq_1, 0);
        lp.template add_message<exactly_one_message_container>(segmentation.detection, f_dummy_in_eq_1, 1);

        // All outgoing disappearances, transitions, division + 1 dummy must sum up to 1.
        idx = 0;
        size = 2 + segmentation.outgoing_transitions.size() + segmentation.outgoing_divisions.size();
        auto* f_dummy_out = lp.template add_factor<binary_factor_container>();
        auto* f_out_eq_1 = lp.template add_factor<exactly_one_factor_container>(size);
        lp.template add_message<exactly_one_message_container>(f_dummy_out, f_out_eq_1, idx++);
        lp.template add_message<exactly_one_message_container>(segmentation.disappearance, f_out_eq_1, idx++);
        for (auto* f : segmentation.outgoing_transitions)
          lp.template add_message<exactly_one_message_container>(f, f_out_eq_1, idx++);
        for (auto* f : segmentation.outgoing_divisions)
          lp.template add_message<exactly_one_message_container>(f, f_out_eq_1, idx++);
        assert(idx == size);

        // Outgoing dummy + segmenation must sum up to 1.
        auto f_dummy_out_eq_1 = lp.template add_factor<exactly_one_factor_container>(2);
        lp.template add_message<exactly_one_message_container>(f_dummy_out, f_dummy_out_eq_1, 0);
        lp.template add_message<exactly_one_message_container>(segmentation.detection, f_dummy_out_eq_1, 1);
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

public: // FIXME: Make protected after changing API.
  std::vector<std::size_t> cumulative_sum_cell_detection_factors;

protected:
  struct segmentation_info {
    binary_factor_container* detection;
    binary_factor_container* appearance;
    binary_factor_container* disappearance;
    std::vector<binary_factor_container*> incoming_transitions;
    std::vector<binary_factor_container*> incoming_divisions;
    std::vector<binary_factor_container*> outgoing_transitions;
    std::vector<binary_factor_container*> outgoing_divisions;

#ifndef NDEBUG
    INDEX no_incoming_transitions, no_incoming_divisions, no_outgoing_transitions, no_outgoing_divisions;
#endif
  };
  using segmentation_info_storage = std::vector<std::vector<segmentation_info>>;
  segmentation_info_storage segmentation_infos_;

  LP<FMC>* lp_;
};

struct FMC_MY {
  constexpr static const char* name = "My Cell Tracking";
  using FMC = FMC_MY;

  using binary_factor_container = FactorContainer<binary_factor, FMC, 0, true>;
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
  using implication_left_message_container = MessageContainer<implication_message<Chirality::left>, 0, 3, message_passing_schedule::right, variableMessageNumber, variableMessageNumber, FMC, 2>;
  using implication_right_message_container = MessageContainer<implication_message<Chirality::right>, 0, 3, message_passing_schedule::right, variableMessageNumber, variableMessageNumber, FMC, 3>;
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
#if 0
  using BaseSolver = Solver<LP<FMC_MY>, StandardVisitor>;
  MpRoundingSolver<BaseSolver> solver(argc, argv);
  solver.ReadProblem(cell_tracking_parser_2d::ParseProblem<BaseSolver>);
  solver.Solve();
#elif 1
  using BaseSolver = Solver<LP_external_solver<DD_ILP::gurobi_interface, LP<FMC_MY>>, StandardVisitor>;
  BaseSolver solver(argc, argv);
  solver.ReadProblem(cell_tracking_parser_2d::ParseProblem<BaseSolver>);
  solver.GetLP().write_to_file("/tmp/my.lp");
  solver.GetLP().solve();

  solver.GetProblemConstructor<0>().debug();
#else
  using BaseSolver = Solver<LP_external_solver<DD_ILP::gurobi_interface, LP<FMC_MY>>, StandardVisitor>;
  BaseSolver solver(argc, argv);
  auto& lp = solver.GetLP();

  auto* f0 = lp.template add_factor<FMC_MY::binary_factor_container>(0);
  auto* f1 = lp.template add_factor<FMC_MY::binary_factor_container>(10);
  auto* f2 = lp.template add_factor<FMC_MY::exactly_one_minorant_factor_container>(2);
  lp.template add_message<FMC_MY::exactly_one_minorant_message_container>(f0, f2, 0);
  lp.template add_message<FMC_MY::exactly_one_minorant_message_container>(f1, f2, 1);

  auto* f3 = lp.template add_factor<FMC_MY::binary_factor_container>(20);
  auto* f4 = lp.template add_factor<FMC_MY::binary_factor_container>(30);
  auto* f5 = lp.template add_factor<FMC_MY::binary_factor_container>(40);
  auto* f6 = lp.template add_factor<FMC_MY::exactly_one_minorant_factor_container>(3);
  lp.template add_message<FMC_MY::exactly_one_minorant_message_container>(f3, f6, 0);
  lp.template add_message<FMC_MY::exactly_one_minorant_message_container>(f4, f6, 1);
  lp.template add_message<FMC_MY::exactly_one_minorant_message_container>(f5, f6, 2);

  solver.GetLP().solve();
#endif
}
