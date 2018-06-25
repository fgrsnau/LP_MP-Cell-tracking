#include <cxxabi.h>
#include <random>
#include <utility>

#include "LP_MP.h"
#include "factors_messages.hxx"
#include "visitors/standard_visitor.hxx"
#include "solver.hxx"

#include "cell_tracking_constructor.hxx"

namespace LP_MP {

template<typename CHECK> struct get_type;

enum class direction { forward, backword };

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

class detection_factor {
public:
  detection_factor(REAL detection_cost, REAL appearance_cost, REAL disappearance_cost, INDEX no_incoming, INDEX no_outgoing)
  : no_incoming_(no_incoming)
  , no_outgoing_(no_outgoing)
  , duals_(dual_idx<dual_selector::size>(0))
  {
    dual_detection() = detection_cost;
    dual_appearance() = appearance_cost;
    dual_disappearance() = disappearance_cost;
  }

  void init_primal() { }

  REAL LowerBound() const {
    return std::min(min_detection(), 0.0);
  }

  REAL EvaluatePrimal() const {
    return 0;
  }

  template<typename ARCHIVE>
  void serialize_primal(ARCHIVE& a) { }

  template<typename ARCHIVE>
  void serialize_dual(ARCHIVE& a) { a(duals_); }

  auto export_variables() { return std::tie(duals_); }

  template<typename SOLVER>
  void construct_constraints(SOLVER& s, typename SOLVER::vector& v) const { }

  template<typename SOLVER>
  void convert_primal(SOLVER& s, typename SOLVER::vector& v) { }

  REAL min_incoming() const {
    REAL x = dual_appearance();
    for (INDEX i = 0; i < no_incoming_; ++i)
      x = std::min(x, dual_incoming(i));
    return x;
  };

  REAL min_marginal_incoming(INDEX i) const {
    return dual_detection() + min_outgoing() + dual_incoming(i);
  }

  REAL min_outgoing() const {
    REAL x = dual_disappearance();
    for (INDEX i = 0; i < no_outgoing_; ++i)
      x = std::min(x, dual_outgoing(i));
    return x;
  }

  REAL min_marginal_outgoing(INDEX i) const {
    return dual_detection() + min_incoming() + dual_outgoing(i);
  }

  REAL min_detection() const {
    return min_incoming() + dual_detection() + min_outgoing();
  }

  REAL min_marginal_detection() const { return min_detection(); }

  const REAL& dual_detection() const { return duals_[dual_idx<dual_selector::detection>(0)]; }
  const REAL& dual_appearance() const { return duals_[dual_idx<dual_selector::appearance>(0)]; }
  const REAL& dual_disappearance() const { return duals_[dual_idx<dual_selector::disappearance>(0)]; }
  const REAL& dual_incoming(INDEX i) const { return duals_[dual_idx<dual_selector::incoming>(i)]; }
  const REAL& dual_outgoing(INDEX i) const { return duals_[dual_idx<dual_selector::outgoing>(i)]; }

  REAL& dual_detection() { return duals_[dual_idx<dual_selector::detection>(0)]; }
  REAL& dual_appearance() { return duals_[dual_idx<dual_selector::appearance>(0)]; }
  REAL& dual_disappearance() { return duals_[dual_idx<dual_selector::disappearance>(0)]; }
  REAL& dual_incoming(INDEX i) { return duals_[dual_idx<dual_selector::incoming>(i)]; }
  REAL& dual_outgoing(INDEX i) { return duals_[dual_idx<dual_selector::outgoing>(i)]; }

protected:
  enum class dual_selector { detection, appearance, disappearance, incoming, outgoing, size };
  template<dual_selector SELECTOR>
  size_t dual_idx(INDEX i) const {
    assert(i >= 0);
    size_t offset = 0;
    if constexpr (SELECTOR == dual_selector::detection) {
      assert(i == 0);
      return offset;
    }
    offset += 1;

    if constexpr (SELECTOR == dual_selector::appearance) {
      assert(i == 0);
      return offset;
    }
    offset += 1;

    if constexpr (SELECTOR == dual_selector::disappearance) {
      assert(i == 0);
      return offset;
    }
    offset += 1;

    if constexpr (SELECTOR == dual_selector::incoming) {
      assert(i < no_incoming_);
      return offset + i;
    }
    offset += no_incoming_;

    if constexpr (SELECTOR == dual_selector::outgoing) {
      assert(i < no_outgoing_);
      return offset + i;
    }
    offset += no_outgoing_;

    if constexpr (SELECTOR == dual_selector::size) {
      return offset;
    }
  };

  INDEX no_incoming_;
  INDEX no_outgoing_;

  vector<REAL> duals_;

  friend class transition_message;
  friend class at_most_one_cell_message;
};

class at_most_one_cell_factor {
public:
  at_most_one_cell_factor(INDEX no_neighbors)
  : constant_(0)
  , duals_(no_neighbors)
  { }

  void init_primal() { }

  REAL LowerBound() const {
    return std::min(duals_.min(), 0.0) + constant_;
  }

  REAL EvaluatePrimal() const {
    return 0;
  }

  void MaximizePotential() {
#ifndef NDEBUG
    std::vector<REAL> old(duals_.begin(), duals_.end());
    for (auto& x : old) x += constant_;
#endif

    auto argmin1 = std::min_element(duals_.begin(), duals_.end());
    auto min1 = *argmin1;
    *argmin1 = std::numeric_limits<REAL>::infinity();
    auto argmin2 = std::min_element(duals_.begin(), duals_.end());
    auto min2 = *argmin2;
    auto diff = min2 - min1;

    constant_ += min1 + diff/2.0;
    *argmin1 = -diff/2.0;
    *argmin2 = diff/2.0;

    for (auto it = duals_.begin(); it != duals_.end(); ++it) {
      if (it != argmin1 && it != argmin2) {
        *it -= min1 + diff/2.0;
      }
    }

#ifndef NDEBUG
    for (INDEX i = 0; i < duals_.size(); ++i)
      assert(std::abs(duals_[i] + constant_ - old[i]) < eps);
#endif
  }

  void MaximizePotentialAndComputePrimal() {
    MaximizePotential();
  }

  template<typename ARCHIVE>
  void serialize_primal(ARCHIVE& a) { }

  template<typename ARCHIVE>
  void serialize_dual(ARCHIVE& a) { a(duals_); }

  auto export_variables() { return std::tie(duals_); }

  template<typename SOLVER>
  void construct_constraints(SOLVER& s, typename SOLVER::vector& v) const { }

  template<typename SOLVER>
  void convert_primal(SOLVER& s, typename SOLVER::vector& v) { }

protected:
  REAL constant_;
  vector<REAL> duals_;

  friend class transition_message;
  friend class at_most_one_cell_message;
};

class transition_message {
public:
  transition_message(bool split, INDEX from, INDEX to)
  : split_(split)
  , from_(from)
  , to_(to)
  {
  }

  template<typename LEFT_FACTOR, typename G2>
  void send_message_to_right(LEFT_FACTOR& l, G2& msg, const REAL omega)
  {
    assert(from_ >= 0 && from_ < l.no_outgoing_);
    //std::cout << __PRETTY_FUNCTION__ << "\n" << "msg[0] -= " << l.min_marginal_outgoing(from_) * (split_ ? 0.5 : 1.0) << std::endl;
    msg[0] -= (l.min_marginal_outgoing(from_) - l.LowerBound()) * omega;
  }

  template<typename RIGHT_FACTOR, typename G2>
  void send_message_to_left(RIGHT_FACTOR& r, G2& msg, const REAL omega)
  {
    assert(to_ >= 0 && to_ < r.no_incoming_);
    //std::cout << __PRETTY_FUNCTION__ << "\n" << "msg[0] -= " << r.min_marginal_incoming(to_) << std::endl;
    msg[0] -= (r.min_marginal_incoming(to_) - r.LowerBound()) * omega;
  }

  template<typename LEFT_FACTOR>
  void RepamLeft(LEFT_FACTOR& l, const REAL msg, const INDEX msg_dim)
  {
    assert(msg_dim == 0);
    l.dual_outgoing(from_) += msg;
    //std::cout << __PRETTY_FUNCTION__ << "\n" << "msg = " << msg << std::endl;
  }

  template<typename RIGHT_FACTOR>
  void RepamRight(RIGHT_FACTOR& r, const REAL msg, const INDEX msg_dim)
  {
    assert(msg_dim == 0);
    r.dual_incoming(to_) += msg;
    //std::cout << __PRETTY_FUNCTION__ << "\n" << "msg = " << msg << std::endl;
  }

  template<typename SOLVER, typename LEFT_FACTOR, typename RIGHT_FACTOR>
  void construct_constraints(SOLVER& s,
    LEFT_FACTOR& left, typename SOLVER::vector& v1,
    RIGHT_FACTOR& right, typename SOLVER::vector& v2) const { }

protected:
  bool split_;
  INDEX from_;
  INDEX to_;
};

class at_most_one_cell_message {
public:
  at_most_one_cell_message(INDEX index)
  : index_(index)
  { }

  template<typename LEFT_FACTOR, typename G2>
  void send_message_to_right(LEFT_FACTOR& l, G2& msg, const REAL omega)
  {
    msg[0] -= l.min_marginal_detection();
  }

  template<typename RIGHT_FACTOR, typename G2>
  void send_message_to_left(RIGHT_FACTOR& r, G2& msg, const REAL omega)
  {
    assert(index_ >= 0 && index_ < r.duals_.size());
    msg[0] -= r.duals_[index_];
  }

  template<typename LEFT_FACTOR>
  void RepamLeft(LEFT_FACTOR& l, const REAL msg, const INDEX msg_dim)
  {
    assert(msg_dim == 0);
    l.dual_detection() += msg;
  }

  template<typename RIGHT_FACTOR>
  void RepamRight(RIGHT_FACTOR& r, const REAL msg, const INDEX msg_dim)
  {
    assert(msg_dim == 0);
    assert(index_ >= 0 && index_ < r.duals_.size());
    r.duals_[index_] += msg;
  }

  template<typename SOLVER, typename LEFT_FACTOR, typename RIGHT_FACTOR>
  void construct_constraints(SOLVER& s,
    LEFT_FACTOR& left, typename SOLVER::vector& v1,
    RIGHT_FACTOR& right, typename SOLVER::vector& v2) const { }

protected:
  INDEX index_;
};

template<typename FMC_T>
class my_tracking_constructor {
public:
  using FMC = FMC_T;

  using detection_factor_container = typename FMC::detection_factor_container;
  using at_most_one_cell_factor_container = typename FMC::at_most_one_cell_factor_container;
  using transition_message_container = typename FMC::transition_message_container;
  using at_most_one_cell_message_container = typename FMC::at_most_one_cell_message_container;

  constexpr bool accept(INDEX timestep, INDEX hypothesis_id)
  {
#if 0
    if (! (timestep >= 0 && timestep <= 3))
      return false;

    //if (! (hypothesis_id >= 0 && hypothesis_id <= 2))
    //  return false;
#endif

    return true;
  }

  template<typename SOLVER>
  my_tracking_constructor(SOLVER& solver)
  : lp_(&solver.GetLP())
  {}

  void set_number_of_timesteps(const INDEX t)
  {
    assert(detections_.size() == 0);
    detections_.resize(t);
    exclusions_.resize(t);
  }

  void add_detection_hypothesis(LP<FMC>& lp,
    const INDEX timestep, const INDEX hypothesis_id,
    const REAL detection_cost, const REAL appearance_cost, const REAL disappearance_cost,
    const INDEX no_incoming_transitions, const INDEX no_incoming_divisions,
    const INDEX no_outgoing_transitions, const INDEX no_outgoing_divisions)
  {
    if (!accept(timestep, hypothesis_id))
      return;

    assert(timestep < detections_.size());
    if (hypothesis_id >= detections_[timestep].size())
      detections_[timestep].resize(hypothesis_id+1);
    assert(detections_[timestep][hypothesis_id] == nullptr);
    if (hypothesis_id > 0)
      assert(detections_[timestep][hypothesis_id-1] != nullptr);

    auto* f = lp.template add_factor<detection_factor_container>(
      detection_cost, appearance_cost, disappearance_cost,
      no_incoming_transitions + no_incoming_divisions,
      no_outgoing_transitions + no_outgoing_divisions);
    detections_[timestep][hypothesis_id] = f;
  }

  void add_cell_transition(LP<FMC>& lp,
    const INDEX timestep_prev, const INDEX hypothesis_prev,
    const INDEX timestep_next, const INDEX hypothesis_next,
    const REAL cost)
  {
    if (!accept(timestep_prev, hypothesis_prev) || !accept(timestep_next, hypothesis_next))
      return;

    auto* factor_prev = detections_[timestep_prev][hypothesis_prev];
    auto& counters_prev = factor_counters_[factor_prev];

    auto* factor_next = detections_[timestep_next][hypothesis_next];
    auto& counters_next = factor_counters_[factor_next];

    factor_prev->GetFactor()->dual_outgoing(counters_prev.second) = cost;
    lp.template add_message<transition_message_container>(factor_prev, factor_next, false, counters_prev.second++, counters_next.first++);

    lp.AddFactorRelation(factor_prev, factor_next);
  }

  void add_cell_division(LP<FMC>& lp,
    const INDEX timestep_prev, const INDEX hypothesis_prev,
    const INDEX timestep_next_1, const INDEX hypothesis_next_1,
    const INDEX timestep_next_2, const INDEX hypothesis_next_2,
    const REAL cost)
  {
    if (!accept(timestep_prev, hypothesis_prev) || !accept(timestep_next_1, hypothesis_next_1) || !accept(timestep_next_2, hypothesis_next_2))
      return;

    auto* factor_prev = detections_[timestep_prev][hypothesis_prev];
    auto& counters_prev = factor_counters_[factor_prev];

    auto* factor_next_1 = detections_[timestep_next_1][hypothesis_next_1];
    auto& counters_next_1 = factor_counters_[factor_next_1];

    auto* factor_next_2 = detections_[timestep_next_2][hypothesis_next_2];
    auto& counters_next_2 = factor_counters_[factor_next_2];

    factor_prev->GetFactor()->dual_outgoing(counters_prev.second) = cost;
    lp.template add_message<transition_message_container>(factor_prev, factor_next_1, true, counters_prev.second, counters_next_1.first++);
    lp.template add_message<transition_message_container>(factor_prev, factor_next_2, true, counters_prev.second++, counters_next_2.first++);

    lp.AddFactorRelation(factor_prev, factor_next_1);
    lp.AddFactorRelation(factor_prev, factor_next_2);
  }

  template<typename ITERATOR>
  void add_exclusion_constraint(LP<FMC>& lp, ITERATOR begin, ITERATOR end) // iterator points to std::array<INDEX,2>
  {
    for (auto it = begin; it != end; ++it)
      if (!accept(it->operator[](0), it->operator[](1)))
        return;

    const INDEX timestep = (*begin)[0];
    exclusions_[timestep].emplace_back();
    auto& exclusion = exclusions_[timestep].back();
    exclusion.timestep = timestep;

    const size_t n = end - begin;
    exclusion.at_most_one = lp.template add_factor<at_most_one_cell_factor_container>(n);

    INDEX idx = 0;
    for (auto it = begin; it != end; ++it) {
      assert((*it)[0] == timestep);
      const INDEX hypothesis_id = (*it)[1];
      auto* f = detections_[timestep][hypothesis_id];
      lp.template add_message<at_most_one_cell_message_container>(f, exclusion.at_most_one, idx++);
      exclusion.segmentations.push_back(hypothesis_id);

      lp.AddAsymmetricFactorRelation(exclusion.at_most_one, f);
    }
    assert(idx == n);
  }

  void begin(LP<FMC>& lp, const std::size_t no_cell_detection_hypotheses, const std::size_t no_transitions, const std::size_t no_divisions)
  {
  }

  void end(LP<FMC>& lp)
  {
    for (auto& timestep : exclusions_) {
      for (auto& exclusion : timestep) {
        if (exclusion.timestep > 0)
          for (auto& detection : detections_[exclusion.timestep-1])
            lp.AddFactorRelation(detection, exclusion.at_most_one);

        if (exclusion.timestep + 1 < exclusions_.size())
          for (auto& detection : detections_[exclusion.timestep+1])
            lp.AddFactorRelation(exclusion.at_most_one, detection);
      }
    }
  }

  template<direction DIRECTION = direction::forward>
  void output_graphviz(LP<FMC>& lp, const std::string& filename)
  {
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
        std::vector<REAL> tmp_container; // convert `unsigned char` to `REAL`
        tmp_container.assign(get_omega_send()[it->second].begin(), get_omega_send()[it->second].end());
        s << "s_fw=" << print_container(tmp_container) << "\\n";
        tmp_container.assign(get_omega_recv()[it->second].begin(), get_omega_recv()[it->second].end());
        s << "r_fw=" << print_container(tmp_container) << "\\n";
      }

      s << "θ=";
      auto [duals] = f->GetFactor()->export_variables();
      s << print_container(duals);
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
      for (size_t timestep = 0; timestep < detections_.size(); ++timestep) {
        for (size_t hypothesis_id = 0; hypothesis_id < detections_[timestep].size(); ++hypothesis_id) {
          auto det_label = [&]() {
            std::stringstream s;
            s << "det(" << timestep << "," << hypothesis_id << ")";
            return s.str();
          };

          auto* detection = detections_[timestep][hypothesis_id];
          o << format_node(detection, det_label());
        }
      }

      for (const auto& timestep : exclusions_) {
        for (const auto& exclusion : timestep) {
          o << format_node(exclusion.at_most_one, "≤1");
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

  void fix_omegas()
  {
    auto omegas = lp_->get_omega();
    auto forward_update_indices = lp_->get_forward_update_indices();
    auto backward_update_indices = lp_->get_backward_update_indices();

    lp_->for_each_factor([&](auto* f) {
      if constexpr (std::is_same_v<decltype(f), at_most_one_cell_factor_container*>) {
        for (auto& x : omegas.receive_mask_forward[forward_update_indices.at(f)])
          x = 1;
        for (auto& x : omegas.receive_mask_backward[backward_update_indices.at(f)])
          x = 1;
      }
    });
  }

  // FIXME: We don't need this, but dictated by interface for now.
  std::vector<std::size_t> cumulative_sum_cell_detection_factors;

protected:
  using detection_storage = std::vector<std::vector<detection_factor_container*>>;
  detection_storage detections_;

  struct exclusion {
    at_most_one_cell_factor_container* at_most_one;
    INDEX timestep;
    std::vector<INDEX> segmentations;
  };

  using exclusion_storage = std::vector<std::vector<exclusion>>;
  exclusion_storage exclusions_;

  std::map<FactorTypeAdapter*, std::pair<INDEX, INDEX>> factor_counters_;

  LP<FMC>* lp_;
};

struct FMC_MY {
  constexpr static const char* name = "My Cell Tracking";
  using FMC = FMC_MY;

  using detection_factor_container = FactorContainer<detection_factor, FMC, 0, false>;
  using at_most_one_cell_factor_container = FactorContainer<at_most_one_cell_factor, FMC, 1, false>;
  using FactorList = meta::list<
    detection_factor_container,
    at_most_one_cell_factor_container>;

  using transition_message_container = MessageContainer<transition_message, 0, 0, message_passing_schedule::only_send, variableMessageNumber, variableMessageNumber, FMC, 0>;
  using at_most_one_cell_message_container = MessageContainer<at_most_one_cell_message, 0, 1, message_passing_schedule::right, variableMessageNumber, variableMessageNumber, FMC, 1>;
  using MessageList = meta::list<
    transition_message_container,
    at_most_one_cell_message_container>;

  using ProblemDecompositionList = meta::list<my_tracking_constructor<FMC>>;
};

}

using namespace LP_MP;

void test_uniform_minorant()
{
  std::random_device rd;
  decltype(rd)::result_type seed = rd();
  std::default_random_engine generator(seed);
  std::uniform_int_distribution<int> uniform(-200, 200);
  auto r = [&generator, &uniform]() { return uniform(generator); };

  Solver<LP<FMC_MY>, StandardVisitor> solver;
  auto& lp = solver.GetLP();
  auto* f0 = lp.template add_factor<FMC_MY::detection_factor_container>(r(), r(), r(), 0, 0);
  auto* f1 = lp.template add_factor<FMC_MY::detection_factor_container>(r(), r(), r(), 0, 0);

#if 0
  auto [f0_var] = f0->GetFactor()->export_variables();
  auto [f1_var] = f1->GetFactor()->export_variables();
  std::cout << print_container(f0_var) << " / " << print_container(f1_var) << std::endl;
#endif

  auto* m0 = lp.template add_factor<FMC_MY::at_most_one_cell_factor_container>(2);
  for (auto& x: std::get<0>(m0->GetFactor()->export_variables()))
    x = r();

  lp.template add_message<FMC_MY::at_most_one_cell_message_container>(f0, m0, 0);
  lp.template add_message<FMC_MY::at_most_one_cell_message_container>(f1, m0, 1);

  lp.Begin();
  lp.set_reparametrization(LPReparametrizationMode::Anisotropic2);
  for (int i = 0; i < 100; ++i) {
    REAL before_lb = lp.LowerBound();
    if (i % 2 == 0)
      lp.ComputeForwardPass();
    else
      lp.ComputeBackwardPass();
    REAL after_lb = lp.LowerBound();
    assert(before_lb <= after_lb + eps);
  }
}

void test_transition_normal()
{
  std::random_device rd;
  decltype(rd)::result_type seed = rd();
  std::default_random_engine generator(seed);
  std::uniform_int_distribution<int> uniform(-200, 200);
  auto r = [&generator, &uniform]() { return uniform(generator); };

  Solver<LP<FMC_MY>, StandardVisitor> solver;
  auto& lp = solver.GetLP();
  auto* f0 = lp.template add_factor<FMC_MY::detection_factor_container>(r(), r(), r(), 0, 1);
  auto* f1 = lp.template add_factor<FMC_MY::detection_factor_container>(r(), r(), r(), 1, 0);
  f0->GetFactor()->dual_outgoing(0) = r();
  f1->GetFactor()->dual_incoming(0) = r();

#if 0
  auto [f0_var] = f0->GetFactor()->export_variables();
  auto [f1_var] = f1->GetFactor()->export_variables();
  std::cout << seed << " / " << print_container(f0_var) << " / " << print_container(f1_var) << std::endl;
#endif

  lp.template add_message<FMC_MY::transition_message_container>(f0, f1, false, 0, 0);
  lp.AddFactorRelation(f0, f1);

  lp.Begin();
  lp.set_reparametrization(LPReparametrizationMode::Anisotropic2);
  for (int i = 0; i < 100; ++i) {
    REAL before_lb = lp.LowerBound();
    if (i % 2 == 0)
      lp.ComputeForwardPass();
    else
      lp.ComputeBackwardPass();
    REAL after_lb = lp.LowerBound();
    assert(before_lb <= after_lb + eps);
  }
}

void test_transition_split()
{
  std::random_device rd;
  decltype(rd)::result_type seed = rd();
  std::default_random_engine generator(seed);
  std::uniform_int_distribution<int> uniform(-200, 200);
  auto r = [&generator, &uniform]() { return uniform(generator); };

  Solver<LP<FMC_MY>, StandardVisitor> solver;
  auto& lp = solver.GetLP();
  auto* f0 = lp.template add_factor<FMC_MY::detection_factor_container>(r(), r(), r(), 0, 1);
  auto* f1 = lp.template add_factor<FMC_MY::detection_factor_container>(r(), r(), r(), 1, 0);
  auto* f2 = lp.template add_factor<FMC_MY::detection_factor_container>(r(), r(), r(), 1, 0);
  f0->GetFactor()->dual_outgoing(0) = r();
  f1->GetFactor()->dual_incoming(0) = r();
  f2->GetFactor()->dual_incoming(0) = r();

#if 1
  auto [f0_var] = f0->GetFactor()->export_variables();
  auto [f1_var] = f1->GetFactor()->export_variables();
  auto [f2_var] = f2->GetFactor()->export_variables();
  std::cout << seed << " / " << print_container(f0_var) << " / " << print_container(f1_var) << " / " << print_container(f2_var) << std::endl;
#endif

  lp.template add_message<FMC_MY::transition_message_container>(f0, f1, true, 0, 0);
  lp.template add_message<FMC_MY::transition_message_container>(f0, f2, true, 0, 0);
  lp.AddFactorRelation(f0, f1);
  lp.AddFactorRelation(f0, f2);

  lp.Begin();
  lp.set_reparametrization(LPReparametrizationMode::Anisotropic2);
  for (int i = 0; i < 100; ++i) {
    REAL before_lb = lp.LowerBound();
    if (i % 2 == 0)
      lp.ComputeForwardPass();
    else
      lp.ComputeBackwardPass();
    REAL after_lb = lp.LowerBound();
    assert(before_lb <= after_lb + eps);
  }
}

int main(int argc, char** argv) {

#ifndef NDEBUG
  std::cout << "test_uniform_minorant" << std::endl;
  for (int i = 0; i < 10000; ++i)
    test_uniform_minorant();

  std::cout << "test_transition_normal" << std::endl;
  for (int i = 0; i < 10000; ++i)
    test_transition_normal();

  std::cout << "test_transition_split" << std::endl;
  for (int i = 0; i < 10000; ++i)
    test_transition_normal();
#endif

  std::cout << "start!" << std::endl;
  using BaseSolver = Solver<LP<FMC_MY>, StandardVisitor>;
  BaseSolver solver(argc, argv);
  solver.ReadProblem(cell_tracking_parser_2d::ParseProblem<BaseSolver>);
  auto& lp = solver.GetLP();

  lp.set_reparametrization(LPReparametrizationMode::Anisotropic);
  solver.GetProblemConstructor<0>().fix_omegas();

  lp.set_reparametrization(LPReparametrizationMode::Anisotropic2);
  solver.GetProblemConstructor<0>().fix_omegas();

#ifndef NDEBUG
  solver.GetProblemConstructor<0>().output_graphviz(solver.GetLP(), "graph.dot");
#endif

#if 0
  lp.Begin();
  lp.set_reparametrization(LPReparametrizationMode::Anisotropic2);
  std::cout << lp.LowerBound() << std::endl;
  lp.ComputeForwardPass();
  solver.GetProblemConstructor<0>().output_graphviz(solver.GetLP(), "graph.dot");
  std::cout << lp.LowerBound() << std::endl;

  //lp.ComputeBackwardPass();

#else
  solver.Solve();
#endif
}

