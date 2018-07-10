#include <cxxabi.h>
#include <random>
#include <utility>

#include "LP_MP.h"
#include "factors_messages.hxx"
#include "visitors/standard_visitor.hxx"
#include "solver.hxx"

#include "detection_factor.hxx"
#include "cell_tracking_constructor.hxx"
#include "uniform_minorant.hxx"

namespace LP_MP {

template<typename CHECK> struct get_type;

enum class direction { forward, backword };


enum class dual_selector { detection, appearance, disappearance, incoming, outgoing, size };

template<typename FMC_T>
class my_tracking_constructor {
public:
  using FMC = FMC_T;

  using detection_factor_container = typename FMC::detection_factor_container;
  using at_most_one_cell_factor_container = typename FMC::at_most_one_cell_factor_container;
  using transition_message_container = typename FMC::transition_message_container;
  using at_most_one_cell_message_container = typename FMC::at_most_one_cell_message_container;

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
    assert(timestep < detections_.size());
    if (hypothesis_id >= detections_[timestep].size())
      detections_[timestep].resize(hypothesis_id+1);
    assert(detections_[timestep][hypothesis_id] == nullptr);
    if (hypothesis_id > 0)
      assert(detections_[timestep][hypothesis_id-1] != nullptr);

    auto* f = lp.template add_factor<detection_factor_container>(
      no_incoming_transitions, no_incoming_divisions,
      no_outgoing_transitions, no_outgoing_divisions,
      detection_cost, appearance_cost, disappearance_cost);
    detections_[timestep][hypothesis_id] = f;
    factor_counters_[f].no_incoming_transition_edges = no_incoming_transitions;
    factor_counters_[f].no_incoming_division_edges = no_incoming_divisions;
    factor_counters_[f].no_outgoing_transition_edges = no_outgoing_transitions;
    factor_counters_[f].no_outgoing_division_edges = no_outgoing_divisions;
  }

  void add_cell_transition(LP<FMC>& lp,
    const INDEX timestep_prev, const INDEX hypothesis_prev,
    const INDEX timestep_next, const INDEX hypothesis_next,
    const REAL cost)
  {
    auto* factor_prev = detections_[timestep_prev][hypothesis_prev];
    auto& counters_prev = factor_counters_[factor_prev];

    auto* factor_next = detections_[timestep_next][hypothesis_next];
    auto& counters_next = factor_counters_[factor_next];

    factor_prev->GetFactor()->set_outgoing_transition_cost(counters_prev.no_outgoing_transition_edges, counters_prev.no_outgoing_division_edges, counters_prev.outgoing_transition_edge_count, 0.5 * cost);
    factor_next->GetFactor()->set_incoming_transition_cost(counters_next.no_incoming_transition_edges, counters_next.no_incoming_division_edges, counters_next.incoming_transition_edge_count, 0.5 * cost);
    lp.template add_message<transition_message_container>(factor_prev, factor_next, false, counters_prev.outgoing_transition_edge_count++, counters_next.incoming_transition_edge_count++);

    lp.AddFactorRelation(factor_prev, factor_next);
  }

  void add_cell_division(LP<FMC>& lp,
    const INDEX timestep_prev, const INDEX hypothesis_prev,
    const INDEX timestep_next_1, const INDEX hypothesis_next_1,
    const INDEX timestep_next_2, const INDEX hypothesis_next_2,
    const REAL cost)
  {
    auto* factor_prev = detections_[timestep_prev][hypothesis_prev];
    auto& counters_prev = factor_counters_[factor_prev];

    auto* factor_next_1 = detections_[timestep_next_1][hypothesis_next_1];
    auto& counters_next_1 = factor_counters_[factor_next_1];

    auto* factor_next_2 = detections_[timestep_next_2][hypothesis_next_2];
    auto& counters_next_2 = factor_counters_[factor_next_2];

    factor_prev->GetFactor()->set_outgoing_division_cost(counters_prev.no_outgoing_transition_edges, counters_prev.no_outgoing_division_edges, counters_prev.outgoing_division_edge_count, 1.0/3.0 * cost);
    factor_next_1->GetFactor()->set_incoming_division_cost(counters_next_1.no_incoming_transition_edges, counters_next_1.no_incoming_division_edges, counters_next_1.incoming_division_edge_count, 1.0/3.0 * cost);
    factor_next_2->GetFactor()->set_incoming_division_cost(counters_next_2.no_incoming_transition_edges, counters_next_2.no_incoming_division_edges, counters_next_2.incoming_division_edge_count, 1.0/3.0 * cost);
    lp.template add_message<transition_message_container>(factor_prev, factor_next_1, true, counters_prev.no_outgoing_transition_edges + counters_prev.outgoing_division_edge_count, counters_next_1.no_incoming_transition_edges + counters_next_1.incoming_division_edge_count++);
    lp.template add_message<transition_message_container>(factor_prev, factor_next_2, true, counters_prev.no_outgoing_transition_edges + counters_prev.outgoing_division_edge_count++, counters_next_2.no_incoming_transition_edges + counters_next_2.incoming_division_edge_count++);

    lp.AddFactorRelation(factor_prev, factor_next_1);
    lp.AddFactorRelation(factor_prev, factor_next_2);
  }

  template<typename ITERATOR>
  void add_exclusion_constraint(LP<FMC>& lp, ITERATOR begin, ITERATOR end) // iterator points to std::array<INDEX,2>
  {
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
    assert(idx > 1);
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

    for (auto x : factor_counters_) {
      assert(x.second.no_incoming_transition_edges == x.second.incoming_transition_edge_count);
      assert(x.second.no_incoming_division_edges == x.second.incoming_division_edge_count);
      assert(x.second.no_outgoing_transition_edges == x.second.outgoing_transition_edge_count);
      assert(x.second.no_outgoing_division_edges == x.second.outgoing_division_edge_count);
    }

    for (auto x : {LPReparametrizationMode::Anisotropic, LPReparametrizationMode::Anisotropic2}) {
      lp.set_reparametrization(x);
      fix_omegas();
    }
  }

  template<direction DIRECTION = direction::forward>
  void output_graphviz(LP<FMC>& lp, const std::string& filename)
  {
    const auto& omega = lp.get_omega();

    //
    // Useless template metaprogramming shizzle.
    //

    auto get_update_indices = [&lp]() constexpr {
      if constexpr (DIRECTION == direction::forward)
        return lp.get_forward_update_indices();
      else
        return lp.get_backward_update_indices();
    };

    auto get_ordered_indices = [&lp]() constexpr {
      if constexpr (DIRECTION == direction::forward)
        return lp.get_forward_indices();
      else
        return lp.get_backward_indices();
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

    auto update_indices = get_update_indices();
    auto ordered_indices = get_ordered_indices();

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

      auto it = update_indices.find(f);
      if (it != update_indices.end()) {
        std::vector<REAL> tmp_container; // convert `unsigned char` to `REAL`
        tmp_container.assign(get_omega_send()[it->second].begin(), get_omega_send()[it->second].end());
        s << "s_fw=" << print_container(tmp_container) << "\\n";
        tmp_container.assign(get_omega_recv()[it->second].begin(), get_omega_recv()[it->second].end());
        s << "r_fw=" << print_container(tmp_container) << "\\n";
      }

      s << "θ=";
      //auto [duals] = f->GetFactor()->export_variables();
      //s << print_container(duals);
      s << "\\n";

      s << "lb=" << f->LowerBound();

      return s.str();
    };

    auto format_node = [&](auto* f, std::string label) {
      std::stringstream s;
      s << f_name(f) << " [label=\"";

      auto it = update_indices.find(f);
      if (it != update_indices.end())
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

      return found ? get_omega_send()[update_indices.at(f_left)][idx] : 0.0;
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

      return found ? get_omega_recv()[update_indices.at(f_right)][idx] : 0.0;
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

        if (ordered_indices.at(f_left) > ordered_indices.at(f_right))
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
        for (auto& x : omegas.forward[forward_update_indices.at(f)])
          x = 1.0 / omegas.forward[forward_update_indices.at(f)].size();
        for (auto& x : omegas.backward[backward_update_indices.at(f)])
          x = 1.0 / omegas.backward[backward_update_indices.at(f)].size();
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

  std::unordered_map<FactorTypeAdapter*, cell_tracking_transition_count::edge_type> factor_counters_;

  LP<FMC>* lp_;
};

struct FMC_MY {
  constexpr static const char* name = "My Cell Tracking";
  using FMC = FMC_MY;

  using detection_factor_container = FactorContainer<detection_factor, FMC, 0, false>;
  using at_most_one_cell_factor_container = FactorContainer<uniform_minorant_factor, FMC, 1, false>;
  using FactorList = meta::list<
    detection_factor_container,
    at_most_one_cell_factor_container>;

  using transition_message_container = MessageContainer<transition_message, 0, 0, message_passing_schedule::full, variableMessageNumber, variableMessageNumber, FMC, 0>;
  using at_most_one_cell_message_container = MessageContainer<uniform_minorant_message, 0, 1, message_passing_schedule::right, variableMessageNumber, variableMessageNumber, FMC, 1>;
  using MessageList = meta::list<
    transition_message_container,
    at_most_one_cell_message_container>;

  using ProblemDecompositionList = meta::list<my_tracking_constructor<FMC>>;
};

}

using namespace LP_MP;

auto create_random_cost_functor()
{
  std::random_device rd;
  auto seed = rd();
  std::default_random_engine generator(seed);
  std::uniform_int_distribution<int> uniform(-200, 200);
  return [=]() mutable { return uniform(generator); };
}

void test_uniform_minorant()
{
  auto r = create_random_cost_functor();

  Solver<LP<FMC_MY>, StandardVisitor> solver;
  auto& lp = solver.GetLP();
  auto& ctor = solver.GetProblemConstructor<0>();

  ctor.set_number_of_timesteps(1);
  ctor.add_detection_hypothesis(lp, 0, 0, r(), r(), r(), 0, 0, 0, 0);
  ctor.add_detection_hypothesis(lp, 0, 1, r(), r(), r(), 0, 0, 0, 0);

  std::array<std::array<INDEX, 2>, 2> exclusions;
  exclusions[0] = {0, 0};
  exclusions[1] = {0, 1};
  ctor.add_exclusion_constraint(lp, exclusions.begin(), exclusions.end());
  ctor.end(lp);

  lp.Begin();
  lp.set_reparametrization(LPReparametrizationMode::Anisotropic);
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
  auto r = create_random_cost_functor();

  Solver<LP<FMC_MY>, StandardVisitor> solver;
  auto& lp = solver.GetLP();
  auto& ctor = solver.GetProblemConstructor<0>();

  ctor.set_number_of_timesteps(2);
  ctor.add_detection_hypothesis(lp, 0, 0, r(), r(), r(), 0, 0, 1, 0);
  ctor.add_detection_hypothesis(lp, 1, 0, r(), r(), r(), 1, 0, 0, 0);
  ctor.add_cell_transition(lp, 0, 0, 1, 0, r());
  ctor.end(lp);

  lp.Begin();
  lp.set_reparametrization(LPReparametrizationMode::Anisotropic);
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
  auto r = create_random_cost_functor();

  Solver<LP<FMC_MY>, StandardVisitor> solver;
  auto& lp = solver.GetLP();
  auto& ctor = solver.GetProblemConstructor<0>();

  ctor.set_number_of_timesteps(2);
  ctor.add_detection_hypothesis(lp, 0, 0, r(), r(), r(), 0, 0, 0, 1);
  ctor.add_detection_hypothesis(lp, 1, 0, r(), r(), r(), 0, 1, 0, 0);
  ctor.add_detection_hypothesis(lp, 1, 1, r(), r(), r(), 0, 1, 0, 0);
  ctor.add_cell_division(lp, 0, 0, 1, 0, 1, 1, r());
  ctor.end(lp);

  lp.Begin();
  lp.set_reparametrization(LPReparametrizationMode::Anisotropic);
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

int main(int argc, char** argv)
{
#ifndef NDEBUG
  for (int i = 0; i < 10000; ++i)
    test_transition_normal();

  for (int i = 0; i < 10000; ++i)
    test_transition_split();

  for (int i = 0; i < 10000; ++i)
    test_uniform_minorant();
#endif

  using BaseSolver = Solver<LP<FMC_MY>, StandardVisitor>;
  BaseSolver solver(argc, argv);
  solver.ReadProblem(cell_tracking_parser_2d::ParseProblem<BaseSolver>);
  auto& lp = solver.GetLP();

  //solver.GetProblemConstructor<0>().output_graphviz(solver.GetLP(), "graph.dot");

  solver.Solve();
}
