#ifndef LP_MP_CELL_TRACKING_HXX
#define LP_MP_CELL_TRACKING_HXX

#include "factors_messages.hxx"
#include "detection_factor.hxx"
#include "detection_factors_fine_decomposition.hxx"
#include "cell_tracking_constructor.hxx"
#include "cell_detection_flow_factor.hxx"
#include "LP_MP.h"

namespace LP_MP {

struct FMC_CELL_TRACKING {
  constexpr static const char* name = "Cell tracking";

  using detection_factor_container = FactorContainer<detection_factor, FMC_CELL_TRACKING, 0, true>;
  using at_most_one_hypothesis_container = FactorContainer<at_most_one_cell_factor, FMC_CELL_TRACKING, 1, false>;
  using FactorList = meta::list<detection_factor_container, at_most_one_hypothesis_container>;

  using transition_message_container = MessageContainer<transition_message, 0, 0, message_passing_schedule::full, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING, 0, 4, 4>;
  using at_most_one_cell_message_container = MessageContainer<at_most_one_cell_message, 0, 1, message_passing_schedule::left, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING, 1, 3, 3>;
  using MessageList = meta::list<transition_message_container, at_most_one_cell_message_container>;
  //using transition_message_container = MessageContainer<transition_message, 0, 0, message_passing_schedule::full, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING, 1, 4, 4>;
  //using at_most_one_cell_message_container = MessageContainer<at_most_one_cell_message, 0, 1, message_passing_schedule::left, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING, 0, 3, 3>;
  //using MessageList = meta::list<at_most_one_cell_message_container, transition_message_container >;

  using base_constructor = basic_cell_tracking_constructor< detection_factor_container >;
  using exclusion_constructor = cell_tracking_exclusion_constructor< base_constructor, at_most_one_hypothesis_container, at_most_one_cell_message_container >; 
  using transition_constructor = transition_message_cell_tracking_constructor< exclusion_constructor, transition_message_container>;
  using constructor = cell_tracking_constructor<transition_constructor>;

  using ProblemDecompositionList = meta::list<constructor>; 
};

struct FMC_CELL_TRACKING_FLOW {
  constexpr static const char* name = "Cell tracking";

  using detection_factor_container = FactorContainer<detection_factor, FMC_CELL_TRACKING_FLOW, 0, true>;
  using at_most_one_hypothesis_container = FactorContainer<at_most_one_cell_factor, FMC_CELL_TRACKING_FLOW, 1, false>;
  using flow_factor_container = FactorContainer<cell_detection_flow_factor, FMC_CELL_TRACKING_FLOW, 2, false>;
  using FactorList = meta::list<detection_factor_container, at_most_one_hypothesis_container, flow_factor_container>;

  using transition_message_container = MessageContainer<transition_message, 0, 0, message_passing_schedule::full, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING_FLOW, 0, 4, 4>;
  using at_most_one_cell_message_container = MessageContainer<at_most_one_cell_message, 0, 1, message_passing_schedule::left, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING_FLOW, 1, 3, 3>;
  using flow_factor_message_container = MessageContainer< cell_detection_flow_message, 0, 2, message_passing_schedule::right, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING_FLOW, 2, 1, 20>;
  using MessageList = meta::list<transition_message_container, at_most_one_cell_message_container, flow_factor_message_container>;

  using base_constructor = basic_cell_tracking_constructor< detection_factor_container >;
  using exclusion_constructor = cell_tracking_exclusion_constructor< base_constructor, at_most_one_hypothesis_container, at_most_one_cell_message_container >; 
  using transition_constructor = transition_message_cell_tracking_constructor< exclusion_constructor, transition_message_container>;
  using constructor = cell_tracking_constructor<transition_constructor>;
  using flow_constructor = cell_detection_flow_constructor< constructor, flow_factor_container, flow_factor_message_container >;

  using ProblemDecompositionList = meta::list<flow_constructor>; 
};

struct FMC_CELL_TRACKING_DUPLICATE_EDGES {
  constexpr static const char* name = "Cell tracking";

  using detection_factor_container = FactorContainer<detection_factor, FMC_CELL_TRACKING_DUPLICATE_EDGES, 0, true>;
  using edge_factor_container = FactorContainer<mapping_edge_factor, FMC_CELL_TRACKING_DUPLICATE_EDGES, 1, false>;
  using at_most_one_hypothesis_container = FactorContainer<at_most_one_cell_factor, FMC_CELL_TRACKING_DUPLICATE_EDGES, 2, false>;

  using incoming_edge_message_container = MessageContainer<cell_incoming_edge_detection_factor, 1, 0, message_passing_schedule::full, 1, variableMessageNumber, FMC_CELL_TRACKING_DUPLICATE_EDGES, 0>;
  using outgoing_edge_message_container = MessageContainer<cell_outgoing_edge_detection_factor, 1, 0, message_passing_schedule::full, 1, variableMessageNumber, FMC_CELL_TRACKING_DUPLICATE_EDGES, 1>;
  using at_most_one_cell_message_container = MessageContainer<at_most_one_cell_message, 0, 2, message_passing_schedule::full, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING_DUPLICATE_EDGES, 2>;

  using FactorList = meta::list<detection_factor_container, edge_factor_container, at_most_one_hypothesis_container>;
  using MessageList = meta::list<incoming_edge_message_container, outgoing_edge_message_container, at_most_one_cell_message_container>;

  using base_constructor = basic_cell_tracking_constructor< detection_factor_container>;
  using exclusion_constructor = cell_tracking_exclusion_constructor<base_constructor, at_most_one_hypothesis_container, at_most_one_cell_message_container >; 
  using transition_constructor = cell_tracking_constructor_duplicate_edges< exclusion_constructor, 
        edge_factor_container, edge_factor_container, 
        incoming_edge_message_container, outgoing_edge_message_container,
        incoming_edge_message_container, outgoing_edge_message_container>;
  using constructor = cell_tracking_constructor<transition_constructor>;

  using ProblemDecompositionList = meta::list<constructor>; 
}; 

struct FMC_CELL_TRACKING_WITH_DIVISION_DISTANCE {
  constexpr static const char* name = "Cell tracking with division distance";

  using detection_factor_container = FactorContainer<detection_factor_dd, FMC_CELL_TRACKING_WITH_DIVISION_DISTANCE, 0, true>;
  using at_most_one_hypothesis_container = FactorContainer<at_most_one_cell_factor, FMC_CELL_TRACKING_WITH_DIVISION_DISTANCE, 1, false>;

  using transition_message_container = MessageContainer<transition_message_dd, 0, 0, message_passing_schedule::full, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING_WITH_DIVISION_DISTANCE, 0>;
  using at_most_one_cell_message_container = MessageContainer<at_most_one_cell_message, 0, 1, message_passing_schedule::left, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING_WITH_DIVISION_DISTANCE, 1>;

  using FactorList = meta::list<detection_factor_container, at_most_one_hypothesis_container>;
  using MessageList = meta::list<transition_message_container, at_most_one_cell_message_container>;

  using base_constructor = basic_cell_tracking_constructor< detection_factor_container>;
  using exclusion_constructor = cell_tracking_exclusion_constructor<base_constructor, at_most_one_hypothesis_container, at_most_one_cell_message_container >; 
  using transition_constructor = transition_message_cell_tracking_constructor< exclusion_constructor, transition_message_container>;
  using constructor = cell_tracking_with_division_distance_constructor<transition_constructor>;

  using ProblemDecompositionList = meta::list<constructor>; 
};

struct FMC_CELL_TRACKING_DIVISION_DISTANCE_DUPLICATE_EDGES{
  constexpr static const char* name = "Cell tracking with division distance";

  using detection_factor_container = FactorContainer<detection_factor_dd, FMC_CELL_TRACKING_DIVISION_DISTANCE_DUPLICATE_EDGES, 0, true>;
  using mapping_edge_factor_container = FactorContainer<mapping_edge_factor_dd, FMC_CELL_TRACKING_DIVISION_DISTANCE_DUPLICATE_EDGES, 1, false>;
  using division_edge_factor_container = FactorContainer<division_edge_factor_dd, FMC_CELL_TRACKING_DIVISION_DISTANCE_DUPLICATE_EDGES, 2, false>;
  using at_most_one_hypothesis_container = FactorContainer<at_most_one_cell_factor, FMC_CELL_TRACKING_DIVISION_DISTANCE_DUPLICATE_EDGES, 3, false>;

  using incoming_mapping_edge_message_container = MessageContainer<cell_incoming_mapping_edge_detection_factor_dd, 1, 0, message_passing_schedule::full, 1, variableMessageNumber, FMC_CELL_TRACKING_DIVISION_DISTANCE_DUPLICATE_EDGES, 0>;
  using outgoing_mapping_edge_message_container = MessageContainer<cell_outgoing_mapping_edge_detection_factor_dd, 1, 0, message_passing_schedule::full, 1, variableMessageNumber, FMC_CELL_TRACKING_DIVISION_DISTANCE_DUPLICATE_EDGES, 1>;
  using incoming_division_edge_message_container = MessageContainer<cell_incoming_division_edge_detection_factor_dd, 2, 0, message_passing_schedule::full, 1, variableMessageNumber, FMC_CELL_TRACKING_DIVISION_DISTANCE_DUPLICATE_EDGES, 0>;
  using outgoing_division_edge_message_container = MessageContainer<cell_outgoing_division_edge_detection_factor_dd, 2, 0, message_passing_schedule::full, 1, variableMessageNumber, FMC_CELL_TRACKING_DIVISION_DISTANCE_DUPLICATE_EDGES, 1>; 
  using at_most_one_cell_message_container = MessageContainer<at_most_one_cell_message, 0, 3, message_passing_schedule::left, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING_DIVISION_DISTANCE_DUPLICATE_EDGES, 2>;

  using FactorList = meta::list<detection_factor_container, mapping_edge_factor_container, division_edge_factor_container, at_most_one_hypothesis_container>;
  using MessageList = meta::list<incoming_mapping_edge_message_container, outgoing_mapping_edge_message_container, incoming_division_edge_message_container, outgoing_division_edge_message_container, at_most_one_cell_message_container>;

  using base_constructor = basic_cell_tracking_constructor< detection_factor_container>;
  using exclusion_constructor = cell_tracking_exclusion_constructor<base_constructor, at_most_one_hypothesis_container, at_most_one_cell_message_container >; 
  using constructor_division_distance = cell_tracking_with_division_distance_constructor<exclusion_constructor>;
  using constructor = cell_tracking_with_division_distance_and_duplicate_edges_constructor<constructor_division_distance,
	mapping_edge_factor_container, division_edge_factor_container, 
	incoming_mapping_edge_message_container, outgoing_mapping_edge_message_container,
	incoming_division_edge_message_container, outgoing_division_edge_message_container >;

  using ProblemDecompositionList = meta::list<constructor>; 
}; 

struct FMC_CELL_TRACKING_MOTHER_MACHINE {
  constexpr static const char* name = "Cell tracking in the mother machine";

  using detection_factor_container = FactorContainer<detection_factor, FMC_CELL_TRACKING_MOTHER_MACHINE, 0, true>;
  using at_most_one_hypothesis_container = FactorContainer<at_most_one_cell_factor, FMC_CELL_TRACKING_MOTHER_MACHINE, 1, false>;
  using exit_constraint = FactorContainer<exit_constraint_factor, FMC_CELL_TRACKING_MOTHER_MACHINE, 2, false>;

  using transition_message_container = MessageContainer<transition_message, 0, 0, message_passing_schedule::full, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING_MOTHER_MACHINE, 0>;
  using at_most_one_cell_message_container = MessageContainer<at_most_one_cell_message, 0, 1, message_passing_schedule::left, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING_MOTHER_MACHINE, 1>;
  using exit_constraint_lower_message = MessageContainer<exit_constraint_message<exit_constraint_position::lower>, 0, 2, message_passing_schedule::left, variableMessageNumber, 1, FMC_CELL_TRACKING_MOTHER_MACHINE, 2>;
  using exit_constraint_upper_message = MessageContainer<exit_constraint_message<exit_constraint_position::upper>, 0, 2, message_passing_schedule::left, variableMessageNumber, 1, FMC_CELL_TRACKING_MOTHER_MACHINE, 3>;

  using FactorList = meta::list< detection_factor_container, at_most_one_hypothesis_container, exit_constraint >;
  using MessageList = meta::list< transition_message_container, at_most_one_cell_message_container, exit_constraint_lower_message, exit_constraint_upper_message >;

  using base_constructor = basic_cell_tracking_constructor< detection_factor_container >;
  using exclusion_constructor = cell_tracking_exclusion_constructor<base_constructor, at_most_one_hypothesis_container, at_most_one_cell_message_container >; 
  using transition_constructor = transition_message_cell_tracking_constructor< exclusion_constructor, transition_message_container>;
  using constructor = cell_tracking_constructor<transition_constructor>;

  using constructor_mother_machine = cell_tracking_mother_machine_constructor<
    constructor,
    exit_constraint, exit_constraint_lower_message, exit_constraint_upper_message
      >;

  using ProblemDecompositionList = meta::list<constructor_mother_machine>;
};


struct FMC_CELL_TRACKING_FINE_DECOMPOSITION {
  constexpr static const char* name = "Cell tracking fine decomposition";

  using incoming_edges_factor = FactorContainer<flow_conservation_factor, FMC_CELL_TRACKING_FINE_DECOMPOSITION, 0, false>;
  using outgoing_edges_factor = FactorContainer<flow_conservation_factor, FMC_CELL_TRACKING_FINE_DECOMPOSITION, 1, false>;
  using at_most_one_hypothesis_container = FactorContainer<at_most_one_cell_factor, FMC_CELL_TRACKING_FINE_DECOMPOSITION, 2, false>;

  using detection_message_container = MessageContainer<detection_message, 0, 1, message_passing_schedule::full, 1, 1, FMC_CELL_TRACKING_FINE_DECOMPOSITION, 0>;
  using transition_message_container = MessageContainer<flow_conservation_message, 1, 0, message_passing_schedule::full, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING_FINE_DECOMPOSITION, 1>;

  using at_most_one_cell_message_container_incoming = MessageContainer<at_most_one_cell_message, 0, 2, message_passing_schedule::left, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING_FINE_DECOMPOSITION, 2>;
  using at_most_one_cell_message_container_outgoing = MessageContainer<at_most_one_cell_message, 1, 2, message_passing_schedule::left, variableMessageNumber, variableMessageNumber, FMC_CELL_TRACKING_FINE_DECOMPOSITION, 3>;

  using FactorList = meta::list< incoming_edges_factor, outgoing_edges_factor, at_most_one_hypothesis_container >;
  using MessageList = meta::list< detection_message_container, transition_message_container, at_most_one_cell_message_container_incoming, at_most_one_cell_message_container_outgoing >;

  // mock class which functions correctly with constructor
  struct detection_factor_pair {
    using incoming_factor_type =  incoming_edges_factor;
    using outgoing_factor_type =  outgoing_edges_factor;

    incoming_edges_factor* incoming;
    outgoing_edges_factor* outgoing;

    detection_factor_pair* GetFactor() { return this; }

    void set_outgoing_transition_cost(const INDEX no_outgoing_transition_edges, const INDEX no_outgoing_division_edges, const INDEX outgoing_edge_index, const REAL cost)
    { outgoing->GetFactor()->set_outgoing_transition_cost(no_outgoing_transition_edges, no_outgoing_division_edges, outgoing_edge_index, cost); }
    void set_incoming_transition_cost(const INDEX no_incoming_transition_edges, const INDEX no_incoming_division_edges, const INDEX incoming_edge_index, const REAL cost)
    { incoming->GetFactor()->set_incoming_transition_cost(no_incoming_transition_edges, no_incoming_division_edges, incoming_edge_index, cost); }

    void set_outgoing_division_cost(const INDEX no_outgoing_transition_edges, const INDEX no_outgoing_division_edges, const INDEX outgoing_edge_index, const REAL cost)
    { outgoing->GetFactor()->set_outgoing_division_cost(no_outgoing_transition_edges, no_outgoing_division_edges, outgoing_edge_index, cost); }
    void set_incoming_division_cost(const INDEX no_incoming_transition_edges, const INDEX no_incoming_division_edges, const INDEX incoming_edge_index, const REAL cost)
    { incoming->GetFactor()->set_incoming_division_cost(no_incoming_transition_edges, no_incoming_division_edges, incoming_edge_index, cost); }

  };

  using base_constructor = basic_cell_tracking_constructor< detection_factor_pair >;
  using constructor = cell_tracking_fine_decomposition_constructor< base_constructor, detection_message_container, transition_message_container, at_most_one_hypothesis_container, at_most_one_cell_message_container_incoming, at_most_one_cell_message_container_outgoing >;

  using ProblemDecompositionList = meta::list<constructor>;
};

} // end namespace LP_MP
#endif // LP_MP_CELL_TRACKING_HXX
