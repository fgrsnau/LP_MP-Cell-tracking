
#include "cell_tracking.h"
#include "visitors/standard_visitor.hxx"

using namespace LP_MP;

int main(int argc, char** argv) {
Solver<LP<FMC_CELL_TRACKING_MOTHER_MACHINE>,StandardVisitor> solver(argc,argv);
solver.ReadProblem(cell_tracking_parser_mother_machine::ParseProblemMotherMachine<decltype(solver)>);
return solver.Solve();
}