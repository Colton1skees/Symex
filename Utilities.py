from binaryninja import *
import z3

# Solves for all possible variable solutions, up to a limit of two.
def solve_for_variable(z3Var) -> List[int]:
    solutions = []
    last_solution = None
    s = z3.Solver()
    while True:
        if last_solution != None:
            s.add(z3Var != last_solution)
        
        check = str(s.check())
        if(check == "unsat"):
            print("Found all possible solutions.")
            break

        if(len(solutions) > 2):
            print("Found too many solutions")
            break

        m : z3.ModelRef = s.model()
        evaluation : z3.BitVecNumRef = m.eval(z3Var, model_completion=True)
        last_solution = evaluation
        solutions.append(evaluation.as_long())

    return solutions
