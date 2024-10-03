import sys
from typing import List
import numpy as np
import importlib
import z3
from binaryninja import *

import symex
import symex.SymbolicEmulator
import symex.utilities
importlib.reload(symex)
importlib.reload(symex.SymbolicEmulator)
importlib.reload(symex.utilities)
from symex.SymbolicEmulator import*
from symex.utilities import*

def calculate_case_address(addr : np.uint32) -> np.uint64:
    # Add the integers.
    eax : np.uint32 = addr + np.uint32(0x7CD7D69E)

    # For some reason, numpy ignores integer overflows.
    # To handle overflows, we have to instantiate a *new* uint32.
    eax = np.uint32(eax)

    # If eax > 0xA, then we jump to the default case. 
    # Otherwise, compute the switch case value normally.
    if eax > np.uint32(0xA):
        return np.uint64(0xC2F)

    # Zero extend eax to 64 bits.
    # TODO: Stop hardcoding table entries
    index = np.uint64(eax)
    cases : List[np.uint64] = (
        np.uint64(0xffff9656),
        np.uint64(0xffff9a04),
        np.uint64(0xffff9b19),
        np.uint64(0xffff9b5b),
        np.uint64(0xffff9c80),
        np.uint64(0xffff9d1f),
        np.uint64(0xffff9d73),
        np.uint64(0xffff9d79),
        np.uint64(0xffff9d9c),
        np.uint64(0xffff9fbf),
        np.uint64(0xffffa071),
    )

    rax = np.uint32(cases[index])
    rdx = np.uint64(0x75d8)
    rdx = rax + rdx

    rdx = rdx - np.uint64(0x100000000)
    print("rdx: " + hex(rdx))
    return rdx

def execute_block(sym: SymbolicEmulator, block: MediumLevelILBasicBlock) -> List[int]:
    result : List[int] = []
    for instr in block:
        if(instr.operation == MediumLevelILOperation.MLIL_GOTO):
            goto : MediumLevelILGoto = instr
            result.append(goto.dest)
            print(f"Encountered goto: exiting block with dest: {hex(goto.dest)}")
            return result

        elif(instr.operation == MediumLevelILOperation.MLIL_IF):
            cond : MediumLevelILIf = instr
            result.append(cond.operands[1])
            result.append(cond.operands[2])
            print(f"Encountered if operation with dests: {hex(cond.operands[1])}. {hex(cond.operands[2])}")
            return result

        elif(instr.operation == MediumLevelILOperation.MLIL_CALL_SSA):
            print("Encountered call instruction: skipping.")
            continue

        sym.execute_instruction(instr)
    return None


def initialize(sym : SymbolicEmulator):
    execute_block(sym, get_block_by_address(mlil, 0xb19))

def run_dispatcher(sym : SymbolicEmulator):
    execute_block(sym, get_block_by_address(mlil, 0xbfb))

def get_outgoing_edges(sym: SymbolicEmulator, bb : MediumLevelILBasicBlock) -> List[int]:
    dests = execute_block(sym, bb)
    return dests
    
# Symbolically executes all block corresponding a switch case.
def execute_case(sym: SymbolicEmulator, block_address) -> List[int]:
    outgoing = get_outgoing_edges(sym, get_block_by_address(mlil, block_address))
    while True:
        next = []
        for edge in outgoing:
            # Exit if we encounter the dispatcher.
            if(edge == 32 or edge == 767):
                print("Encountered dispatcher.")
                return

            # Collect all pairs of outgoing edges.
            for d in get_outgoing_edges(sym, get_block_by_index(mlil, edge)):
                if d not in next:
                    next.append(d)

        # Queue the outgoing edges for execution.
        outgoing = next

# Traverse the symbolic mapping bottom up, 
# until we encounter the latest assignment of the state variable.
def get_state_var_name(sym : SymbolicEmulator):
    next_name = None
    for assignment in sym.expressions[::-1]:
        if("var_5c#" in assignment):
            next_name = assignment
            break

    if next_name == None:
        raise ValueError("Failed to find symbolic name: var_5c#")
    return next_name

# Gets all branch destinations which have not been explored.
def get_new_edges(solutions : List[int], incoming_block_addr : int) -> List[int]:
    results : List[int] = []
    if incoming_block_addr not in explored_edges:
        explored_edges[incoming_block_addr] = []

    for sol in solutions:
        if calculate_case_address(sol) not in explored_edges[incoming_block_addr]:
            results.append(sol)
    return results


# Load the module
bv : BinaryView = BinaryViewType.get_view_of_file("C:\\Users\\colton\\Downloads\\challenge3", update_analysis=True)

# Get the flattened function.
func : Function = bv.get_function_at(0xB0E)

# Get the MLIL function in SSA form.
mlil : MediumLevelILFunction = func.mlil.ssa_form

# Generate SSA form for the function.
mlil.generate_ssa_form()

# Collect all ssa vars.
ssa_vars : List[SSAVariable] = mlil.ssa_vars

# Create a symbolic executor.
symbolic_executor = symex.SymbolicEmulator.SymbolicEmulator(func, mlil)

# Initialize the symbolic executor.
initialize(symbolic_executor)
        
# Setup state.
explored_edges : Dict[int, Set[int]] = {}
execution_queue = []
first_address = 0x1259

# Perform a DFS, traversing every possible unique path.
while(True):
    # Execute the next switch statement case.
    print(f"Exploring block {hex(first_address)}")
    run_dispatcher(symbolic_executor)
    execute_case(symbolic_executor, first_address)

    # Get the state variable's symbolic expression.
    if first_address not in explored_edges:
        explored_edges[first_address] = []
    next_name = get_state_var_name(symbolic_executor)
    next_state = symbolic_executor.variable_mapping[next_name].z3Variable

    # Query all possible values of the state variable.
    sols = []
    if(first_address != 0x134b):
        sols = solve_for_variable(next_state)
    next_solution = None

    # Log all possible values.
    print("solutions after executing block: " + hex(first_address))
    for sol in sols:
        print("    " + hex(sol))

    # Query all edges which have not been explored.
    new_edges = get_new_edges(sols, first_address)

    l = len(new_edges)
    if(l > 2):
        raise ValueError("Flattened blocks cannot have more than two outgoing edges.")
    elif l == 2:
        # Fork & queue the execution state if there are more possible paths to explore.
        execution_queue.append(first_address)
        execution_queue.append(symbolic_executor.fork())
        next_solution = new_edges[0]
    elif l == 1:
        # Explore the only viable path.
        next_solution = new_edges[0]
    else:
        # If our current path hits a deadend, then backtrack to another forked state.
        print("Searching for unexplored states.")
        while True:
            if(len(execution_queue) == 0):
                raise ValueError("Finished execution: all possible states have been explored.")

            # Pop the latest state fork.
            symbolic_executor = execution_queue.pop()

            # Pop the incoming address.
            first_address = execution_queue.pop()

            # Pull the latest expression of the state variable.
            next_name = get_state_var_name(symbolic_executor)

            # Solve for all possible values of the state variable.
            sols = solve_for_variable(symbolic_executor.variable_mapping[next_name].z3Variable)

            # Discard the previous outgoing destination.
            next_solution = None

            # Log all possible state variable values.
            print("Potential outgoing edges:")
            for s in sols:
                print("    " + hex(calculate_case_address(s)))

            # Query all outgoin values for the state fork.
            new_edges = get_new_edges(sols, first_address)

            # Try to execute the forked state.
            l = len(new_edges)
            if(l > 1):
                raise ValueError("Forked states cannot have more than one unexplored path.")
            elif l == 1:
                print("Successfully found state fork to pursue.")
                next_solution = new_edges[0]
                break
            else: # this means you hit zero
                print("Discarding fork: outgoing edges have already been explored.")
                continue

    # Concretize the state variable, and setup state for the next case execution.
    explored_edges[first_address].append(calculate_case_address(next_solution))
    symbolic_executor.variable_mapping[next_name] = Z3Variable(next_name, next_solution)
    first_address = calculate_case_address(next_solution)
