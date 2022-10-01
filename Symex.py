from functools import reduce
from binaryninja import *
import z3

nameCount = 0
symbolic_memory_count = 0
phi_count = 0

def getName():
    global nameCount
    text = "generated_" + str(nameCount)
    nameCount = nameCount + 1
    return text

def getSymbolicMemoryName():
    global symbolic_memory_count
    text = "symbolic_memory" + str(symbolic_memory_count)
    symbolic_memory_count = symbolic_memory_count + 1
    return text

def getPhiName():
    global phi_count
    text = "phi#" + str(phi_count)
    phi_count = phi_count + 1
    return text

class Z3Variable:
    def __init__(self, name : str, z3Variable):
        self.name : str = name
        self.z3Variable = z3Variable

class SymbolicExecutionEngine:
    def __init__(self, func : Function, mlil : MediumLevelILFunction):
        self.func = func
        self.mlil = mlil
        self.solver = z3.Solver()
        self.variable_mapping = dict()
        self.expressions = []

    def fork(self):
        copy = SymbolicExecutionEngine(self.func, self.mlil)
        copy.solver = z3.Solver()
        copy.variable_mapping = dict(self.variable_mapping)
        copy.expressions = self.expressions.copy()

        return copy
        
    def execute_instruction(self, instr: MediumLevelILInstruction):
        print(f"Executing instruction (address: {hex(instr.address)}) and (operation: {str(instr.operation)})")

        if instr.operation == MediumLevelILOperation.MLIL_SET_VAR_SSA:
            return self.handle_set_var_ssa(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_SET_VAR_SSA_FIELD:
            return self.handle_set_var_ssa_field(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_VAR_SSA:
            return self.handle_var_ssa(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_VAR_SSA_FIELD:
            return self.handle_var_ssa_field(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_VAR_PHI:
            return self.handle_var_phi(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_MEM_PHI:
            return self.handle_mem_phi(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_LOAD_SSA:
            return self.handle_load_ssa(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_STORE_SSA:
            return self.handle_store_ssa(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_LOW_PART:
            return self.handle_low_part(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_SX:
            return self.handle_sign_extend(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_ZX:
            return self.handle_zero_extend(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_CONST_PTR:
            return  self.handle_const_ptr(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_CONST:
            return self.handle_const(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_CMP_NE:
            return self.handle_cmp_ne(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_CMP_E:
            return self.handle_cmp_e(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_ADD:
            return self.handle_add(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_SUB:
            return self.handle_sub(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_MUL:
            return self.handle_mul(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_XOR:
            return self.handle_xor(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_OR:
            return self.handle_or(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_AND:
            return self.handle_and(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_NOT:
            return self.handle_not(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_LSL:
            return self.handle_lsl(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_LSR:
            return self.handle_lsr(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_ASR:
            return self.handle_asr(instr)
        elif instr.operation == MediumLevelILOperation.MLIL_RET:
            return self.handle_ret(instr)
        else:
            text = f"Cannot handle instruction: {str(type(instr))}"
            raise ValueError(text)

    def handle_set_var_ssa(self, instr: MediumLevelILSetVarSsa):
        z3_dest = self.get_z3_var(instr.dest)
        z3_src = self.execute_instruction(instr.src)
        self.variable_mapping[z3_dest.name] = z3_src
        self.expressions.append(z3_dest.name)
        return

    def handle_set_var_ssa_field(self, instr: MediumLevelILSetVarSsaField):
        # Get Z3 asts for the operands.
        z3_dest = self.get_z3_var(instr.dest)
        z3_prev = self.get_z3_var(instr.prev)
        z3_src = self.execute_instruction(instr.src)

        # Extract a selection from the source variable, using the provided offset.
        extractSize = instr.size * 8
        extractOffset = instr.offset * 8
        high = (extractOffset) + (extractSize - 1)
        low =  0 if extractOffset == 0 else extractOffset - 1
        extractedField = z3.Extract(high, low, z3_src.z3Variable)

        # Extract any extra bits above the selection.
        extractedLow = None
        if low != 0:
            extractedLow = z3.Extract(low - 1, 0, z3_prev.z3Variable)
        
        # Extract any extra bits below the selection.
        extractedHigh = None    
        if high != instr.src.size - 1:
            extractedHigh = z3.Extract(instr.src.size * 8 - 1, high + 1, z3_prev.z3Variable)

        # Concatenate the extractions together, in order of lowest index to highest.
        finalResult = None
        if extractedHigh == None:
            finalResult = extractedField
        else:
            finalResult = z3.Concat(extractedHigh, extractedField)

        # Compute the complete expression.
        if extractedLow != None:
            finalResult = z3.Concat(finalResult, extractedLow)

        # Store the mapping.
        self.variable_mapping[z3_dest.name] = Z3Variable(z3_dest.name, finalResult)
        self.expressions.append(z3_dest.name)
        return

    def handle_var_ssa(self, instr: MediumLevelILVarSsa):
        return self.get_z3_var(instr.src)

    def handle_var_ssa_field(self, instr: MediumLevelILVarSsaField):
        # Get a z3 AST for the source variable.
        z3_src = self.get_z3_var(instr.src)

        # Extract out a portion of the SSA field.
        finalResult = z3.Extract(
            ((instr.size + instr.offset) * 8) - 1,
            instr.offset * 8,
            z3_src.z3Variable
        )
        
        # Store and return the generated value.
        name = getName()
        var = Z3Variable(name, finalResult)
        self.variable_mapping[name] = var
        return var
        
    def handle_var_phi(self, instr: MediumLevelILVarPhi):
        z3_dest = self.get_z3_var(instr.dest)
        var : SSAVariable = None

        phi_values = []

        # Traverse the expression list backwards, 
        # until we find the latest assignment to the PHI node.
        has_found = False
        for item in self.expressions[::-1]:
            for var in instr.src:
                if has_found:
                    continue

                name = f"{var.name}#{str(var.version)}"
                if name not in self.variable_mapping:
                    continue

                if item == name:
                    has_found = True
                    z3Var = self.get_z3_var(var).z3Variable
                    if var.type.width * 8 > instr.dest.type.width * 8:
                        z3Var = z3.Extract((instr.dest.type.width * 8) - 1, 0, z3Var)
                    elif var.type.width * 8 < instr.dest.type.width * 8:
                        z3Var = z3.ZeroExt((instr.dest.type.width * 8) - (var.type.width * 8), z3Var)
                    phi_values.append(z3Var)
                    continue

                if name == z3_dest.name:
                    continue


        # If none of the phi node sources have expressions,
        # then symbolize the phi node completely.
        if len(phi_values) == 0:
            print("Symbolizing empty phi variable.")
            return z3_dest

        phiName = getPhiName()
        symbolic_phi_selector : z3.Int = z3.Int(phiName)
        self.variable_mapping[phiName] = Z3Variable(z3_dest.name, symbolic_phi_selector)

        phi_expr = phi_values[0]
        if len(phi_values) > 1:
            phi_expr = self.build_nested_ite(symbolic_phi_selector, phi_values, 0)


        self.variable_mapping[z3_dest.name] = Z3Variable(z3_dest.name, phi_expr)
        return z3_dest

    def build_nested_ite(self, inputNode, phi_values, index):
        count = len(phi_values)
        if index + 1 == count:
            print("Creating ITE with single value." + str(index))
            return z3.If(inputNode == z3.IntVal(index), phi_values[index], phi_values[index])
        
        otherIte = self.build_nested_ite(inputNode, phi_values, index + 1)
        return z3.If(inputNode == z3.IntVal(index), phi_values[index], otherIte)

    def handle_mem_phi(self, instr: MediumLevelILMemPhi):
        # Note: all memory is symbolic.
        return None


    def handle_load_ssa(self, instr: MediumLevelILLoadSsa):
        z3_src = self.execute_instruction(instr.src)

        name = getSymbolicMemoryName()

        # For now, we symbolize *all* memory variables.
        symbolic_memory = z3.BitVec(name, instr.size * 8)

        result = Z3Variable(name, symbolic_memory)
        self.variable_mapping[name] = result
        return result

    def handle_store_ssa(self, instr: MediumLevelILStoreSsa):
        # Since all memory is symbolized, we do not need to implement stores.
        return

    def handle_low_part(self, instr: MediumLevelILLowPart):
        z3_input = self.execute_instruction(instr.src)
        extract = z3.Extract((instr.size * 8) - 1, 0, z3_input.z3Variable)
        name = getName()
        result = Z3Variable(name, extract)
        self.variable_mapping[name] = result
        return result
            
    def handle_const_ptr(self, instr: MediumLevelILConstPtr):
        name = f"const_ptr_{str(instr.constant)}"
        z3Integer = z3.BitVecVal(instr.constant, instr.size * 8)
        result = Z3Variable(name, z3Integer)
        self.variable_mapping[name] = result
        return result

    def handle_const(self, instr: MediumLevelILConst):
        name = f"const_{str(instr.constant)}"
        z3Integer = z3.BitVecVal(instr.constant, instr.size * 8)
        result =  Z3Variable(name, z3Integer)
        self.variable_mapping[name] = result
        return result

    def handle_cmp_ne(self, instr: MediumLevelILCmpNe):
        z3_left = self.execute_instruction(instr.left)
        z3_right = self.execute_instruction(instr.right)
        cmpne = z3.If(z3_left.z3Variable != z3_right.z3Variable, z3.BitVecVal(1, instr.size * 8), z3.BitVecVal(0, instr.size * 8))
        name = getName()
        result = Z3Variable(name, cmpne)
        self.variable_mapping[name] = result
        return result

    def handle_cmp_e(self, instr: MediumLevelILCmpNe):
        z3_left = self.execute_instruction(instr.left)
        z3_right = self.execute_instruction(instr.right)
        cmpe = z3.If(z3_left.z3Variable == z3_right.z3Variable, z3.BitVecVal(1, instr.size * 8), z3.BitVecVal(0, instr.size * 8))
        name = getName()
        result = Z3Variable(name, cmpe)
        self.variable_mapping[name] = result
        return result

    def handle_add(self, instr: MediumLevelILAdd):
        z3_left = self.execute_instruction(instr.left)
        z3_right = self.execute_instruction(instr.right)
        addition = z3.BitVecRef(z3.Z3_mk_bvadd(z3.main_ctx().ref(), z3_left.z3Variable.as_ast(), z3_right.z3Variable.as_ast()))
        name = getName()
        result = Z3Variable(name, addition)
        self.variable_mapping[name] = result
        return result

    def handle_sub(self, instr: MediumLevelILSub):
        z3_left = self.execute_instruction(instr.left)
        z3_right = self.execute_instruction(instr.right)
        sub = z3.BitVecRef(z3.Z3_mk_bvsub(z3.main_ctx().ref(), z3_left.z3Variable.as_ast(), z3_right.z3Variable.as_ast()))
        name = getName()
        result = Z3Variable(name, sub)
        self.variable_mapping[name] = result
        return result

    def handle_mul(self, instr: MediumLevelILMul):
        z3_left = self.execute_instruction(instr.left)
        z3_right = self.execute_instruction(instr.right)
        mul = z3.BitVecRef(z3.Z3_mk_bvmul(z3.main_ctx().ref(), z3_left.z3Variable.as_ast(), z3_right.z3Variable.as_ast()))
        name = getName()
        result = Z3Variable(name, mul)
        self.variable_mapping[name] = result
        return result

    def handle_xor(self, instr: MediumLevelILXor):
        z3_left = self.execute_instruction(instr.left)
        z3_right = self.execute_instruction(instr.right)
        xor = z3.BitVecRef(z3.Z3_mk_bvxor(z3.main_ctx().ref(), z3_left.z3Variable.as_ast(), z3_right.z3Variable.as_ast()))
        name = getName()
        result = Z3Variable(name, xor)
        self.variable_mapping[name] = result
        return result

    def handle_or(self, instr: MediumLevelILXor):
        z3_left = self.execute_instruction(instr.left)
        z3_right = self.execute_instruction(instr.right)
        bvor = z3.BitVecRef(z3.Z3_mk_bvor(z3.main_ctx().ref(), z3_left.z3Variable.as_ast(), z3_right.z3Variable.as_ast()))
        name = getName()
        result = Z3Variable(name, bvor)
        self.variable_mapping[name] = result
        return result

    def handle_and(self, instr: MediumLevelILAnd):
        z3_left = self.execute_instruction(instr.left)
        z3_right = self.execute_instruction(instr.right)
        bvand = z3.BitVecRef(z3.Z3_mk_bvand(z3.main_ctx().ref(), z3_left.z3Variable.as_ast(), z3_right.z3Variable.as_ast()))
        name = getName()
        result = Z3Variable(name, bvand)
        self.variable_mapping[name] = result
        return result

    def handle_not(self, instr: MediumLevelILNot):
        src = self.execute_instruction(instr.src)
        bvnot = z3.BitVecRef(z3.Z3_mk_bvnot(z3.main_ctx().ref(), src.z3Variable.as_ast()))
        name = getName()
        result = Z3Variable(name, bvnot)
        self.variable_mapping[name] = result
        return result

    def handle_sign_extend(self, instr: MediumLevelILSx):
        z3_input = self.execute_instruction(instr.src)
        bvsx = z3.SignExt((instr.size * 8) - (instr.src.size * 8), z3_input.z3Variable)
        name = getName()
        result = Z3Variable(name, bvsx)
        self.variable_mapping[name] = result
        return result

    def handle_zero_extend(self, instr: MediumLevelILSx):
        z3_input = self.execute_instruction(instr.src)
        bvzx = z3.ZeroExt((instr.size * 8) - (instr.src.size * 8), z3_input.z3Variable)
        name = getName()
        result = Z3Variable(name, bvzx)
        self.variable_mapping[name] = result
        return result

    def handle_lsl(self, instr: MediumLevelILLsl):
        z3_left = self.execute_instruction(instr.left)
        z3_right = self.execute_instruction(instr.right)
        lsl = z3.BitVecRef(z3.Z3_mk_bvshl(z3.main_ctx().ref(), z3_left.z3Variable.as_ast(), z3_right.z3Variable.as_ast()))
        name = getName()
        result = Z3Variable(name, lsl)
        self.variable_mapping[name] = result
        return result

    def handle_lsr(self, instr: MediumLevelILLsr):
        z3_left = self.execute_instruction(instr.left)
        z3_right = self.execute_instruction(instr.right)
        lshr = z3.LShR(z3_left.z3Variable, z3_right.z3Variable)
        name = getName()
        result = Z3Variable(name, lshr)
        self.variable_mapping[name] = result
        return result

    def handle_asr(self, instr: MediumLevelILAsr):
        z3_left = self.execute_instruction(instr.left)
        z3_right = self.execute_instruction(instr.right)
        asr = z3.BitVecRef(z3.Z3_mk_bvashr(z3.main_ctx().ref(), z3_left.z3Variable.as_ast(), z3_right.z3Variable.as_ast()))
        name = getName()
        result = Z3Variable(name, asr)
        self.variable_mapping[name] = result
        return result

    def handle_ret(self, instr: MediumLevelILRet):
        print("Ignoring ret.")
        return

    def get_z3_var(self, var : SSAVariable):
        name = f"{var.name}#{str(var.version)}"

        # If we have already declared a symbolic variable, then grab it from the mapping.
        if name in self.variable_mapping:
            retValue = self.variable_mapping[name]
            return retValue

        # Otherwise, a placeholder symbolic value.
        result: Z3Variable = None
        typeof = type(var.type)
        if typeof == PointerType :
            z3Pointer : z3.BitVecRef = z3.BitVec(name, var.type.width * 8)
            result = Z3Variable(name, z3Pointer)
            self.variable_mapping[name] = result

        elif typeof == IntegerType:
            z3Integer = z3.BitVec(name, var.type.width * 8)
            result =  Z3Variable(name, z3Integer)
            self.variable_mapping[name] = result
        else:
            text = f"Cannot convert the following type to a z3 var: {str(typeof)}"
            print(text)
            raise ValueError(text)

        print("Created z3 variable: " + name)
        return result
        
    def get_mem_z3_var(self, index, size):
        name = f"mem#{str(index)}"

        # If we have already declared a symbolic variable, then grab it from the mapping.
        if name in self.variable_mapping:
            retValue = self.variable_mapping[name]
            return retValue

        z3MemPointer : z3.BitVecRef = z3.BitVec(name, size)
        result : Z3Variable = Z3Variable(name, z3MemPointer)
        self.variable_mapping[name] = result
        return result
