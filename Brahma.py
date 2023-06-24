
NUM_OF_BITS = 8
import csv
from z3 import *
import z3
from time import *
import time
from inspect import getfullargspec
import inspect
from typing import List, Tuple
from abc import ABC, abstractmethod

'''
The abstract base class for base component specification.
'''
class Component(ABC):
    def __init__(self, name: str) -> None:
        self.name = name
        self.arity = len(getfullargspec(self.semantics)[0]) - 1
    
    @abstractmethod
    def semantics(self, *args):
        raise NotImplementedError

    @abstractmethod
    def expression(self, *args, model) -> str:
        raise NotImplementedError

    def parameters(self):
        return ()

class Add(Component):
    def __init__(self):
        super().__init__('add')

    def semantics(self, a, b):
        return a + b

    def expression(self, a, b, model) -> str:
        return f'{a} + {b}'

class Sub(Component):
    def __init__(self):
        super().__init__('sub')

    def semantics(self, a, b):
        return a - b

    def expression(self, a, b, model) -> str:
        return f'{a} - {b}'

class Inc(Component):
    def __init__(self):
        super().__init__('inc')

    def semantics(self, a):
        return a + 1

    def expression(self, a, model) -> str:
        return f'{a} + 1'

class Dec(Component):
    def __init__(self):
        super().__init__('dec')

    def semantics(self, a):
        return a - 1

    def expression(self, a, model) -> str:
        return f'{a} - 1'

class Neg(Component):
    def __init__(self):
        super().__init__('neg')

    def semantics(self, a):
        return -a 

    def expression(self, a, model) -> str:
        return f'-{a}'

class And(Component):
    def __init__(self):
        super().__init__('and')

    def semantics(self, a, b):
        return a & b

    def expression(self, a, b, model) -> str:
        return f'{a} & {b}'

class Or(Component):
    def __init__(self):
        super().__init__('or')

    def semantics(self, a, b):
        return a | b

    def expression(self, a, b, model) -> str:
        return f'{a} | {b}'

class Not(Component):
    def __init__(self):
        super().__init__('not')

    def semantics(self, a):
        return ~a

    def expression(self, a, model) -> str:
        return f'~{a}'

class Xor(Component):
    def __init__(self):
        super().__init__('xor')

    def semantics(self, a, b):
        return a ^ b

    def expression(self, a, b, model) -> str:
        return f'{a} ^ {b}'
    
class SignBit(Component):
    def __init__(self):
        super().__init__('signbit')

    def semantics(self, a):
        return a >> 31

    def expression(self, a, model) -> str:
        return f'{a} >>> 31'

class NegSignBit(Component):
    def __init__(self):
        super().__init__('negsignbit')

    def semantics(self, a):
        return -(a >> 31)

    def expression(self, a, model) -> str:
        return f'{a} >> 31'

class Ule(Component):
    def __init__(self):
        super().__init__('ule')

    def semantics(self, a, b):
        return z3.If(z3.ULE(a, b), z3.BitVecVal(-1, NUM_OF_BITS), z3.BitVecVal(0, NUM_OF_BITS))

    def expression(self, a, b, model) -> str:
        return f'-((unsigned){a} <= (unsigned){b})'

class Ugt(Component):
    def __init__(self):
        super().__init__('ugt')

    def semantics(self, a, b):
        return z3.If(z3.UGT(a, b), z3.BitVecVal(-1, NUM_OF_BITS), z3.BitVecVal(0, NUM_OF_BITS))

    def expression(self, a, b, model) -> str:
        return f'-((unsigned){a} > (unsigned){b})'

class IfThenElse(Component):
    def __init__(self):
        super().__init__('if-then-else')

    def semantics(self, a, b, c):
        return z3.If(a != 0, b, c)

    def expression(self, a, b, c, model) -> str:
        return f'{a} ? {b} : {c}'

class Constant(Component):
    def __init__(self, value):
        super().__init__(f'const({value})')
        self.value = value

    def semantics(self):
        return self.value

    def expression(self, model) -> str:
        return f'{self.value}'

class VaradicConstant(Component):
    def __init__(self):
        super().__init__(f'varconst')
        self.value = z3.BitVec(f'varconst_{id(self)}', NUM_OF_BITS)

    def semantics(self):
        return self.value

    def expression(self, model) -> str:
        return f'{model.eval(self.value, True)}'

    def parameters(self):
        return (self.value,)

'''
7.3 Choice of Multi-set of Base Components

>   The standard library included 12 components, one each for performing 
> standard operations, such as bitwise-and, bitwise-or, bitwise-not, add-one,
> bitwise-xor, shift-right, comparison, add, and subtract operations.
'''
def std_lib() :
    return [
        # Add(),
        # Sub(),
        # Inc(),
        # Dec(),
        And(),
        # Or(),
        # Not(),
        Xor(),
        # SignBit(),
        # NegSignBit(),
        Ugt(),
        Ule(),
        IfThenElse(),
        # VaradicConstant(),
    ]

class Instruction:
    def __init__(self, component: Component, args: List) -> None:
        self.reached = False
        self.component = component
        self.args = args

class Program:
    def __id2name(self, ident: int) -> str:
        if ident < self.nInput: 
            return f'x{ident}'
        else :
            return f'v{ident - self.nInput}'

    def __init__(self, nInput, model, lPR, lOutput, lib) -> None:
        self.model = model
        self.nInput = nInput
        self.lOutput = model[lOutput].as_long()
        self.sloc = 0

        instrs = [None] * len(lib)
        for (lParams, lRet), comp in zip(lPR, lib):
            lParamVals = [model[lParam].as_long() for lParam in lParams]
            lRetVal = model[lRet].as_long()
            instrs[lRetVal - nInput] = Instruction(comp, lParamVals)
        self.instructions = instrs
        
        '''
        Dead Code Removal

        3   Problem Definition
        
        >   We note that the implementation above is using *all* components
        > from the library. We can assume this without any loss of generality.
        > Even when there is a correct implementation using fewer components,
        > that implementation can always be extended to an implementation that
        > uses all components by adding dead code. Dead code can be easily
        > identified and removed in a post-processing step.
        '''
        def visiting(ident: int) -> None:
            if ident < nInput: return
            instr = instrs[ident - nInput]
            if instr.reached: return
            for sid in instr.args: 
                visiting(sid)
            instr.reached = True
            self.sloc += 1
        
        visiting(self.lOutput)


    def __repr__(self) -> str:
        model = self.model
        prog = [f"def f({', '.join(map(self.__id2name, range(self.nInput)))}):"]
        for ident, instr in enumerate(self.instructions):
            if instr.reached :
                prog.append(f'    v{ident} = ' + instr.component.expression(*map(self.__id2name, instr.args), model))
        prog.append(f'    return {self.__id2name(self.lOutput)}')
        return '\n'.join(prog)

def wfp_cons(lInput: List, lPR: List[Tuple], lOutput):
    cons = []

    # Appropriate Values
    nInput = len(lInput)
    nLib = len(lPR)
    for lParams, lRet in lPR:
        for lParam in lParams:
            cons.append(z3.And(0 <= lParam, lParam < nInput + nLib))
        cons.append(z3.And(nInput <= lRet, lRet < nInput + nLib))
    cons.append(z3.And(0 <= lOutput, lOutput < nInput + nLib))
    # Assign Fixed Value for lInput
    for i, lInp in enumerate(lInput) :
        cons.append(lInp == i)

    '''
    -   Consistency Constraint
    >   Every line in the program has at most one component.
    '''
    lRets = tuple(zip(*lPR))[1]
    for i in range(len(lRets)):
        for j in range(i):
            cons.append(lRets[i] != lRets[j])

    '''
    -   Acyclicity Constraint
    >   In a well-formed program, every variable is initialized *before* it is
    > used.
    '''
    for lParams, lRet in lPR:
        for lParam in lParams:
            cons.append(lParam < lRet)
    
    return z3.And(*cons)

def conn_cons(lInput: List, lPR: List[Tuple], lOutput, vInput: List, vPR: List[Tuple], vOutput):
    cons = []

    lList = lInput + [lOutput]
    for lParams, lRet in lPR:
        lList += lParams
        lList.append(lRet)
    
    vList = vInput + [vOutput]
    for vParams, vRet in vPR:
        vList += vParams
        vList.append(vRet)
    
    n = len(lList)
    assert n == len(vList)

    for i in range(n):
        for j in range(i):
            cons.append(z3.Implies(lList[i] == lList[j], vList[i] == vList[j]))
    
    return z3.And(*cons)

def lib_cons(vPR: List[Tuple], lib: List[Component]):
    cons = []
    for (vParam, vRet), comp in zip(vPR, lib):
        cons.append(vRet == comp.semantics(*vParam))
    return z3.And(*cons)

class ResultWriter():
    def __init__(self, save_folder, file_name):
        super(ResultWriter, self).__init__()
        self.save_path = os.path.join(save_folder, file_name)
        self.csv_writer = None
        if not os.path.exists(save_folder):
            os.makedirs(save_folder)

    def create(self, csv_head):
        with open(self.save_path, 'w') as f:
            csv_writer = csv.writer(f)
            csv_writer.writerow(csv_head)

    def write(self, data_row):
        with open(self.save_path, 'a') as f:
            csv_write = csv.writer(f)
            csv_write.writerow(data_row)

class Synthesizer:
    def __init__(self, nInput, spec, lib=std_lib):
        self.nInput = nInput
        self.lib = lib()
        self.spec = lambda vInput, vOutput: spec(vOutput, *vInput)

    '''
    6   Synthesis Constraint Solving
    '''
    def synthesize(self, max_iter=100, timeout=120000) :
        lib = self.lib
        nInput = self.nInput

        def id_arr(prefix, num):
            return [f'{prefix}_{i}' for i in range(num)]

        def make_loc_vars(prefix):
            lInput = list(z3.Ints(id_arr(f'{prefix}_locInput', nInput)))
            lPR = [
                (   
                    list(z3.Ints(id_arr(f'{prefix}_locParam_{i}', comp.arity))), 
                    z3.Int(f'{prefix}_locReturn_{i}')
                ) for i, comp in enumerate(lib)
            ]
            lOutput = z3.Int(f'{prefix}_locOutput')
            return lInput, lPR, lOutput

        def make_value_vars(prefix):
            vInput = list(z3.BitVecs(id_arr(f'{prefix}_valInput', nInput), NUM_OF_BITS))
            vPR = [
                (
                    list(z3.BitVecs(id_arr(f'{prefix}_valParam_{i}', comp.arity), NUM_OF_BITS)), 
                    z3.BitVec(f'{prefix}_valReturn_{i}', NUM_OF_BITS)
                ) for i, comp in enumerate(lib)
            ]
            vOutput = z3.BitVec(f'{prefix}_valOutput', NUM_OF_BITS)
            return vInput, vPR, vOutput


        lInput, lPR, lOutput = make_loc_vars('cur')
        cevInput, cevPR, cevOutput = make_value_vars('ctr')
        
        synthesizer = z3.Solver()
        synthesizer.set(timeout=timeout)
        synthesizer.add(wfp_cons(lInput, lPR, lOutput))
        # print("\n\n\nsynthesizer wfp_cons:");print(wfp_cons(lInput, lPR, lOutput))################################

        verifier = z3.Solver()
        verifier.set(timeout=timeout)
        verifier.add(conn_cons(lInput, lPR, lOutput, cevInput, cevPR, cevOutput))
        # print("\n\n\nverifier adding conn_cons:");print(conn_cons(lInput, lPR, lOutput, cevInput, cevPR, cevOutput))################################
        verifier.add(lib_cons(cevPR, lib))
        # print("\n\n\nverifier adding lib_cons:");print(lib_cons(cevPR, lib))################################
        verifier.add(z3.Not(self.spec(cevInput, cevOutput)))
        # print("\n\n\nverifier adding NOT spec:\nthis is normal spec");print(z3.Not(self.spec(cevInput, cevOutput)))################################
        
        '''
        ExAllSolver
        '''
        for iteration in range(max_iter):
            print(f'> Running iteration {iteration} ...')
            # print("tessst")
            # print(self.spec(cevInput, cevOutput))
            '''
            Step 1. Finite Synthesis
            >   In this step, we synthesize a design that works for finitely many
            > inputs. Specifically, the procedure finds values for L that work for
            > all the inputs in S.
            '''
            check_result = synthesizer.check()
            if check_result == z3.sat:
                syn_model = synthesizer.model()
                program = Program(nInput, syn_model, lPR, lOutput, lib)
            elif check_result == z3.unsat:
                '''
                >   If no such values are found, we terminate and declare that no
                > design could be found.
                '''
                return None 
            else:
                return None

            # print("\n\n\nsyn_model in iteration ",iteration,":\n")#############################
            # print(syn_model)############################################################
            '''
            Step 2. Verification
            >   In this step, we verify if the synthesized design - that we know
            > works for the inputs in S - also works for all inputs. Specifically, 
            > if the generated value currL for L works for all inputs, then we
            > terminate with success. If not, then we find an input on which it does
            > not work and add it to S.
            '''
            verifier.push()
            # print("\n\n\npush starts:")
            for lv in lInput:
                '''
                `model.eval(var, True)` is needed for model completion, since
                `model[var]` simply doesn't work for irrelavent variables. See
                https://github.com/Z3Prover/z3/issues/1920, it seems that Z3Py
                doesn't provide interface for enabling model completion globally.
                '''
                verifier.add(lv == syn_model.eval(lv, True))
                # print("\n\n\nadd lInput to verifier:");print(lv == syn_model.eval(lv, True))################################
            for lParams, lRet in lPR:
                # print("\n\n\nadd new... to verifier:")###########################################
                for lParam in lParams:
                    verifier.add(lParam == syn_model.eval(lParam, True))
                    # print("\n\n\nadd lparams to verifier:");print(lParam == syn_model.eval(lParam, True))################################
                verifier.add(lRet == syn_model.eval(lRet, True))
                # print("\n\n\nadd lRet to verifier:");print(lRet == syn_model.eval(lRet, True))################################
            verifier.add(lOutput == syn_model.eval(lOutput, True))
            # print("\n\n\nadd lOutput to verifier:");print(lOutput == syn_model.eval(lOutput, True))################################

            for comp in lib:
                for param in comp.parameters() :
                    verifier.add(param == syn_model.eval(param, True))

            check_result = verifier.check()
            if check_result == z3.unsat:
                return program
            elif check_result == z3.sat:
                ver_model = verifier.model()
                # print("\n\n\nver_model in iteration ",iteration,":\n")####################################
                # print(ver_model)########################################################################
                cvInput, cvPR, cvOutput = make_value_vars(f'c{iteration}')
                synthesizer.add(lib_cons(cvPR, lib))
                # print("\n\n\nadd lib_cons to synthesizer:");print(lib_cons(cvPR, lib))################################
                synthesizer.add(conn_cons(lInput, lPR, lOutput, cvInput, cvPR, cvOutput))
                # print("\n\n\nadd conn_cons to synthesizer:");print(conn_cons(lInput, lPR, lOutput, cvInput, cvPR, cvOutput))################################
                synthesizer.add(self.spec(cvInput, cvOutput))
                # print("\n\n\nsynthesizer adding spec:");print(self.spec(cvInput, cvOutput))################################
                # print("\n\n\nadd new... to verifier:")###################################################
                for cevI, cvI in zip(cevInput, cvInput) :
                    synthesizer.add(cvI == ver_model.eval(cevI, True))
                    # print("\n\nverifier adding new_cons:");print(cvI == ver_model.eval(cevI, True))################################
            else:
                return None

            verifier.pop()

        return None

timestr = time.strftime("%Y%m%d_%H%M%S")
log_file_name = 'Log_' + timestr + '.csv'
log = ResultWriter('Logs',log_file_name)
log.create(['problem', 'Z3', 'CVC4', 'CVC5']) 

problem_num = 0
z3_time = 0
cvc4_time = 0
cvc5_time = 0
log.write([problem_num, z3_time, cvc4_time, cvc5_time])

problems = [
    lambda y, x: y == x,
    lambda y, a, b: If(ULE(a & b, a ^ b), y != 0, y == 0),
    # lambda y, x, z: y == (-1 if (x ^ z) <= (x & z) else 0),
]
'''
    lambda y, x: y == (x & (x - 1)),
    lambda y, x: y == (x & (x + 1)),
    lambda y, x: y == (x & (~x + 1)),
    lambda y, x: y == (x ^ (x - 1)),
    lambda y, x: y == (x | (x - 1)),

    lambda y, x: y == (x | (x + 1)),
    lambda y, x: y == (~x & (x + 1)),
    lambda y, x: y == ((x - 1) & ~x),
    lambda y, x: y == ((x ^ (x >> 31)) - (x >> 31)),
    lambda y, x, z: y == (-1 if (x ^ z) <= (x & z) else 0),


    lambda y, x: y == ,
    lambda y, x: y == ,
    lambda y, x: y == ,
    lambda y, x: y == ,
    lambda y, x: y == ,

    lambda y, x: y == ,
    lambda y, x: y == ,
    lambda y, x: y == ,
    lambda y, x: y == ,
    lambda y, x: y == ,

    lambda y, x: y == ,
    lambda y, x: y == ,
    lambda y, x: y == ,
    lambda y, x: y == ,
    lambda y, x: y == ,
    '''

for problem_num, problem_specification in enumerate(problems):
    print(f'Synthesizing #{problem_num} ...')
    arity = len(inspect.getfullargspec(problem_specification)[0]) - 1
    synth = Synthesizer(arity, problem_specification)
    program = None
    start_time = process_time()
    program = synth.synthesize()
    print(program)
    z3_time = process_time() - start_time
    print("time is: {0:0.2f} sec".format(z3_time))
    log.write([problem_num, z3_time, 0, 0])


'''
input_specification = lambda y, a: y == a & (a - 1)
class brahma_synthesizer:
    def __init__(self, user_specifications):
        self.specifications = lambda user_Input, user_Output: user_specifications(user_Output, user_Input)
    
    def synthesize(self):
        s = z3.Solver()
        z3_Input = z3.BitVec('z3_Input', NUM_OF_BITS)
        z3_Output = z3.BitVec('z3_Output', NUM_OF_BITS)
        s.add(self.specifications(z3_Input, z3_Output))
        print(s.assertions())
        print(s.check())
        print(s.model())        
        s2 = z3.Solver()
        z3_Input = z3.BitVec('z3_Input', 32)
        z3_Output = z3.BitVec('z3_Output', 32)
        s2.add(z3.Not(self.specifications(z3_Input, z3_Output)))
        print(s2.assertions())
        print(s2.check())
        print(s2.model())
        
test_synthesizer = brahma_synthesizer(input_specification)
test_synthesizer.synthesize()
'''



# print('%.2f seconds used.' % (time.clock() - t0))

# s = Solver()
# a = Real('a')
# b = Real('b')
# x = Real('x')
# y = Real('y')
# # lambda y, a: y == a | (a - 1)

# # s.add(lambda y, a: y == a | (a - 1))
# s.add([y == x + 1, ForAll([y], Implies(y <= 0, x > y))])
# print(s.check())
# print(s.model())

# r=0
# dde = eval(input('>>> '))
# print(dde)

# x = Int('x')
# y = Int('y')
# n = x + y >= 3
# print ("num args: ", n.num_args())
# print ("children: ", n.children())
# print ("1st child:", n.arg(0))
# print ("2nd child:", n.arg(1))
# print ("operator: ", n.decl())
# print ("op name:  ", n.decl().name())

# s = Solver()

# x = Bool("x")
# y = Bool("y")
# z = Bool("z")
# f1 = Or([x,y,z])
# s.add(f1)
# f2 = Or([Not(x),Not(y)])
# s.add(f2)
# f3 = Or([Not(y),Not(z)])
# s.add(f3)

# print(s.assertions())
# print(s.check())
# print(s.model())