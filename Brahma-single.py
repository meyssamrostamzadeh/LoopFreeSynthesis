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
this is a python implementation of Loopfree_bitvector synthesizer "Brahma" that first intruduced in
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/pldi11-loopfree-synthesis.pdf
the main paper had no implementation and a lot of Idea's for bulding  synthesizer here is borrowed from 
Rust implementation available at https://fitzgeraldnick.com/2020/01/13/synthesizing-loop-free-programs.html
this code is also utilized Z3 as SMT-Solver. we tried CVC5 and PYSMT as
backbone but it didn't go well! we are planning to keep working on it
the solutions will be added here(https://github.com/meyssamrostamzadeh/LoopFreeSynthesis)
Note: we made all function's in single .py file as we needed to run this on server and mobility matters!
'''

'''
making components as classes. there were better idea's regards defining specs that
doesn't need for duplicate difinitions. but this structure has no problem and works fine...
'''
class Component(ABC):
    def __init__(self, name: str) -> None:
        self.name = name
        self.arity = len(getfullargspec(self.semantics)[0]) - 1
    
    # semantics used to pass component specification to SMT-Solver
    @abstractmethod
    def semantics(self, *args):
        raise NotImplementedError

    # expression used to generate programs from locations returned by SMT-Solver
    @abstractmethod
    def expression(self, *args, model) -> str:
        raise NotImplementedError

    def parameters(self):
        return ()
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
class And2(Component):
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
class Not2(Component):
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
class Xor2(Component):
    def __init__(self):
        super().__init__('xor')

    def semantics(self, a, b):
        return a ^ b

    def expression(self, a, b, model) -> str:
        return f'{a} ^ {b}'
class Xor3(Component):
    def __init__(self):
        super().__init__('xor')

    def semantics(self, a, b):
        return a ^ b

    def expression(self, a, b, model) -> str:
        return f'{a} ^ {b}'
class Xor4(Component):
    def __init__(self):
        super().__init__('xor')

    def semantics(self, a, b):
        return a ^ b

    def expression(self, a, b, model) -> str:
        return f'{a} ^ {b}'
class Shr(Component):
    def __init__(self):
        super().__init__('shr')

    def semantics(self, a, b):
        return a >> b

    def expression(self, a, b,  model) -> str:
        return f'{a} >>> {b}'
class Shr2(Component):
    def __init__(self):
        super().__init__('shr')

    def semantics(self, a, b):
        return a >> b

    def expression(self, a, b,  model) -> str:
        return f'{a} >>> {b}'
class Shl(Component):
    def __init__(self):
        super().__init__('shl')

    def semantics(self, a, b):
        return a << b

    def expression(self, a, b,  model) -> str:
        return f'{a} << {b}'
# SignBit and NegSignBit just needed for one problem (13) out of 25 Hacker's delight problems
# and not added to other problems components
class SignBit(Component):
    def __init__(self):
        super().__init__('signbit')

    def semantics(self, a):
        return a >> (NUM_OF_BITS - 1)

    def expression(self, a, model) -> str:
        return f'{a} >>> 31'
class NegSignBit(Component):
    def __init__(self):
        super().__init__('negsignbit')

    def semantics(self, a):
        return -(a >> (NUM_OF_BITS - 1))

    def expression(self, a, model) -> str:
        return f'{a} >> 31'
# Ule_Uge_Ugt are problem specific components and added when needed(not added to all problem components)
class Ule(Component):
    def __init__(self):
        super().__init__('ule')

    def semantics(self, a, b):
        return z3.If(z3.ULE(a, b), z3.BitVecVal(-1, NUM_OF_BITS), z3.BitVecVal(0, NUM_OF_BITS))

    def expression(self, a, b, model) -> str:
        return f'-((unsigned){a} <= (unsigned){b})'
class Uge(Component):
    def __init__(self):
        super().__init__('ule')

    def semantics(self, a, b):
        return z3. z3.If(z3.UGE(a, b), z3.BitVecVal(-1, NUM_OF_BITS), z3.BitVecVal(0, NUM_OF_BITS))

    def expression(self, a, b, model) -> str:
        return f'-((unsigned){a} >= (unsigned){b})'
class Ugt(Component):
    def __init__(self):
        super().__init__('ugt')

    def semantics(self, a, b):
        return z3.If(z3.UGT(a, b), z3.BitVecVal(-1, NUM_OF_BITS), z3.BitVecVal(0, NUM_OF_BITS))

    def expression(self, a, b, model) -> str:
        return f'-((unsigned){a} > (unsigned){b})'
class Eq(Component):
    def __init__(self):
        super().__init__('eq')

    def semantics(self, a, b):
        return z3.If(a == b, z3.BitVecVal(-1, NUM_OF_BITS), z3.BitVecVal(0, NUM_OF_BITS))

    def expression(self, a, b, model) -> str:
        return f'-((unsigned){a} > (unsigned){b})'
class Eq2(Component):
    def __init__(self):
        super().__init__('eq')

    def semantics(self, a, b):
        return z3.If(a == b, z3.BitVecVal(-1, NUM_OF_BITS), z3.BitVecVal(0, NUM_OF_BITS))

    def expression(self, a, b, model) -> str:
        return f'-((unsigned){a} > (unsigned){b})'
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
# IfThenElse wasn't used in any of 25 Hacker's delight problems and just added
# for testing purposes
class IfThenElse(Component):
    def __init__(self):
        super().__init__('if-then-else')

    def semantics(self, a, b, c):
        return z3.If(a != 0, b, c)

    def expression(self, a, b, c, model) -> str:
        return f'{a} ? {b} : {c}'

def std_lib() :
    return [
        Add(),
        Sub(),
        And(),
        Or(),
        Not(),
        Xor(),
        SignBit(),
        NegSignBit(),
        Ugt(),
        Ule(),
        Uge(),
        VaradicConstant(),
    ]

def full_lib() :
    return [
        Add(),
        Sub(),
        And(),
        Or(),
        Not(),
        Xor(),
        SignBit(),
        NegSignBit(),
        Ugt(),
        Ule(),
        Uge(),
        VaradicConstant(),
    ]
def min_lib() :
    return [
        Add(),
        Sub(),
        And(),
        Or(),
        Not(),
        Xor(),
        VaradicConstant(),
    ]
def p10_lib() :
    return [
        Add(),
        Sub(),
        And(),
        Or(),
        Not(),
        Xor(),
        Ule(),
        VaradicConstant(),

    ]
def p11_lib() :
    return [
        Add(),
        Sub(),
        And(),
        Or(),
        Not(),
        Xor(),
        Ugt(),
        VaradicConstant(),
    ]
def p13_lib() :
    return [
        And(),
        Xor(),
        Add(),
        Shr(),
        Shr2(),
        Sub(),
        Or(),
        Not(),
        Ugt(),
        Ule(),
        Uge(),
        VaradicConstant(),
    ]
def p14_lib() :
    return [
        And(),
        Xor(),
        Add(),
        Shr(),
        Sub(),
        Or(),
        Not(),
        VaradicConstant(),
    ]
def p15_lib() :
    return [
        Shr(),
        Add(),
        Sub(),
        And(),
        Or(),
        Not(),
        Xor(),
        VaradicConstant(),
    ]
def p16_lib() :
    return [
        And(),
        Not(),
        Xor(),
        Xor2(),
        Shr(),
        Add(),
        Sub(),        
        Or(),
        Uge(),
        Ugt(),
        Ule(),
        VaradicConstant(),
    ]
def p19_lib() :
    return [
        And(),
        Xor(),
        Xor2(),
        Xor3(),
        Shr(),
        Shl(),
        VaradicConstant(),
    ]
def p21_lib() :
    return [
        Eq(),
        Eq2(),
        And(),
        And2(),
        Xor(),
        Xor2(),
        Xor3(),
        Xor4(),
        Not(),
        Not2(),
        VaradicConstant(),
    ]

'''
here the returned "location" of synthesizer turned to readable "program"
this part mainly borrowed from fitzgen's Rust implementation.
although the variable names seems somehow "awkward"! but the program itself is correct
example look like this(generated solution for problem #2):
def f(x0):
    v0 = x0 - x0
    v1 = -((unsigned)v0 >= (unsigned)v0)
    v4 = ~x0
    v5 = v1 + v4
    v6 = x0 ^ v5
    v10 = v6 & x0
    return v10
'''
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

'''
adding wellformedness constraints.
here all constraints "AND"ed together and are aggregated in "cons" as a
list and "z3.And(*cons)" returned
'''
def wfp_cons(input_location: List, lPR: List[Tuple], lOutput):
    cons = []
    nInput = len(input_location)
    nLib = len(lPR)
    for lParams, lRet in lPR:
        for lParam in lParams:
            cons.append(z3.And(0 <= lParam, lParam < nInput + nLib))
        cons.append(z3.And(nInput <= lRet, lRet < nInput + nLib))
    cons.append(z3.And(0 <= lOutput, lOutput < nInput + nLib))
    for i, lInp in enumerate(input_location) :
        cons.append(lInp == i)
    lRets = tuple(zip(*lPR))[1]
    for i in range(len(lRets)):
        for j in range(i):
            cons.append(lRets[i] != lRets[j])
    for lParams, lRet in lPR:
        for lParam in lParams:
            cons.append(lParam < lRet)
    return z3.And(*cons)

'''
adding connection constraints.
we used "z3.Implies" for connectiong location's and values
'''
def conn_cons(input_location: List, lPR: List[Tuple], lOutput, input_value: List, vPR: List[Tuple], vOutput):
    cons = []
    lList = input_location + [lOutput]
    for lParams, lRet in lPR:
        lList += lParams
        lList.append(lRet)   
    vList = input_value + [vOutput]
    for vParams, vRet in vPR:
        vList += vParams
        vList.append(vRet) 
    n = len(lList)
    assert n == len(vList)
    for i in range(n):
        for j in range(i):
            cons.append(z3.Implies(lList[i] == lList[j], vList[i] == vList[j]))
    return z3.And(*cons)

'''
adding library constraints.
here, used libraries semantics will added to Solver.
'''
def lib_cons(vPR: List[Tuple], lib: List[Component]):
    cons = []
    for (vParam, vRet), comp in zip(vPR, lib):
        cons.append(vRet == comp.semantics(*vParam))
    return z3.And(*cons)

'''
just for logging time of synthesis in .csv file
'''
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

'''
the main part of Body. in the synthesized class the main synthesized and the
verifier defined and bounded together.
comments inside!
'''
class Synthesizer:
    def __init__(self, nInput, spec, lib=std_lib):
        self.nInput = nInput
        self.lib = lib()
        self.spec = lambda input_value, vOutput: spec(vOutput, *input_value)

    def synthesize(self, max_iter=100, timeout=120000) :
        lib = self.lib
        nInput = self.nInput
        '''
        generating requierd variables for  making SMT-Solver understand's the connections
        '''
        def name_generator(prefix, num):
            return [f'{prefix}_{i}' for i in range(num)]
        def generate_location_variables(prefix):
            input_location = list(z3.Ints(name_generator(f'{prefix}_input_location', nInput)))
            lPR = [
                (   
                    list(z3.Ints(name_generator(f'{prefix}_parameter_location_{i}', comp.arity))), 
                    z3.Int(f'{prefix}_return_location_{i}')
                ) for i, comp in enumerate(lib)
            ]
            lOutput = z3.Int(f'{prefix}_output_location')
            return input_location, lPR, lOutput
        def make_value_variables(prefix):
            input_value = list(z3.BitVecs(name_generator(f'{prefix}_input_value', nInput), NUM_OF_BITS))
            vPR = [
                (
                    list(z3.BitVecs(name_generator(f'{prefix}_parameter_value_{i}', comp.arity), NUM_OF_BITS)), 
                    z3.BitVec(f'{prefix}_returned_value_{i}', NUM_OF_BITS)
                ) for i, comp in enumerate(lib)
            ]
            vOutput = z3.BitVec(f'{prefix}_output_value', NUM_OF_BITS)
            return input_value, vPR, vOutput
        input_location, lPR, lOutput = generate_location_variables('location_variables')
        counter_example_input_value, cevPR, cevOutput = make_value_variables('value_variables')
        
        #main synthesizer
        synthesizer = z3.Solver()
        synthesizer.set(timeout=timeout)
        synthesizer.add(wfp_cons(input_location, lPR, lOutput))
        #verifier 
        verifier = z3.Solver()
        verifier.set(timeout=timeout)
        verifier.add(conn_cons(input_location, lPR, lOutput, counter_example_input_value, cevPR, cevOutput))
        verifier.add(lib_cons(cevPR, lib))
        verifier.add(z3.Not(self.spec(counter_example_input_value, cevOutput)))
        
        # starting synthesis procedure
        for iteration in range(1, max_iter):
            print(f'> Running iteration {iteration} ...')
            # Step 1. synthesize
            check_result = synthesizer.check()
            if check_result == z3.sat:
                syn_model = synthesizer.model()
                program = Program(nInput, syn_model, lPR, lOutput, lib)
                # in this case, verifier should check the answer
            elif check_result == z3.unsat:
                # in this case this is impossible to find any program that
                # satisfies the specification
                return None 
            else:
                return None

            # Step 2. Verification
            '''
            here we use .push() and .pop() because each time verifier should check the
            brand new solution provided by synthesizer (the locations changed by
            the synthesizer and old locations should be dropped.
            in RUST implementation, each time a new Z3.solver defined and used)
            '''
            verifier.push()
            for lv in input_location:
                verifier.add(lv == syn_model.eval(lv, True))
            for lParams, lRet in lPR:
                for lParam in lParams:
                    verifier.add(lParam == syn_model.eval(lParam, True))
                verifier.add(lRet == syn_model.eval(lRet, True))
            verifier.add(lOutput == syn_model.eval(lOutput, True))

            for comp in lib:
                for param in comp.parameters() :
                    verifier.add(param == syn_model.eval(param, True))

            check_result = verifier.check()
            if check_result == z3.unsat:
                # here, there was no counter example and synthesis procedure terminates successfully.
                return program
            elif check_result == z3.sat:
                # here the finded counter example feeded back to main synthesizer
                ver_model = verifier.model()
                cvInput, cvPR, cvOutput = make_value_variables(f'c{iteration}')
                synthesizer.add(lib_cons(cvPR, lib))
                synthesizer.add(conn_cons(input_location, lPR, lOutput, cvInput, cvPR, cvOutput))
                synthesizer.add(self.spec(cvInput, cvOutput))
                for cevI, cvI in zip(counter_example_input_value, cvInput) :
                    synthesizer.add(cvI == ver_model.eval(cevI, True))
            else:
                return None
            verifier.pop()
        return None

# initialize the code
timestr = time.strftime("%Y%m%d_%H%M%S")
log_file_name = 'Log_' + timestr + '.csv'
log = ResultWriter('Logs',log_file_name)
log.create(['problem', 'Z3', 'CVC4', 'CVC5']) 
problem_num = 0
z3_time = 0
cvc4_time = 0
cvc5_time = 0
log.write([problem_num, z3_time, cvc4_time, cvc5_time])
# specifications passed to solver as lambda functions utilizing Z3 function's like Z3.If, Z3.ULE and...
problems = [
    lambda y, x: y == x, #p0
    lambda y, x : y == (x & (x - 1)), #p1
    lambda y, x : y == (x & (x + 1)), #p2
    lambda y, x : y == (x & (~x + 1)), #p3
    lambda y, x : y == (x ^ (x - 1)), #p4
    lambda y, x : y == (x | (x - 1)), #p5
    lambda y, x : y == (x | (x + 1)),#p6
    lambda y, x : y == (~x & (x + 1)),#p7
    lambda y, x : y == ((x - 1) & ~x),#p8
    lambda y, x : y == ((x ^ (x >> (NUM_OF_BITS - 1))) - (x >> (NUM_OF_BITS - 1))),#p9
    lambda y, a, b: If(ULE(a & b, a ^ b), y != 0, y == 0), #p10
    lambda y, z, x : y == If(UGT(x & ~z, z), (x | ~x), (x & ~x)),#p11
    lambda y, z, x : y == If(ULE(x & ~z, z), (x | ~x), (x & ~x)),#p12
    lambda y, x : y == ((x >> (NUM_OF_BITS - 1)) | (~x >> (NUM_OF_BITS - 1))),#p13
    lambda y, z, x : y == ((x & z) + ((x ^ z) >> 1)),#p14
    lambda y, z, x : y == ((x | z) - ((x ^ z) >> 1)),#p15
    lambda y, z, x : y == (((x ^ z) & (~(If(UGE(x, z), (x | ~x), (x & ~x))))) ^ z),#p16
    lambda y, x : y == (((x | (x - 1)) + 1) & x),#p17
    lambda y, x: y == x, #p0==p18
    lambda y, x, k, m : y == (((((x ^ (x >> k)) & m) << k) ^ ((x ^ (x >> k)) & m)) ^ x),#p19
    lambda y, x : y == ((((x ^ (x & ~x)) >> 2) / (x & ~x)) | (x + (x & ~x))),#p20
    lambda y, x, a, b, c : y == ((((~(~(x ^ c))) & (a ^ c)) ^ ((~(~(x ^ a))) & (b ^ c))) ^ c),#p21
    lambda y, x : y == (((((((x >> 1) ^ x) ^ (x - ((x >> 1) ^ x))) & 0x1111) * 0x1111) >> 28) & 0x1),#p22
    lambda y, x : y == ((((((x - ((x >> 1) & 0x5555)) & 0x3333) + ((x - ((x >> 1) & 0x5555)) & 0x3333)) >> 4) + (((x - ((x >> 1) & 0x5555)) & 0x3333) + ((x - ((x >> 1) & 0x5555)) & 0x3333))) & 0x0F0F),#p23
    lambda y, x : y == (((((((x - 1) | ((x - 1) >> 1)) | (((x - 1) | ((x - 1) >> 1)) >> 2)) | ((((x - 1) | ((x - 1) >> 1)) | (((x - 1) | ((x - 1) >> 1)) >> 2)) >> 4)) | (((((x - 1) | ((x - 1) >> 1)) | (((x - 1) | ((x - 1) >> 1)) >> 2)) | ((((x - 1) | ((x - 1) >> 1)) | (((x - 1) | ((x - 1) >> 1)) >> 2)) >> 4)) >> 8)) >> 16) + 1),#p24
    lambda y, z, x : y == (((x & 0xFFFF) * (z >> 16) + ((((x >> 16) * (z & 0xFFFF)) & (((x & 0xFFFF) * (z & 0xFFFF)) >> 16)) & 0xFFFF)) >> 16) + (((x >> 16) * (z & 0xFFFF) + (((x & 0xFFFF) * (z & 0xFFFF)) >> 16)) >> 16) + (x >> 16) + (z >> 16), #p25
]

# example: 
problem_num = 2
problem_specification = problems[problem_num]
print(f'Synthesizing Problem #{problem_num} ...')
arity = len(inspect.getfullargspec(problem_specification)[0]) - 1
synth = Synthesizer(arity, problem_specification,full_lib)
program = None
start_time = process_time()
program = synth.synthesize()
print(program)
z3_time = process_time() - start_time
print("time is: {0:0.2f} sec".format(z3_time))
log.write([problem_num, z3_time, 0, 0])

