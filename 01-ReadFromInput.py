from z3 import *

constraint = eval(input('>>> '))
print(constraint)

input_specification = lambda y, a: y == a & (a - 1)
print("hi")



class brahma_synthesizer:
    def __init__(self, user_specifications):
        self.specifications = lambda user_Input, user_Output: user_specifications(user_Output, user_Input)
    
    def synthesize(self):
        s = z3.Solver()
        z3_Input = z3.BitVec('z3_Input', 32)
        z3_Output = z3.BitVec('z3_Output', 32)
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