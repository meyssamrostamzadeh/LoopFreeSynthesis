from z3 import *

s = Solver()

x = Bool("x")
y = Bool("y")
z = Bool("z")
f1 = Or([x,y,z])
s.add(f1)
f2 = Or([Not(x),Not(y)])
s.add(f2)
f3 = Or([Not(y),Not(z)])
s.add(f3)

print(s.check())
print(s.model())

