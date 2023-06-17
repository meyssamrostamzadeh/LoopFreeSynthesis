from z3 import *

## Components Locations and Inputs
L_I1p, L_I2p, L_I2z = BitVecs('L_I1p L_I2p L_I2z', 8)
I1p, I2p, I2z = BitVecs('I1p I2p I2z', 8)

## Input and Output Locations and Outputs
L_O1p, L_O2p = BitVecs('L_O1p L_O2p', 8)
O1p, O2p = BitVecs('O1p O2p', 8)
I = BitVecVal(12, 8)
Is = [ BitVec('I%s' % i, 8) for i in range(8) ]
O = BitVecVal(13, 8)
Os = [ BitVec('O%s' % o, 8) for o in range(8) ]

# Setting components definition constraints
Conn = [And(Implies(True, I1p == I2p), Implies(True, 2 <= I1p))]

## Test Constraints
Cons = [0 <= I1p,
        I1p <= 2,
        2 <= I2p,
        I2p <= 4]

solve(Conn + Cons)
