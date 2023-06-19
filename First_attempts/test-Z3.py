from z3 import *

# Defining all necessary variables

## Components Locations and Inputs
L_I1p, L_I2p, L_I2z = BitVecs('L_I1p L_I2p L_I2z', 8)
I1p, I2p, I2z = BitVecs('I1p I2p I2z', 8)

## Components Locations and Outputs
L_O1p, L_O2p = BitVecs('L_O1p L_O2p', 8)
O1p, O2p = BitVecs('O1p O2p', 8)

## Input and Output Locations and Outputs
LI, LO = BitVecs('LI LO', 8)
I = BitVec('I', 8)
Is = [ BitVec('I%s' % i, 8) for i in range(8) ]
O = BitVec('O', 8)
Os = [ BitVec('O%s' % o, 8) for o in range(8) ]

## Connecting input and output to their bits
Input_Assertion = I == Sum([Is[s]*2**s for s in range(8)])
Output_Assertion = O == Sum([Os[s]*2**s for s in range(8)])
IO_Assertions = And(Input_Assertion, Output_Assertion)

# Setting well-formedness constraints

## Setting Consistency Constraints
wfp_cons = [L_O1p != L_O2p]

## Setting Acyclicity Constraints
wfp_acyc = [
    L_I1p < L_O1p,
    L_I2p < L_O2p,
    L_I2z < L_O2p
]

## Setting Other Constraints
wfp_other = [
    0 <= LI,
    LI <= 0,
    0 <= L_I1p,
    L_I1p <= 2,
    0 <= L_I2p,
    L_I2p <= 2,
    0 <= L_I2z,
    L_I2z <= 2,
    1 <= L_O1p,
    L_O1p <= 2,
    1 <= L_O2p,
    L_O2p <= 2,
    1 <= LO,
    LO <= 2
]

## Gathering all constraints above in one assertion term
wfp = wfp_cons + wfp_acyc + wfp_other

# Setting components definition constraints
lib = And(
    O1p == I1p - 1,
    O2p == I2p & I2z
)

# Setting connectivity constraints
conn = And(
    Implies(LI == LO, I == O),
    Implies(LI == L_I1p, I == I1p),
    Implies(LI == L_I2p, I == I2p),
    Implies(LI == L_I2z, I == I2z),
    Implies(LI == L_O1p, I == O1p),
    Implies(LI == L_O2p, I == O2p),
    Implies(LO == L_I1p, O == I1p),
    Implies(LO == L_I2p, O == I2p),
    Implies(LO == L_I2z, O == I2z),
    Implies(LO == L_O1p, O == O1p),
    Implies(LO == L_O2p, O == O2p),
    Implies(L_I1p == L_I2p, I1p == I2p),
    Implies(L_I1p == L_I2z, I1p == I2z),
    Implies(L_I1p == L_O1p, I1p == O1p),
    Implies(L_I1p == L_O2p, I1p == O2p),
    Implies(L_I2p == L_I2z, I2p == I2z),
    Implies(L_I2p == L_O1p, I2p == O1p),
    Implies(L_I2p == L_O2p, I2p == O2p),
    Implies(L_I2z == L_O1p, I2z == O1p),
    Implies(L_I2z == L_O2p, I2z == O2p),
    Implies(L_O1p == L_O2p, O1p == O2p),
)

# Setting programs specification constraints
spec = And(
    Implies(And(Is[7] == 1, Is[6] == 0, Is[5] == 0, Is[4] == 0, Is[3] == 0, Is[2] == 0, Is[1] == 0, Is[0] == 0)
            , And(Os[7] == 0, Os[6] == Is[6], Os[5] == Is[5], Os[4] == Is[4], Os[3] == Is[3], Os[2] == Is[2], Os[1] == Is[1], Os[0] == Is[0])),
    Implies(And(Is[6] == 1, Is[5] == 0, Is[4] == 0, Is[3] == 0, Is[2] == 0, Is[1] == 0, Is[0] == 0),
             And(Os[7] == Is[7], Os[6] == 0, Os[5] == Is[5], Os[4] == Is[4], Os[3] == Is[3], Os[2] == Is[2], Os[1] == Is[1], Os[0] == Is[0])),
    Implies(And(Is[5] == 1, Is[4] == 0, Is[3] == 0, Is[2] == 0, Is[1] == 0, Is[0] == 0),
             And(Os[7] == Is[7], Os[6] == Is[6], Os[5] == 0, Os[4] == Is[4], Os[3] == Is[3], Os[2] == Is[2], Os[1] == Is[1], Os[0] == Is[0])),
    Implies(And(Is[4] == 1, Is[3] == 0, Is[2] == 0, Is[1] == 0, Is[0] == 0),
             And(Os[7] == Is[7], Os[6] == Is[6], Os[5] == Is[5], Os[4] == 0, Os[3] == Is[3], Os[2] == Is[2], Os[1] == Is[1], Os[0] == Is[0])),
    Implies(And(Is[3] == 1, Is[2] == 0, Is[1] == 0, Is[0] == 0),
             And(Os[7] == Is[7], Os[6] == Is[6], Os[5] == Is[5], Os[4] == Is[4], Os[3] == 0, Os[2] == Is[2], Os[1] == Is[1], Os[0] == Is[0])),
    Implies(And(Is[2] == 1, Is[1] == 0, Is[0] == 0),
             And(Os[7] == Is[7], Os[6] == Is[6], Os[5] == Is[5], Os[4] == Is[4], Os[3] == Is[3], Os[2] == 0, Os[1] == Is[1], Os[0] == Is[0])),
    Implies(And(Is[1] == 1, Is[0] == 0),
             And(Os[7] == Is[7], Os[6] == Is[6], Os[5] == Is[5], Os[4] == Is[4], Os[3] == Is[3], Os[2] == Is[2], Os[1] == 0, Os[0] == Is[0])),
    Implies(Is[0] == 1, And(Os[7] == Is[7], Os[6] == Is[6], Os[5] == Is[5], Os[4] == Is[4], Os[3] == Is[3], Os[2] == Is[2], Os[1] == Is[1], Os[0] == 0))
)

# Some other constraints on input bits
Icons = And(Or(Is[0] == 0, Is[0] == 1),
            Or(Is[1] == 0, Is[1] == 1),
            Or(Is[2] == 0, Is[2] == 1),
            Or(Is[3] == 0, Is[3] == 1),
            Or(Is[4] == 0, Is[4] == 1),
            Or(Is[5] == 0, Is[5] == 1),
            Or(Is[6] == 0, Is[6] == 1),
            Or(Is[7] == 0, Is[7] == 1))
Ocons = And(Or(Os[0] == 0, Os[0] == 1),
            Or(Os[1] == 0, Os[1] == 1),
            Or(Os[2] == 0, Os[2] == 1),
            Or(Os[3] == 0, Os[3] == 1),
            Or(Os[4] == 0, Os[4] == 1),
            Or(Os[5] == 0, Os[5] == 1),
            Or(Os[6] == 0, Os[6] == 1),
            Or(Os[7] == 0, Os[7] == 1))
Cons = And(Icons, Ocons)

# Gathering all constraints under one roof
Spec = And(spec, Cons, IO_Assertions)
prereq = And(lib, conn)
impl = [Implies(prereq, Spec)]
Final_Assertion = wfp + [prereq]

solve([Spec] + [I == 48] + Final_Assertion)
