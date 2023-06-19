from z3 import *

# Defining all necessary variables

## Components Locations and Inputs
L_I11, L_I22, L_I33, L_I33p = BitVecs('L_I11 L_I22 L_I33 L_I33p', 8)
I11, I22, I33, I33p = BitVecs('I11 I22 I33 I33p', 8)

## Components Locations and Outputs
L_O11, L_O22, L_O33 = BitVecs('L_O11 L_O22 L_O33', 8)
O11, O22, O33 = BitVecs('O11 O22 O33', 8)

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
wfp_cons = [L_O11 != L_O22,
            L_O11 != L_O33,
            L_O22 != L_O33]

## Setting Acyclicity Constraints
wfp_acyc = [
    L_I11 < L_O11,
    L_I22 < L_O22,
    L_I33 < L_O33,
    L_I33p < L_O33
]

## Setting Other Constraints
wfp_other = [
    0 <= LI,
    LI <= 0,
    0 <= L_I11,
    L_I11 <= 3,
    0 <= L_I22,
    L_I22 <= 3,
    0 <= L_I33,
    L_I33 <= 3,
    0 <= L_I33p,
    L_I33p <= 3,
    1 <= L_O11,
    L_O11 <= 3,
    1 <= L_O22,
    L_O22 <= 3,
    1 <= L_O33,
    L_O33 <= 3,
    1 <= LO,
    LO <= 3
]

## Gathering all constraints above in one assertion term
wfp = wfp_cons + wfp_acyc + wfp_other

# Setting components definition constraints
lib = And(
    O11 == ~ I11,
    O22 == I22 + 1,
    O33 == I33 & I33p
)

# Setting connectivity constraints
conn = And(
    Implies(LI == LO, I == O),
    Implies(LI == L_I11, I == I11),
    Implies(LI == L_I22, I == I22),
    Implies(LI == L_I33, I == I33),
    Implies(LI == L_I33p, I == I33p),
    Implies(LI == L_O11, I == O11),
    Implies(LI == L_O22, I == O22),
    Implies(LI == L_O33, I == O33),
    Implies(LO == L_I11, O == I11),
    Implies(LO == L_I22, O == I22),
    Implies(LO == L_I33, O == I33),
    Implies(LO == L_I33p, O == I33p),
    Implies(LO == L_O11, O == O11),
    Implies(LO == L_O22, O == O22),
    Implies(LO == L_O33, O == O33),
    Implies(L_I11 == L_I22, I11 == I22),
    Implies(L_I11 == L_I33, I11 == I33),
    Implies(L_I11 == L_I33p, I11 == I33p),
    Implies(L_I11 == L_O11, I11 == O11),
    Implies(L_I11 == L_O22, I11 == O22),
    Implies(L_I11 == L_O33, I11 == O33),
    Implies(L_I22 == L_I33, I22 == I33),
    Implies(L_I22 == L_I33p, I22 == I33p),
    Implies(L_I22 == L_O11, I22 == O11),
    Implies(L_I22 == L_O22, I22 == O22),
    Implies(L_I22 == L_O33, I22 == O33),
    Implies(L_I33 == L_I33p, I33 == I33p),
    Implies(L_I33 == L_O11, I33 == O11),
    Implies(L_I33 == L_O22, I33 == O22),
    Implies(L_I33 == L_O33, I33 == O33),
    Implies(L_I33p == L_O11, I33p == O11),
    Implies(L_I33p == L_O22, I33p == O22),
    Implies(L_I33p == L_O33, I33p == O33),
    Implies(L_O11 == L_O22, O11 == O22),
    Implies(L_O11 == L_O33, O11 == O33),
    Implies(L_O22 == L_O33, O22 == O33)
)

# Setting programs specification constraints
spec = And(
    Implies(And(Is[7] == 1, Is[6] == 1, Is[5] == 1, Is[4] == 1, Is[3] == 1, Is[2] == 1, Is[1] == 1, Is[0] == 1),
             And(Os[7] == 0, Os[6] == 0, Os[5] == 0, Os[4] == 0, Os[3] == 0, Os[2] == 0, Os[1] == 0, Os[0] == 0)),
    Implies(And(Is[7] == 0, Is[6] == 1, Is[5] == 1, Is[4] == 1, Is[3] == 1, Is[2] == 1, Is[1] == 1, Is[0] == 1),
             And(Os[7] == 1, Os[6] == 0, Os[5] == 0, Os[4] == 0, Os[3] == 0, Os[2] == 0, Os[1] == 0, Os[0] == 0)),
    Implies(And(Is[6] == 0, Is[5] == 1, Is[4] == 1, Is[3] == 1, Is[2] == 1, Is[1] == 1, Is[0] == 1),
             And(Os[7] == 0, Os[6] == 1, Os[5] == 0, Os[4] == 0, Os[3] == 0, Os[2] == 0, Os[1] == 0, Os[0] == 0)),
    Implies(And(Is[5] == 0, Is[4] == 1, Is[3] == 1, Is[2] == 1, Is[1] == 1, Is[0] == 1),
             And(Os[7] == 0, Os[6] == 0, Os[5] == 1, Os[4] == 0, Os[3] == 0, Os[2] == 0, Os[1] == 0, Os[0] == 0)),
    Implies(And(Is[4] == 0, Is[3] == 1, Is[2] == 1, Is[1] == 1, Is[0] == 1),
             And(Os[7] == 0, Os[6] == 0, Os[5] == 0, Os[4] == 1, Os[3] == 0, Os[2] == 0, Os[1] == 0, Os[0] == 0)),
    Implies(And(Is[3] == 0, Is[2] == 1, Is[1] == 1, Is[0] == 1),
             And(Os[7] == 0, Os[6] == 0, Os[5] == 0, Os[4] == 0, Os[3] == 1, Os[2] == 0, Os[1] == 0, Os[0] == 0)),
    Implies(And(Is[2] == 0, Is[1] == 1, Is[0] == 1),
             And(Os[7] == 0, Os[6] == 0, Os[5] == 0, Os[4] == 0, Os[3] == 0, Os[2] == 1, Os[1] == 0, Os[0] == 0)),
    Implies(And(Is[1] == 0, Is[0] == 1),
             And(Os[7] == 0, Os[6] == 0, Os[5] == 0, Os[4] == 0, Os[3] == 0, Os[2] == 0, Os[1] == 1, Os[0] == 0)),
    Implies(Is[0] == 0, And(Os[7] == 0, Os[6] == 0, Os[5] == 0, Os[4] == 0, Os[3] == 0, Os[2] == 0, Os[1] == 0, Os[0] == 1))
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

solve([Spec] + [I == 111] + Final_Assertion)
