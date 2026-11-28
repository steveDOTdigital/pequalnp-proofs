import EightVertexOneNot32991

namespace TwinLeafTables32991

/-- First row order removes vertex 4. The other keeps vertices 4 and 2 at zero. -/
def twinRow (r : Fin 128) (i : Fin 8) : Bool :=
  if i.val < 4 then r.val.testBit i.val
  else if i.val = 4 then false else r.val.testBit (i.val - 1)

def leafRow (r : Fin 64) (i : Fin 8) : Bool :=
  if i.val < 2 then r.val.testBit i.val
  else if i.val = 2 || i.val = 4 then false
  else if i.val = 3 then r.val.testBit 2 else r.val.testBit (i.val - 2)

def leafRowHigh (r : Fin 64) (i : Fin 8) : Bool :=
  if i.val = 2 then true else leafRow r i

def twin : BitVec 128 := 0xffffffffffffeeeefffefffceeeeaa00

def leafLow : BitVec 64 := 0xffffffeefefceea0

def leafHigh : BitVec 64 := 0xffffffeeffffeea0

set_option maxRecDepth 10000 in
theorem twinTable : ∀ r : Fin 128,
    EightVertexOneNot32991.posted (twinRow r) = twin.getLsbD r.val := by decide +kernel

set_option maxRecDepth 10000 in
theorem leafLowTable : ∀ r : Fin 64,
    EightVertexOneNot32991.posted (leafRow r) = leafLow.getLsbD r.val := by decide +kernel

set_option maxRecDepth 10000 in
theorem leafHighTable : ∀ r : Fin 64,
    EightVertexOneNot32991.posted (leafRowHigh r) = leafHigh.getLsbD r.val := by decide +kernel

#print axioms twinTable
#print axioms leafLowTable
#print axioms leafHighTable

end TwinLeafTables32991
