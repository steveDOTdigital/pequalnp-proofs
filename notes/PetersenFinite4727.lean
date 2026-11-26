import PEqualNP.Defs.MetaComplexity
import PEqualNP.Defs.NotBracket

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenFinite4727

attribute [local instance] lineDegreeGateOpDecEq

abbrev Input := Fin 10 → Bool
def graph : Input → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ))

/-- There are at most 29 live wires. Index 29 represents every invalid read. -/
def cap (i : Nat) : Fin 30 := ⟨min i 29, by omega⟩

structure Slot where
  kind : Fin 3
  first : Option (Fin 30)
  second : Option (Fin 30)

def Slot.gate (s : Slot) : Gate :=
  ⟨if s.kind = 0 then .and else if s.kind = 1 then .or else .not,
   (s.first.toList ++ s.second.toList).map Fin.val⟩

def encode (g : Gate) : Slot :=
  ⟨if g.op = .and then 0 else if g.op = .or then 1 else 2,
   g.inputs[0]?.map cap, g.inputs[1]?.map cap⟩

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem kind_ok {g : Gate} (h : legal g) : (encode g).gate.op = g.op := by
  rcases h.1 with k | k | k <;> simp [encode,Slot.gate,k]

theorem pins_ok {g : Gate} (h : legal g) :
    (encode g).gate.inputs = g.inputs.map (fun i => (cap i).val) := by
  have len := h.2
  cases e : g.inputs with
  | nil => simp [encode,Slot.gate,e]
  | cons a xs =>
    cases xs with
    | nil => simp [encode,Slot.gate,e]
    | cons b tail =>
      have ht : tail = [] := by
        rw [e] at len
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at len
        omega
      subst tail
      simp [encode,Slot.gate,e]

theorem cappedRead (w : List Bool) (i : Nat) (small : w.length ≤ 29) :
    w.getD (cap i).val false = w.getD i false := by
  by_cases hi : i ≤ 29
  · simp [cap,Nat.min_eq_left hi]
  · have hc : w.length ≤ (cap i).val := by change w.length ≤ min i 29; omega
    have hw : w.length ≤ i := by omega
    simp only [List.getD,List.getElem?_eq_none hc,List.getElem?_eq_none hw]


def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_ok (w : List Bool) (g : Gate) (h : legal g) (sw : w.length ≤ 29) :
    step w (encode g).gate = step w g := by
  have reads (i : Nat) := cappedRead w i sw
  simp only [step,kind_ok h,pins_ok h,List.map_map,Function.comp_def,reads]

private def normalized (gs : List Gate) := gs.map fun g => (encode g).gate

theorem fold_ok (gs : List Gate) (w : List Bool) (h : ∀ g ∈ gs, legal g)
    (sw : w.length + gs.length ≤ 29) :
    (normalized gs).foldl step w = gs.foldl step w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (normalized gs).foldl step (step w (encode g).gate) = gs.foldl step (step w g)
    rw [step_ok w g (h g (by simp)) (by omega)]
    apply ih (w := step w g)
    · intro a ha; exact h a (by simp [ha])
    · simp [step] at *
      omega

private def negs (gs : List Gate) := (gs.filter fun g => decide (g.op = GateOp.not)).length

theorem count_ok (gs : List Gate) (h : ∀ g ∈ gs, legal g) :
    negs (normalized gs) = negs gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have tail := ih (fun a ha => h a (by simp [ha]))
    have hh := kind_ok (h g (by simp))
    change (( (encode g).gate :: normalized gs).filter _).length = ((g :: gs).filter _).length
    simp only [List.filter_cons,hh]
    split <;> simp_all [negs]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons,ih,step]; omega

def decode {n : Nat} (p : Fin n → Slot) (o : Fin 30) : Circuit :=
  ⟨List.ofFn (fun i => (p i).gate),o.val⟩

theorem slot_legal (s : Slot) : legal s.gate := by
  constructor
  · by_cases k : s.kind = 0
    · simp [Slot.gate,k]
    · by_cases j : s.kind = 1 <;> simp [Slot.gate,k,j]
  · cases s with
    | mk kind a b => cases a <;> cases b <;> simp [Slot.gate]

theorem decoded_legal {n : Nat} (p : Fin n → Slot) (o : Fin 30) : FanInTwo (decode p o) := by
  intro g hg
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hg
  exact slot_legal (p i)

theorem clone (c : Circuit) (basis : FanInTwo c) (size : c.size ≤ 19) :
    ∃ (n : Fin 20) (p : Fin n.val → Slot) (o : Fin 30),
      PEqualNP.NotBracket.notCount (decode p o) = PEqualNP.NotBracket.notCount c ∧
      ∀ x : Input, (decode p o).eval (List.ofFn x) = c.eval (List.ofFn x) := by
  let n : Fin 20 := ⟨c.gates.length,by change c.gates.length ≤ 19 at size; omega⟩
  let p : Fin n.val → Slot := fun i => encode (c.gates.get i)
  have h : ∀ g ∈ c.gates, legal g := basis
  have eqs : (decode p (cap c.output)).gates = normalized c.gates := by
    change List.ofFn (fun i => (encode (c.gates.get i)).gate) = normalized c.gates
    apply List.ext_getElem
    · simp [normalized]
    · intro i hi hj
      simp only [List.getElem_ofFn,normalized,List.getElem_map,List.get_eq_getElem]
  refine ⟨n,p,cap c.output,?_,?_⟩
  · change negs (decode p (cap c.output)).gates = negs c.gates
    rw [eqs,count_ok c.gates h]
  · intro x
    change (((decode p (cap c.output)).gates).foldl step (List.ofFn x)).getD (cap c.output).val false =
      (c.gates.foldl step (List.ofFn x)).getD c.output false
    rw [eqs,fold_ok _ _ h (by change c.gates.length ≤ 19 at size; simp; omega)]
    apply cappedRead
    rw [fold_length,List.length_ofFn]
    change c.gates.length ≤ 19 at size
    omega

def unpack (r : Fin 1024) (i : Fin 10) := r.val.testBit i.val

theorem represent (x : Input) : ∃ r : Fin 1024, unpack r = x := by
  let b := BitVec.ofBoolListLE (List.ofFn x)
  let r : Fin 1024 := ⟨b.toNat,by have h := b.isLt; simpa [b] using h⟩
  refine ⟨r,?_⟩
  funext i
  change b.getLsbD i.val = x i
  simp only [b,BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]

/-- The search obligation is entirely finite, including the optional selectors,
the NOT count, the choice of output and all 1,024 Boolean inputs. -/
def FiniteExclusion : Prop :=
  ∀ (n : Fin 20) (p : Fin n.val → Slot) (o : Fin 30),
    1 ≤ PEqualNP.NotBracket.notCount (decode p o) →
    PEqualNP.NotBracket.notCount (decode p o) ≤ 4 →
    ¬ ∀ r : Fin 1024, (decode p o).eval (List.ofFn (unpack r)) = graph (unpack r)

/-- Each word stores one bit for every ten-input assignment. -/
def pack (f : Fin 1024 → Bool) : Nat := (BitVec.ofBoolListLE (List.ofFn f)).toNat

theorem bit_pack (f : Fin 1024 → Bool) (r : Fin 1024) : (pack f).testBit r.val = f r := by
  change (BitVec.ofBoolListLE (List.ofFn f)).getLsbD r.val = f r
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD,List.getElem?_ofFn,dite_eq_left r.isLt,Option.getD_some]

def ones := pack fun _ => true
def inputs : List Nat := List.ofFn fun i : Fin 10 => pack fun r => unpack r i
def target := pack fun r => graph (unpack r)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The target word used by the independent prefix search. -/
theorem target_word : target =
    ([0xffeafaeaffeaf8c8, 0xffeefeeeffeefccc, 0xfffffffffffaf8f8, 0xfffffffffffefcfc,
      0xffffffffffeaffc8, 0xffffffffffffffff, 0xfffffffffffafff8, 0xffffffffffffffff,
      0xfffffaeafffff8c8, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
      0xffffffffffffffc8, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff] : List Nat).foldr
      (fun limb acc => limb + (2^64) * acc) 0 := by decide +kernel

theorem input_bits (r : Fin 1024) :
    inputs.map (fun w => w.testBit r.val) = List.ofFn (unpack r) := by
  apply List.ext_getElem
  · simp only [inputs,List.length_map,List.length_ofFn]
  · intro i hi hj
    simp only [inputs,List.getElem_map,List.getElem_ofFn,bit_pack]

def readPin (w : List Nat) (absent : Nat) : Option (Fin 30) → Nat
  | none => absent
  | some i => w.getD i.val 0

def wordStep (w : List Nat) (s : Slot) : List Nat :=
  w ++ [if s.kind = 0 then readPin w ones s.first &&& readPin w ones s.second
        else if s.kind = 1 then readPin w 0 s.first ||| readPin w 0 s.second
        else (readPin w 0 (s.first.or s.second)) ^^^ ones]

theorem bit_read (w : List Nat) (i j : Nat) :
    (w.getD i 0).testBit j = (w.map fun t => t.testBit j).getD i false := by
  simp only [List.getD,List.getElem?_map]
  cases w[i]? <;> simp

theorem step_bits (s : Slot) (w : List Nat) (r : Fin 1024) :
    (wordStep w s).map (fun t => t.testBit r.val) = step (w.map fun t => t.testBit r.val) s.gate := by
  have unit : ones.testBit r.val = true := bit_pack _ r
  have readOption (u : Option Nat) : (u.getD 0).testBit r.val =
      (u.map (fun t => t.testBit r.val)).getD false := by cases u <;> simp
  obtain ⟨k,a,b⟩ := s
  by_cases andGate : k = 0 <;> by_cases orGate : k = 1 <;>
    cases a <;> cases b <;>
    simp [wordStep,Slot.gate,step,andGate,orGate,readPin,GateOp.eval,
      Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,unit,readOption,Option.or]

theorem fold_bits (p : List Slot) (w : List Nat) (r : Fin 1024) :
    (p.foldl wordStep w).map (fun t => t.testBit r.val) =
      (p.map Slot.gate).foldl step (w.map fun t => t.testBit r.val) := by
  induction p generalizing w with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.foldl_cons,List.map_cons,ih,step_bits]

theorem output_bit {n : Nat} (p : Fin n → Slot) (o : Fin 30) (r : Fin 1024) :
    (((List.ofFn p).foldl wordStep inputs).getD o.val 0).testBit r.val =
      (decode p o).eval (List.ofFn (unpack r)) := by
  rw [bit_read,fold_bits,input_bits]
  change ((List.map Slot.gate (List.ofFn p)).foldl step (List.ofFn (unpack r))).getD o.val false =
    ((List.ofFn (fun i => (p i).gate)).foldl step (List.ofFn (unpack r))).getD o.val false
  rw [List.map_ofFn]
  rfl

def WordExclusion : Prop :=
  ∀ (n : Fin 20) (p : Fin n.val → Slot) (o : Fin 30),
    1 ≤ PEqualNP.NotBracket.notCount (decode p o) →
    PEqualNP.NotBracket.notCount (decode p o) ≤ 4 →
    pack (fun r => (((List.ofFn p).foldl wordStep inputs).getD o.val 0).testBit r.val) ≠ target

theorem words_iff_finite : WordExclusion ↔ FiniteExclusion := by
  constructor
  · intro words n p o low high allRows
    apply words n p o low high
    unfold target
    congr 1
    funext r
    exact (output_bit p o r).trans (allRows r)
  · intro finite n p o low high equal
    apply finite n p o low high
    intro r
    have bit := congrArg (fun w : Nat => w.testBit r.val) equal
    simp only [target,bit_pack,output_bit] at bit
    exact bit

theorem finite_iff_posted : FiniteExclusion ↔ (have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (19 : ℕ) → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x2 → PEqualNP.NotBracket.notCount x2 ≤ (4 : ℕ) → ¬∀ (x7 : Fin (10 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) := by
  change FiniteExclusion ↔ ∀ c : Circuit, FanInTwo c → c.size ≤ 19 →
    1 ≤ PEqualNP.NotBracket.notCount c → PEqualNP.NotBracket.notCount c ≤ 4 →
    ¬ ∀ x : Input, c.eval (List.ofFn x) = graph x
  constructor
  · intro excluded c basis size lo hi correct
    obtain ⟨n,p,o,count,eqs⟩ := clone c basis size
    apply excluded n p o (count ▸ lo) (count ▸ hi)
    intro r
    exact (eqs (unpack r)).trans (correct (unpack r))
  · intro posted n p o lo hi allRows
    apply posted (decode p o) (decoded_legal p o) (by
      change (List.ofFn (fun i => (p i).gate)).length ≤ 19
      rw [List.length_ofFn]; have h := n.isLt; omega) lo hi
    intro x
    obtain ⟨r,rfl⟩ := represent x
    exact allRows r

end PetersenFinite4727
