import PEqualNP.Defs
import PEqualNP.Defs.LineDegree
import Mathlib.Data.Finset.Card

namespace PlaneSupport7915

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open Finset

inductive Tree (n : ℕ) where
  | raw (i : Fin n)
  | constant (value : Bool)
  | both (left right : Tree n)
  | either (left right : Tree n)

variable {n : ℕ}

def value (x : Fin n → Bool) : Tree n → Bool
  | .raw i => x i
  | .constant b => b
  | .both a b => value x a && value x b
  | .either a b => value x a || value x b

def degree (marked : Finset ℕ) : Tree n → ℕ
  | .raw i => if i.val ∈ marked then 1 else 0
  | .constant _ => 0
  | .both a b => degree marked a + degree marked b
  | .either a b => max (degree marked a) (degree marked b)

def shoreCount (marked : Finset ℕ) (support : Finset (Fin n)) : ℕ :=
  (support.filter fun i => i.val ∈ marked).card

theorem shoreUnion (marked : Finset ℕ) (s t : Finset (Fin n)) :
    shoreCount marked (s ∪ t) ≤ shoreCount marked s + shoreCount marked t := by
  unfold shoreCount
  rw [Finset.filter_union]
  exact Finset.card_union_le _ _

theorem supportOfTruth (tree : Tree n) (points lines : Finset ℕ) (x : Fin n → Bool)
    (accepted : value x tree = true) :
    ∃ S : Finset (Fin n), (∀ i ∈ S, x i = true) ∧
      shoreCount points S ≤ degree points tree ∧ shoreCount lines S ≤ degree lines tree ∧
      ∀ y : Fin n → Bool, (∀ i ∈ S, y i = true) → value y tree = true := by
  induction tree with
  | raw i =>
    refine ⟨{i},?_,?_,?_,?_⟩
    · intro j hj
      simpa [value, Finset.mem_singleton.mp hj] using accepted
    · by_cases h : i.val ∈ points
      · rw [degree, if_pos h]
        unfold shoreCount
        exact (Finset.card_filter_le _ _).trans (by simp)
      · simp [shoreCount,degree,h]
    · by_cases h : i.val ∈ lines
      · rw [degree, if_pos h]
        unfold shoreCount
        exact (Finset.card_filter_le _ _).trans (by simp)
      · simp [shoreCount,degree,h]
    · intro y active
      exact active i (by simp)
  | constant b =>
    exact ⟨∅,by simp,by simp [degree,shoreCount],by simp [degree,shoreCount],fun _ _ => accepted⟩
  | both a b ihA ihB =>
    change (value x a && value x b) = true at accepted
    obtain ⟨sa,onA,pointA,lineA,forceA⟩ := ihA (Bool.and_eq_true_iff.mp accepted).1
    obtain ⟨sb,onB,pointB,lineB,forceB⟩ := ihB (Bool.and_eq_true_iff.mp accepted).2
    refine ⟨sa ∪ sb,?_,?_,?_,?_⟩
    · intro i hi
      exact (Finset.mem_union.mp hi).elim (onA i) (onB i)
    · exact (shoreUnion points sa sb).trans (Nat.add_le_add pointA pointB)
    · exact (shoreUnion lines sa sb).trans (Nat.add_le_add lineA lineB)
    · intro y hot
      exact Bool.and_eq_true_iff.mpr ⟨forceA y (fun i hi => hot i (Finset.mem_union_left _ hi)),
        forceB y (fun i hi => hot i (Finset.mem_union_right _ hi))⟩
  | either a b ihA ihB =>
    change (value x a || value x b) = true at accepted
    rcases Bool.or_eq_true_iff.mp accepted with ha | hb
    · obtain ⟨sa,on,pa,la,force⟩ := ihA ha
      exact ⟨sa,on,pa.trans (le_max_left _ _),la.trans (le_max_left _ _),
        fun y hot => Bool.or_eq_true_iff.mpr (Or.inl (force y hot))⟩
    · obtain ⟨sb,on,pb,lb,force⟩ := ihB hb
      exact ⟨sb,on,pb.trans (le_max_right _ _),lb.trans (le_max_right _ _),
        fun y hot => Bool.or_eq_true_iff.mpr (Or.inr (force y hot))⟩

def treeAt (wires : List (Tree n)) (i : ℕ) : Tree n :=
  wires.getD i (.constant false)

def ands : List (Tree n) → Tree n
  | [] => .constant true
  | t::ts => .both t (ands ts)

def ors : List (Tree n) → Tree n
  | [] => .constant false
  | t::ts => .either t (ors ts)

def unrollGate (wires : List (Tree n)) (gate : Gate) : Tree n :=
  match gate.op with
  | .and => ands (gate.inputs.map (treeAt wires))
  | .or => ors (gate.inputs.map (treeAt wires))
  | _ => .constant false

theorem valueAnds (x : Fin n → Bool) (trees : List (Tree n)) :
    value x (ands trees) = (trees.map (value x)).all id := by
  induction trees with
  | nil => rfl
  | cons a rest ih => simp [ands,value,ih]

theorem valueOrs (x : Fin n → Bool) (trees : List (Tree n)) :
    value x (ors trees) = (trees.map (value x)).any id := by
  induction trees with
  | nil => rfl
  | cons a rest ih => simp [ors,value,ih]

theorem degreeAnds (marked : Finset ℕ) (trees : List (Tree n)) :
    degree marked (ands trees) = (trees.map (degree marked)).sum := by
  induction trees with
  | nil => rfl
  | cons a rest ih => simp [ands,degree,ih]

theorem degreeOrs (marked : Finset ℕ) (trees : List (Tree n)) :
    degree marked (ors trees) = (trees.map (degree marked)).foldr max 0 := by
  induction trees with
  | nil => rfl
  | cons a rest ih => simp [ors,degree,ih]

theorem mappedRead {A B : Type} (f : A → B) (xs : List A) (i : ℕ) (fallback : A) :
    f (xs.getD i fallback) = (xs.map f).getD i (f fallback) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases xs[i]? <;> rfl

theorem gateEval (x : Fin n → Bool) (wires : List (Tree n)) (g : Gate)
    (basis : g.op = .and ∨ g.op = .or) :
    value x (unrollGate wires g) =
      g.op.eval (g.inputs.map fun i => (wires.map (value x)).getD i false) := by
  have listEq : (g.inputs.map (treeAt wires)).map (value x) =
      g.inputs.map (fun i => (wires.map (value x)).getD i false) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact mappedRead (value x) wires i (.constant false)
  rcases basis with op | op
  · simp only [unrollGate,op,valueAnds,listEq,GateOp.eval]
  · simp only [unrollGate,op,valueOrs,listEq,GateOp.eval]

theorem gateDegree (marked : Finset ℕ) (wires : List (Tree n)) (g : Gate)
    (basis : g.op = .and ∨ g.op = .or) :
    degree marked (unrollGate wires g) = g.lineDegree (wires.map (degree marked)) := by
  have listEq : (g.inputs.map (treeAt wires)).map (degree marked) =
      g.inputs.map (fun i => (wires.map (degree marked)).getD i 0) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact mappedRead (degree marked) wires i (.constant false)
  rcases basis with op | op
  · simp [unrollGate,op,degreeAnds,listEq,Gate.lineDegree]
  · simp [unrollGate,op,degreeOrs,listEq,Gate.lineDegree]

theorem liftFold {A B G : Type} (gs : List G) (init : List A) (map : A → B)
    (left : List A → G → A) (right : List B → G → B)
    (step : ∀ g ∈ gs, ∀ xs, map (left xs g) = right (xs.map map) g) :
    (gs.foldl (fun xs g => xs ++ [left xs g]) init).map map =
      gs.foldl (fun ys g => ys ++ [right ys g]) (init.map map) := by
  induction gs generalizing init with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun h member => step h (List.mem_cons_of_mem _ member))]
    simp only [List.map_append,List.map_cons,List.map_nil,step g (by simp)]

def circuitTree (n : ℕ) (C : Circuit) : Tree n :=
  treeAt (C.gates.foldl (fun xs g => xs ++ [unrollGate xs g]) (List.ofFn Tree.raw)) C.output

theorem actualValue (C : Circuit) (mono : Monotone2 C) (x : Fin n → Bool) :
    value x (circuitTree n C) = circuitFun n C x := by
  have wires := liftFold C.gates (List.ofFn (Tree.raw : Fin n → Tree n)) (value x) unrollGate
    (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    (fun g ing xs => gateEval x xs g (by simpa using (mono g ing).1))
  unfold circuitTree treeAt
  rw [mappedRead (value x)]
  unfold circuitFun Circuit.eval Circuit.wires
  rw [wires]
  simp [value,Function.comp_def]

theorem actualDegree (C : Circuit) (mono : Monotone2 C) (marked : Finset ℕ) :
    degree marked (circuitTree n C) = C.lineDeg n marked := by
  have wires := liftFold C.gates (List.ofFn (Tree.raw : Fin n → Tree n)) (degree marked) unrollGate
    (fun w g => g.lineDegree w)
    (fun g ing xs => gateDegree marked xs g (by simpa using (mono g ing).1))
  unfold circuitTree treeAt
  rw [mappedRead (degree marked)]
  unfold Circuit.lineDeg Circuit.lineDegrees
  have initial : (List.ofFn (Tree.raw : Fin n → Tree n)).map (degree marked) =
      (List.range n).map (fun i => if i ∈ marked then 1 else 0) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [degree]
  rw [wires,initial]
  rfl

theorem circuitSupport (C : Circuit) (mono : Monotone2 C) (points lines : Finset ℕ)
    (x : Fin n → Bool) (yes : circuitFun n C x = true) :
    ∃ S : Finset (Fin n), (∀ i ∈ S, x i = true) ∧
      shoreCount points S ≤ C.lineDeg n points ∧ shoreCount lines S ≤ C.lineDeg n lines ∧
      ∀ y : Fin n → Bool, (∀ i ∈ S, y i = true) → circuitFun n C y = true := by
  have ok : value x (circuitTree n C) = true := (actualValue C mono x).trans yes
  simpa only [actualValue C mono,actualDegree C mono] using
    supportOfTruth (circuitTree n C) points lines x ok

#print axioms circuitSupport

end PlaneSupport7915