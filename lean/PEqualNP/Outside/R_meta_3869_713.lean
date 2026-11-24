import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A shortest output OR needs the preceding gate and three distinguishable earlier wires.
theorem PEqualNP.Outside.R_meta_3869_713
    (peel : let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    let R := fun (p : List Gate) (i : ℕ) (x : Fin 9 → Bool) => ((Circuit.mk p 0).wires (List.ofFn x ++ [x 0 || x 3])).getD i false
    let good := fun p : List Gate => FanInTwo (Circuit.mk p 0) ∧ (p.countP fun g => g.op.eval [false]) ≤ 1 ∧ (∀ v ∈ ([0,3] : List ℕ), (p.countP fun g => (g.op.eval [false] && g.inputs.head? == some v || !g.op.eval [false] && g.inputs.contains v)) ≤ 2)
    ∀ gs i j, List.length gs=13 → good gs → (∀ x, (R gs i x || R gs j x) = F x) →
      ∃ (p : List Gate) (a b c : ℕ) (t : Bool), List.length p=12 ∧ good p ∧ b<c ∧ (t=false → a<b) ∧ ∀ x, (R p a x || (if t then R p b x && R p c x else R p b x || R p c x)) = F x)
    (signature : let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    let R := fun (p : List Gate) (i : ℕ) (x : Fin 9 → Bool) => ((Circuit.mk p 0).wires (List.ofFn x ++ [x 0 || x 3])).getD i false
    ∀ (p : List Gate) (a b c : ℕ) (t : Bool), p.length=12 → (FanInTwo (Circuit.mk p 0) ∧ (p.countP fun g => g.op.eval [false]) ≤ 1) → (∀ x, (R p a x || (if t then R p b x && R p c x else R p b x || R p c x)) = F x) →
      ((b<c → c<10 → 10*b+c ∈ ([1,4,5,12,16,23,27,34,38,49,57,58,68] : List ℕ)) ∧ 21 ∈ [a,b,c] ∧ 10 ≤ a ∧ (t=false → 10 ≤ b ∧ 10 ≤ c) ∧ ∀ ns ∈ (if t then [[2],[4],[6],[1,3,5]] else [[0],[1],[2],[4]] : List (List ℕ)), ∃ x, (R p a x).toNat + 2*(R p b x).toNat + 4*(R p c x).toNat ∈ ns))
    (exclude : let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    let R := fun (p : List Gate) (i : ℕ) (x : Fin 9 → Bool) => ((Circuit.mk p 0).wires (List.ofFn x ++ [x 0 || x 3])).getD i false
    ∀ (p : List Gate) (a b c : ℕ) (t : Bool), p.length=12 → (FanInTwo (Circuit.mk p 0) ∧ (p.countP fun g => g.op.eval [false]) ≤ 1 ∧ (∀ v ∈ ([0,3] : List ℕ), (p.countP fun g => (g.op.eval [false] && g.inputs.head? == some v || !g.op.eval [false] && g.inputs.contains v)) ≤ 2)) → b<c → (t=false → a<b) → ((b<c → c<10 → 10*b+c ∈ ([1,4,5,12,16,23,27,34,38,49,57,58,68] : List ℕ)) ∧ 21 ∈ [a,b,c] ∧ 10 ≤ a ∧ (t=false → 10 ≤ b ∧ 10 ≤ c) ∧ ∀ ns ∈ (if t then [[2],[4],[6],[1,3,5]] else [[0],[1],[2],[4]] : List (List ℕ)), ∃ x, (R p a x).toNat + 2*(R p b x).toNat + 4*(R p c x).toNat ∈ ns) → ∃ x, (R p a x || (if t then R p b x && R p c x else R p b x || R p c x)) ≠ F x) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         x2 ≤ (24 : ℕ) →           x3 ≤ (24 : ℕ) →             (∀ x9 ∈ [(0 : ℕ), (3 : ℕ)],                 have x11 : ℕ := List.countP (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.false] && x11.inputs.head? == Option.some x9 || !x11.op.eval [Bool.false] && x11.inputs.contains x9) (x1 ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate }]);                 (1 : ℕ) ≤ x11 ∧ x11 ≤ (2 : ℕ)) →               ∃ (x10 : Fin (9 : ℕ) → Bool),                 have x11 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]);                 (x11.getD x2 Bool.false || x11.getD x3 Bool.false) ≠ (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))) := by
  intro gs i j len legal lim _ _ readers
  by_contra! hit
  let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have h (x : Fin 9 → Bool) : (((Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 3])).getD i false || ((Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 3])).getD j false) = F x := by
    rw [not_ne_iff.mp (hit x)]
    simp only [F,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
    rfl
  have budget (v : ℕ) (hv : v ∈ ([0,3] : List ℕ)) :
      (gs.countP fun g => (g.op.eval [false] && g.inputs.head? == some v || !g.op.eval [false] && g.inputs.contains v)) ≤ 2 := by
    have hh := (readers v hv).2
    simp only [List.countP_append] at hh
    omega
  obtain ⟨p,a,b,c,t,sz,ok,lt,sorted,eq⟩ := peel gs i j len ⟨legal,lim,budget⟩ h
  obtain ⟨x,bad⟩ := exclude p a b c t sz ok lt sorted (signature p a b c t sz ⟨ok.1,ok.2.1⟩ eq)
  exact bad (eq x)
