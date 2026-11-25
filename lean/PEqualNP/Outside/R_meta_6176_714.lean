import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

/-- Fano incidence on 58 boundary rows and two single-read cost trials. -/
theorem PEqualNP.Outside.R_meta_6176_714
    (ordinary : ∀ (C : Circuit), IsAO2 14 C → ∀ x : List Bool,
      (fun (xs : List ℕ) => (C.gates.foldl (fun w g =>
        let ys := g.inputs.map fun i => w.getD i 2
        w ++ [GateOp.casesOn (motive := fun _ => ℕ) g.op
          (ys.foldl (fun a b => min 2 (a+b)) 0) (ys.foldl min 2) 2 (fun _ => 2) 2]) xs).getD C.output 2) (x.map fun (b : Bool) => if b then (0 : ℕ) else 2) =
        (if C.eval x then 0 else 2))
    (linear : ∀ (C : Circuit) (side : ℕ → Bool) (x : List Bool),
      (fun (xs : List ℕ) => (C.gates.foldl (fun w g =>
        let ys := g.inputs.map fun i => w.getD i 2
        w ++ [GateOp.casesOn (motive := fun _ => ℕ) g.op
          (ys.foldl (fun a b => min 2 (a+b)) 0) (ys.foldl min 2) 2 (fun _ => 2) 2]) xs).getD C.output 2) (x.zipIdx.map fun (u : Bool × ℕ) => if u.1 then (if side u.2 then (1 : ℕ) else 0) else 2) = 1 →
        ((PEqualNP.ReadK.linearParts C side x).getD C.output (false,false)).2 = true)
    (finite : ∀ (C : Circuit), C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) → (gateAt C 0).op = GateOp.and →
      let v := fun (xs : List ℕ) => (C.gates.foldl (fun w g =>
        let ys := g.inputs.map fun i => w.getD i 2
        w ++ [GateOp.casesOn (motive := fun _ => ℕ) g.op
          (ys.foldl (fun a b => min 2 (a+b)) 0) (ys.foldl min 2) 2 (fun _ => 2) 2]) xs).getD C.output 2
      let seed := fun (z o : ℕ) => (List.range 14).map fun i => if z.testBit i then 0 else if o.testBit i then 1 else 2
      (∀ k : Fin 58, v (seed (211734286467423520663767949732333950747687027482404064444210235045367168613163296630917073174147246981747312435419253653533538809284953252185926621222613580764455684141578531588650361403910737832013878772983026687188753384278356795181089439873 >>> (14*k.val)) 0) = (if k.val < 21 then 0 else 2)) →
      v (seed 1 128) = 1 ∨ v (seed 128 1) = 1) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →           have x6 : Finset (Fin (7 : ℕ)) := {(0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ))};           (∀ (x7 x8 : Fin (7 : ℕ)), x7 - x8 ∈ x6 → x1.eval (List.ofFn fun (x10 : Fin (14 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (7 : ℕ) x7 ∨ x10 = Fin.natAdd (7 : ℕ) x8)) = Bool.true) →             (∀ (x8 : Finset (Fin (7 : ℕ))),                 have x9 : Finset (Fin (7 : ℕ)) := {x9 : Fin (7 : ℕ) | ∀ x10 ∈ x8, x10 - x9 ∉ x6};                 (∀ x10 ∉ x8, ∃ x12 ∈ x9, x10 - x12 ∈ x6) → x1.eval (List.ofFn fun (x11 : Fin ((7 : ℕ) + (7 : ℕ))) => Fin.addCases (fun (x12 : Fin (7 : ℕ)) => Decidable.decide (x12 ∈ x8)) (fun (x12 : Fin (7 : ℕ)) => Decidable.decide (x12 ∈ x9)) x11) = Bool.false) →               PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ) (fun (x9 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x9)) [((0 : ℕ), (7 : ℕ))] := by
  intro C size ao distinct first offsets yes no
  let v := fun (xs : List ℕ) => (C.gates.foldl (fun w g =>
        let ys := g.inputs.map fun i => w.getD i 2
        w ++ [GateOp.casesOn (motive := fun _ => ℕ) g.op
          (ys.foldl (fun a b => min 2 (a+b)) 0) (ys.foldl min 2) 2 (fun _ => 2) 2]) xs).getD C.output 2
  let row := fun (r : ℕ) => (List.range 14).map fun i => if r.testBit i then 0 else 2
  let mark := fun (p l : ℕ) => (List.range 14).map fun i => if i = p then 0 else if i = l then 1 else 2
  let bits := fun (r : ℕ) => (List.range 14).map (fun i => r.testBit i)
  let positives : List ℕ := [129,2049,8193,130,258,4098,260,516,8196,136,520,1032,272,1040,2064,544,2080,4128,1088,4160,8256]
  let negatives : List ℕ := [16256,5889,11778,1539,7300,5125,3078,14600,4361,10250,6156,12944,4625,8722,4244,12312,4125,9632,1313,9250,1188,1063,8488,8368,8250,3008,833,2626,2244,2376,2126,720,595,480,361,244,127]
  have bitCost (r : ℕ) : row r = (bits r).map (fun b => if b then 0 else 2) := by
    simp [row,bits,List.map_map,Function.comp_def]
  have pos : ∀ k : Fin 21, ∃ p l : Fin 7, p-l ∈ offsets ∧
      bits (positives.getD k 0) = List.ofFn (fun i : Fin 14 =>
        decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)) := by decide +kernel
  let points := fun (r : ℕ) => Finset.univ.filter (fun p : Fin 7 => r.testBit p.val)
  let lines := fun (s : Finset (Fin 7)) => Finset.univ.filter
    (fun l : Fin 7 => ∀ p ∈ s, p-l ∉ offsets)
  have neg : ∀ k : Fin 37,
      let r := negatives.getD k 0
      let s := points r
      (∀ p ∉ s, ∃ l ∈ lines s, p-l ∈ offsets) ∧
      bits r = List.ofFn (fun i : Fin (7+7) =>
        Fin.addCases (fun p => decide (p ∈ s)) (fun l => decide (l ∈ lines s)) i) := by
    decide +kernel
  have pval (k : Fin 21) : v (row (positives.getD k 0)) = 0 := by
    obtain ⟨p,l,edge,eq⟩ := pos k
    rw [bitCost,show v _ = _ from ordinary C ao _,eq,yes p l edge]
    rfl
  have nval (k : Fin 37) : v (row (negatives.getD k 0)) = 2 := by
    obtain ⟨maximal,eq⟩ := neg k
    rw [bitCost,show v _ = _ from ordinary C ao _,eq,no _ maximal]
    rfl
  let input := (List.range 14).map fun i => i == 0 || i == 7
  let line := fun (i : ℕ) => decide (7 ≤ i)
  have lseed : mark 0 7 = input.zipIdx.map (fun (u : Bool × ℕ) =>
      if u.1 then (if line u.2 then 1 else 0) else 2) := by decide +kernel
  have pseed : mark 7 0 = input.zipIdx.map (fun (u : Bool × ℕ) =>
      if u.1 then (if !line u.2 then 1 else 0) else 2) := by decide +kernel
  let seed := fun (z o : ℕ) => (List.range 14).map fun i => if z.testBit i then 0 else if o.testBit i then 1 else 2
  let packed : ℕ := 211734286467423520663767949732333950747687027482404064444210235045367168613163296630917073174147246981747312435419253653533538809284953252185926621222613580764455684141578531588650361403910737832013878772983026687188753384278356795181089439873
  have table : ∀ k : Fin 58, if k.val < 21 then
      ∃ j : Fin 21, seed (packed >>> (14*k.val)) 0 = row (positives.getD j 0)
    else ∃ j : Fin 37, seed (packed >>> (14*k.val)) 0 = row (negatives.getD j 0) := by
    decide +kernel
  have trials (k : Fin 58) : v (seed (packed >>> (14*k.val)) 0) = (if k.val<21 then 0 else 2) := by
    have h := table k
    by_cases early : k.val < 21
    · simp only [early,↓reduceIte] at h ⊢
      obtain ⟨j,eq⟩ := h
      rw [eq,pval]
    · simp only [early,↓reduceIte] at h ⊢
      obtain ⟨j,eq⟩ := h
      rw [eq,nval]
  rcases finite C size ao distinct first trials with hl | hp
  · change v (seed 1 128) = 1 at hl
    rw [show seed 1 128 = mark 0 7 by decide +kernel] at hl
    rw [lseed] at hl
    have h := linear C line input hl
    change PEqualNP.ReadK.lineSingle C 14 line 0 7 = true at h
    change (bif (!(PEqualNP.ReadK.lineSingle C 14 line 0 7) && !(PEqualNP.ReadK.lineSingle C 14 (fun i => !line i) 0 7)) then [(0,7)] else []) = ([] : List (ℕ × ℕ))
    rw [h]
    rfl
  · change v (seed 128 1) = 1 at hp
    rw [show seed 128 1 = mark 7 0 by decide +kernel] at hp
    rw [pseed] at hp
    have h := linear C (fun i => !line i) input hp
    change PEqualNP.ReadK.lineSingle C 14 (fun i => !line i) 0 7 = true at h
    change (bif (!(PEqualNP.ReadK.lineSingle C 14 line 0 7) && !(PEqualNP.ReadK.lineSingle C 14 (fun i => !line i) 0 7)) then [(0,7)] else []) = ([] : List (ℕ × ℕ))
    rw [h]
    cases PEqualNP.ReadK.lineSingle C 14 line 0 7 <;> rfl
