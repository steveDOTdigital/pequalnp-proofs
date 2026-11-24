import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open scoped BigOperators

namespace PEqualNP.Outside.L_meta_1843_aux

def Well (N : ℕ) (C : Circuit) :=
  (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧ ReadsBack (N+N) C

def Cross (N : ℕ) (C : Circuit) (j : ℕ) :=
  (gateAt C j).op = GateOp.and ∧ ¬ ((∃ i ∈ (gateAt C j).inputs,
    (C.lineDegrees (N+N) (Finset.Ico N (N+N))).getD i 0 = 0) ∨
    (∀ i ∈ (gateAt C j).inputs, (C.lineDegrees (N+N) (Finset.range N)).getD i 0 = 0))

noncomputable def count (N : ℕ) (C : Circuit) :=
  Set.ncard {j : ℕ | j < C.gates.length ∧ Cross N C j}

noncomputable def view (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) : Circuit := by
  classical
  exact ⟨List.ofFn (fun j : Fin C.gates.length => if Cross N C j then
    ⟨.or, [(gateAt C j).inputs.getD (sg j).val 0, (gateAt C j).inputs.getD (sg j).val 0]⟩
    else gateAt C j), C.output⟩

theorem view_zero (N : ℕ) (C : Circuit) (hz : count N C ≤ 0) (sg : ℕ → Fin 2) :
    view N C sg = C := by
  classical
  let T := {j : ℕ | j < C.gates.length ∧ Cross N C j}
  have hf : T.Finite := (Set.finite_lt_nat C.gates.length).subset (fun _ h => h.1)
  have he : T = ∅ := (Set.ncard_eq_zero hf).1 (Nat.eq_zero_of_le_zero hz)
  have hn (j : Fin C.gates.length) : ¬ Cross N C j := by
    intro h
    have hm : j.val ∈ T := ⟨j.isLt,h⟩
    rw [he] at hm
    exact hm
  have hg (j : Fin C.gates.length) : gateAt C j = C.gates[j.val] :=
    List.getD_eq_getElem _ _ j.isLt
  simp [view, hn, hg]

def bits {N : ℕ} (X Y : Finset (Fin N)) : Fin (N+N) → Bool :=
  Fin.append (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))

def run {N : ℕ} (C : Circuit) (X Y : Finset (Fin N)) := circuitFun (N+N) C (bits X Y)

def removed {N : ℕ} (S W : Finset (Fin N)) :=
  Finset.image (fun p : Fin N => p.val) Sᶜ ∪ Finset.image (fun l : Fin N => N+l.val) Wᶜ

def State {N : ℕ} (K : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (S W : Finset (Fin N)) :=
  (0 < C.gates.length ∧
    (∀ j < C.gates.length, ∀ i ∈ (gateAt C j).inputs,
      (C.lineDegrees (N+N) (removed S W)).getD i 0 = 0) ∧
    (C.lineDegrees (N+N) (removed S W)).getD C.output 0 = 0) ∧
  (∀ p ∈ S, ∀ l ∈ W, I p l → run C {p} {l} = true) ∧
  (∀ X Y, X ⊆ S → Y ⊆ W → Y.card ≤ K → (∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) → run C X Y = false)

def Clean {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit) (S W : Finset (Fin N)) (R : ℕ) :=
  ∀ sg : ℕ → Fin 2, ∀ w ∈ W, ∀ X : Finset (Fin N), X ⊆ S →
    (∀ p ∈ X, ¬ I p w) → X.card ≤ R → run (view N C sg) X {w} = false

theorem clean_zero {N K R : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit}
    {S W : Finset (Fin N)} (hs : State K I C S W) (hk : 1 ≤ K) (hz : count N C ≤ 0) :
    Clean I C S W R := by
  intro sg w hw X hX hI _
  rw [view_zero N C hz sg]
  apply hs.2.2 X {w} hX (Finset.singleton_subset_iff.mpr hw) (by simpa using hk)
  simpa using hI

theorem zero_degrees (C : Circuit) (n i : ℕ) : (C.lineDegrees n ∅).getD i 0 = 0 := by
  have fold (gs : List Gate) (w : List ℕ) (h : ∀ v ∈ w, v = 0) :
      ∀ v ∈ gs.foldl (fun d g => d ++ [g.lineDegree d]) w, v = 0 := by
    induction gs generalizing w with
    | nil => exact h
    | cons g gs ih =>
      apply ih
      have hd (j : ℕ) : w.getD j 0 = 0 := by
        by_cases hj : j < w.length
        · rw [List.getD_eq_getElem _ _ hj]
          exact h _ (List.getElem_mem _)
        · exact List.getD_eq_default _ _ (by omega)
      have hg : g.lineDegree w = 0 := by
        have hh (xs : List ℕ) :
            (xs.map fun j => w.getD j 0).sum = 0 ∧
            (xs.map fun j => w.getD j 0).foldr max 0 = 0 := by
          induction xs with
          | nil => simp
          | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.foldr_cons, hd x, ih.1, ih.2, add_zero, max_self, and_self]
        unfold Gate.lineDegree
        split <;> first | exact (hh _).1 | exact (hh _).2
      intro v hv
      rcases List.mem_append.mp hv with h1 | h1
      · exact h _ h1
      · simpa [hg] using h1
  have ha : ∀ v ∈ C.lineDegrees n ∅, v = 0 := fold _ _ (by simp)
  by_cases hi : i < (C.lineDegrees n ∅).length
  · rw [List.getD_eq_getElem _ _ hi]
    exact ha _ (List.getElem_mem _)
  · exact List.getD_eq_default _ _ (by omega)

theorem bits_left {N : ℕ} (X Y : Finset (Fin N)) (p : Fin N) :
    bits X Y (Fin.castAdd N p) = decide (p ∈ X) := Fin.append_left _ _ _

theorem bits_right {N : ℕ} (X Y : Finset (Fin N)) (l : Fin N) :
    bits X Y (Fin.natAdd N l) = decide (l ∈ Y) := Fin.append_right _ _ _

theorem initial {N k : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] (C : Circuit)
    (hk : 1 ≤ k) (edge : ∃ p l, I p l)
    (hp : ∀ p l, I p l → circuitFun (N+N) C
      (fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)) = true)
    (hn : ∀ z : Fin (N+N) → Bool,
      (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ k →
      (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N+N) C z = false) : State k I C Finset.univ Finset.univ := by
  classical
  have pos (p l : Fin N) (h : I p l) : run C {p} {l} = true := by
    unfold run
    rw [← hp p l h]
    congr 1
    funext j
    refine Fin.addCases (fun x => ?_) (fun y => ?_) j
    · rw [bits_left]
      congr 1
      simp [Fin.ext_iff]
      omega
    · rw [bits_right]
      congr 1
      simp [Fin.ext_iff]
      omega
  have neg (X Y : Finset (Fin N)) (hy : Y.card ≤ k) (hI : ∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) :
      run C X Y = false := by
    apply hn
    · simpa only [bits_right, decide_eq_true_eq, Finset.filter_mem_eq_inter, Finset.univ_inter] using hy
    · rintro ⟨p,l,hpl,hx,hy'⟩
      rw [bits_left, decide_eq_true_eq] at hx
      rw [bits_right, decide_eq_true_eq] at hy'
      exact hI p hx l hy' hpl
  have gates : 0 < C.gates.length := by
    by_contra! hz
    have hh : C.gates = [] := List.length_eq_zero_iff.mp (by omega)
    have raw (X Y : Finset (Fin N)) : run C X Y =
        (List.ofFn (bits X Y)).getD C.output false := by
      simp [run, circuitFun, Circuit.eval, Circuit.wires, hh]
    obtain ⟨p,l,hi⟩ := edge
    have hout : C.output < N+N := by
      by_contra! h
      have hp' := pos p l hi
      rw [raw, List.getD_eq_default _ _ (by simpa using h)] at hp'
      contradiction
    let out : Fin (N+N) := ⟨C.output,hout⟩
    have evalOut (X Y : Finset (Fin N)) : run C X Y = bits X Y out := by
      rw [raw, List.getD_eq_getElem _ _ (by simpa using hout)]
      simp [out]
    have any (j : Fin (N+N)) : ∃ X Y : Finset (Fin N), Y.card ≤ k ∧
        (∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) ∧ bits X Y j = true := by
      refine Fin.addCases (fun p => ?_) (fun l => ?_) j
      · exact ⟨{p},∅,by simp,by simp,by rw [bits_left]; simp⟩
      · exact ⟨∅,{l},by simpa using hk,by simp,by rw [bits_right]; simp⟩
    obtain ⟨X,Y,hy,hI,hout'⟩ := any out
    have no := neg X Y hy hI
    rw [evalOut, hout'] at no
    contradiction
  refine ⟨⟨gates, ?_, ?_⟩, (fun p _ l _ h => pos p l h), (fun X Y _ _ => neg X Y)⟩
  · intro j _ i _
    simpa [removed] using zero_degrees C (N+N) i
  · simpa [removed] using zero_degrees C (N+N) C.output

def gain (q r t : ℕ) := max (r * max (2*t) (q+1)) (3*q*t)

def lost (q : ℕ) (R : ℕ → ℕ) (d : ℕ) := ∑ i ∈ Finset.range d, (1+R i*(q+1))

theorem count_finish {N q r t d L a c size : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (S W : Finset (Fin N)) (_hr : 0 < r) (ht : 0 < t) (hq : d < q)
    (hw : N-L ≤ W.card) (hd : ∀ l ∈ W, q+1-d ≤ (S.filter (fun p => I p l)).card)
    (budget : a * gain q r t ≤ c * (r*t*(N-L)*(q-d)))
    (bound : r*t*((S ×ˢ W).filter (fun pl => I pl.1 pl.2)).card ≤
      r*t*W.card + gain q r t * size) : a ≤ c*size := by
  have hdeg : W.card * (q-d+1) ≤ ((S ×ˢ W).filter (fun pl => I pl.1 pl.2)).card := by
    calc
      _ = ∑ _ ∈ W, (q-d+1) := by simp
      _ ≤ ∑ l ∈ W, (S.filter (fun p => I p l)).card :=
        Finset.sum_le_sum (fun l hl => le_trans (by omega) (hd l hl))
      _ = _ := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right]
  have hb : r*t*(N-L)*(q-d) ≤ gain q r t * size := by
    have h1 := Nat.mul_le_mul_left (r*t) hdeg
    have h2 := Nat.mul_le_mul_left (r*t*(q-d)) hw
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_add] at h1
    nlinarith only [h1, h2, bound]
  have hq' : 0 < q := by omega
  have hg : 0 < gain q r t := lt_of_lt_of_le (by positivity : 0 < 3*q*t) (le_max_right _ _)
  refine Nat.le_of_mul_le_mul_right ?_ hg
  calc
    _ ≤ c*(r*t*(N-L)*(q-d)) := budget
    _ ≤ c*(gain q r t*size) := Nat.mul_le_mul_left c hb
    _ = _ := by ring

theorem budget_nat {N q d r t a c : ℕ} {R : ℕ → ℕ} {u : ℤ}
    (ht : (t : ℤ) = u) (hl : lost q R d ≤ N) (hd : d ≤ q)
    (hb : (a : ℤ) * max ((r : ℤ) * max (2*u) ((q : ℤ)+1)) (3*(q : ℤ)*u) ≤
      (c : ℤ)*((r : ℤ)*u*((N : ℤ)-∑ i ∈ Finset.range d, (1+(R i : ℤ)*((q : ℤ)+1)))*
        ((q : ℤ)-(d : ℤ)))) :
    a * gain q r t ≤ c * (r*t*(N-lost q R d)*(q-d)) := by
  apply (Nat.cast_le (α := ℤ)).mp
  simp only [gain, Nat.cast_mul, Nat.cast_max, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    Nat.cast_sub hl, Nat.cast_sub hd, ht]
  simpa only [lost, Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hb

end PEqualNP.Outside.L_meta_1843_aux

open PEqualNP.Outside.L_meta_1843_aux
theorem PEqualNP.Outside.L_meta_1843 : (∀ (Nlv15b Klv15b mlv15b : ℕ) (Ilv15b : Fin Nlv15b → Fin Nlv15b → Prop) [DecidableRel Ilv15b] (Clv15b : PEqualNP.CircuitLowerBounds.Circuit) (Slv15b Wlv15b Xlv15b : Finset (Fin Nlv15b)) (wlv15b : Fin Nlv15b) (sglv15b : ℕ → Fin 2) (Splv15b Wplv15b : Finset (Fin Nlv15b)), ((∀ glv15b ∈ Clv15b.gates, (glv15b.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15b.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15b.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15b + Nlv15b) Clv15b) → Set.ncard {jlv15b : ℕ | jlv15b < Clv15b.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15b).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.Ico Nlv15b (Nlv15b + Nlv15b))).getD ilv15b 0 = 0) ∨ (∀ hlv15b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15b).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.range Nlv15b)).getD hlv15b 0 = 0))} ≤ mlv15b + 1 → ((0 < Clv15b.gates.length ∧ (∀ jlv15bx1 < Clv15b.gates.length, ∀ ilv15bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx1).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx5 : Fin Nlv15b => (plv15bx5 : ℕ)) (Slv15b)ᶜ ∪ Finset.image (fun llv15bx4 : Fin Nlv15b => Nlv15b + (llv15bx4 : ℕ)) (Wlv15b)ᶜ)).getD ilv15bx1 0 = 0) ∧ (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx6 : Fin Nlv15b => (plv15bx6 : ℕ)) (Slv15b)ᶜ ∪ Finset.image (fun llv15bx5 : Fin Nlv15b => Nlv15b + (llv15bx5 : ℕ)) (Wlv15b)ᶜ)).getD Clv15b.output 0 = 0) ∧ (∀ plv15bx3 ∈ Slv15b, ∀ llv15bx2 ∈ Wlv15b, Ilv15b plv15bx3 llv15bx2 → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Clv15b (Fin.append (fun plv15bx7 : Fin Nlv15b => decide (plv15bx7 ∈ ({plv15bx3} : Finset (Fin Nlv15b)))) (fun llv15bx6 : Fin Nlv15b => decide (llv15bx6 ∈ ({llv15bx2} : Finset (Fin Nlv15b))))) = true) ∧ (∀ Xlv15bx1 Ylv15b : Finset (Fin Nlv15b), Xlv15bx1 ⊆ Slv15b → Ylv15b ⊆ Wlv15b → Ylv15b.card ≤ Klv15b + 1 → (∀ plv15bx4 ∈ Xlv15bx1, ∀ llv15bx3 ∈ Ylv15b, ¬ Ilv15b plv15bx4 llv15bx3) → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Clv15b (Fin.append (fun plv15bx8 : Fin Nlv15b => decide (plv15bx8 ∈ Xlv15bx1)) (fun llv15bx7 : Fin Nlv15b => decide (llv15bx7 ∈ Ylv15b))) = false)) → wlv15b ∈ Wlv15b → Xlv15b ⊆ Slv15b → (∀ plv15bx1 ∈ Xlv15b, ¬ Ilv15b plv15bx1 wlv15b) → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv15bx2 : Fin Clv15b.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.Ico Nlv15b (Nlv15b + Nlv15b))).getD ilv15bx2 0 = 0) ∨ (∀ hlv15bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.range Nlv15b)).getD hlv15bx1 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs.getD (sglv15b jlv15bx2.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs.getD (sglv15b jlv15bx2.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val))) Clv15b.output) (Fin.append (fun plv15bx9 : Fin Nlv15b => decide (plv15bx9 ∈ Xlv15b)) (fun llv15bx8 : Fin Nlv15b => decide (llv15bx8 ∈ ({wlv15b} : Finset (Fin Nlv15b))))) = true → Splv15b = Slv15b.filter (fun ulv15b : Fin Nlv15b => ¬ Ilv15b ulv15b wlv15b ∧ ulv15b ∉ Xlv15b) → Wplv15b = Wlv15b.filter (fun llv15bx1 : Fin Nlv15b => llv15bx1 ≠ wlv15b ∧ ∀ plv15bx2 ∈ Xlv15b, ¬ Ilv15b plv15bx2 llv15bx1) → (∃ plv15b ∈ Splv15b, ∃ llv15b ∈ Wplv15b, Ilv15b plv15b llv15b) → ∃ Dlv15b : PEqualNP.CircuitLowerBounds.Circuit, ((∀ glv15bx1 ∈ Dlv15b.gates, (glv15bx1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15bx1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15bx1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15b + Nlv15b) Dlv15b) ∧ Set.ncard {jlv15bx3 : ℕ | jlv15bx3 < Dlv15b.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15bx3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx3).inputs, (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.Ico Nlv15b (Nlv15b + Nlv15b))).getD ilv15bx3 0 = 0) ∨ (∀ hlv15bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx3).inputs, (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.range Nlv15b)).getD hlv15bx2 0 = 0))} ≤ mlv15b ∧ Dlv15b.size ≤ Clv15b.size ∧ ((0 < Dlv15b.gates.length ∧ (∀ jlv15bx4 < Dlv15b.gates.length, ∀ ilv15bx4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx4).inputs, (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx12 : Fin Nlv15b => (plv15bx12 : ℕ)) (Splv15b)ᶜ ∪ Finset.image (fun llv15bx11 : Fin Nlv15b => Nlv15b + (llv15bx11 : ℕ)) (Wplv15b)ᶜ)).getD ilv15bx4 0 = 0) ∧ (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx13 : Fin Nlv15b => (plv15bx13 : ℕ)) (Splv15b)ᶜ ∪ Finset.image (fun llv15bx12 : Fin Nlv15b => Nlv15b + (llv15bx12 : ℕ)) (Wplv15b)ᶜ)).getD Dlv15b.output 0 = 0) ∧ (∀ plv15bx10 ∈ Splv15b, ∀ llv15bx9 ∈ Wplv15b, Ilv15b plv15bx10 llv15bx9 → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Dlv15b (Fin.append (fun plv15bx14 : Fin Nlv15b => decide (plv15bx14 ∈ ({plv15bx10} : Finset (Fin Nlv15b)))) (fun llv15bx13 : Fin Nlv15b => decide (llv15bx13 ∈ ({llv15bx9} : Finset (Fin Nlv15b))))) = true) ∧ (∀ Xlv15bx2 Ylv15bx1 : Finset (Fin Nlv15b), Xlv15bx2 ⊆ Splv15b → Ylv15bx1 ⊆ Wplv15b → Ylv15bx1.card ≤ Klv15b → (∀ plv15bx11 ∈ Xlv15bx2, ∀ llv15bx10 ∈ Ylv15bx1, ¬ Ilv15b plv15bx11 llv15bx10) → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Dlv15b (Fin.append (fun plv15bx15 : Fin Nlv15b => decide (plv15bx15 ∈ Xlv15bx2)) (fun llv15bx14 : Fin Nlv15b => decide (llv15bx14 ∈ Ylv15bx1))) = false))) → (∀ (Nlv16 : ℕ) (Clv16 : PEqualNP.CircuitLowerBounds.Circuit) (Vlv16 : (ℕ → Fin 2) → PEqualNP.CircuitLowerBounds.Circuit), ((∀ glv16x2 ∈ Clv16.gates, (glv16x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv16x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv16x2.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv16 + Nlv16) Clv16) → Vlv16 = (fun sglv16x3 : ℕ → Fin 2 => (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv16x2 : Fin Clv16.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv16x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs, (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD ilv16x1 0 = 0) ∨ (∀ hlv16x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs, (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD hlv16x3 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs.getD (sglv16x3 jlv16x2.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs.getD (sglv16x3 jlv16x2.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val))) Clv16.output)) → (∀ zlv16 : Fin (Nlv16 + Nlv16) → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv16 + Nlv16) Clv16 zlv16 = true ↔ ∀ sglv16 : ℕ → Fin 2, PEqualNP.MetaComplexity.circuitFun (Nlv16 + Nlv16) (Vlv16 sglv16) zlv16 = true) ∧ (∀ sglv16x1 : ℕ → Fin 2, ((∀ glv16x1 ∈ (Vlv16 sglv16x1).gates, (glv16x1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv16x1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv16x1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv16 + Nlv16) (Vlv16 sglv16x1)) ∧ (∀ jlv16 < (Vlv16 sglv16x1).gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x1) jlv16).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((∃ ilv16 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x1) jlv16).inputs, ((Vlv16 sglv16x1).lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD ilv16 0 = 0) ∨ (∀ hlv16x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x1) jlv16).inputs, ((Vlv16 sglv16x1).lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD hlv16x2 0 = 0))) ∧ (Vlv16 sglv16x1).size = Clv16.size ∧ ∀ (zlv16x1 : Fin (Nlv16 + Nlv16) → Bool) (wlv16 : ℕ), (Clv16.wires (List.ofFn zlv16x1)).getD wlv16 false = true → ((Vlv16 sglv16x1).wires (List.ofFn zlv16x1)).getD wlv16 false = true) ∧ (∀ (sglv16x2 : ℕ → Fin 2) (glv16 : ℕ), ((Vlv16 sglv16x2).lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD glv16 0 = 0 → 0 < ((Vlv16 sglv16x2).lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD glv16 0 → ∃ Elv16 : Finset ℕ, (∀ hlv16 ∈ Elv16, (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD hlv16 0 = 0 ∧ (Relation.ReflTransGen (fun alv16 blv16 : ℕ => ∃ jlv16x1 < (Vlv16 sglv16x2).gates.length, blv16 = Nlv16 + Nlv16 + jlv16x1 ∧ alv16 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x2) jlv16x1).inputs ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x2) jlv16x1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 0 < (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD blv16 0 ∧ 0 < (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD blv16 0) hlv16 glv16)) ∧ ∀ ylv16 : Fin Nlv16 → Bool, ((Vlv16 sglv16x2).wires (List.ofFn (Fin.append (fun _ulv16 : Fin Nlv16 => false) ylv16))).getD glv16 false = decide (∃ hlv16x1 ∈ Elv16, (Clv16.wires (List.ofFn (Fin.append (fun _ulv16x1 : Fin Nlv16 => false) ylv16))).getD hlv16x1 false = true))) → (∀ (qlv17 Nlv17 Klv17 mlv17 Rlv17 Dlv17 : ℕ) (Ilv17 : Fin Nlv17 → Fin Nlv17 → Prop) [DecidableRel Ilv17] (Clv17 : PEqualNP.CircuitLowerBounds.Circuit) (Slv17 Wlv17 : Finset (Fin Nlv17)), 2 ≤ qlv17 → Nlv17 = qlv17 ^ 2 + qlv17 + 1 → (∀ llv17 : Fin Nlv17, (Finset.univ.filter (fun plv17 => Ilv17 plv17 llv17)).card = qlv17 + 1) → (∀ palv17 pblv17 : Fin Nlv17, palv17 ≠ pblv17 → ∃! lblv17 : Fin Nlv17, Ilv17 palv17 lblv17 ∧ Ilv17 pblv17 lblv17) → ((∀ glv17 ∈ Clv17.gates, (glv17.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv17 + Nlv17) Clv17) → Set.ncard {jlv17 : ℕ | jlv17 < Clv17.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.Ico Nlv17 (Nlv17 + Nlv17))).getD ilv17 0 = 0) ∨ (∀ hlv17 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.range Nlv17)).getD hlv17 0 = 0))} ≤ mlv17 → ((0 < Clv17.gates.length ∧ (∀ jlv17x1 < Clv17.gates.length, ∀ ilv17x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x1).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.image (fun plv17x3 : Fin Nlv17 => (plv17x3 : ℕ)) (Slv17)ᶜ ∪ Finset.image (fun llv17x3 : Fin Nlv17 => Nlv17 + (llv17x3 : ℕ)) (Wlv17)ᶜ)).getD ilv17x1 0 = 0) ∧ (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.image (fun plv17x4 : Fin Nlv17 => (plv17x4 : ℕ)) (Slv17)ᶜ ∪ Finset.image (fun llv17x4 : Fin Nlv17 => Nlv17 + (llv17x4 : ℕ)) (Wlv17)ᶜ)).getD Clv17.output 0 = 0) ∧ (∀ plv17x1 ∈ Slv17, ∀ llv17x1 ∈ Wlv17, Ilv17 plv17x1 llv17x1 → PEqualNP.MetaComplexity.circuitFun (Nlv17 + Nlv17) Clv17 (Fin.append (fun plv17x5 : Fin Nlv17 => decide (plv17x5 ∈ ({plv17x1} : Finset (Fin Nlv17)))) (fun llv17x5 : Fin Nlv17 => decide (llv17x5 ∈ ({llv17x1} : Finset (Fin Nlv17))))) = true) ∧ (∀ Xlv17 Ylv17 : Finset (Fin Nlv17), Xlv17 ⊆ Slv17 → Ylv17 ⊆ Wlv17 → Ylv17.card ≤ Klv17 → (∀ plv17x2 ∈ Xlv17, ∀ llv17x2 ∈ Ylv17, ¬ Ilv17 plv17x2 llv17x2) → PEqualNP.MetaComplexity.circuitFun (Nlv17 + Nlv17) Clv17 (Fin.append (fun plv17x6 : Fin Nlv17 => decide (plv17x6 ∈ Xlv17)) (fun llv17x6 : Fin Nlv17 => decide (llv17x6 ∈ Ylv17))) = false)) → 2 ^ mlv17 + Dlv17 = Klv17 + 1 → 1 ≤ Dlv17 → 1 ≤ Rlv17 → Rlv17 ≤ qlv17 → (∀ sglv17 : ℕ → Fin 2, ∀ wlv17 ∈ Wlv17, ∀ Xlv17x1 : Finset (Fin Nlv17), Xlv17x1 ⊆ Slv17 → (∀ plv17x7 ∈ Xlv17x1, ¬ Ilv17 plv17x7 wlv17) → Xlv17x1.card ≤ Rlv17 → PEqualNP.MetaComplexity.circuitFun (Nlv17 + Nlv17) (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv17x2 : Fin Clv17.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.Ico Nlv17 (Nlv17 + Nlv17))).getD ilv17x2 0 = 0) ∨ (∀ hlv17x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.range Nlv17)).getD hlv17x1 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs.getD (sglv17 jlv17x2.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs.getD (sglv17 jlv17x2.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val))) Clv17.output) (Fin.append (fun plv17x8 : Fin Nlv17 => decide (plv17x8 ∈ Xlv17x1)) (fun llv17x7 : Fin Nlv17 => decide (llv17x7 ∈ ({wlv17} : Finset (Fin Nlv17))))) = false) → Rlv17 * Dlv17 * ((Slv17 ×ˢ Wlv17).filter (fun pllv17 => Ilv17 pllv17.1 pllv17.2)).card ≤ Rlv17 * Dlv17 * Wlv17.card + max (Rlv17 * max (2 * Dlv17) (qlv17 + 1)) (3 * qlv17 * Dlv17) * Clv17.size) → (∀ (q131 N131 r131 : ℕ) (I131 : Fin N131 → Fin N131 → Prop) [DecidableRel I131] (S131 W131 : Finset (Fin N131)), 2 ≤ q131 → N131 = q131 ^ 2 + q131 + 1 → (∀ l131f : Fin N131, (Finset.univ.filter (fun p131b => I131 p131b l131f)).card = q131 + 1) → (∀ pa131 pb131 : Fin N131, pa131 ≠ pb131 → ∃! lb131 : Fin N131, I131 pa131 lb131 ∧ I131 pb131 lb131) → (∀ (pz131 : Fin N131) (T131 : Finset (Fin N131)), T131.card ≤ r131 → (W131 \ W131.filter (fun l131 => ¬ I131 pz131 l131 ∧ l131 ∉ T131)).card ≤ q131 + 1 + r131 ∧ ∀ l131b ∈ W131.filter (fun l131a => ¬ I131 pz131 l131a ∧ l131a ∉ T131), (S131.filter (fun u131 => I131 u131 l131b)).card ≤ ((S131.filter (fun u131a => u131a ≠ pz131 ∧ ∀ m131 ∈ T131, ¬ I131 u131a m131)).filter (fun u131b => I131 u131b l131b)).card + r131) ∧ (∀ (wz131 : Fin N131) (Q131 : Finset (Fin N131)), Q131.card ≤ r131 → (W131 \ W131.filter (fun l131c => l131c ≠ wz131 ∧ ∀ p131 ∈ Q131, ¬ I131 p131 l131c)).card ≤ 1 + r131 * (q131 + 1) ∧ ∀ l131e ∈ W131.filter (fun l131d => l131d ≠ wz131 ∧ ∀ p131a ∈ Q131, ¬ I131 p131a l131d), (S131.filter (fun u131c => I131 u131c l131e)).card ≤ ((S131.filter (fun u131d => ¬ I131 u131d wz131 ∧ u131d ∉ Q131)).filter (fun u131e => I131 u131e l131e)).card + 1)) → ∀ (qlv18 Nlv18 klv18 mlv18 alv18 clv18 : ℕ) (Ilv18 : Fin Nlv18 → Fin Nlv18 → Prop) [DecidableRel Ilv18] (Clv18 : PEqualNP.CircuitLowerBounds.Circuit) (Rlv18 : ℕ → ℕ), 2 ≤ qlv18 → Nlv18 = qlv18 ^ 2 + qlv18 + 1 → (∀ llv18 : Fin Nlv18, (Finset.univ.filter (fun plv18 => Ilv18 plv18 llv18)).card = qlv18 + 1) → (∀ palv18 pblv18 : Fin Nlv18, palv18 ≠ pblv18 → ∃! lblv18 : Fin Nlv18, Ilv18 palv18 lblv18 ∧ Ilv18 pblv18 lblv18) → 1 ≤ klv18 → klv18 ≤ qlv18 → ((∀ glv18 ∈ Clv18.gates, (glv18.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv18.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv18.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv18 + Nlv18) Clv18) → Set.ncard {jlv18 : ℕ | jlv18 < Clv18.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18 jlv18).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv18x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18 jlv18).inputs, (Clv18.lineDegrees (Nlv18 + Nlv18) (Finset.Ico Nlv18 (Nlv18 + Nlv18))).getD ilv18x3 0 = 0) ∨ (∀ hlv18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18 jlv18).inputs, (Clv18.lineDegrees (Nlv18 + Nlv18) (Finset.range Nlv18)).getD hlv18 0 = 0))} ≤ mlv18 → (∀ plv18x1 llv18x1 : Fin Nlv18, Ilv18 plv18x1 llv18x1 → PEqualNP.MetaComplexity.circuitFun (Nlv18 + Nlv18) Clv18 (fun klv18x1 => decide (klv18x1 = Fin.castAdd Nlv18 plv18x1 ∨ klv18x1 = Fin.natAdd Nlv18 llv18x1)) = true) → (∀ zlv18 : Fin (Nlv18 + Nlv18) → Bool, (Finset.univ.filter (fun llv18x2 : Fin Nlv18 => zlv18 (Fin.natAdd Nlv18 llv18x2) = true)).card ≤ klv18 → (¬ ∃ plv18x2 llv18x3 : Fin Nlv18, Ilv18 plv18x2 llv18x3 ∧ zlv18 (Fin.castAdd Nlv18 plv18x2) = true ∧ zlv18 (Fin.natAdd Nlv18 llv18x3) = true) → PEqualNP.MetaComplexity.circuitFun (Nlv18 + Nlv18) Clv18 zlv18 = false) → (∀ dlv18 < mlv18, 1 ≤ Rlv18 dlv18 ∧ Rlv18 dlv18 ≤ qlv18) → (∀ dlv18x1 elv18x1 : ℕ, dlv18x1 + elv18x1 = mlv18 → 2 ^ elv18x1 + dlv18x1 ≤ klv18 ∧ ∑ ilv18 ∈ Finset.range dlv18x1, (1 + Rlv18 ilv18 * (qlv18 + 1)) < Nlv18) → (∀ dlv18x2 elv18x2 : ℕ, dlv18x2 + elv18x2 + 1 = mlv18 → (alv18 : ℤ) * max ((Rlv18 dlv18x2 : ℤ) * max (2 * ((klv18 : ℤ) + 1 - (dlv18x2 : ℤ) - 2 ^ (elv18x2 + 1))) ((qlv18 : ℤ) + 1)) (3 * (qlv18 : ℤ) * ((klv18 : ℤ) + 1 - (dlv18x2 : ℤ) - 2 ^ (elv18x2 + 1))) ≤ (clv18 : ℤ) * ((Rlv18 dlv18x2 : ℤ) * ((klv18 : ℤ) + 1 - (dlv18x2 : ℤ) - 2 ^ (elv18x2 + 1)) * ((Nlv18 : ℤ) - ∑ ilv18x1 ∈ Finset.range dlv18x2, (1 + (Rlv18 ilv18x1 : ℤ) * ((qlv18 : ℤ) + 1))) * ((qlv18 : ℤ) - (dlv18x2 : ℤ)))) → (alv18 : ℤ) * max ((qlv18 : ℤ) * max (2 * ((klv18 : ℤ) - (mlv18 : ℤ))) ((qlv18 : ℤ) + 1)) (3 * (qlv18 : ℤ) * ((klv18 : ℤ) - (mlv18 : ℤ))) ≤ (clv18 : ℤ) * ((qlv18 : ℤ) * ((klv18 : ℤ) - (mlv18 : ℤ)) * ((Nlv18 : ℤ) - ∑ ilv18x2 ∈ Finset.range mlv18, (1 + (Rlv18 ilv18x2 : ℤ) * ((qlv18 : ℤ) + 1))) * ((qlv18 : ℤ) - (mlv18 : ℤ))) → alv18 ≤ clv18 * Clv18.size := by
  intro spill _views cnf residual q N k m a c I inst C R hq hN hline hpair hk hkq hwell hcross hp hn
    hR hstage hmid hend
  classical
  have startEdge : ∃ p l, I p l := by
    let l : Fin N := ⟨0,by omega⟩
    have hl := hline l
    obtain ⟨p,hm⟩ := Finset.card_pos.mp (show 0 < _ by omega : 0 < (Finset.univ.filter (fun p => I p l)).card)
    exact ⟨p,l,(Finset.mem_filter.mp hm).2⟩
  have start := initial C hk startEdge hp hn
  have stage : ∀ e d : ℕ, d+e=m → ∀ (B : Circuit) (S W : Finset (Fin N)),
      Well N B → count N B ≤ e → B.size ≤ C.size → State (k-d) I B S W →
      N-lost q R d ≤ W.card → (∀ l ∈ W, q+1-d ≤ (S.filter (fun p => I p l)).card) →
      a ≤ c*C.size := by
    intro e
    induction e with
    | zero =>
      intro d hdm B S W hwellB hzero hsize hs hw hd
      have hdm' : d = m := by omega
      subst d
      obtain ⟨hk0,hl0⟩ := hstage m 0 (by omega)
      change lost q R m < N at hl0
      simp only [pow_zero] at hk0
      have clean := clean_zero (R := q) hs (by omega) hzero
      have hb := cnf q N (k-m) 0 q (k-m) I B S W hq hN hline hpair hwellB hzero hs
        (by simp [Nat.add_comm]) (by omega) (by omega) (by omega) clean
      have budget := budget_nat (t := k-m) (Nat.cast_sub (by omega : m ≤ k)) hl0.le
        (by omega : m ≤ q) hend
      exact (count_finish I S W (by omega) (by omega) (by omega) hw hd budget hb).trans
        (Nat.mul_le_mul_left c hsize)
    | succ e ih =>
      intro d hdm B S W hwellB hcrossB hsize hs hw hd
      obtain ⟨hk0,hl0⟩ := hstage d (e+1) hdm
      change lost q R d < N at hl0
      have hpow : 0 < 2^(e+1) := by positivity
      obtain ⟨hr,hrq⟩ := hR d (by omega)
      let t := k+1-d-2^(e+1)
      have ht : 1 ≤ t := by dsimp [t]; omega
      by_cases clean : Clean I B S W (R d)
      · have hb := cnf q N (k-d) (e+1) (R d) t I B S W hq hN hline hpair hwellB
          hcrossB hs (by dsimp [t]; omega) ht hr hrq clean
        have hz : (t : ℤ) = (k : ℤ)+1-d-2^(e+1) := by
          dsimp [t]
          rw [Nat.cast_sub (by omega : 2^(e+1) ≤ k+1-d), Nat.cast_sub (by omega : d ≤ k+1)]
          push_cast
          rfl
        have budget := budget_nat hz hl0.le (by omega : d ≤ q) (hmid d e (by omega))
        exact (count_finish I S W hr ht (by omega) hw hd budget hb).trans (Nat.mul_le_mul_left c hsize)
      · unfold Clean at clean
        push Not at clean
        obtain ⟨sg,w,hw0,X,hX,havoid,hcard,hyes⟩ := clean
        let T := S.filter (fun u => ¬ I u w ∧ u ∉ X)
        let Z := W.filter (fun l => l ≠ w ∧ ∀ p ∈ X, ¬ I p l)
        obtain ⟨hlost,hdegs⟩ := (residual q N (R d) I S W hq hN hline hpair).2 w X hcard
        have hsub : Z ⊆ W := Finset.filter_subset _ _
        change (W \ Z).card ≤ 1+R d*(q+1) at hlost
        rw [Finset.card_sdiff_of_subset hsub] at hlost
        have hnext : d+1+e = m := by omega
        have hl1 := (hstage (d+1) e hnext).2
        change lost q R (d+1) < N at hl1
        have hadd : lost q R (d+1) = lost q R d + (1+R d*(q+1)) :=
          Finset.sum_range_succ _ _
        have hw' : N-lost q R (d+1) ≤ Z.card := by omega
        have hd' (l) (hl : l ∈ Z) : q+1-(d+1) ≤ (T.filter (fun p => I p l)).card := by
          have h1 := hd l (hsub hl)
          have h2 := hdegs l hl
          change _ ≤ (T.filter (fun p => I p l)).card + 1 at h2
          omega
        obtain ⟨l,hl⟩ := Finset.card_pos.mp (show 0 < Z.card by omega)
        have hpdeg := hd' l hl
        obtain ⟨p,hp'⟩ := Finset.card_pos.mp (show 0 < (T.filter (fun p => I p l)).card by omega)
        obtain ⟨hpT,hpl⟩ := Finset.mem_filter.mp hp'
        have hs' : State ((k-(d+1))+1) I B S W := by
          rwa [show k-(d+1)+1 = k-d by omega]
        have yes : run (view N B sg) X {w} = true := by simpa using hyes
        obtain ⟨D,wellD,countD,sizeD,stateD⟩ := spill N (k-(d+1)) e I B S W X w sg T Z
          hwellB hcrossB hs' hw0 hX havoid yes rfl rfl ⟨p,hpT,l,hl,hpl⟩
        exact ih (d+1) hnext D T Z wellD countD (sizeD.trans hsize) stateD hw' hd'
  apply stage m 0 (by omega) C Finset.univ Finset.univ hwell hcross (le_refl _)
  · simpa using start
  · simp [lost]
  · intro l _
    simp [hline]
