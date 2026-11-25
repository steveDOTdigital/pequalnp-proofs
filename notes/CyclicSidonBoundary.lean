import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.HeptadCover PEqualNP.GenericRejection

namespace CyclicSidonBoundary

theorem geometry : ∀ (m : ℕ) (D : Finset (Fin (m+1))), 0 ∈ D → (∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ∀ d ∈ D, a ≠ b → a-b = c-d → a=c) →
    let S := fun l : Fin (m+1) => Finset.univ.filter (fun p : Fin (m+1) => p-l ∈ D)
    (∀ i, i ∈ S i) ∧ (∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1) ∧
      (incidences S).card = (m+1)*D.card := by
  intro m D h0 unique
  let S := fun l : Fin (m+1) => Finset.univ.filter (fun p : Fin (m+1) => p-l ∈ D)
  change (∀ i, i ∈ S i) ∧ (∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1) ∧
    (incidences S).card = (m+1)*D.card
  refine ⟨fun i => by simpa [S] using h0,?_,?_⟩
  · intro a b ab
    apply Finset.card_le_one.mpr
    intro x hx y hy
    simp only [S,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and] at hx hy
    have ne : x-a ≠ x-b := fun h => ab (sub_right_inj.mp h)
    have delta : (x-a)-(x-b) = (y-a)-(y-b) := by abel
    exact sub_left_inj.mp (unique _ hx.1 _ hx.2 _ hy.1 _ hy.2 ne delta)
  · have eq : (incidences S).card = (Finset.univ (α:=Fin (m+1)) ×ˢ D).card := by
      apply Finset.card_bij (fun pl _ => (pl.2,pl.1-pl.2))
      · intro pl hp
        simpa [incidences,S] using hp
      · intro a ha b hb he
        have right := congrArg Prod.fst he
        have diff := congrArg Prod.snd he
        change a.2=b.2 at right
        change a.1-a.2=b.1-b.2 at diff
        rw [right] at diff
        exact Prod.ext (sub_left_inj.mp diff) right
      · rintro ⟨l,d⟩ hd
        refine ⟨(d+l,l),?_,?_⟩
        · simpa [incidences,S] using hd
        · simp
    simpa using eq

-- The tape monotonicity proof is shared with the independent singleton-frontier result.
def increases (xs ys : List Bool) :=
  xs.length = ys.length ∧ ∀ i, xs.getD i false = true → ys.getD i false = true

theorem snoc {xs ys : List Bool} {a b : Bool} (h : increases xs ys) (ab : a=true → b=true) :
    increases (xs++[a]) (ys++[b]) := by
  obtain ⟨len,ord⟩ := h
  refine ⟨by simp [len],?_⟩
  intro i
  by_cases hi : i<xs.length
  · rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (len ▸ hi)]
    exact ord i
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),← len]
    cases i-xs.length with
    | zero => exact ab
    | succ j => simp [List.getD_eq_getElem?_getD]

def advance (xs : List Bool) (g : Gate) :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

theorem advanceMono (xs ys : List Bool) (g : Gate) (op : g.op=.and ∨ g.op=.or)
    (h : increases xs ys) : increases (advance xs g) (advance ys g) := by
  apply snoc h
  rcases op with e|e
  · simp only [e, GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    intro all w hw
    exact h.2 w (all w hw)
  · simp only [e, GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨w,hw,hit⟩
    exact ⟨w,hw,h.2 w hit⟩

theorem foldMono (gs : List Gate) (ops : ∀ g ∈ gs, g.op=.and ∨ g.op=.or)
    (xs ys : List Bool) (h : increases xs ys) :
    increases (gs.foldl advance xs) (gs.foldl advance ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g tail ih =>
    exact ih (fun k hk => ops k (List.mem_cons_of_mem _ hk)) _ _
      (advanceMono xs ys g (ops g List.mem_cons_self) h)

theorem tapeOfFn {n : ℕ} (f g : Fin n → Bool)
    (up : ∀ i, f i=true → g i=true) : increases (List.ofFn f) (List.ofFn g) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases h : i<n
  · simpa [List.getD_eq_getElem?_getD,h] using up ⟨i,h⟩
  · simp [List.getD_eq_getElem?_getD,h]

theorem tapeAppend {a b c d : List Bool} (ab : increases a b) (cd : increases c d) :
    increases (a++c) (b++d) := by
  obtain ⟨len,hab⟩ := ab
  obtain ⟨rest,hcd⟩ := cd
  constructor
  · simp [len,rest]
  · intro i
    by_cases hi : i<a.length
    · rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (len ▸ hi)]
      exact hab i
    · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len]
      exact hcd _

theorem onSets {n : ℕ} (C : Circuit) (model : IsAO2 (n+n) C)
    {X X' Y Y' : Finset (Fin n)} (hx : X⊆X') (hy : Y⊆Y') :
    C.eval (incidenceInput X Y) = true → C.eval (incidenceInput X' Y') = true := by
  have raw : increases (incidenceInput X Y) (incidenceInput X' Y') := by
    apply tapeAppend
    · apply tapeOfFn
      simpa only [decide_eq_true_eq] using (show ∀ i, i ∈ X → i ∈ X' from fun _ hi => hx hi)
    · apply tapeOfFn
      simpa only [decide_eq_true_eq] using (show ∀ i, i ∈ Y → i ∈ Y' from fun _ hi => hy hi)
  exact (foldMono C.gates model.1 _ _ raw).2 C.output

theorem boundary : ∀ (n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit), IsAO2 (n+n) C →
    (∀ p l, p ∈ S l → C.eval (incidenceInput {p} {l}) = true) →
    (∀ (X Y : Finset (Fin n)), (∀ p, p ∈ X ↔ ∀ l ∈ Y, p ∉ S l) →
       (∀ l, l ∈ Y ↔ ∀ p ∈ X, p ∉ S l) → C.eval (incidenceInput X Y) = false) →
    ∀ z : Fin (n+n) → Bool, circuitFun (n+n) C z =
      decide (∃ p l, p ∈ S l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true) := by
  intro n S C model positive negative z
  let X : Finset (Fin n) := Finset.univ.filter fun p => z (Fin.castAdd n p) = true
  let Y : Finset (Fin n) := Finset.univ.filter fun l => z (Fin.natAdd n l) = true
  have sx (p : Fin n) : p∈X ↔ z (Fin.castAdd n p)=true := by simp [X]
  have sy (l : Fin n) : l∈Y ↔ z (Fin.natAdd n l)=true := by simp [Y]
  have split : Fin.append (fun p : Fin n => decide (p∈X))
      (fun l : Fin n => decide (l∈Y)) = z := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro p
      rw [Fin.append_left]
      exact Bool.eq_iff_iff.mpr (by simpa using sx p)
    · intro l
      rw [Fin.append_right]
      exact Bool.eq_iff_iff.mpr (by simpa using sy l)
  have row : incidenceInput X Y = List.ofFn z := by
    change List.ofFn (fun p : Fin n => decide (p∈X)) ++ List.ofFn (fun l : Fin n => decide (l∈Y)) = _
    rw [←List.ofFn_fin_append,split]
  change C.eval (List.ofFn z) = _
  rw [←row]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro on
    by_contra free
    let A := Finset.univ.filter fun p => ∀ l ∈ Y, p ∉ S l
    let B := Finset.univ.filter fun l => ∀ p ∈ A, p ∉ S l
    have memA (p : Fin n) : p ∈ A ↔ ∀ l ∈ Y, p ∉ S l := by simp [A]
    have memB (l : Fin n) : l ∈ B ↔ ∀ p ∈ A, p ∉ S l := by simp [B]
    have subX : X ⊆ A := by
      intro p hp
      exact (memA p).mpr (fun l hl edge => free ⟨p,l,edge,(sx p).mp hp,(sy l).mp hl⟩)
    have subY : Y ⊆ B := by
      intro l hl
      exact (memB l).mpr (fun p hp => (memA p).mp hp l hl)
    have closedA (p : Fin n) : p ∈ A ↔ ∀ l ∈ B, p ∉ S l := by
      exact ⟨fun hp l hl => (memB l).mp hl p hp,
        fun miss => (memA p).mpr (fun l hl => miss l (subY hl))⟩
    have bad := onSets C model subX subY on
    rw [negative A B closedA memB] at bad
    contradiction
  · rintro ⟨p,l,edge,hp,hl⟩
    exact onSets C model (Finset.singleton_subset_iff.mpr ((sx p).mpr hp))
      (Finset.singleton_subset_iff.mpr ((sy l).mpr hl)) (positive p l edge)

end CyclicSidonBoundary
