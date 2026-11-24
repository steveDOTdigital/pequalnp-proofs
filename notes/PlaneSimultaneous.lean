import PlaneGateProjection
import PlaneProtectedFlags

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneGateProjection

namespace PlaneSimultaneous

def row (X : Finset (Fin n)) : List Bool := List.ofFn (fun i => decide (i ∈ X))
def wirePrefix (C : Circuit) (j : ℕ) (x : List Bool) := (C.gates.take j).foldl step x

def active (C : Circuit) (j : ℕ) (X : Finset (Fin n)) : Prop :=
  ∃ g, C.gates[j]? = some g ∧ ∃ i ∈ g.inputs, (wirePrefix C j (row X)).getD i false = true

theorem row_mono {X Y : Finset (Fin n)} (sub : X ⊆ Y) : below (row X) (row Y) := by
  refine ⟨by simp [row], ?_⟩
  intro i
  by_cases h : i < n
  · simpa [row,h] using (show (⟨i,h⟩ : Fin n) ∈ X → ⟨i,h⟩ ∈ Y from fun m => sub m)
  · simp [row, h]

theorem prefix_mono (C : Circuit) (mc : Monotone2 C) (j : ℕ) {X Y : Finset (Fin n)}
    (sub : X ⊆ Y) : below (wirePrefix C j (row X)) (wirePrefix C j (row Y)) := by
  have ordered (gs : List Gate) (allAO : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (x y : List Bool) (xy : below x y) : below (gs.foldl step x) (gs.foldl step y) := by
    induction gs generalizing x y with
    | nil => exact xy
    | cons g gs ih =>
      exact ih (fun k hk => allAO k (List.mem_cons_of_mem _ hk)) _ _
        (extend xy (bit_mono (allAO _ List.mem_cons_self) (Or.inl rfl) xy))
  exact ordered _ (fun g hg => (mc g (List.mem_of_mem_take hg)).1) _ _ (row_mono sub)

def edit (C : Circuit) (E : Finset ℕ) (A : Finset (Fin n)) (j : ℕ) (g : Gate) : Gate :=
  if j ∈ E then
    match g.op, g.inputs with
    | .and, [a,b] => ⟨.or, [if (wirePrefix C j (row A)).getD a false then b else a]⟩
    | _, _ => g
  else g

theorem edit_cases (C : Circuit) (E : Finset ℕ) (A : Finset (Fin n)) (j : ℕ) (g : Gate) :
    (edit C E A j g = g ∧ (j ∉ E ∨ g.op ≠ .and ∨ g.inputs.length ≠ 2)) ∨
    ∃ a b, j ∈ E ∧ g.op = .and ∧ g.inputs = [a,b] ∧
      edit C E A j g = ⟨.or, [if (wirePrefix C j (row A)).getD a false then b else a]⟩ := by
  by_cases sel : j ∈ E
  · rcases g with ⟨op,ins⟩
    cases op <;> simp [edit,sel]
    cases ins with
    | nil => simp
    | cons a rest =>
      cases rest with
      | nil => simp
      | cons b rest => cases rest <;> simp
  · exact Or.inl ⟨by simp [edit,sel],Or.inl sel⟩

theorem selects (n : ℕ) (C : Circuit) (mc : Monotone2 C) (E : Finset ℕ)
    (G : Finset (Fin n) → Prop) (initial : G ∅) :
    ∃ (A : Finset (Fin n)) (D : Circuit), G A ∧ A.card ≤ 2*E.card ∧
      D.size = C.size ∧ Monotone2 D ∧
      (∀ j g, C.gates[j]? = some g →
        (D.gates[j]? = some g ∧ (j ∉ E ∨ g.op ≠ .and ∨ g.inputs.length ≠ 2)) ∨
        ∃ i ∈ g.inputs, D.gates[j]? = some ⟨.or,[i]⟩) ∧
      (∀ x, C.eval x = true → D.eval x = true) ∧
      (∀ B : Finset (Fin n), B.card ≤ 2 → G (A ∪ B) →
        D.eval (List.ofFn (fun i => decide (i ∈ A ∪ B))) =
        C.eval (List.ofFn (fun i => decide (i ∈ A ∪ B)))) := by
  classical
  let key := E.equivFin.symm
  let H := fun (i : Fin E.card) (X : Finset (Fin n)) => active C (key i).val X
  have hmono : ∀ i a b, a ⊆ b → H i a → H i b := by
    rintro i a b hab ⟨g,hg,w,hw,hot⟩
    exact ⟨g,hg,w,hw,(prefix_mono C mc _ hab).2 _ hot⟩
  obtain ⟨A, allowed, ⟨T,_,cost⟩, locked⟩ := PlaneProtectedFlags.stabilize n E.card G H hmono initial
  have small : A.card ≤ 2*E.card := by
    have h : T.card ≤ E.card := by simpa using Finset.card_le_univ T
    omega
  have stable (j : ℕ) (hj : j ∈ E) : ¬ active C j A →
      ∀ B : Finset (Fin n), B.card ≤ 2 → G (A ∪ B) → ¬ active C j (A ∪ B) := by
    simpa only [H,key,Equiv.symm_apply_apply] using locked (E.equivFin ⟨j,hj⟩)
  let ps := C.gates.mapIdx (fun j g => (g,edit C E A j g))
  let D : Circuit := ⟨ps.map Prod.snd,C.output⟩
  have src : ps.map Prod.fst = C.gates := by
    apply List.ext_getElem
    · simp [ps]
    · intro i hi hj
      simp [ps]
  have member {j : ℕ} {p : Gate × Gate} (h : ps[j]? = some p) :
      C.gates[j]? = some p.1 ∧ p.2 = edit C E A j p.1 := by
    simp only [ps,List.getElem?_mapIdx] at h
    cases e : C.gates[j]? with
    | none => simp [e] at h
    | some g =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst p
      exact ⟨rfl,rfl⟩
  have shape (j : ℕ) (p : Gate × Gate) (hp : ps[j]? = some p) :
      (p.2 = p.1 ∧ (j ∉ E ∨ p.1.op ≠ .and ∨ p.1.inputs.length ≠ 2)) ∨
      ∃ i ∈ p.1.inputs, p.1.op = .and ∧ p.2 = ⟨.or,[i]⟩ := by
    rw [(member hp).2]
    rcases edit_cases C E A j p.1 with same | ⟨a,b,_,op,ins,edited⟩
    · exact Or.inl same
    · right
      refine ⟨_,?_,op,edited⟩
      rw [ins]
      split <;> simp
  have valid : ∀ p ∈ ps, (p.1.op = .and ∨ p.1.op = .or) ∧ projects p.1 p.2 := by
    intro p hm
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hm
    have orig := (member hj).1
    refine ⟨(mc _ (List.mem_of_getElem? orig)).1,?_⟩
    rcases shape j p hj with same | ⟨i,hi,op,eq⟩
    · exact Or.inl same.1.symm
    · exact Or.inr ⟨op,i,hi,by rw [eq],by rw [eq]⟩
  refine ⟨A,D,allowed,small,by simp [D,ps,Circuit.size],?_,?_,?_,?_⟩
  · intro g hg
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hg
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hp
    rcases shape j p hj with ⟨eq,_⟩ | ⟨i,_,_,eq⟩
    · rw [eq]
      exact mc _ (List.mem_of_getElem? (member hj).1)
    · simp [eq]
  · intro j g h
    have pair : ps[j]? = some (g,edit C E A j g) := by simp [ps,List.getElem?_mapIdx,h]
    have target : D.gates[j]? = some (edit C E A j g) := by simp [D,List.getElem?_map,pair]
    rw [target]
    rcases shape _ _ pair with ⟨eq,h⟩ | ⟨i,hi,_,eq⟩
    · exact Or.inl ⟨congrArg some eq,h⟩
    · exact Or.inr ⟨i,hi,congrArg some eq⟩
  · intro x
    have dom := output_dominates ps C.output valid x
    simpa only [src] using dom
  · intro B bsize safe
    let x := row (A ∪ B)
    have eq := exact_run ps x (by
      intro pre p post split
      let j := pre.length
      have atJ : ps[j]? = some p := by
        rw [split,List.getElem?_append_right (by rfl)]
        simp [j]
      obtain ⟨orig,edited⟩ := member atJ
      have old : C.gates.take j = pre.map Prod.fst := by
        rw [← src,split,List.map_append]
        simp [j]
      change bit ((pre.map Prod.fst).foldl step x) p.1 = bit ((pre.map Prod.fst).foldl step x) p.2
      rw [← old,edited]
      rcases edit_cases C E A j p.1 with same | ⟨a,b,inE,op,ins,rep⟩
      · rw [same.1]
      · let ws := fun Z : Finset (Fin n) => wirePrefix C j (row Z)
        have act (Z : Finset (Fin n)) :
            active C j Z ↔ ((ws Z).getD a false || (ws Z).getD b false) = true := by
          simp [active,orig,ins,ws,Bool.or_eq_true]
        have stuck : ((ws A).getD a false || (ws A).getD b false) = false →
            ((ws (A ∪ B)).getD a false || (ws (A ∪ B)).getD b false) = false := by
          intro off
          have h := stable j inE (fun on => Bool.noConfusion (off.symm.trans ((act A).mp on)))
            B bsize safe
          cases out : ((ws (A ∪ B)).getD a false || (ws (A ∪ B)).getD b false) with
          | false => rfl
          | true => exact False.elim (h ((act _).mpr out))
        have up := (prefix_mono C mc j (show A ⊆ A ∪ B from Finset.subset_union_left)).2
        have bits := selectBit _ _ _ _ (up a) (up b) stuck
        rw [rep]
        change bit (ws (A ∪ B)) p.1 = bit (ws (A ∪ B)) _
        simp only [bit,op,ins,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
          List.all_cons,List.all_nil,id_eq,Bool.and_true,Bool.or_false]
        cases h : (wirePrefix C j (row A)).getD a false <;>
          simpa only [ws,h,Bool.false_eq_true,eq_self,ite_false,ite_true] using bits)
    rw [src] at eq
    exact congrArg (fun w : List Bool => w.getD C.output false) eq.symm

end PlaneSimultaneous
