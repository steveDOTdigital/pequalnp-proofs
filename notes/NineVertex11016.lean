import PEqualNP.Outside.L_meta_8451
import PEqualNP.Outside.L_meta_8455
import PEqualNP.Outside.L_meta_8459

namespace NineVertex11016
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_8451
open Maj.Helpers Maj.Helpers.Readers

def graph (x : Fin 9 → Bool) := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8)

def circuit : Circuit := ⟨[
  ⟨.or, [4,5]⟩,
  ⟨.or, [9,6]⟩,
  ⟨.and, [0,10]⟩,
  ⟨.or, [5,7]⟩,
  ⟨.or, [12,8]⟩,
  ⟨.and, [1,13]⟩,
  ⟨.or, [2,3]⟩,
  ⟨.and, [6,15]⟩,
  ⟨.or, [2,4]⟩,
  ⟨.and, [7,17]⟩,
  ⟨.or, [3,5]⟩,
  ⟨.and, [8,19]⟩,
  ⟨.or, [11,14]⟩,
  ⟨.or, [21,16]⟩,
  ⟨.or, [22,18]⟩,
  ⟨.or, [23,20]⟩], 24⟩

theorem upper : HasCircuitSize 9 graph 16 := by
  refine ⟨circuit, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | decide +kernel
  · decide +kernel

def leaf (i : Fin 2) : Fin 9 := ![2,3] i

theorem sensitive (i : Fin 2) : Dep graph (leaf i) := by
  refine ⟨fun j => decide (j = 6), ?_⟩
  fin_cases i <;> decide +kernel

theorem varies (i : Fin 2) (b : Bool) : ∃ x y : Fin 9 → Bool,
    graph (Function.update x (leaf i) b) ≠ graph (Function.update y (leaf i) b) := by
  refine ⟨fun _ => false, fun j => decide (j = 0 ∨ j = 4), ?_⟩
  fin_cases i <;> cases b <;> decide +kernel

theorem pin2 (s : ℕ) (h : HasCircuitSize 9 (fun x => graph (Function.update x 2 false)) s) : 14 ≤ s := by
  let labels : Fin 9 → Fin 8 := ![3, 1, 0, 5, 6, 0, 7, 4, 2]
  have smaller := Bow.relabel_size labels _ s h
  have eq : (fun x : Fin 8 → Bool => graph (Function.update (x ∘ labels) 2 false)) =
      (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7)) := by
    funext x
    simp [graph, labels, Function.update, Function.comp_def]
    ac_rfl
  rw [eq] at smaller
  exact PEqualNP.Outside.L_meta_8455 s smaller

theorem pin3 (s : ℕ) (h : HasCircuitSize 9 (fun x => graph (Function.update x 3 false)) s) : 14 ≤ s := by
  let labels : Fin 9 → Fin 8 := ![3, 1, 7, 0, 5, 0, 6, 4, 2]
  have smaller := Bow.relabel_size labels _ s h
  have eq : (fun x : Fin 8 → Bool => graph (Function.update (x ∘ labels) 3 false)) =
      (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 7) || (x 6 && x 7)) := by
    funext x
    simp [graph, labels, Function.update, Function.comp_def]
    ac_rfl
  rw [eq] at smaller
  exact PEqualNP.Outside.L_meta_8459 s smaller

theorem pinned (i : Fin 2) (s : ℕ)
    (h : HasCircuitSize 9 (fun x => graph (Function.update x (leaf i) false)) s) : 14 ≤ s := by
  fin_cases i <;> first | exact pin2 s h | exact pin3 s h

theorem lower (s : ℕ) (h : HasCircuitSize 9 graph s) : 15 ≤ s := by
  obtain ⟨t, saved, small⟩ := Bow.one_gate_at 8 graph (leaf 0) false s (sensitive 0) (varies 0 false) h
  have := pinned 0 t small
  omega

-- In either deletion, a second read or a constant OR operand would save
-- two gates and contradict the checked fourteen-gate lower bound.
theorem uniqueOr (i : Fin 2) {gs : List Gate} {o : ℕ} (L : Least 9 graph gs o) (size : gs.length ≤ 15) :
    ∃ p g, gs[p]? = some g ∧ (leaf i).val ∈ g.inputs ∧ g.op = .or ∧
      ∀ q, Reads gs q (leaf i).val → q = p := by
  obtain ⟨p, hp⟩ := L.dep_read (leaf i) (sensitive i) (varies i)
  have impossible (q : ℕ) (other : p ≠ q) (rc : RC 8 gs (leaf i) false q) : False := by
    obtain ⟨s, saving, small⟩ := L.save2 (leaf i) false (varies i false) p q other (rc_input false hp) rc
    have := pinned i s small
    omega
  obtain ⟨g, hg, raw⟩ := hp
  refine ⟨p, g, hg, raw, ?_, ?_⟩
  · by_contra nonOr
    have fb : fixBit g = false := by unfold fixBit; split <;> simp_all
    have fixed := const_read 8 gs L.hcl (leaf i) false p g hg (leaf i) raw
      (by rw [fb]; exact stF_self 8 gs (leaf i) false)
    obtain ⟨q, later, _, rc⟩ := L.next (leaf i) false (varies i false) p
      (List.getElem?_eq_some_iff.mp hg).1 fixed
    exact impossible q (by omega) rc
  · intro q hq
    by_contra neq
    exact impossible q (Ne.symm neq) (rc_input false hq)

-- Any companion signal which is high on both sides of a sensitive flip
-- would mask it at the unique reader and hence at the circuit output.
theorem noMask (i : Fin 2) {gs : List Gate} {o p : ℕ} {g : Gate} (L : Least 9 graph gs o)
    (atGate : gs[p]? = some g) (isOr : g.op = .or)
    (unique : ∀ q, Reads gs q (leaf i).val → q = p) (w : ℕ) (mem : w ∈ g.inputs)
    (x : Fin 9 → Bool)
    (diff : graph (Function.update x (leaf i) false) ≠ graph (Function.update x (leaf i) true)) :
    ¬(vl gs (Function.update x (leaf i) false) w = true ∧
      vl gs (Function.update x (leaf i) true) w = true) := by
  let v := leaf i
  let lo := Function.update x v false
  let hi := Function.update x v true
  rintro ⟨bitL,bitH⟩
  have forced (y : Fin 9 → Bool) (bit : vl gs y w = true) : vl gs y (9+p) = true := by
    rw [vl_gate gs L.hcl y p g atGate,isOr]
    change (g.inputs.map (vl gs y)).any id = true
    apply List.any_eq_true.mpr
    exact ⟨true,List.mem_map.mpr ⟨w,mem,bit⟩,rfl⟩
  have agree := agree_B gs L.hcl lo hi (fun j => j = v.val) (o+1)
    (by
      intro j hj away
      rw [vl_input gs lo j hj, vl_input gs hi j hj]
      have ne : (⟨j,hj⟩ : Fin 9) ≠ v := fun e => away (congrArg Fin.val e)
      simp [lo,hi,Function.update_of_ne ne])
    (by
      rintro q gate pos _ _ ⟨a, reads, rfl⟩ _
      have eq : q = p := unique q ⟨gate,pos,reads⟩
      subst q
      exact (forced lo bitL).trans (forced hi bitH).symm)
  have out : o ≠ v.val := by
    intro eq
    obtain ⟨u,z,h⟩ := varies i false
    apply h
    rw [← L.hev, ← L.hev,eq,vl_input gs _ v.val v.isLt,vl_input gs _ v.val v.isLt]
    simp [v]
  exact diff ((L.hev lo).symm.trans ((agree o (by omega) out).trans (L.hev hi)))

def allowed (i : Fin 2) (a b : Fin 9) : Bool :=
  let pairs : List (Nat × Nat) := if i = 0 then
    [(0, 1), (0, 4), (0, 5), (0, 6), (1, 3), (1, 5), (1, 7), (1, 8), (3, 4), (3, 6), (3, 8), (4, 7), (5, 8)]
    else [(0, 1), (0, 4), (0, 5), (0, 6), (1, 2), (1, 5), (1, 7), (1, 8), (2, 5), (2, 6), (2, 7), (4, 7), (5, 8)]
  pairs.contains (a.val,b.val)

private def witnessRow (i : Fin 2) (a b : Fin 9) : Fin 512 :=
  let tab : Fin 9 → Fin 9 → Fin 512 := if i = 0 then
    ![![129, 0, 0, 137, 0, 0, 0, 129, 385],
    ![0, 66, 0, 0, 82, 0, 66, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![137, 0, 0, 136, 0, 168, 0, 136, 0],
    ![0, 82, 0, 0, 80, 112, 80, 0, 336],
    ![0, 0, 0, 168, 112, 96, 96, 160, 0],
    ![0, 66, 0, 0, 80, 96, 64, 192, 320],
    ![129, 0, 0, 136, 0, 160, 192, 128, 384],
    ![385, 0, 0, 0, 336, 0, 320, 384, 320]]
    else ![![257, 0, 261, 0, 0, 0, 0, 385, 257],
    ![0, 66, 0, 0, 82, 0, 66, 0, 0],
    ![261, 0, 260, 0, 276, 0, 0, 0, 260],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 82, 276, 0, 80, 112, 80, 0, 272],
    ![0, 0, 0, 0, 112, 96, 96, 224, 0],
    ![0, 66, 0, 0, 80, 96, 64, 192, 320],
    ![385, 0, 0, 0, 0, 224, 192, 192, 384],
    ![257, 0, 260, 0, 272, 0, 320, 384, 256]]
  tab a b

private theorem sensitiveRows : ∀ (i : Fin 2) (a b : Fin 9), a ≤ b → a ≠ leaf i → b ≠ leaf i →
    allowed i a b = false →
    let x := fun j : Fin 9 => (witnessRow i a b).val.testBit j.val
    x a = true ∧ x b = true ∧
      graph (Function.update x (leaf i) false) ≠ graph (Function.update x (leaf i) true) := by
  decide +kernel

theorem andMateAllowed (i : Fin 2) {gs : List Gate} {o p : ℕ} {g : Gate}
    (L : Least 9 graph gs o) (atGate : gs[p]? = some g) (isOr : g.op = .or)
    (unique : ∀ q, Reads gs q (leaf i).val → q = p) (w : ℕ) (mem : w ∈ g.inputs)
    (a b : Fin 9) (order : a ≤ b) (ha : a ≠ leaf i) (hb : b ≠ leaf i)
    (rep : ∀ x : Fin 9 → Bool, vl gs x w = (x a && x b)) : allowed i a b = true := by
  by_contra! bad
  have failed : allowed i a b = false := by simpa using bad
  let x := fun j : Fin 9 => (witnessRow i a b).val.testBit j.val
  obtain ⟨xa,xb,diff⟩ := sensitiveRows i a b order ha hb failed
  apply noMask i L atGate isOr unique w mem x diff
  constructor <;> rw [rep] <;> simp [Function.update_of_ne ha,Function.update_of_ne hb,x,xa,xb]

theorem noRawMate (i : Fin 2) {gs : List Gate} {o p : ℕ} {g : Gate}
    (L : Least 9 graph gs o) (atGate : gs[p]? = some g) (isOr : g.op = .or)
    (unique : ∀ q, Reads gs q (leaf i).val → q = p) (a : Fin 9) (ha : a ≠ leaf i) :
    a.val ∉ g.inputs := by
  intro mem
  have fixed := andMateAllowed i L atGate isOr unique a.val mem a a le_rfl ha ha
    (fun x => by rw [vl_input gs x a.val a.isLt]; simp)
  have absent : ∀ (j : Fin 2) (u : Fin 9), allowed j u u = false := by decide +kernel
  rw [absent] at fixed
  contradiction

end NineVertex11016
