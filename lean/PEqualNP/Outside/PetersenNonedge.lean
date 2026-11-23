import PEqualNP.Outside.L_meta_651

namespace PEqualNP.Outside.PetersenNonedge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_651

private def addr (n cap j : ℕ) :=
  if j < n then j else if j = n then cap else j-1

private def rename (n cap : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (addr n cap)⟩

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

private theorem snoc_other (w : List Bool) (b : Bool) (j : ℕ) (ne : j ≠ w.length) :
    (w ++ [b]).getD j false = w.getD j false := by
  by_cases lt : j < w.length
  · exact List.getD_append _ _ _ _ lt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem simulate (n cap : ℕ) (gs : List Gate) (before after : List Bool)
    (hlen : before.length = after.length+1) (hn : n ≤ after.length)
    (bound : after.length + gs.length ≤ cap)
    (agree : ∀ j, after.getD (addr n cap j) false = before.getD j false) :
    ∀ j, ((gs.map (rename n cap)).foldl step after).getD (addr n cap j) false =
      (gs.foldl step before).getD j false := by
  induction gs generalizing before after with
  | nil => exact agree
  | cons g gs ih =>
    have room : after.length < cap := by simp at bound; omega
    have eq : (rename n cap g).inputs.map (fun j => after.getD j false) =
        g.inputs.map (fun j => before.getD j false) := by
      simp only [rename, List.map_map, Function.comp_def]
      exact List.map_congr_left fun j _ => agree j
    apply ih
    · simp [step, hlen]
    · simp [step]; omega
    · simp [step] at *; omega
    · intro j
      simp only [step, eq]
      by_cases atEnd : j = before.length
      · subst j
        have a : addr n cap before.length = after.length := by unfold addr; split_ifs <;> omega
        rw [a]
        simp [rename]
      · have other : addr n cap j ≠ after.length := by
          unfold addr
          split_ifs <;> omega
        rw [snoc_other _ _ _ other, snoc_other _ _ _ atEnd]
        exact agree j

-- False is the evaluator's value for an out-of-range wire, including an
-- out-of-range output. The sentinel stays beyond the last gate.
theorem frozen_size {n : ℕ} (gs : List Gate) (out : ℕ) (ok : FanInTwo ⟨gs,out⟩) :
    HasCircuitSize n (fun x => (Circuit.mk gs out).eval (List.ofFn x ++ [false])) gs.length := by
  let cap := n + gs.length
  refine ⟨⟨gs.map (rename n cap), addr n cap out⟩, ?_, by simp [Circuit.size], ?_⟩
  · intro g hg
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    have allowed := ok h hh
    simpa [rename] using allowed
  · intro x
    apply simulate n cap gs (List.ofFn x ++ [false]) (List.ofFn x)
    · simp
    · simp
    · simp [cap]
    · intro j
      by_cases low : j < n
      · simp only [addr, ite_eq_left low]
        exact (List.getD_append _ _ _ _ (by simpa using low)).symm
      by_cases mid : j = n
      · subst j
        simp [addr, cap]
      · rw [List.getD_eq_default _ _ (by simp [addr,low,mid]; omega),
          List.getD_eq_default _ _ (by simp; omega)]

abbrev Input := Vertex → Bool

def forced (tail : List Gate) (out : ℕ) (x : Input) (w : Bool) :=
  (Circuit.mk tail out).eval (List.ofFn x ++ [w])

set_option maxRecDepth 12000 in
theorem delete_nonedge (tail : List Gate) (out : ℕ) (ok : FanInTwo ⟨tail,out⟩)
    (h : ∀ x, forced tail out x (x 0 && x 2) = edgeFunction x)
    (up : ∀ x, ∀ v ∈ ([0,2] : List Vertex),
      forced tail out (Function.update x v false) false = true → forced tail out x false = true)
    (wire : ∀ x, x 0 = true → x 2 = true →
      forced tail out x false = true → forced tail out x true = true) :
    HasCircuitSize 10 edgeFunction tail.length := by
  have splitEdge : ∀ x : Input, edgeFunction x =
      (edgeFunction (Function.update x 0 false) || edgeFunction (Function.update x 2 false)) := by decide
  have agree (x : Input) : forced tail out x false = edgeFunction x := by
    cases h0 : x 0 <;> cases h2 : x 2 <;> try simpa [h0,h2] using h x
    have on : forced tail out x true = edgeFunction x := by simpa [h0,h2] using h x
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact fun hx => on ▸ wire x h0 h2 hx
    · intro he
      rw [splitEdge x, Bool.or_eq_true] at he
      rcases he with he | he
      · apply up x 0 (by decide)
        have eq := h (Function.update x 0 false)
        simpa only [Function.update_self, Bool.false_and] using eq.trans he
      · apply up x 2 (by decide)
        have eq := h (Function.update x 2 false)
        simpa only [Function.update_self, Bool.and_false] using eq.trans he
  rw [← funext agree]
  exact frozen_size tail out ok

-- If freezing the gate creates a false positive, its input mask is one
-- of these five. Bit i of the mask is the value of vertex i.
set_option maxRecDepth 16000 in
theorem negative_masks : ∀ m : Fin 1024,
    (m.val.testBit 0 = true ∧ m.val.testBit 2 = true ∧
      edgeFunction (fun i => m.val.testBit i.val) = false) ↔
      m.val ∈ ([5,69,261,517,773] : List ℕ) := by decide

def guarded23 : Circuit := ⟨[
  ⟨.and,[0,2]⟩, ⟨.not,[10]⟩,
  ⟨.or,[1,4]⟩, ⟨.or,[12,5]⟩, ⟨.and,[0,13]⟩,
  ⟨.or,[1,3]⟩, ⟨.or,[15,7]⟩, ⟨.and,[2,16]⟩,
  ⟨.or,[1,9]⟩, ⟨.or,[18,8]⟩, ⟨.and,[6,19]⟩,
  ⟨.or,[4,8]⟩, ⟨.and,[3,21]⟩, ⟨.or,[7,8]⟩, ⟨.and,[5,23]⟩,
  ⟨.or,[4,7]⟩, ⟨.and,[9,25]⟩, ⟨.or,[14,17]⟩, ⟨.or,[27,20]⟩,
  ⟨.or,[22,24]⟩, ⟨.or,[29,26]⟩, ⟨.and,[11,30]⟩, ⟨.or,[28,31]⟩],32⟩

set_option maxRecDepth 16000 in
theorem guarded23_correct : guarded23.size = 23 ∧ FanInTwo guarded23 ∧
    ∀ x : Input, guarded23.eval (List.ofFn x) = edgeFunction x := by
  refine ⟨rfl, ?_, ?_⟩
  · intro g hg
    simp only [guarded23,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have inputs : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9] := by simp [List.ofFn_succ]
    rw [inputs]
    simp [guarded23, Circuit.eval, Circuit.wires, GateOp.eval, edgeFunction, Bool.and_or_distrib_left]
    cases h0 : x 0 <;> cases h2 : x 2 <;> simp
    all_goals try ac_rfl
    cases (x 1) <;> cases (x 4) <;> cases (x 5) <;> cases (x 3) <;> cases (x 7) <;> simp
    ac_rfl

end PEqualNP.Outside.PetersenNonedge
