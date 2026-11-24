import notes.PetersenFinalNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenOneNotSplit

private def Good (g : Gate) : Prop := ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨
        ∃ i : ℕ, g = ⟨GateOp.not,[i]⟩
private def Positive (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

private theorem cut (gs : List Gate) (ok : ∀ g ∈ gs, Good g)
    (one : gs.countP (fun g => g.op.eval [false]) = 1) :
    ∃ (pre post : List Gate) (arg : ℕ), gs = pre ++ (⟨GateOp.not,[arg]⟩ :: post) ∧
      (∀ g ∈ pre, Positive g) ∧ (∀ g ∈ post, Positive g) := by
  induction gs with
  | nil => simp at one
  | cons g gs ih =>
    have tail : ∀ z ∈ gs, Good z := fun z hz => ok z (List.mem_cons_of_mem g hz)
    rcases ok g List.mem_cons_self with mono | ⟨arg,rfl⟩
    · have neg : ¬ g.op.eval [false] = true := by
        rcases mono.1 with hand | hor
        · rw [hand]; decide
        · have eq : g.op = GateOp.or := hor
          rw [eq]; decide
      obtain ⟨pre,post,arg,eq,pm,qm⟩ := ih tail (by simpa only [List.countP_cons_of_neg (p := fun z : Gate => z.op.eval [false]) neg] using one)
      refine ⟨g::pre,post,arg,by simp [eq],?_,qm⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hit
      · exact mono
      · exact pm z hit
    · have zero : gs.countP (fun z => z.op.eval [false]) = 0 := by
        change (⟨GateOp.not,[arg]⟩ :: gs).countP (fun z => z.op.eval [false]) = 1 at one
        rw [List.countP_cons] at one
        change gs.countP (fun z => z.op.eval [false]) + 1 = 1 at one
        omega
      refine ⟨[],gs,arg,rfl,by simp,?_⟩
      intro z hz
      rcases tail z hz with good | ⟨i,rfl⟩
      · exact good
      · exact False.elim (List.countP_eq_zero.mp zero _ hz rfl)

theorem splitter : ∀ C : Circuit, C.gates[0]? = some ⟨GateOp.or,[0,3]⟩ →
      (∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨
        ∃ i : ℕ, g = ⟨GateOp.not,[i]⟩) →
      C.gates.countP (fun g => g.op.eval [false]) = 1 →
      ∃ A B : Circuit, A.size+B.size+2=C.size ∧ Monotone2 A ∧ Monotone2 B ∧
      let w := fun x : Fin 9 → Bool => A.wires (List.ofFn x ++ [x 0 || x 3])
      let h := fun x => (w x).getD A.output false
      let k := fun x t => B.eval (w x ++ [t])
      Monotone h ∧ (∀ x y, x ≤ y → ∀ a b : Bool, a ≤ b → k x a ≤ k y b) ∧
      ∀ x, k x (!(h x)) = circuitFun 9 C x := by
  intro C first legal total
  cases C with
  | mk gates out =>
    cases gates with
    | nil => simp at first
    | cons g gs =>
      have start : g = ⟨GateOp.or,[0,3]⟩ := Option.some.inj first
      subst g
      have one : gs.countP (fun z => z.op.eval [false]) = 1 := by
        change ((⟨GateOp.or,[0,3]⟩ : Gate) :: gs).countP (fun z => z.op.eval [false]) = 1 at total
        rw [List.countP_cons] at total
        exact total
      obtain ⟨pre,post,arg,cutEq,pm,qm⟩ := cut gs (fun z hz => legal z (List.mem_cons_of_mem _ hz)) one
      subst gs
      let A : Circuit := ⟨pre,arg⟩
      let B : Circuit := ⟨post,out⟩
      refine ⟨A,B,?_,pm,qm,?_⟩
      · change pre.length + post.length + 2 = (_ :: (pre ++ _ :: post)).length
        simp
        omega
      let row := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 3]
      let w := fun x : Fin 9 → Bool => A.wires (row x)
      have len (x y : Fin 9 → Bool) : (w x).length = (w y).length := by
        change (FinalNotWires.fold pre (row x)).length = (FinalNotWires.fold pre (row y)).length
        simp [FinalNotWires.fold_length,row]
      have order (x y : Fin 9 → Bool) (le : x ≤ y) : FinalNotWires.WireLE (w x) (w y) := by
        apply FinalNotWires.fold_mono pre (row x) (row y) (fun z hz => (pm z hz).1)
        · simp [row]
        · apply FinalNotWires.append_mono _ _ (by simp)
          · exact FinalNotWires.inputs_mono x y (fun j => Bool.le_iff_imp.mp (le j))
          · have disj : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a || b) ≤ (c || d) := by decide
            exact Bool.le_iff_imp.mp (disj _ _ _ _ (le 0) (le 3))
      refine ⟨fun x y xy => Bool.le_iff_imp.mpr (order x y xy arg),?_,?_⟩
      · intro x y xy a b ab
        apply Bool.le_iff_imp.mpr
        exact FinalNotWires.fold_mono post _ _ (fun z hz => (qm z hz).1) (by simp [len x y])
          (FinalNotWires.append_mono _ _ (len x y) (order x y xy) _ _ (Bool.le_iff_imp.mp ab)) out
      · intro x
        have raw (j : Fin 9) : (List.ofFn x).getD j.val false = x j := by
          rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
        have e0 := raw 0
        have e3 := raw 3
        change (List.ofFn x).getD 0 false = x 0 at e0
        change (List.ofFn x).getD 3 false = x 3 at e3
        have init : FinalNotWires.step (List.ofFn x) ⟨GateOp.or,[0,3]⟩ = row x := by
          change _ ++ [(List.ofFn x).getD 0 false || ((List.ofFn x).getD 3 false || false)] = _
          rw [e0,e3,Bool.or_false]
        change (FinalNotWires.fold post (w x ++ [!((w x).getD arg false)])).getD out false =
          (FinalNotWires.fold ((⟨GateOp.or,[0,3]⟩ : Gate) :: (pre ++ ⟨GateOp.not,[arg]⟩ :: post)) (List.ofFn x)).getD out false
        change _ = (FinalNotWires.fold (pre ++ ⟨GateOp.not,[arg]⟩ :: post)
          (FinalNotWires.step (List.ofFn x) ⟨GateOp.or,[0,3]⟩)).getD out false
        rw [init]
        simp only [FinalNotWires.fold,List.foldl_append,List.foldl_cons]
        rfl

end PetersenOneNotSplit
