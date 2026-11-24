import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace ElevenThreeMarks

theorem assemble : ∀ (P : Fin 4 → Circuit) (a : Fin 3 → List ℕ),
      (∀ i, Monotone2 (P i)) → (∀ i, (a i).length ≤ 2) →
      ∃ C : Circuit, Monotone2 C ∧ C.size = (∑ i, (P i).size) + 3 ∧
      let w := fun (xs : List Bool) (k : ℕ) => ((List.finRange 3).take k).foldl (fun ws i =>
        let vs := (P i.castSucc).wires ws
        vs ++ [(a i).all (fun j => vs.getD j false)]) xs
      ∀ xs, C.eval xs = (P 3).eval (w xs 3) := by
  intro P a legal arity
  let gate := fun i : Fin 3 => (⟨GateOp.and,a i⟩ : Gate)
  let C : Circuit := ⟨(P 0).gates ++ [gate 0] ++ (P 1).gates ++ [gate 1] ++
      (P 2).gates ++ [gate 2] ++ (P 3).gates,(P 3).output⟩
  refine ⟨C,?_,?_,?_⟩
  · have marked (i : Fin 3) : (gate i).op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧
          (gate i).inputs.length ≤ 2 := ⟨Or.inl rfl,arity i⟩
    intro g hg
    change g ∈ (_ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _) at hg
    simp only [List.mem_append,List.mem_singleton] at hg
    rcases hg with ((((((h | h) | h) | h) | h) | h) | h)
    · exact legal 0 g h
    · exact h ▸ marked 0
    · exact legal 1 g h
    · exact h ▸ marked 1
    · exact legal 2 g h
    · exact h ▸ marked 2
    · exact legal 3 g h
  · simp [C,Circuit.size,Fin.sum_univ_succ]
    omega
  · dsimp only
    intro xs
    have indices : (List.finRange 3).take 3 = [0,1,2] := by decide
    rw [indices]
    simp [C,Circuit.eval,Circuit.wires,List.foldl_append,gate,GateOp.eval,List.all_map]

end ElevenThreeMarks
