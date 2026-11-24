import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

namespace G11CoreProfile

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem classify : let G := edgeGraph 11 (List.ofFn fun i : Fin 16 => let w := (182734661465985816910654985662253763081 : ℕ) >>> (8*i.val)
      (w / 16 % 16,w % 16))
    ∀ I : Finset (Fin 11), I.card=4 → (∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v) →
      ∃ i : Fin 22, ∀ v : Fin 11, ((5337049209409285386193401725542463193349738924283176925588630423176538127 : ℕ) >>> (11*i.val)).testBit v.val = true ↔ v ∈ I := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem density : let G := edgeGraph 11 (List.ofFn fun i : Fin 16 => let w := (182734661465985816910654985662253763081 : ℕ) >>> (8*i.val)
      (w / 16 % 16,w % 16))
    ∀ S : Finset (Fin 11), S.card ≤ 4+([1,2,3,5,8,12,16] : List ℕ).countP (fun k => decide (k ≤ (S.sym2 ∩ G.edgeFinset).card)) := by
  decide +kernel


def graph : SimpleGraph (Fin 11) := edgeGraph 11 (List.ofFn fun i : Fin 16 => let w := (182734661465985816910654985662253763081 : ℕ) >>> (8*i.val)
      (w / 16 % 16,w % 16))
instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (edgeGraph 11 (List.ofFn fun i : Fin 16 => let w := (182734661465985816910654985662253763081 : ℕ) >>> (8*i.val)
      (w / 16 % 16,w % 16))).Adj)
def ports : Finset (Fin 11) := {0,1,2,3}
def seed (i : Fin 22) : Finset (Fin 11) := Finset.univ.filter fun v => ((5337049209409285386193401725542463193349738924283176925588630423176538127 : ℕ) >>> (11*i.val)).testBit v.val = true

theorem seeds : ∀ i, (seed i).card=4 ∧ ∀ u ∈ seed i, ∀ v ∈ seed i, ¬graph.Adj u v := by decide +kernel
theorem portsIndependent : ∀ u ∈ ports, ∀ v ∈ ports, ¬graph.Adj u v := by decide +kernel

-- Each feasible core can be completed with every available port simultaneously.
-- A seed in that completion recovers a seven-vertex original cover attaining
-- this deficit, which proves the converse of the calculation in the reduction.
theorem converse (U : Finset (Sym2 (Fin 11))) (d : ℕ)
    (bound : ∀ T X : Finset (Fin 11), T.card = 7 → graph.IsVertexCover (↑T) → X ⊆ T →
      (graph.deleteEdges ↑U).IsVertexCover (↑(T\X)) → X.card ≤ d)
    (K : Finset (Fin 11)) (disjoint : Disjoint K ports)
    (stable : ∀ u ∈ K, ∀ v ∈ K, ¬(graph.deleteEdges ↑U).Adj u v) :
    let H := graph.deleteEdges (↑U)
    let N := ports.filter fun v => ∃ w ∈ K, H.Adj w v
    (∃ i, seed i ⊆ K ∪ (ports\N)) → K.card ≤ d+N.card := by
  classical
  let H := graph.deleteEdges (↑U)
  let N := ports.filter fun v => ∃ w ∈ K, H.Adj w v
  let Q := K ∪ (ports\N)
  change (∃ i, seed i ⊆ Q) → K.card ≤ d+N.card
  rintro ⟨i,inside⟩
  let T := Finset.univ \ seed i
  let X := Q \ seed i
  have size : T.card=7 := by
    rw [show T = Finset.univ \ seed i from rfl,Finset.card_sdiff_of_subset (Finset.subset_univ _),(seeds i).1]
    rfl
  have avoids (v) (hv : v ∉ T) : v ∈ seed i := by simpa [T] using hv
  have covered : graph.IsVertexCover (↑T) := by
    intro u v edge
    by_contra! both
    exact (seeds i).2 u (avoids u both.1) v (avoids v both.2) edge
  have subset : X ⊆ T := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp hv).2⟩
  have noCross (u) (hu : u ∈ K) (v) (hv : v ∈ ports\N) : ¬H.Adj u v := by
    intro adj
    have both := Finset.mem_sdiff.mp hv
    exact both.2 (Finset.mem_filter.mpr ⟨both.1,u,hu,adj⟩)
  have qInd (u) (hu : u ∈ Q) (v) (hv : v ∈ Q) : ¬ H.Adj u v := by
    rcases Finset.mem_union.mp hu with ku | pu <;> rcases Finset.mem_union.mp hv with kv | pv
    · exact stable u ku v kv
    · exact noCross u ku v pv
    · exact fun h => noCross v kv u pu h.symm
    · exact fun h => portsIndependent u (Finset.mem_sdiff.mp pu).1 v (Finset.mem_sdiff.mp pv).1
        (SimpleGraph.deleteEdges_adj.mp h).1
  have leftover : T\X = Finset.univ\Q := by
    ext v
    by_cases h : v ∈ seed i
    · simp [T,X,h,inside h]
    · simp [T,X,h]
  have resCovered : H.IsVertexCover ↑(T\X) := by
    rw [leftover]
    intro u v adj
    by_contra! neither
    exact qInd u (by simpa using neither.1) v (by simpa using neither.2) adj
  have cap := bound T X size covered subset resCovered
  have xq := Finset.card_sdiff_add_card_eq_card inside
  have apart : Disjoint K (ports\N) := disjoint.mono_right Finset.sdiff_subset
  have total : Q.card = K.card+(ports\N).card := Finset.card_union_of_disjoint apart
  have subN : N ⊆ ports := Finset.filter_subset _ _
  have ns := Finset.card_sdiff_add_card_eq_card subN
  have four : ports.card=4 := by decide
  have seedFour := (seeds i).1
  change X.card+(seed i).card=Q.card at xq
  omega


-- The eleven individually critical edges form two triangles and a pentagon.
def criticalPair : Fin 11 → Fin 11 × Fin 11 :=
  ![(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(5,9),(6,7)]
def criticalEdge (k : Fin 11) := s((criticalPair k).1,(criticalPair k).2)
def oldFour (k : Fin 11) : Finset (Fin 11) :=
  Finset.univ.filter fun v => ((![15,43,15,15,15,526,15,15,29,1066,71] : Fin 11 → ℕ) k).testBit v.val
def extraVertex : Fin 11 → Fin 11 := ![9,10,4,8,5,10,6,7,8,9,7]

theorem criticalWitness : ∀ k : Fin 11,
    (oldFour k).card = 4 ∧ extraVertex k ∉ oldFour k ∧
    (∀ u ∈ oldFour k, ∀ v ∈ oldFour k, ¬graph.Adj u v) ∧
    (∀ u ∈ insert (extraVertex k) (oldFour k), ∀ v ∈ insert (extraVertex k) (oldFour k),
      graph.Adj u v → s(u,v) = criticalEdge k) := by decide +kernel

theorem criticalPresent : ∀ S : Finset (Fin 11), 4 < S.card →
    ∃ k : Fin 11, (criticalPair k).1 ∈ S ∧ (criticalPair k).2 ∈ S := by decide +kernel
theorem criticalAdjacent : ∀ k, graph.Adj (criticalPair k).1 (criticalPair k).2 := by decide +kernel

/-- At zero budget the graph condition is equivalent to retaining these eleven
edges. The other five edges may all be deleted at the same time. -/
theorem zeroIff (U : Finset (Sym2 (Fin 11))) :
    (∀ T X : Finset (Fin 11), T.card=7 → graph.IsVertexCover (↑T) → X ⊆ T →
      (graph.deleteEdges ↑U).IsVertexCover (↑(T\X)) → X.card ≤ 0) ↔
    ∀ k : Fin 11, criticalEdge k ∉ U := by
  classical
  constructor
  · intro bound k missing
    obtain ⟨four,out,ind,only⟩ := criticalWitness k
    let T := Finset.univ \ oldFour k
    let x := extraVertex k
    have sz : T.card=7 := by
      rw [show T = Finset.univ \ oldFour k from rfl,Finset.card_sdiff_of_subset (Finset.subset_univ _),four]
      rfl
    have cover : graph.IsVertexCover (↑T) := by
      intro a b adj
      by_contra! bad
      exact ind a (by simpa [T] using bad.1) b (by simpa [T] using bad.2) adj
    have inside : ({x} : Finset (Fin 11)) ⊆ T := Finset.singleton_subset_iff.mpr (by simpa [T,x] using out)
    have lift (v : Fin 11) (h : v ∉ T\{x}) : v ∈ insert x (oldFour k) := by
      by_cases eq : v=x
      · simp [eq]
      · by_contra! fail
        exact h (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun mem => fail (Finset.mem_insert_of_mem mem)⟩,by simpa using eq⟩)
    have res : (graph.deleteEdges ↑U).IsVertexCover (↑(T\{x})) := by
      intro a b adj
      by_contra! bad
      obtain ⟨g,kept⟩ := SimpleGraph.deleteEdges_adj.mp adj
      exact kept ((only a (lift a bad.1) b (lift b bad.2) g).symm ▸ missing)
    have absurd := bound T {x} sz cover inside res
    simpa using absurd
  · intro kept T X seven _ sub cover
    let S := Finset.univ \ (T\X)
    have maxFour : S.card ≤ 4 := by
      by_contra! more
      obtain ⟨k,l,r⟩ := criticalPresent S more
      have adj : (graph.deleteEdges ↑U).Adj (criticalPair k).1 (criticalPair k).2 :=
        SimpleGraph.deleteEdges_adj.mpr ⟨criticalAdjacent k,kept k⟩
      rcases cover adj with a | b
      · exact (Finset.mem_sdiff.mp l).2 a
      · exact (Finset.mem_sdiff.mp r).2 b
    have ss := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (T\X))
    have ts := Finset.card_sdiff_add_card_eq_card sub
    change S.card+(T\X).card=(Finset.univ : Finset (Fin 11)).card at ss
    simp only [Finset.card_univ,Fintype.card_fin] at ss
    omega

end G11CoreProfile
