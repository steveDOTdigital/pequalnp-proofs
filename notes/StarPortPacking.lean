import PEqualNP.MetaComplexity.Helpers.Elim
import Mathlib.Combinatorics.Hall.Basic

namespace StarPortPacking

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers

-- Each selected input occurrence is routed to the same extra, zero-pinned input k.
-- Counting its reader gates charges only once when both slots of a gate were selected.
def readersOf (k : ℕ) : List Gate → ℕ
  | [] => 0
  | g :: tail => (if k ∈ g.inputs then 1 else 0) + readersOf k tail

theorem simultaneousSaving (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (ok : ∀ g ∈ gs, NOk g) (valid : k < acc.1.length)
    (pin : acc.1.getD k (Stat.const false) = Stat.const false) :
    (elim n gs acc).2.length + readersOf k gs ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim, readersOf]
  | cons g gs ih =>
    let next := elimStep n acc g
    have stable : next.1.getD k (Stat.const false) = Stat.const false := by
      dsimp [next, elimStep]
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact pin
    have step := ih next (fun h hh => ok h (List.mem_cons_of_mem _ hh))
      (by dsimp [next, elimStep]; simp; omega) stable
    change (elim n gs next).2.length + readersOf k (g :: gs) ≤ _
    by_cases mark : k ∈ g.inputs
    · have hg := ok g List.mem_cons_self
      have skip : (simplify g.op (n+acc.2.length)
          (g.inputs.map fun w => acc.1.getD w (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hg.1.1
        · simpa using hg.1.2
        · intro h; simpa using hg.2 h
        · exact ⟨false, List.mem_map.mpr ⟨k, mark, pin⟩⟩
      have len : next.2.length = acc.2.length := by
        change (acc.2 ++ (simplify g.op (n+acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [skip]; simp
      simp only [readersOf, ite_eq_left mark, List.length_cons]
      omega
    · have one := toList_length_le (simplify g.op (n+acc.2.length)
          (g.inputs.map fun w => acc.1.getD w (Stat.const false))).1
      have len : next.2.length ≤ acc.2.length + 1 := by
        dsimp [next, elimStep]; rw [List.length_append]; omega
      simp only [readersOf, ite_eq_right mark, Nat.zero_add, List.length_cons]
      omega

-- Semantics and the simultaneous size bound refer to the very same compiled circuit.
theorem compiledCut (n : ℕ) (gs : List Gate) (ok : ∀ g ∈ gs, NOk g) :
    let acc := elim n gs (initStats n false, [])
    acc.2.length + readersOf n gs ≤ gs.length ∧
    ∀ x : Fin n → Bool, Inv n (List.ofFn x)
      (wiresFrom gs (List.ofFn x ++ [false])) acc := by
  constructor
  · have pin : (initStats n false).getD n (Stat.const false) = Stat.const false := by
      apply getD_snoc_len
      simp
    simpa using simultaneousSaving n n gs (initStats n false, []) ok
      (by simp [initStats]) pin
  · intro x
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (ok g hg).1) (inv_init n false x)

-- Positive edges missed by the cut are the only new terms needed at the output.
theorem restore {V : Type*} [DecidableEq V] {E lost : Finset (Finset V)}
    {before after : Finset V → Prop}
    (correct : ∀ z, before z ↔ ∃ e ∈ E, e ⊆ z)
    (lower : ∀ z, after z → before z)
    (mono : ∀ a b, a ⊆ b → after a → after b)
    (lostSubset : lost ⊆ E) (kept : ∀ e ∈ E, e ∉ lost → after e) (z : Finset V) :
    (after z ∨ ∃ e ∈ lost, e ⊆ z) ↔ before z := by
  constructor
  · rintro (ha | ⟨e, he, hz⟩)
    · exact lower z ha
    · exact (correct z).mpr ⟨e, lostSubset he, hz⟩
  · intro hb
    obtain ⟨e, he, hz⟩ := (correct z).mp hb
    by_cases hl : e ∈ lost
    · exact Or.inr ⟨e, hl, hz⟩
    · exact Or.inl (mono _ _ hz (kept e he hl))

-- A star with m edges has m gates. Joining it to a surviving residual costs one more.
-- Tracking which edges the residual rejects permits extraction on both shores at once.
theorem extendExtraction {V : Type*} [DecidableEq V]
    {E P L : Finset (Finset V)} {core next : Finset V → Prop}
    (old : ∀ z, (core z ∨ ∃ e ∈ P, e ⊆ z) ↔ ∃ e ∈ E, e ⊆ z)
    (miss : ∀ e ∈ P, ¬core e) (lower : ∀ z, next z → core z)
    (mono : ∀ a b, a ⊆ b → next a → next b) (newEdges : L ⊆ E)
    (lost : ∀ e ∈ L, ¬next e) (keep : ∀ e ∈ E, e ∉ P → e ∉ L → next e) :
    (∀ z, (next z ∨ ∃ e ∈ P ∪ L, e ⊆ z) ↔ ∃ e ∈ E, e ⊆ z) ∧
    (∀ e ∈ P ∪ L, ¬next e) := by
  constructor
  · intro z
    constructor
    · rintro (hn | ⟨e, h, sub⟩)
      · exact (old z).mp (Or.inl (lower z hn))
      · rcases Finset.mem_union.mp h with hp | hl
        · exact (old z).mp (Or.inr ⟨e, hp, sub⟩)
        · exact ⟨e, newEdges hl, sub⟩
    · rintro ⟨e, he, sub⟩
      by_cases hp : e ∈ P
      · exact Or.inr ⟨e, Finset.mem_union_left _ hp, sub⟩
      by_cases hl : e ∈ L
      · exact Or.inr ⟨e, Finset.mem_union_right _ hl, sub⟩
      exact Or.inl (mono _ _ sub (keep e he hp hl))
  · intro e he hn
    rcases Finset.mem_union.mp he with hp | hl
    · exact miss e hp (lower e hn)
    · exact lost e hl hn

-- Finite sets record which marked slots an accepting proof uses. An OR selects
-- one proof, an AND selects two, and traversing a marked slot inserts its label.
section Proofs
variable {Port : Type*} [DecidableEq Port]
abbrev Proofs (α : Type*) := Finset α → Prop
def avoids (p : Proofs Port) (s : Finset Port) := ∃ a, p a ∧ Disjoint a s
def joinOr (p q : Proofs Port) : Proofs Port := fun a => p a ∨ q a
def joinAnd (p q : Proofs Port) : Proofs Port :=
  fun a => ∃ b c, p b ∧ q c ∧ b ∪ c = a
def mark (i : Port) (p : Proofs Port) : Proofs Port := fun a => ∃ b, p b ∧ insert i b = a

omit [DecidableEq Port] in
theorem avoidsOr (p q : Proofs Port) (s : Finset Port) :
    avoids (joinOr p q) s ↔ avoids p s ∨ avoids q s := by
  constructor
  · rintro ⟨a, hp | hq, dis⟩
    · exact Or.inl ⟨a, hp, dis⟩
    · exact Or.inr ⟨a, hq, dis⟩
  · rintro (⟨a, hp, dis⟩ | ⟨a, hp, dis⟩)
    · exact ⟨a, Or.inl hp, dis⟩
    · exact ⟨a, Or.inr hp, dis⟩

theorem avoidsAnd (p q : Proofs Port) (s : Finset Port) :
    avoids (joinAnd p q) s ↔ avoids p s ∧ avoids q s := by
  constructor
  · rintro ⟨_, ⟨a,b,ha,hb,rfl⟩, dis⟩
    exact ⟨⟨a, ha, (Finset.disjoint_union_left.mp dis).1⟩,
      ⟨b, hb, (Finset.disjoint_union_left.mp dis).2⟩⟩
  · rintro ⟨⟨a, ha, da⟩, ⟨b, hb, db⟩⟩
    exact ⟨_, ⟨a,b,ha,hb,rfl⟩, Finset.disjoint_union_left.mpr ⟨da,db⟩⟩

theorem avoidsMark (i : Port) (p : Proofs Port) (s : Finset Port) :
    avoids (mark i p) s ↔ i ∉ s ∧ avoids p s := by
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, dis⟩
    obtain ⟨hi, da⟩ := Finset.disjoint_insert_left.mp dis
    exact ⟨hi, a, ha, da⟩
  · rintro ⟨hi,a,ha,da⟩
    exact ⟨_, ⟨a,ha,rfl⟩, Finset.disjoint_insert_left.mpr ⟨hi, da⟩⟩
end Proofs

-- If peeling a nonempty star within budget is excluded, each selected reader costs
-- at least one distinct jointly lost edge. Losing none would strictly shrink the circuit.
theorem starExpansion (slots saved lost : ℕ) (count : slots ≤ saved)
    (noFree : lost = 0 → saved = 0)
    (noPeel : 0 < lost → saved < lost + 1) : slots ≤ lost := by
  by_cases h : lost = 0
  · have := noFree h; omega
  · have := noPeel (by omega); omega

-- For each retained edge, choose one accepting proof. Every jointly lost edge occurs
-- in the union of the proof incidences of the ports that were cut.
theorem assignPorts {Port Edge : Type*} [DecidableEq Edge]
    (uses : Port → Finset Edge) (lost : Finset Port → Finset Edge)
    (expands : ∀ s, s.card ≤ (lost s).card)
    (meets : ∀ s, lost s ⊆ s.biUnion uses) :
    ∃ f : Port → Edge, Function.Injective f ∧ ∀ p, f p ∈ uses p := by
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective uses).mp
  intro s
  exact (expands s).trans (Finset.card_le_card (meets s))

-- With one unit of strict expansion, any prescribed edge can be kept free.
theorem reservePort {Port Edge : Type*} [DecidableEq Edge]
    (uses : Port → Finset Edge) (spare : Edge)
    (strict : ∀ s : Finset Port, s.Nonempty → s.card < (s.biUnion uses).card) :
    ∃ f : Port → Edge, Function.Injective f ∧ ∀ p, f p ∈ (uses p).erase spare := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective _).mp
  intro s
  by_cases hs : s.Nonempty
  · have h := strict s hs
    have le : ((s.biUnion uses).erase spare).card ≤
        (s.biUnion fun p => (uses p).erase spare).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨neq, mem⟩ := Finset.mem_erase.mp he
      obtain ⟨p,hp,ep⟩ := Finset.mem_biUnion.mp mem
      exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_erase.mpr ⟨neq,ep⟩⟩
    by_cases inside : spare ∈ s.biUnion uses
    · rw [Finset.card_erase_of_mem inside] at le; omega
    · rw [Finset.erase_eq_of_notMem inside] at le; omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

-- The converse quantifies over all per-edge routings. For every surviving edge
-- one can choose an accepting proof avoiding this particular set of cut ports.
theorem robustIff {Port Edge Route : Type*} [DecidableEq Edge]
    (uses : Route → Port → Finset Edge) (lost : Finset Port → Finset Edge)
    (meets : ∀ r s, lost s ⊆ s.biUnion (uses r))
    (avoid : ∀ s, ∃ r, s.biUnion (uses r) ⊆ lost s) :
    (∀ s, s.card ≤ (lost s).card) ↔
    ∀ r, ∃ f : Port → Edge, Function.Injective f ∧ ∀ p, f p ∈ uses r p := by
  constructor
  · intro h r; exact assignPorts _ _ h (meets r)
  · intro h s
    obtain ⟨r, hr⟩ := avoid s
    exact ((Finset.all_card_le_biUnion_card_iff_exists_injective (uses r)).mpr (h r) s).trans
      (Finset.card_le_card hr)

-- A block of raw variables whose sole exit H is shared. The other input of K
-- records the outside assignment. Each block variable is essential on an edge.
theorem privateBlock {V W : Type*} [DecidableEq V] [DecidableEq W] [Nonempty V]
    (H : Finset V → Bool) (K : Bool → Finset W → Bool)
    (empty : K false ∅ = false)
    (insideSingles : ∀ a, K (H {a}) ∅ = false)
    (outsideSingles : ∀ b, K false {b} = false)
    (active : ∀ a, (∃ a', K (H {a,a'}) ∅ = true) ∨
      ∃ b, K (H {a}) {b} = true) :
    (∀ a, H {a} = true) ∨ ((∀ a, H {a} = false) ∧ K true ∅ = true) := by
  classical
  by_cases ex : ∃ a, H {a} = true
  · obtain ⟨a, on⟩ := ex
    have blocked := insideSingles a
    rw [on] at blocked
    left
    intro v
    rcases active v with ⟨w, hw⟩ | ⟨b, hb⟩
    · cases e : H {v,w} <;> simp [e, empty, blocked] at hw
    · cases e : H {v} with
      | true => rfl
      | false => simp [e, outsideSingles] at hb
  · have off : ∀ a, H {a} = false := by
      intro a
      cases h : H {a} with
      | false => rfl
      | true => exact False.elim (ex ⟨a,h⟩)
    refine Or.inr ⟨off, ?_⟩
    let a := Classical.choice (inferInstance : Nonempty V)
    rcases active a with ⟨w, hw⟩ | ⟨b, hb⟩
    · cases e : H {a,w} with
      | false => simp [e, empty] at hw
      | true => simpa [e] using hw
    · simp [off, outsideSingles] at hb

theorem residualBudget (g n m cover excess : ℕ)
    (reads : g + 1 = n + excess) (sharing : 3 ≤ excess)
    (noCompleteExtraction : g + 1 < m + cover) :
    n + 2 ≤ g ∧ n + 4 ≤ m + cover := by omega

end StarPortPacking
