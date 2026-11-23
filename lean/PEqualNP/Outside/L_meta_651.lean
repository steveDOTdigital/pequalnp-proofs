import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_651

abbrev Vertex := Fin 10

def edges : List (Vertex × Vertex) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]

def adjacent (i j : Vertex) : Bool := edges.contains (i,j) || edges.contains (j,i)

def edgeFunction (x : Vertex → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
  (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

private def generator : Fin 3 → Vertex → Vertex :=
  ![![1,2,3,4,0,6,7,8,9,5], ![5,7,9,6,8,0,2,4,1,3], ![0,5,7,2,1,4,8,9,3,6]]

private lemma permutes : ∀ g, Function.Bijective (generator g) := by decide

private lemma preserves : ∀ g i j, adjacent (generator g i) (generator g j) = adjacent i j := by
  decide

private lemma unchanged (g : Fin 3) (x : Vertex → Bool) :
    edgeFunction (x ∘ generator g) = edgeFunction x := by
  fin_cases g <;> simp [edgeFunction, generator] <;> ac_rfl

private def move (g : Fin 3) (p : Vertex × Vertex) : Vertex × Vertex :=
  (generator g p.1, generator g p.2)

private def pairs : ℕ → List (Vertex × Vertex)
  | 0 => [(0,1),(0,2)]
  | n+1 =>
    let old := pairs n
    (old ++ old.map (move 0) ++ old.map (move 1) ++ old.map (move 2)).eraseDups

private def represented (p : Vertex × Vertex) : Prop :=
  ∃ e : Vertex ≃ Vertex, (∀ x, edgeFunction (x ∘ e) = edgeFunction x) ∧
    (∀ i j, adjacent (e i) (e j) = adjacent i j) ∧ e 0 = p.1 ∧ (e 1 = p.2 ∨ e 2 = p.2)

private lemma moved {p : Vertex × Vertex} (h : represented p) (g : Fin 3) :
    represented (move g p) := by
  rcases h with ⟨e, inv, adj, h0, h12⟩
  let perm := Equiv.ofBijective (generator g) (permutes g)
  refine ⟨e.trans perm, fun x => (inv (x ∘ generator g)).trans (unchanged g x), ?_,
    congrArg (generator g) h0, h12.imp (congrArg _) (congrArg _)⟩
  exact fun i j => (preserves g (e i) (e j)).trans (adj i j)

private lemma represented_of_mem (depth : ℕ) : ∀ p ∈ pairs depth, represented p := by
  induction depth with
  | zero =>
    intro p hp
    simp only [pairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨Equiv.refl _, fun _ => rfl, fun _ _ => rfl, rfl, Or.inl rfl⟩
    · exact ⟨Equiv.refl _, fun _ => rfl, fun _ _ => rfl, rfl, Or.inr rfl⟩
  | succ n ih =>
    intro p hp
    simp only [pairs, List.mem_eraseDups, List.mem_append, List.mem_map] at hp
    rcases hp with ((old | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩
    · exact ih p old
    · exact moved (ih q hq) 0
    · exact moved (ih q hq) 1
    · exact moved (ih q hq) 2

set_option maxRecDepth 16000 in
private lemma coverage : ∀ i j : Vertex, i ≠ j → (i,j) ∈ pairs 5 := by decide

-- With ordered input positions, adjacency is the only distinction.
lemma first_pair_symmetry (i j : Vertex) (hne : i ≠ j) :
    ∃ e : Vertex ≃ Vertex, (∀ x, edgeFunction (x ∘ e) = edgeFunction x) ∧
      e 0 = i ∧ e (if adjacent i j then 1 else 2) = j := by
  obtain ⟨e, inv, adj, h0, h12⟩ := represented_of_mem 5 _ (coverage i j hne)
  change e 0 = i at h0
  change e 1 = j ∨ e 2 = j at h12
  refine ⟨e, inv, h0, ?_⟩
  rcases h12 with h1 | h2
  · have val : adjacent i j = true := by rw [← h0, ← h1, adj]; decide
    simpa [val] using h1
  · have val : adjacent i j = false := by rw [← h0, ← h2, adj]; decide
    simpa [val] using h2

private def probe (i j k : Vertex) (b c : Bool) (v : Vertex) : Bool :=
  if v = i then b else if v = j then c else decide (v = k)

-- One further active vertex witnesses the relevance of j at either value of i.
private lemma probe_exists : ∀ i j : Vertex, i ≠ j → ∃ k : Vertex, ∀ b : Bool,
    edgeFunction (probe i j k b false) = false ∧ edgeFunction (probe i j k b true) = true := by
  decide

-- If fixing i makes a gate ignore j, that gate cannot be the sole channel
-- carrying j to the answer. The downstream computation may use every other input.
lemma bypass_required (i j : Vertex) (hne : i ≠ j) (gate : Bool → Bool → Bool)
    (b : Bool) (absorbs : gate b false = gate b true) :
    ¬ ∃ downstream : (Vertex → Bool) → Bool → Bool, ∀ x,
      edgeFunction x = downstream (Function.update x j false) (gate (x i) (x j)) := by
  rintro ⟨downstream, realizes⟩
  obtain ⟨k, both⟩ := probe_exists i j hne
  have same : Function.update (probe i j k b false) j false =
      Function.update (probe i j k b true) j false := by
    funext v
    by_cases hj : v = j <;> simp [Function.update, probe, hj]
  have off := realizes (probe i j k b false)
  have on := realizes (probe i j k b true)
  rw [(both b).1] at off
  rw [(both b).2] at on
  simp only [probe, ite_eq_right hne.symm] at off on
  change false = downstream (Function.update (probe i j k b false) j false) (gate b false) at off
  change true = downstream (Function.update (probe i j k b true) j false) (gate b true) at on
  rw [same, absorbs] at off
  exact Bool.noConfusion (off.trans on.symm)

private def canonicalEdge (i j : Vertex) := (min i j, max i j)

private def edgeSet := edges.toFinset.image (fun e => canonicalEdge e.1 e.2)

private lemma edge_count : edgeSet.card = 15 := by decide

set_option maxRecDepth 16000 in
private lemma cover_bound : ∀ S : Finset Vertex,
    (∀ e ∈ edges, e.1 ∈ S ∨ e.2 ∈ S) → 6 ≤ S.card := by decide

private lemma no_four_cycle : ∀ a b c d : Vertex, a ≠ b → c ≠ d →
    adjacent a c → adjacent a d → adjacent b c → ¬ adjacent b d := by decide

-- Every nonempty complete bipartite subgraph is a star. In particular an
-- OR of two different leaves cannot feed stars at two different centers.
lemma rectangle_is_star (A B : Finset Vertex) (valid : ∀ a ∈ A, ∀ b ∈ B, adjacent a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra! large
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp large.1
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp large.2
  exact no_four_cycle a b c d hab hcd (valid _ ha _ hc) (valid _ ha _ hd)
    (valid _ hb _ hc) (valid _ hb _ hd)

-- A star term with d positive leaves uses d-1 binary OR gates and one AND.
-- Combining all the terms uses one fewer binary OR than the number of terms.
private def starEdges (g : Vertex × Finset Vertex) :=
  g.2.image (canonicalEdge g.1)

private def starUnion : List (Vertex × Finset Vertex) → Finset (Vertex × Vertex)
  | [] => ∅
  | g :: rest => starEdges g ∪ starUnion rest

private lemma starUnion_card (groups : List (Vertex × Finset Vertex)) :
    (starUnion groups).card ≤ (groups.map fun g => g.2.card).sum := by
  induction groups with
  | nil => simp [starUnion]
  | cons g tail ih =>
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le ih)

private lemma starUnion_mem {edge : Vertex × Vertex} (groups : List (Vertex × Finset Vertex)) :
    edge ∈ starUnion groups → ∃ g ∈ groups, edge ∈ starEdges g := by
  induction groups with
  | nil => simp [starUnion]
  | cons g tail ih =>
    intro h
    rcases Finset.mem_union.mp h with here | later
    · exact ⟨g, List.mem_cons_self, here⟩
    · obtain ⟨v, hv, he⟩ := ih later
      exact ⟨v, List.mem_cons_of_mem g hv, he⟩

lemma star_cover_cost (groups : List (Vertex × Finset Vertex)) (covers : edgeSet ⊆ starUnion groups) :
    20 ≤ (groups.map fun g => g.2.card).sum + groups.length - 1 := by
  have edgeBudget := (Finset.card_le_card covers).trans (starUnion_card groups)
  rw [edge_count] at edgeBudget
  let centers := (groups.map Prod.fst).toFinset
  have hc : 6 ≤ centers.card := by
    apply cover_bound
    rintro ⟨u, w⟩ he
    obtain ⟨g, hg, prodMem⟩ := starUnion_mem groups (covers
      (Finset.mem_image.mpr ⟨(u,w), List.mem_toFinset.mpr he, rfl⟩))
    have inc : g.1 ∈ centers := List.mem_toFinset.mpr (List.mem_map.mpr ⟨g, hg, rfl⟩)
    obtain ⟨v, _, eq⟩ := Finset.mem_image.mp prodMem
    have endpoint : g.1 = u ∨ g.1 = w := by
      change canonicalEdge g.1 v = canonicalEdge u w at eq
      unfold canonicalEdge at eq
      rcases le_total g.1 v with s | s <;> rcases le_total u w with r | r <;>
        simp [s, r] at eq <;> tauto
    rcases endpoint with h | h
    · exact Or.inl (h ▸ inc)
    · exact Or.inr (h ▸ inc)
  have count : centers.card ≤ groups.length := by
    simpa [centers] using (List.toFinset_card_le (groups.map Prod.fst))
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit20 : Circuit :=
  ⟨[⟨.or,[1,4]⟩, ⟨.or,[10,5]⟩, ⟨.and,[0,11]⟩,
    ⟨.or,[2,6]⟩, ⟨.and,[1,13]⟩,
    ⟨.or,[2,4]⟩, ⟨.or,[15,8]⟩, ⟨.and,[3,16]⟩,
    ⟨.or,[2,5]⟩, ⟨.or,[18,9]⟩, ⟨.and,[7,19]⟩,
    ⟨.or,[6,5]⟩, ⟨.and,[8,21]⟩, ⟨.or,[4,6]⟩, ⟨.and,[9,23]⟩,
    ⟨.or,[12,14]⟩, ⟨.or,[25,17]⟩, ⟨.or,[26,20]⟩, ⟨.or,[27,22]⟩, ⟨.or,[28,24]⟩],29⟩

lemma twenty_suffices : HasCircuitSize 10 edgeFunction 20 := by
  refine ⟨circuit20, ?_, by decide, ?_⟩
  · intro g hg
    simp [circuit20] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst g <;> simp
  · intro x
    have list : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9] := by
      simp [List.ofFn_succ]
    rw [list]
    simp [Circuit.eval, Circuit.wires, circuit20, GateOp.eval, edgeFunction, Bool.and_or_distrib_left]
    ac_rfl

private def extendWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)]

private lemma tail_ignores (gs : List Gate) (j : ℕ)
    (unused : ∀ g ∈ gs, j ∉ g.inputs) (u v : List Bool) (len : u.length = v.length)
    (same : ∀ a ≠ j, u.getD a false = v.getD a false) :
    ∀ a ≠ j, (gs.foldl extendWire u).getD a false = (gs.foldl extendWire v).getD a false := by
  induction gs generalizing u v with
  | nil => exact same
  | cons g gs ih =>
    have inputs : g.inputs.map (fun a => u.getD a false) =
        g.inputs.map (fun a => v.getD a false) :=
      List.map_congr_left fun a ha => same a (fun eq => unused g List.mem_cons_self (eq ▸ ha))
    apply ih (fun t ht => unused t (List.mem_cons_of_mem g ht))
    · simp [extendWire, len]
    · intro a ha
      unfold extendWire
      rw [inputs]
      by_cases h : a < u.length
      · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (len ▸ h)]
        exact same a ha
      · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), len]

private lemma extends_input (gs : List Gate) (u : List Bool) :
    ∃ suffix, gs.foldl extendWire u = u ++ suffix := by
  induction gs generalizing u with
  | nil => exact ⟨[], (List.append_nil _).symm⟩
  | cons g gs ih =>
    obtain ⟨suffix, hs⟩ := ih (extendWire u g)
    exact ⟨[_] ++ suffix, hs.trans (List.append_assoc ..)⟩

private lemma input_read (x : Vertex → Bool) (i : Vertex) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

-- This states the bypass property for the repository's circuit evaluator.
-- At the absorbing value of the other input, the first gate has lost j.
lemma later_reader (i j : Vertex) (hne : i ≠ j) (op : GateOp) (tail : List Gate) (out : ℕ)
    (b : Bool) (absorbs : op.eval [b,false] = op.eval [b,true])
    (computes : ∀ x : Vertex → Bool,
      (Circuit.mk (⟨op,[i.val,j.val]⟩ :: tail) out).eval (List.ofFn x) = edgeFunction x) :
    ∃ g ∈ tail, j.val ∈ g.inputs := by
  have out_ne : out ≠ j.val := by
    rintro rfl
    let x : Vertex → Bool := fun k => decide (k = j)
    have f0 : ∀ k : Vertex, edgeFunction (fun v => decide (v = k)) = false := by decide
    have eq := computes x
    obtain ⟨more, hm⟩ := extends_input (⟨op,[i.val,j.val]⟩ :: tail) (List.ofFn x)
    change ((⟨op,[i.val,j.val]⟩ :: tail).foldl extendWire (List.ofFn x)).getD j.val false = _ at eq
    rw [hm, List.getD_append _ _ _ _ (by simp), input_read, f0] at eq
    simp [x] at eq
  by_contra! unused
  apply bypass_required i j hne (fun u v => op.eval [u,v]) b absorbs
  refine ⟨fun z val => (tail.foldl extendWire (List.ofFn z ++ [val])).getD out false, ?_⟩
  intro x
  rw [← computes x]
  change (tail.foldl extendWire (extendWire (List.ofFn x) ⟨op,[i.val,j.val]⟩)).getD out false = _
  simp only [extendWire, List.map_cons, List.map_nil, input_read]
  apply tail_ignores tail j.val unused _ _ (by simp) _ out out_ne
  intro a ha
  by_cases valid : a < 10
  · let k : Vertex := ⟨a,valid⟩
    have hkj : k ≠ j := fun eq => ha (congrArg Fin.val eq)
    rw [List.getD_append _ _ _ _ (by simpa using valid), List.getD_append _ _ _ _ (by simpa using valid)]
    exact (input_read x k).trans ((Function.update_of_ne hkj ..).symm.trans
      (input_read (Function.update x j false) k).symm)
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt valid),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt valid)]
    simp

-- At vertex zero the false cofactor deletes the three incident edges.
-- For the true cofactor the three neighbors enter separately and the remaining
-- six vertices induce a cycle. These circuits cap what a one-vertex bound can pay.
private def binaryCircuit (nodes : List (Bool × ℕ × ℕ)) (out : ℕ) : Circuit :=
  ⟨nodes.map (fun p => ⟨if p.1 then .and else .or, [p.2.1,p.2.2]⟩), out⟩

private lemma binary_allowed (nodes : List (Bool × ℕ × ℕ)) (out : ℕ) :
    FanInTwo (binaryCircuit nodes out) := by
  intro g hg
  obtain ⟨⟨op,a,b⟩, _, rfl⟩ := List.mem_map.mp hg
  cases op <;> simp

private def withoutZero := binaryCircuit
  [(false,2,6),(true,1,10),(false,2,4),(false,12,8),(true,3,13),
   (false,2,5),(false,15,9),(true,7,16),(false,6,5),(true,8,18),
   (false,4,6),(true,9,20),(false,11,14),(false,22,17),(false,23,19),(false,24,21)] 25

private def withZero := binaryCircuit
  [(false,3,7),(true,2,10),(false,3,6),(true,8,12),(false,6,7),(true,9,14),
   (false,11,13),(false,16,15),(false,17,1),(false,18,4),(false,19,5)] 20

lemma false_cofactor : HasCircuitSize 10 (fun x => edgeFunction (Function.update x 0 false)) 16 := by
  refine ⟨withoutZero, binary_allowed _ _, by decide, ?_⟩
  intro x
  have list : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9] := by simp [List.ofFn_succ]
  rw [list]
  simp [withoutZero, binaryCircuit, Circuit.eval, Circuit.wires, GateOp.eval, edgeFunction,
    Function.update, Bool.and_or_distrib_left]
  ac_rfl

lemma true_cofactor : HasCircuitSize 10 (fun x => edgeFunction (Function.update x 0 true)) 11 := by
  refine ⟨withZero, binary_allowed _ _, by decide, ?_⟩
  intro x
  have list : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9] := by simp [List.ofFn_succ]
  rw [list]
  simp [withZero, binaryCircuit, Circuit.eval, Circuit.wires, GateOp.eval, edgeFunction,
    Function.update, Bool.and_or_distrib_left]
  cases h1 : x 1 <;> cases h4 : x 4 <;> cases h5 : x 5 <;> simp
  ac_rfl

end PEqualNP.Outside.L_meta_651
