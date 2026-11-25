import FlagCrossRank

namespace OrderFourAlarmRank
open FlagCrossRank
open scoped BigOperators

-- We only charge leaves whose labels are physical inputs. A virtual input
-- may distinguish nonlocal cells without contributing to any charged rank.
theorem rawRank {E V : Type} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (T : FlagCrossRank.Tree V) (raw : V → Bool) (left right : E → V)
    (positive negative : E → V → Bool)
    (yes : ∀ e, T.val (positive e) = true) (no : ∀ e, T.val (negative e) = false)
    (endsRaw : ∀ e, raw (left e) = true ∧ raw (right e) = true)
    (different : ∀ e, left e ≠ right e)
    (diag : ∀ e w, positive e w = true → negative e w = false → w = left e ∨ w = right e)
    (off : ∀ a b v w, a ≠ b → (v = left a ∨ v = right a) →
      (v = left b ∨ v = right b) → positive a w = true → negative b w = false → w = v)
    (other : ∀ a v, (v = left a ∨ v = right a) → ∃ b, a ≠ b ∧ (v = left b ∨ v = right b))
    (n : ℕ) (cover : ∀ K : Finset V, (∀ e, left e ∈ K ∨ right e ∈ K) → n ≤ K.card) :
    Fintype.card E + n ≤ T.cost (fun v => if raw v then 1 else 0) := by
  classical
  let weight (v : V) : ℕ := if raw v then 1 else 0
  obtain ⟨P,_,total,truth⟩ := tree_protocol_cost T weight positive negative
  let report (e : E) := P.label (P.start e e)
  let miss (e : E) := if report e = left e then right e else left e
  have pair (e : E) : (report e = left e ∧ miss e = right e) ∨
      (report e = right e ∧ miss e = left e) := by
    obtain ⟨on,zero⟩ := truth e e (yes e) (no e)
    rcases diag e _ on zero with h | h
    · change report e = left e at h; left; simp [miss,h]
    · change report e = right e at h; right; simp [miss,h,(different e).symm]
  have atEnd (e : E) (v : V) (mem : miss e = v ∨ report e = v) :
      v = left e ∨ v = right e := by rcases pair e with h | h <;> grind
  have charge (e : E) : raw (miss e) = true ∧ raw (report e) = true := by
    have h := endsRaw e; rcases pair e with h' | h' <;> grind
  have force (a b : E) (v : V) (ne : a ≠ b) (av : miss a = v ∨ report a = v)
      (bv : miss b = v ∨ report b = v) : P.label (P.start a b) = v := by
    obtain ⟨on,zero⟩ := truth a b (yes a) (no b)
    exact off a b v _ ne (atEnd a v av) (atEnd b v bv) on zero
  have localBound := partitionLocal P.label P.start P.row P.col P.block id miss report
    (fun _ => rfl) (fun e => by rcases pair e with h | h <;> have := different e <;> grind)
    force (by
      intro e v ev
      obtain ⟨b,ne,bv⟩ := other e v (atEnd e v ev)
      refine ⟨b,force e b v ne ev ?_⟩
      rcases pair b with h | h <;> grind)
  let price (v : V) := if raw v then Fintype.card {b // P.label b = v} else 0
  have counted := aggregate miss report price (by
    intro v
    cases h : raw v with
    | true => simpa [price,h] using localBound v
    | false =>
      have : IsEmpty {e // miss e = v} := ⟨fun ⟨e,he⟩ => by
        have := (charge e).1; rw [he,h] at this; contradiction⟩
      have absent : v ∉ Finset.univ.image report := by
        rintro hv; obtain ⟨e,_,he⟩ := Finset.mem_image.mp hv
        have := (charge e).2; rw [he,h] at this; contradiction
      simp [absent,price,h])
  have fiber (v : V) : price v = ∑ b, if P.label b = v then weight v else 0 := by
    cases h : raw v <;> simp [price,weight,h,Fintype.card_subtype,Finset.sum_boole]
  have sum : (∑ v, price v) = ∑ b, weight (P.label b) := by
    simp_rw [fiber]; rw [Finset.sum_comm]; simp
  have minimum := cover (Finset.univ.image report) (fun e => by
    have mem := Finset.mem_image_of_mem report (Finset.mem_univ e)
    rcases pair e with h | h
    · exact Or.inl (h.1 ▸ mem)
    · exact Or.inr (h.1 ▸ mem))
  change Fintype.card E + n ≤ T.cost weight
  rw [←total,←sum]; omega

def substitute {V W : Type} (f : V → FlagCrossRank.Tree W) : FlagCrossRank.Tree V → FlagCrossRank.Tree W
  | .raw v => f v
  | .gate op a b => .gate op (substitute f a) (substitute f b)

theorem substitute_eval {V W : Type} (f : V → FlagCrossRank.Tree W) (T : FlagCrossRank.Tree V) (x : W → Bool) :
    (substitute f T).val x = T.val (fun v => (f v).val x) := by
  induction T with
  | raw => rfl
  | gate op a b ha hb => simp [substitute,FlagCrossRank.Tree.val,ha,hb]

theorem expansion {V W : Type} (raw : V → Bool) (f : V → FlagCrossRank.Tree W)
    (size : ∀ v, (f v).leaves + 2 * (if raw v then 1 else 0) ≤ 3) (T : FlagCrossRank.Tree V) :
    (substitute f T).leaves + 2 * T.cost (fun v => if raw v then 1 else 0) ≤ 3*T.leaves := by
  induction T with
  | raw v => simpa [FlagCrossRank.Tree.leaves,FlagCrossRank.Tree.cost,substitute] using size v
  | gate op a b ha hb => simp only [substitute,FlagCrossRank.Tree.leaves,FlagCrossRank.Tree.cost]; omega

theorem paidFormulaLower {V W : Type} (T : FlagCrossRank.Tree V) (raw : V → Bool) (f : V → FlagCrossRank.Tree W)
    (size : ∀ v, (f v).leaves + 2 * (if raw v then 1 else 0) ≤ 3)
    (rawLeaves : 105 ≤ T.cost (fun v => if raw v then 1 else 0))
    (expanded : 126 ≤ (substitute f T).leaves) : 112 ≤ T.leaves := by
  have := expansion raw f size T
  omega

abbrev Vertex := Fin 21 ⊕ Fin 21
abbrev Formula := FlagCrossRank.Tree (Fin 56)

def incident (p l : Fin 21) : Bool :=
  [0,5,7,17,20].contains ((l.val+21-p.val)%21)

def inputTree (v : Fin 56) : FlagCrossRank.Tree Vertex :=
  if v.val < 21 then .raw (.inl (Fin.ofNat 21 v.val))
  else if v.val < 42 then .raw (.inr (Fin.ofNat 21 (v.val-21)))
  else
    let i := (v.val-42)%7
    let line (d : ℕ) : FlagCrossRank.Tree Vertex := .raw (.inr (Fin.ofNat 21 (3*i+d)))
    let pair := FlagCrossRank.Tree.gate true (line 5) (line 17)
    if v.val < 49 then pair else .gate true pair (line 20)

def values (x : Vertex → Bool) (v : Fin 56) := (inputTree v).val x
def isRaw (v : Fin 56) := decide (v.val < 42)
def hasFlag (x : Vertex → Bool) := ∃ p l, incident p l = true ∧ x (.inl p) = true ∧ x (.inr l) = true
def computes (T : Formula) := ∀ x, T.val (values x) = true ↔ hasFlag x

def retainedPoint (e : Fin 84) : Fin 21 :=
  let slot := e.val%12
  Fin.ofNat 21 (3*(e.val/12) + if slot < 2 then 0 else if slot < 7 then 1 else 2)

def retainedLine (e : Fin 84) : Fin 21 :=
  let slot := e.val%12
  let d := if slot < 2 then 7*slot else #[0,5,7,17,20][(slot-2)%5]!
  Fin.ofNat 21 ((retainedPoint e).val+d)

def left (e : Fin 84) : Fin 56 := Fin.ofNat 56 (retainedPoint e).val
def right (e : Fin 84) : Fin 56 := Fin.ofNat 56 (21+(retainedLine e).val)
def rowBits (e : Fin 84) := edgeBits (retainedPoint e, retainedLine e)
def negBits (e : Fin 84) : Vertex → Bool
  | .inl a => let l := retainedLine e
              decide (a ≠ retainedPoint e) && incident a l &&
                decide (l.val%3 ≠ 2 ∨ a.val%3 ≠ 0)
  | .inr b => let l := retainedLine e
              decide (b ≠ l) && (incident (retainedPoint e) b ||
                decide (l.val%3 = 2 ∧ b.val%3 = 2))

def matched (p : Fin 21) : Fin 84 :=
  Fin.ofNat 84 (12*(p.val/3) + if p.val%3 = 0 then 0 else if p.val%3 = 1 then 2 else 7)

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem matchVal : ∀ p, (left (matched p)).val%21 = p.val ∧
    (right (matched p)).val%21 = p.val := by decide +kernel

theorem matchedCover (K : Finset (Fin 56)) (h : ∀ e, left e ∈ K ∨ right e ∈ K) :
    21 ≤ K.card := by
  let chosen (p : Fin 21) : K := if yes : left (matched p) ∈ K then ⟨_,yes⟩
    else ⟨_,(h (matched p)).resolve_left yes⟩
  have read (p : Fin 21) : (chosen p).val.val%21 = p.val := by
    dsimp [chosen]; split
    · exact (matchVal p).1
    · exact (matchVal p).2
  have inj : Function.Injective chosen := by
    intro a b eq; apply Fin.ext
    rw [←read a,←read b,eq]
  simpa using Fintype.card_le_of_injective chosen inj

private theorem endpoints : ∀ e, isRaw (left e) = true ∧ isRaw (right e) = true ∧
    left e ≠ right e := by decide +kernel

private theorem incidentRows : ∀ e, incident (retainedPoint e) (retainedLine e) = true := by
  decide +kernel

private theorem negativeRows : ∀ e, ¬ hasFlag (negBits e) := by
  unfold hasFlag; decide +kernel

private theorem diagonal : ∀ e w, values (rowBits e) w = true → values (negBits e) w = false →
    w = left e ∨ w = right e := by decide +kernel

private theorem offPoint : ∀ a b, a ≠ b → retainedPoint a = retainedPoint b →
    ∀ w, values (rowBits a) w = true → values (negBits b) w = false → w = left a := by
  decide +kernel

private theorem offLine : ∀ a b, a ≠ b → retainedLine a = retainedLine b →
    ∀ w, values (rowBits a) w = true → values (negBits b) w = false → w = right a := by
  decide +kernel

private theorem peer : ∀ a, (∃ b, a ≠ b ∧ left a = left b) ∧
    (∃ b, a ≠ b ∧ right a = right b) := by decide +kernel

private theorem leftEq : ∀ a b, left a = left b → retainedPoint a = retainedPoint b := by
  decide +kernel
private theorem rightEq : ∀ a b, right a = right b → retainedLine a = retainedLine b := by
  decide +kernel
private theorem disjoint : ∀ a b, left a ≠ right b := by decide +kernel

theorem actualRaw (T : Formula) (correct : computes T) :
    105 ≤ T.cost (fun v => if isRaw v then 1 else 0) := by
  apply rawRank T isRaw left right (fun e => values (rowBits e)) (fun e => values (negBits e))
    ?_ ?_ (fun e => ⟨(endpoints e).1,(endpoints e).2.1⟩) (fun e => (endpoints e).2.2)
    diagonal ?_ ?_ 21 matchedCover
  · intro e; apply (correct _).2
    exact ⟨_,_,incidentRows e,by simp [rowBits,edgeBits],by simp [rowBits,edgeBits]⟩
  · intro e; cases h : T.val (values (negBits e)) with
    | false => rfl
    | true => exact ((negativeRows e) ((correct _).1 h)).elim
  · intro a b v w ne av bv hx hy
    rcases av with rfl | rfl <;> rcases bv with eq | eq
    · exact offPoint a b ne (leftEq _ _ eq) w hx hy
    · exact (disjoint a b eq).elim
    · exact (disjoint b a eq.symm).elim
    · exact offLine a b ne (rightEq _ _ eq) w hx hy
  · rintro e v (rfl | rfl)
    · obtain ⟨b,ne,eq⟩ := (peer e).1; exact ⟨b,ne,Or.inl eq⟩
    · obtain ⟨b,ne,eq⟩ := (peer e).2; exact ⟨b,ne,Or.inr eq⟩

private theorem degree : ∀ l, (Finset.univ.filter (fun p => incident p l = true)).card = 5 := by
  decide +kernel
private def common (p a : Fin 21) : Fin 21 :=
  ((List.finRange 21).find? (fun l => incident p l && incident a l)).getD 0
private theorem commonSpec : ∀ p a, p ≠ a →
    (incident p (common p a) = true ∧ incident a (common p a) = true) ∧
    ∀ l, (incident p l = true ∧ incident a l = true) → l = common p a := by decide +kernel
private theorem uniqueLine : ∀ p a, p ≠ a → ∃! l, incident p l = true ∧ incident a l = true := by
  intro p a ne
  exact ⟨common p a,(commonSpec p a ne).1,(commonSpec p a ne).2⟩

theorem actualExpanded (T : Formula) (correct : computes T) : 126 ≤ (substitute inputTree T).leaves := by
  apply planeCrossOnly 4 21 (fun p l => incident p l = true) rfl (by decide) degree uniqueLine
  · intro e; rw [substitute_eval]; apply (correct _).2
    exact ⟨e.val.1,e.val.2,e.property,by simp [edgeBits],by simp [edgeBits]⟩
  · intro e; rw [substitute_eval]
    let x := crossBits (fun p l => incident p l = true) e.val
    change T.val (values x) = false
    cases h : T.val (values x) with
    | false => rfl
    | true =>
      obtain ⟨a,b,ab,ha,hb⟩ := (correct x).mp h
      simp only [x,crossBits,decide_eq_true_eq] at ha hb
      exact (crossNegative _ (planeSquareFree _ uniqueLine) e.property ha hb ab).elim

private theorem inputSize : ∀ v, (inputTree v).leaves + 2 * (if isRaw v then 1 else 0) ≤ 3 := by
  decide +kernel

theorem orderFourFormulaLower (T : Formula) (correct : computes T) : 112 ≤ T.leaves :=
  paidFormulaLower T isRaw inputTree inputSize (actualRaw T correct) (actualExpanded T correct)

end OrderFourAlarmRank
