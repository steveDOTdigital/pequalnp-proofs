import PrismSignedFrontier

namespace PrismSignedFrontier

theorem zero_inter (x : W) : (0 : W) &&& x = 0 := BitVec.zero_and

theorem survivors_zero (r : ℕ) (s : List W) : survivors r s 0 = 0 := by
  cases s <;> simp [survivors]

theorem survivors_inter (r : ℕ) (s : List W) (u v : W) :
    survivors r s (u &&& v) = survivors r s u &&& v := by
  induction s generalizing u with
  | nil => rfl
  | cons a tail ih =>
    by_cases hu : u = 0
    · subst u
      rw [zero_inter, survivors_zero, zero_inter]
    · by_cases hv : u &&& v = 0
      · rw [hv, survivors_zero, survivors, if_neg hu]
        rw [← ih]
        rw [BitVec.and_assoc, BitVec.and_comm (rowMask r a), ← BitVec.and_assoc, hv]
        rw [zero_inter, survivors_zero]
      · rw [survivors, if_neg hv, survivors, if_neg hu, ← ih]
        rw [BitVec.and_assoc, BitVec.and_comm v, ← BitVec.and_assoc]

-- Screen the four candidate outputs together. Once the retained inputs agree
-- with a negative row, only the candidate output itself can separate the row.
def screen (g : W) (base : List W) : List ℕ → List W → List W
  | [], candidates => candidates
  | r :: rows, candidates =>
    if candidates.isEmpty then [] else
    let mask := survivors r base g
    if mask = 0 then screen g base rows candidates else
      screen g base rows (candidates.filter fun w => (mask &&& rowMask r w) == 0)

theorem screen_keeps {g w : W} (hg : g ≠ 0) (base : List W) (rows : List ℕ)
    (candidates : List W) (hw : w ∈ candidates) (ok : covered g rows (w :: base) = true) :
    w ∈ screen g base rows candidates := by
  induction rows generalizing candidates with
  | nil => exact hw
  | cons r rows ih =>
    have clear := List.all_eq_true.mp ok r List.mem_cons_self
    have tail : covered g rows (w :: base) = true := by
      apply List.all_eq_true.mpr
      intro i hi
      exact List.all_eq_true.mp ok i (List.mem_cons_of_mem _ hi)
    have hm : survivors r base g &&& rowMask r w = 0 := by
      have h := beq_iff_eq.mp clear
      simpa only [survivors, if_neg hg, survivors_inter] using h
    unfold screen
    have hn : candidates.isEmpty = false := by
      cases candidates <;> simp_all
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    split
    · exact ih _ hw tail
    · exact ih _ (List.mem_filter.mpr ⟨hw,beq_iff_eq.mpr hm⟩) tail

def fastBranch (g : W) (rows : List ℕ) (locate : List W → Bool)
    (k : ℕ) (candidates base : List W) : Bool :=
  decide (0 < k) && decide (base.length ≤ k) &&
    (screen g base rows candidates).any fun w => !locate (w :: base)

def fastPair (g : W) (rows : List ℕ) (locate : List W → Bool)
    (k : ℕ) (s : List W) (a b : W) : Bool :=
  let choices' := choices a b
  choices'.contains g ||
    let rest := s.filter fun u => u != a && u != b
    let fresh := choices'.filter fun w => w != 0 && !s.contains w
    fastBranch g rows locate k fresh rest ||
    fastBranch g rows locate k fresh (a :: rest) ||
    fastBranch g rows locate k fresh (b :: rest) ||
    fastBranch g rows locate k fresh (a :: b :: rest)

def fastClosed (g : W) (rows : List ℕ) (words : ℕ → ℕ → List W)
    (count : ℕ → ℕ) (lookup : ℕ → List W → ℕ × ℕ) (sym : ℕ → List Switch) :
    ℕ → ℕ → Bool
  | 0, i => !(words 0 i).contains g
  | k+1, i =>
    let s := words (k+1) i
    let locate := found words count lookup sym k
    !s.contains g && !(s.any fun a => s.any fun b =>
      decide (a.toNat < b.toNat) && fastPair g rows locate k s a b)

theorem branch_of {g w : W} (hg : g ≠ 0) (rows : List ℕ) (locate : List W → Bool)
    (k : ℕ) (fresh base : List W) (hw : w ∈ fresh)
    (hk : 0 < k) (len : (w :: base).length ≤ k+1)
    (cov : covered g rows (w :: base) = true) (miss : locate (w :: base) = false) :
    fastBranch g rows locate k fresh base = true := by
  have p : base.length ≤ k := by simpa only [List.length_cons, Nat.add_le_add_iff_right] using len
  simp only [fastBranch, hk, p, decide_true, Bool.true_and]
  exact List.any_eq_true.mpr ⟨w, screen_keeps hg base rows fresh hw cov, by simp [miss]⟩

theorem fastPair_of {g : W} (hg : g ≠ 0) (rows : List ℕ) (locate : List W → Bool)
    (k : ℕ) (s : List W) (a b : W) (ha : a ∈ s) (hb : b ∈ s) (absent : g ∉ s)
    (h : onePair s (fun t => t.contains g || (decide (0 < k) && decide (t.length ≤ k+1) &&
      covered g rows t && !locate t)) a b = true) :
    fastPair g rows locate k s a b = true := by
  obtain ⟨w,form,test⟩ := List.any_eq_true.mp h
  obtain ⟨fresh,keeps⟩ := Bool.and_eq_true_iff.mp test
  obtain ⟨ka,_,rest⟩ := List.any_eq_true.mp keeps
  obtain ⟨kb,_,ok⟩ := List.any_eq_true.mp rest
  let base := s.filter fun u => u != a && u != b
  have wf : w ∈ (choices a b).filter (fun z => z != 0 && !s.contains z) :=
    List.mem_filter.mpr ⟨form,fresh⟩
  by_cases hit : g ∈ choices a b
  · simp [fastPair,hit]
  · have nw : w ≠ g := fun eq => hit (eq ▸ form)
    have na : g ≠ a := fun e => absent (e ▸ ha)
    have nb : g ≠ b := fun e => absent (e ▸ hb)
    have ng : g ∉ base := by
      intro h
      exact absent (List.mem_filter.mp h).1
    have stop : (after s a b w ka kb).contains g = false := by
      cases ka <;> cases kb <;>
        simp [after,withWire,List.contains_eq_mem,Ne.symm nw,na,nb,absent]
    dsimp only at ok
    rw [stop, Bool.false_or] at ok
    obtain ⟨left,miss⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨dims,cov⟩ := Bool.and_eq_true_iff.mp left
    obtain ⟨positive,len⟩ := Bool.and_eq_true_iff.mp dims
    have hk := of_decide_eq_true positive
    have hl := of_decide_eq_true len
    have hm : locate (after s a b w ka kb) = false := by simpa using miss
    have spec := branch_of hg rows locate k _ _ wf hk hl cov hm
    cases ka <;> cases kb <;>
      simp [after,withWire] at spec <;> simp [fastPair, hit, spec]

theorem fastClosed_sound (g : W) (hg : g ≠ 0) (rows : List ℕ) (words : ℕ → ℕ → List W)
    (count : ℕ → ℕ) (lookup : ℕ → List W → ℕ × ℕ) (sym : ℕ → List Switch)
    (k i : ℕ) (ok : fastClosed g rows words count lookup sym k i = true) :
    closed g rows words count lookup sym k i = true := by
  cases k with
  | zero => exact ok
  | succ k =>
    obtain ⟨absent,fast⟩ := Bool.and_eq_true_iff.mp ok
    apply Bool.and_eq_true_iff.mpr
    refine ⟨absent,?_⟩
    have ng : g ∉ words (k+1) i := by simpa [List.contains_eq_mem] using absent
    by_contra! fail
    have h : moves (words (k+1) i) (fun t => t.contains g || (decide (0 < k) &&
        decide (t.length ≤ k+1) && covered g rows t &&
        !found words count lookup sym k t)) = true := by simpa using fail
    obtain ⟨a,ha,inside⟩ := List.any_eq_true.mp h
    obtain ⟨b,hb,both⟩ := List.any_eq_true.mp inside
    obtain ⟨lt,slow⟩ := Bool.and_eq_true_iff.mp both
    have fp := fastPair_of hg rows (found words count lookup sym k) k _ a b ha hb ng slow
    have yes : ((words (k+1) i).any fun a => (words (k+1) i).any fun b =>
        decide (a.toNat < b.toNat) && fastPair g rows (found words count lookup sym k) k
          (words (k+1) i) a b) = true :=
      List.any_eq_true.mpr ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,Bool.and_eq_true_iff.mpr ⟨lt,fp⟩⟩⟩
    simp [yes] at fast

def guidedClosed (g : W) (choose : ℕ → ℕ → List W → W → W → List ℕ)
    (words : ℕ → ℕ → List W) (count : ℕ → ℕ) (lookup : ℕ → List W → ℕ × ℕ)
    (sym : ℕ → List Switch) : ℕ → ℕ → Bool
  | 0, i => !(words 0 i).contains g
  | k+1, i =>
    let s := words (k+1) i
    !s.contains g && !(s.any fun a => s.any fun b => decide (a.toNat < b.toNat) &&
      fastPair g (choose (k+1) i s a b) (found words count lookup sym k) k s a b)

theorem onePair_mono (s : List W) {f h : List W → Bool}
    (mono : ∀ t, f t = true → h t = true) (a b : W)
    (good : onePair s f a b = true) : onePair s h a b = true := by
  obtain ⟨w,form,t⟩ := List.any_eq_true.mp good
  obtain ⟨fresh,tests⟩ := Bool.and_eq_true_iff.mp t
  obtain ⟨ka,hka,rest⟩ := List.any_eq_true.mp tests
  obtain ⟨kb,hkb,ok⟩ := List.any_eq_true.mp rest
  exact List.any_eq_true.mpr ⟨w,form,Bool.and_eq_true_iff.mpr ⟨fresh,
    List.any_eq_true.mpr ⟨ka,hka,List.any_eq_true.mpr ⟨kb,hkb,mono _ ok⟩⟩⟩⟩

theorem guidedClosed_sound (g : W) (hg : g ≠ 0) (rows : List ℕ)
    (choose : ℕ → ℕ → List W → W → W → List ℕ)
    (subset : ∀ k i s a b r, r ∈ choose k i s a b → r ∈ rows)
    (words : ℕ → ℕ → List W) (count : ℕ → ℕ) (lookup : ℕ → List W → ℕ × ℕ)
    (sym : ℕ → List Switch) (k i : ℕ) (ok : guidedClosed g choose words count lookup sym k i = true) :
    closed g rows words count lookup sym k i = true := by
  cases k with
  | zero => exact ok
  | succ k =>
    obtain ⟨absent,guided⟩ := Bool.and_eq_true_iff.mp ok
    apply Bool.and_eq_true_iff.mpr
    refine ⟨absent,?_⟩
    have ng : g ∉ words (k+1) i := by simpa [List.contains_eq_mem] using absent
    by_contra! fail
    let s := words (k+1) i
    let locate := found words count lookup sym k
    let test := fun rs : List ℕ => fun t : List W => t.contains g ||
      (decide (0 < k) && decide (t.length ≤ k+1) && covered g rs t && !locate t)
    have h : moves s (test rows) = true := by simpa [s,locate,test] using fail
    obtain ⟨a,ha,inside⟩ := List.any_eq_true.mp h
    obtain ⟨b,hb,both⟩ := List.any_eq_true.mp inside
    obtain ⟨lt,slow⟩ := Bool.and_eq_true_iff.mp both
    let short := choose (k+1) i s a b
    have mono : ∀ t, test rows t = true → test short t = true := by
      intro t ht
      obtain hit | all := Bool.or_eq_true_iff.mp ht
      · exact Bool.or_eq_true_iff.mpr (Or.inl hit)
      · obtain ⟨left,miss⟩ := Bool.and_eq_true_iff.mp all
        obtain ⟨dims,cov⟩ := Bool.and_eq_true_iff.mp left
        have cov' : covered g short t = true := List.all_eq_true.mpr (fun r hr =>
          List.all_eq_true.mp cov r (subset _ _ _ _ _ _ hr))
        exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.and_eq_true_iff.mpr
          ⟨Bool.and_eq_true_iff.mpr ⟨dims,cov'⟩,miss⟩))
    have converted := onePair_mono s mono a b slow
    have fp := fastPair_of hg short locate k s a b ha hb ng converted
    have yes : (s.any fun a => s.any fun b => decide (a.toNat < b.toNat) &&
        fastPair g (choose (k+1) i s a b) locate k s a b) = true :=
      List.any_eq_true.mpr ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,Bool.and_eq_true_iff.mpr ⟨lt,fp⟩⟩⟩
    change (!(s.any fun a => s.any fun b => decide (a.toNat < b.toNat) &&
      fastPair g (choose (k+1) i s a b) locate k s a b)) = true at guided
    rw [yes] at guided
    contradiction

end PrismSignedFrontier
