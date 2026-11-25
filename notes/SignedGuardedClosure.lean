import SignedTerminalCuts

namespace PrismSignedFrontier

-- A successor can be discharged immediately by a certified lower bound.
-- Only the remaining representatives need to carry an explicit wire list.
def guardedClosed (g : W) (negative : List ℕ) (words : ℕ → ℕ → List W) (count : ℕ → ℕ)
    (lookup : ℕ → List W → ℕ × ℕ) (sym : ℕ → List Switch) (guard : ℕ → List W → Bool) : ℕ → ℕ → Bool
  | 0, i => !(words 0 i).contains g
  | k+1, i =>
    let s := words (k+1) i
    !s.contains g && !(moves s fun t =>
      t.contains g || (decide (0 < k) && decide (t.length ≤ k+1) && covered g negative t &&
        !(guard k t || found words count lookup sym k t)))

theorem guardedClosed_excludes (g : W) (hg : g ≠ 0) (negative : List ℕ)
    (neg : ∀ r ∈ negative, r < 64 ∧ g.getLsbD r = false)
    (words : ℕ → ℕ → List W) (count : ℕ → ℕ) (lookup : ℕ → List W → ℕ × ℕ)
    (sym : ℕ → List Switch) (valid : ∀ j, ∀ op ∈ sym j, op.Valid)
    (fix : ∀ j, reindex (sym j) g = g) (guard : ℕ → List W → Bool)
    (safe : ∀ k t d, d ≤ k → Cone g d t.toFinset → guard k t = false) (cap : ℕ)
    (nd : ∀ k ≤ cap, ∀ i < count k, (words k i).Nodup)
    (checks : ∀ k ≤ cap, ∀ i < count k, guardedClosed g negative words count lookup sym guard k i = true) :
    ∀ k ≤ cap, ∀ i < count k, ∀ d ≤ k, ¬ Cone g d (words k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro hk i hi d hd run
    have de : d = 0 := by omega
    subst d
    have terminal {t : Finset W} (p : Cone g 0 t) : g ∈ t := by cases p; simp
    have mem := List.mem_toFinset.mp (terminal run)
    simpa [guardedClosed,mem] using checks 0 hk i hi
  | succ k ih =>
    intro hk i hi d hd run
    obtain ⟨absent,reject⟩ := Bool.and_eq_true_iff.mp (checks (k+1) hk i hi)
    cases d with
    | zero =>
      have terminal {t : Finset W} (p : Cone g 0 t) : g ∈ t := by cases p; simp
      have mem := List.mem_toFinset.mp (terminal run)
      simp [mem] at absent
    | succ d =>
      let test := fun t : List W => t.contains g || (decide (0 < k) && decide (t.length ≤ k+1) &&
        covered g negative t && !(guard k t || found words count lookup sym k t))
      have next := moves_complete (words (k+1) i) test hg (nd _ hk _ hi) run rfl (fun t uniq ht => by
        dsimp only [test]
        by_cases mem : g ∈ t
        · simp [mem]
        have positive : 0 < k := by
          by_contra! fail
          have dz : d = 0 := by omega
          subst d
          have terminal {u : Finset W} (p : Cone g 0 u) : g ∈ u := by cases p; simp
          exact mem (List.mem_toFinset.mp (terminal ht))
        have size := ht.size
        rw [List.toFinset_card_of_nodup uniq] at size
        have no : found words count lookup sym k t = false := by
          by_contra! yes
          have hfound : found words count lookup sym k t = true := by simpa using yes
          obtain ⟨inside,perm⟩ := Bool.and_eq_true_iff.mp hfound
          have hree := ht.reindex (sym (lookup k t).2) (valid _)
          rw [fix] at hree
          have eq : (t.map (reindex (sym (lookup k t).2))).toFinset = (words k (lookup k t).1).toFinset := by
            ext v
            simp only [List.mem_toFinset]
            exact (List.isPerm_iff.mp perm).mem_iff
          have into : t.toFinset.image (reindex (sym (lookup k t).2)) = (words k (lookup k t).1).toFinset := by
            rw [← eq]
            ext v
            simp
          rw [into] at hree
          exact ih (by omega) _ (of_decide_eq_true inside) d (by omega) hree
        simp [positive,show t.length ≤ k+1 by omega,ht.covered negative neg,no,safe k t d (by omega) ht])
      change (!moves (words (k+1) i) test) = true at reject
      simp [next] at reject


-- The lookup chooses a symmetry and a certificate. Both are checked against the
-- actual successor, so an incorrect hint cannot certify a feasible circuit.
def successorCut (g : W) (cert : Nat → CutCertificate g)
    (sym : Nat → List Switch) (hint : Nat → List W → Nat × Nat)
    (k : Nat) (s : List W) : Bool :=
  let (c,j) := hint k s
  let v := cert c
  maskedCut v.mask v.patterns v.bound k (s.map (reindex (sym j)))

theorem successorCut_sound (g : W) (cert : Nat → CutCertificate g)
    (sym : Nat → List Switch) (valid : ∀ j, ∀ op ∈ sym j, op.Valid)
    (fix : ∀ j, reindex (sym j) g = g) (hint : Nat → List W → Nat × Nat)
    (k : Nat) (s : List W) (d : Nat) (small : d ≤ k) (h : Cone g d s.toFinset) :
    successorCut g cert sym hint k s = false := by
  let j := (hint k s).2
  have run := h.reindex (sym j) (valid j)
  rw [fix] at run
  have eq : (s.map (reindex (sym j))).toFinset = s.toFinset.image (reindex (sym j)) := by
    ext w
    simp
  exact (cert (hint k s).1).sound k _ small (eq.symm ▸ run)

end PrismSignedFrontier
