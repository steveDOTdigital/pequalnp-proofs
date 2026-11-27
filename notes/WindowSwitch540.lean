import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic

namespace WindowSwitch540

theorem traceShape {X : Type} {m : Nat}
    (edge : Fin m → X × X) (row : Fin m → Nat) (enabled : Fin m → Prop)
    (separated : ∀ a b, (edge a).1 ≠ (edge b).2)
    (p : Nat → X) (n : Nat)
    (steps : ∀ i < n, p (i + 1) = p i ∨
      ∃ j, enabled j ∧ row j = i ∧ p i = (edge j).1 ∧ p (i + 1) = (edge j).2) :
    (∀ i ≤ n, p i = p 0) ∨
      ∃ j, enabled j ∧ row j < n ∧ p 0 = (edge j).1 ∧
        ∀ i ≤ n, p i = if i ≤ row j then (edge j).1 else (edge j).2 := by
  induction n with
  | zero =>
    left
    intro i hi
    obtain rfl : i = 0 := by omega
    rfl
  | succ n ih =>
    have pref := ih (fun i hi => steps i (by omega))
    rcases steps n (by omega) with equal | ⟨j, hj, hr, hs, ht⟩
    · rcases pref with h | ⟨k, hk, hkr, hks, he⟩
      · left
        intro i hi
        by_cases hp : i ≤ n
        · exact h i hp
        · obtain rfl : i = n + 1 := by omega
          exact equal.trans (h n (by omega))
      · right
        refine ⟨k, hk, by omega, hks, ?_⟩
        intro i hi
        by_cases hp : i ≤ n
        · exact he i hp
        · obtain rfl : i = n + 1 := by omega
          rw [equal, he n (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    · rcases pref with h | ⟨k, hk, hkr, hks, he⟩
      · right
        refine ⟨j, hj, by omega, (h n (by omega)).symm.trans hs, ?_⟩
        intro i hi
        by_cases hp : i ≤ n
        · rw [ite_eq_left (by omega)]
          exact (h i hp).trans ((h n (by omega)).symm.trans hs)
        · obtain rfl : i = n + 1 := by omega
          rw [ite_eq_right (by omega)]
          exact ht
      · have atEnd : p n = (edge k).2 := by
          rw [he n (by omega), ite_eq_right (by omega)]
        exact (separated j k (hs.symm.trans atEnd)).elim

theorem canonicalSteps {X : Type} {m n : Nat} (edge : Fin m → X × X)
    (row : Fin m → Nat) (enabled : Fin m → Prop)
    (j : Fin m) (hj : enabled j) (hr : row j < n) :
    let p := fun i : Nat => if i ≤ row j then (edge j).1 else (edge j).2
    p 0 = (edge j).1 ∧ p n = (edge j).2 ∧
      (∀ i < n, p (i + 1) = p i ∨
        ∃ k, enabled k ∧ row k = i ∧ p i = (edge k).1 ∧ p (i + 1) = (edge k).2) := by
  dsimp
  refine ⟨rfl, by rw [ite_eq_right (by omega)], ?_⟩
  intro i _
  by_cases eq : i = row j
  · right
    refine ⟨j, hj, eq.symm, ite_eq_left (by omega), ite_eq_right (by omega)⟩
  · left
    by_cases before : i < row j
    · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]


theorem traceUniqueOn {X : Type} {m n : Nat} (edge : Fin m → X × X)
    (row : Fin m → Nat) (enabled : Fin m → Prop)
    (injectiveEdge : ∀ {j k}, edge j = edge k → j = k)
    (separated : ∀ j k, (edge j).1 ≠ (edge k).2)
    (p q : Nat → X) (head : p 0 = q 0) (tail : p n = q n)
    (hp : ∀ i < n, p (i + 1) = p i ∨
      ∃ j, enabled j ∧ row j = i ∧ p i = (edge j).1 ∧ p (i + 1) = (edge j).2)
    (hq : ∀ i < n, q (i + 1) = q i ∨
      ∃ j, enabled j ∧ row j = i ∧ q i = (edge j).1 ∧ q (i + 1) = (edge j).2) :
    ∀ i ≤ n, p i = q i := by
  rcases traceShape edge row enabled separated p n hp with pc | ⟨j, hj, jr, jp, pj⟩ <;>
    rcases traceShape edge row enabled separated q n hq with qc | ⟨k, hk, kr, kq, qk⟩
  · intro i hi
    rw [pc i hi, qc i hi, head]
  · have endpoint : q n = (edge k).2 := by rw [qk n (by omega), ite_eq_right (by omega)]
    exact (separated k k (kq.symm.trans (head.symm.trans ((pc n (by omega)).symm.trans (tail.trans endpoint))))).elim
  · have endpoint : p n = (edge j).2 := by rw [pj n (by omega), ite_eq_right (by omega)]
    exact (separated j j (jp.symm.trans (head.trans ((qc n (by omega)).symm.trans (tail.symm.trans endpoint))))).elim
  · have pEnd : p n = (edge j).2 := by rw [pj n (by omega), ite_eq_right (by omega)]
    have qEnd : q n = (edge k).2 := by rw [qk n (by omega), ite_eq_right (by omega)]
    have pair : edge j = edge k :=
      Prod.ext (jp.symm.trans (head.trans kq)) (pEnd.symm.trans (tail.trans qEnd))
    obtain rfl := injectiveEdge pair
    intro i hi
    rw [pj i hi, qk i hi]


theorem overlapIter (s : Nat → Nat → Bool) (L w : Nat)
    (overlap : ∀ i < L, ∀ j, j + 1 < w → s (i + 1) j = s i (j + 1))
    (i k j : Nat) (ht : i + k ≤ L) (hw : j + k < w) :
    s (i + k) j = s i (j + k) := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    calc
      s (i + (k + 1)) j = s (i + k + 1) j := by rfl
      _ = s (i + k) (j + 1) := overlap (i + k) (by omega) j (by omega)
      _ = s i (j + 1 + k) := ih (j + 1) (by omega) (by omega)
      _ = s i (j + (k + 1)) := by congr 1; omega

def encode (s : Nat → Nat → Bool) (L t : Nat) : Bool :=
  s (min L t) (t - min L t)

theorem encodeWindows (s : Nat → Nat → Bool) (L w : Nat)
    (overlap : ∀ i < L, ∀ j, j + 1 < w → s (i + 1) j = s i (j + 1))
    (i j : Nat) (hi : i ≤ L) (hj : j < w) : encode s L (i + j) = s i j := by
  let a := min L (i + j)
  change s a (i + j - a) = s i j
  have ha : i ≤ a := by
    dsimp [a]
    exact Nat.le_min.mpr ⟨hi, by omega⟩
  have haL : a ≤ L := Nat.min_le_left _ _
  have haj : a ≤ i + j := Nat.min_le_right _ _
  simpa only [show i + (a - i) = a by omega, show i + j - a + (a - i) = j by omega] using
    (overlapIter s L w overlap i (a - i) (i + j - a) (by omega) (by omega))

theorem windowsDetermine (u v : Nat → Bool) (L w : Nat) (pos : 0 < w)
    (agree : ∀ i ≤ L, ∀ j < w, u (i+j) = v (i+j)) :
    ∀ t < L+w, u t = v t := by
  intro t ht
  let i := min L t
  have hi : i ≤ L := Nat.min_le_left _ _
  have hit : i ≤ t := Nat.min_le_right _ _
  have hj : t - i < w := by
    dsimp [i]
    by_cases h : L ≤ t
    · rw [Nat.min_eq_left h]
      omega
    · rw [Nat.min_eq_right (by omega)]
      omega
  simpa only [show i + (t - i) = t by omega] using agree i hi (t-i) hj


def traceAt {X : Type} {n : Nat} (p : Fin (n+1) → X) (i : Nat) : X :=
  if hi : i ≤ n then p ⟨i, by omega⟩ else p 0

def ValidTrace {X : Type} {m n : Nat} (edge : Fin m → X × X) (row : Fin m → Nat)
    (enabled : Fin m → Prop) (x y : X) (p : Fin (n+1) → X) : Prop :=
  traceAt p 0 = x ∧ traceAt p n = y ∧
    ∀ i < n, traceAt p (i+1) = traceAt p i ∨
      ∃ j, enabled j ∧ row j = i ∧ traceAt p i = (edge j).1 ∧ traceAt p (i+1) = (edge j).2

theorem exactTraceCount {X : Type} [DecidableEq X] {m n : Nat}
    (edge : Fin m → X × X) (row : Fin m → Nat) (enabled : Fin m → Prop)
    (rowInRange : ∀ j, row j < n)
    (injectiveEdge : Function.Injective edge)
    (separated : ∀ j k, (edge j).1 ≠ (edge k).2) (x y : X)
    (traces : Finset (Fin (n+1) → X))
    (mem : ∀ p, p ∈ traces ↔ ValidTrace edge row enabled x y p)
    [Decidable (∃ j, enabled j ∧ edge j = (x,y))] :
    traces.card =
      (if x = y then 1 else 0) + (if ∃ j, enabled j ∧ edge j = (x,y) then 1 else 0) := by
  classical
  have unique (p q : Fin (n+1) → X) (hp : p ∈ traces) (hq : q ∈ traces) : p = q := by
    rcases (mem p).mp hp with ⟨ph,pt,ps⟩
    rcases (mem q).mp hq with ⟨qh,qt,qs⟩
    have he := traceUniqueOn edge row enabled (fun {j k} eq => injectiveEdge eq) separated
      (traceAt p) (traceAt q) (ph.trans qh.symm) (pt.trans qt.symm) ps qs
    funext i
    simpa [traceAt, show i.val ≤ n by omega] using he i.val (by omega)
  have cardOne (p : Fin (n+1) → X) (hp : p ∈ traces) : traces.card = 1 := by
    apply Finset.card_eq_one.mpr
    refine ⟨p, ?_⟩
    ext q
    simp only [Finset.mem_singleton]
    exact ⟨fun hq => unique q p hq hp, fun h => h.symm ▸ hp⟩
  by_cases same : x = y
  · subst y
    have hn : ¬∃ j, enabled j ∧ edge j = (x,x) := by
      rintro ⟨j,_,hj⟩
      exact separated j j (congrArg Prod.fst hj |>.trans (congrArg Prod.snd hj).symm)
    rw [ite_eq_left rfl, ite_eq_right hn]
    change traces.card = 1
    apply cardOne (fun _ => x)
    apply (mem _).mpr
    refine ⟨?_, ?_, ?_⟩
    · simp [traceAt]
    · simp [traceAt]
    · intro i _
      left
      simp [traceAt]
  · rw [ite_eq_right same]
    simp only [Nat.zero_add]
    by_cases jump : ∃ j, enabled j ∧ edge j = (x,y)
    · rw [ite_eq_left jump]
      obtain ⟨j,hj,ej⟩ := jump
      let p : Fin (n+1) → X := fun i => if i.val ≤ row j then (edge j).1 else (edge j).2
      have ev {i : Nat} (hi : i ≤ n) :
          traceAt p i = if i ≤ row j then (edge j).1 else (edge j).2 := by simp [traceAt,hi,p]
      obtain ⟨start,finish,step⟩ := canonicalSteps edge row enabled j hj (rowInRange j)
      apply cardOne p
      apply (mem _).mpr
      refine ⟨?_, ?_, ?_⟩
      · exact (ev (by omega)).trans (start.trans (congrArg Prod.fst ej))
      · exact (ev (by omega)).trans (finish.trans (congrArg Prod.snd ej))
      · intro i hi
        simp only [ev (show i+1 ≤ n by omega), ev (show i ≤ n by omega)]
        exact step i hi
    · rw [ite_eq_right jump]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨a,b,c⟩ := (mem p).mp hp
      rcases traceShape edge row enabled separated (traceAt p) n c with flat | ⟨j,hj,rj,start,shape⟩
      · exact same (a.symm.trans ((flat n (by omega)).symm.trans b))
      · apply jump
        have finish : traceAt p n = (edge j).2 := by rw [shape n (by omega), ite_eq_right (by omega)]
        exact ⟨j,hj,Prod.ext (start.symm.trans a) (finish.symm.trans b)⟩


theorem shortMultiplicity (D w L m : Nat) (h : L < 10 * w) (eq : 2*m = D*w) :
    D * min L D ≤ 20*m := by
  calc
    D * min L D ≤ D * (10*w) := Nat.mul_le_mul_left _ (Nat.le_trans (Nat.min_le_left _ _) (by omega))
    _ = 10*(D*w) := by ac_rfl
    _ = 20*m := by omega

theorem longMultiplicity (D w L t rows m : Nat) (hL : 10*w ≤ L) (hD : 2 ≤ D)
    (ht : t = min (L-5*w) (D-1)) (hrows : t ≤ 2*rows) (hm : 2*m = D*rows) :
    D * min L D ≤ 20*m := by
  have h₁ : L ≤ 2*(L-5*w) := by omega
  have h₂ : D ≤ 2*(D-1) := by omega
  have minBound : min L D ≤ 2*t := by
    by_cases cmp : L-5*w ≤ D-1
    · rw [ht, Nat.min_eq_left cmp]
      exact Nat.le_trans (Nat.min_le_left _ _) h₁
    · have rt : min (L-5*w) (D-1) = D-1 := Nat.min_eq_right (by omega)
      rw [ht, rt]
      exact Nat.le_trans (Nat.min_le_right _ _) h₂
  calc
    D * min L D ≤ D * (2*t) := Nat.mul_le_mul_left _ minBound
    _ = 2 * (D*t) := by ac_rfl
    _ ≤ 2 * (D*(2*rows)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hrows)
    _ = 4 * (D*rows) := by ac_rfl
    _ ≤ 20*m := by omega

def advance {d : Nat} (control : (Fin d → Bool) → Bool) (s : Fin (d+1) → Bool) :
    Fin (d+1) → Bool :=
  let tail := fun i : Fin d => s i.succ
  Fin.snoc tail (xor (s 0) (control tail))

def toggle {d : Nat} (s : Fin (d+1) → Bool) : Fin (d+1) → Bool :=
  Fin.cons (!s 0) (fun i : Fin d => s i.succ)

theorem toggleAdvance {d : Nat} (control : (Fin d → Bool) → Bool) (s : Fin (d+1) → Bool) :
    advance control (toggle s) =
      Fin.snoc (fun i : Fin d => s i.succ) (!(xor (s 0) (control (fun i : Fin d => s i.succ)))) := by
  simp only [advance, toggle, Fin.cons_succ, Fin.cons_zero]
  congr 1
  cases s 0 <;> cases control (fun i : Fin d => s i.succ) <;> decide


def windows {L w : Nat} (word : Fin (L+w) → Bool) :
    Fin (L+1) → Fin w → Bool :=
  fun i j => word ⟨i.val+j.val, by omega⟩

def Overlaps {L w : Nat} (states : Fin (L+1) → Fin w → Bool) : Prop :=
  ∀ (i : Nat) (hi : i < L) (j : Nat) (hj : j+1 < w),
    states ⟨i+1, by omega⟩ ⟨j, by omega⟩ =
      states ⟨i, by omega⟩ ⟨j+1, hj⟩

theorem windows_overlap {L w : Nat} (word : Fin (L+w) → Bool) :
    Overlaps (windows word) := by
  intro i hi j hj
  unfold windows
  congr 1
  apply Fin.ext
  simp only
  omega

theorem windows_injective {L w : Nat} (hw : 0 < w) :
    Function.Injective (@windows L w) := by
  intro u v eq
  funext k
  let u' := fun i : Nat => if hi : i < L+w then u ⟨i,hi⟩ else false
  let v' := fun i : Nat => if hi : i < L+w then v ⟨i,hi⟩ else false
  have agree : ∀ i ≤ L, ∀ j < w, u' (i+j) = v' (i+j) := by
    intro i hi j hj
    have bound : i+j < L+w := by omega
    simpa [u',v',bound,windows] using
      congrArg (fun f : Fin (L+1) → Fin w → Bool =>
        f ⟨i,by omega⟩ ⟨j,hj⟩) eq
  simpa [u',v',k.isLt] using windowsDetermine u' v' L w hw agree k.val k.isLt

theorem windows_of_overlap {L w : Nat} (states : Fin (L+1) → Fin w → Bool)
    (ov : Overlaps states) : ∃ word : Fin (L+w) → Bool, windows word = states := by
  let s := fun i j : Nat => if hi : i ≤ L then
      if hj : j < w then states ⟨i, by omega⟩ ⟨j,hj⟩ else false
    else false
  have ovNat (i : Nat) (hi : i < L) (j : Nat) (hj : j+1 < w) :
      s (i+1) j = s i (j+1) := by
    simpa [s, show i+1 ≤ L by omega, show i ≤ L by omega, show j < w by omega, hj] using ov i hi j hj
  refine ⟨fun k => encode s L k.val, ?_⟩
  funext i j
  simpa [windows,s,show i.val ≤ L by omega,j.isLt] using
    encodeWindows s L w ovNat i.val j.val (by omega) j.isLt


def lowerTrace {L w : Nat} (P : Fin (L+1) → Equiv (Fin w → Bool) (Fin w → Bool))
    (states : Fin (L+1) → Fin w → Bool) : Fin (L+1) → Fin w → Bool :=
  fun i => (P i).symm (states i)

def raiseTrace {L w : Nat} (P : Fin (L+1) → Equiv (Fin w → Bool) (Fin w → Bool))
    (states : Fin (L+1) → Fin w → Bool) : Fin (L+1) → Fin w → Bool :=
  fun i => P i (states i)

theorem wordTraceCard {L w : Nat} (hw : 0 < w)
    (P : Fin (L+1) → Equiv (Fin w → Bool) (Fin w → Bool))
    (words : Finset (Fin (L+w) → Bool))
    (traces : Finset (Fin (L+1) → Fin w → Bool))
    (classify : ∀ z, z ∈ words ↔ lowerTrace P (windows z) ∈ traces)
    (ov : ∀ p ∈ traces, Overlaps (raiseTrace P p)) :
    words.card = traces.card := by
  classical
  apply Finset.card_bij (fun z _ => lowerTrace P (windows z))
  · intro z hz
    exact (classify z).mp hz
  · intro z hz u hu eq
    apply windows_injective hw
    funext i
    simpa [lowerTrace] using congrArg (P i) (congrFun eq i)
  · intro p hp
    obtain ⟨z,hz⟩ := windows_of_overlap (raiseTrace P p) (ov p hp)
    have eq : lowerTrace P (windows z) = p := by
      rw [hz]
      funext i
      simp [lowerTrace,raiseTrace]
    exact ⟨z, (classify z).mpr (eq.symm ▸ hp), eq⟩

end WindowSwitch540
