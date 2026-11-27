import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
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


def shiftBit {d : Nat} (ctrl : (Fin d → Bool) → Bool) (s : Fin (d+1) → Bool) : Bool :=
  xor (s 0) (ctrl (fun j : Fin d => s j.succ))

theorem advance_inj {d : Nat} (ctrl : (Fin d → Bool) → Bool) :
    Function.Injective (advance ctrl) := by
  intro s t h
  have tails : (fun j : Fin d => s j.succ) = (fun j : Fin d => t j.succ) := by
    funext j
    simpa [advance] using congrFun h j.castSucc
  have last : xor (s 0) (ctrl (fun j : Fin d => s j.succ)) =
      xor (t 0) (ctrl (fun j : Fin d => t j.succ)) := by
    simpa [advance] using congrFun h (Fin.last d)
  rw [tails] at last
  have first : s 0 = t 0 := by
    have cancel (a b c : Bool) : xor a c = xor b c → a = b := by
      cases a <;> cases b <;> cases c <;> decide
    exact cancel _ _ _ last
  funext j
  refine Fin.cases first (fun k => congrFun tails k) j

theorem toggle_toggle {d : Nat} (s : Fin (d+1) → Bool) : toggle (toggle s) = s := by
  funext j
  refine Fin.cases ?_ (fun k => by simp [toggle]) j
  simp [toggle]

def windowChunk {d L : Nat} (word : Fin (L+(d+1)) → Bool) (i : Fin L) : Fin (d+2) → Bool :=
  fun j => word ⟨i.val+j.val, by omega⟩

theorem chunk_prefix {d L : Nat} (word : Fin (L+(d+1)) → Bool) (i : Fin L) :
    (fun j : Fin (d+1) => windowChunk word i j.castSucc) = windows word i.castSucc := rfl

theorem chunk_next {d L : Nat} (word : Fin (L+(d+1)) → Bool) (i : Fin L) :
    windows word i.succ =
      Fin.snoc (fun j : Fin d => windows word i.castSucc j.succ)
        (windowChunk word i (Fin.last (d+1))) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [Fin.snoc_last]
    unfold windows windowChunk
    congr 1
    apply Fin.ext
    simp
    omega
  · rw [Fin.snoc_castSucc]
    unfold windows
    congr 1
    apply Fin.ext
    simp
    omega

def tableBase {d L : Nat} (control : Fin L → (Fin d → Bool) → Bool)
    (s : Fin L × (Fin (d+2) → Bool)) : Bool :=
  decide (s.2 (Fin.last (d+1)) = shiftBit (control s.1) (fun j => s.2 j.castSucc))

def flipPort {d L : Nat} (control : Fin L → (Fin d → Bool) → Bool)
    (i : Fin L) (s : Fin (d+1) → Bool) : Fin L × (Fin (d+2) → Bool) :=
  (i, Fin.snoc s (!(shiftBit (control i) s)))

theorem flipPort_base {d L : Nat} (control : Fin L → (Fin d → Bool) → Bool)
    (i : Fin L) (s : Fin (d+1) → Bool) : tableBase control (flipPort control i s) = false := by
  simp only [flipPort,tableBase,Fin.snoc_last,Fin.snoc_castSucc]
  cases shiftBit (control i) s <;> decide

theorem flipPort_prefix {d L : Nat} (control : Fin L → (Fin d → Bool) → Bool)
    (i : Fin L) (s : Fin (d+1) → Bool) :
    (fun j => (flipPort control i s).2 j.castSucc) = s := by
  funext j
  simp [flipPort]

theorem base_advance_iff {d L : Nat} (control : Fin L → (Fin d → Bool) → Bool)
    (word : Fin (L+(d+1)) → Bool) (i : Fin L) :
    tableBase control (i,windowChunk word i) = true ↔
      windows word i.succ = advance (control i) (windows word i.castSucc) := by
  rw [tableBase,decide_eq_true_eq,chunk_prefix,chunk_next]
  constructor
  · intro eq
    change windowChunk word i (Fin.last (d+1)) = shiftBit (control i) (windows word i.castSucc) at eq
    exact congrArg (fun b : Bool => Fin.snoc (α := fun _ => Bool)
      (fun j : Fin d => windows word i.castSucc j.succ) b) eq
  · intro eq
    simpa only [advance,shiftBit,Fin.snoc_last] using congrFun eq (Fin.last d)

theorem port_advance_iff {d L : Nat} (control : Fin L → (Fin d → Bool) → Bool)
    (word : Fin (L+(d+1)) → Bool) (i : Fin L) (s : Fin (d+1) → Bool) :
    (i,windowChunk word i) = flipPort control i s ↔
      windows word i.castSucc = s ∧
      windows word i.succ = advance (control i) (toggle s) := by
  rw [toggleAdvance,chunk_next]
  constructor
  · intro eq
    have p := congrArg Prod.snd eq
    have old : windows word i.castSucc = s := by
      rw [← chunk_prefix word i]
      funext j
      simpa [flipPort] using congrFun p j.castSucc
    refine ⟨old, ?_⟩
    have last := congrFun p (Fin.last (d+1))
    simp only [flipPort,Fin.snoc_last] at last
    rw [old,last]
    rfl
  · rintro ⟨old,nxt⟩
    apply Prod.ext
    · rfl
    change windowChunk word i = Fin.snoc s (!(shiftBit (control i) s))
    have last := congrFun nxt (Fin.last d)
    simp only [Fin.snoc_last] at last
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa [flipPort,shiftBit] using last
    · simpa [flipPort,← chunk_prefix word i] using congrFun old k


abbrev State (d : Nat) := Fin (d+1) → Bool
abbrev PackingPrefix (d L : Nat) := Fin (L+1) → Equiv (State d) (State d)
abbrev WindowTable (d L : Nat) := Fin L → (Fin d → Bool) → Bool

def portsOf {d L m : Nat} (ctrl : WindowTable d L) (P : PackingPrefix d L)
    (edge : Fin m → State d × State d) (row : Fin m → Fin L) (j : Fin m) :
    Fin L × (Fin (d+2) → Bool) :=
  flipPort ctrl (row j) (P (row j).castSucc (edge j).1)

theorem portsOf_injective {d L m : Nat} (ctrl : WindowTable d L) (P : PackingPrefix d L)
    (edge : Fin m → State d × State d) (row : Fin m → Fin L)
    (inj : Function.Injective edge)
    (canFlip : ∀ j, toggle (P (row j).castSucc (edge j).1) = P (row j).castSucc (edge j).2) :
    Function.Injective (portsOf ctrl P edge row) := by
  intro j k eq
  have rr : row j = row k := congrArg Prod.fst eq
  have front : P (row j).castSucc (edge j).1 = P (row k).castSucc (edge k).1 := by
    have hp := congrArg (fun s : Fin L × (Fin (d+2) → Bool) =>
      fun i : Fin (d+1) => s.2 i.castSucc) eq
    simpa [portsOf,flipPort_prefix] using hp
  have first : (edge j).1 = (edge k).1 := by
    rw [rr] at front
    exact (P (row k).castSucc).injective front
  have back : P (row j).castSucc (edge j).2 = P (row k).castSucc (edge k).2 :=
    (canFlip j).symm.trans ((congrArg toggle front).trans (canFlip k))
  rw [rr] at back
  exact inj (Prod.ext first ((P (row k).castSucc).injective back))

def LocalStep {d L m : Nat} (edge : Fin m → State d × State d) (row : Fin m → Fin L)
    (enabled : Finset (Fin m)) (q : Fin (L+1) → State d) (i : Fin L) : Prop :=
  q i.succ = q i.castSucc ∨
    ∃ j ∈ enabled, row j = i ∧ q i.castSucc = (edge j).1 ∧ q i.succ = (edge j).2

theorem allowed_steps {d L m : Nat} (ctrl : WindowTable d L) (P : PackingPrefix d L)
    (edge : Fin m → State d × State d) (row : Fin m → Fin L)
    (baseStep : ∀ i x, P i.succ x = advance (ctrl i) (P i.castSucc x))
    (canFlip : ∀ j, toggle (P (row j).castSucc (edge j).1) = P (row j).castSucc (edge j).2)
    (enabled : Finset (Fin m)) (z : Fin (L+(d+1)) → Bool) (i : Fin L) :
    (tableBase ctrl (i,windowChunk z i) = true ∨
      (i,windowChunk z i) ∈ enabled.image (portsOf ctrl P edge row)) ↔
      LocalStep edge row enabled (lowerTrace P (windows z)) i := by
  let q := lowerTrace P (windows z)
  have atP (k) : P k (q k) = windows z k := by simp [q,lowerTrace]
  have eqv (k) (x) : q k = x ↔ windows z k = P k x := by
    constructor
    · intro h
      rw [← atP k, h]
    · intro h
      apply (P k).injective
      exact (atP k).trans h
  have baseline : tableBase ctrl (i,windowChunk z i) = true ↔ q i.succ = q i.castSucc := by
    rw [base_advance_iff, eqv i.succ, baseStep i, atP i.castSucc]
  have jump : (i,windowChunk z i) ∈ enabled.image (portsOf ctrl P edge row) ↔
      ∃ j ∈ enabled, row j = i ∧ q i.castSucc = (edge j).1 ∧ q i.succ = (edge j).2 := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨j,hj,eq⟩
      have rr : row j = i := congrArg Prod.fst eq
      subst i
      have step := (port_advance_iff ctrl z (row j) (P (row j).castSucc (edge j).1)).mp eq.symm
      refine ⟨j,hj,rfl,(eqv _ _).mpr step.1,(eqv _ _).mpr ?_⟩
      rw [step.2, canFlip j, baseStep (row j)]
    · rintro ⟨j,hj,rr,old,nxt⟩
      subst i
      refine ⟨j,hj, ((port_advance_iff ctrl z _ _).mpr ⟨(eqv _ _).mp old, ?_⟩).symm⟩
      rw [(eqv _ _).mp nxt, canFlip j, baseStep (row j)]
  exact or_congr baseline jump

theorem validTrace_local {d L m : Nat} (edge : Fin m → State d × State d) (row : Fin m → Fin L)
    (enabled : Finset (Fin m)) (x y : State d) (q : Fin (L+1) → State d) :
    ValidTrace edge (fun j => (row j).val) (fun j => j ∈ enabled) x y q ↔
      q 0 = x ∧ q (Fin.last L) = y ∧ ∀ i : Fin L, LocalStep edge row enabled q i := by
  have zero : traceAt q 0 = q 0 := by simp [traceAt]
  have last : traceAt q L = q (Fin.last L) := by simp [traceAt,Fin.last]
  simp only [ValidTrace,zero,last]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro h i
    have hs := h i.val i.isLt
    simp only [traceAt,dite_eq_left (show i.val+1 ≤ L by omega),dite_eq_left (show i.val ≤ L by omega)] at hs
    rcases hs with eq | ⟨j,hj,hr,hs,ht⟩
    · exact Or.inl eq
    · exact Or.inr ⟨j,hj,Fin.ext hr,hs,ht⟩
  · intro h i hi
    let k : Fin L := ⟨i,hi⟩
    simp only [traceAt,dite_eq_left (show i+1 ≤ L by omega),dite_eq_left (show i ≤ L by omega)]
    rcases h k with eq | ⟨j,hj,hr,hs,ht⟩
    · exact Or.inl eq
    · exact Or.inr ⟨j,hj,congrArg Fin.val hr,hs,ht⟩

theorem raised_overlap {d L m : Nat} (ctrl : WindowTable d L) (P : PackingPrefix d L)
    (edge : Fin m → State d × State d) (row : Fin m → Fin L) (enabled : Finset (Fin m))
    (baseStep : ∀ i x, P i.succ x = advance (ctrl i) (P i.castSucc x))
    (canFlip : ∀ j, toggle (P (row j).castSucc (edge j).1) = P (row j).castSucc (edge j).2)
    (q : Fin (L+1) → State d) (steps : ∀ i, LocalStep edge row enabled q i) :
    Overlaps (raiseTrace P q) := by
  intro i hi j hj
  let r : Fin L := ⟨i,hi⟩
  let k : Fin d := ⟨j, by omega⟩
  change P r.succ (q r.succ) k.castSucc = P r.castSucc (q r.castSucc) k.succ
  rcases steps r with equal | ⟨a,_,rr,start,finish⟩
  · rw [equal, baseStep r]
    simp [advance]
  · rw [start,finish,← rr,baseStep (row a),← canFlip a,toggleAdvance]
    simp


theorem countTable {d L m : Nat} (ctrl : WindowTable d L) (P : PackingPrefix d L)
    (edge : Fin m → State d × State d) (row : Fin m → Fin L)
    (baseStep : ∀ i x, P i.succ x = advance (ctrl i) (P i.castSucc x))
    (ends₀ : ∀ x, P 0 x = x) (ends₁ : ∀ x, P (Fin.last L) x = x)
    (canFlip : ∀ j, toggle (P (row j).castSucc (edge j).1) = P (row j).castSucc (edge j).2)
    (inj : Function.Injective edge)
    (separated : ∀ j k, (edge j).1 ≠ (edge k).2)
    (enabled : Finset (Fin m)) (x y : State d)
    (words : Finset (Fin (L+(d+1)) → Bool))
    (mem : ∀ z, z ∈ words ↔
      windows z 0 = x ∧ windows z (Fin.last L) = y ∧
        ∀ i : Fin L, tableBase ctrl (i,windowChunk z i) = true ∨
          (i,windowChunk z i) ∈ enabled.image (portsOf ctrl P edge row)) :
    words.card = (if x = y then 1 else 0) + (if ∃ j ∈ enabled, edge j = (x,y) then 1 else 0) := by
  classical
  let traces : Finset (Fin (L+1) → State d) :=
    Finset.univ.filter (ValidTrace edge (fun j => (row j).val) (fun j => j ∈ enabled) x y)
  have memTrace (q : Fin (L+1) → State d) : q ∈ traces ↔
      ValidTrace edge (fun j => (row j).val) (fun j => j ∈ enabled) x y q := by simp [traces]
  have classify z : z ∈ words ↔ lowerTrace P (windows z) ∈ traces := by
    rw [mem z,memTrace,validTrace_local]
    have left : lowerTrace P (windows z) 0 = windows z 0 := by
      unfold lowerTrace
      rw [← ends₀ ((P 0).symm (windows z 0))]
      exact (P 0).apply_symm_apply _
    have right : lowerTrace P (windows z) (Fin.last L) = windows z (Fin.last L) := by
      unfold lowerTrace
      rw [← ends₁ ((P (Fin.last L)).symm (windows z (Fin.last L)))]
      exact (P (Fin.last L)).apply_symm_apply _
    rw [left,right]
    exact and_congr_right (fun _ => and_congr_right (fun _ =>
      forall_congr' (allowed_steps ctrl P edge row baseStep canFlip enabled z)))
  have overlap (q) (hq : q ∈ traces) : Overlaps (raiseTrace P q) := by
    have good := (validTrace_local edge row enabled x y q).mp ((memTrace q).mp hq)
    exact raised_overlap ctrl P edge row enabled baseStep canFlip q good.2.2
  rw [wordTraceCard (by omega) P words traces classify overlap]
  exact exactTraceCount edge (fun j => (row j).val) (fun j => j ∈ enabled)
    (fun j => (row j).isLt) inj separated x y traces memTrace

theorem smallAddress {n k : Nat} [NeZero n] (bound : k < n) :
    Fin.ofNat n k = ⟨k,bound⟩ := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt bound

def orientPair {X : Type} (rev : Bool) (p : X × X) : X × X :=
  if rev then p.swap else p

theorem orient_inj {X : Type} (rev : Bool) : Function.Injective (@orientPair X rev) := by
  intro p q h
  cases rev with
  | false => exact h
  | true =>
    apply Prod.ext
    · exact congrArg Prod.snd h
    · exact congrArg Prod.fst h

theorem orient_eq_iff {X : Type} (rev : Bool) (p : X × X) (x y : X) :
    orientPair rev p = (x,y) ↔ p = (if rev then (y,x) else (x,y)) := by
  cases rev with
  | false => rfl
  | true =>
    constructor
    · intro h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

theorem packFromRows {d L m : Nat} (ctrl : WindowTable d L) (P : PackingPrefix d L)
    (edge : Fin m → State d × State d) (row : Fin m → Fin L)
    (baseStep : ∀ i x, P i.succ x = advance (ctrl i) (P i.castSucc x))
    (ends₀ : ∀ x, P 0 x = x) (ends₁ : ∀ x, P (Fin.last L) x = x)
    (canFlip : ∀ j, toggle (P (row j).castSucc (edge j).1) = P (row j).castSucc (edge j).2)
    (inj : Function.Injective edge)
    (separated : ∀ j k, (edge j).1 ≠ (edge k).2) :
    ∀ rev : Bool, Function.Injective (portsOf ctrl P (fun j => orientPair rev (edge j)) row) ∧
      (∀ j, tableBase ctrl (portsOf ctrl P (fun j => orientPair rev (edge j)) row j) = false) ∧
      ∀ (enabled : Finset (Fin m)) (x y : State d),
        (Finset.univ.filter (fun z : Fin (L+d+1) → Bool =>
          (∀ j : Fin (d+1), z (Fin.ofNat (L+d+1) j.val) = x j ∧
            z (Fin.ofNat (L+d+1) (L+j.val)) = y j) ∧
          ∀ i : Fin L, let s := (i,fun j : Fin (d+2) => z (Fin.ofNat (L+d+1) (i.val+j.val)))
            tableBase ctrl s = true ∨ s ∈ enabled.image
                (portsOf ctrl P (fun j => orientPair rev (edge j)) row))).card =
          (if x = y then 1 else 0) + (if ∃ j ∈ enabled, edge j =
            (if rev then (y,x) else (x,y)) then 1 else 0) := by
  intro rev
  let dir := fun j => orientPair rev (edge j)
  have dirInj : Function.Injective dir := (orient_inj rev).comp inj
  have dirFlip (j) : toggle (P (row j).castSucc (dir j).1) = P (row j).castSucc (dir j).2 := by
    cases rev with
    | false => exact canFlip j
    | true => exact (congrArg toggle (canFlip j)).symm.trans (toggle_toggle _)
  have dirSeparate (j k) : (dir j).1 ≠ (dir k).2 := by
    cases rev with
    | false => exact separated j k
    | true => exact Ne.symm (separated k j)
  refine ⟨portsOf_injective ctrl P dir row dirInj dirFlip, ?_, ?_⟩
  · intro j
    exact flipPort_base ctrl _ _
  · intro enabled x y
    have same (j : Fin m) : dir j = (x,y) ↔ edge j = (if rev then (y,x) else (x,y)) :=
      orient_eq_iff rev (edge j) x y
    have condition : (∃ j ∈ enabled, dir j = (x,y)) ↔
        (∃ j ∈ enabled, edge j = (if rev then (y,x) else (x,y))) :=
      exists_congr (fun j => and_congr_right (fun _ => same j))
    have condIte : (if ∃ j ∈ enabled, dir j = (x,y) then 1 else 0) =
        (if ∃ j ∈ enabled, edge j = (if rev then (y,x) else (x,y)) then 1 else 0) := by
      by_cases h : ∃ j ∈ enabled, dir j = (x,y)
      · simp [h,condition.mp h]
      · have no : ¬∃ j ∈ enabled, edge j = (if rev then (y,x) else (x,y)) :=
          fun yes => h (condition.mpr yes)
        rw [ite_eq_right h, ite_eq_right no]
    rw [← condIte]
    apply countTable ctrl P dir row baseStep ends₀ ends₁ dirFlip dirInj dirSeparate enabled x y
    intro z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [← and_assoc]
    apply and_congr
    · unfold windows
      constructor
      · intro h
        constructor
        · funext j
          simpa only [Fin.val_zero,Nat.zero_add,← smallAddress (by omega : j.val < L+d+1)] using (h j).1
        · funext j
          simpa only [Fin.val_last,← smallAddress (by omega : L+j.val < L+d+1)] using (h j).2
      · rintro ⟨h₁,h₂⟩ j
        constructor
        · simpa only [Fin.val_zero,Nat.zero_add,smallAddress (by omega : j.val < L+d+1)] using congrFun h₁ j
        · simpa only [Fin.val_last,smallAddress (by omega : L+j.val < L+d+1)] using congrFun h₂ j
    · apply forall_congr'
      intro i
      have chunk : (fun j : Fin (d+2) => z (Fin.ofNat (L+d+1) (i.val+j.val))) = windowChunk z i := by
        funext j
        unfold windowChunk
        exact congrArg z (smallAddress (n := L+d+1) (by omega : i.val+j.val < L+d+1))
      rw [chunk]


theorem enumerateFromBank {d L : Nat} (P : PackingPrefix d L)
    (rows : Finset (Fin L)) (bank : Finset (State d))
    (motion : Fin L → State d → State d)
    (hasFlip : ∀ i ∈ rows, ∀ x ∈ bank,
      toggle (P i.castSucc x) = P i.castSucc (motion i x))
    (leavesBank : ∀ i ∈ rows, ∀ x ∈ bank, motion i x ∉ bank)
    (rowUnique : ∀ x ∈ bank, ∀ i ∈ rows, ∀ j ∈ rows, motion i x = motion j x → i = j) :
    ∃ (m : Nat) (edge : Fin m → State d × State d) (row : Fin m → Fin L),
      m = rows.card * bank.card ∧ Function.Injective edge ∧
      (∀ j k, (edge j).1 ≠ (edge k).2) ∧
      (∀ j, toggle (P (row j).castSucc (edge j).1) = P (row j).castSucc (edge j).2) := by
  classical
  let Index := (↥rows) × (↥bank)
  let m := Fintype.card Index
  let index : Fin m ≃ Index := (Fintype.equivFin Index).symm
  let row : Fin m → Fin L := fun j => (index j).1.val
  let input : Fin m → State d := fun j => (index j).2.val
  let edge : Fin m → State d × State d := fun j => (input j,motion (row j) (input j))
  have memberRow (j) : row j ∈ rows := (index j).1.property
  have memberInput (j) : input j ∈ bank := (index j).2.property
  refine ⟨m,edge,row,?_,?_,?_,?_⟩
  · simp [m,Index,Fintype.card_prod]
  · intro j k e
    have first : input j = input k := congrArg Prod.fst e
    have second : motion (row j) (input j) = motion (row k) (input j) := by
      have second := congrArg Prod.snd e
      change motion (row j) (input j) = motion (row k) (input k) at second
      simpa only [← first] using second
    have r := rowUnique _ (memberInput j) _ (memberRow j) _ (memberRow k) second
    apply index.injective
    exact Prod.ext (Subtype.ext r) (Subtype.ext first)
  · intro j k eq
    apply leavesBank _ (memberRow k) _ (memberInput k)
    change input j = motion (row k) (input k) at eq
    rw [← eq]
    exact memberInput j
  · intro j
    exact hasFlip _ (memberRow j) _ (memberInput j)

theorem primitivePowerBasis (w : Nat) (hw : w ≠ 0) :
    ∃ (g : (GaloisField 2 w)ˣ) (pb : PowerBasis (ZMod 2) (GaloisField 2 w)),
      orderOf g = 2^w-1 ∧ pb.gen = (g : GaloisField 2 w) ∧ pb.dim = w := by
  classical
  obtain ⟨g,gen⟩ := IsCyclic.exists_generator (α := (GaloisField 2 w)ˣ)
  have ord : orderOf g = 2^w-1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers gen, Nat.card_units, GaloisField.card 2 w hw]
  have top : IntermediateField.adjoin (ZMod 2) {(g : GaloisField 2 w)} = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    by_cases h : x = 0
    · subst x
      exact zero_mem _
    · let u : (GaloisField 2 w)ˣ := Units.mk0 x h
      obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff u g).mp (mem_powers_iff_mem_zpowers.mpr (gen u))
      have e : (g : GaloisField 2 w)^j = x := by
        simpa [u] using congrArg (fun a : (GaloisField 2 w)ˣ => (a : GaloisField 2 w)) hj
      rw [← e]
      exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _
  let pb := (IntermediateField.adjoin.powerBasis (Algebra.IsSeparable.isIntegral (ZMod 2)
    (g : GaloisField 2 w))).map ((IntermediateField.equivOfEq top).trans IntermediateField.topEquiv)
  refine ⟨g,pb,ord,?_,?_⟩
  · rfl
  · exact pb.finrank.symm.trans (GaloisField.finrank 2 hw)

theorem dualMultiplication_not_fixed {K F : Type} [Field K] [Field F] [Algebra K F]
    (a : F) (hne : a ≠ 1) (f : F →ₗ[K] K) (nonzero : f ≠ 0)
    (fix : ∀ x, f (a*x) = f x) : False := by
  apply nonzero
  ext y
  let x := (a-1)⁻¹*y
  have h : (a-1)*x = y := by
    rw [show (a-1)*x = ((a-1)*(a-1)⁻¹)*y by simp [x,mul_assoc], mul_inv_cancel₀ (sub_ne_zero.mpr hne),one_mul]
  calc
    f y = f ((a-1)*x) := congrArg f h.symm
    _ = f (a*x) - f x := by rw [sub_mul,one_mul,map_sub]
    _ = 0 := sub_eq_zero.mpr (fix x)
    _ = (0 : F →ₗ[K] K) y := rfl


theorem dualOrbit_inj {K F : Type} [Field K] [Field F] [Algebra K F]
    (g : Fˣ) (f : F →ₗ[K] K) (hf : f ≠ 0) :
    Function.Injective (fun i : Fin (orderOf g) => fun x : F => f ((g : F)^i.val * x)) := by
  intro i j he
  apply Fin.ext
  by_contra hne
  have ordered {a b : Fin (orderOf g)} (lt : a.val < b.val)
      (eq : (fun x : F => f ((g : F)^a.val * x)) = fun x : F => f ((g : F)^b.val * x)) : False := by
    let n := b.val - a.val
    have pos : n ≠ 0 := by dsimp [n]; omega
    have nlt : n < orderOf g := by
      have := b.isLt
      dsimp [n]
      omega
    have notone : (g : F)^n ≠ 1 := by
      intro h
      apply pow_ne_one_of_lt_orderOf (x := g) pos nlt
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val,Units.val_one] using h
    apply dualMultiplication_not_fixed ((g : F)^n) notone f hf
    intro x
    have nonzero : (g : F)^a.val ≠ 0 := pow_ne_zero _ (Units.ne_zero g)
    have collapse : (g : F)^a.val * (((g : F)^a.val)⁻¹*x) = x := by
      rw [← mul_assoc,mul_inv_cancel₀ nonzero,one_mul]
    have exp : b.val = n + a.val := by dsimp [n]; omega
    have diff : (g : F)^b.val * (((g : F)^a.val)⁻¹*x) = (g : F)^n*x := by
      rw [exp,pow_add,mul_assoc,collapse]
    have q := congrFun eq (((g : F)^a.val)⁻¹*x)
    rw [collapse,diff] at q
    exact q.symm
  rcases lt_or_gt_of_ne hne with h|h
  · exact ordered h he
  · exact ordered h he.symm

theorem multiplier_shifts {K F : Type} [Field K] [Field F] [Algebra K F]
    (pb : PowerBasis K F) (f : F →ₗ[K] K) (i : Nat) (h : i+1 < pb.dim) :
    f (pb.gen * pb.basis ⟨i,by omega⟩) = f (pb.basis ⟨i+1,h⟩) := by
  rw [pb.basis_eq_pow,pb.basis_eq_pow]
  simp only [pow_succ']

end WindowSwitch540
