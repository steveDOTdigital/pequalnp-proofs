import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_471
import PEqualNP.Outside.L_lib_394

namespace PEqualNP.Outside.L_lib_540_aux

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

abbrev Vec2 (w : Nat) := Fin w → ZMod 2

def pairValue {w : Nat} (x y : Vec2 w) : ZMod 2 :=
  ∑ i, x i * y i

theorem pair_symm {w : Nat} (x y : Vec2 w) : pairValue x y = pairValue y x := by
  simp only [pairValue, mul_comm]

theorem pair_add_left {w : Nat} (x z y : Vec2 w) :
    pairValue (x+z) y = pairValue x y + pairValue z y := by
  simp [pairValue, add_mul, Finset.sum_add_distrib]

theorem pair_sub_left {w : Nat} (x z y : Vec2 w) :
    pairValue (x-z) y = pairValue x y - pairValue z y := by
  simp [pairValue, sub_mul, Finset.sum_sub_distrib]

theorem pair_single {w : Nat} (i : Fin w) (y : Vec2 w) :
    pairValue (Pi.single i (1 : ZMod 2)) y = y i := by
  simp [pairValue, Pi.single_apply, ite_mul, Finset.sum_ite_eq']

theorem pair_zero_left {w : Nat} (x : Vec2 w) : pairValue 0 x = 0 := by simp [pairValue]

theorem bitDichotomy (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  exact h a

theorem nonzero_coordinate {w : Nat} (y : Vec2 w) (hy : y ≠ 0) :
    ∃ i, y i = 1 := by
  by_contra! h
  apply hy
  funext i
  exact (bitDichotomy (y i)).resolve_right (h i)

theorem balancedPair {w : Nat} (y : Vec2 w) (hy : y ≠ 0) :
    2 * (Finset.univ.filter (fun x : Vec2 w => pairValue x y = 1)).card = 2^w ∧
    2 * (Finset.univ.filter (fun x : Vec2 w => pairValue x y = 0)).card = 2^w := by
  obtain ⟨i,hi⟩ := nonzero_coordinate y hy
  let e : Vec2 w := Pi.single i 1
  have pair : pairValue e y = 1 := (pair_single i y).trans hi
  let zeros := Finset.univ.filter (fun x : Vec2 w => pairValue x y = 0)
  let ones := Finset.univ.filter (fun x : Vec2 w => pairValue x y = 1)
  have in₀ x : x ∈ zeros ↔ pairValue x y = 0 := by simp [zeros]
  have in₁ x : x ∈ ones ↔ pairValue x y = 1 := by simp [ones]
  have eq : zeros.card = ones.card := by
    apply Finset.card_bij (fun x _ => x+e)
    · intro x h
      apply (in₁ _).mpr
      rw [pair_add_left,pair,(in₀ _).mp h,zero_add]
    · intro a ha b hb h
      exact add_right_cancel h
    · intro z hz
      refine ⟨z-e, (in₀ _).mpr ?_, sub_add_cancel z e⟩
      rw [pair_sub_left,pair,(in₁ _).mp hz,sub_self]
  have disj : Disjoint zeros ones := by
    refine Finset.disjoint_left.mpr ?_
    intro a az ao
    exact zero_ne_one ((in₀ _).mp az |>.symm.trans ((in₁ _).mp ao))
  have total : zeros ∪ ones = Finset.univ := by
    ext x
    simp only [Finset.mem_union,in₀,in₁,Finset.mem_univ,iff_true]
    exact bitDichotomy _
  have dim : (Finset.univ : Finset (Vec2 w)).card = 2^w := by
    simp [Vec2,ZMod.card]
  have two : zeros.card + ones.card = 2^w := by
    rw [← Finset.card_union_of_disjoint disj,total,dim]
  change 2*ones.card = 2^w ∧ 2*zeros.card = 2^w
  omega

theorem triangularForm {w : Nat} (v : Fin w → Vec2 w)
    (diag : ∀ i, v i i = 1)
    (lastZero : ∀ i j, i.val < j.val → v i j = 0) :
    ∃ l : Vec2 w, ∀ i, pairValue l (v i) = 1 := by
  induction w with
  | zero =>
    exact ⟨0, fun i => Fin.elim0 i⟩
  | succ w ih =>
    let sub : Fin w → Vec2 w := fun i j => v i.castSucc j.castSucc
    obtain ⟨l,hl⟩ := ih sub (fun i => diag i.castSucc)
      (fun i j h => lastZero i.castSucc j.castSucc h)
    let last := 1-pairValue l (fun j : Fin w => v (Fin.last w) j.castSucc)
    refine ⟨Fin.snoc l last,?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · unfold pairValue
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc,Fin.snoc_last,diag,mul_one]
      change pairValue l (fun j : Fin w => v (Fin.last w) j.castSucc) + last = 1
      rw [add_comm]
      exact sub_add_cancel _ _
    · unfold pairValue
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc,Fin.snoc_last,lastZero j.castSucc (Fin.last w) j.isLt,
        mul_zero,add_zero]
      exact hl j


theorem manyOddRows {I : Type} [DecidableEq I] {w : Nat}
    (rows : Finset I) (v : I → Vec2 w) (nz : ∀ i ∈ rows, v i ≠ 0) :
    ∃ l : Vec2 w, rows.card ≤ 2 * (rows.filter (fun i => pairValue l (v i) = 1)).card := by
  classical
  let good (l : Vec2 w) := (rows.filter (fun i => pairValue l (v i) = 1)).card
  have dim : (Finset.univ : Finset (Vec2 w)).card = 2^w := by simp [Vec2,ZMod.card]
  have total : (∑ l : Vec2 w, 2 * good l) = rows.card * 2^w := by
    calc
      _ = ∑ l : Vec2 w, ∑ i ∈ rows, 2 * (if pairValue l (v i) = 1 then 1 else 0) := by
        simp only [good,Finset.card_filter,Finset.mul_sum]
      _ = ∑ i ∈ rows, ∑ l : Vec2 w, 2 * (if pairValue l (v i) = 1 then 1 else 0) :=
        Finset.sum_comm
      _ = ∑ i ∈ rows, 2^w := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa only [← Finset.mul_sum, ← Finset.card_filter] using (balancedPair (v i) (nz i hi)).1
      _ = _ := by simp
  by_contra! bad
  have impossible : (∑ l ∈ (Finset.univ : Finset (Vec2 w)), (2 * good l + 1)) ≤
      ∑ _ ∈ (Finset.univ : Finset (Vec2 w)), rows.card := by
    apply Finset.sum_le_sum
    intro l _
    exact Nat.succ_le_of_lt (bad l)
  rw [Finset.sum_add_distrib,total,Finset.sum_const,Finset.sum_const,dim] at impossible
  simp only [nsmul_eq_mul] at impossible
  have pos : 0 < 2^w := Nat.two_pow_pos w
  change rows.card * 2^w + 2^w * 1 ≤ 2^w * rows.card at impossible
  rw [mul_one, Nat.mul_comm (2^w) rows.card] at impossible
  omega


def bitAsZ : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := decide (z = 1)
  left_inv b := by cases b <;> decide
  right_inv z := by
    have exactBit : ∀ a : ZMod 2, ((if decide (a = 1) then 1 else 0) : ZMod 2) = a := by decide
    exact exactBit z

def stateVec (d : Nat) : State d ≃ Vec2 (d+1) :=
  Equiv.piCongrRight (fun _ => bitAsZ)

theorem pair_add_right {w : Nat} (x y z : Vec2 w) :
    pairValue x (y+z) = pairValue x y + pairValue x z := by
  rw [pair_symm x (y+z),pair_add_left,pair_symm y x,pair_symm z x]

theorem bankOfVector {d L : Nat} (P : PackingPrefix d L) (J : Finset (Fin L))
    (move : Fin L → Vec2 (d+1)) (l : Vec2 (d+1)) (nonzero : l ≠ 0)
    (distinct : ∀ i ∈ J, ∀ j ∈ J, move i = move j → i = j)
    (odd : ∀ i ∈ J, pairValue l (move i) = 1)
    (flip : ∀ i ∈ J, ∀ x : State d,
      toggle (P i.castSucc x) = P i.castSucc ((stateVec d).symm (stateVec d x + move i))) :
    ∃ (m : Nat) (edge : Fin m → State d × State d) (row : Fin m → Fin L),
      2*m = 2^(d+1)*J.card ∧ Function.Injective edge ∧
      (∀ j k, (edge j).1 ≠ (edge k).2) ∧
      (∀ j, toggle (P (row j).castSucc (edge j).1) = P (row j).castSucc (edge j).2) := by
  classical
  let bank := Finset.univ.filter (fun x : State d => pairValue l (stateVec d x) = 0)
  let motion := fun (i : Fin L) (x : State d) => (stateVec d).symm (stateVec d x + move i)
  have bankSpec (x : State d) : x ∈ bank ↔ pairValue l (stateVec d x) = 0 := by simp [bank]
  have bc : bank.card = (Finset.univ.filter (fun z : Vec2 (d+1) => pairValue z l = 0)).card := by
    apply Finset.card_bij (fun s _ => stateVec d s)
    · intro s hs
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rw [pair_symm]
      exact (bankSpec _).mp hs
    · intro a _ b _ e
      exact (stateVec d).injective e
    · intro z hz
      have zc : pairValue z l = 0 := by simpa using hz
      refine ⟨(stateVec d).symm z,(bankSpec _).mpr ?_,(stateVec d).apply_symm_apply _⟩
      rw [(stateVec d).apply_symm_apply, pair_symm]
      exact zc
  have size : 2*bank.card = 2^(d+1) := by
    rw [bc]
    exact (balancedPair l nonzero).2
  have leaves : ∀ i ∈ J, ∀ x ∈ bank, motion i x ∉ bank := by
    intro i hi x hx hc
    have z := (bankSpec _).mp hc
    simp only [motion,Equiv.apply_symm_apply,pair_add_right,(bankSpec _).mp hx,odd i hi,zero_add] at z
    exact one_ne_zero z
  have unique : ∀ x ∈ bank, ∀ i ∈ J, ∀ j ∈ J, motion i x = motion j x → i = j := by
    intro x _ i hi j hj same
    have z : stateVec d x + move i = stateVec d x + move j := by
      simpa only [motion,Equiv.apply_symm_apply] using congrArg (stateVec d) same
    exact distinct i hi j hj (add_left_cancel z)
  obtain ⟨m,edge,row,hcount,hinj,hsep,hflip⟩ :=
    enumerateFromBank P J bank motion (fun i hi x _ => flip i hi x) leaves unique
  refine ⟨m,edge,row,?_,hinj,hsep,hflip⟩
  calc
    2*m = (2*bank.card)*J.card := by rw [hcount]; ac_rfl
    _ = _ := by rw [size]


theorem bankFromEarly {d L : Nat} (P : PackingPrefix d L) (size : d+1 ≤ L)
    (short : L < 10*(d+1)) (move : Fin L → Vec2 (d+1))
    (diag : ∀ i : Fin (d+1), move (Fin.castLE size i) i = 1)
    (above : ∀ i j : Fin (d+1), i.val < j.val → move (Fin.castLE size i) j = 0)
    (flip : ∀ (i : Fin L), i.val < d+1 → ∀ x : State d,
      toggle (P i.castSucc x) = P i.castSucc ((stateVec d).symm (stateVec d x + move i))) :
    ∃ (m : Nat) (edge : Fin m → State d × State d) (row : Fin m → Fin L),
      2^(d+1) * min L (2^(d+1)) ≤ 20*m ∧ Function.Injective edge ∧
      (∀ j k, (edge j).1 ≠ (edge k).2) ∧
      (∀ j, toggle (P (row j).castSucc (edge j).1) = P (row j).castSucc (edge j).2) := by
  let J := Finset.univ.image (Fin.castLE size)
  have jc : J.card = d+1 := by
    rw [show J = Finset.univ.image (Fin.castLE size) from rfl,Finset.card_image_of_injective]
    · simp
    · intro a b eq
      exact Fin.ext (congrArg (fun q : Fin L => q.val) eq)
  have orig {i : Fin L} (hi : i ∈ J) : ∃ j : Fin (d+1), Fin.castLE size j = i := by
    simpa [J,Finset.mem_image] using hi
  obtain ⟨l,hl⟩ := triangularForm (fun i => move (Fin.castLE size i)) diag above
  have lnz : l ≠ 0 := by
    intro eq
    have h1 := hl 0
    rw [eq,pair_zero_left] at h1
    exact zero_ne_one h1
  have odd (i) (hi : i ∈ J) : pairValue l (move i) = 1 := by
    obtain ⟨j,rfl⟩ := orig hi
    exact hl j
  have distinct (i) (hi : i ∈ J) (j) (hj : j ∈ J) (eq : move i = move j) : i=j := by
    obtain ⟨a,rfl⟩ := orig hi
    obtain ⟨b,rfl⟩ := orig hj
    by_cases same : a = b
    · subst b
      rfl
    · rcases lt_or_gt_of_ne (show a.val ≠ b.val from fun hs => same (Fin.ext hs)) with h|h
      · exfalso
        have e := congrFun eq b
        rw [above a b h,diag b] at e
        exact zero_ne_one e
      · exfalso
        have e := congrFun eq a
        rw [diag a, above b a h] at e
        exact one_ne_zero e
  obtain ⟨m,edge,row,hm,inj,sep,ok⟩ := bankOfVector P J move l lnz distinct odd (by
    intro i hi x
    obtain ⟨j,rfl⟩ := orig hi
    exact flip _ j.isLt x)
  rw [jc] at hm
  exact ⟨m,edge,row,shortMultiplicity _ (d+1) _ m short hm,inj,sep,ok⟩

theorem bankFromLong {d L t : Nat} (P : PackingPrefix d L)
    (large : 10*(d+1) ≤ L) (tdef : t = min (L-5*(d+1)) (2^(d+1)-1))
    (move : Fin L → Vec2 (d+1))
    (nz : ∀ i : Fin L, i.val < t → move i ≠ 0)
    (distinct : ∀ i j : Fin L, i.val < t → j.val < t → move i = move j → i=j)
    (flip : ∀ (i : Fin L), i.val < t → ∀ x : State d,
      toggle (P i.castSucc x) = P i.castSucc ((stateVec d).symm (stateVec d x + move i))) :
    ∃ (m : Nat) (edge : Fin m → State d × State d) (row : Fin m → Fin L),
      2^(d+1) * min L (2^(d+1)) ≤ 20*m ∧ Function.Injective edge ∧
      (∀ j k, (edge j).1 ≠ (edge k).2) ∧
      (∀ j, toggle (P (row j).castSucc (edge j).1) = P (row j).castSucc (edge j).2) := by
  have tL : t ≤ L := by
    rw [tdef]
    exact (Nat.min_le_left _ _).trans (Nat.sub_le _ _)
  have Dtwo : 2 ≤ 2^(d+1) := by
    rw [pow_succ]
    have := Nat.two_pow_pos d
    omega
  have pos : 0 < t := by
    rw [tdef]
    exact Nat.lt_min.mpr ⟨by omega,by omega⟩
  let all := Finset.univ.image (Fin.castLE tL)
  have allCard : all.card = t := by
    rw [show all = Finset.univ.image (Fin.castLE tL) from rfl,Finset.card_image_of_injective]
    · simp
    · intro a b eq
      exact Fin.ext (congrArg (fun q : Fin L => q.val) eq)
  have member {i : Fin L} (h : i ∈ all) : i.val < t := by
    obtain ⟨j,rfl⟩ : ∃ j : Fin t, Fin.castLE tL j = i := by simpa [all,Finset.mem_image] using h
    exact j.isLt
  obtain ⟨l,hl⟩ := manyOddRows all move (fun i hi => nz i (member hi))
  let J := all.filter (fun i => pairValue l (move i) = 1)
  have count : t ≤ 2*J.card := by simpa only [← allCard] using hl
  have lnz : l ≠ 0 := by
    intro eq
    have J0 : J.card = 0 := by simp [J,eq,pair_zero_left]
    omega
  have both {i : Fin L} (h : i ∈ J) : i ∈ all ∧ pairValue l (move i) = 1 := Finset.mem_filter.mp h
  obtain ⟨m,edge,row,hm,inj,sep,ok⟩ :=
    bankOfVector P J move l lnz
      (fun i hi j hj e => distinct i j (member (both hi).1) (member (both hj).1) e)
      (fun i hi => (both hi).2) (fun i hi x => flip i (member (both hi).1) x)
  exact ⟨m,edge,row,longMultiplicity _ _ _ t J.card m large Dtwo tdef count hm,inj,sep,ok⟩

noncomputable def advancePerm {d : Nat} (control : (Fin d → Bool) → Bool) : Equiv.Perm (State d) :=
  Equiv.ofBijective (advance control) ⟨advance_inj control, Finite.surjective_of_injective (advance_inj control)⟩

theorem rangeLast (m : Nat) :
    List.finRange (m+1) = (List.finRange m).map Fin.castSucc ++ [Fin.last m] := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  by_cases hi : i < m
  · rw [List.getElem_append_left (by simp [hi])]
    simp
  · have him : i = m := by
      simp only [List.length_finRange] at h1
      omega
    subst him
    rw [List.getElem_append_right (by simp)]
    simp [Fin.last]

noncomputable def prefixOf {d L : Nat} (control : WindowTable d L) (i : Fin (L+1)) :
    Equiv.Perm (State d) :=
  (List.finRange i.val).foldl
    (fun p r => p.trans (advancePerm (control ⟨r.val, by omega⟩)))
    (Equiv.refl (State d))

theorem prefixOf_zero {d L : Nat} (ctrl : WindowTable d L) (x : State d) : prefixOf ctrl 0 x = x := by
  simp [prefixOf]

theorem prefixOf_succ {d L : Nat} (ctrl : WindowTable d L) (i : Fin L) (x : State d) :
    prefixOf ctrl i.succ x = advance (ctrl i) (prefixOf ctrl i.castSucc x) := by
  unfold prefixOf
  simp only [Fin.val_succ,Fin.val_castSucc]
  rw [rangeLast,List.foldl_append,List.foldl_map]
  rfl

theorem fold_perm_eval {d L : Nat} (ctrl : WindowTable d L) (rows : List (Fin L))
    (p : Equiv.Perm (State d)) (x : State d) :
    (rows.foldl (fun q j => q.trans (advancePerm (ctrl j))) p) x =
      rows.foldl (fun y j => advance (ctrl j) y) (p x) := by
  induction rows generalizing p with
  | nil => rfl
  | cons a tail ih =>
    simp only [List.foldl_cons]
    rw [ih]
    rfl

theorem prefixOf_last {d L : Nat} (ctrl : WindowTable d L) (x : State d) :
    prefixOf ctrl (Fin.last L) x = (List.finRange L).foldl (fun s j => advance (ctrl j) s) x := by
  unfold prefixOf
  exact fold_perm_eval ctrl (List.finRange L) (Equiv.refl (State d)) x



theorem prefixUntouched {d L : Nat} (ctrl : WindowTable d L) (x : State d)
    (n : Nat) (hn : n ≤ L) (j : Fin (d+1)) (h : n+j.val < d+1) :
    prefixOf ctrl ⟨n,by omega⟩ x j = x ⟨n+j.val,h⟩ := by
  induction n generalizing j with
  | zero =>
    change prefixOf ctrl 0 x j = _
    rw [prefixOf_zero]
    congr 1
    apply Fin.ext
    simp
  | succ n ih =>
    let k : Fin d := ⟨j.val, by omega⟩
    let i : Fin L := ⟨n,by omega⟩
    have eq : j = k.castSucc := Fin.ext rfl
    have sum : n+k.succ.val = n+1+j.val := by dsimp [k]; omega
    calc
      _ = prefixOf ctrl i.succ x k.castSucc := congrArg (prefixOf ctrl i.succ x) eq
      _ = prefixOf ctrl i.castSucc x k.succ := by rw [prefixOf_succ,advance,Fin.snoc_castSucc]
      _ = x ⟨n+k.succ.val,by omega⟩ := ih (by omega) k.succ (by omega)
      _ = _ := congrArg x (Fin.ext sum)

noncomputable def firstDifference {d L : Nat} (ctrl : WindowTable d L) (i : Fin L) : State d :=
  (prefixOf ctrl i.castSucc).symm (toggle (prefixOf ctrl i.castSucc (fun _ => false)))

theorem difference_diagonal {d L : Nat} (ctrl : WindowTable d L) (i : Fin L)
    (hi : i.val < d+1) : firstDifference ctrl i ⟨i.val,hi⟩ = true := by
  have describe (x : State d) : prefixOf ctrl i.castSucc x 0 = x ⟨i.val,hi⟩ := by
    have a := prefixUntouched ctrl x i.val (by omega) 0 (by change i.val+0 < d+1; omega)
    have idx : (⟨i.val,by omega⟩ : Fin (L+1)) = i.castSucc := Fin.ext rfl
    rw [idx] at a
    simpa using a
  have eq := congrFun ((prefixOf ctrl i.castSucc).apply_symm_apply
    (toggle (prefixOf ctrl i.castSucc (fun _ => false)))) 0
  change prefixOf ctrl i.castSucc (firstDifference ctrl i) 0 = _ at eq
  rw [toggle,Fin.cons_zero,describe,describe] at eq
  simpa using eq

theorem difference_upper_zero {d L : Nat} (ctrl : WindowTable d L) (i : Fin L)
    (j : Fin (d+1)) (gt : i.val < j.val) : firstDifference ctrl i j = false := by
  let k : Fin d := ⟨j.val-i.val-1,by omega⟩
  have sum : i.val+k.succ.val=j.val := by dsimp [k]; omega
  have describe (x : State d) : prefixOf ctrl i.castSucc x k.succ = x j := by
    have a := prefixUntouched ctrl x i.val (by omega) k.succ (by omega)
    have idx : (⟨i.val,by omega⟩ : Fin (L+1)) = i.castSucc := Fin.ext rfl
    rw [idx] at a
    exact a.trans (congrArg x (Fin.ext sum))
  have eq := congrFun ((prefixOf ctrl i.castSucc).apply_symm_apply
    (toggle (prefixOf ctrl i.castSucc (fun _ => false)))) k.succ
  change prefixOf ctrl i.castSucc (firstDifference ctrl i) k.succ = _ at eq
  rw [toggle,Fin.cons_succ,describe,describe] at eq
  exact eq



def IsAffine2 {w : Nat} (f : Vec2 w → Vec2 w) : Prop :=
  ∀ x y, f (x+y) = f x + f y - f 0

theorem affine_sub {w : Nat} {f : Vec2 w → Vec2 w} (hf : IsAffine2 f)
    (x y : Vec2 w) : f (x-y) = f x - f y + f 0 := by
  have h := hf (x-y) y
  rw [sub_add_cancel] at h
  calc
    f (x-y) = (f (x-y) + f y - f 0) - f y + f 0 := by abel
    _ = _ := by rw [← h]

theorem affine_comp {w : Nat} {f g : Vec2 w → Vec2 w}
    (hf : IsAffine2 f) (hg : IsAffine2 g) : IsAffine2 (f ∘ g) := by
  intro x y
  unfold Function.comp
  rw [hg x y,affine_sub hf, hf (g x) (g y)]
  abel

def liftToVec {d : Nat} (f : State d → State d) : Vec2 (d+1) → Vec2 (d+1) :=
  fun x => stateVec d (f ((stateVec d).symm x))

theorem liftToVec_comp {d : Nat} (f g : State d → State d) :
    liftToVec (f ∘ g) = liftToVec f ∘ liftToVec g := by
  funext x
  simp [liftToVec]

theorem bitAsZ_xor (a b : Bool) :
    bitAsZ (xor a b) = bitAsZ a + bitAsZ b := by cases a <;> cases b <;> decide

theorem stateVec_false (d : Nat) : stateVec d (fun _ => false) = 0 := rfl

theorem stateVec_toggle {d : Nat} (x : State d) :
    stateVec d (toggle x) = stateVec d x + Pi.single 0 1 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change bitAsZ (!x 0) = bitAsZ (x 0) + ((Pi.single (0 : Fin (d+1)) (1 : ZMod 2)) : Vec2 (d+1)) 0
    simp only [Pi.single_eq_same]
    cases x 0 <;> decide
  · change bitAsZ ((toggle x) j.succ) =
      bitAsZ (x j.succ) + ((Pi.single (0 : Fin (d+1)) (1 : ZMod 2)) : Vec2 (d+1)) j.succ
    simp [toggle,j.succ_ne_zero]

theorem firstDifference_affine {d L : Nat} (ctrl : WindowTable d L) (i : Fin L)
    (affine : IsAffine2 (liftToVec (prefixOf ctrl i.castSucc))) (x : State d) :
    toggle (prefixOf ctrl i.castSucc x) =
      prefixOf ctrl i.castSucc ((stateVec d).symm (stateVec d x + stateVec d (firstDifference ctrl i))) := by
  let P := prefixOf ctrl i.castSucc
  let v := firstDifference ctrl i
  have init : (stateVec d).symm 0 = fun _ => false :=
    (stateVec d).symm_apply_eq.mpr (stateVec_false d).symm
  have atv : P v = toggle (P (fun _ => false)) := P.apply_symm_apply _
  apply (stateVec d).injective
  change stateVec d (toggle (P x)) = liftToVec P (stateVec d x + stateVec d v)
  rw [affine, stateVec_toggle]
  simp only [liftToVec,Equiv.symm_apply_apply,init]
  change stateVec d (P x) + Pi.single 0 1 =
    stateVec d (P x) + stateVec d (P v) - stateVec d (P (fun _ => false))
  rw [atv,stateVec_toggle]
  abel

theorem prefixAffine {d L : Nat} (ctrl : WindowTable d L)
    (rows : ∀ i, IsAffine2 (liftToVec (advance (ctrl i)))) (i : Fin (L+1)) :
    IsAffine2 (liftToVec (prefixOf ctrl i)) := by
  have general : ∀ n (hn : n≤L), IsAffine2 (liftToVec (prefixOf ctrl ⟨n,by omega⟩)) := by
    intro n
    induction n with
    | zero =>
      intro hn x y
      have same (z : Vec2 (d+1)) : liftToVec (prefixOf ctrl 0) z = z := by
        simp [liftToVec,prefixOf_zero]
      change liftToVec (prefixOf ctrl 0) (x+y) =
        liftToVec (prefixOf ctrl 0) x + liftToVec (prefixOf ctrl 0) y - liftToVec (prefixOf ctrl 0) 0
      simp only [same,sub_zero]
    | succ n ih =>
      intro hn
      let j : Fin L := ⟨n,by omega⟩
      change IsAffine2 (liftToVec (prefixOf ctrl j.succ))
      have e : (prefixOf ctrl j.succ : State d → State d) =
          advance (ctrl j) ∘ prefixOf ctrl j.castSucc := by
        funext x
        exact prefixOf_succ ctrl j x
      rw [e,liftToVec_comp]
      exact affine_comp (rows j) (ih (by omega))
  exact general i.val (by omega)


def tappedControl {d : Nat} (taps : Fin d → Bool) (bias : Bool) (tail : Fin d → Bool) : Bool :=
  (List.finRange d).foldl (fun b j => xor b (taps j && tail j)) bias

def tapSum {d : Nat} (taps : Fin d → Bool) (v : Vec2 d) : ZMod 2 :=
  ((List.finRange d).map fun j => bitAsZ (taps j) * v j).sum

theorem bitAsZ_and (a b : Bool) :
    bitAsZ (a && b) = bitAsZ a * bitAsZ b := by cases a <;> cases b <;> decide

theorem foldTap_toZ {d : Nat} (taps tail : Fin d → Bool) (rows : List (Fin d)) (init : Bool) :
    bitAsZ (rows.foldl (fun b j => xor b (taps j && tail j)) init) =
      bitAsZ init + (rows.map fun j => bitAsZ (taps j) * bitAsZ (tail j)).sum := by
  induction rows generalizing init with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons,ih,bitAsZ_xor,bitAsZ_and,List.map_cons,List.sum_cons, add_assoc]

theorem tapSum_add {d : Nat} (taps : Fin d → Bool) (x y : Vec2 d) :
    tapSum taps (x+y) = tapSum taps x + tapSum taps y := by
  unfold tapSum
  generalize List.finRange d = rows
  induction rows with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [ih,Pi.add_apply,mul_add]
    abel

theorem tapSum_zero {d : Nat} (taps : Fin d → Bool) : tapSum taps 0 = 0 := by
  unfold tapSum
  generalize List.finRange d = rows
  induction rows with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [ih]
    simp

theorem tapAdvance_match {d : Nat} (taps : Fin d → Bool) (bias : Bool) (s : State d) :
    advance (tappedControl taps bias) s =
      Fin.snoc (fun j : Fin d => s j.succ)
        ((List.finRange d).foldl (fun b j => xor b (taps j && s j.succ)) (xor (s 0) bias)) := by
  have e : xor (s 0) (tappedControl taps bias (fun j => s j.succ)) =
      (List.finRange d).foldl (fun b j => xor b (taps j && s j.succ)) (xor (s 0) bias) := by
    apply bitAsZ.injective
    simp only [tappedControl,bitAsZ_xor,foldTap_toZ,add_assoc]
  simp only [advance,e]

theorem tapAdvance_affine {d : Nat} (taps : Fin d → Bool) (bias : Bool) :
    IsAffine2 (liftToVec (advance (tappedControl taps bias))) := by
  have low (x : Vec2 (d+1)) (j : Fin d) :
      liftToVec (advance (tappedControl taps bias)) x j.castSucc = x j.succ := by
    have inv := congrFun ((stateVec d).apply_symm_apply x) j.succ
    change bitAsZ (((stateVec d).symm x) j.succ) = x j.succ at inv
    change bitAsZ (advance (tappedControl taps bias) ((stateVec d).symm x) j.castSucc) = _
    simpa only [advance,Fin.snoc_castSucc] using inv
  have high (x : Vec2 (d+1)) :
      liftToVec (advance (tappedControl taps bias)) x (Fin.last d) =
        x 0 + bitAsZ bias + tapSum taps (fun j => x j.succ) := by
    let s := (stateVec d).symm x
    have inv (j : Fin (d+1)) : bitAsZ (s j) = x j :=
      congrFun ((stateVec d).apply_symm_apply x) j
    change bitAsZ (advance (tappedControl taps bias) s (Fin.last d)) = _
    rw [tapAdvance_match,Fin.snoc_last,foldTap_toZ,bitAsZ_xor,inv 0]
    simp [tapSum, inv]
  intro x y
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Pi.add_apply,Pi.sub_apply,high,Pi.zero_apply,zero_add]
    have tail : (fun i : Fin d => x i.succ + y i.succ) =
      (fun i : Fin d => x i.succ) + (fun i : Fin d => y i.succ) := rfl
    rw [tail,tapSum_add]
    have z : (fun _ : Fin d => (0 : ZMod 2)) = 0 := rfl
    rw [z,tapSum_zero,add_zero]
    abel
  · simp only [Pi.add_apply,Pi.sub_apply,low,Pi.zero_apply,sub_zero]

theorem earlySupplyFromReset {d L : Nat} (wL : d+1 ≤ L) (short : L < 10*(d+1))
    (taps : Fin L → Fin d → Bool) (bias : Fin L → Bool)
    (reset : ∀ x : State d,
      (List.finRange L).foldl (fun (s : State d) row =>
        let z : Fin d → Bool := fun j => s j.succ
        let feedback := (List.finRange d).foldl
          (fun acc bit => xor acc (taps row bit && z bit)) (xor (s 0) (bias row))
        Fin.snoc (α := fun _ : Fin (d+1) => Bool) z feedback) x = x) :
    ∃ (ctrl : WindowTable d L) (P : PackingPrefix d L)
      (m : Nat) (edge : Fin m → State d × State d) (row : Fin m → Fin L),
      2^(d+1) * min L (2^(d+1)) ≤ 20*m ∧ Function.Injective edge ∧
      (∀ j k, (edge j).1 ≠ (edge k).2) ∧
      (∀ i x, P i.succ x = advance (ctrl i) (P i.castSucc x)) ∧
      (∀ x, P 0 x = x) ∧ (∀ x, P (Fin.last L) x = x) ∧
      (∀ j, toggle (P (row j).castSucc (edge j).1) = P (row j).castSucc (edge j).2) := by
  let ctrl : WindowTable d L := fun i => tappedControl (taps i) (bias i)
  let P := prefixOf ctrl
  let move := fun i => stateVec d (firstDifference ctrl i)
  have diag (i : Fin (d+1)) : move (Fin.castLE wL i) i = 1 := by
    change bitAsZ (firstDifference ctrl (Fin.castLE wL i) i) = 1
    have e := difference_diagonal ctrl (Fin.castLE wL i) i.isLt
    rw [show (⟨(Fin.castLE wL i).val,i.isLt⟩ : Fin (d+1)) = i from Fin.ext rfl] at e
    rw [e]
    rfl
  have upper (i j : Fin (d+1)) (h : i.val < j.val) : move (Fin.castLE wL i) j = 0 := by
    change bitAsZ (firstDifference ctrl (Fin.castLE wL i) j) = 0
    rw [difference_upper_zero ctrl (Fin.castLE wL i) j h]
    rfl
  obtain ⟨m,edge,row,large,inj,sep,ok⟩ := bankFromEarly P wL short move diag upper (by
    intro i _ x
    exact firstDifference_affine ctrl i
      (prefixAffine ctrl (fun r => tapAdvance_affine (taps r) (bias r)) _) x)
  refine ⟨ctrl,P,m,edge,row,large,inj,sep,prefixOf_succ ctrl,prefixOf_zero ctrl, ?_,ok⟩
  intro x
  unfold P
  rw [prefixOf_last]
  change (List.finRange L).foldl (fun s r => advance (tappedControl (taps r) (bias r)) s) x = x
  simp_rw [tapAdvance_match]
  exact reset x

theorem tailPerm_as_advance {d : Nat} (T : Equiv.Perm (State d))
    (tail : ∀ (s : State d) (j : Fin d), T s j.castSucc = s j.succ) :
    ∃ ctrl : (Fin d → Bool) → Bool, ∀ s, advance ctrl s = T s := by
  let ctrl := fun (z : Fin d → Bool) => T (Fin.cons false z) (Fin.last d)
  refine ⟨ctrl,?_⟩
  intro s
  refine Fin.consCases (fun b z => ?_) s
  have distinct : T (Fin.cons true z) (Fin.last d) ≠ T (Fin.cons false z) (Fin.last d) := by
    intro same
    have all : T (Fin.cons true z) = T (Fin.cons false z) := by
      funext i
      refine Fin.lastCases same (fun j => ?_) i
      rw [tail,tail,Fin.cons_succ,Fin.cons_succ]
    have h := congrFun (T.injective all) 0
    exact Bool.noConfusion (by simpa only [Fin.cons_zero] using h)
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [advance,Fin.snoc_last,Fin.cons_zero,Fin.cons_succ,ctrl]
    cases hb : b
    · simp
    · cases first : T (Fin.cons false z) (Fin.last d) <;>
        cases second : T (Fin.cons true z) (Fin.last d) <;> simp_all
  · rw [advance,Fin.snoc_castSucc,tail]

def leftMulMap {K F : Type} [Field K] [Field F] [Algebra K F] (a : F) : F →ₗ[K] F where
  toFun x := a*x
  map_add' x y := mul_add ..
  map_smul' c x := by
    change a*(c • x) = c • (a*x)
    simp only [Algebra.smul_def]
    ac_rfl

def mulPull {K F : Type} [Field K] [Field F] [Algebra K F]
    (a : F) (f : F →ₗ[K] K) : F →ₗ[K] K := f.comp (leftMulMap a)

theorem mulPull_at {K F : Type} [Field K] [Field F] [Algebra K F]
    (a : F) (f : F →ₗ[K] K) (x : F) : mulPull a f x = f (a*x) := rfl

def pullUnit {K F : Type} [Field K] [Field F] [Algebra K F] (g : Fˣ) :
    (F →ₗ[K] K) ≃ₗ[K] (F →ₗ[K] K) where
  toFun := mulPull (g : F)
  invFun := mulPull (↑g⁻¹ : F)
  left_inv f := by
    ext x
    simp only [mulPull_at,← mul_assoc,← Units.val_mul,mul_inv_cancel, Units.val_one,one_mul]
  right_inv f := by
    ext x
    simp only [mulPull_at,← mul_assoc,← Units.val_mul,inv_mul_cancel, Units.val_one,one_mul]
  map_add' f h := by ext x; rfl
  map_smul' a f := by ext x; rfl

theorem pull_iterate {K F : Type} [Field K] [Field F] [Algebra K F]
    (a : F) (f : F →ₗ[K] K) (x : F) (i : Nat) :
    ((mulPull a)^[i] f) x = f (a^i*x) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply',mulPull_at,ih,pow_succ,mul_assoc]

theorem fullCycleShift (d : Nat) :
    ∃ (T : Equiv.Perm (State d)) (ctrl : (Fin d → Bool) → Bool),
      (∀ x, T x = advance ctrl x) ∧ IsAffine2 (liftToVec T) ∧
      (liftToVec T 0 = 0) ∧
      Function.Injective (fun i : Fin (2^(d+1)-1) =>
        (T.symm^[i.val]) (toggle (fun _ => false))) := by
  let w := d+1
  let F := GaloisField 2 w
  let K := ZMod 2
  obtain ⟨g,pb,ord,origin,dim⟩ := primitivePowerBasis w (by dsimp [w]; omega)
  let B : Module.Basis (Fin w) K F := pb.basis.reindex (finCongr dim)
  let E : (Vec2 w) ≃ₗ[K] (F →ₗ[K] K) := B.constr K
  let read := (stateVec d).trans E.toEquiv
  let T : Equiv.Perm (State d) := (read.trans (pullUnit (K := K) g).toEquiv).trans read.symm
  have basisPow (i : Fin w) : B i = (g : F)^i.val := by
    rw [show B i = pb.basis ((finCongr dim).symm i) by simp [B,Module.Basis.reindex_apply]]
    simp [pb.basis_eq_pow,origin]
  have read_at (s : State d) (i : Fin w) : read s (B i) = bitAsZ (s i) := by
    exact B.constr_basis K (stateVec d s) i
  have act (s : State d) : read (T s) = mulPull (g : F) (read s) := by
    change read (read.symm (mulPull (g : F) (read s))) = _
    exact read.apply_symm_apply _
  have invAct (s : State d) : read (T.symm s) = mulPull (↑g⁻¹ : F) (read s) := by
    change read (read.symm (mulPull (↑g⁻¹ : F) (read s))) = _
    exact read.apply_symm_apply _
  have tail : ∀ s : State d, ∀ j : Fin d, T s j.castSucc = s j.succ := by
    intro s j
    apply bitAsZ.injective
    rw [← read_at (T s) j.castSucc, act,mulPull_at, ← read_at s j.succ]
    simp only [basisPow,Fin.val_castSucc,Fin.val_succ,pow_succ']
  obtain ⟨ctrl,ctrlEq⟩ := tailPerm_as_advance T tail
  let A := (E.trans (pullUnit (K := K) g)).trans E.symm
  have lin (v : Vec2 w) : liftToVec T v = A v := by
    change stateVec d ((read.symm) (mulPull (g : F) (read ((stateVec d).symm v)))) = _
    simp [read,A,pullUnit]
  have z : liftToVec T 0 = 0 := by rw [lin,map_zero]
  have aff : IsAffine2 (liftToVec T) := by
    intro x y
    rw [lin,lin,lin,z,sub_zero,map_add]
  let p : State d := toggle (fun _ => false)
  have fNZ : read p ≠ 0 := by
    intro eq
    have base : read (fun _ : Fin (d+1) => false) = 0 := by
      change E (stateVec d (fun _ => false)) = 0
      rw [stateVec_false,map_zero]
    have h := congrFun (read.injective (eq.trans base.symm)) 0
    simp [p,toggle] at h
  have iter (i : Nat) (x : F) :
      read ((T.symm^[i]) p) x = read p ((↑g⁻¹ : F)^i*x) := by
    induction i generalizing x with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply',invAct,mulPull_at,ih,pow_succ,mul_assoc]
  have invOrd : orderOf g⁻¹ = 2^w-1 := by rw [orderOf_inv,ord]
  refine ⟨T,ctrl,fun s => (ctrlEq s).symm,aff,z,?_⟩
  intro i j eq
  change (T.symm^[i.val]) p = (T.symm^[j.val]) p at eq
  have ip : i.val < orderOf g⁻¹ := by rw [invOrd]; exact i.isLt
  have jp : j.val < orderOf g⁻¹ := by rw [invOrd]; exact j.isLt
  have funEq : (fun x : F => read p ((↑g⁻¹ : F)^i.val*x)) =
      (fun x : F => read p ((↑g⁻¹ : F)^j.val*x)) := by
    funext x
    rw [← iter i.val x,← iter j.val x,eq]
  have h : (⟨i.val,ip⟩ : Fin (orderOf g⁻¹)) = ⟨j.val,jp⟩ :=
    dualOrbit_inj g⁻¹ (read p) fNZ funEq
  exact Fin.ext (congrArg (fun k : Fin (orderOf g⁻¹) => k.val) h)

def runTable {d L : Nat} (ctrl : WindowTable d L) (x : State d) : State d :=
  (List.ofFn ctrl).foldl (fun s c => advance c s) x

theorem finRange_map_control {A : Type} {L : Nat} (ctrl : Fin L → A) :
    (List.finRange L).map ctrl = List.ofFn ctrl := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

theorem runTable_eq_fold {d L : Nat} (ctrl : WindowTable d L) (x : State d) :
    runTable ctrl x = (List.finRange L).foldl (fun s row => advance (ctrl row) s) x := by
  unfold runTable
  rw [← finRange_map_control, List.foldl_map]

theorem runTable_append {d a b : Nat} (left : WindowTable d a) (right : WindowTable d b)
    (x : State d) : runTable (Fin.append left right) x = runTable right (runTable left x) := by
  simp [runTable,List.foldl_append]

theorem runTable_cast {d a b : Nat} (e : a = b) (ctrl : WindowTable d a) (x : State d) :
    runTable (fun i : Fin b => ctrl (Fin.cast e.symm i)) x = runTable ctrl x := by
  subst b
  rfl

theorem prefix_constant {d L t : Nat} (ctrl : WindowTable d L)
    (step : (Fin d → Bool) → Bool) (T : Equiv.Perm (State d))
    (Tmatch : ∀ x, T x = advance step x)
    (first : ∀ i : Fin L, i.val < t → ctrl i = step)
    (n : Nat) (hn : n ≤ L) (ht : n ≤ t) (x : State d) :
    prefixOf ctrl ⟨n,by omega⟩ x = (T^[n]) x := by
  induction n with
  | zero => exact prefixOf_zero ctrl x
  | succ n ih =>
    let r : Fin L := ⟨n,by omega⟩
    change prefixOf ctrl r.succ x = _
    have ih' : prefixOf ctrl r.castSucc x = (T^[n]) x := ih (by omega) (by omega)
    rw [prefixOf_succ,first r (by dsimp [r]; omega),← Tmatch,ih',Function.iterate_succ_apply']

theorem runTable_constant {d t : Nat} (step : (Fin d → Bool) → Bool)
    (T : Equiv.Perm (State d)) (Tmatch : ∀ x, T x = advance step x) (x : State d) :
    runTable (fun _ : Fin t => step) x = (T^[t]) x := by
  rw [runTable_eq_fold,← prefixOf_last]
  exact prefix_constant (t := t) _ step T Tmatch (fun _ _ => rfl) t (by omega) (by omega) x

theorem lift_pow_affine {d : Nat} (T : Equiv.Perm (State d)) (aff : IsAffine2 (liftToVec T)) (n : Nat) :
    IsAffine2 (liftToVec (T^n : Equiv.Perm (State d))) := by
  induction n with
  | zero =>
    intro x y
    rw [pow_zero]
    simp [liftToVec]
  | succ n ih =>
    rw [pow_succ]
    have mulEq : (⇑((T^n)*T) : State d → State d) = (T^n : Equiv.Perm (State d)) ∘ T := rfl
    rw [mulEq,liftToVec_comp]
    exact affine_comp ih aff

theorem pow_fix_zero {d : Nat} (T : Equiv.Perm (State d)) (zero : liftToVec T 0 = 0)
    (n : Nat) : (T^n) (fun _ => false) = (fun _ => false) := by
  have fixed : T (fun _ => false) = (fun _ => false) := by
    apply (stateVec d).injective
    rw [stateVec_false]
    have inp : (stateVec d).symm 0 = (fun _ => false) :=
      (stateVec d).symm_apply_eq.mpr (stateVec_false d).symm
    simpa only [liftToVec,inp] using zero
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ,Equiv.Perm.mul_apply,fixed,ih]

theorem power_inverse_at {X : Type} (T : Equiv.Perm X) (n : Nat) (x : X) :
    (T^n).symm x = (T.symm^[n]) x := by
  change ((T^n)⁻¹) x = _
  rw [← inv_pow]
  exact congrFun (Equiv.Perm.coe_pow T⁻¹ n) x

def RowSupply (d L : Nat) : Prop :=
    ∃ (ctrl : WindowTable d L) (P : PackingPrefix d L)
      (m : Nat) (edge : Fin m → State d × State d) (row : Fin m → Fin L),
      2^(d+1) * min L (2^(d+1)) ≤ 20*m ∧ Function.Injective edge ∧
      (∀ j k, (edge j).1 ≠ (edge k).2) ∧
      (∀ i x, P i.succ x = advance (ctrl i) (P i.castSucc x)) ∧
      (∀ x, P 0 x = x) ∧ (∀ x, P (Fin.last L) x = x) ∧
      (∀ j, toggle (P (row j).castSucc (edge j).1) = P (row j).castSucc (edge j).2)

theorem longSupplyFromRouting (d L : Nat) (large : 10*(d+1) ≤ L)
    (undo : ∀ T : Equiv.Perm (State d), ∃ ctrl : WindowTable d (4*(d+1)),
      ∀ x, runTable ctrl x = T x)
    (idle : ∀ n, d+1 ≤ n → ∃ ctrl : WindowTable d n, ∀ x, runTable ctrl x = x) :
    RowSupply d L := by
  let w := d+1
  let t := min (L-5*w) (2^w-1)
  let r := L-(t+4*w)
  have cap : t ≤ L-5*w := Nat.min_le_left _ _
  have tD : t ≤ 2^w-1 := Nat.min_le_right _ _
  have room : w ≤ r := by dsimp only [r]; omega
  have len : (t+4*w)+r = L := by dsimp only [r]; omega
  obtain ⟨T,step,e,aff,z,orbit⟩ := fullCycleShift d
  obtain ⟨middle,hm⟩ := undo (T^t).symm
  obtain ⟨pad,hp⟩ := idle r room
  let firstTable : WindowTable d t := fun _ => step
  let total := Fin.append (Fin.append firstTable middle) pad
  let ctrl : WindowTable d L := fun i => total (Fin.cast len.symm i)
  let P := prefixOf ctrl
  have first (i : Fin L) (hi : i.val<t) : ctrl i = step := by
    let a : Fin t := ⟨i.val,hi⟩
    have eq : Fin.cast len.symm i = Fin.castAdd r (Fin.castAdd (4*w) a) := Fin.ext rfl
    change total (Fin.cast len.symm i) = step
    rw [eq]
    simp [total,firstTable,w]
  have run (x : State d) : runTable ctrl x = x := by
    change runTable (fun i : Fin L => total (Fin.cast len.symm i)) x = x
    rw [runTable_cast len]
    change runTable (Fin.append (Fin.append firstTable middle) pad) x = _
    rw [runTable_append,runTable_append,hp,hm]
    change (T^t).symm (runTable (fun _ : Fin t => step) x) = x
    rw [runTable_constant step T e,← Equiv.Perm.coe_pow]
    exact (T^t).symm_apply_apply _
  have pre (i : Fin L) (hi : i.val < t) : P i.castSucc = T^i.val := by
    apply Equiv.ext
    intro x
    change prefixOf ctrl ⟨i.val,by omega⟩ x = _
    rw [Equiv.Perm.coe_pow]
    exact prefix_constant ctrl step T e first i.val (by omega) (by omega) x
  let move := fun i => stateVec d (firstDifference ctrl i)
  let p := toggle (fun _ : Fin (d+1) => false)
  have eqDiff (i : Fin L) (hi : i.val < t) :
      firstDifference ctrl i = (T.symm^[i.val]) p := by
    change (P i.castSucc).symm (toggle (P i.castSucc (fun _ => false))) = _
    rw [pre i hi,pow_fix_zero T z,power_inverse_at]
  have noFalse : p ≠ (fun _ => false) := by
    intro q
    have e := congrFun q 0
    simp [p,toggle] at e
  have nz (i : Fin L) (hi : i.val<t) : move i ≠ 0 := by
    intro h
    have f : firstDifference ctrl i = (fun _ => false) := by
      apply (stateVec d).injective
      rw [stateVec_false]
      exact h
    apply noFalse
    rw [eqDiff i hi,← power_inverse_at] at f
    have eq := congrArg (T^i.val) f
    simpa only [Equiv.apply_symm_apply,pow_fix_zero T z] using eq
  have distinct (i j : Fin L) (hi : i.val<t) (hj : j.val<t) (q : move i = move j) : i=j := by
    have h := (stateVec d).injective q
    rw [eqDiff i hi,eqDiff j hj] at h
    have eq : (⟨i.val,by omega⟩ : Fin (2^w-1)) = ⟨j.val,by omega⟩ := orbit h
    exact Fin.ext (congrArg (fun a : Fin (2^w-1) => a.val) eq)
  have flip (i : Fin L) (hi : i.val<t) (x : State d) :
      toggle (P i.castSucc x) = P i.castSucc ((stateVec d).symm (stateVec d x + move i)) := by
    apply firstDifference_affine
    rw [show prefixOf ctrl i.castSucc = T^i.val from pre i hi]
    exact lift_pow_affine T aff i.val
  obtain ⟨m,edge,row,hm,inj,sep,ok⟩ := bankFromLong P large rfl move nz distinct flip
  refine ⟨ctrl,P,m,edge,row,hm,inj,sep,prefixOf_succ ctrl,prefixOf_zero ctrl,?_,ok⟩
  intro x
  rw [show P (Fin.last L) x = (List.finRange L).foldl (fun s j => advance (ctrl j) s) x from prefixOf_last ctrl x,
    ← runTable_eq_fold]
  exact run x

theorem acceptedTapReset (d L : Nat) (wL : d+1 ≤ L) :
    ∃ (taps : Fin L → Fin d → Bool) (bias : Fin L → Bool),
      ∀ x : State d, (List.finRange L).foldl (fun (s : State d) row =>
        let z : Fin d → Bool := fun j => s j.succ
        let feedback := (List.finRange d).foldl
          (fun acc bit => xor acc (taps row bit && z bit)) (xor (s 0) (bias row))
        Fin.snoc (α := fun _ : Fin (d+1) => Bool) z feedback) x = x := by
  obtain ⟨taps,bias,good⟩ :=
    (PEqualNP.Outside.L_lib_471 d L (fun _ => false)).mpr (Or.inl wL)
  exact ⟨taps,bias,fun x => by simpa using good x⟩

theorem acceptedIdle (d L : Nat) (wL : d+1 ≤ L) :
    ∃ ctrl : WindowTable d L, ∀ x, runTable ctrl x = x := by
  obtain ⟨taps,bias,good⟩ := acceptedTapReset d L wL
  refine ⟨fun j => tappedControl (taps j) (bias j),?_⟩
  intro x
  rw [runTable_eq_fold]
  simp_rw [tapAdvance_match]
  exact good x

theorem acceptedRouting (d : Nat) (T : Equiv.Perm (State d)) :
    ∃ ctrl : WindowTable d (4*(d+1)), ∀ x, runTable ctrl x = T x := by
  obtain ⟨ctrl,good⟩ := PEqualNP.Outside.L_lib_394 d T
  exact ⟨ctrl, fun x => by simpa only [runTable_eq_fold,advance] using good x⟩

theorem chooseSupply (d L : Nat) (wL : d+1 ≤ L) : RowSupply d L := by
  by_cases small : L < 10*(d+1)
  · obtain ⟨taps,bias,reset⟩ := acceptedTapReset d L wL
    exact earlySupplyFromReset wL small taps bias reset
  · exact longSupplyFromRouting d L (by omega) (acceptedRouting d) (acceptedIdle d)

end PEqualNP.Outside.L_lib_540_aux

theorem PEqualNP.Outside.L_lib_540 :
∀ (d L : Nat),
  let w := d+1
  let D := 2^w
  w ≤ L →
    let X := Fin w → Bool
    let S := Fin L × (Fin (w+1) → Bool)
    ∃ (m : Nat) (edge : Fin m → X × X) (base : S → Bool) (port : Bool → Fin m → S),
      D * min L D ≤ 20*m ∧ Function.Injective edge ∧
      (∀ u v : Fin m, (edge u).1 ≠ (edge v).2) ∧
      ∀ rev : Bool, Function.Injective (port rev) ∧ (∀ j, base (port rev j) = false) ∧
        ∀ enabled : Finset (Fin m), ∀ x y : X,
          (Finset.univ.filter (fun word : Fin (L+d+1) → Bool =>
            (∀ pos : Fin w,
              word (Fin.ofNat (L+d+1) pos.val) = x pos ∧
              word (Fin.ofNat (L+d+1) (L+pos.val)) = y pos) ∧
            ∀ i : Fin L,
              let s : S := (i,fun off => word (Fin.ofNat (L+d+1) (i.val+off.val)))
              base s = true ∨ s ∈ enabled.image (port rev))).card =
                (if x = y then 1 else 0) +
                (if ∃ j ∈ enabled, edge j = (if rev then (y,x) else (x,y)) then 1 else 0) := by
  intro d L
  dsimp only
  intro wL
  obtain ⟨ctrl,P,m,edge,row,h,inj,sep,steps,beginning,ending,flip⟩ :=
    PEqualNP.Outside.L_lib_540_aux.chooseSupply d L wL
  refine ⟨m,edge,PEqualNP.Outside.L_lib_540_aux.tableBase ctrl,
    fun rev => PEqualNP.Outside.L_lib_540_aux.portsOf ctrl P (fun j => PEqualNP.Outside.L_lib_540_aux.orientPair rev (edge j)) row,
    h,inj,sep,?_⟩
  exact PEqualNP.Outside.L_lib_540_aux.packFromRows ctrl P edge row steps beginning ending flip inj sep
