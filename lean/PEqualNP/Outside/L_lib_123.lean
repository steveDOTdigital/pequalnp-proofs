import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_123

open PEqualNP.Library

-- Any exponent gap would already give a gap of one at its lower endpoint.
lemma adjacent_exponents :
    (∃ p q : ℕ, 1 ≤ p ∧ p < q ∧ FP3 p q) ↔ ∃ p : ℕ, 1 ≤ p ∧ FP3 p (p + 1) := by
  constructor
  · rintro ⟨p, q, hp, hpq, fast⟩
    refine ⟨p, hp, ?_⟩
    intro L hL
    apply fast L
    obtain ⟨c, f, correct, M, time⟩ := hL
    refine ⟨c, f, correct, M, fun n => (time n).trans ?_⟩
    exact Nat.add_le_add_right (Nat.mul_le_mul_left c
      (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_right n hpq))) c
  · rintro ⟨p, hp, h⟩
    exact ⟨p, p + 1, hp, Nat.lt_succ_self _, h⟩

-- The verifier receives the three blocks concatenated, without delimiters.
def unpack (s : ℕ) (test : List Bool → List Bool → List Bool → Prop) (w : List Bool) : Prop :=
  test (w.take s) ((w.drop s).take s) ((w.drop s).drop s)

private lemma unpack_append {s : ℕ} {a b : List Bool} (ha : a.length = s)
    (hb : b.length = s) (c : List Bool) (test : List Bool → List Bool → List Bool → Prop) :
    unpack s test (a ++ (b ++ c)) ↔ test a b c := by
  simp only [unpack, ← ha, List.take_left, List.drop_left]
  rw [ha, ← hb, List.take_left, List.drop_left]

lemma three_blocks (s : ℕ) (test : List Bool → List Bool → List Bool → Prop) :
    Alt 3 s (unpack s test) ↔ ∃ a : List Bool, a.length = s ∧
      ∀ b : List Bool, b.length = s → ∃ c : List Bool, c.length = s ∧ test a b c := by
  classical
  simp only [Alt, not_exists, not_and, not_forall, not_not, List.append_nil]
  apply exists_congr
  intro a
  apply and_congr_right
  intro ha
  apply forall_congr'
  intro b
  apply forall_congr'
  intro hb
  apply exists_congr
  intro c
  constructor
  · rintro ⟨hc, ok⟩
    exact ⟨hc, (unpack_append ha hb c test).mp ok⟩
  · rintro ⟨hc, ok⟩
    exact ⟨hc, (unpack_append ha hb c test).mpr ok⟩

-- Checkpoint i occupies width consecutive bits in the first block.
def endpoint (width : ℕ) (commitment : List Bool) (i : ℕ) : Fin width → Bool :=
  fun j => commitment[i * width + j.val]?.getD false

private lemma encode_endpoints (s count width : ℕ) (hw : 0 < width)
    (fits : count * width ≤ s) (codes : ℕ → Fin width → Bool) :
    ∃ a : List Bool, a.length = s ∧ ∀ i < count, endpoint width a i = codes i := by
  let bit (k : Fin s) := codes (k.val / width) ⟨k.val % width, Nat.mod_lt _ hw⟩
  refine ⟨List.ofFn bit, List.length_ofFn, ?_⟩
  intro i hi
  funext j
  have room : i * width + j.val < s := calc
    _ < (i + 1) * width := by rw [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ s := (Nat.mul_le_mul_right width hi).trans fits
  have index : (i * width + j.val) / width = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  simp [endpoint, room, bit, index, Nat.mod_eq_of_lt j.isLt]

-- The challenge uses its number of true bits to select an interval.
private lemma select_interval {s i : ℕ} (hi : i ≤ s) :
    ∃ b : List Bool, b.length = s ∧ b.count true = i := by
  refine ⟨List.replicate i true ++ List.replicate (s - i) false, ?_, ?_⟩
  · simp; omega
  · simp [List.count_replicate]

-- At index zero the starting state is public. Later endpoints are decoded
-- from the same commitment for every challenge.
def atBoundary {C : Type} {width : ℕ} (start : C) (decode : (Fin width → Bool) → C)
    (a : List Bool) : ℕ → C
  | 0 => start
  | i + 1 => decode (endpoint width a i)

def segmentTest {C : Type} {width : ℕ} (start : C) (decode : (Fin width → Bool) → C)
    (count : ℕ) (accept : C → Prop) (localTest : C → C → List Bool → Prop)
    (a b c : List Bool) : Prop :=
  let boundary := atBoundary start decode a
  accept (boundary count) ∧
    (b.count true < count → localTest (boundary (b.count true)) (boundary (b.count true + 1)) c)

-- This is correctness of the protocol. The running time of a concrete
-- implementation of decoding and checking is a separate obligation.
lemma checkpoint_protocol {C : Type} (step : C → C) (start : C) (accept : C → Prop)
    (count span width s : ℕ) (hw : 0 < width) (fits : count * width ≤ s)
    (decode : (Fin width → Bool) → C)
    (encodable : ∀ i < count, ∃ code, decode code = step^[span * (i+1)] start)
    (localTest : C → C → List Bool → Prop)
    (local_spec : ∀ u v, (∃ c : List Bool, c.length = s ∧ localTest u v c) ↔ step^[span] u = v) :
    Alt 3 s (unpack s (segmentTest start decode count accept localTest)) ↔
      accept (step^[span * count] start) := by
  classical
  rw [three_blocks]
  constructor
  · rintro ⟨a, _, answers⟩
    let boundary := atBoundary start decode a
    have consistent (i : ℕ) (hi : i < count) : step^[span] (boundary i) = boundary (i+1) := by
      have hc : count ≤ s := (Nat.le_mul_of_pos_right count hw).trans fits
      obtain ⟨b, hb, pick⟩ := select_interval (hi.le.trans hc)
      obtain ⟨c, hlen, _, check⟩ := answers b hb
      exact (local_spec _ _).mp ⟨c, hlen, by simpa [pick] using check (pick ▸ hi)⟩
    have follows (i : ℕ) (hi : i ≤ count) : boundary i = step^[span * i] start := by
      induction i with
      | zero => simp [boundary, atBoundary]
      | succ i ih =>
        rw [← consistent i hi, ih (by omega), Nat.mul_succ, Nat.add_comm,
          Function.iterate_add_apply]
    obtain ⟨_, _, final, _⟩ := answers (List.replicate s false) (by simp)
    exact follows count le_rfl ▸ final
  · intro final
    let codes (i : ℕ) : Fin width → Bool :=
      if h : i < count then (encodable i h).choose else fun _ => false
    obtain ⟨a, ha, readback⟩ := encode_endpoints s count width hw fits codes
    have ends (i : ℕ) (hi : i ≤ count) : atBoundary start decode a i = step^[span * i] start := by
      cases i with
      | zero => simp [atBoundary]
      | succ i =>
        rw [atBoundary, readback i hi]
        simpa [codes, show i < count from hi] using (encodable i hi).choose_spec
    refine ⟨a, ha, fun b _ => ?_⟩
    by_cases selected : b.count true < count
    · have advance : step^[span] (atBoundary start decode a (b.count true)) =
          atBoundary start decode a (b.count true + 1) := by
        rw [ends _ selected.le, ends _ selected, Nat.mul_succ, Nat.add_comm,
          Function.iterate_add_apply]
      obtain ⟨c, hc, checked⟩ := (local_spec _ _).mpr advance
      exact ⟨c, hc, ends count le_rfl ▸ final, fun _ => checked⟩
    · exact ⟨List.replicate s false, by simp, ends count le_rfl ▸ final,
        fun h => (selected h).elim⟩

-- For the exponent pair two and three, commitments can hold this many
-- fixed-width endpoints, and the selected segment has exactly one block's length.
lemma checkpoint_budget (m : ℕ) :
    (2^m : ℕ) * 2^m = 2^(2*m) ∧ (2^(2*m) : ℕ) * 2^m = 2^(3*m) := by
  constructor <;> rw [← pow_add] <;> congr 1 <;> omega

-- A halted configuration retains its output until the end of a padded run.
def tick {C : Type} (next : C → Option C) (u : C) : C := (next u).getD u

private lemma tick_exact {C : Type} (next : C → Option C) (n : ℕ) (a b : C)
    (h : (flip bind next)^[n] (some a) = some b) : (tick next)^[n] a = b := by
  induction n generalizing a with
  | zero => exact Option.some.inj h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    cases e : next a with
    | some c =>
      rw [show flip bind next (some a) = some c from e] at h
      simpa [tick, e] using ih c h
    | none =>
      rw [show flip bind next (some a) = none from e,
        Function.iterate_fixed (f := flip bind next) (x := none) rfl n] at h
      contradiction

lemma tick_to_deadline {C : Type} (next : C → Option C) (a b : C) (deadline : ℕ)
    (run : StateTransition.EvalsToInTime next a (some b) deadline) (halted : next b = none) :
    (tick next)^[deadline] a = b := by
  have padding := Nat.sub_add_cancel run.steps_le_m
  rw [← padding, Function.iterate_add_apply, tick_exact next run.steps a b run.evals_in_steps]
  exact Function.iterate_fixed (by simp [tick, halted]) _

-- This applies to the project's actual machine output convention.
lemma machine_at_deadline (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (deadline : ℕ)
    (run : Turing.TM2OutputsInTime tm input (some output) deadline) :
    (tick tm.step)^[deadline] (Turing.initList tm input) = Turing.haltList tm output :=
  tick_to_deadline tm.step _ _ deadline run rfl

-- At fixed exponents, constants in the original time class still fit the schedule.
lemma padded_budget (K m : ℕ) :
    K * 2^(3*m) + K ≤ (K * 2^(2*m) + K) * 2^m := by
  rw [Nat.add_mul, Nat.mul_assoc, (checkpoint_budget m).2]
  exact Nat.add_le_add_left (Nat.le_mul_of_pos_right K (by positivity)) _

-- Even with uneven intervals, recording a stack verbatim at every boundary
-- fails on a high peak. Before the peak here the stack grows by one each step.
lemma literal_peak_bound (times : ℕ → ℕ) (count peak budget : ℕ)
    (start : times 0 = 0) (covers : peak ≤ times count)
    (gap : ∀ i < count, times (i+1) ≤ times i + budget)
    (raw : ∀ i ≤ count, times i ≤ peak → times i ≤ budget) :
    peak ≤ 2 * budget := by
  by_contra! too_high
  have before (i : ℕ) (hi : i ≤ count) : times i < peak := by
    induction i with
    | zero => omega
    | succ i ih =>
      have prior := ih (by omega)
      have small := raw i (by omega) prior.le
      have jump := gap i hi
      omega
  exact (before count le_rfl).not_ge covers

-- Constants and additive padding cannot turn a power gap into a constant factor.
lemma power_gap (p q K : ℕ) (pq : p < q) :
    ∃ m₀, ∀ m ≥ m₀, 4 * (K * 2^(p*m) + K) < 2^(q*m) := by
  refine ⟨8*K + 1, ?_⟩
  intro m hm
  have grows : 8*K < 2^m := lt_of_lt_of_le (by omega : 8*K < m) (Nat.le_of_lt (Nat.lt_two_pow_self))
  have pos : 0 < 2^(p*m) := by positivity
  have larger : 2^(p*m) * 2^m ≤ (2 : ℕ)^(q*m) := by
    rw [← pow_add, ← Nat.succ_mul]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right m pq)
  apply lt_of_lt_of_le _ larger
  have scale := Nat.mul_lt_mul_of_pos_left grows pos
  have repeatK := Nat.mul_le_mul_left K (show 1 ≤ 2^(p*m) from pos)
  nlinarith

-- A rule is a bit, the empty word, or a join of two earlier rules.
-- Listing the newest rule first lets either operand be reused arbitrarily.
def joinProgram : List (List Bool) → Prop
  | [] => True
  | x :: prev => joinProgram prev ∧
    (x.length ≤ 1 ∨ ∃ a ∈ prev, ∃ b ∈ prev, x = a ++ b)

def factors (k : ℕ) (x : List Bool) : Finset (List Bool) :=
  (Finset.range (x.length + 1 - k)).image fun i => (x.drop i).take k

private def seen (k : ℕ) : List (List Bool) → Finset (List Bool)
  | [] => ∅
  | x :: prev => factors k x ∪ seen k prev

private lemma seen_includes {x : List Bool} {program : List (List Bool)}
    (k : ℕ) (hm : x ∈ program) : factors k x ⊆ seen k program := by
  induction program with
  | nil => simp at hm
  | cons y ys ih =>
    rcases List.mem_cons.mp hm with rfl | prev
    · exact Finset.subset_union_left
    · exact (ih prev).trans Finset.subset_union_right

private def crossing (k : ℕ) (a b : List Bool) : Finset (List Bool) :=
  (Finset.range (k - 1)).image fun d => ((a.drop (a.length - (d+1))) ++ b).take k

-- A new length-k factor must straddle the join, using between one and k-1
-- letters from the left operand. Each such split gives at most one factor.
private lemma factors_join (k : ℕ) (a b : List Bool) :
    factors k (a ++ b) ⊆ (factors k a ∪ factors k b) ∪ crossing k a b := by
  intro w hw
  obtain ⟨i, hr, rfl⟩ := Finset.mem_image.mp hw
  have valid := Finset.mem_range.mp hr
  rw [List.length_append] at valid
  by_cases left : i + k ≤ a.length
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
    rw [List.drop_append_of_le_length (by omega : i ≤ a.length), List.take_append_of_le_length]
    simp; omega
  · by_cases right : a.length ≤ i
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨i - a.length, Finset.mem_range.mpr (by omega), ?_⟩
      simp [List.drop_append, List.drop_eq_nil_of_le right]
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨a.length - i - 1, Finset.mem_range.mpr (by omega), ?_⟩
      rw [List.drop_append_of_le_length (by omega : i ≤ a.length)]
      simp only [show a.length - (a.length - i - 1 + 1) = i by omega]

lemma join_factor_bound (k : ℕ) (hk : 2 ≤ k) (program : List (List Bool))
    (valid : joinProgram program) : (seen k program).card ≤ program.length * (k-1) := by
  induction program with
  | nil => simp [seen]
  | cons x prev ih =>
    obtain ⟨old, rule⟩ := valid
    have budget := ih old
    simp only [seen, List.length_cons, Nat.add_mul, one_mul]
    rcases rule with short | ⟨a, ha, b, hb, rfl⟩
    · have no_factors : factors k x = ∅ := by
        simp [factors, show x.length + 1 - k = 0 by omega]
      rw [no_factors, Finset.empty_union]
      omega
    · have included : factors k (a ++ b) ∪ seen k prev ⊆ seen k prev ∪ crossing k a b := by
        apply Finset.union_subset
        · intro w hw
          rcases Finset.mem_union.mp (factors_join k a b hw) with oldFactor | newFactor
          · apply Finset.mem_union_left
            rcases Finset.mem_union.mp oldFactor with left | right
            · exact seen_includes k ha left
            · exact seen_includes k hb right
          · exact Finset.mem_union_right _ newFactor
        · exact Finset.subset_union_left
      have cross : (crossing k a b).card ≤ k - 1 :=
        Finset.card_image_le.trans_eq (Finset.card_range _)
      exact (Finset.card_le_card included).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add budget cross))

-- This stack is explicit: concatenate all k-bit strings once. Its order
-- has no effect on the lower bound.
private noncomputable def words (k : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin k → Bool)).image List.ofFn

private def enumerateWords : ℕ → List (List Bool)
  | 0 => [[]]
  | k+1 => (enumerateWords k).map (false :: ·) ++ (enumerateWords k).map (true :: ·)

private lemma enumerate_spec (k : ℕ) (w : List Bool) :
    w ∈ enumerateWords k ↔ w.length = k := by
  induction k generalizing w with
  | zero => simp [enumerateWords]
  | succ k ih =>
    cases w with
    | nil => simp [enumerateWords]
    | cons b tail => cases b <;> simp [enumerateWords, ih]

private lemma enumerate_count (k : ℕ) : (enumerateWords k).length = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [enumerateWords, ih, pow_succ]; omega

def catalogue (k : ℕ) : List Bool := (enumerateWords k).flatten

private lemma word_count (k : ℕ) : (words k).card = 2^k := by
  rw [words, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

private lemma word_length {k : ℕ} {w : List Bool} (h : w ∈ words k) : w.length = k := by
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h
  exact List.length_ofFn

lemma catalogue_length (k : ℕ) : (catalogue k).length = k * 2^k := by
  rw [catalogue, List.length_flatten]
  have sizes : (enumerateWords k).map List.length = (enumerateWords k).map (fun _ => k) :=
    List.map_congr_left fun w h => (enumerate_spec k w).mp h
  simp [sizes, enumerate_count, Nat.mul_comm]

lemma catalogue_requires_rules (k : ℕ) (hk : 2 ≤ k) (program : List (List Bool))
    (valid : joinProgram program) (holds : catalogue k ∈ program) :
    2^k ≤ program.length * (k-1) := by
  have allWords : words k ⊆ factors k (catalogue k) := by
    intro w hw
    have len := word_length hw
    obtain ⟨pre, post, split⟩ := List.mem_iff_append.mp ((enumerate_spec k w).mpr len)
    unfold catalogue factors
    rw [split, List.flatten_append, List.flatten_cons]
    refine Finset.mem_image.mpr ⟨pre.flatten.length, Finset.mem_range.mpr ?_, ?_⟩
    · simp only [List.length_append]; omega
    · simp [← len]
  rw [← word_count]
  exact (Finset.card_le_card (allWords.trans (seen_includes k holds))).trans
    (join_factor_bound k hk program valid)

private lemma square_le_exp (m : ℕ) (hm : 4 ≤ m) : m*m ≤ 2^m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [pow_succ]
    have gap : 0 ≤ (n : ℤ) - 3 := by omega
    have prod := mul_nonneg gap (show 0 ≤ (n : ℤ) + 1 by positivity)
    zify at ih ⊢
    nlinarith

-- For every proposed power saving and constant allowance, an explicit stack
-- fits within the original time scale yet needs more join rules than the
-- entire shorter witness block has bits, even at one bit per rule.
lemma join_compression_obstruction (p q K : ℕ) (pq : p < q) :
    ∃ n k : ℕ, 2 ≤ k ∧ (catalogue k).length ≤ 2^(q*n) ∧
      ∀ program, joinProgram program → catalogue k ∈ program →
        K * 2^(p*n) + K < program.length := by
  let m := (2*K + 1) * (p+q+1) + 4
  let n := 2*m
  let k := (p+q)*m
  have m_big : 4 ≤ m := by dsimp [m]; omega
  have q_pos : 1 ≤ p+q := by omega
  have k_big : 2 ≤ k := by dsimp [k]; nlinarith
  have sq := square_le_exp m m_big
  have coeff : 2*K*(p+q) < m := by dsimp [m]; nlinarith
  have coef2 : p+q ≤ m := by dsimp [m]; nlinarith
  have width : k ≤ 2^m := (Nat.mul_le_mul_right m coef2).trans sq
  have ampl : 2*K*k < 2^m := by
    rw [show 2*K*k = (2*K*(p+q))*m by dsimp [k]; ring]
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right coeff (by omega)) sq
  have left_gap : p*n+m ≤ k := by
    dsimp [n,k]
    have h := Nat.mul_le_mul_right m pq
    nlinarith
  have right_gap : k+m ≤ q*n := by
    dsimp [n,k]
    have h := Nat.mul_le_mul_right m pq
    nlinarith
  refine ⟨n, k, k_big, ?_, ?_⟩
  · rw [catalogue_length]
    calc k * 2^k ≤ 2^m * 2^k := Nat.mul_le_mul_right _ width
         _ = 2^(m+k) := (pow_add _ _ _).symm
         _ ≤ 2^(q*n) := Nat.pow_le_pow_right (by decide) (by omega)
  · intro program valid holds
    have lower := catalogue_requires_rules k k_big program valid holds
    by_contra! small
    have one : 1 ≤ 2^(p*n) := Nat.pow_pos (by decide)
    have cap : program.length ≤ (2*K)*2^(p*n) := by
      have hk := Nat.mul_le_mul_left K one
      nlinarith
    have impossible : program.length * (k-1) < 2^k := calc
      _ ≤ ((2*K)*2^(p*n))*k := Nat.mul_le_mul cap (by omega)
      _ = 2^(p*n)*(2*K*k) := by ring
      _ < 2^(p*n)*2^m := Nat.mul_lt_mul_of_pos_left ampl one
      _ = 2^(p*n+m) := (pow_add _ _ _).symm
      _ ≤ 2^k := Nat.pow_le_pow_right (by decide) left_gap
    omega

-- Every actual checkpoint has a short description: its index in the run.
-- This decoder can cost the whole original time because it starts from time zero.
def replayIndex {C : Type} (step : C → C) (start : C) (span width : ℕ)
    (bits : Fin width → Bool) : C :=
  step^[span * ((∑ j : Fin width, if bits j then j.val else 0) + 1)] start

lemma replay_encodes {C : Type} (step : C → C) (start : C) (span width : ℕ)
    (i : ℕ) (hi : i < width) :
    ∃ bits, replayIndex step start span width bits = step^[span * (i+1)] start := by
  let j : Fin width := ⟨i, hi⟩
  refine ⟨fun k => decide (k = j), ?_⟩
  simp [replayIndex, j]

-- Perfect logical certificates already exist with index descriptions and
-- deterministic replay. The definition of SigmaV additionally charges the
-- time of a single machine deciding the relation on every encoded input.
lemma replay_protocol {C : Type} (step : C → C) (start : C) (accept : C → Prop) (m : ℕ) :
    Alt 3 (2^(2*m)) (unpack (2^(2*m))
      (segmentTest start (replayIndex step start (2^(2*m)) (2^m)) (2^m) accept
        (fun u v _ => step^[2^(2*m)] u = v))) ↔ accept (step^[2^(3*m)] start) := by
  rw [← (checkpoint_budget m).2]
  apply checkpoint_protocol step start accept (2^m) (2^(2*m)) (2^m) (2^(2*m)) (by positivity)
    (checkpoint_budget m).1.le _ (replay_encodes step start _ _)
  intro u v
  constructor
  · rintro ⟨_, _, eq⟩
    exact eq
  · intro eq
    exact ⟨List.replicate (2^(2*m)) false, by simp, eq⟩

-- A fixed input-independent transcript exposes the cost of the replay decoder.
-- Only the last commitment bit is one. The all-ones challenge lies outside
-- the valid interval indices, so the checker must answer using the final state.
def marker (s : ℕ) : List Bool := List.ofFn fun i : Fin s => decide (i.val + 1 = s)

lemma replay_on_marker {C : Type} (step : C → C) (start : C) (accept : C → Prop)
    (width span : ℕ) (hw : 0 < width) :
    let s := width * width
    unpack s (segmentTest start (replayIndex step start span width) width accept
      (fun u v _ => step^[span] u = v))
      (marker s ++ (List.replicate s true ++ List.replicate s false)) ↔
      accept (step^[span * width] start) := by
  dsimp only
  rw [unpack_append (by simp [marker]) (List.length_replicate ..)]
  let last : Fin width := ⟨width-1, by omega⟩
  have split : (width-1)*width + width = width*width := by
    calc _ = (width-1+1)*width := by ring
         _ = _ := by rw [Nat.sub_add_cancel hw]
  have bits : endpoint width (marker (width*width)) (width-1) = fun j => decide (j = last) := by
    funext j
    have room : (width-1)*width + j.val < width*width := by omega
    simp only [endpoint, marker, List.getElem?_ofFn, room, dite_eq_left, Option.getD_some]
    congr 1
    apply propext
    rw [Fin.ext_iff]
    change _ ↔ j.val = width-1
    omega
  have finalState : atBoundary start (replayIndex step start span width)
      (marker (width*width)) width = step^[span * width] start := by
    conv_lhs => arg 4; rw [← Nat.sub_add_cancel hw]
    rw [atBoundary, bits]
    simp [replayIndex, last, Nat.sub_add_cancel hw]
  have large : width ≤ width*width := Nat.le_mul_of_pos_right _ hw
  simp [segmentTest, finalState, Nat.not_lt.mpr large]

end PEqualNP.Outside.L_lib_123
