import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12254_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenSignedSlice

abbrev Signal (α : Type) := α → Bool
def inv {α} (a : Signal α) : Signal α := fun x => !(a x)
def meet {α} (a b : Signal α) : Signal α := fun x => a x && b x

-- A pool stores both polarities of every paid AND. Old wires remain available.
inductive Run {α : Type} (start : List (Signal α)) : ℕ → List (Signal α) → Prop where
  | nil : Run start 0 start
  | gate {k w} (h : Run start k w) {a b} (ha : a ∈ w) (hb : b ∈ w) :
      Run start (k+1) (w ++ [meet a b, inv (meet a b)])

theorem Run.keep {α} {s w : List (Signal α)} {k} (h : Run s k w) :
    ∀ v ∈ s, v ∈ w := by
  induction h with
  | nil => exact fun _ h => h
  | gate h _ _ ih => exact fun v hv => List.mem_append_left _ (ih v hv)

theorem Run.comp {α} {s w u : List (Signal α)} {k j} (h : Run s k w) (h' : Run w j u) :
    Run s (k+j) u := by
  induction h' with
  | nil => exact h
  | gate h' ha hb ih => exact Run.gate ih ha hb

structure Wire (α : Type) where
  f : Signal α
  lo : Bool
  hi : Bool

def K {α} (b : Bool) : Wire α := ⟨fun _ => b,b,b⟩
def neg {α} (a : Wire α) : Wire α := ⟨inv a.f,!a.lo,!a.hi⟩
def conj {α} (a b : Wire α) : Wire α := ⟨meet a.f b.f,a.lo && b.lo,a.hi && b.hi⟩
def disj {α} (a b : Wire α) : Wire α := neg (conj (neg a) (neg b))

def Good {α} (w : List (Signal α)) (a : Wire α) : Prop := a.f ∈ w ∧ inv a.f ∈ w
def Stable {α} (a : Wire α) : Prop := (∃ b, ∀ x, a.f x = b) ∨ a.lo = a.hi

theorem goodNeg {α} {w : List (Signal α)} {a} (h : Good w a) : Good w (neg a) := by
  refine ⟨h.2,?_⟩
  have eq : inv (inv a.f) = a.f := by funext x; simp [inv]
  change inv (inv a.f) ∈ w
  rw [eq]
  exact h.1

theorem stableNeg {α} {a : Wire α} (h : Stable a) : Stable (neg a) := by
  rcases h with ⟨b,hb⟩ | eq
  · exact Or.inl ⟨!b,fun x => by simp [neg,inv,hb]⟩
  · exact Or.inr (congrArg Bool.not eq)

def Eval {α} (op : GateOp) (args : List (Wire α)) : Wire α :=
  ⟨fun x => op.eval (args.map fun a => a.f x),op.eval (args.map Wire.lo),op.eval (args.map Wire.hi)⟩

def Paid (g : Gate) : ℕ :=
  if g.op.eval [false] then 0 else if g.inputs.length = 2 then 1 else 0

def Effect {α} (w : List (Signal α)) (n : ℕ) (a : Wire α) (inputs : List (Wire α)) : Prop :=
  ∃ c t, Run w c t ∧ c ≤ n ∧ Good t a ∧
    (c = n → (∀ u ∈ inputs, Stable u) → Stable a)

private theorem bin {α} (w : List (Signal α)) (base : ∀ b, Good w (K b)) (a b : Wire α)
    (ha : Good w a) (hb : Good w b) : Effect w 1 (conj a b) [a,b] := by
  classical
  by_cases ca : ∃ t, ∀ x, a.f x = t
  · obtain ⟨t,e⟩ := ca
    refine ⟨0,w,.nil,by decide,?_,by intro impossible; contradiction⟩
    cases t
    · have eq : (conj a b).f = (K (α := α) false).f := by funext x; simp [conj,meet,e,K]
      simpa only [Good,eq] using base false
    · have eq : (conj a b).f = b.f := by funext x; simp [conj,meet,e]
      simpa only [Good,eq] using hb
  by_cases cb : ∃ t, ∀ x, b.f x = t
  · obtain ⟨t,e⟩ := cb
    refine ⟨0,w,.nil,by decide,?_,by intro impossible; contradiction⟩
    cases t
    · have eq : (conj a b).f = (K (α := α) false).f := by funext x; simp [conj,meet,e,K]
      simpa only [Good,eq] using base false
    · have eq : (conj a b).f = a.f := by funext x; simp [conj,meet,e]
      simpa only [Good,eq] using ha
  · refine ⟨1,_,Run.gate Run.nil ha.1 hb.1,le_rfl,?_,?_⟩
    · exact ⟨List.mem_append_right _ (by simp [conj]),List.mem_append_right _ (by simp [conj])⟩
    · intro _ stable
      have ea := (stable a (by simp)).resolve_left ca
      have eb := (stable b (by simp)).resolve_left cb
      exact Or.inr (by simp [conj,ea,eb])

private theorem gateEffect {α} (w : List (Signal α)) (base : ∀ b, Good w (K b))
    (op : GateOp) (args : List (Wire α)) (h : ∀ a ∈ args, Good w a)
    (ok : op = .and ∨ op = .or ∨ op = .not) (sz : args.length ≤ 2) :
    Effect w (if op.eval [false] then 0 else if args.length = 2 then 1 else 0) (Eval op args) args := by
  have zero (z : Wire α) (hz : Good w z) (st : (∀ v ∈ args, Stable v) → Stable z) :
      Effect w 0 z args := ⟨0,w,.nil,le_rfl,hz,fun _ => st⟩
  rcases ok with rfl | rfl | rfl
  · cases args with
    | nil => exact zero _ (base true) (fun _ => Or.inl ⟨true,fun _ => rfl⟩)
    | cons a rest =>
      cases rest with
      | nil =>
        have eq : Eval .and [a] = a := by cases a; simp [Eval,GateOp.eval]
        rw [eq]
        exact zero a (h a (by simp)) (fun st => st a (by simp))
      | cons b rest =>
        have e : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at sz; omega)
        subst rest
        have eq : Eval .and [a,b] = conj a b := by simp [Eval,GateOp.eval,conj]; rfl
        rw [eq]
        exact bin w base a b (h a (by simp)) (h b (by simp))
  · cases args with
    | nil => exact zero _ (base false) (fun _ => Or.inl ⟨false,fun _ => rfl⟩)
    | cons a rest =>
      cases rest with
      | nil =>
        have eq : Eval .or [a] = a := by cases a; simp [Eval,GateOp.eval]
        rw [eq]
        exact zero a (h a (by simp)) (fun st => st a (by simp))
      | cons b rest =>
        have e : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at sz; omega)
        subst rest
        have eq : Eval .or [a,b] = disj a b := by simp [Eval,GateOp.eval,disj,conj,neg]; funext x; simp [inv,meet]
        rw [eq]
        obtain ⟨c,t,r,k,g,st⟩ := bin w base (neg a) (neg b) (goodNeg (h a (by simp))) (goodNeg (h b (by simp)))
        refine ⟨c,t,r,k,goodNeg g,fun equal stable => stableNeg (st equal ?_)⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl | h'
        · exact stableNeg (stable _ (by simp))
        · have hv := List.mem_singleton.mp h'
          exact hv ▸ stableNeg (stable b (by simp))
  · cases args with
    | nil => exact zero _ (base true) (fun _ => Or.inl ⟨true,fun _ => rfl⟩)
    | cons a rest =>
      exact zero (neg a) (goodNeg (h a (by simp))) (fun st => stableNeg (st a (by simp)))


def step {α} (v : List (Wire α)) (g : Gate) : List (Wire α) :=
  v ++ [Eval g.op (g.inputs.map fun i => v.getD i (K false))]

theorem get_property {α} (P : α → Prop) (v : List α) (d : α) (i : ℕ)
    (hd : P d) (h : ∀ z ∈ v, P z) : P (v.getD i d) := by
  by_cases hi : i < v.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hd

theorem fold {α} (gs : List Gate) (legal : ∀ g ∈ gs,
    (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (w : List (Signal α)) (base : ∀ b, Good w (K b)) (v : List (Wire α))
    (old : ∀ a ∈ v, Good w a) :
    ∃ k t, Run w k t ∧ k ≤ (gs.map Paid).sum ∧
      (∀ a ∈ gs.foldl step v, Good t a) ∧
      (k = (gs.map Paid).sum → (∀ a ∈ v, Stable a) → ∀ a ∈ gs.foldl step v, Stable a) := by
  induction gs generalizing w v with
  | nil => exact ⟨0,w,.nil,le_rfl,old,fun _ st => st⟩
  | cons g gs ih =>
    let args := g.inputs.map fun i => v.getD i (K false)
    have allg : ∀ z ∈ args, Good w z := by
      intro z mem
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
      exact get_property _ _ _ _ (base false) old
    have h := gateEffect w base g.op args allg (legal g (by simp)).1 (by simpa [args] using (legal g (by simp)).2)
    obtain ⟨c,t,run,cap,gnew,snew⟩ := h
    have ec : c ≤ Paid g := by simpa only [Paid,args,List.length_map] using cap
    have goodKeep {a} (ok : Good w a) : Good t a := ⟨run.keep _ ok.1,run.keep _ ok.2⟩
    have goodNext : ∀ a ∈ step v g, Good t a := by
      intro a mem
      rcases List.mem_append.mp mem with ov | nv
      · exact goodKeep (old a ov)
      · exact (List.mem_singleton.mp nv) ▸ gnew
    obtain ⟨j,u,tail,limit,done,st⟩ := ih (fun z hz => legal z (List.mem_cons_of_mem g hz))
      t (fun b => goodKeep (base b)) (step v g) goodNext
    refine ⟨c+j,u,run.comp tail,by simpa using Nat.add_le_add ec limit,done,?_⟩
    intro equal previous
    simp only [List.map_cons,List.sum_cons] at equal
    apply st (by omega)
    intro a mem
    rcases List.mem_append.mp mem with ov | nv
    · exact previous a ov
    · apply (List.mem_singleton.mp nv) ▸ snew (by simpa only [args,List.length_map,Paid] using (show c = Paid g by omega))
      intro z hz
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
      exact get_property _ _ _ _ (Or.inl ⟨false,fun _ => rfl⟩ : Stable (K (α := α) false)) previous

def addPair (w : List Bool) (ij : ℕ × ℕ) : List Bool :=
  let z := w.getD ij.1 false && w.getD ij.2 false
  w ++ [z,!z]

theorem Run.program {α} {s w : List (Signal α)} {k} (r : Run s k w) :
    ∃ prog : List (ℕ × ℕ), prog.length = k ∧ ∀ x : α,
      prog.foldl addPair (s.map fun f => f x) = w.map fun f => f x := by
  induction r with
  | nil => exact ⟨[],rfl,fun _ => rfl⟩
  | @gate k w r a b ha hb ih =>
    obtain ⟨p,len,sim⟩ := ih
    obtain ⟨i,hi,ei⟩ := List.getElem_of_mem ha
    obtain ⟨j,hj,ej⟩ := List.getElem_of_mem hb
    refine ⟨p++[(i,j)],by simp [len],?_⟩
    intro x
    rw [List.foldl_append,sim]
    simp only [List.foldl_cons,List.foldl_nil,addPair,List.map_append,List.map_cons,List.map_nil]
    rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hj)]
    simp [List.getElem_map,ei,ej,meet,inv]

def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem getMap {α β} (h : α → β) (v : List α) (i : ℕ) (d : α) :
    h (v.getD i d) = (v.map h).getD i (h d) := by
  simp [List.getD,List.getElem?_map,Option.getD_map]

theorem aligns {α} (h : Wire α → Bool) (hd : h (K false) = false)
    (he : ∀ op args, h (Eval op args) = op.eval (args.map h)) (gs : List Gate) (v : List (Wire α)) :
    (gs.foldl step v).map h = gs.foldl boolStep (v.map h) := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih]
    congr 1
    simp only [step,boolStep,List.map_append,List.map_cons,List.map_nil,he,List.map_map,
      Function.comp_def,getMap h,hd]

theorem outputMap {α} (h : Wire α → Bool) (hd : h (K false) = false)
    (he : ∀ op args, h (Eval op args) = op.eval (args.map h)) (C : Circuit) (v : List (Wire α)) :
    h ((C.gates.foldl step v).getD C.output (K false)) = C.eval (v.map h) := by
  rw [getMap h,hd,aligns h hd he]
  rfl


theorem compile (α : Type) (C : Circuit) (hc : FanInTwo C) (s : List (α → Bool))
    (v : List ((α → Bool) × Bool × Bool)) (constants : ∀ b : Bool, (fun _ : α => b) ∈ s)
    (pins : ∀ a ∈ v, a.1 ∈ s ∧ (fun x => !(a.1 x)) ∈ s ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2)) :
    ∃ (p : List (ℕ × ℕ)) (o : ℕ),
      p.length ≤ (C.gates.map fun g => ite (g.op.eval [false] = true) 0 (ite (g.inputs.length = 2) 1 0)).sum ∧
      ∀ x : α, (p.foldl (fun w ij =>
        let z := w.getD ij.1 false && w.getD ij.2 false
        w ++ [z,!z]) (s.map fun f => f x)).getD o false = C.eval (v.map fun a => a.1 x) := by
  let make := fun a : (α → Bool) × Bool × Bool => Wire.mk a.1 a.2.1 a.2.2
  let a := v.map make
  have base (b : Bool) : Good s (K b) := ⟨constants b,constants (!b)⟩
  have old : ∀ u ∈ a, Good s u ∧ Stable u := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hu
    obtain ⟨hg,hn,hs⟩ := pins z hz
    exact ⟨⟨hg,hn⟩,hs⟩
  obtain ⟨k,t,run,limit,accepted,stable⟩ :=
    fold C.gates (fun g hg => ⟨(hc g hg).1,(hc g hg).2⟩) s base a (fun u hu => (old u hu).1)
  let out := (C.gates.foldl step a).getD C.output (K false)
  have values (x : α) : out.f x = C.eval (v.map fun u => u.1 x) := by
    simpa [out,a,make,List.map_map,Function.comp_def] using
      outputMap (fun u : Wire α => u.f x) rfl (fun _ _ => rfl) C a
  have zero : Good t (K false) := ⟨run.keep _ (base false).1,run.keep _ (base false).2⟩
  have usable : Good t out := get_property _ _ _ _ zero accepted
  obtain ⟨o,ho,eo⟩ := List.getElem_of_mem usable.1
  obtain ⟨p,len,sim⟩ := run.program
  refine ⟨p,o,by rw [len]; exact limit,?_⟩
  intro x
  change (p.foldl addPair _).getD o false = _
  rw [sim,List.getD_eq_getElem _ _ (by simpa using ho),List.getElem_map,eo]
  exact values x

end PetersenSignedSlice

namespace ThresholdReplacement
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) := Nat.testBit (4269834368 * 2 ^ 32 + 2155905024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[
  ⟨.and, [4,5]⟩,
  ⟨.or, [4,5]⟩,
  ⟨.and, [1,2]⟩,
  ⟨.or, [1,2]⟩,
  ⟨.and, [0,8]⟩,
  ⟨.or, [3,7]⟩,
  ⟨.and, [10,11]⟩,
  ⟨.and, [3,6]⟩,
  ⟨.or, [0,9]⟩,
  ⟨.and, [13,14]⟩,
  ⟨.or, [12,15]⟩], 16⟩
theorem size : witness.size = 11 := by decide +kernel
theorem legal : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel
theorem value : ∀ x, circuitFun 6 witness x = target x := by decide +kernel

abbrev Input := Fin 6 → Bool
def sliceTarget (x : Input) := target x
def signedStart (x : Input) := [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not
def signed (p : List (ℕ × ℕ)) (o : ℕ) (x : Input) :=
  (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false

-- A signed binary program stores each wire together with its complement.
-- The entire six-input function is preserved, and NOT gates cost no steps.
theorem compileFull (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 6 C x = target x) :
    ∃ p o, p.length ≤ (C.gates.map PetersenSignedSlice.Paid).sum ∧
      ∀ x, signed p o x = sliceTarget x := by
  let raw := List.ofFn (fun j : Fin 6 => fun x : Input => x j)
  let pool := [(fun _ : Input => false), (fun _ : Input => true)] ++ raw ++
    raw.map (fun u x => !(u x))
  let wire := fun j : Fin 6 => (fun x : Input => x j, false, false)
  let v := List.ofFn wire
  have constants (b : Bool) : (fun _ : Input => b) ∈ pool := by cases b <;> simp [pool]
  have pins : ∀ a ∈ v, a.1 ∈ pool ∧ (fun x => !(a.1 x)) ∈ pool ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2) := by
    intro a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    have pos : (fun x : Input => x j) ∈ raw := List.mem_ofFn.mpr ⟨j,rfl⟩
    exact ⟨List.mem_append_left _ (List.mem_append_right _ pos),
      List.mem_append_right _ (List.mem_map_of_mem pos),Or.inr rfl⟩
  obtain ⟨p,o,small,ev⟩ := PetersenSignedSlice.compile Input C ok pool v constants pins
  refine ⟨p,o,small,fun x => ?_⟩
  have start : pool.map (fun u => u x) = signedStart x := by
    simp only [pool,raw,signedStart,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  change (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false = target x
  rw [←start]
  exact (ev x).trans (by simpa [v,wire,circuitFun,List.map_ofFn,Function.comp_def] using hit x)

theorem replacement
    (sliceLower : ∀ p o, (∀ x, signed p o x = sliceTarget x) → 10 ≤ p.length)
    (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 6 C x = target x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ ∀ x, circuitFun 6 D x = target x := by
  by_cases mono : Monotone2 C
  · exact ⟨C, mono, le_rfl, hit⟩
  · obtain ⟨p,o,sz,ev⟩ := compileFull C ok hit
    have paid (gs : List Gate) : (gs.map PetersenSignedSlice.Paid).sum ≤ gs.length ∧
        ((gs.map PetersenSignedSlice.Paid).sum = gs.length →
          ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) →
            (g.op = .and ∨ g.op = .or)) := by
      induction gs with
      | nil => simp
      | cons g t ih =>
        have cap : PetersenSignedSlice.Paid g ≤ 1 := by unfold PetersenSignedSlice.Paid; split <;> (first | decide | split <;> decide)
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        refine ⟨by omega, ?_⟩
        intro eq u mem kind
        rcases List.mem_cons.mp mem with rfl | tail
        · rcases kind with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · have := ih.1
            simp [PetersenSignedSlice.Paid, h, GateOp.eval] at eq
            omega
        · exact ih.2 (by omega) _ tail kind
    obtain ⟨cap, full⟩ := paid C.gates
    have strict : (C.gates.map PetersenSignedSlice.Paid).sum < C.gates.length := by
      by_contra! fail
      apply mono
      intro g hg
      exact ⟨full (by omega) _ hg (ok g hg).1, (ok g hg).2⟩
    have := sliceLower p o ev
    exact ⟨witness, legal, by rw [size]; change 11 ≤ C.gates.length; omega, value⟩

end ThresholdReplacement

namespace SignedFrontier

abbrev W := BitVec 64

def canonical (w : W) : W := if w.getLsbD 0 then ~~~w else w

def choices (a b : W) : List W :=
  [a &&& b, a &&& ~~~b, ~~~a &&& b, a ||| b]

theorem canonical_not (w : W) : canonical (~~~w) = canonical w := by
  cases h : w.getLsbD 0 <;> simp_all [canonical, BitVec.not_not]

theorem canonical_bit (w : W) : (canonical w).getLsbD 0 = false := by
  unfold canonical
  split <;> simp_all

theorem operation (a b : W) :
    canonical (a &&& b) ∈ choices (canonical a) (canonical b) := by
  cases ha : a.getLsbD 0 <;> cases hb : b.getLsbD 0 <;>
    simp_all [choices, canonical, BitVec.not_and, BitVec.not_not]

theorem constants (a b : W) (h : a = 0 ∨ b = 0 ∨ a = b) :
    ∀ w ∈ choices a b, w = 0 ∨ w = a ∨ w = b := by
  rcases h with rfl | rfl | rfl <;> simp [choices]
  · exact Or.inr BitVec.allOnes_and
  · exact Or.inr (Or.inl BitVec.and_allOnes)

-- Read the live gates backwards from the single required output. The two
-- operands can belong to the suffix already when a wire is shared.
inductive Cone (goal : W) : ℕ → Finset W → Prop where
  | done : Cone goal 0 {goal}
  | step {k : ℕ} {needed : Finset W} {a b w : W}
      (rest : Cone goal k needed) (wanted : w ∈ needed)
      (a0 : a ≠ 0) (b0 : b ≠ 0) (ab : a ≠ b) (aw : a ≠ w) (bw : b ≠ w)
      (form : w ∈ choices a b) :
      Cone goal (k+1) (insert a (insert b (needed.erase w)))

theorem Cone.size {goal : W} {k : ℕ} {s : Finset W} (h : Cone goal k s) :
    s.card ≤ k+1 := by
  induction h with
  | done => simp
  | @step k needed a b w rest wanted a0 b0 ab aw bw form ih =>
    have e := Finset.card_erase_of_mem wanted
    have hn := Finset.card_pos.mpr ⟨w,wanted⟩
    have p := Finset.card_insert_le b (needed.erase w)
    have q := Finset.card_insert_le a (insert b (needed.erase w))
    omega

def add (ws : List W) (ij : ℕ × ℕ) : List W :=
  let w := ws.getD ij.1 0 &&& ws.getD ij.2 0
  ws ++ [w,~~~w]

def available (ws : List W) : Finset W := insert 0 (ws.map canonical).toFinset

theorem available_read (ws : List W) (i : ℕ) : canonical (ws.getD i 0) ∈ available ws := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    simp only [available, Finset.mem_insert, List.mem_toFinset, List.mem_map]
    exact Or.inr ⟨_,List.getElem_mem hi,rfl⟩
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [available,canonical]

theorem available_add (ws : List W) (ij : ℕ × ℕ) :
    available (add ws ij) = insert (canonical (ws.getD ij.1 0 &&& ws.getD ij.2 0)) (available ws) := by
  ext w
  simp [available,add,canonical_not]
  tauto

theorem extract (p : List (ℕ × ℕ)) (ws : List W) (g : W) (k : ℕ) (s : Finset W)
    (h : Cone g k s) (hs : s ⊆ available (p.foldl add ws)) :
    ∃ j t, j ≤ k+p.length ∧ t ⊆ available ws ∧ Cone g j t := by
  induction p generalizing ws k s with
  | nil => exact ⟨k,s,by simp,hs,h⟩
  | cons ij tail ih =>
    obtain ⟨j,t,hj,ht,hr⟩ := ih (add ws ij) k s h hs
    rw [available_add] at ht
    by_cases sub : t ⊆ available ws
    · exact ⟨j,t,by simp only [List.length_cons]; omega,sub,hr⟩
    · let a := canonical (ws.getD ij.1 0)
      let b := canonical (ws.getD ij.2 0)
      let w := canonical (ws.getD ij.1 0 &&& ws.getD ij.2 0)
      have ha : a ∈ available ws := available_read _ _
      have hb : b ∈ available ws := available_read _ _
      have hz : (0 : W) ∈ available ws := Finset.mem_insert_self ..
      have new : w ∉ available ws := by
        intro hold
        exact sub (fun z h' => (Finset.mem_insert.mp (ht h')).elim (fun e => e ▸ hold) id)
      have want : w ∈ t := by
        by_contra hn
        exact sub (fun z h' => (Finset.mem_insert.mp (ht h')).resolve_left (by rintro rfl; contradiction))
      have form : w ∈ choices a b := operation _ _
      have diff : ¬ (a = 0 ∨ b = 0 ∨ a = b) := by
        intro bad
        rcases constants a b bad w form with e | e | e <;> apply new <;> simp_all
      refine ⟨j+1,_,by simp only [List.length_cons]; omega,?_,
        Cone.step hr want (fun e => diff (Or.inl e)) (fun e => diff (Or.inr (Or.inl e)))
          (fun e => diff (Or.inr (Or.inr e))) (fun e => new (e ▸ ha)) (fun e => new (e ▸ hb)) form⟩
      intro z hz'
      rcases Finset.mem_insert.mp hz' with rfl | hz'
      · exact ha
      rcases Finset.mem_insert.mp hz' with rfl | hz'
      · exact hb
      obtain ⟨hne,hzt⟩ := Finset.mem_erase.mp hz'
      exact (Finset.mem_insert.mp (ht hzt)).resolve_left hne

theorem Cone.noZero {g : W} {k : ℕ} {s : Finset W} (h : Cone g k s) (hg : g ≠ 0) :
    0 ∉ s := by
  induction h with
  | done => exact fun hz => hg (Finset.mem_singleton.mp hz).symm
  | step rest wanted a0 b0 ab aw bw form ih =>
    intro hz
    rcases Finset.mem_insert.mp hz with e | hm
    · exact a0 e.symm
    rcases Finset.mem_insert.mp hm with e | hm
    · exact b0 e.symm
    exact ih (Finset.mem_of_mem_erase hm)

theorem same_choice (a b w : W) (hw : w ∈ choices a b) (i j : ℕ) (hi : i < 64) (hj : j < 64)
    (ha : a.getLsbD i = a.getLsbD j) (hb : b.getLsbD i = b.getLsbD j) :
    w.getLsbD i = w.getLsbD j := by
  simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_or,hi,hj,decide_true,
      Bool.true_and,ha,hb]

theorem Cone.agree {g : W} {k : ℕ} {s : Finset W} (h : Cone g k s)
    (i j : ℕ) (hi : i < 64) (hj : j < 64)
    (same : ∀ u ∈ s, u.getLsbD i = u.getLsbD j) : g.getLsbD i = g.getLsbD j := by
  induction h with
  | done => exact same _ (Finset.mem_singleton_self _)
  | @step k needed a b w rest wanted a0 b0 ab aw bw form ih =>
    apply ih
    intro u hu
    by_cases h : u = w
    · subst u
      exact same_choice _ _ _ form i j hi hj (same a (by simp)) (same b (by simp))
    · exact same u (by simp [h, hu])

def rowMask (r : ℕ) (u : W) := if u.getLsbD r then u else ~~~u

def survivors (r : ℕ) : List W → W → W
  | [], mask => mask
  | a :: tail, mask =>
    if mask = 0 then 0 else survivors r tail (mask &&& rowMask r a)

theorem survivor_sound (r j : ℕ) (hj : j < 64) (s : List W) (m : W)
    (hit : (survivors r s m).getLsbD j = true) :
    m.getLsbD j = true ∧ ∀ u ∈ s, u.getLsbD r = u.getLsbD j := by
  induction s generalizing m with
  | nil => exact ⟨hit,by simp⟩
  | cons a tail ih =>
    simp only [survivors] at hit
    split at hit
    · simp at hit
    · obtain ⟨head,rest⟩ := ih _ hit
      simp only [BitVec.getLsbD_and,Bool.and_eq_true] at head
      refine ⟨head.1,?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | h
      · have v := head.2
        unfold rowMask at v
        cases h : u.getLsbD r <;> simp_all
      · exact rest u h

def covered (g : W) (rows : List ℕ) (s : List W) :=
  rows.all fun r => survivors r s g == 0

theorem Cone.covered {g : W} {k : ℕ} {s : List W} (h : Cone g k s.toFinset)
    (rows : List ℕ) (neg : ∀ r ∈ rows, r < 64 ∧ g.getLsbD r = false) :
    covered g rows s = true := by
  apply List.all_eq_true.mpr
  intro r hr
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨limit,off⟩ := neg r hr
  cases hv : (survivors r s g).getLsbD j with
  | false => simp
  | true =>
    obtain ⟨on,same⟩ := survivor_sound r j hj s g hv
    have eq := h.agree r j limit hj (by simpa using same)
    simp [off,on] at eq

def withWire (keep : Bool) (a : W) (s : List W) := if keep then a :: s else s

theorem mem_withWire {u a : W} {s : List W} (keep : Bool) :
    u ∈ withWire keep a s ↔ (keep = true ∧ u = a) ∨ u ∈ s := by
  cases keep <;> simp [withWire]

def after (s : List W) (a b w : W) (ka kb : Bool) : List W :=
  w :: withWire ka a (withWire kb b (s.filter fun u => u != a && u != b))

theorem after_exact (s : List W) (needed : Finset W) (a b w : W)
    (hs : s.toFinset = insert a (insert b (needed.erase w))) (want : w ∈ needed) :
    (after s a b w (decide (a ∈ needed)) (decide (b ∈ needed))).toFinset = needed := by
  ext u
  have mem : u ∈ s ↔ u = a ∨ u = b ∨ u ≠ w ∧ u ∈ needed := by
    rw [← List.mem_toFinset,hs]
    simp
  simp only [List.mem_toFinset,after,List.mem_cons,mem_withWire,decide_eq_true_eq,
    List.mem_filter,Bool.and_eq_true,bne_iff_ne,mem]
  grind

def onePair (s : List W) (f : List W → Bool) (a b : W) :=
  (choices a b).any fun w => w != 0 && !s.contains w &&
    ([false,true] : List Bool).any fun ka => ([false,true] : List Bool).any fun kb =>
      f (after s a b w ka kb)

def moves (s : List W) (f : List W → Bool) :=
  s.any fun a => s.any fun b => decide (a.toNat < b.toNat) && onePair s f a b

theorem swap_choices {a b w : W} : w ∈ choices a b → w ∈ choices b a := by
  simp only [choices,List.mem_cons,List.not_mem_nil,or_false]
  intro h
  rcases h with rfl | rfl | rfl | rfl <;> simp [BitVec.and_comm,BitVec.or_comm]

theorem after_nodup (s : List W) (hs : s.Nodup) (a b w : W) (ka kb : Bool)
    (diff : a ≠ b) (fresh : w ∉ s) (aw : a ≠ w) (bw : b ≠ w) :
    (after s a b w ka kb).Nodup := by
  have base := hs.filter (fun u => u != a && u != b)
  have ha : a ∉ s.filter (fun u => u != a && u != b) := by simp
  have hb : b ∉ s.filter (fun u => u != a && u != b) := by simp
  have hw : w ∉ s.filter (fun u => u != a && u != b) := by simp [fresh]
  cases ka <;> cases kb <;> simp [after,withWire,base,fresh,Ne.symm aw,Ne.symm bw,diff]

theorem onePair_complete (s : List W) (f : List W → Bool)
    {g a b w : W} {k : ℕ} {needed : Finset W} (hg : g ≠ 0)
    (unique : s.Nodup) (ab : a ≠ b) (rest : Cone g k needed) (want : w ∈ needed)
    (hs : s.toFinset = insert a (insert b (needed.erase w)))
    (aw : a ≠ w) (bw : b ≠ w) (form : w ∈ choices a b)
    (succ : ∀ t : List W, t.Nodup → Cone g k t.toFinset → f t = true) :
    onePair s f a b = true := by
  have nz : w ≠ 0 := fun e => rest.noZero hg (e ▸ want)
  have fresh : w ∉ s := by
    rw [← List.mem_toFinset,hs]
    simp [Ne.symm aw,Ne.symm bw]
  apply List.any_eq_true.mpr
  refine ⟨w,form,?_⟩
  simp only [bne_iff_ne.mpr nz,List.contains_eq_mem,decide_eq_false fresh,
    Bool.not_false,Bool.true_and]
  apply List.any_eq_true.mpr
  refine ⟨decide (a ∈ needed),by cases decide (a ∈ needed) <;> simp,?_⟩
  apply List.any_eq_true.mpr
  refine ⟨decide (b ∈ needed),by cases decide (b ∈ needed) <;> simp,?_⟩
  exact succ _ (after_nodup s unique a b w _ _ ab fresh aw bw) ((after_exact s needed a b w hs want).symm ▸ rest)

theorem moves_complete (s : List W) (f : List W → Bool)
    {g : W} {k : ℕ} {state : Finset W} (hg : g ≠ 0)
    (unique : s.Nodup) (h : Cone g (k+1) state) (eq : s.toFinset = state)
    (succ : ∀ t : List W, t.Nodup → Cone g k t.toFinset → f t = true) :
    moves s f = true := by
  cases h with
  | @step _ needed a b w rest want a0 b0 ab aw bw form =>
    have ha : a ∈ s := List.mem_toFinset.mp (eq.symm ▸ Finset.mem_insert_self ..)
    have hb : b ∈ s := List.mem_toFinset.mp (eq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    apply List.any_eq_true.mpr
    have distinct : a.toNat ≠ b.toNat := fun e => ab (BitVec.eq_of_toNat_eq e)
    rcases lt_or_gt_of_ne distinct with lt | gt
    · refine ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,?_⟩⟩
      simp only [lt,decide_true,Bool.true_and]
      exact onePair_complete s f hg unique ab rest want eq aw bw form succ
    · refine ⟨b,hb,List.any_eq_true.mpr ⟨a,ha,?_⟩⟩
      simp only [gt,decide_true,Bool.true_and]
      rw [Finset.insert_comm] at eq
      exact onePair_complete s f hg unique ab.symm rest want eq bw aw (swap_choices form) succ

def feasible (g : W) (rows : List ℕ) : ℕ → List W → Bool
  | 0, s => s.contains g
  | k+1, s => s.contains g ||
    (decide (s.length ≤ k+2) && covered g rows s &&
      moves s (feasible g rows k))

theorem feasible_complete {g : W} (hg : g ≠ 0) (rows : List ℕ)
    (neg : ∀ r ∈ rows, r < 64 ∧ g.getLsbD r = false)
    (cap : ℕ) (s : List W) (unique : s.Nodup) (k : ℕ) (bound : k ≤ cap) (h : Cone g k s.toFinset) :
    feasible g rows cap s = true := by
  induction cap generalizing k s with
  | zero =>
    have hz : k = 0 := by omega
    subst k
    have final {t : Finset W} (c : Cone g 0 t) : g ∈ t := by cases c; simp
    simpa [feasible] using final h
  | succ cap ih =>
    simp only [feasible,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    cases k with
    | zero =>
      left
      have final {t : Finset W} (c : Cone g 0 t) : g ∈ t := by cases c; simp
      simpa using final h
    | succ k =>
      right
      refine ⟨⟨by have sz := h.size; rw [List.toFinset_card_of_nodup unique] at sz; omega,h.covered rows neg⟩,?_⟩
      exact moves_complete _ _ hg unique h rfl (fun t nd ht => ih t nd k (by omega) ht)

def Essential (g : W) (raws : List W) :=
  ∀ w ∈ raws, ∃ i j : Fin 64, g.getLsbD i.val ≠ g.getLsbD j.val ∧
    ∀ v ∈ raws, v ≠ w → v.getLsbD i.val = v.getLsbD j.val

theorem Cone.initial {g : W} (hg : g ≠ 0) (raws : List W) (ess : Essential g raws)
    {k : ℕ} {s : Finset W} (h : Cone g k s) (sub : s ⊆ insert 0 raws.toFinset) :
    s = raws.toFinset := by
  have contained : s ⊆ raws.toFinset := by
    intro z hz
    exact (Finset.mem_insert.mp (sub hz)).resolve_left (fun e => h.noZero hg (e ▸ hz))
  apply Finset.Subset.antisymm contained
  intro w hw
  by_contra missing
  obtain ⟨i,j,diff,others⟩ := ess w (List.mem_toFinset.mp hw)
  exact diff (h.agree _ _ i.isLt j.isLt (fun u hu =>
    others u (List.mem_toFinset.mp (contained hu)) (fun e => missing (e ▸ hu))))

def evaluate (p : List (ℕ × ℕ)) (ws : List W) (o : ℕ) : W := (p.foldl add ws).getD o 0

theorem from_check (g : W) (hg : g ≠ 0) (raws ws : List W) (unique : raws.Nodup) (start : available ws = insert 0 raws.toFinset)
    (rows : List ℕ) (neg : ∀ r ∈ rows, r < 64 ∧ g.getLsbD r = false) (ess : Essential g raws)
    (cap : ℕ) (checked : feasible g rows cap raws = false) (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : canonical (evaluate p ws o) = g) : cap < p.length := by
  by_contra! short
  have sub : {g} ⊆ available (p.foldl add ws) := by
    apply Finset.singleton_subset_iff.mpr
    rw [← hit]
    exact available_read _ _
  obtain ⟨k,s,bound,inside,run⟩ := extract p ws g 0 {g} Cone.done sub
  rw [start] at inside
  have eq := run.initial hg raws ess inside
  rw [eq] at run
  have possible := feasible_complete hg rows neg cap raws unique k (by omega) run
  simp [checked] at possible

-- A mask selects the low positions and the matching high positions of a swap.
structure Switch where
  distance : ℕ
  low : W
  high : W

def Switch.source (s : Switch) (r : ℕ) :=
  if s.low.getLsbD r then s.distance + r else if s.high.getLsbD r then r-s.distance else r

def Switch.apply (s : Switch) (w : W) : W :=
  (w &&& ~~~(s.low ||| s.high)) ||| ((w >>> s.distance) &&& s.low) |||
    ((w <<< s.distance) &&& s.high)

def Switch.Valid (s : Switch) :=
  ∀ r : Fin 64, ¬ (s.low.getLsbD r.val = true ∧ s.high.getLsbD r.val = true) ∧
    (s.high.getLsbD r.val = true → s.distance ≤ r.val) ∧
    s.source r.val < 64 ∧ s.source (s.source r.val) = r.val

theorem Switch.read (s : Switch) (ok : s.Valid) (w : W) (r : ℕ) (hr : r < 64) :
    (s.apply w).getLsbD r = w.getLsbD (s.source r) := by
  obtain ⟨disj,lower,_,_⟩ := ok ⟨r,hr⟩
  change ¬ (s.low.getLsbD r = true ∧ s.high.getLsbD r = true) at disj
  change s.high.getLsbD r = true → s.distance ≤ r at lower
  simp only [Switch.apply, BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight,hr,decide_true,Bool.true_and,Switch.source]
  cases a : s.low.getLsbD r <;> cases b : s.high.getLsbD r <;> simp_all

theorem Switch.inj (s : Switch) (ok : s.Valid) : Function.Injective s.apply := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  obtain ⟨_,_,lim,inv⟩ := ok ⟨r,hr⟩
  have e := congrArg (fun u : W => u.getLsbD (s.source r)) h
  simpa only [s.read ok _ _ lim, inv] using e

theorem Switch.not (s : Switch) (ok : s.Valid) (w : W) : s.apply (~~~w) = ~~~(s.apply w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have bound := (ok ⟨i,hi⟩).2.2.1
  simp only [s.read ok _ _ hi,BitVec.getLsbD_not,hi,bound,decide_true,Bool.true_and]

theorem Switch.and (s : Switch) (ok : s.Valid) (a b : W) :
    s.apply (a &&& b) = s.apply a &&& s.apply b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [s.read ok _ _ hi,BitVec.getLsbD_and]

theorem Switch.or (s : Switch) (ok : s.Valid) (a b : W) :
    s.apply (a ||| b) = s.apply a ||| s.apply b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [s.read ok _ _ hi,BitVec.getLsbD_or]

theorem Cone.switched {g : W} {k : ℕ} {xs : Finset W} (h : Cone g k xs) (s : Switch) (ok : s.Valid) :
    Cone (s.apply g) k (xs.image s.apply) := by
  have zero : s.apply 0 = 0 := by simp [Switch.apply]
  have inj := s.inj ok
  induction h with
  | done => simpa using (Cone.done (goal := s.apply g))
  | @step k ys a b w rest want a0 b0 ab aw bw form ih =>
    have wanted : s.apply w ∈ ys.image s.apply := Finset.mem_image_of_mem _ want
    have erase : (ys.erase w).image s.apply = (ys.image s.apply).erase (s.apply w) := by
      ext x
      simp only [Finset.mem_image,Finset.mem_erase]
      constructor
      · rintro ⟨v,⟨hne,mem⟩,rfl⟩
        exact ⟨fun e => hne (inj e),v,mem,rfl⟩
      · rintro ⟨hne,v,mem,rfl⟩
        exact ⟨v,⟨fun e => hne (congrArg _ e),mem⟩,rfl⟩
    have operate : s.apply w ∈ choices (s.apply a) (s.apply b) := by
      simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at form ⊢
      rcases form with rfl | rfl | rfl | rfl <;> simp [s.and ok,s.or ok,s.not ok]
    simp only [Finset.image_insert,erase]
    exact Cone.step ih wanted (fun e => a0 (inj (e.trans zero.symm)))
      (fun e => b0 (inj (e.trans zero.symm))) (fun e => ab (inj e))
      (fun e => aw (inj e)) (fun e => bw (inj e)) operate

def reindex : List Switch → W → W
  | [], w => w
  | s :: tail, w => reindex tail (s.apply w)

theorem Cone.reindex {g : W} {k : ℕ} {s : Finset W} (h : Cone g k s) (ops : List Switch)
    (ok : ∀ op ∈ ops, op.Valid) :
    Cone (reindex ops g) k (s.image (reindex ops)) := by
  induction ops generalizing s g with
  | nil => simpa [SignedFrontier.reindex] using h
  | cons op tail ih =>
    have step := h.switched op (ok _ List.mem_cons_self)
    have result := ih step (fun u hu => ok u (List.mem_cons_of_mem _ hu))
    simpa only [SignedFrontier.reindex,Finset.image_image,Function.comp_def] using result

def found (words : ℕ → ℕ → List W) (count : ℕ → ℕ)
    (lookup : ℕ → List W → ℕ × ℕ) (sym : ℕ → List Switch) (k : ℕ) (s : List W) :=
  let (i,j) := lookup k s
  decide (i < count k) && (s.map (reindex (sym j))).isPerm (words k i)

def closed (g : W) (negative : List ℕ) (words : ℕ → ℕ → List W) (count : ℕ → ℕ)
    (lookup : ℕ → List W → ℕ × ℕ) (sym : ℕ → List Switch) : ℕ → ℕ → Bool
  | 0, i => !(words 0 i).contains g
  | k+1, i =>
    let s := words (k+1) i
    !s.contains g && !(moves s fun t =>
      t.contains g || (decide (0 < k) && decide (t.length ≤ k+1) && covered g negative t &&
        !found words count lookup sym k t))

theorem closed_excludes (g : W) (hg : g ≠ 0) (negative : List ℕ)
    (neg : ∀ r ∈ negative, r < 64 ∧ g.getLsbD r = false)
    (words : ℕ → ℕ → List W) (count : ℕ → ℕ) (lookup : ℕ → List W → ℕ × ℕ)
    (sym : ℕ → List Switch) (valid : ∀ j, ∀ op ∈ sym j, op.Valid)
    (fix : ∀ j, reindex (sym j) g = g) (cap : ℕ)
    (nd : ∀ k ≤ cap, ∀ i < count k, (words k i).Nodup)
    (checks : ∀ k ≤ cap, ∀ i < count k, closed g negative words count lookup sym k i = true) :
    ∀ k ≤ cap, ∀ i < count k, ∀ d ≤ k, ¬ Cone g d (words k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro hk i hi d hd run
    have de : d = 0 := by omega
    subst d
    have terminal {t : Finset W} (p : Cone g 0 t) : g ∈ t := by cases p; simp
    have mem := List.mem_toFinset.mp (terminal run)
    simpa [closed,mem] using checks 0 hk i hi
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
        covered g negative t && !found words count lookup sym k t)
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
        simp [positive,show t.length ≤ k+1 by omega,ht.covered negative neg,no])
      change (!moves (words (k+1) i) test) = true at reject
      simp [next] at reject

end SignedFrontier

namespace SignedFrontier

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


end SignedFrontier

namespace SignedFrontier.SmallCert

def span (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_member {f n o} (h : span f n o = true) :
    ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    intro i lo hi
    obtain ⟨first,tail⟩ := Bool.and_eq_true_iff.mp h
    rcases Nat.eq_or_lt_of_le lo with rfl | gt
    · exact first
    · exact ih tail i (by omega) (by omega)

theorem span_join {f a o b} (left : span f a o = true) (right : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using right
  | succ a ih =>
    obtain ⟨first,rest⟩ := Bool.and_eq_true_iff.mp left
    rw [Nat.succ_add]
    exact Bool.and_eq_true_iff.mpr ⟨first,ih rest (by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using right)⟩

end SignedFrontier.SmallCert

namespace SignedFrontier.SmallCert.Full

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def target : W := 0xfe80808080808000
def negative : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 53, 54, 56]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨14,15,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨13,15,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨11,15,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨7,15,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨7,23,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨7,39,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0xff88ff8800000000ff88888800000000ff80ff8000000000ff0fff0000000000ff0affaa00000000ff0aff0a00000000ff00ffee00000000ff00ffaa00000000ff00ff8800000000ff00ff0000000000ff00aaaa00000000ff00aa0000000000ff000f0000000000ff0000aa00000000ff00000000000000fefefefe00000000feeefeee00000000feaafeaa00000000fcfcfcfc00000000eeeeeeee00000000eeaaeeaa00000000ee00ee0000000000eaeaeaea00000000cccccccc00000000afaaafaa00000000af00af0000000000aeaeaeae00000000aaaaffaa00000000aaaaeeee00000000aaaaaaaa00000000aaaaaa0000000000aa88aa8800000000aa0aaa0a00000000aa00ff0000000000aa00aaaa00000000aa00aa0000000000aa00000000000000a8a8a8a8000000008a8a8a8a000000008888aaaa000000008888888800000000880088000000000080808080000000003f003f00000000002a2a2a2a000000000f0a0f0a000000000f00ff00000000000e0e0e0e000000000a0aaaaa000000000a0a0a0a000000000a000a0000000000080808080000000000ffff000000000000aaaaaa000000000000ffaa000000000000ff00000000000000eeee000000000000aaaa000000000000aa0000000000000088880000000000000f000000000000000a0a00000000000000aa0000000000000000 else (if page < 2 then 0xff880000ff880000ff00ffffffaa0000ff00ffffff000000ff00ffff00000000ff00ffaaffaa0000ff00ffaaff000000ff00ff00ffaa0000ff00ff00ff000000ff00ff0000000000ff000000ffaa0000ff000000ff000000fefe0000fefe0000eeeeeeeeeeee0000cccc0000cccc0000aaaaffffaaaa0000aaaaffff00000000aaaaff00ffaa0000aaaaff00ff000000aaaacccceeee0000aaaaaaaaaaaa0000aaaaaaaa00000000aaaa0000aaaa0000aa00ffffaaaa0000aa00ff00ff000000aa00aaaaaaaa0000aa00aa00aa0000008888aaaaaaaa000088888888888800000f0ffffff0f000000f0affaaffaa00000f00fffffff000000f00fff0fff000000f00ff00ff0000000a0afffffafa00000a0affffaaaa00000a0aaaaaaaaa000000ffffffff00000000ffff00ff00000000aaaaaaaaaa00000000ffffffee00000000ffffffaa00000000ffffff8800000000ffffff0000000000ffffaaaa00000000ffff000000000000fffefffe00000000ffeeffee00000000ffeeffaa00000000ffeeeeee00000000ffeaffea00000000ffccffcc00000000ffafffaa00000000ffaeffae00000000ffaaffee00000000ffaaffaa00000000ffaaff8800000000ffaaff0000000000ffaaeeaa00000000ffaacc8800000000ffaaafaa00000000ffaaaaaa00000000ffa8ffa800000000ff8aff8a00000000ff88ffaa else 0xf0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f0a0f0f0f0a0f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0affaaffaa0f0a0f0a0f0a0f0a0f080f080f080f080f00ff00ff00ff000f000f00fff0fff00f000f00f0f0f0f00f000f00afaaafaa0f000f000f000f000e0e0e0eeeeeeeee0c0c0c0c0c0c0c0c0aaaaaaaaaaaaaaa0a0aaaaaaaaaaaaa0a0a0a0aff0aff0a0a0a0a0afafafafa0a0a0a0acececece0a0a0a0aaaaaaaaa0a0a0a0a8a8a8a8a0a0a0a0a0a0a0a0a0a000a00ff00ff000a000a00aaaaaaaa0a000a00aa00aa0008080808aaaaaaaa080808088888888803030303fcfcfcfc03000300ff00ff0002020202aaaaaaaa00ffffffffffff0000ffffff00ff000000ffffff0000000000ffff00ffffff0000ffff00ff00ff0000ff00ffff00ff0000ff00ff00ff000000ff00ff00aa00aa00ff00ff0000000000ff00aa00ff00aa00ff0000ffffff0000ff0000ffff000000ff0000aaffaaaa00ff000000ff00aa00ff000000ff000000aaaaaaaaaaaaaa0000ffffffffff000000ffffffffaaaa0000ffffffff00000000ffffff00ff000000ffff0000ffaa0000ffff0000ff000000ffff0000f0f00000ffff0000cccc0000ffff0000aaaa0000ffff000000000000ffee0000ffee0000ffcc0000ffcc0000ffaaffaaffaa0000ffaa0000ffaa)) else (if page < 4 then 0x8b888b888b888b888a8aaaaaaaaaaaaa8a8a8a8ababababa8a8a8a8aaaaaaaaa8a8a8a8aaa8aaa8a8a8a8a8a8a8aaaaa8a8a8a8a8a8a8a8a8a8a8a888a8a8a888a888a88aaaaaaaa8a888a88aa88aa888a888a888a8a8a8a8a888a888a888a888a8888888a8888888a808a808a808a808a0a8a0a8a0a8a0a8a008a008a008a008888aaaaaaaaaaaa88888888ff88ff8888888888f8f8f8f888888888aaaaaaaa88888888aa88aa8888888888a8a8a8a8888888888a8a8a8a888888888888aaaa8888888888888888888888880000000088888800888888008880888088808880880888088808880888008800ff00ff0088008800aaaaaaaa88008800aa00aa00880088008888888888008800880088008800000088000000828282828a8a8a8a8282828282828282828082808280828080808080aaaaaaaa80808080888888888080808080808080800080008000800077777777000000005f5f5f5f0000000055ff55ff0000000055aa55aa55aa55aa5555ffff0000000055555555aaaaaaaa5555555555550000555555555500550055555555505050505555555544444444555555550000000055445544554455444444444444444444333333333030303033333333000000000fff0fff000000000f0fffffffff00000f0fffff000000000f0ff0f0ffff00000f0ff0f0f0f0f0f00f0f0f0ff0f0f0f00f0f0f0f0f0a0f0a else (if page < 5 then 0xaa88aa88af8caf8caa88aa88aaaaaaaaaa88aa88aaaaaa88aa88aa88aaa8aaa8aa88aa88aa8aaa8aaa88aa88aa88aaaaaa88aa88aa88aa88aa88aa88aa88aa00aa88aa88aa888888aa88aa80aa88aa80aa88aa00aa88aa00aa88a888aa88a888aa88a080aa88a080aa888a88aa888a88aa888888aaaaaaaaaa888888aa88aa88aa888888aa888888aa88888888888888aa80aa80aaaaaaaaaa80aa80aa88aa88aa80aa80aa80aa80aa808080aa808080aa55aa55ff00ff00aa55aa55aaaaaaaaaa44aa44aa44aa44aa22aa22aa22aa22aa0aaa0aaaaaaaaaaa0aaa0aaa0aaa0aaa00ff00ff00ff00aa00aaaaaaaaaaaaaa00aa00ffffaa00aa00aa00ff00ff00aa00aa00ff00aa00aa00aa00eecceeccaa00aa00ee00ee00aa00aa00aaaaaaaaaa00aa00aaaaaa00aa00aa00aa88aa88aa00aa00aa0aaa0aaa00aa00aa00ff00aa00aa00aa00aaaaaa00aa00aa00aa00aa008800aa008800a8a8a8a8fcfcfcfca8a8a8a8aaaaaaaaa8a8a8a8a8a8a8a8a888a888a888a888a800a800a800a800a2a2a2a2a2a2a2a2a0a0a0a0a0a0a0a0a0a0a0a0000000009a9a9a9a9a9a9a9a99999999aaaaaaaa9988998899889988990099009900990098989898989898988f888f888f888f888f008f008f008f008e8e8e8e8e8e8e8e8e8a8e8a8e8a8e8a8e888e888e888e888c8c8c8ccccccccc8c8c8c8c8c8c8c8c8b8a8b8a8b8a8b8a else 0xaaffaaaaaaffaaaaaaffaa00aaffaa00aaff0000aaff0000aaaaffff00000000aaaaffaaffaaffaaaaaaeeeeeeeeeeeeaaaaaaaaffffffaaaaaaaaaaffeeffeeaaaaaaaaffaaffaaaaaaaaaaffaaaaaaaaaaaaaaff00ff00aaaaaaaafefefefeaaaaaaaaeeeeeeeeaaaaaaaaeeaaeeaaaaaaaaaaeaeaeaeaaaaaaaaaccccccccaaaaaaaaafaaafaaaaaaaaaaaeaeaeaeaaaaaaaaaaaaffaaaaaaaaaaaaaaeeeeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88aaaaaaaaaaaaaa0aaaaaaaaaaaaaaa00aaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaaa0a0a0a0aaaaaaaa88aa88aaaaaaaaaa88888888aaaaaaaa22222222aaaaaaaa0a0a0a0aaaaaaaaa00aa00aaaaaaaaaa0000aaaaaaaaaaaa00000000aaaaaaa8aaaaaaa8aaaaaa8aaaaaaa8aaaaaaa88aaaaaaaaaaaaaa88aaaaaa88aaaaaa88aaaaaa00aaaaaa88aa88aa88aaaaaa80aaaaaa80aaaaaa0aaaaaaa0aaaaaaa00ffffff00aaaaaa00aaaaaaaaaaaaaa00aaaaaa00aaaaaa00aa00aa00aaaa8888aaaa8888aaaa00aaaaaa00aaaaaa0000aaaaaaaaaaaa0000aaaa0000aaaa000000000000aaa8aaa8aaaaaaaaaaa8aaa8aaa8aaa8aaa8aa88aaa8aa88aaa8a8a8aaa8a8a8aaa0aaa0aaa0aaa0aa8caa8caa8caa8caa8aaa8aaaaaaaaaaa8aaa8aaa8aaa8aaa8aaa88aa8aaa88aa8a8a8aaa8a8a8aaa88aaaaaaaaaaaaaa88aa88ffccffccaa88aa88bb88bb88))) else (if page < 9 then (if page < 7 then 0xccffccffccccccccccffccccccffccccccfcccfcccfcccfccceecceecceecceeccccccccffeeffeeccccccccffccffccccccccccfcfcfcfccccccccceeeeeeeecccccccccececececccccccccccccccccccccccccccccc00cccccccccc88cc88ccccccccc4c4c4c4ccccccccc0c4c0c4ccccccccc0c0c0c0cccccccc88cc88cccccccccc88888888cccccccc44444444cccccccc00440044cccccccc00000000cccccc88cccccc88cccccc00cccccc00ccccc0c0ccccc0c0cccc8888cccc8888cccc0000cccc0000cccacccacccacccaccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc8ccc8ccc8ccc8ccc88cccccc88cccccc88cc88cccccccccc88cc88cc88cc88cc888888cc888888cc44cc44cc44cc44cc0ccc0ccc0ccc0ccc00cc00ff00ff00cc00cc00cccccccccc00cc00cc00cc00c4c4c4c4c4c4c4c4c0c0c0c0c0c0c0c0bfaabfaabfaabfaabbaabbaabbaabbaabb8abb8abb8abb8abb88bb88bb88bb88bb00bb00bb00bb00babababababababab0b0b0b0b0b0b0b0afafafaf00000000afafafaaafafafaaafafaf00afafaf00afaeafaeafaeafaeafaaafaaffaaffaaafaaafaaafaaafaaafaaaaaaafaaaaaaafa0afa0afa0afa0af8caf8caf8caf8caeaeaeaeeeeeeeeeaeaeaeaeaeaeaeaeaeaaaeaaaeaaaeaaae0cae0cae0cae0cae00ae00ae00ae00acacacacacacacacabaaabaaabaaabaaaaffaaff00000000 else (if page < 8 then 0xf0f2f0f2f0f2f0f2f0f0f0f0fafafafaf0f0f0f0f5f0f5f0f0f0f0f0f3f2f3f2f0f0f0f0f3f0f3f0f0f0f0f0f2f2f2f2f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f050505050f0f0f0f000000000f0f0f0c0f0f0f0c0f0f0c0c0f0f0c0c0f0e0f0e0f0e0f0e0f0d0f0d0f0d0f0d0f0c0f0c0f0f0f0f0f0c0f0c0f0c0f0c0f0c0c0c0f0c0c0c0f0a0f0a0f0a0f0a0f080f080f080f080f000f000f000f000efeeefeeefeeefeeefaaefaaefaaefaaeeeeeeeeffeeffeeeeeeeeeefefefefeeeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeee00000000eeeeeeaaeeeeeeaaeeeeee00eeeeee00eeeaeeeaeeeaeeeaeee0eee0eee0eee0eecceecceecceecceeaeeeaeeeaeeeaeeeaaeeaaffaaffaaeeaaeeaaeeeeeeeeeeaaeeaaeeaaeeaaeeaacc00eeaacc00eeaaaaaaeeaaaaaaee88ee88ee88ee88ee66ee66ee66ee66ee22ee22ee22ee22ee0eee0eee0eee0eee00ee00ff00ff00ee00ee00eeeeeeeeee00ee00ee00ee00ee00aa00ee00aa00ececececececececeaeaeaeaeeeeeeeeeaeaeaeaeaeaeaeaeac0eac0eac0eac0eaaaeaaaeaaaeaaae6e6e6e6e6e6e6e6e0e0e0e0e0e0e0e0dddddddd00000000dcfcdcfcdcfcdcfcdcdcdcdcdcdcdcdccfcccfcccfcccfcccf00cf00cf00cf00cecececececececececcceccceccceccce8ace8ace8ace8ace00ce00ce00ce00 else 0xff00ee22ff00ee22ff00ee00ff00ee00ff00cf00ff00cf00ff00cc00ff00cc00ff00aaaaff00ff00ff00aaaaff00aa00ff00aa00ffffaa00ff00aa00ff00aa00ff00aa00aa00aa00ff008a00ff008a00ff008800ff008800ff000f00ff000f00ff000000ffffff00ff000000ffff0000ff000000ffaa0000ff000000ff00ff00ff000000ff00aa00ff000000ff000000ff000000aa00aa00ff00000000ff0000ff0000000000ff00ff0000000000aa00ff00000000000000fefefefefefefefefefe0000fefe0000fefafefafefafefafef0fef0fef0fef0feeefeeefeeefeeefeaafeaafeaafeaafe00fe00ff00ff00fe00fe00fe00fe00fe00fa00fe00fa00fe00f000fe00f000fe00ee00fe00ee00fe00aa00fe00aa00fcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfcccccccccfcfcfcfc00000000fcf0fcf0fcf0fcf0fcccfcccfcccfcccfc30fc30fc30fc30fc00fc00fc00fc00fafafafafafafafafaf8faf8faf8faf8f8f8f8f8f8f8f8f8f6f6f6f6f6f6f6f6f6f2f6f2f6f2f6f2f6f0f6f0f6f0f6f0f5f5f5f500000000f4f4f4f4f4f4f4f4f4f0f4f0f4f0f4f0f3f0f3f0f3f0f3f0f300f300f300f300f2f2f2f2f2f2f2f2f2f2f2f2f0f0f0f0f2f0f2f0f2f0f2f0f1f0f1f0f1f0f1f0f100f100f100f100f0f5f0f5f0f0f0f0f0f5f0f0f0f5f0f0f0f4f0f4f0f4f0f4f0f3f0f3f0f0f0f0f0f3f0f0f0f3f0f0)) else (if page < 10 then 0xffccffccffccffccffccffcc00000000ffccccccffccccccffcc0000ffff0000ffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc00000ffc00000ffaf0000ffaf0000ffaaffaaffffffaaffaaffaaffeeffeeffaaffaaffaaffaaffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaa00000000ffaaff00ffaaff00ffaaeeaaffaaeeaaffaacc88ffaacc88ffaaaaaaffaaaaaaffaa0000ffff0000ffaa0000ffaa0000ffaa0000aaaa0000ffa8ffa8ffa8ffa8ff8aff8aff8aff8aff88ff88ffaaffaaff88ff88ff88ff88ff888888ff888888ff880000ff880000ff80ff80ff80ff80ff55ff5500000000ff30ff30ff30ff30ff0fff0f00000000ff0aff0aff0aff0aff00ffffffffff00ff00ffffff00ff00ff00ffffff000000ff00ffff00000000ff00ffaaff00ffaaff00ffaaff00ff00ff00ffaa00000000ff00ff00ffffff00ff00ff00ffccffccff00ff00ffaaffaaff00ff00ffaaff00ff00ff00ff0aff0aff00ff00ff00ff00ff00ff00ff000000ff00ff00f500f500ff00ff00f000f000ff00ff00ee00ee00ff00ff00dd00dd00ff00ff00cc00cc00ff00ff00aaaaaaaaff00ff00aa00ff00ff00ff00aa00aa00ff00ff0088008800ff00ff005500ff00ff00ff0055005500ff00ff000f000f00ff00ff0000aa00aaff00ff000000ff00ff00ff000000cc00ff00ff000000aa00ff00ff0000000000ff00f000ff00f000 else (if page < 11 then 0xffffffff00000808ffffffff00000300ffffffff00000202ffffffff0000000affffffff00000000ffffffeeffffffeeffffffccffffffccffffffaaffffffaaffffff00ffffff00ffffff0000000000fffff0f0fffff0f0fffff0f000000000ffffccccffffccccffffaaaaffffaaaaffffaaaaffff0000ffffaaaa00000000ffffaa88ffffaa88ffff00ffffffff00ffff00ffffff0000ffff00ff00ff0000ffff00ff00000000ffff00aaffff00aaffff00aaffff0000ffff0055ffff0000ffff0044ffff0044ffff0033ffff0000ffff000affff000affff0000ffffffaaffff0000ffffff00ffff0000ffffaaaaffff0000ffffaa00ffff0000ffff5500ffff0000ffff2222ffff0000ffff0f0affff0000ffff0f00ffff0000ffff0a0affff0000ffff0000ffff0000ffcc0000ffff0000ffaaff00ffff0000ffaa0000ffff0000f0f00000ffff0000ccdd0000ffff0000cccc0000ffff0000aaff0000ffff0000aaaa0000ffff000055ff0000ffff000055550000ffff00000fff0000ffff000000ff0000ffff000000550000ffff00000000aaaaffff000000000000fffefffefffefffefffcfffcfffcfffcfffc0000fffc0000fff0fff0fff0fff0fff00000fff00000ffeeffeeffeeffeeffeeffaaffeeffaaffeeeeeeffeeeeeeffee0000ffee0000ffeaffeaffeaffeaffdd0000ffdd0000ffcf0000ffcf0000 else 0xffffffffffffff00ffffffffffff0000ffffffffffaaffaaffffffffff00ff00ffffffffff000000fffffffff0f0f0f0ffffffffeeeeeeeeffffffffccccccccffffffffaaaaffaaffffffffaaaaaaaaffffffffaaaa0000ffffffffaa00aa00ffffffff88888888ffffffff80008000ffffffff0f0f0000ffffffff0f000f00ffffffff0a0a0a0affffffff01000100ffffffff00ffff00ffffffff00ff0000ffffffff00aa00aaffffffff00550000ffffffff00440044ffffffff00330000ffffffff00300030ffffffff00220022ffffffff000a0a0affffffff000a000affffffff0000ff0affffffff0000ff00ffffffff0000ee00ffffffff0000ccccffffffff0000af00ffffffff0000aaaaffffffff0000aa0affffffff0000aa00ffffffff00008800ffffffff00003f00ffffffff00003030ffffffff00002a2affffffff00000f0affffffff00000f00ffffffff00000e0effffffff00000a0affffffff00000a00)))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xaee9b874d7aee9b878d7aee9b888d7a6e2135c30aee27884d7aee9b884d7 else 0
  | 4 => if page < 1 then 0x8c1f96d9680dabba6e53834f48c1f96d96b0e2bb8c9f9668f9aee9b885f93e6bba6e53830f9aee2e7e5d939ebba6e5386cdcaee9b94e1039ebba6e1d7e4e7aee9b881f939e537e5b65a07d8b9f96d9680dabba6e21438e7aee2e7e5e139ebba6e1e7e4e7aee9b94e1c36a2e7e5b65ac328a9f96d96b01abb8c9f9744e7aee9b87df939ebba6e227e4e7a6e217e4e70c2bb89e217e4e794df96d9682362e7e5b65a055aee9b94df940ebba6e21724e7aee657e5d139ebba6deb744e7aee9b94e0f39e537e5b65ac79aee9b94df9412537e5b65a0788b9f96d9680c6bba6e2139cd78b9f96d96b276bba6e5388cd7aee9b8551635ebba6e53890d7aee9b885e535eb77e5b65ac9daee9b8856b35e537e5b65ac9d8a5f96d96b0069b94e2835c30aee9b94e2135ebba6e28884d7002bba6e2135eec7e5b65ac9d8a5f96d96b276bba6e53870dbaee9b885f939ebba6e21824e7aee9b94e0d3e6bba6e538a0d7aee9b94df9416bba6e53844e7 else 0
  | 5 => if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0xaee9b94e28794d7aee9b94e285acd7002bba6e538a0d7aee297e5b65ac55bae297e5b65ac08aeeb77e5b65ac9aaee297e5b65ac9aa6e537e5b65ac3daee9b94df96d92eaee9b94df96d92bb7e9b94df96d96baee9b94df96d8adbae297e5b65ac78bae2e7e5b65ac36a6e5e7e5b65ac36aee9b94df9794f9a6e447e5b65ac22aee9b94df9668f9aee9b94e1c7e4f9aee9b94df970cf9aee9b94df96d96ba6e537e5b65ac49b069b94df96d96baee9b94df96d93eb0e9b94df96d96baee9b94df96d945b269b94df96d96baee9b94df96d8fcaee2e7e5b65ac7daee327e5b65ac36a6e5c7e5b65ac36bae297e5b65ac36aee9b94df9754e7a6e537e5b65ac8baee9b94df9744e7aee2e7e5b65ac55bae537e5b65ac78aee9b94e1c5acd7bae537e5b65ac8ba32537e5b65ac8baee9b94e287e4e7aee9b94e1c824e7aee537e5b65ac7daee587e5b65ac78aee9b94e09794e7a8e417e5b65ac22aee9b94e0d458e7aee9b94e28824e7b662e7e5b65ac36aee587e5b65ac7daee9b94dc65acd7ab6537e5b65ac36ab6417e5b65ac36aee9b94de5644e7aee9b94e0d5ace7aee9b94df9618e7aee9b94df9794e7b3e9b94df96d96baee9b94df96d8f9a32537e5b657c22a32537e5b65ac06aee9b94df9768e7aee9b94e0c5ace7aee9b94df96d939 else (if page < 2 then 0xa6e447e5b65ac17a6e537e5b65acb2a6e497e5b65ac17a6e537e5b65ac3fa6e537e5b65ac37aee9b94df96d8f3a32537e5b65ac04a32537e5b65acc5aee657e5b65acdeaee9b94db65acc2aee327e5b65acdeaee9b94df96d92faee9b94df9760e7b229b94df96d96baee9b94df96d8feaee2e7e5b65ac0bba22e7e5b65ac55a6e537e5b65ac4eaee9b94df96d958aee9b94df96d94b8b9f96d96b26c55aee9b94df9414e794df96d96b26c55aee9b94df95ad05addf96d96b26c55aedf96d96b26c55bae527e5b65ac7894df96d96b59c78aee9b94df979505ab2537e5b65ac78002bba6e537e505bae537e5b65ac7794df96d96b1e006a6e537e5b65ac7bac6537e5b65ac78bb2537e5b65ac78ab6537e5b65ac78aee9b94df9404f9b169b94df96d96baee9b94df96d931bb22e7e5b65ac31aee9b94df9728e7aee9b94e1c43ce7aee327e5b65ac78ab6537e5b65ac31aee537e5b65ac7caee9b94df973cf9a6e537e5b65ac43afe9b94df96d96baee9b94df96d942aee297e5b65ac7daee417e5b65ac9aaee9b94e2839cd7aee2e7e5b65ac9aaee9b94e1c734d7aee9b7e5b65ac99bae2e7e5b65ac78aee9b94e175acd7aee9b94e14794d7aee537e5b65ac9a94e297e5b65ac06aee9b94e155acd7ade297e5b65ac22aee9b94e1c458d7 else 0xaee2e7e5b65ac01a6e538a1f939c30aee9b94e217e4e7aee9b8a2217e4e7002bba6e217e4e7bb2537e5b65ac8da32537e5b65ac8daee9b94df9795088b9f96d96b154228b9f96d96b57855bb22e7e5b65ac55aee337e5b65ac55aee9b94e057e4e7aee2e7e5b65ac21aee9b94e28724e7aee9b94e11794e7aee9b94e1c660dbbae5f7e5b65ac8baee9b94e1c5acdbbae2b7e5b65ac8b002bba6e53870dbaee9b94e117e4e7a325f7e5b65ac8b002bba6e53844e7a322b7e5b65ac8baee9b94df9424e7aee657e5b6458e7a6e537e5e539c3faee9b8d5f9794e7ade2e7e5b65ac43aee9b94deb794e7aee9b94df975ce7aee9b99df9744e7a6e537e5b65ac4faee9b94df96d957aee9b94df96d95aa6e537e5b65ac56aee9b94df96d94994df96d96b1fc3f996537e5b65ac3faee9b94ded6d92fa6e536d96b2d43fa6e537e59f5ac43a6e537adb65ac3faee7994df96d92ba6e537e5b64e43faee9b8f1f96d92fa6e387e5b65ac43aee9b94df96912baee9b94df968139a6e377e5b65ac22a6e4a7e5b65ac22a6e497e5b65ac22aee6b7e5b65ad16aee6c7e5b65ad16aee657e5b65ad16a32537e5b659c6ca32537e5b65ac6baee9b94df96d8f4b1e9b94df96d96baee9b94df96d943b4a9b94df96d96baee9b94df96d92daee9b94df9758e7)) else (if page < 4 then 0xa6e417e5b65ac5abae307e5b65ac36aee9b94db6644f9a32537e5b65ac1daee9b94df9614e7aee417e5b65ac7db6a9b94df96d96baee9b94df96d8dbaee9b94df95ad0aaee9b885f95ace7a6e537e5b65ac8da6e537e5e539c49aee9b8e1f9794e7ade2e7e5b65ac49aee9b94dec794e7a6e417e5b659822ba62e7e5b65ac55bae537e5b65ac7dbb22e7e5b65ac36aee9b94e28438e7aee9b94e1c6d8dbaee9b94e115ace7a6e5f7e5b65ac8ba6e2b7e5b65ac8ba32537e5b65ac07aee9b94df9784e7b3e9b94df9794e7aee9b8c1f9794e7aee9b94df979ce7aee9b94df9748e7aeeb78b9f9794e7a6e53871985ac49aee9b901f9794e7a32537e5b65ac09aee9b94df977ce7bae537e5b65ac81aee9b94df9794e4aee9b94df979507aee9b94df9794d8aee9b94df9798e7aee9b94df9750e7aee9b94e247e4e7aee9b94df939cafa6e537e5e539c51aee9b8f9f9794e7ade2e7e5b65ac57aee9b94df1794e7bae537e5b65ac8caee9b94df97950aaee9b94df9428e7a36537e5b65ac06aee9b94e067e4e7aee9b94df974ce7a6e537e5e339c36aee2e7e5b654ce7a6e53865985ac22aee9b7e5ea744e7aee9b94d985ac9faee2e7e5b65ace5a32537e5b659c06aee9b94e257e4e7a6e537e5e539c30aee9b885f9794e7bae537e5b65ac8d else (if page < 5 then 0xaee9b94e096d8ecaee327e5b65ac1ca6e5c7e5b65ac1ca6e537e5b65ac6ea6e5a7e5b65ac36aee9b94df9708f4aa6537e5b65ac36aee9b94e1a7e4fcaee9b94df9790ecaee9b94e086d8ecb029b94df96d96baee9b94df96d946aee9b94df9788e7aee9b94df976ce7a6e537e5b65ac3eaee9b94df96d92aaee9b94df9780e7aee9b94df9774e7aee9b94df961ce7a6e537e5b65ac35aee9b94df96d8f2a32537e5b65ac3894e2e7e5b65ac38a6e457e5b65ac22a86417e5b65ac2294e2e7e5b65ac35a6e2d7e5b65ac22aee9b94df9770e7aee327e5b6458e7aee2e7e5a7458e7aee9b94df9764e7aee537e5b65ac7aa6e537e5b65ac70a32537e5b65ac0faee9b94df9740e7aee2e7e5b65ac47ac6537e5b65ac70a32537e5b65ac70aee9b94df95acffaee9b94e237e4e7aee9b94e1482ce7aee9b855f9458e7aee9b94e267e4e7aee9b886147e4e7ade537e5b65ac8dba6537e5b65ac7d94df96d96b1f42294df96d96b5787dbb2537e5b65ac7daae537e5b65ac7d94df96d96b27036aedf96d96b27036a6df96d96b27036badf96d96b270368b9f96d96b270368b9f96d96b59c36a6e5d7e5b65ac36ac62e7e5b65ac368b9f96d96b0d806b8a2e7e5b65ac36aee9b94df9610e7a6e537e5b65ac5aaee9b94df960ce7a6e5e7e5b65ac5a else 0xaee9b94e0d7e4f9a8e5c7e5b65ac36002bba6e53834f9a3e5c7e5b65ac36aee9b94df9718f9aee327e5b65ac08aee9b94e096d912aee9b94df96d90caee9b94e096d8f9a8e537e5b65ac49a3e537e5b65ac49a6e537e5b65ac57a6e537e5b65ac4baee9b94df96d93da6e537e5b65ac51b429b94df96d96baee9b94df96d8f5aee9b94df96f939aee9b94df96e8f9a6e447e5b657c22aee307e5b65ac06aee9b94df964cf9aee9b94e0a7e4f9aee9b94df96811caee9b94df966cf9a6e537e5b65ac38b329b94df96d96baee9b94df96d8fbaeea394dfb6d96bb1a9b94df96d8f9aeead94df96d93eaee9b8f5f96d8f9aee9b94df96851caee9b94df96e4f9aee9b94e096d939aee9b94dee6d8f9a6e7294df96d91caee9b94df96d927b46a594df96d96baee9b94df96fd3eaee9b94e016d93eaee9b94def6d93eaf29b94df96d96baee9b94df96d94cafa9b94df96d96baee9b94df96d95caee9f94dfa6d96baeea694df96d93eb529b94df96d945aee7c94df96d93eaee9b94df96f545a6e4b7e5b65ac22aee6d7e5b65ad16af69b94df96d96baee9b94df96d95bb4e9b94df96d939aee8194df96d939aee9b94df96f139aee9b94dff6d939aee9b94df06d939aee9b94df96d8fdaee9b8edf96d96baee9b94df96d928aee9b94e177e4f9))) else (if page < 9 then (if page < 7 then 0xaee9b94df9618f9a6e537e5b63e449aee9b8e1f96d8f9aee9b94dec6d8f9a6e447e5b65ac49aee9b94df96e0f9aee9b94df9778f9a3e537e5b65ac06aee9b94df9744f9bae537e5b65ac7caae537e5b65ac7ca6e537e5b65ac41aee9b94df96d930aee9b94e0d5acf9a3e5e7e5b65ac36a6e307e5b65ac8bab2537e5b65ac36aee307e5b65ac8baee447e5b65ac7db66297e5b65ac36aee9b94e167e4f9b66a394df96d96ba6e447e5b65ac2caee9b94df96a8f9b3e9b94df96d8f9aee9b8c1f96d8f9a6e537e5995ac49aee9b901f96d8f9aee9b94df9690f9aee9b94df9674f9aee9b94df9404a8a6e537e56b40449aee9b8f1f96d8f994e327e5b65ac49a6e537e5b65ac69aee9b94e0b7e4f9aee9b94df9654f9aee9b94df9670f9a6e537e5ac3e436a6e447e5b65aca8a6e447e5b657822aee9b94e187e4f9aee9b94df9704f9aee9b94e157e4f9ba6327e5b65ac36aee9b94df9414f9aee337e5b65ac36aee2c7e5b65ac36a6e537e5b63e441aee9b8d9f96d8f9a6e307e5b65ac49aee9b94deb6d8f9a6e447e5b65ac24aee9b94df9680f9aee9b94df96dcf9aee9b94df9678f9aee9b94df9708f9aee9b94db6644a8aee9b94e1c3e4d7a3e537e5b65ac1daee9b94df9700f9aee9b94e287e4f9aee307e5b65ac55aee9b94e0d6d8f9 else (if page < 8 then 0xa6e537e5b65a055b0a9b94df96d96baee9b94df96d93aaee9b885f96d912a6e537e5b65ac5ba6e537e5b65ac42aee9b94df96d937a6e4a7e5b65ac2ca6e537d9b65ac2caee9b855f96d939aee9b94df96a939a6e537e5b659849aee9b94e1c7e4f4a6e537e5b65ac7eaee9994df96d96baee317e5b65ac36a6df96d96b24036aee9b94df95ad0094df96d96b1d8368c5f96d96b0d822a6e597e5b65ac36a6df96d96b24436b3a9b94df96d96baee9b94df96d8faa6e537e5b65a036a6e537e5b65ac30aee9b94df96d968aee9b94df970d39a6e537e5b661849aee9b961f96d939aee9b94df970ceca8e537e5b65a036b3e537e5b65ac7daee587e5b65ac8ba6e587e5b65ac8bbb2307e5b65ac36ab6537e5b65ac55a6e53825b65ac30b3e9b94df96d968b66ad94df96d96ba8e5e7e5b65ac36aba537e5b65ac36aee9b94df961905a8e537e5b65ac57aee9b94df971939a6e5e7e5b65ac49aee9b94df970d45a6e537e5b66184baee9b961f96d93db66a294df96d96baee9b94df970cfcaee9b8e9f96d96bab6537e5b65ac49a6e53835b65ac49b669b94df96d939b66aa94df96d96baee9b94e0d6d939a6e53825b65ac49b3e9b94df96d939b3e9b94e096d96baee9b94df9658f9aee9b94df9768f9aee9b8e5f96d96baae537e5b65ac55 else 0xa6e537e5b65ac4aaee9b94df96d944a6e537e5b65ac4caee9b94df96d93caee9b94df96f539aee6c7e5b65ad20b2a9b94df96d96baee9b94df96d8f7aee6d7e5b65ad20a6e727e5b65ad20aee9b7e5b65ad29aee9b94df969cf4aee9b94df9668f49b1f96d96b458499ca6c7e5b65ad16a6e537e5a045849aee6c7e5a05ad16aee9b7b1a05ad16a6df96d96b34849aee9b94db6594c1a6e537e5b634849a6e537e5b6594c1a6e537e5b65ac50aee9b94df96d94aa6e537e5b65ac3baee9b94df96d8f6aee9b94df9408a8aee537e5b65acc3a6e537e5b65acc1a6e4a7e5b657822aee9b94df9794e9aee9b94df9794f4a6e537e5b65ac2faee9b94df96d959a6e537e5b65ac58aee9b94df96d95d94df96d96b20c51a0e537e5b65ac51aee9b94df36d95aa6e536d96b2e451a6e537e5ab5ac57a6e537c5b65ac51aee8994df96d94b94df96d96b22449a62537e5b65ac49a6e536d96b30049a6e537e5b45ac49aee2f7e5b65ac06a6e4f7e5b65ac2ca6e537e1b65ac2ca6e537e5b65ac39aee9b94df96d8f8aee9b855f96d94baee9b94df96ad53a6e537e5b65aca0a6e537e5b65ac2eaee9b94df96d938a6e537e5b65ac52aee9b94df96d96ab6e9b94df96d96baee9b94df96d96994df96d96b1d030a6e217e5b65ac30aee9b94df96d568)) else (if page < 10 then 0xaee9794df96d939a6e537e5b15ac49aee9b901f96d939a56537e5b65ac49aee9b94df96a539a6e537e5b65ac62aee9b94df96d933a6e537e5b654448aee9b901f96d934a6e537e5b658c3faee9b8e1f96d939a6e3c7e5b65ac46aee9b94df96a536a6e4d7e5b65ac2baee9b94df96a139aee9b94df971d39aee9b94df970939aee9b94df9780e4aee9b94e076d939aee9b94df76d8fc94df96d96b20849aee9b94df96d9409ee537e5b65ac49aee9b94df26d939a6e537e5b65ac5da6e536d96b2e049a6e537e5a85ac49aee9b94df96d947a6e537e5a45ac49aee8794df96d939a6e537e5b65ac6094df96d96b21449a4e537e5b65ac49a6e536d96b2f849a6e537e5af5ac49a6e537e5b64e449aee9b8f1f96d939a6e387e5b65ac49aee9b94df969139a6e4a7e5b65ac4994df96d96b20049a6e536d96b2d849a6e537e5a05ac49aee7b94df96d9399b2537e5b65ac49aee9b94dee6d939929f96d96b21422a4e4a7e5b65ac22a6e4a6d96b2f822a6e4a7e5af5ac22a6e537d9af5ac2294df96d96b20038a92537e5b65ac38a3e537e5b65ac3894e317e5b65ac49a6e437e5b65ac22a6e537e5b65ac40aee9b94df96d932a6e537e5b65ac44aee9b94df96d92ca6e427e5b65ac22aee317e5b65ac1caee9b94df96d90bb62a994df96d96b else (if page < 11 then 0xaee9b94df96d93b94df96d96b21849a6e536d96b2ec49a6e536d96b2fc49aee9b94df96d93fa6e537e5b65ac4594df96d96b21438a3a537e5b65ac09a6e557e5b65ac49a7a537e5b65ac49a5a537e5b65ac49a6e547e5b65ac49a6e537f1b65ac49a6e537e5b25ac49a6e537e5b65bc49a6e537f5b65ac49a6e537e5b05ac49a82537e5b65ac49a52537e5b65ac49a9e537e5b65ac49a6e5380db65ac49a6e53811b65ac49a6e537e5a15ac49a6e537e5a25ac499e2537e5b65ac49aa2537e5b65ac49a6e53809b65ac49a6e537e5a35ac499b6537e5b65ac49a6e537e5b64e451aee8394df96d939a6e387e5b65ac57aee9b94df16d939a6e537e5b65ac63a6e537e5a05ac57aee9a94df96d9399b2537e5b65ac51aee9b94df36d939a6e537e5b65ac5eaee9b94e006d939aee9b94def6d939aee9b8fdf96d96bb569b94df96d939aee7c94df96d93994df96816b20049a6e537b1b65ac51aee8994df96d939a6e537e5b65ac61a6e536816b2d8499b2537e5a05ac49b529b94df96d939aee8094df96d939aee9b94df96996ba6e537b1a05ac49aee7b94dee6d939a6e537e5b654449a6e537e5b658c49a6e3c7e5b65ac49a6e4d7e5b65ac49a6e537e5b65ac46aee9b94df96d936a6e537e5b65ac48aee9b94df96d934a6e537e5a95ac49 else 0xa6e536d96b2f049a6e537e5ab5ac4994df96d96b20c49a0e537e5b65ac49a6e536d96b2e449a6e537e5a55ac4994db65acb620049a6e537e5b633049b129b94df96d96b)))) else 0
  | 6 => if page < 15 then (if page < 7 then (if page < 3 then (if page < 1 then 0xaee9b94df9735b65aee8a6e537e5b65ac31aee9b911f96d96b0c6bba6e537e5b65d96baee9b94df96d96b48abba6e537e5b65ac0caee9b94df96d96b06ebba6e538716b39cd7aee9b94df9794e735ebba6e53849b65acd7aee9b8b9f96d96b1e29b94e297e5b65ac22aee9b94df96d91635ebba6e53851b65acd7002bba6e538716b35ebba6e6494df96d96baee9b94df96d96b23abba6e537e5b65ac15aee9b94df96d96b35abba6e537e5b65ac78aee9b8a5f96d96b1e2bba6e53825b65ace7aee9b94db66456b39eeba6e537e5b65ac36a6e537e5b65ac840dabba6e2e7e5b65ac36a6e537e5b65ac3608a9b94df96d96b57836aee9b94df9795b65aee9a6e537e5b65ac36aee9b94df96d9865aebba8e537e5b65ac36002cfa6e537e5b65aebba6e537e5b65acf9aee8f94df96d96b0d800aee9b94df96d8f9aee9b94df96d96b022bba6e537e5b65ac31aee9b905f96d96b0dabba6e537e5b65dd6baee9b94df96d96b472bba6e537e5b65ac0eaee9b94df96d96b072eba6e417e5b65ac36a6e417e5b65ac840da9b94df96d96b25436a6e417e5b65ac950dabba6df96d96b24836aee9b8a5f96d96b0da9b905f96d96b0d822a6e417e5b65ad5e0dabba6e537e5e55ace7ba69b905f96d96b0d800aee9b94df9794e7aee9b94e0d7e56b39ebba8e417e5b65ac36002bba6e538356b39ebba3e417e5b65ac36aee9b8b9f96d96b022bba6e537e5b65ace7aee9b94df96d96b0d800aee9b94df96d96baee9b94df964d6b39ebba6e417e5b65ac1c else (if page < 2 then 0xaee9b94df96d96b37a9b94df96d96b0d817a6e53905f96d96b05ebba6e537e56b31c17aee9b94df96d95e05ebba6e6794df96d96bb829b94df96d96b05ebba6e537e5b66296baee9b94df96d96b3bebba6e537e5b65ac04aee9b94df96d9715aebba6e537e5b65ad23aee9b94df96d96b482bba6e537e5b658817aee9b94df9794e737abba6e677e5b65acdeaee9b94df96d90e2a2bba6e537e5b65ac17a6e537e5b65ace60dabba6e2e7e5b65acdeaee9b94df9761b65aebba6e537e5b65acacaee9b94df96d96b05abba6e537e5b65acddaee9b94df96d96b1b2bba6e537e5b65346caee9b94df972db65aebba6e537e5b65acb4aee9b94df96d96b2a2bba6e537e5b6434a8ba29b8b9f96d96b0dabba6e53849f9794e7aee9ba0a537e5b65aebba6e537e5b65ac0aaee9b94df96d96b0a6bba6e537e5b65ad52aee9b94df96d96b44ae8a6e537e5b65ac36aee9b94df973d6b39eeba32537e5b65ac78a6e2e7e5b65ac9b0dabba6e53871f95ace7aee9b94df96d8f939eeba6e537e5b65ac78002eb94df96d96b1e29b94df96d96b26c36aee9b7e5b65ac9b0da9b94df96d96b1e022aee537e5b65ad4e1e2e9a6e537e5b65ac78aee8f94df96d96b1e2bba6e537e5b65ed6baee9b94df96d96b41abba6e537e5b65ac13aee9b94df96d96b19aeb94e2e7e5b65ac31aeeb78b9f96d96b0c69b94df96d96b26c31aee9b94df96d90f39ebba6e537e5b65acd7ba69b94df96d96b0c69b94df96d96b21031a6e537e5b65ac3108a9b94df96d96b57831 else 0xaeeb78b9f96d96b39ebba6e8894df9794e7aeeb78b9f96d96b08abba6e53871985ac22aee9b94df97a9e539ebba6e8694df9794e7bae8c94df96d96b01800a32537e5b65ac06aee9b94df9794e70b2bba6e537e5e5744e7002bba6e537e5d139ebba6e538a1f9794e7002bba6e538a1f939eeba32537e5b65ac08aeeb78b9f96d96b15400aee2e7e5b65ac55aee9b94df9795c939eeba32537e5b65ac8b002eb94df96d96b22c00a32537e5b65ac8ba6e537e5b65ace70febba6e357e5b65ace7a6e538b9f96d96b10ebba6e537adb65ace7aee9b94df96d93939ebba6e677e5b6458e7aee9b99e537e5e539ebba6e8494df96d96baee9b94df96d96b0fe9b99e537e5b65ac3f0029b94df96d96b0febba6e537e5b65ad2faee9b9f6537e5b64bc00aee9b94df96d92fa6e6e94df96d96b10ebba6e537e5b65ac430029b94df96d96b10ebba6e7a94df96d92baee9b94df96d96b4ac00aee9b94df96d92baee9b99e537e5b64e6bba6e537e5b65ad39002bba6e537e5b64e69b9ce537e5b65ac22b829b94df96d96b08abba6e6e7e5b65ad16aee9b99df96d96b45aeba32537e5b65ac6caee8c94df96d94e1b29b94e417e5b65ac22a6e537e5b65acd408abba6e537e5b65386caee9b9d6537e5b65aebba6e537e5b65acecaee9b94df96d96b08abba6e537e5b665d6baee9b94df96d96b366bba6e537e5b65e96baee9b94df96d96b38abba6e537e5b65ac14aee9b94df96d96b192bba6e537e5e539c17a6e537e5b65acd505ebba6e537e5b6498e7)) else (if page < 5 then (if page < 4 then 0xa6e417e5b66696b08abba6e537e5a7458e7a6e417e5b65ad1608abba6e537e59a458e7a6e53905f96d96b2a29b94e417e5b657822aee9b94e187e56b39ebba6e537e5da5ace7aee9b94df97791639c00aee9b94df9768e7aee9b94df46d90e2a2bba6e537e5b64e516aee9b94df96d96b1f6bb94e2e7e5b65ac06aee9b94e157e56b39eb7a6e417e5b65ac22aee9b94e1c7e51639ebba6e538a2147e4e7aee9b905f96d96b156ebaee2e7e5b65ac08aee9b94e1c851f939ebbade537e5b65ac7daee8c94df96d96b1f400aee537e5b65ac7daee9b94df97196b39ebba6e537e5b66096bbae538b9f96d96b0dabba6e537e5c35ace7baebb8b9f96d96b0daeba6e2e7e5b65ac36002eb8b9f96d96b0da9b8b9f96d96b21036aee2e7e5b65ac530da9b8b9f96d96b0d822a6e2e7e5b65ad5e0da9b905f96d96b1d422aee2e7e5b65ad4e0dae9a6e2e7e5b65ac36aee9b94df96196b39ebba8e2e7e5b65ac36002bba6e537e58639ebba3e2e7e5b65ac36aee9b8c1f96d96b0dabba6e53829f95ace7aee9b8b9f96d96b072bba6e538716b438e7aee9b94df96d96b22e9ba32537e5b65ac06aee9b94df97456b39ebba6e538a1f95ace7aee538b9f96d96b156bba6e7594df9794e7ba69b905f96d96b08abba6e537e5e539c22aee9b94df97951639ebba6e53851f9794e7bae8c94df96d96b0dabbade2e7e5b65ac36aee9b94e146d90e39eeba6e537e5b65ac8ba6e8c94df96d96b22c00a6e537e5b65ac8baeeb7a6e537e5e539ebba6e537e5e539c36 else 0xaee9b7e5b65ac95072bba6df96d96b23c1caee9b94df9769b65aee1a6e537e5b65ac1caee9b94df96d9855aebba86537e5b65ac1c002c9a6e537e5b65aebba6e537e5b65acfcaee9294df96d96b07000aee9b94df96d8fcaee9b94df96d96b016bba6e477e5b65ac1caee9b94df96d9725aebba6e537e5b65ad25aee9b94df96d96b036bba6e537e5b65801ca6e53905f96d96b0b2bba6e537e5b654ce7aee9b94df96d96b1cebba6e537e5b65ace5b3e9b94df96d96b39ebba6e307e5b65ace7aee9b94df96e96b39ebba6e537e5b6470e7aee9b94df96d96b3babba6e537e5b65acdfaee9b99a537e5b65ae9b94df96d9985ac49aee9b901f96d96b39e9ba32537e5b65ac49aee9b94df96d94839ebba6e537e5b65ac81aee9b94df96d96b392bba6e537e5b65ad07aee9b94df96d96b362bba6e537e5b95ace7aee9b94df96d92439ebba6e537e5b65acedaee9b94df96d96b38ebba6e5385df95ace7aee9b94df96d8e72a2bba6e537e5cc6d96baee9b94df96d96b2869b94df96d96b39c49aee9b8e1f96d96b39e9b94e2e7e5b65ac49aee9b94dec6d96b39e9b94e417e5b65ac49aee9b94df96d96b1c6bba6e537e5b66256ba32537e5b65ac7208a8c94df96d96b1a822aee9b94e0b7e56b39ebba6e537e5965ace7a32537e5b65ac2201a9b905f96d96b0881caee9b94df96516b39e9b94e4c7e5b65ac22aee9b94df96d92039ebba6e537e5b85ace7aee9b94df96d91639ebba6e537e5de5ace7a6e537e5b6578e70dabba6e2e7e5b6458e7) else (if page < 6 then 0xb9edca6e537e5b65aebba6e537e5b65dc22a6e537e5b65dd6b08abba6df96d97f5ad16b729b94df96d96b08abba6e607e5b65ad16b729b94df96d96b0da9b94df96d9600d822a6e537e5b65ac5301abbab6537e5b65ad1caee9b94df9711b63e69b94df96d96b53c36a6e537e5b65ad1c0da9b94df9721b65ac22aee9b94df96d95045abba6e7594df96d91caee9b94df96d95f08a9b94df96d9905ac36aee9b94df97a1b65aebba6e537e5b65aca2aee9b94df96d96b076bba6e537e5b65acf0aee9b94df96d98b5aebba6e537e5b65ac06aee9b94df96d96b45abba6e537e5db6d96baee9b94df96d96b296bba6e537e5b65ac26a6e53839f96d96b03abba6e537e5c35ac0eaee9b94df96656b03abba6e537edb65ac36aee9b94df96d9640dadda6e537e5b65ac36aee9d94df96d96b0dabba52537e5b65ac36aee9b929f96d96b0dabba6e536d96b2f40eaee9b94df46d96b03adca6e537e5b65ac0eaee9b94df96d96f5aebba72537e5b65ac0e002c1a6e537e5b65aebba6e537e5b65ad3eaee9b945f96d96b03800aee9b94df96d93eaee9b94df96d96b00abba6e537e5b65cd6baee9b94dfe6d96b03abba6e537e5b65b96baee9b94df96dd6b03800b0e9b94df96d96baee9b94df96d96b516bba6e537e5b35ac0e002bba6e537e5b6516bba6e537e5b65ac03aee9b94df96d96503abba8e537e5b65ac1caee8f94df96d96b072bba6e537e5b65dc1cb869b94df96d96b0dabba86537e5b65ac36aee9094df96d96b0dabba6e467e5b65ac36 else 0xaee9b94df970d6b3e6bba6e5c7e5b65ac36b668f94df96d96b0da8f94df96d96b2103694e327e5b65ac950dabb8c9f96d96b25436a6e307e5b65ac840dabba3e297e5b65ac36a3e537e5b65ac3608a8f94df96d96b57836ba68f94df96d96b0dabba6e537e5b6648f9aeeb7a6e537e5b63e6bba6e537e5b63e436aee9ba22537e5b63e6bba6e307e5b65ac22aee9b94df96656b08abba6e537e5ea6d8f9aee9b9fe537e5b63e6bba6e447e5b65ac220029b911f96d96b08abba6e537e56b40422aee9b94df96d99a3e400aee9b94df9668f9aee9b94e1c7e5b63e400aee9b94e1c7e4f9aee538c9f96d96b0d800aee327e5b65ac36aee9b9a6537e5b63e6aba6e537e5b65ac67aee9b94df96d8f9066bba6e537e5b63e4f0aee9b94e147e5b63e6bba6e537e5b63e4d7aee9b94df970db63e400aee9b94df970cf9a6e5c94df96d96b0d800a6e5c7e5b65ac36aee9b8c1f96d96b022bba3e537e5b65ac08b3e9b94df96d96b0dabba6e527e5b65ac36aee9b7e5b65ac8f022cfa6e537e5b65ac08aee9b949f96d96b022bba6e537e5b65b56baee9b94df96d96b552bba8e537e5b65ac31aee9b911f96d96b0da9b94df96d96b12436a6e537e5b65dc3608abba8e537e5b65dd6baee9b98a537e5b63e6bba6e8694df96d96baee9b94df96d96b1269b94df96d9775ac490029b94df96d96b126bba6e7794df96d96baee9b94df96d96b066bba6e537e5b65ac24aee9b94df96d96b47ebba6e537e5e76d96baee9b94df96d96b0eabba6e537e5b65aceb))) else (if page < 11 then (if page < 9 then (if page < 8 then 0xbae537e5b65ac840da9b94df96d96b59836bb29b94df96d96b0daeba8e537e5b65ac36ab69b94df96d96b0dabba6e537e5b65ac25aee9b94df96d96b46ebba6e538a1f96d96baee9b94df96d96b156e3b3e9b94df96d96bb3e9b94df96d96b08abba6e537e5b661822aee9b961f96d96b45aebb3e9b94df96d96baee9b961f96d96b0da9b97a537e5b65ac36bb2a394df96d96b0daa394df96d96b21036ab6537e5b65ac950daa394df96d96b25436a6e5e7e5b65ac840dabba8e307e5b65ac36a8e537e5b65ac3608aa394df96d96b57836ba6a394df96d96b0daecb3e9b94df96d96baeea394df96d96b156e9b3e9b94df96d96baee9b979f96d96b0d800a6e5e7e5b65ac36b3e9b94df96d96b0c6bba6e53825e56d96baeead94df96d96b0d800ab6537e5b65ac36b92cfa6e537e5b65aebba6e537e5b661825b669b94df96d96b076bba6e587e5b65ad1bb669b9d6537e5b65aebba6e53835b65ac22aeea394df96d96b08ad9a6e537e5b65ad16b3e9b9d6537e5b65aebba6e53825b65ac22aeead94df96d96b08acfa6e537e5b65ad16b3e9b94df9795b65aebba6e53825b65ac36bae8f94df96d96b0dad9a6e537e5b65ac36a6e53911f96d96b08abba6e537e59a5acf9aee9b94e1c7e56b3e6bba6e327e5b65ac36aee9b9d6537e5b63e69b972537e5b65ac22aee9b94df96d8f908abba6e537e5b6458f9aae9b94df96d96b0dabba6e537e5e56d8f9aee9b94df97956b3e400aee9b94df9794f9aee9b9a6537e5b65aebba6e537e5b65ac67 else 0x94df96d96b23c840dabba6df96d96b24c36a6e537e5b65ac8a0daeb94df96d96b1d436aee537e5b65ac850dabba4e537e5b65ac36aee9b7e5b65ac960dabba6e536d96b2f836aee9b94df96d9630dabba6e537e5b65acaaaee9b959f96d96b0daa2a6e537e5b65ac36a6e5694df96d96b0da9b959f96d96b0d822a6e477e5b65ac3608a9b94df96d96b58436a6e537e5b65ac4908abba6e537e5b65d56bac69b94df96d96b0da9b9d2537e5b65ac36a6e537e5b65aca80da9b94df96d95e0d822aee9b7e5b65f96b45a9b94df96d9755ac36a6e537e5b65ac540dab0a6e537e5b65ac36aee9b7e5b65ac940dabba6e387e5b65ac36aee9b94db65acba0dabba6e537e5b654436aee9b94df96d9885aebba6e537e5b65ac34b7a9b94df96d96b0da9b94df96d97c5ac36aee9b94df96d96b2a6bba6e537e5b65ac1ea6df96d96b23c3608a9b94df96d96b0d806aee9b96df96d96b0dabba6e347e5b65ac36aee9b94df96d96b1bebba6e537e5b65ac3394df96d96b538840dae2a6e537e5b65ac36a6e537e5b65acc40dabba6e537e5b65ad21aee9b94df96d96b0469b9ca537e5b65ac36aee537e5b65ac800dabb9b2537e5b65ac36aee9b94db65acb60dabba6e537e5b64e436a6e537e5b66016b0da9b94df96d96b31836a6e537e5b65ac360b29b94df978db65ac36aee9b94df96d98e5aebba6e537e5b65ac2aa6e537d1b65aca60dabba6e537e5b65acabaee9b94df96d96b0b2bba6e537e5b65ad53a6e537e5b65ac880dae9a6df96d96b25436) else (if page < 10 then 0xaee9b94df96d8cf01a9b94df96d96b0b422a6e537e5f46d96b0b2e6a6e537e5b65ac2caee9b94df96d98f5aebba6e537e5b65ace8aee9b94df96d96b01ebba6e537e5b65d16baee9b94df96d96b462bbae29b94df96d953a6e53865f96d96b08abba6e537e5b659d16aee9b94e237e5b65aebba6e537e5b65ac9eaee9b94df9789b65aebba6e537e5b65ac9faee9b94df96d96701a9b94df9795b65ac30aeeb7a6e537e5b65a2bba6e8b94df96d96baee9b94df96d96b006bba6e537e5b65ac30a6e538a1f96d96b0c000a6e537e5b65ac30aee9b94df96d96b5a2ecaee9b94df96d968002bba6e537e5b65a2bba6df96d96b25c08a6e537e5b65ac5508a9b94df96d96b57855bb29b94df96d96b156bba6e537e5b65e56baee9b94df96d96b45ebba6e537e5b65ac10aee9b94df96d96b086bba6e538a1f96d912ada9b94df96d96b08abba6e537e5b645912aee9b9aa537e5b65aebba6e537e5b65ac59aee9b94df96d96b06abba6e537e5b65ad10a6e537e5e56d96b126bbade9b94df96d939ade9b94df96d96b126bba6e53871f96d939b8e9b94df96d96b0b2bba6e7594df96d953ba69b94df96d96b126bba6e537e5e56d939aee9b94df96d8ce08abba6e537e5b659822baecba6e537e5b65aebba6e537e5e56d8ecba69b94df96d96b156bba6e537e5e56d912aee9b7e5b65ac970daeba6df96d96b25c36a6e537e5b65ac970daeba6e527e5b65ac36a6e537e5b65ad670dabba6df96d96b26036a6e537e5b65ac980dab794df96d96b21036 else 0xaee9b94df96d96b4d6bba6e537e5b65ac47aee9b94df96d96b446bba6e537e5de6d939b869b94df96d96b08abba6e717e5b65ad16a6e537e5b65acd108abba6e537e5b66316baee9b94df96d96b386bba6e537e5b65ac0faee9b94df96d96b28ebba6e537e5b661d6baee9b94df96d96b3c69b94df96d96b34c1cb269b94df96d96b45abba6e537e5f46d8fcaee9b94df96d95e3b2bba6e537e5de5acdeaee9b94df96d95e2a2e3a6e537e5b65ac22aee9b94df96d95e08a9b94df96d96b32c22a6e537e5b6578cb08abba6e757e5b65ad16b8e9b94df96d95e08abba6df96d97d5ad16aee9b94df9785b65ae9b94e1c7e5b65ac49baebba6e537e5b64e6bba6e537e5b65ac09aee9b94df977db65aeeba6e537e5b65ac49aee9b94e147e5b64e6bba6e537e5e96d96baee9b94df96d96b452e9b2e9b94df96d96baee9b94e147e5b63b2bba6e537e5e66d96baee9b94df96d96b556bba6e53891f96d96baee9b94df96d96b2be9b94df9795b65ac51aeeb7a6e537e5b656ab7a6e537e5b65ac57aee9b94e1c7e5b652ebbaea9b94df96d96baee9b94df96d96b1469ba1a537e5b65ac510029b94df96d96b146bba6e537e5b65ad5aaeeb9a6e537e5b656800aee9b94df96d95aae29b94df96d96b15ebba6e537e5b65ac570029b94df96d96b15ebba6e8a94df96d94baee9b94df96d96b52c00aee9b94df96d94bbaa9b94df96d96b126cba6e537e5b65ac06aee9b94df96d9815aebba6e537e5b65ad13aee9b94df96d96c5aebba6e537e5b65ad56)) else (if page < 13 then (if page < 12 then 0xaee9b94df96d96b196bba6e537e5ce6d96baee9b94df96d96b1a2bba46537e5b65ac06b2e9b94df96d96b08abba6e567e5b65ac1caeea194df96d96b08abba6e487e5b65ac22aee9b9da537e5b65aebba6e537e5b65ac18aee9b94df96d96b08ebba6e537e5b65ad1daee9b94df96d96b0f2bba6e537e5b65aceab9edda6e537e5b65aebba6e537e5b65cc22a6e537e5b65ad2008abba6e757e5b65ad20aee9b94df9775b65aebba6e537e5b65aca7aee9b94df9771b65aebba6e537e5b65aca4aee9b94df96d96b07ebba6e537d5b65ac0eaee9c94df96d96b08abba6e4e7e5b65ac22aee9b94dfa6d96b08abba6e537e5b35ac22aee9b94df96d96308abba6e537e5b85ac17aee9b94df96d96108a9b94df96d9a75ac49aee9b94df96a56b45a9b94df96d9ac5ac49aee9b94df96d95145abba6e537e5b65acb7aee9b94df96d96b456bba6e577e5b65ad16aee9b94df96d9163b2bba6e537e5b65ad1eaee9b94df96d96b382bba6e537e5d96d96ba6e537e5b66696b126bba6e537e5a85ad16a6e537e5b65ad4e126bba6e537e5a45ad16a6e537e5b65ad5e126bba6e537e5b65acb3aee9b94df96d9705aebba6e567e5b65ad16a6e537e5b65ad16126bba6e537e5a05ad16aee9b94df96d96b3069b9d5f96d96b45849aee9b9b1f96d96b45abb9d66c7e5b65ad16002bb9b1f96d96b45a9b9d6537e5b645849aee9b9d5f96816b45ae7a6e537e5b65acc1a6e537e5f46d96b30400a6e537e5b65acc1aee9ba16537e5b65aebba6e537e5b65ac2b else 0xaee9b94df96d96305ebba6e5384df96d939ad29b94df96d96b17ebba6e387e5b65ac34aee9b94df96d948392bba6e4a7e5b65ac1ca6e7f94df96d96b126bbace9b94df96d939aca9b94df96d96b126bba6e8894df96d939b8e9b94df96d96b126bba6e7594df96d939aee537e5b65ac8608abba6e4d7e5b65ac22aee9b94db65acbf08abba6e537e5b15ac22aee9b94df96d8cc08a9b94df96d96b13422a6e7e94df96d96b08abb94df96d96b20822aee9b8f1f96d96b08abba6e536d96b2e022aee9b94df96916b08abba6e537e5b632822aee9b94df96d93908abba6e537e5b65ad41aee9b94df96d96b082bba6e537e5b65acb1aee9b94df96d96b1b6bba6e537e5b634022a6e537e5b65acd008a9b9ca537e5b65ac22aee537e5b65ac8008abba6e387e5b65ac22aee9b94db65acb608abba6e537e5a05ac22aee537e5b65ac8508abba6e4a7e5b65ac22aee9b94db65acbe08abba6e537e5af5ac22a6e7594df96d96b126bba6e7f94df96d939b8e537e5b65ac8508ae3a6e4a7e5b65ac22a6e53929f96d96b08800a6e4a7e5b65ac22b8e9b94db65acbe08ae3a6e537e5af5ac22b8e9b94df96d8cb08abb94df96d96b1d822aee9b8bdf96d96b08abba6e537e5b65ac27aee9b94df96d96b46a9b95a537e5b65ac49aee9b94df96d96b0e29b96e537e5b65ac380029b94df96d96b0e2bba6e537e5b65acf4aee9b94df9715b63d000aee9b94df96d8f4b369b94df96d96b08a9b98e537e5b65ac22a6e6194df96d96b08abba6e6894df96d96b) else (if page < 14 then 0xa6e7594df96d96b15ebba6e7f94df96d94bae29b94df96d96b1269b94df96d96b200499d6537e5b65ac801240094df96d96b20049a6e8694df96d96b1269b9d6536d96b2d849a6e537e5b65acb612400a6e536d96b2d849b969b94df96d96b126bba6e537e5b66356baee9b94df96d96b3a6bba6e537e5b65e16baee9b94df96d96b466bba6e537e5b65ac12ace9b94df96d96b126a4a6e537e5b65ac49a6e8e94df96d96b1269b94df96d96b12409a6e537e5b65ac540d29b94df96d96b15006a6e537e5bb6d96b1269b94df96d9ad5ac49a6e537e5b65ac4904a9b94df96d96b13420aee9b94db65acbe03abb94df96d96b21c0eaee9b94df95acc803abba6e537e5b63340eb5a9b9d6537e5b65aebba6e7f94df96d93eb5e9b9d6537e5b65aebba6e7f94df96d945a6e537e5b66816b1269b9b2537e5b65ac49aee9ba1a537e5b64e6bbae69b94df96d939aee9b941f96d96b03abba6e537e5a05ac49a6e7594df96816b12400a6e537e5a05ac49aee7b94df96d96b4e6bb9fe7b94df96d939002bb9ee537e5b64e6bba6e8a94df96d9399d66c94df96d96b126bb9b2537e5b65ac490026c94df96d96b126bba6e537e5b15ac0eaee9b9fe537b9b64e6bba6e537b9b65ad39002bba6e537b9b64e69b9ca537e5b65ac49aeeb2a6e537e5b64e6bba6e7094df96d96baee9b94df96d96b172bba6e537e5e06d96baee9b94df96d96b17ebbad69b94df96d939aeeafa6e537e5b64e6b4a6e537e5b65ac5caee9b94df96d939082bba6e537e5b654515 else 0x2bba6e6f94df96d96ba6e7594df96d96b146bba6e7f94df96d95a)))) else 0
  | 7 => if page < 3 then (if page < 1 then 0xba6bba6e537e5b65ac36002bba6e537e5e56d96b002e9a6e537e5b65ac36aeea3a6e537e5b65ac36002bba6e537e5b66196b002bba8e537e5b65ac3600000b3e9b94df96d96baee9ba3e537e5b65ac36002bba6e537e5b65acf9002bba3e537e5b65ac3600000aee9b94df96d8f9aee9b94df96d96b0d808002bba6e537e5b65ac08aee9b94df96d96b0d831002bba6e537e5b65ace7aee9b94df96d9775ac36002bba6e537e5b65dd6baee9b94df96d96b58036002bba6e537e5b65ad1caee9b94df96d96b2980e002bba6e537e5b65ac0eaee9b94df96d96b0d81c002bba6e537e5b65ac1caeeb7a6e537e5b65ace7aee9b94df96d96b39c36aee9b94e2e7e5b65ace7aee9ba22537e5b65ace7aee9b94e2e7e5b65ac22aee9b94df96d9985ac22aee9b94df97a9b65ace7aee9b9d6537e5b65ace7aee9b94e417e5b65ac220029b94e417e5b65ac22aee9b94df96d96b39c22aee9b94df96d96b458e7002bba6e537e5b6458e7aee9b94e147e5b65ace7002bba6e53871f95ace7aee9ba32537e5b65ac36aee9b94e2e7e5b65ac36002bba6e2e7e5b65ac36aee9b94df96d96b438e7aee9b94df9795b65ace7002bba6e537e5e55ace700000aee9b94df9794e7aee9b99e537e5b65ace7002bba6e6794df96d96baee9ba32537e5b65ac6c002bba6e537e5b65ac6caee9b94df96d96b39c17002bba6e537e5b65ac17aee9b94df96d96b39cde002bba6e537e5b65acdeaee9b94e127e5b65ace7002bba6e537e5cd6d96baee9ba32537e5b65ac78002bba6e537e5b65ac78aee9b94e2e7e5b65ac31002bba6e537e5b65ac31aee9b94df96d96b39cd7002bba6e537e5b65acd7aee9b94e417e5b65ac36002bba6e537e5b65ac36002bba6e417e5b65ac36 else (if page < 2 then 0xaee9b94df96d9ac5ac22aee9b94df96d96b45822aee9b94df96d96b53916aee9b9d6537e5b65ad16002bba6e757e5b65ad16aee9b94df9779b65ad16002bba6e537e5da6d96baee9b94df97d1b65aca8002bba6e537e5b65aca8aee9b94df96d96b4581caee9b94df96d96b458deaee9b94df96d96b57822002bba6e537e5b65ac22002bba6e537e5b657822aeeb7a6e537e5e56d96baee9ba22537e5e56d96baeeb7a6e537e5b65ac22aee9b94e1c7e5b65ac22aee9b94e1c7e5b65ad16aee9ba1a537e5e56d96b002bba6e8694df96d96bbaebba6e537e5b65ac06002bba6e537e5b65ac06aee9b94df9795b65ac2c002bba6e537e5b65ac2caeeb7a6e537e5b65ad53002bba6e537e5b65ad53aee9b94e287e5e56d96b002bba6e538a1f96d96bbaebba6e537e5b65ac08aeeb7a6e537e5b65ac55002bba6e537e5b65ac55aee9b94e1c7e5b65ad12002bba6e537e5b65ad12aee9b9d6537e5e56d96bba6bba6e537e5b65ac22aee9b94df9795b65ac22aee9b94df9795b65ad16aee9b94e147e5e56d96bbaebba6e537e5b65ac36002eba6e537e5b65ac36aee9b94df96d96b14c36aee9b94df96d96b254360029b94df96d96b25436aeeb7a6e537e5b65ac36aee9b94df96d96b210360029b94df96d96b21036aee9b94df96d96b1d436b8ebba6e537e5b65ac36aee9b94df96d96b32422aee9b94df96d96b0d8220029b94df96d96b0d822aee9b94df96d96b578360029b94df96d96b57836aeeb2a6e537e5b65ac36aee9b94df96d96b2b822aee9b94df96d96b1d422aee9b94df96d96b53836aee9b9d6537e5b65ac36aee9b94df96d96b29822aee9b94df96d96b21022aee9b94df96d96b45836aee9b94df9795b65ac36aee9b94df96d96b29836 else 0xaeeb3a6e7594df96d96baee9ba1a7594df96d96baee9b9d6537e5b65ac490029b9d6537e5b65ac49002bba6e537e5b65ac4900000a6e537e5b65ac49b9ebba6e537e5b65ac0eaee9b9fe537e5b65ad39002bba6e7f94df96d939002bba6e537e5b65ad3900000aee9b94df96d939aee9b9fe7594df96d96bb96bba6e537e5b65ac22aee9b94df96d96b0a022aee9b9fe537e5b65ac22aee9b94df96d96b2c022aee9b94df96d96b1c822aee9b94df96d96b32c220029b94df96d96b32c22aee9b9d6537e5b65ac22aee9b94df96d96b2f422aee9b94df96d96b1a822b8ebba6e537e5b65ac22002bba6e7594df96d96b002e3a6e537e5b65ac22aee9b95a537e5b65ac22002bba6e537e5b662d6baee9b94e477e5b65ac22002bba6e537e5b65acecaee9b94df96d96b08806aee9b94df96d96b0881caee9b94df96e1b65ac22002bba6e537e5b65cd6baee9b94df96d9ae5ac22002bba6e537e5b65ad20aee9b94df96d96b0880eaee9b94df96d96b08817002bba6e537e5b65ad16aeeb3a6e537e5b65ad16aee9b94df96d99a5ac22aee9b94df96d9a75ad16aee9b9fe537e5b65ad16)) else 0
  | 8 => if page < 1 then 0xaee9b9d6537e5b65ac00002bba6e537e5b65ac2200000aee9b94df96d96b45800002bba6e537e5e56d96b00000aee9b94df96d96b0d800002bba6e537e5b65ace7 else 0
  | 9 => if page < 1 then 0xaee9b94df96d96b else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 6
  | 4 => 58
  | 5 => 713
  | 6 => 899
  | 7 => 170
  | 8 => 6
  | 9 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 1024
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 10)

def pool (k i : ℕ) := decode (k+1) (field encodedPool k (10*(k+1)) i)

def entries : ℕ → ℕ
  | 3 => 20
  | 4 => 179
  | 5 => 1790
  | 6 => 2459
  | 7 => 615
  | 8 => 60
  | 9 => 1
  | _ => 0

def keys (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xf5bd3cabf3b62e5bea0a4ab6d5799febc2482701b52e50aaab2927dfa37b8d3a9f5251148be919e98088b7127f212aa06fffbbac5b6f10e1537d18c32bac4afb2b84400f2a0109871fdd7d510f3aef1d else 0
  | 4 => if page < 3 then (if page < 1 then 0x608019e45efc14715eed31d85e112bcf5dc5f5295d9483ec5d1dda645b6f10e156bddbbb54c264f3542a62905084d9c54decc9964d8fc9814c6745134bddf8c54b07bf504772e57145ad11af459c18e2451e20d144fb592244a5c22d433b427b4328179240c23e0040b0a36840588a283f1c12983efedb6c3ee14bf43ec1710f3d494d913ceff5003b4f757d397e138a3960dc5e3923720136786fe734fb78752fb03b262e931cbc2c65214129ab1a3928c6b6b026becab225da554b20a760231eb366901ca19abf1b684cab18c4da981878d58c1411399d1391c7a2138d51c813666b0211a64d930ee464000c5c2b230b424fa80a56b3ca04339da0036e7eec else (if page < 2 then 0xb8b1eb24b5a5ac1cb495513db3cb03ccb1067e4db056a31eaf06077facb43ba8aca7b459ac585717abbaed9aaab83729aa2d2dbda87547d8a8724702a4c2438aa4a8d786a3896d22a14d42c29df68bb59dc94e609bddd45197f88f3097ef66129701cde596e7c5c39569c70394b031e78e1bc8a78743e3ca86e8396186722723866d044f85c9df33854cdeb284fcbf528386ec4a835105be8201c4cd807068947e9f462f7e3754a37cc96ad67b5faa707b46344e790147217832088c77c9526c76468e7d7526f3cc745ed8d4738950567265a280707a28716f8ff2446e77438b6b19b0c36aa3d383684c542f6640868f65aa4adb6593c68b64550c8060ee2429 else 0xffeea722ff1da36ffb2f6a09f9f70ed2f96a61b0f925259ef56df9eef5274a59f4a89e86f40e0ac8f3b62e5bf32867f0ed00c5b9ecfa6861e7900dabe73740e2e6f2d068e29e94eede4f1db7ddd37ac5dcde64bfdc63a3a8dc0c5d91d5799febd2ecc2fbd25cb609d22b2d33d1cde1d9d0dabf08d0a76af4d0665567cff6ba8ccec23267cd4295efc9f2dbd2c97eb29dc6a6145ec4d6bceac44cb7efc2f84410c27700fdc20f2231c1827289c144e673c06b738bc04e3c5fc010d202beaeb8e1bb5e9892b9ec0397b9564158)) else 0
  | 5 => if page < 28 then (if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0x9f715eb09f6307c09ef7bb609ec110509be9eb509b6790a09948e36099336db096fd5d308d5524f082ac24807f97a3d07eebbb307cf8ea107a762990768276a0750a7a10742f2c60730a8ae072862f906fa94ce06f7e12e06ead6e30675e5e9064b8633062cc51806020ccb05da7c04058f0af1052f035e0509901b04e7906d04bff74b04ac7ff704aa165104a89cc60451efe604249862042315aa03f95a9803e0587903a6772102f9467d02e58fee02bb0717028611f90279b6bc02385b050216e04a020d0d2c0206c80c01ebb1c901da11b901bdb5f201b87d9101702115016cb4aa0136b44500bf0e6900bddb52004b32460028dcc800270593002305c3 else (if page < 2 then 0x1490c1551458252213f1e7441394af631373cf68133055df12f1b26712e8865f12d8d55012d3caa012b9283312b45cf7128cf53212890f8d1276cacc1271e846121f68271210460311e0c2ea11d2bc471183dfb4117a58e11122e11810c07a91108f1c8d100736d80fe091480fd3bd7f0fcab8c50fbb56cf0fa16cd00f8132020f7619b60f4ff3c80f000ef50efbaf0d0ebf8f890ea6a5860e9a0f0e0de950010dc2301f0d91eab50d69d7630d69191a0d60e7b10d37d8ff0d2c6de90ceafddc0c3bc57f0c3b85ed0c0b41950bfa91680baa532d0b7725550b08a04c0b0166020ad05e9a0abee8180aa590120a9b6c1f0a79b5be0a56b3ca0a43120a09f9d6a1 else 0x1e08316f1db6f9961d80a9771d0f7d331cf271e31cee48d91cedf6021cdb3f671c96793a1c8dbd981c7c9a891c763e391c71cd6c1c660bb51c42b95d1bf20ced1bdb93121ba49b1d1b7c8ee71b0adf5e1afea23a1ac3dd641abb6f161aae22141aa4f3f51a7871921a7018bb1a5b3a661a42110f19f0c54419d20fc419c0dfec1983356c193e891319120ae91905dba318acc6a718a215f4188e16bc1852892b184fcc6018491473183c3ec8181028271807725317c672be17b12ae41786e07f177ef9f51775fc831738733917373eea172cecb11721b90c16f9d25816ac79521602877c15de8fd9152b29a1151f24d51503ded414ffbe8714fe195414c52553)) else (if page < 5 then (if page < 4 then 0x2614a06b2613f93f26049fad259f01182595eced256e4106251e7d222518213f2511536424e46afa24d6458b24be4b282485e9dc24623716244af2d9241963de23e8eea123e671b623db7c62236939c6232e185a2311090022f9354322ce113e22620a15224da7fb2249c11f2219972d21f79df021f3dc5521acd25a218aa8ff217401f22157834b213f743f20f2c82220e5508e20c7232c20b692dd2071e0a42039213c2017b7211ff50c011fc489a01fb79aa01fab90451f8885cd1f82aec81f80e3a71f7f895e1f7010c21f5ad9151f3bd31a1f1fdac71eeb09f11eddb7091e9b700c1e902dfb1e87c0b61e8548721e84768c1e7d80ed1e203dc41e132ccc else 0x2e02397d2dfb20772d9448fd2d921df12d800be82d67e58b2d23cf392d1611b82cfed9b82ce5e9b72ce333f62ce24aea2ccef1ac2ccbde6c2cc84c722c80c6052c7f53922c64a4292be696b72bd97e2c2bb1bccf2b7da8632b664f102b5ce8992b3fa44c2af9b4012aee36fc2ad0b4442ab71a132ab1cc9c2a9f7fd42a8f83542a8cc65d2a8cbfdd2a78bf1d2a689d902a661a7f2a37d7652a37b8eb2a25e38e2a19ebee2a11908529ef98c329b545c4299eef29298b1c6f297c614f297be6ca292910c62905090a28d0037928966d64289483cf288a1bd32876c41e28763e212844855e2737048e26becab226bc04592689e17a267f5479267bb5c5267949c9) else (if page < 6 then 0x35bba22235b90ad635b89f3035b7b1833598a979359088dc354758ec352ec6853525ab0435217c22351bf30734e37aa034949d9c34914b633490227a348baf0d3489ab223485dd7b343f3502340846df33ad72f43391bdb433662c14335e8d1b333b78e333173147330d3ac732b7db13324f3840323e5c283221bcd731fb71f031ad95f631aa6ce031934158317fd0c6314d9242313b8b06313b47f43128a3a23102a62530f25d4f30dd792930d178a130b629ac30970d3330941c61306da2b43036d213303517033033a0f130064e7d2fc071c62f722b742f68d1502f5794122f2355322f1713872ef4123e2eb64e642e5cfa482e5958a22e4960242e2b7a25 else 0x3fc393863fb5d86f3efedb6c3ebe88a13eb46cef3e794c3e3e5421e43e395bc83e2d1b983e065c483de498eb3de1d0bd3dbc7ba93dbc4e343da7df953d7f4b193d38cbc43d0704303cdac4ba3cd6a8863c717d3d3c432b3b3c1322b33c107f803c0c597d3c07968b3bfbcf6f3bee2a783be9730b3ba38ae63b9e92bc3b3519783b34aa383ad4a1893aceb5963a7043c83a67af103a61ef403a58ace23a3069803a20e14e3a023ffe39fd1e1239c5431739b4e2fc39ac01f739964e193966614f3960dc5e395e7abf395a959d3956db0b394779a7388af30037901b27377d568e37246a41371c9f5c36ebdf2b36d8a2c9369f67103685d13e363a974135cb7c5f))) else (if page < 10 then (if page < 8 then 0x47f7b87447ae5b4f479b2c5f4778083b476a7702474f3ad44740f811472c3c574724c6b447157f7e4712a22646cf0dc546b517cc46ab6c3946811405467e72aa46593fcf4655912046085faf45f267f045e72d7c45cba2ee45997cf8458bfdff457b9923456c255d4553358f4512f81944fb592244f4f6e044d1c63444b8ae3b446ad12243b5cbce43aa5c6f4383bb7f436b42a6433f1f59433b427b43372cc3430503ab42e6b44742d82d3e4294ef9e426cb1da420e2e4a41eb692f41e3c02b41a8d8c1416cc5654168f0db4157d013410ed3b9410724eb40e8775040d8a95f40c0fe6e40c0bfe840bfaf0140994938406d080f406706a0402caa6f4027ffff else (if page < 9 then 0x535d1301531e9ecc5318a8b0530eecb352d7b68d52b2bf41525522dd524cacc1521f659a51e8677651a2ed77516c9e3b516b9fb05150eb34514d50b05124494450ddcda950581b8c50496c3d50481c155042fdba5028754b501aed285001260f4fe900aa4fe7a2834f426b364f247b154ece4ef84e6fd0c74e68a04a4dc2017a4d6e16bd4d549edd4d3565f74d17c1c14d0fbe434d0146d74cfeec0c4c8046b54c13ad2a4bd6876b4b7171354b5dbb7b4aaacdbf4a6a50654a5d9a954a588a444a24b2c94a19941449eda60449e09c3c49c5393549bfe39e49976e5b497d6faa49110707489a1ca84882a9134878309848781d3d4867f4b84819c73d48113617 else 0x5c0fabfb5c0c4d415bfd8aae5bbcc9785ba35cd05ba13f2a5b72cbb85b50b4af5aecc6e25a278ec95a19624e5a186ab459de2e4859ca797f59988def5980e214596db93d59628c43595c55495933423859322d9458e3f48858e3b7c8588b0f0a57e0f0c757b93da157a036a15789e48957708a1c57647841576258c3574573135719462a56e487ad56e43b5456c8b01d568f703d567d49d75670ea2e566c41e75664066b5650b9ce561124f25603401c55f6f6f555dc6afd55ca2df455a884fb5580f327556eee0a555b790355285c2454eac6ef54e3f08c54d85ef454815121544323a5542cfa2b53fa8ee153f0cf2253d90a0153d60d06538e67865380f51a)) else (if page < 12 then (if page < 11 then 0x64bad0f664b145aa649a96f06462fa35644729a163cd3fdf63bc1108637d9baa636cbce3635a0620634d47806344ff126340ff6f63367f09632e0f22631edeae62e273f0629881916240599a623c256a6231e50c61e2494361a16bc7619b61cf614e3f88612ed93a611d75e860f0eb5360c051dc608ab9b5606f8bb360298ec75ff31a285fe4c0525fc73e455fbb48635f9dbb175f9472525f86f3835f5e81ff5f3fb1c55eb963755eb55bf25e97ab405e30dd505e2d9c085e0a03355dffa3a95dff90ae5def76ae5da155ea5d62acfe5d2be84c5d1f14475d1141d65d0c62115cfc78a65cf9b2c15ccf577a5c877a6f5c5ce74c5c5776cc5c36518b5c1ea543 else 0x6e0715a06d96c0f16d6ebcec6d4a604a6d07e7cd6cec20486cd26a966cb247c16c98867d6c97b6116c4f541e6be333b06bd67f3e6bbe0cee6bb315cf6ba73f446ba472bd6b3cea7e6b0177fc6af6ef8b6a78544f6a5bd4a76a26b0dd6a052f636a01067c69f7207269d74aa969be005369b1a0c2696396cb6955edbe694760b2693f0bc569104a8f68d659d468d16ccb68c462c468b5c90368a9d4ba68a37066688529eb6881804b68793cdf6874f0a56872711a6842d03868231ec167dd77c367cb543c67c6920167884d6a676af5f76735669d66ed965066e6c82e66b4f49866b347ff664299c666361eea65fdff536587f9376582051b6576c2506569c58f) else (if page < 13 then 0x786158fc7839409a78197393780a39d777c9526c77ad731177a89be977897aa9775ff702771344e976d0ef9b76cb88347685b3b07654cef175d23d927585bdc77579e96f753f7c9b753d81b7753423bd75087a4774f5462974e4ca4574e1f86774c60c03749e4d9474709dea73fb94f073a317c7738135bf7332010d72ca41b572a1070f726a06b472544ea5722509d5716d8488715413e0714ca7d5711ee375710a95f87102d5fe70c625fd70c1e05f70a30f4f7082df33705e5b41703801d770260c0670217b26701d7b926ffd7eb86ff4fd846fd2cf376fc9ef746fabb9066f764d3b6f2c7f806ed180216e7699ae6e6191136e4c07636e4824806e31b7de else 0x81e0f5b781549b89815363d181461042811b46198113b9c28111e322810a387681029f9a81015bb280fa5d2380f565ed80e3163480da391280c31ca680b9ae8180b783f38024710b7ff1b5bb7fe488267f4d7c1e7f3365407f31a7de7f1f7f2b7f0cbfb07ef1bc6c7ecff3547ebf2b1f7ead606a7e6e5e767e53b2477e51fe217e34e22f7e2c1d497e2506117dc63d767d87f19d7d770cbb7d4cbd647d3fed5f7d1776037cc49ec97c08c17d7bcf79997bb772bc7ba39d657b6ecf1d7b6d0f137b50e5927b499dda7b2792b57af9f6c57aa097977a21e34479fc5ab079de13fd79d1be7a79950e52793a24287939d1f678a30e9d7898f87c78969d4f78665586)))) else (if page < 21 then (if page < 17 then (if page < 15 then 0x8a8c4a668a4857eb8a2a1d818a249abc8a1fe3dd8a1b9ead89eb68e78984366b89712764895657118942bc378939fcfe8920a7da890aaa84890a677a88da996e881c08d187dbbedf87d62cd487c6601287c47c0387adee878784a4568736c2fd870f392686ebeb4686e7070a86cd0eb786b94fda86b83d49869f5ac0868fdc6c86814b5e867e2f528668931786591b19864d66e38640a33c860e3eb785afba2c857a41dc8549f7c3851d4b13850a406e846cf29f84217cae8414060d8406b08283ca39a083bc7a14837441148372b1378371a17f8341f45e833572128334e83282f8da6782f310be82def3f182d8e61e82c465e582b92f1f826c6e3481f1d579 else (if page < 16 then 0x92a16bcd928a0f3b927f1c2b926042e6925a6be1922d6f2a92002fdf91eb584b91e713e591d69c7391a5a964919db4ef9197934f918e387d9138cdbf9100e0e790fcae6090e2acf090d40d7c90c7b0bc90bf5bb090967e1e90943aa9902aeab4902189648fe4e6818fcc52168fb74bd28f90dfa58f7f186a8f67d8cc8f60b77b8f2160ae8f01906d8ec933ed8eba2cd88e99f2a98e6554e68e2578078e1df40f8de67e0d8ddc526e8dc8a9db8d896a6f8d7cb10e8cff55038cff0daf8cf2eae28cf019218cdbd2118cb82cc38c7038e18c39e8818c39d6678c2c934e8c2646f58c14249e8bfc76878bfc4a1d8bb481fc8b51239a8af528a38af2420f8aa14992 else 0x9bf72a299b74d81f9b572a9a9b508a5a9b3eddb79b15a7069aebfada9ae987d69a671c3a9a6500d99a33ee619a28750799ba796199af4d2f99076ad598ef4e2f98dbce9798b9e76498b3f83498a887c99885eebe987531d49831377297f8a18197c2dc58976c4858975a9fa196eff8d096e0cfaa96c8273396baf78c96aeaa1396957b3f96634b98964da94d9639aaac961cc0b7961c265995fc5f2995f969af95eaecf495e9a1cd95c8fca095a55d7495a327bd95799d7395385b5795316ed294f869fa94ebc89794cb2f8094c33004949c167c9475134b941171d2940876f893ca471293bcb97593ae2fe6934c1022933780e09306c13f92cf56d092cbbb0f)) else (if page < 19 then (if page < 18 then 0xa4e3c23da47b3217a46afe71a439904aa40ce45ca3de8c54a35d9ac5a3066de0a305fc95a2f35961a2adc40fa29bcb9ca29a14f2a25a9ebfa2433d6ba212076ca20a8773a2075be0a1d79faea1b1fefca1a3cec6a143d1e4a140ad75a11419dba1091df0a108ffeca0e444d0a0816116a064dea0a05c49fba03b1c56a021e5e8a019f54ea00b29759ffdc1d09fbb63089faebe959f992a679f79f21f9f6771cf9f6520b19f6436ed9f4be4fa9f31f45d9ed4f4489e961f779e65bc4d9e60a5c69dff77ac9df397f79da828ac9da356e59d39a6a99ce9443d9ce866e49ccbefda9cc93fee9ca1114f9c7e24c59c6c2c689c5fcde09c523d429c18ebd79c019ef8 else 0xae236e9bae1ee623adc446f2adade623ad893d74ad7fc709ad74bd3dad71610ead0e7d28acb43ba8ac5bd025ac59170cac06f322ac024896abf74b7babc3b2f3ab74a8a5ab6a254aaaef9197aae0b27caab51bd7aa2ebe5caa1e9161aa0c2a75a9bb7753a9b32ec5a99e9752a9874c66a96b3889a950c82fa94b942da948c743a9194250a912545aa90b120ca907f4aea8da96fea8cbefbaa8cbc0f4a88c0192a84f2c24a82a63afa818828ca8030682a7eccd66a7cda3f0a7ac9aa1a79a51b7a786f531a7707e1aa6fc9c9ba6f581baa6f05b2ca6eebf7ca67aad71a671f849a645152aa5a6b7e5a579d207a57818b3a54137c5a50f40d3a4e5393ea4e46c66) else (if page < 20 then 0xb9453ff1b934e800b8b1eb24b86300e3b84e303bb83dff76b83afe7db822863cb81a6355b8118677b7e4d8ddb7d366a9b7b73a0eb790e077b762562cb7388349b6f25890b6ed5871b6e98f68b6a23305b68aef5ab60560bcb5c9f70eb5c76987b59a95e9b56f7e66b56048dfb535e2b4b4948d67b461445fb45377ebb401d50ab3fdf49cb3fc75e0b3a3f8acb33737b7b2e1fa36b2d6cca3b2c00ba6b29d1e72b24e4896b1eea898b1a2c6a6b18c2a08b1510957b14ae437b13d66f7b11ce193b1109099b0bc4e39b08b6c38b07655fcb049c3f3b01ceafaafed2cd6afc4dfa1afa7caadaf5e215daf3ef47aaef778a3aed9aeb3ae61e31aae5b90f7ae316c36 else 0xc2faa2e7c2f49530c2c057a5c29af308c27473cac2371d14c20988ebc1e0746bc1d877edc1cd230dc1af7845c1a253d0c173f99dc129b4eac0a9d03fc051abd7c04e3c5fc0487efec02f9676bfc22df6bfb05072bfaefa97bf85fe48bf392358bf30cbe0bf170e40bf13ee52bf11eaf3bf02182bbef63568beecca9fbe755806be3df95dbe394e85be2b9026be29d6c7bdf1c762bde7f189bdaa752cbd362d32bd1fc511bce93d01bcdfffb4bcdc01dbbccfc1a4bc09cdc1bb819b89bb7d5e8abb5d24f5bb2a7c64bb2657f1baf5baa9ba73b51eba49cbfeba36cdc6ba34b482ba230722ba04c944b9d86882b9b5bcadb9b3b960b9a076f1b984f61ab98201fd))) else (if page < 24 then (if page < 22 then 0xcc1b147ecc0792d6cbba455ccba3a548cb8a3aedcb3f3274cb2a7fa0cae7afe3cae4be90cad46595cab75328cab41327ca1fe98bc9f1d729c9aa0800c9a5cf13c8f7737dc8dae711c8c6a61ec8c1fc30c8b3721bc892804dc8778e6cc872e1d2c85fe559c856c75bc84bf8e5c8342db0c80236e5c7f00339c77fb63fc76bda91c74166dcc71ae0bec7112f17c6abfe92c6a85781c66b7afac66ac46cc5bc6831c5984ab4c5784267c5750f6dc555b2afc5516de5c5015d4ec4d7c9b4c4d4b363c4b9570dc4a930d4c444e243c432ee10c42f6b1cc4229045c41953dfc4027a41c3fa3cbdc3f43865c3e1e4c7c3c56951c392e9fac34a478fc34107bcc32fd8a5 else (if page < 23 then 0xd59388eed570c4d5d5536dccd55146bbd54d7ee7d53ea374d52a8f20d51d3ccfd4e741f8d4e24335d4a8053fd48ee4ddd470dd3cd467094dd45c51a3d430ad91d416c457d40fc549d3cf2751d3b2f948d37b4da9d367f3bdd34abc91d3068997d30422ebd2d97a1cd2c8b06ed2c4ffd1d2ba13ced2a80dd4d2a5c1a5d2826940d2499000d230f66bd1c95699d183fcead14d5e2cd1306854d10764a6d0f32d6ad0d7f735d09ddb50cff6ba8ccf5ecff4cf2e24f9cf0e0ea4cee34521cecf0fa9cebf73c0ce7b19e9ce764ab1ce54ab44ce4a88d1cdc18c1fcdb5281bcd954af6cd3b8749cce6f44bcca4d537cc772ba9cc5f73f4cc5ba52bcc55f182cc3ed23e else 0xdcde0853dcceb107dcbe95b2dc626c3bdc4db3fbdc47f43fdc3aa4cfdc37806cdc29c811dc011928dbfca0fedbf908d2dbe31fc4dbd75676dbce39fbdbca53e0dbc23edddba82962db93b0b5db5c986cdb55b06cdb1e8f72daeaad4adae7eee2da90d874da6f1f6eda562b82da176f4dd9e20f14d9d0e9c6d9adb47fd988030fd97a94bad91cc47ed8ee4406d8e8967bd8cb045bd8897894d8890e91d85c4958d85561a8d85526efd851713fd84474ddd82b5184d816e512d802d273d7ff5df7d791dbd5d784b168d7641dc9d7618b6ad70f09fad6dcb5bed6dab473d6920979d6798a60d666dfabd659e2a0d6392502d61e60f5d5e1f40ed5d0b348d5c4c1a2)) else (if page < 26 then (if page < 25 then 0xe70ae117e6e481d1e6da8d49e6bf5e51e6b67c9be6835b2fe5fea9f5e5f5df82e5f4bac9e5efcbdbe5d8f428e5a31cece58af94fe56a7d3ae548e5a8e4fd09d4e4ac5094e4a11cb3e455d69ee4023d0de3f9c212e3c25ce7e3732f3de359565fe300b314e2d2f02ae2d2847be2cbcd12e283f54fe26cb015e2561c22e246a690e208473fe1fe92e5e1ddda24e1dd6c5fe1c2cb79e1afd929e18c2511e150ec60e13b11f2e12784ade0ff5dc3e0e2fb59e0d3ed9be0c83aede07294dee063fedae063c831e05c275cdff7041edfbe6303df985640df32a3dedefadd30def9f0e4deb25dc2de2a5c9bde0a1339dd867aa5dd7452e8dd06b651dcf49a44dcf0a01d else 0xf07af259f07762e1f03f6790eff83871eff3b4afefd2c9c5efc02a77efb38080ef732dedef301e03ef2b9431ef11249feefca4a4eeeb7e41eed21a33eebaa013ee72fecbee719175ee58e203ee260e7aedfc33bdedf2e5dfedeb3ea5edeaf641ed9e7491ed4bf959ed2a4e84ed1d8603ed0f55afecbc8501ecab3341ec8fc239ec70a3abec5eddafec34efeaebf1992deb5c0ee6eae70b5beab6bde0eaa3dba6ea6b0ea6ea6833faea591356ea33dd83ea2d902de9bf6f6ce9a067c6e967adede95dde07e93dabdee937cd61e9341b25e91a9e76e900f5aae874e1dae82d156de81e88a4e7d658a5e7a19573e7862643e77d3a3ee77c2cafe76e0bd1e74b0a05) else (if page < 27 then 0xf87abff0f8570ec0f82a0362f8173a26f7f5e884f7d70639f76e13b8f762e05bf74155e4f72525a4f6e66793f6d76c9ff69b1a03f63f82e1f63d9727f6302bbcf5da13b3f580ee66f57ce270f56df9eef55fe276f5588debf534804af525613af5232232f4fadba7f4d14daaf4ce97e9f489835ff45da984f413b495f3fcbea3f3f30332f3d83681f3cfc322f3b7941df38cd588f373601df3712293f33938d0f3301b05f31f5a4df31a54b4f30e10dff2ee7d7af2d9b364f26a49d5f24fc8bdf23a3b18f213b31ef20b2259f1fe4787f1c70292f1bcef00f178c4e2f111c3c6f1025360f0ffd631f0fb74c3f0e72f33f0bf6013f0a8435ff0a78dd3f094ffca else 0xffcb9942ffc81ca8ff945971ff53e6d8ff2ce923ff22e6b3ff13b88bfefc31c8fe2baad9fde58dc6fd8970f2fd83a6cffd7f2ce8fd6276a8fd5e2bb5fd32d12dfd1e9025fcf5c5c2fcf4818cfcdc81effcd3fbedfcc972ecfcc020fcfcba86ebfcaba6befca93003fc8cd60bfc78dde8fc42147dfc1ce2e0fc147644fbf523c6fbdd9602fbdc3a76fbce75b4fbbdbabcfb942a62fb76a37bfb752c9cfb52755dfb454af0fb2f6a09faf1cbc5fae57d4efad78d5afac6f14efac69f05fa794264fa600e0efa5a4922fa4b5e61fa32a49afa258c23f9d8e281f9bb49b5f9920390f96d3a93f95b44dff91a774cf910b320f9060b6ef8e8d03a))))) else 0
  | 6 => if page < 39 then (if page < 19 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x55a9fa305550f400507352a04f4c4f604eb16e704e7906d04d746f804be05b604bc820104ba0f44049c6eec0493df4d0475718104611ceb04472148042e7a790428ae8304159092040e3e2403d0307803c6b15103b61bcf03a8bb3003a1d3c4039d27da039b08d303951522037a4cb00370718703529c2503439a79030e133603066b5602eeed0902b4d0c302abb83802aaf55402a539ce02917c0f02829d2a024f444002488a6f023dceff021818b401efb6b201b335b0018595930184d5c10177c61b01449689011acde10108d512010774b50104c79400fe956c00f8911300e4d8ff00d42be200d0ac7e00bdca65004c243f00459fb60010a60f000ad511 else 0xc2666de0c0452640befac440bd636350bd0c9750ba184230b70e3b90b5b989d0b5329c80b2e87a60b24a2940b1a3acc0b10b3ed0aeab49c0abe91c60ab3f30c0a9007840a547f880a5370100a4dd4620a4019b10a21843c0a01720109f715eb09a6915d09a56c9c097c974f092791710909a12809056c5b08dc6ae2085b38b20826914407e47ec00794046f0783d4940759aecf0757eb96074242cb07384a49073395d5072862f90717cc2907046beb06f32be806f30a9706dee8c406afb24906722c34066f9b8a0658e9da06566bf0062effb5062bbfa5061d505705f2a85505d51e1705cceb1c0596c8ee058f0af1058b2e0e05788e7d0570d53e056d4c29) else (if page < 3 then 0x12d3982c12c94ebc12c365ab12b3873c12a79e1f126edfb1125b350b122781401222702e121e847e121d172811d8274611d7d2e011ce18dc11ba335311ae59ad1138f9d7112992bb1122e1181108c11f11077a571104e47110776297104616c2103569ab101f81051017490c0febcd420fd3bd7f0fba82cd0fa911a70fa0be210f2b98e30f1c37b80f158f870f09d1ee0ee58bd40ee068b50ea8d0ee0ea6a5860e84909f0e7e994c0e67607e0e672f4d0e38bba00df91fa00d8ba2060d7dc7c10d7af6000d76ce2d0d5b75bb0d52ad160d37d8ff0d1562e60d09f4f00cfd646e0ce9ecb10cdb7ce70cb32e710ca500660ca296410c62ae810c5fc5db0c33951f else 0x19e8212819c2a39a19955b3c199247b419908ffa1967ab9a1965d021193e2fb71937b9a7192365da192164521917253418c7d6a818a215f41891dfb6188b49861852892b1810e04f17cc8d631792ac761786e07f17844f76176b2369175b65371744198a173e98b5171db26c1710d53716f9d25816ee533c16e43d1d16926c3316677e29163199121620baf015e7e5d715c559a515b8334e1599a5e3158e99901587a6ec153b288d153b1f041532ba9014f489f114e1fd2414c425f214bd580e14b022a814a581741495277c148f706c14799dba146083021425431b1410245513f1b22313da967313c6bfb013476cd5133192f6133055df1318962112d65afc)) else (if page < 6 then (if page < 5 then 0x20f19bf220d5fcc320cba27a20aec51220910a2520699b7c20263364200e8b78200514cb200105fd1fc867761fa548bb1f928c921f7010c21f61806e1f418ef81f3fb0151f3d802a1f31d19d1f1741f81efdfb101efc91611eeb09f11ea47ef61e8a3d7a1e7e74d61e702dd61e58bc481e4d05941e37ed671e2f87cd1e2ef80c1e2837c41de98d901db82ba61dae08161da0cff21d8883121d881c3d1d80e2ca1d7064cc1d4d96ca1d4805631d41fbb31cfa1f9a1cf418bb1ce076321c8483361c7e2f501c6db84f1c393b191bcb7d721bb1f30d1b616c301b4fb5971b1e4ea61b1afe241b0e660e1aef5e531ad5a6931aaa23461a972ea41a72a4e51a2f136e else 0x26cbb02a26ae66dc26954cfc2690f508267f5bad267f54792660a56a264da132263d47102614a06b2613f93f26082a5725fc976d25f5e3be25e7327d25c77ff325b48ce025a722e425a455262595eced2594012425808e1d2539119a252bf2502511536424fba08924bad1bf24aa608124591cfb245525352425e4662415909623df685d23dd692023d2b05a23d13f9723bade1a237d48b1237a53c1236b24892364a361234186da2333ce1922f6715522acacb622639e9f22627c8d225dbb5e225d8f8422533bda223798bf22337b4522239a42221d3b0222140823221176c621ccb1b321a5326d2193dccb215b0cd42147ca5221396ed9212f19b121063626) else (if page < 7 then 0x2db0e07b2d8157cc2d5435a22d5400312d51933d2d3b10632d1a08352d061cad2ce333f62ce323f32cdd5c252cdcd1b42c7516902c64811d2c3df4722c2a936b2c140f322c0f5fcb2c0366412bf0f39b2bdb9a502bb025d62b9af5122b7f9fef2b562fa62b512fb02b293ba42b1f9dc52adb5bda2a92ad792a86ffaf2a6111032a390c4b2a2add402a2032392a0358d729dde9df29c9cedc29c5a71e29b6261129b152c4299dc57f299d8ed6295f6e842950e76e2947eb16293b23002935ba32291bf18a28d7d05c289316202881240c2844855e28024cd327e2f03327c7dd7227b1f1762789ec9c277e1d60275dc16227465c5a271d8f86270fa10f26e29de3 else (if page < 8 then 0x34d0f72634708ea83462b52a341994c133e61e3d33d7af5d33a80164338b594c3372cdd533499451333895733335897e33209bae32d9c89732709562326c17253268e1f832522b39323c91103229dcbd31ef2e5231dca6b531d9a8d131ca9b9631c8771031c3f95131aa6ce031a7be7231a4ffd0319e67ca3163310e31607b723146ed22313b8f883139a5e8310cef95310bb48b30f32f5530e35eb230d2a4d830bab09730a7eefc3081f77c3073ddb23064c5bf30296f64302519e12ffa78232fe700662fb1eb7e2f722b742f61b7392f610f692f430f692eb971fb2e90734b2e8c658b2e64b5612e56fde32e527a792e2ec1b82e0f1e3b2dc291222dc07321 else 0x3c107f7e3be763653bdc0f523bbdef093b6212f93b5f87d63b3266323afa1a113aed820a3abf91613aae52f03aa5580b3a9a9a153a9a636c3a7488593a68371e3a67af103a55918b3a51c3453a4c58ab3a3d465a3a1984e83a0eef4c39bd8b5239b485fb39ac01f73984a1ae3946f61339411f0e393a892a391f1fb739035d9e38e6e30c389567b6386d78ac386aba76382818d537e522af37d7bbdc37c9601d37c0037537ab581a37a60edd37901b273787657137764ba1376f7cd13750c681371eb77b3704083c36ed26b536dbdb9236d0e2ad36af9c993685d13e36491c54360f799d35f7809835b7d32b3578470c356bdad8355b5a6435328f8f34f4ece9)))) else (if page < 14 then (if page < 11 then (if page < 10 then 0x4218016c41db79c141ad5f55419ef8c0419c89be4193244a417b6fc0415594114127f8684127eb18411b1d0c41121b3640fd197240ed9c1940e95cd440e8775040e52f7d40d903eb40d478c4409c1416408ed05a4083937d403997a44023902c40232e96401604293ffbfc253fea4e073fe271083fcc54623fa118753f04a19d3eeb35613ee6fa123ecfc3aa3e6f6a1c3e5b5bc43e3781793e2d87b53e1490563da7df953d62f4363d4b390a3d42b1ad3d2669a93d0e52483d0db11b3d0420013cf7c0c93ce1349a3cd054fa3ccf157c3cc4ab3e3cbbd2c63ca39ea73c8345803c801a5b3c72ff753c5f2dc03c5a2a8d3c4d9ba73c444c093c3093723c1322b3 else 0x482f57b3482a85114814fa964811699b480cb5594803f77b47aa582b479b2c5f479927854787c7184773863a4745f0ea473f92aa4723b8f3472023b946ce79c246c3379746b1340c466ff6de466a8c01465659d34653901346520d6a463babed46231615462086d3461a61d045f9e7a145efff7e45cba2ee45a17d914561a393455192a345220c7344f3befc44dfa94744d3326244d1c63444c86c7844bd176a44b1967244969a5a44809d4e4469845c4446396b441ede0443cb352643775cbc436513334357528d434d1f6e431a871f430000f842ff50a942fd888f42f3e18f42cdcf9942c426d542968fa4427447c4424ca0b6423ce218422e67f24226081c) else (if page < 12 then 0x4e5b5b384e054bc34dfd66094de34fc84dcc76e34dc3f25f4dc14a914d723e654d6fd40b4d6a4d4d4d5b67f44d5241034d49b2264d22c0c94d1aea3c4d17c1c14cfb7b814ccd2a354cca4bce4cb593254cad6d584c9b00c54c9869e44c8d69794c792db84bbe25ba4b9b51024b51b19e4b06c6d44b04c14d4afd3c734ad7ced54ac1166b4ab6740c4a9d04574a999a004a2ca17b4a166e2949eda60449e5b36049e0e2ff49bfe39e49b0e7b449b0270b49989c1949976e5b4990b084497936a24976ae7d494127a549260aa2490550bc48fdea3e48f9ab2248f5519b48f51af248e4463248dd3dbf48d0b24d48c5c26b48c003ef48b87fc2487551cd485f91c9 else (if page < 13 then 0x54eac6ef54d7c6dc54c46de754a95d335494995054486568543c3b21541eb5405414d5a753daba6653d4928153ce159353b7fdd253a0f87a537d1b905370d2875333115c5332eab3531db12753052b0752e8402c52d7b68d52d5753452d3313852a82be15267ce395236435c5224ba5951ec3e0251d326c151c9137b51b12deb51aeffe151a5db2751997b96519564b05192b567518453bb514e4ddf5110c40951029ea850d6feeb50abdcd950a4ee2b5062299e50415c8f5034b0c85017eba34ff907874fde683c4fcbd70b4f8d53644f787e284f70d5a04f62938a4f51ad844f2ef7a74f010b754efd6ba14ed3c6954ecde1d34ec1c6b04eab91d44e5f6f6d else 0x5bca8b915b89a2c95b862b655b72cbb85b63ce2b5b3e74ad5b315c385b1a1af05aecc6e25ad2d4675acaad475a9edca05a700b0e5a619b565a568b085a446ddb59f1900e59e3e0a559db5a7359bd7fd059a5e8e059a1f3fa59a11627595ad61e594652b7593c3d7c59322d94591a8f4558e59c3258d875db58be41f6589effbb587be3735872dd355850a8fe583e7d325829fe0358226aeb581fdcab5810954657f661af57e8bcc557d5b54b57c00c2d57aab90a5799e0475771efdf57715bce576af1e65727a7dd566fe18a561124f25602d84f55f69d8955eedec355e01835558d178e55755c3e55755a5c5552329a554f3c30551975ca5508b4c855015bfa))) else (if page < 16 then (if page < 15 then 0x633e22416336ab59632462e6631ddab6631357d062ff541c62c3378562b2688f6298819162841ee6627469d9624fd5a3624fd1fd624da858620d88eb61fbb9ba61f87f2a61aec6fd618c4fd061740a91616f5a926136993461339d86610786a060ba534e608ab9b5606007eb605eaaff6041cad15fbea8665fafe4955f8412c35f839ab75f70750d5f60ada95f4703e95edc88325ec2509f5eb9e4745eac9b305e9d27d65e8022a65e569bf35e52c72f5e17bd195e162b135e11fbb35ddaa33a5dbcc0675d9316205d8b70235ce55e565ccf577a5cc8a8955cbc840d5c966bc15c5824c05c35b0365c285fce5c23de515c1859515c10bece5bfd8aae5bf0dfd4 else 0x68a8d9d86886c501687ece9b686aece6685bb3fd68595427684ae7516819a69767f7247967c33f2e67b23c92678a3a746789b895677b1393671ead226704c14666ae7861668048a96656394a66413b736637c9bf6616b3e26614a166660653c665fdff5365fd7ba065f82ff865dd896f65bffe7a65b9e97465b910b565a80fcc65a305d8659afc7165927e086566f799656436d4654b0c3a6543dccf65407c7f652199c564fd491764e884a064c29e7164bad0f664b8fa2f64ab30f26493fd03648853d96458496d644d38e3642db12664257d236424e531641a2fc4640b789664000acb63d21ff963c4e34f639b672c63793cd8635a06206356a9f1633fba01) else (if page < 17 then 0x6ef7c25b6ef363bc6ed180216ec1c4696e6fa8626e65bc9a6e287e106e281a096e0193eb6df775036dcc9c3c6d6ebcec6d5ae5ef6d35dc4f6d30e3266d2106936d13f94f6ce2c5826ce282786cddf6b46cdb3c416cd9bc396c8d1fcf6c6abd2c6c63c6196c4b2ff06c3c2ef56c24a6306c23c6c06c0df05a6ba5193d6ba040466b9c13d96b8749ae6b51723d6b4941006b46b2126b2af1c76af014456aed35866ae884436adaeb926a9ceec26a6b856c6a6a1d276a5e12bf6a5bd4a76a59613f6a4f6fc06a4ab30a6a2f5af16a1edea86a18a8436a168bd269a70ad2699a8cec6965d2fa69621719695cf1cf6940c5dc692bada168e237f768dd40c168b5c903 else (if page < 18 then 0x751f735074ea0aae748f0009748cc25e748ac91b74823bc974709dea7444208f7404e6c373fbff7273d44eb573d38eba7384ced97380b76573509e00734caa39734064eb731d865673177315730c09ec72f7322972e5b65372cef19772c7279472ae766072a3402772892466725f6676724d23a5724904f9720c75907208e18371fc0d6f71eaf08d71ce3b8371b85d7a71b450fa7193de867181e419717e4c0371591e4e7146444b7123d6b0711ee375710a95f8710184f270d728ad70c3477470c1a22470b54ba7709bceb7709898db70900f027054c8f4701fd266701f14de700f08b26fbe2be16f9c017e6f90ecfa6f6971dc6f64d5f26f5fb2ee6f4dbfe4 else 0x7c58d36a7c327dc97bdfba1c7bb52fb87b9934c27b7f3ac57b722a1c7b32f9317ae6040f7ac6516a7ac3d0c97ab232d77aae7ca67a8f1af87a48c0307a21e3447a12b46879de13fd79b433d9797c99fe794c6a7479491c2a7932e68f792e2602792aefda792a19f579251b737865bf14786158fc7837beef782d3bcb7819739377e5b8e077e5167b77d1587377d0f52a77cf744177c8737b77c2d40077c2853b77be749077592406774ca51976c91c1576b8913a76b3365a76adf54476710d32766cd23b765f3f7a7654cef17653faef7640de3b763c9d85760c012d75f4c1d175e5d04f75cf8a8f75c37b34758bdfad7561cd1675356c7c75313bfe752a8645))))) else (if page < 29 then (if page < 24 then (if page < 21 then (if page < 20 then 0x8452658e840b85f88400ce8483d3b92d83d002fd83b590b8837edee0830192a882ffdb0f82e9a57482e3542b82e3528082a81077825dc15e8207604581f0063781d88d3881d4948781a761bf8153afa8813ff79b81146d0480f1988780e3dbec80b6505a809dda7980711a178018334080170bc68002356c7fe8f9567fcc88287fa133eb7f9d08ba7f9c841e7f88e3b97f7a6d1a7f21ed237f0b52387efc12107ef7fa437ef19a877ed7d3a47ed280aa7ea2f6627ea2d2607e889f027e7527457e6892ab7e57b0667e4892bd7e0e83ae7dd9a7d17dd2c7c87dbb047e7da7bdb27d3acf3e7d2b44777d095e8b7cecd7077ce9cb4a7cc307c07cba33127ca2fc95 else 0x8a696c998a52fd168a2a1d818a223df58a19a73b8a18a5208a1625a18a0a0eee8a01d4fb8a01982989dc136089dafefc899c0c08899b168e8924874488bbd54288b26e36889c473688790fcb8876c5ab886656a9883f9a31882f881f87ff0faf87fe47b687f6a2c387f3044987d8a6e987c9ae8687b7716b879b65838794a168877c145e874d2d07873bc6ca8719cf318702c22386fdf07886dd6da386bccf1c86b1b7b086ad502c8694d2a68685df0d861e206786106b8586103b6c8603526d85e4696285d9c86385c4bcdc85a572f98595c7318590683a857ecd6f855ee5808554dfe6854ce958852ff41a8523b59c84b626c5849aba70848ab49784677106) else (if page < 22 then 0x91e6bed791d5df319161bfb691503841914afcbc91342bd1912c259b9119714e90d50a1d90d40d7c90bf5bb090bc969390b6c55c908da1539070071f902b3d178feae1568fd1dcb38fa6e3798f97de4f8f7c3a218f2160ae8f1a25dc8f0fa2a08f0569938ecd037c8e97817a8e95f26e8e5a100c8e52f7688e5175938e3a2ed98e3798fc8e2c1ef48e28e6fe8dd901938dbc32748db02c978d8fda868d668a698d5b26748d52e1b38d1f34928d15bbf88d0cf31b8c90deeb8c8f5be08c6344e88c614eb68c39e8818c2c934e8c20e8f28c14249e8c08faca8be37a1b8be1081b8b9518ab8b45789d8aea77308ad27ea88aa149928a9e84cf8a8911918a77a8f2 else (if page < 23 then 0x97a5680d979abbe79799133b9787d201977d399497726d11975b532a974661e39730e2c79728bffd9722ea9696f920e896eff8d096c1898796be82db9688295d966b332e9649bdee961cc0b79600691895bd8ed895ac21c695ab8a15958a1c59955d56bc9554780e95384cb4952cdb5b9523b3499507eb2a94fde4a094ed310e94dd734594c8e646949c167c946ce95394625596945404639451ae389440f1e0941801c4940876f893fdbb9493e29d3293c35d1893a3382e937a5d439373da6a93566ec29328f14c9320f52092f1879292d84c5a92ad8754929f0bd99297f10792870748927d05d49269c8b49245ee629205eaaf91f1f40a91ee9f7991e713e5 else 0xa00b29759fee65829fe6deff9fdbcb639fc8a0419fbb417d9f775ff89f55d81c9f305c949f10b68f9ecd9c549eb341849eaa78069e80ae569e6f3dd19e54c6e59e4fb4809e2309df9e15b8139e0868229de89d109dcd68f79d8c19779d81cd309d78d2e19d6f24ee9d6107c19d546ebb9d3b11b69ceebf8a9c0cdeaf9bf803ed9bd5bf999b729f359b5b5d479b3eddb79b3ce19f9b38fef39a9fecd19a97eb249a244e9d9a18c9ba99ba370899996800996b43f89960cc7099595c5a9951df0598f1d58698eacf8e98d5e22d98ccdce298cc5d2d98a3a22d989eb61d985d9bec98547a87985267bf98313772980a296a980852029800487797dfa5ec97d9699b))) else (if page < 26 then (if page < 25 then 0xa75a36e7a72ce07ca6948606a685a5bba65ffc8ea610d5eea603db2ea5db7553a5d227bca59fbce3a5974fdba58ceebca5899dbea570bbafa545984ca4fe0869a4ed13f5a4afb8e1a4ac925da4a47574a477d37aa450cccfa3ffd73aa3f67ed9a3ce6978a3b84559a37864b9a367f09aa356c290a3464f95a3443dd6a328560ca2c7113ca2b436e9a28eab86a28e04eba270ab35a247d152a244fb65a22276ffa1f77592a1f0b116a1d1864ea1c5665ca1bd6a63a1bc3241a1a86e66a18ca5fba1770ffca15c13b0a14c03a9a1262a6aa11419dba10b966ba0c3a001a0be7374a084d7c5a06bf873a05c2d22a04b9209a0487563a037e2f3a0241827a00bc086 else 0xaea9b721ae883407ae81d9aeae8059faae2489b1ae16aa86adc8edfaadb8cc8dad9b9884ad76ac33ad74bd3dad3e398cad2a2c4dad0e51c8ad0344b7acf7b2e3acbacf79ac9a86f4ac54f3c9abedd6e0abd36215abcc0ad6ab866ac2ab3e29cdab3cade6aaf7f932aaf202f6aadac3ffaac70ba6aa740283aa5be376aa562370aa41da5faa3a7ec8aa15aa3ea9f67494a9dff9aaa9da8158a9c4805aa9a51a0ca99b8ab3a9617e00a9202f38a902a3d7a8f1cd31a8db792aa8cbc0f4a8913958a876afe4a85f09e6a8518ba6a84f2c24a825870fa817714aa7fe3170a7f45636a7eccd66a7cdb72ba7ba9b3fa7a729d6a7909bbfa76df0e6a763031da75fd6fa) else (if page < 27 then 0xb48eafb2b48cb00bb47dd37eb47c24bcb46ae163b44aa300b411e503b401d50ab3f2f908b3db44aab3c3a25ab3b08a90b3a99ff2b39fd07bb39ce03bb38b801cb315ec89b3074cddb2e1fa36b2e167f0b2cb9629b2bc440bb2a6f067b2a57bceb285187fb2794dd6b26613afb24fdc40b215fd9db1ef192db1c4d238b1ba3cecb19a479ab1999b1bb17146f7b16e2395b165b1d3b16068ebb1485c96b13d6d14b13d66f7b121d678b12067efb0ff4ca2b0dbdb2db0aaa168b0a5419bb08b6c38b08733d9b0517eccb047c02db040f06fb03ea22faffe8e3cafed2cd6afe56e34afb097a2af8d0c8baf5fb8c0af49a8f8aeef26d1aee4cdadaeda2cb3aebab92b else (if page < 28 then 0xbaf11f01baebfdbfbae8b608bada63cebacd7f86bac194b2baa1eea2ba8e9bbeba81bcd9ba799b26ba58cfdfba4a1344ba206f54ba1af8f8ba17090cb9f67bf3b9ca54b2b9577325b9502146b92067c5b90b681fb8f84f62b8cc4e29b8ca21aab8bd19a3b8bce077b8a975b9b88efaf0b88c9b73b86448d4b8517e8bb83dff76b8285df3b8097211b7d433f0b7b55cf1b7af4296b7aa12f5b730f5b7b7295deab710ae1db6fba1c0b6ecc1c9b6d0bd9bb6d08eb0b6ae435db69e9c71b63425e9b6320991b5f24438b5e4fdbeb5a9b417b5a966f3b5929998b56249b8b5597297b523621db517550db50b331ab4fec0b0b4eadb81b4dcac65b4d6dd04b4a5112f else 0xc0a9d03fc08b0830c074d295c0715be9c070e965bff165c7bfedd0a9bf754facbf5af9cfbf59e48abf5090febf39973cbf367f8dbf047141bf018482bef94840bef6e4cebef64247beecca9fbeea636abecf986bbeb1b190be665763be56e2bcbe39a25dbe32bc74be2564d5be019e07bdf48237bdf29d07bddc7e66bdb007e3bdaa648fbd9ef6efbd9cfc9abd852f4bbd5033f1bd3b6ab2bd362d32bd2bdd80bd1308d9bccf1cccbcb2c221bcae4089bc967bb5bc960d73bc83e3a7bc5f2e9cbc506c38bc4e6b96bbf0341cbbec56b6bbdcbd25bbc863b9bbc800f5bbc05dd4bbbc513dbb8ecda1bb5e026bbb4d0ee6bb379ffdbb27637dbb08d975baf277f8)))) else (if page < 34 then (if page < 31 then (if page < 30 then 0xc8ce5aa2c892804dc876fc6dc863971fc85865b1c821e515c81337eac810958cc80f857ac80b8398c7a4d35dc73b156dc7321201c71e9a44c7176859c7112f17c68420c3c6572d23c653d645c63f7ac5c61f7103c60594edc5dd2b90c5d3de70c587d593c555d68cc5543626c53c7192c5017cf0c4d883b0c4d4b363c4cc2ff3c4b945f6c4b2a911c4a57af8c4a0d094c4041e79c3f03864c3e0f784c3dd78e9c3741e68c34a478fc32fa5c2c2e8dc44c28e5a2dc25f5032c2112b25c2009970c1ece96cc1d80a5ec1d6519bc1cad45ac1c5dd19c19983c9c17bec28c164872fc14e8e03c129cfe3c1057cfec0fbab3ec0f865aac0ce49bbc0bad1fec0b1567c else 0xcfadaf48cf71d120cf434f89cf28587acf255616cf1fd726cf1ae28acf0b4474cef396eccebf73c0cea73925ce7ace1cce4a88d1ce0273e7cdb8b238cdb52689cda8a67dcd8d3514cd8af7c0cd7094a7cd69bcc7cd6268f2cce6f44bcce0038dccdd8253cc7746a7cc37e470cc1c7dbacbcb1e27cbbd594bcbb032f4cb851b1ecb7bf848cb610ac9cb596b7fcb413133cb3c08b6cb23a348cae5d10dcadee20fcad55bb1caad4727ca8c652aca7ae156ca719d60ca59519fca5622d2ca514ac9ca44b28eca106d59ca0c4065ca0982aac9d6d865c9b7e6bfc998cc3ec982b970c9826d74c94474e1c938c734c92fef53c9271cf2c91703b8c9135292c8fc689e) else (if page < 32 then 0xd5be91f6d5b6a81cd58a1effd5776997d575a3ced56eae62d5692bb4d56659f3d54c3ac1d5400bcfd5358461d5350120d53490bcd5013dafd4ec2ce2d4e8ecaad4da86ebd49e9264d480fd79d46c58fad467094dd4587e7fd437a5e4d42a790dd41e0316d4083c44d4066f14d3bd293fd3b2f948d398b289d363e426d34abc91d346cffdd331dcd6d30dd7ccd2ca72b2d2c329e7d26e5703d261a9b9d251b9f7d2500eced24a84b1d240ee2ad1e632cfd1d018e8d19fd0fcd1823698d1790c94d14f50bdd1471bc4d12042f0d10c96bbd1047433d0ebe83dd0c6691bd09ddb50d068c51ad05b95bdd0313584d0130d9ccfe1d687cfde58e4cfb3a069cfaf57f4 else (if page < 33 then 0xdb3b40f2db311140dafd801bdae0f437dad147a5da993b78da809046da7e69ceda66b3afda432d23da1b4596da1920ced9d9dd0dd9cd7cbad9b817cad9b03636d9a32ddcd97ceb06d9537342d9426ab6d8ee70fbd8eae013d8d25e98d8a88187d8a4a5c0d8a270c3d88ffbdad86b297bd85c4958d85b2753d855142dd847589ad81b99e8d817c425d80c4ec2d7e03d26d7c3541ed7c1e3a2d7b8759fd7b48c3ad7ad5abdd791dbd5d74f35e2d748c8efd74117d6d71bca30d71a19b6d6f809bfd6c56abfd6b69f80d69b6915d69434e1d68d7fe9d68217c9d678a975d659e2a0d6529340d6438838d63929a1d611f2a9d5f7fe55d5e9cd5ed5e73806d5e1f40e else 0xe208473fe1f355fce1dc0ef7e1acb2a1e17daba7e139a306e1011641e0ff5dc3e0f57387e0f2abbde0c9d6eae09b8c98e099156ee0629ac4e05b5443e0436e75e03501a0e02af3b7e01f7bafe01be010e0139b05dfcd3ec4df858975df80f75cdf56bafadf38974fdf2e8531df1a37b4df153ba7ded6ef0adebf4860deb621fbdeb1b889dea580d2de930189de8be156de85577bde84ae51de7ed653de5d1c72de2c0d5cde1dba2cde182566de136937de035289ddf29c28ddd7e723dd907111dd488c01dd1a14ecdd1012f6dd01f0abdce121dddc74e2a8dc4d34fbdbf624badbe94d53dbdf113bdbc15cd1dbb79df6dba898acdb95fd63db93a304db540d04))) else (if page < 36 then (if page < 35 then 0xe8f40a32e8e0c467e8a747a8e88f89d8e88c9cfee8803916e867c5dce85149dbe8330d1ae82a0ae4e7dc18bbe7b368fce7ade479e77ffc65e77ec70be743b322e6f2261ae6e481d1e68fb3dce669d8c9e6632e89e6591005e64abfd9e63f7ed2e62d230ce629154fe61fe9bae619a339e612264ce5fdd32fe5e22228e5b7e565e58b6de2e56aa4d3e56a7d3ae54856a8e53d00b6e5250c6de51c317fe4f0c8cae4cd73c5e4c61686e4a868d2e47caba7e46470ade4619ae4e44ba1b8e439b0f4e4356c1de3b7c1b4e3ae6a31e39ebc7fe37299f1e371a295e36c746fe35e7e4fe2f01999e2cbcd12e2985052e2267e6ae220dec4e219529ce21903dee20cf2f1 else 0xefe0ec46efcca16cef5ed06aef40735fef3cd579ef23da39ef02cc23eee52abdeed2b1b7eebd1f9eee7505deee737cfdee72fecbee719175ee62737aee320ee2ee260e7aee190cceedb97a5eeda77b68ed9e0e83ed7b1e5ced5dc7e8ed54fec4ed4a50a0ed46585ced1dd766ed1609aaed083025ecfd64b0ecd3ec1aec9d6fceec94f901ec85b8c1ec377803ec348298ec001381ebdca514ebdb37f6ebda1d87ebd3d172ebc63af3ebc221eeeba8878feb7ce669eb53b722eb2e7b50eb17b5c9eb0c5b00eb01398eea8a1b54ea4de080ea0c151bea00144de9f58f69e9c449d9e9a590c6e9955747e97f40bee95c2514e957fbe9e9189b54e90b4621e8f45707) else (if page < 37 then 0xf7b2b36ff797a1c9f76e6b26f762e05bf724277af6ff5be6f6f99dfef6f64244f6ce7154f6a186eef695ac6bf63d9727f6302bbcf62ef08bf61dff7df6151d6af5fd4426f5bf896ef561bac4f55fe276f542ede8f4fe22e1f4eb305df4da7f79f4c7c350f4bde60ff4a504fbf476dc28f463d7faf41c2f45f41a2b90f40a7cf1f3fe74eef3e938dbf3e26c3cf3e03d6df3a4a877f36d4466f33938d0f3329c53f31a54b4f30c1c9df2e8b091f2a4ff2ef294d233f247e8daf2434ba6f2296f97f1fe4787f1fd4ecaf1def0bff1d90c5bf184b9c8f17a1493f178c4e2f133d983f126940bf1214111f102e4bbf0cd9f9af06422d7f054f757effcfd85efed204f else (if page < 38 then 0xfd9e39fafd8970f2fd7da3fbfd6c87c7fd63c764fd568739fd521578fd374b99fd31026afcc020fcfcbf235afcb74ef1fc99485afc7704c7fc3ffff6fc2ab182fc29bf63fc04798efbd9c218fb981400fb942a62fb94106bfb832b77fb52755dfb4ab516fb3dc31efb19b847fab0f461fa6e4537fa498a3dfa41c4b0fa3c4748f9daf15ef9cad4c5f9c0e4cbf9b9bd31f9b00226f99a7f18f9932265f97f2b7ef96880c1f96585f9f965603df96233b5f9363d56f9321142f8fc0487f8f5a506f8eab2dff8e3930df8d6fcebf8ceadd5f8bc267bf88b6c2cf879b524f85fb0b2f85212d4f84aa7d3f8494f35f83ba4ccf8379e61f803afb4f7d6cde6f7b374af else 0xfffa4492fff3116fff7468ccff689962ff5ee50aff5e567aff383ee9ff366790ff2f8b9cff02188efee0a061fed30586fecefd6cfea1426cfe72e1bdfe71857ffe414e9bfe313cfafdfe4b06fdf99d44fdf2ccaefdf10079fdeb8a5bfddbdf1efdcfb364fdb1c84cfdafeeb8)))))) else 0
  | 7 => if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0x156b4e4615589be21501e30914799dba13ef60f0134a33fe1342b07912d65afc12c336ae127f629b124d1937114749581108c11f0fb986a20ef42f460ea8d0ee0e8fb3a40e79ba780e5372a90e0a462d0df91fa00ddc82f10dca76f80d7dc7c10d7af6000ce0cd010cdb7ce70ccb68110cb32e710c2666de0c216ebc0befac440ba184230b622e950b248f7e0b049aff09dac80109cb55a909c4ced509af101c0989ff2f0927974e08dfd14908b9fa1607e47ec0076c83190757eb96067b4dbb0679efd106566bf00570d53e05550f4004ff606504fa247904050e7303ca51b403c86263039d27da0370718702a0d2bb02917c0f01c66218016734ee004a74c2 else 0x291c5af1287f236a27fbca4727abbcbb2796e3172791e024274d2fdc272c62cd271dcd3826c40f3526ac5d042693fafe2661204725f2056525beccd325808e1d2539119a24aa60812451b095244729ca23ad443e23645616235c9a8f2349edcd234186da22f6d11822f6715522dcf48122627c8d22239a422193dccb216f6326211dee3420fc8a14205d094b1fa200de1ef8589b1ec74b8e1eaf6a731ea9872d1d7fb42f1d69bb031d5385681ccc837c1c016f951ba81da81b616c301b3843281b116f471ad79c971ac1a36b1a5703691a246be419bce61b199247b4189f10a7186957af17a9faa1170204da1601ea3215f6f90f15c559a515b8334e1587a6ec) else (if page < 3 then 0x424e5d34423ce2184234809d4127eb18408a1e744063be473fc7bea33f04a19d3ecfc3aa3e4fe4b73e06f68f3c8345803c5a2a8d3c1322b33be84c133ba0b6753affa9c43ad14efb3abf91613a7488593a55918b3a38e72c3984a1ae3963b90138f89edd3829376337e522af37a60edd3790cf943733607036bba16936b88fe0369bbd463681e0af356bdad834b5050933f3a5ae33d9c91733209bae329d44c9325456a131ca9b9631a7be7231a4a55330c518933087029a2ff52d312fcc682e2fac3f092f4d09d62e55f8242db0e07b2d2203142cb0b5ea2ca4f23e2c64811d2be14e702b9af5122b48e6a12b293ba42a73b8762a5c271b2a0358d72932541d else (if page < 4 then 0x624da8586233c21361740a915fe1643b5fd4f7325fbea8665cef58e25cd8f7655cbc840d5c7a8b9c5b72cbb85b69a8485b5194905b3e74ad5b315c385a47414a5a30dfcd5a2890e35a15192659f1900e5992abf45987b4c758a97cf85877e9d6577fabfd56df9d2f56cc2161568aec8c5573a54055602d83542409c952cac05a5142485350fcddd74e054bc34dff58574de8f6da4dc14a914c6194054c158bfa4b1fb4b24ad84c9e4a97b43c49f78d6449f563bf49b0270b494a6cb449340b37486952414830350647dc20d647aca8624787c718475356634683eee94644e33d45eb871a45e2c89945a17d91453ad187451658ef4327353342ff50a942c426d5 else 0x7ed280aa7be90ea77bca78067bb52fb879491c2a792e2602782d3bcb77f20b1f77c8737b7759240676606fb5759e47c27598076b758bdfad74cb315c74b7b99f748f000974709dea73fbff7273c8e2ef738650697327c3e273125ef272a40c7872224c767193de867182ba637158508d70de38d170512ed56f9c017e6f6971dc6f23cfc56ea5abdf6e72d83f6e5d734f6de427266dc1a3376ccb71036c2e7a9b6c24a6306c01c4486a1edea8699a8cec6918916e690519b168a1f8d0688b975367b462fc6704347e667079d6666fac88665d0219660653c6653a54b564964fde641f04d263ce00de63c794f0633fba0163351ec362c33785627ec14f62565fb0))) else (if page < 7 then (if page < 6 then 0x9d6107c19d3b11b69c54c4a49b409ac39b3ce19f9b38fef39a244e9d99acad0c997e2136996b43f89960cc70994203019938dd6098d34ec1985d9bec97d9699b9722ea96970c0f7496d6099e94f62c9c93902fd992ad8754925723d1902b94608fa276138f8dfad58f2160ae8f15ac4d8dca645b8db4ff6b8d69db4f8d64c4198ce5e33d8c2c934e8bde59ad8ab4ed038aa149928a8e20ab8a3af8248a01d4fb89dafefc88afd87688a067d5884443d387f30449877c145e86fdf0788694d2a6861e20678603526d85d935088523b59c82be68538217c46d82025f7d809dfa4a807d9d94800557537fd524287f6facd57f5a47e57f38f0577f024d157efc1210 else 0xba17090cba16126ab8d3c311b8517e8bb7c9b15bb7893f34b743d4b8b730f5b7b710ae1db6d0bd9bb5e4fdbeb5c115e0b5597297b411e503b318fe48b2d45391b2a6f067b28ee915b24179ccb1ba3cecb1aeafedb19a479ab0bb0df9b03e8445b01919d9af7b0218af401a6bae8059faadad5aaeac8bda1eac386bbaab90a36aab8998a2ab81c868aa740283aa41da5fa9728fc1a848bcc3a832c397a8076492a7d6ee7ba7958c10a76df0e6a6d11555a6ccdcc5a5fc0fffa5f64ab2a5da77dba58ceebca545984ca530c124a4783b52a368193ba353f867a2730335a21c29b2a1a86e66a11419dba084d7c5a03456da9eb869849e15b8139de89d109d78d2e1) else (if page < 8 then 0xd22bdfadd1e67531d16db2dcd0b5db03cf67d739cf53ae75cf3d1912ced28e34cec9a360ce4a88d1ce329aadccc3ece6cc7ab451cc218bc8cae124beca65fbb3ca1da291ca14f7bfca106d59c998cc3ec9826d74c89d5691c81337eac80c474fc73b156dc72e7a97c71cd84ac6793fbfc669bf09c63f7ac5c633d543c62468e1c5b11010c59a578fc5600c1cc501efc0c42cc195c3e86aeec3d12827c38bbdabc31fee46c25f5032c173b5cec164c5dac14ae943c1057cfec0fb2ea9c077d6aec074d295c01e6cd4bfd9a2d5bf5090febf2e84d0beecca9fbe6b02a3bd664d5dbd1d5f35bc866d38bbc2eb0bbb7bdaa9bb24b732baf11f01ba8e9bbeba71c8f3 else (if page < 9 then 0xeee75eb6eee52abdeeab3a91ee94a52eebcd0362eb976721ea327313e9be9e6ae8ef4f89e7b86176e759f640e6c49475e6b9b1cfe62d230ce61a9d24e51c317fe5089c2ce4b79838e45ac731e450bd5be4468279e4119a37e33ff70ae2f89aa3e2985052e2299f84e20fa8d2e1b2af99e19529f5e0cb6de1e050830be0332793de930189de5d1c72de1d326ede136937ddc28ebfdd1012f6dca76696db1a7727da7e69ceda7c434eda253147da1b4596d9d9dd0dd955fc3ed9537342d904f84ad8aaa022d7fac49dd7f27af3d7c9b144d791dbd5d78d571cd6ade4a6d65ce0b2d5a15532d56ac6a6d4e53f84d4089a18d364c13dd314c5a1d30dd7ccd26e5703 else 0xfff8bb23ff71ef90ff2f8b9cff1a45a2fe72e1bdfe4f58fdfe414e9bfdd75f41fd4baba8fd31026afcc9d7f8fb2f47a9fa6559fffa5785b4fa19c489f88b6c2cf803afb4f74a070ff6f99dfef5b49500f5737cdaf4019d69f3fe74eef3e938dbf3e19a02f3ce2245f3b0d230f33938d0f30c7d68f26c51bdf1def0bff1d90c5bf138b51cf102e4bbf081ef05f00d671fef02cc23eeffa6fdeefbe68d)))) else 0
  | 8 => if page < 1 then 0xfffa4492fe72e1bdfca901f4f9ed6e8eedf999cbdec203a2ddf29c28dd5a3459dc85062ed9bd0a73d9a32ddcd5be91f6d575a3ced26e5703c9135292c490b053c1cad45ac0a1015cc08b0830bfedd0a9be32bc74bbc05dd4bacb47ceb88c9b73b710ae1db12b935aa5c21fe8a2933cbda0f8ac6e98d5e22d8eb8b44e89dafefc877c145e8619e7d080e3dbec7c77496b7c2645777aaea44975313bfe7289246671eaf08d699a8cec6955227066413b73624fd1fd618c4fd05e9d27d65d93162058e2630d491d5d2c3f7611d13c9f6e6332af48022539119a2523acaa16a79d960c39de9b0c2666de0990f9b50010a60f else 0
  | 9 => if page < 1 then 0x1852892b else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0xde0000001020003008000600050001c2001200800050602020040000080202020601410040805240203 else 0
  | 4 => if page < 3 then (if page < 1 then 0xa81832982c000703068001a981e000482035202a002e240024044002460040603000a1205e08064e1825050900a000d4e01a7092100c982c060992089200a901e061224084902c00220211280154048a006240502044185a481048193d080900a0c330016a4058182e4815481aa5030086a08180011800700030301300090003c1006a02f060225 else (if page < 2 then 0x800220814000d36074104c080a0602820d5406a0008480fa400d301c08344e1181058101e001d0214920b8005c30034803a401430020024781c920d418180021000ca80dd2018100f06108c05d206e100e4810240a9203ea03004058008c105ea02d0000a80b4603290216c0da80800040302e6c1c2407400080003520b800c540461817180000 else 0x5e9403240028011203e000b0600a4078c00694120c0480001284a082b001b020d8281a00186c1c800400020103918130502418709c04041b800c0184a0c23301502019204cc00a000c1202c1058081e0418240d1404e000e000792088004494054a122509540660802480886)) else 0
  | 5 => if page < 28 then (if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0x5c0588a9e7249e808f93562000d183a821f5549ef1f400f2252fc0c08a8e900dc36524e0c83190000d1250002cc90c1049f026e940840e14008c000b4041400df004602ad002d69ea5486d8044401e401ff252fb65ac2206915c50fdbc18800029a29486c184140b8e9dc34a25801fc324401fc067a013692242010a004b802f01ccc9869092f00 else (if page < 2 then 0x41223a0901002f4210d305e097c001f8019401b001ac0153b01149271022f0c83aa23521f4f04a483a24a6d81f910054954397ade38a04f13018851a9219200f56d510122419f80ac200ca035693bca9e5d213193485257a0193610782a5e180c080e030a0187092210ac2480f8f99432b6026c8114126f5427a4aa0488a0050142faa07704a53c else 0x412938905301040179c2166d96d008400a00a3fade430064a5389254aa96b4d412403a1170a116492aa57c4017a091530dd007241c00000212f28018d445a021632330404520f6a85b853c807d00864013b5415801fc1048308800f6020f004221a43540182a41510a9cc9190900a7c00aa02550cb08555a198ea04806479241c04c405f6015c84)) else (if page < 5 then (if page < 4 then 0x2146034302a0750800741226d974553ea90253ad8080d24e700091ea7af2400ac2383b003b490094a0da47852528ce054d3c029a0047a92ab7258804780352aa794edac234d201e908551478006410a50a89648fb60cdb024fdfc00932498c301805e34ce527154344b0402195301a9d09580089034e806b4152118bc00282a80cf200a8024e2c40 else 0x601419ea1044918b02d8614e004e754ab70c81018f1e548d12879c0908062900a48a53a33f00253720d8263813f404a6751c46a28657705b34ca21e23c30da99f5185f068d1914608ef00d2a47f5d23e11ef00918516c0a6ef53c8a1423af00262021c4f37a41b1b4b4912360413c86400d4a02613448006db45c30bb0761066514004018a501f98) else (if page < 6 then 0x94c0cea02a442a843aad2330ba916757a909c2430014d36c68010002aa10670887b6aadd9c04888602f8c41800ee069100c1259216d22044006263c2d922c91979487c262dc6006e5dd0477a4a5461e60e5e0ca38b4fde85aa51e10b7c6294752c1df000001b4d23386a13e60918e769501801c64882002441274963403508199400149e21002e00 else 0x5a03114d8bb4848245ed4ac6004402770078879d691ce06590c3f53cc4002f540b0c25925347a8558df001b8019ca02a00570062d543091910a98120ec0526004f032abc88812c318c46d60010152caa5692300ea5b0402bf161b00a3090941038925000a0852ed4000c0ba6c19a4a7198080889010a0436c3378a1ce051a004c80042f1d80604a9))) else (if page < 10 then (if page < 8 then 0x3d92ca8365518f83059804fa01510c13007195120083600954211c0404003048b4b242c2878f086002db6664c0f804e50016a4315216a911501113c2ec0266325400b88419094b8057154103c87523e8117d4e2b24ab0a8be006b0903006806ac070270497808580457159a7a9a1d1ac053e787c0108809615082f27e0c72046c020cad90b067d01 else (if page < 9 then 0x3ed30e0018f01260107401c201b400c88008c049c19e719150c040636ea19b4aa3b35144b5402ac02f382a7462eada1a00062a021494400c62ee0428c0311004fc00ff801249554a8f9021828780900095b0045a0008803fe313e184e0a578c17a0c660054807fc0aec0489607982980003a0c0518cb828b4b9ced85748fb277000c3c9d6b020386 else 0x28c38a30170c960272c297890060319005c408a4058306d2937b40ae4481748a888374013801b80861000bd6d2e791018b33c460318410ad480500a3d22d4ce79241d3c4653b14e9e70ac23641c196c00606c812a7cd28860174485e2893c022400345247009fc099412a004adc50b81d5c9c0004fb9c0b1204ef01750c1a676c21b401e7016424)) else (if page < 12 then (if page < 11 then 0xb5440e9843040d271452b72a1144a34264380accaa4b01370c9ec011a0a010423b087400d84a0f54a40c219b2e005985e5b1263003480d1c48b8bc28c186c4973488b004302a7001548491b12c89188001100f7284700084015b0a8fc5ad801a40031092c800441bea00d60036001640d0c0111187b29a0d3842002e047b021d42a7a31a7020e01 else 0x8812d3cf02260a91c83c01189c914cf500250c8e090cb80840c1d1ea98a81279602a2355424aa986f00a43dd3ca6c21300148087c002400587a5f01350049ca9ca483e2a3a9439e3cd5093ba91b13806027c700a820f803da02bf3b1abf8946298cdc250a0c5515330809940164066c4010ed9b24e45ac46db0f20e840004a63c400aa924e213580) else (if page < 13 then 0x1d283201e602030518540be49d05acca8568a84606015531927a4083a90463030007b00050012b50c6a41e4027401a351130cb1c34a8242a49428055e1cb69c32021ba72cd827211140406a9330c30400856e1446271353a1a03312c00254654834f5087e458cc017a952e00dc02a52184a024e04c6841d0651ea8220a431226402d4a287096301 else 0x440010ae9785157a771009b801ca541c010d8197e11241860838d9f8ae0031063ab02bd2544306f48170f0bc02ec01a1532480380045471466e7f00b1802020a64521f8635cdca4984f095f105dd2c2accd748a3891a123ea4a678cfca64282938300818c2a81502a0c907904e9a84b401389d84721924b10018c5aa98e8ba54240510014e86d928)))) else (if page < 21 then (if page < 17 then (if page < 15 then 0x45c00029c5048718053cda5401a404b0283780524657b51461d25001f401090a6a8093404e0ec50004f000153bf8082649328e93c32c30e7328dc80b0c686c9cbf007380060007c49d60161861b061780935028801475248e042508be031fc0146028e00e5814ac642090a5054a92390056e084454000f371b19401a450552848c142236bc7c8600 else (if page < 16 then 0x7413b8e982676df286814882f97f503c8623004766d304e63806240500189f00cf82a19337608275412000b9410e02496059005752b7c048b04738256235100ab30c65050a808f0e9481207800d409bea16032cc8079c1b8402930c132167d416a011024db826ed5456e5370144810841d64002a552da600dc412f14208ec9270429b20117480380 else 0x118f0d0a62d2a141d88cc422418700ff840592306000e0012aa5d1e310a1b873534518d2530999908828c57942c6965600f102ab53ab20de34e0c361cc01e0092104f000365e186023f029b3d0b802e8007008e48c2fd3b38a07e38a52a2f8c4e4b07a195d243cd20fa0ac500f00c7953426d9fe020e006806288263048f115100105432b04e7680)) else (if page < 19 then (if page < 18 then 0x20428b615ae080686034002c958e0623122453a66010e01242c6cd3c24f1da78ae89ae003d40d8a0080a42cd4326142618000c5205b029043483f1d6fd31a262378aa1c05f80006d876754500588cca202480004247e0158e00530460804546550366965221286982f4c0b051060c75008109c26748b258edd040027b292c2753ceb38969a010700 else 0x10815160ce20ad48244412d04415024c303d93176093b0a8083999641aaaa20007029f8b460aa10009aaa58d434601a8009580250c2d690c800af91000c05a995c3620804b152eea108245cb6785e9344a5402139a02000dc0404845fa4065b4b24a2f022e3641401eca169512e8008954a6f09366e6036b40810960b013d462800560a65a011b45) else (if page < 20 then 0x658005a943d00878087930e89864015fc6290083009cf2a968c7dc038c947c783a00650140a9cc5014d80679816691a236153065c0459004e6e7736001bd1a4997540d809a4040409d352520095c030210960049815cd52c470a5002d2858942fe9c3100db8366a1ad29a5200230604c046c02560d23264543250003978e8a52fd31e8006900e292 else 0x694918661ab5041c0620185449924d520c8bd8070018400b527861507690250317802ed284e60de6c81046f4186a028e187c249c40528c9c80646043c1e0e404004e102a5c5249800cb480882a7a30de0172181443049f1a0d8cd00fe2711d224a08134b178c8cd33540df94ef78382002f294304edb802c4c180d91a6d03a70a8235e14094844a7))) else (if page < 24 then (if page < 22 then 0x5dd244000861870131f4039b01b684b62a6013c2c605d02198019c03820c9218860493c1516a1126d1d009a9f85eb0766cf1ad34921cc00546d1100a6630eac404000d2460941faa0173092003d924e8988b0120bd02c293a9c1a4c0a42aa6284e00cc512a807c80d50ede448a5b061008bad88a609603825fb50a21500eaa88540854f13b081628 else (if page < 23 then 0x8b1230c9dd901461ba7190640d0e85282a34401cc91af00ad035ac002b08f5045b92b1c6049042e52131b7482bb2300600b7374741942003451000637c18a8c1990ac805a48023c11f4041381a85949a404c0218bc0c12862a8ab48211249c034c1129490b860a40b3c14f74a1b0c01541ca047c48ef02350080000bd00aea6778209b090b0062a5 else 0x8112228a217181527414940c04264cb4b83e423b615b8011700ad4321092a38a45aa29942b10d0278b7036a9b27e942a040ba58283052604406140ba28680ea2248d33000a4d28c0cb70044a4259502808be0000096f4150a188006488023c0586323c24641600130000d580a048c2f8205c9aaa8a7b0324c003e94248147061340018128124fc2a)) else (if page < 26 then (if page < 25 then 0x979e3cc028d3679242280a3290fd0014bc5981a1a00685076a432523cc121003071c8d62d46c028184da43d93cbe00d90c698203c1a24065108160064c018291fe094730019559000ee034c81618e12a1a45487e423f921c8902908cb2826000e2e8325403a4019e25c316502ca807cc04509dc1604a800a23c62001d512100980218c0242045e25 else 0x191b4a424fb00e082aa461fea98f02cec2ae8006e991308b3856d00890d8bd495f0007810e89cfa8404267ec24b6005078afc75a00062928c64b53900032daa1eb013e0034c1a280e961ebf035e8010a48e80029a48286184051e8c894259d44dc49508c05aa0b9225e3224385ea8aaa3b5c0943303e81724914a04854808a71fc08589c5406f33c) else (if page < 27 then 0x47a38440c51502f36034f04890554cb8800a4129716220962b06fd4046da551b119c299a0a218920030a40b12cda94b24820bf9d8233e0c0b787b000092bae012804de0069d40bc05321894808b131e601b870001232e310a0006082c843c0054a56218105a7b11226291750018008ac0330088c54f43a90602dcea9c029e82989a920025c00ef81 else 0x4024c18244490fcaa618cd0903b8108a0046001930079b30a006d4f25001dc027216120d1d4554d505c95d209270006802b800220518001780144917a034386974321a14434e9e04225c8e69805526f8280404a602870054282219334a2136113aa8e40a4108920281a6509fbf40181009f1287c09eea217011500a34e816013e00ee00))))) else 0
  | 6 => if page < 39 then (if page < 19 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x5f4002e5f57195bc67412e240a3460e6030b120ca4a51003c805ede5a090f2041994b6c1bb0b10d019080108166ec364054f985a522dcf18c013c831b835b2086d00fb01d38b128aa570133a633c0068a824096a863519602fb54006682d6c64aa18332b5bc32a8101a02e00017a72f534a092c518b640104608a1b7b00e300880047214040c0625 else 0x225e69c000c18510133830440124250a80600617200c003423c0bd31003f05190a009a8035c0e3d009886a9de032165c2459805dc7638003c188da11f40b9ab66218140244c184c007f51313cb21827a30d318253c881206248f700c2865b5314401074a73298f004cc934a000b2a169e42c937146872992402c9057418d3003e9e0b89eaa01b680) else (if page < 3 then 0x241cc96f35701773f4d491d891580196be53861a208a04f75234f81e280a2360b881cd5e118001c48472c93022c8925e082300216011af8818123857882828a9a28b0e331a002c8aab84916807022ae648241932a7bc5e1fa01fa029e807fc211c08ba0501266255474d8eb31a08107c12e4fe6318d702721e62c9c2885a147730101a496a4c73a9 else 0xcc796c91d604b439c4c04929325192e8c0f414a89c356c8781ba031c2021154ec3e008017c09c70c8b122e0125411a900ac800fc0494021702ca80d5832141a268512803f0012490a70019800592024028500f025158f5024ac104ba001b4318012fb00a40005c002c61c6513da406c00660f820046369d923a0dac1065f00b741356087d04128c)) else (if page < 6 then (if page < 5 then 0xdf0027e451305b7a4dbc76ea183924de8068c03400f5a4eef850a539ec329c08e0800794ad40ef4002612d40056516c703b81c3ee0836c20501950005d23c200345a89a5418067006320112833a61284017f7927bc494008091d084e5305d8294c323a00958010d254849b1510800334040600f14e1ab05fc05220159819a000ad22bea14401ae30 else 0x68a23e6989a25029888811ec00906c50261280608303118e044724180a91af2d73061000074a9f57c5a825d5a62c988b067f8001d3a5ef13e000d240d803b60a8578098446d251492df4a8a06b3400e000bd49810296c0032a95e480a92d1e36909896184a3cb192108905201688005405240034782a000cc70da15f74839ad3b8c3aa0042016ea4) else (if page < 7 then 0x4f493a202470730a4b78353018c1094d18995239c08a507388c465207e4ab6093c1240002069d3246dc80ca0048c147f482aa48c2108e001d0036023280a0a014518e7421bce68b1b100c0b41da0319c4a0c015d00395217e00e41805bcb546aee52f9010d8f13c96e2771a04d9a814db1a6098f05a8b0d29e04c0f200185000f0949c02ad7a3d92 else (if page < 8 then 0xb39241c02363063249c1fa60010d1199804a925b49d4130049e09c0196fddc5a07b012494ce9ccc04a83f9b01e6e926200143695130c200b8730127bd840d2053101990217c06ee190a4a3e86c70685a0c21522012ca4921002796d1700a1c932e004c017006c65e27c55de00390cc99fe569d3b4ca02ac300c38049924fb3cc440182035b00dc84 else 0xb8c21a0e1f50154802fd46ea04d0092e92d657404925201ac0630523c8f00c016a800712b1492e98caea4854258ca8dc023d861380160906e0911808e00002cf410076807c005341b5a4dbaaad4182061951051380dbd91540c240163804a0896201d71b73807f0009ed9700ad6020e8218e019a78908092c206a023f09938080c08600a3724fc24)))) else (if page < 14 then (if page < 11 then (if page < 10 then 0x9300b7002de203b0368c13ac0f52015080c00162c4a6e00e898bede5c61850185080c603382086c4b043c9bc05ff0daf268600c7815c602587e0c3fb6c10760e6e080aa4be013a0181900adaa244023878001847816ad505262587c6300d98659405ce06ed0f988930c9a3300aba695c089e347e0c1205b7402220071060f2838c05c8009000c380 else 0x5a94400030c013a243789610a8e349ab0c45c82a04b63014f8690c65f80b3304318a30db096ea5e00783f16435bcf918255d24d7403646174241c00730014204964cc182e04067c031900aa4374156a6022224608117824f4dc6a769c403e8158870510b913f21891e00b2b4ce90122860e6fef6625d989cd38484ac902e9840052b1290ea859c33) else (if page < 12 then 0x84de0ac025f1eb9806a836c506ac083bb79489418041509a48ca00e1e49d8b74e128930016e10de00a9824b5b2501b68019c81545dd2e721f852080520c1b0017106820c500c492a97404ea0679414eafec7619b1e6b1616a0dd84cb400cd5503832e705280258956a20216815f244bc066a00bd00fa00cccb1feb29e48a88096414a231762e6718 else (if page < 13 then 0x6a01c88904548393d82403fc10436c1704d48911e00dd481001479254c0d0b30c5b4585e058c1df006d24680016a02440157009f80576f2f508b50078d535e01e819010096814d20696001700400705a0a09045d80654081ed8a5012dbe0dc0190009d4906127c401a0da9d7efa047edb230021f611f80164958a016b0260057140bce024b017488 else 0xc7034fc4aa84e0f8124980f4082648198ca3c0cb200804abcc20613cd80b440007c2239fa40d929192280075b30c0ad0800aa7980909a01ab5b852458923d8032503aa812c9b38a0168074800b5c61b2016b8ba3c72712302aab97e62366284b2804f10777001c4046e11120144a41d803d23364006d30cd806c11adf0ca780521d0600c9118a59b))) else (if page < 16 then (if page < 15 then 0x51c56584d04006f0271612000422552303a18961e0026022a8000e10c670f53935801401108580400113cdc035080410070b19764a130492401a600590f312015978b98c15940c601c605888636c60b8993c549f8059c166831c87c9e0021636fa02f14975924542112f9df0876016a0165a006e028c9b14099b29b70010d01b3520f098b30cea92 else 0x55d207aaa40001e0098403b20c777592003480034a9bb0b3c807fc0444309718e48057d2c3091f94c4580d500a8c4a060433b801d36ee027c001fa7c7920000c4f038000bdc1490005e7f38924a404360d4601813f15935ee9b570c2c0069941e49869045180ca4358007581a5a0072013fc059d008c0c12da1d600621567001b9ee0ea821180d00) else (if page < 17 then 0x2f81db601a40b6bbdcc4043066664cfe80354069a02ff8cd2300e464fe01648f93819a8206a04570b952c228059004d44ca68068a156c04c00755bc75120d69e1078e042ad4e4ba01b7255900d6066889c3e4978aa3f1241001dd2551004bd5254974f611c06c54150232f00156006b41b9c022800022591156b8016b0585a693405d6326d4e5c00 else (if page < 18 then 0xcb5f87490151923000cc1692018748dd8086862d0e2cd541fa475c0868f99300e2004a02b12f08d7e3100c4c10ec1979498d2a6c810689c230062861d49192018200e83c804200609f754cfa89ed32d00b15082c361ec220031e502a946a31329e184f26e2283241ac601057f5d022bc04a800394825246dc026a301722808605833ee02a3001c0c else 0xce13c6060bb060a8274c809e01b04e0d3c76413d00021483380b54664a4ada194627925e1c291b0003480a993d54fd7e00c5007515314a33800e6ac0292ac0953d4f34011e425a891db1d8a801b0004e11b25126023b860ac30f2036681781222e12708b2b2762d444890b548142a7b8030c9f190cd90072541c891f200453d8e40630400301afb9))))) else (if page < 29 then (if page < 24 then (if page < 21 then (if page < 20 then 0x3bc19cea1dc4f0e45d25301c01dd197098aadfaf80e1a011d80a6c05a600747204008040ab69dc70198be73416360af74e4480c5de3e805f05484828c1e4ac0f67005b0264d22ee013104ec8e6d1432ef055500cbc038965e00d16c3f82ab455ac08bb0465bc1f06698789f4c190cb2ce4d69d350091a86a86ab89dbf4acb2a6bc93a090960111b6 else 0x1562c009b485580d11ac2a3258796a0fc5c02b305f14801aa4b832450a7a756600d0c0beafd5a00191869d438e109612fb3e9d0182a15686d77828b004ac0ae2013e9c2242692c2b33736a495008c689a7014c183880068998a0626812395471085d0837007a091de02fa00c896a9c26601ac8002b270f4022803670c31c1771fd709b25012192) else (if page < 22 then 0xad415d2925f074dbd31403fc4873011b85a480a98a9a8502104754668c4ad725ac809ad22eaa231019c8d6c1330e0677731f032ac08200964538d8012004169f325b2185c7066d8013e05100236c916e003458f2004400332903e01ba803ec0090901b4824023400b340d875479b62e1c3fb080f005cb980de19c32b610a8ba028031eaafc00b028 else (if page < 23 then 0xad81daf05900660378c2978586f00c7800c0057830182423a42b1b4d6984918f20412954aa01a8008602ab4040ea62704ac3c8ac16d40965832f2481804c803384d032a338f028f2654d159e3c548be09480cfca7218616003031a58a487822f203700f6d26b489268b4094e4b807ac020691bf00b782a7c034a17037c96003c1e1f702d41d8900 else 0x2e1b49aff2e25089803d5568334424bd8034010b4031400300060524ae13284e6d00d98906a92a8488e185a5351c9c2d00fd8006065a6c1031e9606059e6f2000c4e808484cc23a186803611862812a0304a2d504209211085dd224d901059120600501a2f3e63803a2180302a980079245601226c9ea60b80bac3b76009992351c0f81b0e008183))) else (if page < 26 then (if page < 25 then 0x370000a02cc4ad88264006ba35f2782904a0d2592033a54473c37864b20d031c5fa4055e5b2012b031780bda1a000b7f485b038acc67618014e20926c821cc982c015780d24134201242707301f201901b744ca8881a4330a01c3006a287cc1362008e5bb04318521ba331355628625466e44a51087c0c19dcd4e015e787280bc8965836e9362b06 else 0x5851bac222064700d6412500062387130835511ed8e802b4a9ba5516c02b500991d0a92eeaf8555322852082036084c18ac86c6c262042d179300c5dc10ac490f6cab00ab1e65801820ce78056c054800a8009183a81b3aa0434494cbf74187020753030a424bc10f8f6b1026b801040544da4a7bba902b5b20430b703764087460fe9706194e3c) else (if page < 27 then 0x3d004ce9088484fa76a544c600676c298051c0146047d553e04d5c68fa025b7f5213d84adba0f7a01aab25c002ec44738b21057940654998d00ee803b4136090bc2609051fc36d60950002d423e4f28601ef01a20178803d401fd6c4601c05e0b2333625a580df8927a269448c2c0a9401e203760ccd8379014c6497978a50058de628a96e843601 else (if page < 28 then 0x5a057e9deb097f123d401000ea3723d0387999c0101a03700e19803420425001580338030a05c70326ad569f42a4b32000bc5d001b0806d7042f922240a4c0020004f2664486bc6d9b78a42451864344aab00ed1500de0641a8b481282035e088913e1e7706211535ca0266069927440e3401cb001292a580dd31df1057ec515c032c90d3009086 else 0x4e40912fc180174009a404e4fc8b04288461920ba02ab0966241f8040412f349c0269a42358a8954f65981182432a8000505181440112aadf2b584017121faa8d6002e8144922c40014012b92c04daee055287b222aec05264b16130d8083c0aac09b300c90c1ec02c2a87e055e00ddd2520073c4811a4d110366111a30baba16c0386a12b0ce900)))) else (if page < 34 then (if page < 31 then (if page < 30 then 0x6dc6356b29e00b50276001ce498a0dc0271e123e69204004540758a3a8f0f91859987cd38be0e3b0954001f006dc00930870004cc66c25dad0521831b122c2035601b486ce4326a904360db0c75c061a0a76005e00a20930ef015858180355262e901e4a9306979e0f632c60001a4099536a019d18d510721fa7e149625b2bc3709dbe532078e482 else 0xfc63280102017a8143413b652dc384101005caaa0653492b000714622f2f70105858b5b14a09fd48ff00bdc644c009500d1830a1e6aacc7d08e0835e002c291ba0a85a5125b074f07a514aa6b306128001e18c884b3df8720032249d0066001ba002f481f3c3c000fe0e61555c824a9427a91034bb7860853436096b843630680120a1804514881) else (if page < 32 then 0x22c64240aaf7a6e9259c78a004cf04882adf5201600fe0342041d81620031d48f1807e8018f09300b3a803a2152a9df5794022d213b2c016f08d280524deeea8a9480f80a700b66041638e5a8920604695230525819b8094892b68d46a6814f3a432d8197032834021200f302808092031920aad80f12a9b006e43192257d8132df2d29e118cfbbc else (if page < 33 then 0xbc0635aa28d4f66068e1e5e809ac5b01846a863184b1755708605c2e9207302d730822461feb41502872451493fc32350119a4054189c04cc0069a42544a28049070068c51400a8d9a108778620c014c000f496b80150092a98157ec284d0a3468006b4da180340006648830c808cdf00b5a00347e9b403e002d0c1a90777802c80202143200ef04 else 0x7d563aaa6f07b9c0341cd80016e52aa84ce4619601fd78e982630656d1d627882c51bc526e00db00e9968dc60a415ae01298004400e401548d47261a9d33c033d8ccf80d8e02621d0319500022a0dec105b4e3d00ce19352080502220089000461ac33942006c829fc0317038e80728281c331f02cb812fd2da8947f12b30c98001d8011f002480))) else (if page < 36 then (if page < 35 then 0xa996a3af0454c323a15c26b000564bb78099938a00282783684aa0198003011089a420db4d001947802b093d537cf0b970c01206db4d4077801ad0097952366c5e0025a8835211a1a6808a8860913c46187f012e003e806ba1b0954778233d3666432f7e600262000faf3370169063c1f442a4502551b89141b3800964e5225569e10849fd542182 else 0x7681ca00201009f82d680a3e1b1618123c9b5334ac0bc240aad308113c9c5e79248235d367e10db6015246d8039aa8247e1d007d9f9fe1a2a057b46a15517a9d2200a8b600091f60ad97b0d9583c01060e0885181ede4363000000027362e8047e0d3c7897000ec7cc80c8100538c8d8e594003b2b3c823f9257a48cd488e129540b78020d0d3e80) else (if page < 37 then 0xc7c0256635d1947800adb10ef08e7c10a7d90e46a924009ab0db08e49e01658f24123c8048e03037ece25b0476169dfa08f685018063a1b5501a002bb536d202064994930a0002c022e7e191e7b401be009524650007c24b4022906908c4b8602002b50e792470802dc79f800c5259681dec07125488982b9b0e2081554ca838a8059e337902f300 else (if page < 38 then 0xba8e984db285ad883cb865c2f14378f4806240862001300200ca6e043206bf4c30b002d56c401f94997000714868000f79a780938611c0d1500d90375c9b7c0cb96c278c16c619412c960feb010c041508cf079c80985e6040ee50cb5c4b7800ccdb595f3fb94fcb9740d170195826d890c701e924949220804be557a48c90090c020609260a9a00 else 0x2ce004d6c49803c412cc4b23032dbc7181858d89320f20116d2398a22c54b38315948b648af3067a43706c18314f30f901de0324e033258b906)))))) else 0
  | 7 => if page < 10 then (if page < 5 then (if page < 2 then (if page < 1 then 0x11c08f41871081980100c0180c7548260c16c09520026081fbc07d608a90a224250c274813afc9b10222407c113c90211c32a6295510094a14e3f9615e10e6f096540a0c0f400de9047040c2407880ec00207e2ea426c304208a380382805c0040a879184b012401056a89700169713de0500028084500048191e900d0c2492128203c044700013c else 0x260012c0822004dad04801363004000d8020899341876480e8e0f0003200270a50a6248180a906f00111827801063c5c0414280015040b429240f0c2806052006048248c2500146705d4a270008460ba381d1e200010c809cfc3000248014d2050046700440611150b6405c7e0ea41741134006972298017150b000255054061c400569054000d1e) else (if page < 3 then 0x254314a909c005092119b0c4d8a84a14a40000136007f0025050dd4148004960211217000821865480a001ad208c300d082a801b490b2001c0c25001687030c0410a1700139689a306702340417168b6305100228c12c60aed8654e100220961449c5d184702168787e000c003c9226c11004871020492174301690831c1b0013c2888002b824c82 else (if page < 4 then 0x1dce05c483d780e8c1e9294a00270c2100034090c00390253aa12c00220817480d8616801065093780fbf118109e485a062f9220ca8e00c520024000881040f0410611030752906041a0010861f0012210804e320029c088030a90e25c21e0e0d20016000e80021b0a6c049060e832249104185b0c3e80208104a0ca04c3fbe10c104e0c877e2512 else 0x2c104c006148148225df8d600794e51c1144203430824c05001a0011af482104abc0a461489069703539108613c949d2c16241fc30d20842541a001686144302d2215861d020f0882106119601920da00788248001c9e10a18910018a51189088f01e0c3f0019930e8006d282592171e01ee09d0c400c2086904486d2a02800b1507aa843004127))) else (if page < 7 then (if page < 6 then 0x707856f0472612001ac1112304a84371309cc056881c003a860e000fc90794c0e030bc9136b01b303324289303890205853a41a0083000a4023aa524c013220830c4d930a12148a8664e458004c004a604b08530000550464c800c54241a5b0e6107744358307d501a0016183bc1038209e00432c10a410808f4902a242e831b8b104002a00003c else 0x13000b4945a041d00171f04294a9023900005e0980817602012130901ed8586c130121e28423c8c002a05268401618225027c222830420010700f8029c01009883004400066113af81a2448bc10920fe407f7e4c860741100900b4a24b6081f090b00e023f2a07de038382300090216920b8b06d480cb607d693e300f723f0112de0f6908f4c178c) else (if page < 8 then 0x80013a002a180f041040036300e004b00158006aa06a703a800b86082084e0c4d8d0780136480b060e250ed31369c6b0c060223600fc08a80001001f550f6004f184abe07868b4182324408012c28489c284a2e8f114014c90480c412d20861404876022e800bc00640049043904100f13e9c2700400020408b1081500230009c1057001106243e else (if page < 9 then 0x2783094f06e00428009c209098250008391bd303a18a34422811003066d87d0205802640138184308418722c107ea89500209828138d4d827022d8411818d80c59183c400706022008e000180134014c049b4c2d8019c209a088c04532a0b4288e34290226921d9510c18244c22aa27d309c9c5b1a37121198126106f4e38181b00004a82b381f25 else 0xe008520803b625921080c7d482f121149020d8a50220841c00048903018163c1de0038089a040fbe14000d80830242b800ac0102187478548627c908204440c31801ad29021c295427842501142307a001282)))) else 0
  | 8 => if page < 1 then 0xc00060c052a0083005800648020c018e0042808b40418028c00c7804940050028e005200840047e028201150049002500201005e0089005280084014900204044c00aa0102004600400020d01090089c01000100004100094051e02800061000000304023e005b008b004260018001200a0c042c018c00ca008f0032a0006 else 0
  | 9 => if page < 1 then 0x0 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def search (k h : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel+1, lo, hi =>
    if lo+1 < hi then
      let m := (lo+hi)/2
      if field keys k 32 m ≤ h then search k h fuel m hi else search k h fuel lo m
    else lo

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let ix := search k (key xs) 14 0 (entries k)
  let slot := field targets k 17 ix
  (slot / 128,slot % 128)

def s45 : Switch := ⟨16,0xffff0000,0xffff00000000⟩
theorem s45_ok : s45.Valid := by unfold Switch.Valid; decide +kernel
def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel
def s35 : Switch := ⟨24,0xff00ff00,0xff00ff00000000⟩
theorem s35_ok : s35.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel
def s03 : Switch := ⟨7,0xaa00aa00aa00aa,0x5500550055005500⟩
theorem s03_ok : s03.Valid := by unfold Switch.Valid; decide +kernel
def s14 : Switch := ⟨14,0xcccc0000cccc,0x3333000033330000⟩
theorem s14_ok : s14.Valid := by unfold Switch.Valid; decide +kernel
def s25 : Switch := ⟨28,0xf0f0f0f0,0xf0f0f0f00000000⟩
theorem s25_ok : s25.Valid := by unfold Switch.Valid; decide +kernel
def s15 : Switch := ⟨30,0xcccccccc,0x3333333300000000⟩
theorem s15_ok : s15.Valid := by unfold Switch.Valid; decide +kernel
def s24 : Switch := ⟨12,0xf0f00000f0f0,0xf0f00000f0f0000⟩
theorem s24_ok : s24.Valid := by unfold Switch.Valid; decide +kernel
def s04 : Switch := ⟨15,0xaaaa0000aaaa,0x5555000055550000⟩
theorem s04_ok : s04.Valid := by unfold Switch.Valid; decide +kernel
def s13 : Switch := ⟨6,0xcc00cc00cc00cc,0x3300330033003300⟩
theorem s13_ok : s13.Valid := by unfold Switch.Valid; decide +kernel
def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s05 : Switch := ⟨31,0xaaaaaaaa,0x5555555500000000⟩
theorem s05_ok : s05.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s45]
  | 2 => [s34]
  | 3 => [s34, s35]
  | 4 => [s35, s34]
  | 5 => [s35]
  | 6 => [s12]
  | 7 => [s12, s45]
  | 8 => [s12, s34]
  | 9 => [s12, s34, s35]
  | 10 => [s12, s35, s34]
  | 11 => [s12, s35]
  | 12 => [s01]
  | 13 => [s01, s45]
  | 14 => [s01, s34]
  | 15 => [s01, s34, s35]
  | 16 => [s01, s35, s34]
  | 17 => [s01, s35]
  | 18 => [s01, s02]
  | 19 => [s01, s02, s45]
  | 20 => [s01, s02, s34]
  | 21 => [s01, s02, s34, s35]
  | 22 => [s01, s02, s35, s34]
  | 23 => [s01, s02, s35]
  | 24 => [s02, s01]
  | 25 => [s02, s01, s45]
  | 26 => [s02, s01, s34]
  | 27 => [s02, s01, s34, s35]
  | 28 => [s02, s01, s35, s34]
  | 29 => [s02, s01, s35]
  | 30 => [s02]
  | 31 => [s02, s45]
  | 32 => [s02, s34]
  | 33 => [s02, s34, s35]
  | 34 => [s02, s35, s34]
  | 35 => [s02, s35]
  | 36 => [s03, s14, s25]
  | 37 => [s03, s14, s25, s12]
  | 38 => [s03, s14, s25, s01]
  | 39 => [s03, s14, s25, s01, s02]
  | 40 => [s03, s14, s25, s02, s01]
  | 41 => [s03, s14, s25, s02]
  | 42 => [s03, s15, s24, s12]
  | 43 => [s03, s15, s24]
  | 44 => [s03, s15, s24, s01, s02]
  | 45 => [s03, s15, s24, s01]
  | 46 => [s03, s15, s24, s02]
  | 47 => [s03, s15, s24, s02, s01]
  | 48 => [s04, s13, s25, s01]
  | 49 => [s04, s13, s25, s01, s12]
  | 50 => [s04, s13, s25]
  | 51 => [s04, s13, s25, s02]
  | 52 => [s04, s13, s25, s12]
  | 53 => [s04, s13, s25, s12, s01]
  | 54 => [s04, s15, s23, s02, s12]
  | 55 => [s04, s15, s23, s02]
  | 56 => [s04, s15, s23, s12]
  | 57 => [s04, s15, s23, s12, s02]
  | 58 => [s04, s15, s23]
  | 59 => [s04, s15, s23, s01]
  | 60 => [s05, s13, s24, s01, s12]
  | 61 => [s05, s13, s24, s01]
  | 62 => [s05, s13, s24, s02]
  | 63 => [s05, s13, s24]
  | 64 => [s05, s13, s24, s12, s01]
  | 65 => [s05, s13, s24, s12]
  | 66 => [s05, s14, s23, s02]
  | 67 => [s05, s14, s23, s02, s12]
  | 68 => [s05, s14, s23, s12, s02]
  | 69 => [s05, s14, s23, s12]
  | 70 => [s05, s14, s23, s01]
  | 71 => [s05, s14, s23]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s45_ok, s34_ok, s35_ok, s12_ok, s01_ok, s02_ok, s03_ok, s14_ok, s25_ok, s15_ok, s24_ok, s04_ok, s13_ok, s23_ok, s05_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 9 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 6 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 6 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x16 : span (checked 4) 16 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x32 : span (checked 4) 16 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x48 : span (checked 4) 10 48 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 58 0 = true :=
  (@span_join (checked 4) 32 0 26 (@span_join (checked 4) 16 0 16 chunk4x0 chunk4x16) (@span_join (checked 4) 16 32 10 chunk4x32 chunk4x48))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x16 : span (checked 5) 16 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x32 : span (checked 5) 16 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x48 : span (checked 5) 16 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x64 : span (checked 5) 16 64 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x80 : span (checked 5) 16 80 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x96 : span (checked 5) 16 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x112 : span (checked 5) 16 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x128 : span (checked 5) 16 128 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x144 : span (checked 5) 16 144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x160 : span (checked 5) 16 160 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x176 : span (checked 5) 16 176 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x192 : span (checked 5) 16 192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x208 : span (checked 5) 16 208 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x224 : span (checked 5) 16 224 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x240 : span (checked 5) 16 240 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x256 : span (checked 5) 16 256 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x272 : span (checked 5) 16 272 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x288 : span (checked 5) 16 288 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x304 : span (checked 5) 16 304 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x320 : span (checked 5) 16 320 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x336 : span (checked 5) 16 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x352 : span (checked 5) 16 352 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x368 : span (checked 5) 16 368 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x384 : span (checked 5) 16 384 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x400 : span (checked 5) 16 400 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x416 : span (checked 5) 16 416 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x432 : span (checked 5) 16 432 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x448 : span (checked 5) 16 448 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x464 : span (checked 5) 16 464 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x480 : span (checked 5) 16 480 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x496 : span (checked 5) 16 496 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x512 : span (checked 5) 16 512 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x528 : span (checked 5) 16 528 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x544 : span (checked 5) 16 544 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x560 : span (checked 5) 16 560 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x576 : span (checked 5) 16 576 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x592 : span (checked 5) 16 592 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x608 : span (checked 5) 16 608 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x624 : span (checked 5) 16 624 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x640 : span (checked 5) 16 640 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x656 : span (checked 5) 16 656 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x672 : span (checked 5) 16 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x688 : span (checked 5) 16 688 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x704 : span (checked 5) 9 704 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 713 0 = true :=
  (@span_join (checked 5) 352 0 361 (@span_join (checked 5) 176 0 176 (@span_join (checked 5) 80 0 96 (@span_join (checked 5) 32 0 48 (@span_join (checked 5) 16 0 16 chunk5x0 chunk5x16) (@span_join (checked 5) 16 32 32 chunk5x32 (@span_join (checked 5) 16 48 16 chunk5x48 chunk5x64))) (@span_join (checked 5) 48 80 48 (@span_join (checked 5) 16 80 32 chunk5x80 (@span_join (checked 5) 16 96 16 chunk5x96 chunk5x112)) (@span_join (checked 5) 16 128 32 chunk5x128 (@span_join (checked 5) 16 144 16 chunk5x144 chunk5x160)))) (@span_join (checked 5) 80 176 96 (@span_join (checked 5) 32 176 48 (@span_join (checked 5) 16 176 16 chunk5x176 chunk5x192) (@span_join (checked 5) 16 208 32 chunk5x208 (@span_join (checked 5) 16 224 16 chunk5x224 chunk5x240))) (@span_join (checked 5) 48 256 48 (@span_join (checked 5) 16 256 32 chunk5x256 (@span_join (checked 5) 16 272 16 chunk5x272 chunk5x288)) (@span_join (checked 5) 16 304 32 chunk5x304 (@span_join (checked 5) 16 320 16 chunk5x320 chunk5x336))))) (@span_join (checked 5) 176 352 185 (@span_join (checked 5) 80 352 96 (@span_join (checked 5) 32 352 48 (@span_join (checked 5) 16 352 16 chunk5x352 chunk5x368) (@span_join (checked 5) 16 384 32 chunk5x384 (@span_join (checked 5) 16 400 16 chunk5x400 chunk5x416))) (@span_join (checked 5) 48 432 48 (@span_join (checked 5) 16 432 32 chunk5x432 (@span_join (checked 5) 16 448 16 chunk5x448 chunk5x464)) (@span_join (checked 5) 16 480 32 chunk5x480 (@span_join (checked 5) 16 496 16 chunk5x496 chunk5x512)))) (@span_join (checked 5) 96 528 89 (@span_join (checked 5) 48 528 48 (@span_join (checked 5) 16 528 32 chunk5x528 (@span_join (checked 5) 16 544 16 chunk5x544 chunk5x560)) (@span_join (checked 5) 16 576 32 chunk5x576 (@span_join (checked 5) 16 592 16 chunk5x592 chunk5x608))) (@span_join (checked 5) 48 624 41 (@span_join (checked 5) 16 624 32 chunk5x624 (@span_join (checked 5) 16 640 16 chunk5x640 chunk5x656)) (@span_join (checked 5) 16 672 25 chunk5x672 (@span_join (checked 5) 16 688 9 chunk5x688 chunk5x704))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x16 : span (checked 6) 16 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x32 : span (checked 6) 16 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x48 : span (checked 6) 16 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x64 : span (checked 6) 16 64 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x80 : span (checked 6) 16 80 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x96 : span (checked 6) 16 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x112 : span (checked 6) 16 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x128 : span (checked 6) 16 128 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x144 : span (checked 6) 16 144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x160 : span (checked 6) 16 160 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x176 : span (checked 6) 16 176 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x192 : span (checked 6) 16 192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x208 : span (checked 6) 16 208 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x224 : span (checked 6) 16 224 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x240 : span (checked 6) 16 240 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x256 : span (checked 6) 16 256 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x272 : span (checked 6) 16 272 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x288 : span (checked 6) 16 288 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x304 : span (checked 6) 16 304 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x320 : span (checked 6) 16 320 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x336 : span (checked 6) 16 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x352 : span (checked 6) 16 352 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x368 : span (checked 6) 16 368 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x384 : span (checked 6) 16 384 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x400 : span (checked 6) 16 400 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x416 : span (checked 6) 16 416 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x432 : span (checked 6) 16 432 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x448 : span (checked 6) 16 448 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x464 : span (checked 6) 16 464 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x480 : span (checked 6) 16 480 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x496 : span (checked 6) 16 496 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x512 : span (checked 6) 16 512 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x528 : span (checked 6) 16 528 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x544 : span (checked 6) 16 544 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x560 : span (checked 6) 16 560 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x576 : span (checked 6) 16 576 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x592 : span (checked 6) 16 592 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x608 : span (checked 6) 16 608 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x624 : span (checked 6) 16 624 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x640 : span (checked 6) 16 640 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x656 : span (checked 6) 16 656 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x672 : span (checked 6) 16 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x688 : span (checked 6) 16 688 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x704 : span (checked 6) 16 704 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x720 : span (checked 6) 16 720 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x736 : span (checked 6) 16 736 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x752 : span (checked 6) 16 752 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x768 : span (checked 6) 16 768 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x784 : span (checked 6) 16 784 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x800 : span (checked 6) 16 800 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x816 : span (checked 6) 16 816 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x832 : span (checked 6) 16 832 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x848 : span (checked 6) 16 848 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x864 : span (checked 6) 16 864 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x880 : span (checked 6) 16 880 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x896 : span (checked 6) 3 896 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 899 0 = true :=
  (@span_join (checked 6) 448 0 451 (@span_join (checked 6) 224 0 224 (@span_join (checked 6) 112 0 112 (@span_join (checked 6) 48 0 64 (@span_join (checked 6) 16 0 32 chunk6x0 (@span_join (checked 6) 16 16 16 chunk6x16 chunk6x32)) (@span_join (checked 6) 32 48 32 (@span_join (checked 6) 16 48 16 chunk6x48 chunk6x64) (@span_join (checked 6) 16 80 16 chunk6x80 chunk6x96))) (@span_join (checked 6) 48 112 64 (@span_join (checked 6) 16 112 32 chunk6x112 (@span_join (checked 6) 16 128 16 chunk6x128 chunk6x144)) (@span_join (checked 6) 32 160 32 (@span_join (checked 6) 16 160 16 chunk6x160 chunk6x176) (@span_join (checked 6) 16 192 16 chunk6x192 chunk6x208)))) (@span_join (checked 6) 112 224 112 (@span_join (checked 6) 48 224 64 (@span_join (checked 6) 16 224 32 chunk6x224 (@span_join (checked 6) 16 240 16 chunk6x240 chunk6x256)) (@span_join (checked 6) 32 272 32 (@span_join (checked 6) 16 272 16 chunk6x272 chunk6x288) (@span_join (checked 6) 16 304 16 chunk6x304 chunk6x320))) (@span_join (checked 6) 48 336 64 (@span_join (checked 6) 16 336 32 chunk6x336 (@span_join (checked 6) 16 352 16 chunk6x352 chunk6x368)) (@span_join (checked 6) 32 384 32 (@span_join (checked 6) 16 384 16 chunk6x384 chunk6x400) (@span_join (checked 6) 16 416 16 chunk6x416 chunk6x432))))) (@span_join (checked 6) 224 448 227 (@span_join (checked 6) 112 448 112 (@span_join (checked 6) 48 448 64 (@span_join (checked 6) 16 448 32 chunk6x448 (@span_join (checked 6) 16 464 16 chunk6x464 chunk6x480)) (@span_join (checked 6) 32 496 32 (@span_join (checked 6) 16 496 16 chunk6x496 chunk6x512) (@span_join (checked 6) 16 528 16 chunk6x528 chunk6x544))) (@span_join (checked 6) 48 560 64 (@span_join (checked 6) 16 560 32 chunk6x560 (@span_join (checked 6) 16 576 16 chunk6x576 chunk6x592)) (@span_join (checked 6) 32 608 32 (@span_join (checked 6) 16 608 16 chunk6x608 chunk6x624) (@span_join (checked 6) 16 640 16 chunk6x640 chunk6x656)))) (@span_join (checked 6) 112 672 115 (@span_join (checked 6) 48 672 64 (@span_join (checked 6) 16 672 32 chunk6x672 (@span_join (checked 6) 16 688 16 chunk6x688 chunk6x704)) (@span_join (checked 6) 32 720 32 (@span_join (checked 6) 16 720 16 chunk6x720 chunk6x736) (@span_join (checked 6) 16 752 16 chunk6x752 chunk6x768))) (@span_join (checked 6) 64 784 51 (@span_join (checked 6) 32 784 32 (@span_join (checked 6) 16 784 16 chunk6x784 chunk6x800) (@span_join (checked 6) 16 816 16 chunk6x816 chunk6x832)) (@span_join (checked 6) 32 848 19 (@span_join (checked 6) 16 848 16 chunk6x848 chunk6x864) (@span_join (checked 6) 16 880 3 chunk6x880 chunk6x896))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x16 : span (checked 7) 16 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x32 : span (checked 7) 16 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x48 : span (checked 7) 16 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x64 : span (checked 7) 16 64 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x80 : span (checked 7) 16 80 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x96 : span (checked 7) 16 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x112 : span (checked 7) 16 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x128 : span (checked 7) 16 128 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x144 : span (checked 7) 16 144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x160 : span (checked 7) 10 160 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 170 0 = true :=
  (@span_join (checked 7) 80 0 90 (@span_join (checked 7) 32 0 48 (@span_join (checked 7) 16 0 16 chunk7x0 chunk7x16) (@span_join (checked 7) 16 32 32 chunk7x32 (@span_join (checked 7) 16 48 16 chunk7x48 chunk7x64))) (@span_join (checked 7) 48 80 42 (@span_join (checked 7) 16 80 32 chunk7x80 (@span_join (checked 7) 16 96 16 chunk7x96 chunk7x112)) (@span_join (checked 7) 16 128 26 chunk7x128 (@span_join (checked 7) 16 144 10 chunk7x144 chunk7x160))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x0 : span (checked 8) 6 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer8 : span (checked 8) 6 0 = true :=
  chunk8x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk9x0 : span (checked 9) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer9 : span (checked 9) 1 0 = true :=
  chunk9x0
theorem verified : ∀ k ≤ 9, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer7 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer8 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer9 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 10 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 9
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    9 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Full



namespace SignedFrontier.CliqueLink
def target := SmallCert.Full.target
def raw := SmallCert.Full.raw
def initial : List W := [0, ~~~(0 : W)] ++ raw ++ raw.map (fun w => ~~~w)
theorem lower (p : List (ℕ × ℕ)) (o : ℕ) (hit : canonical (evaluate p initial o) = target) : 10 ≤ p.length := by
  have inside : {target} ⊆ available (p.foldl add initial) := by
    apply Finset.singleton_subset_iff.mpr
    rw [←hit]
    exact available_read _ _
  obtain ⟨k,s,le,access,run⟩ := extract p initial target 0 {target} Cone.done inside
  have start : available initial = insert 0 SmallCert.Full.raw.toFinset := by decide +kernel
  rw [start] at access
  have bounded := SmallCert.Full.lower run access
  omega
end SignedFrontier.CliqueLink

namespace TableLink
open SignedFrontier

def assignment (r : Fin 64) (v : Fin 6) : Bool := r.val.testBit v.val

theorem rawTable : ∀ r : Fin 64, CliqueLink.initial.map (fun u => u.getLsbD r.val) =
    ThresholdReplacement.signedStart (assignment r) := by decide +kernel

theorem goalTable : ∀ r : Fin 64, CliqueLink.target.getLsbD r.val =
    ThresholdReplacement.sliceTarget (assignment r) := by decide +kernel

theorem readDefault (xs : List W) (j r : ℕ) :
    (xs.getD j 0).getLsbD r = (xs.map (fun u => u.getLsbD r)).getD j false := by
  by_cases hj : j < xs.length
  · rw [List.getD_eq_getElem _ _ hj,List.getD_eq_getElem _ _ (by simpa using hj)]
    simp
  · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem addRow (xs : List W) (ij : ℕ × ℕ) (r : ℕ) (hr : r < 64) :
    (add xs ij).map (fun u => u.getLsbD r) =
      PetersenSignedSlice.addPair (xs.map (fun u => u.getLsbD r)) ij := by
  simp only [add,PetersenSignedSlice.addPair,List.map_append,List.map_cons,List.map_nil,
      BitVec.getLsbD_and,BitVec.getLsbD_not,hr,decide_true,Bool.true_and,readDefault]

theorem foldRow (p : List (ℕ × ℕ)) (xs : List W) (r : Fin 64) :
    (p.foldl add xs).map (fun u => u.getLsbD r.val) =
      p.foldl PetersenSignedSlice.addPair (xs.map (fun u => u.getLsbD r.val)) := by
  induction p generalizing xs with
  | nil => rfl
  | cons ij tail ih =>
    simp only [List.foldl_cons,ih,addRow _ _ _ r.isLt]

theorem wordOfSolution (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : ∀ x, ThresholdReplacement.signed p o x = ThresholdReplacement.sliceTarget x) :
    canonical (evaluate p CliqueLink.initial o) = CliqueLink.target := by
  have eq : evaluate p CliqueLink.initial o = CliqueLink.target := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Fin 64 := ⟨i,hi⟩
    change ((p.foldl add CliqueLink.initial).getD o 0).getLsbD r.val = _
    rw [readDefault,foldRow p CliqueLink.initial r,rawTable r]
    exact (hit (assignment r)).trans (goalTable r).symm
  rw [eq]
  decide +kernel

theorem sliceRequirement
    (lower : ∀ p o, canonical (evaluate p CliqueLink.initial o) = CliqueLink.target → 10 ≤ p.length)
    (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : ∀ x, ThresholdReplacement.signed p o x = ThresholdReplacement.sliceTarget x) : 10 ≤ p.length :=
  lower p o (wordOfSolution p o hit)

end TableLink

end PEqualNP.Outside.L_meta_12254_aux

open PEqualNP.Outside.L_meta_12254_aux

theorem PEqualNP.Outside.L_meta_12254 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269834368 * 2 ^ 32 + 2155905024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269834368 * 2 ^ 32 + 2155905024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s existsC
  obtain ⟨C,ok,bound,hit⟩ := existsC
  obtain ⟨D,mono,small,evaluates⟩ := ThresholdReplacement.replacement
    (TableLink.sliceRequirement SignedFrontier.CliqueLink.lower) C ok hit
  exact ⟨D,mono,small.trans bound,evaluates⟩
