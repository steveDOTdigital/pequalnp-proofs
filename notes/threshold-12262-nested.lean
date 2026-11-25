import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12262_aux

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

def target (x : Fin 6 → Bool) := Nat.testBit (4269860992 * 2 ^ 32 + 3900735616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[
  ⟨.or, [0,1]⟩,
  ⟨.and, [0,1]⟩,
  ⟨.or, [6,2]⟩,
  ⟨.and, [7,2]⟩,
  ⟨.and, [6,2]⟩,
  ⟨.or, [10,7]⟩,
  ⟨.or, [4,5]⟩,
  ⟨.and, [4,5]⟩,
  ⟨.and, [11,12]⟩,
  ⟨.and, [8,13]⟩,
  ⟨.or, [14,15]⟩,
  ⟨.and, [3,16]⟩,
  ⟨.or, [9,17]⟩], 18⟩
theorem size : witness.size = 13 := by decide +kernel
theorem legal : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel
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
    (sliceLower : ∀ p o, (∀ x, signed p o x = sliceTarget x) → 12 ≤ p.length)
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
    exact ⟨witness, legal, by rw [size]; change 13 ≤ C.gates.length; omega, value⟩

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

def essentialRows (g : W) (raw : List W) (xs : List (W × Fin 64 × Fin 64)) :=
  xs.all (fun t => decide (g.getLsbD t.2.1.val ≠ g.getLsbD t.2.2.val) &&
    raw.all (fun v => v == t.1 || (v.getLsbD t.2.1.val == v.getLsbD t.2.2.val)))

theorem essentialOfRows (g : W) (raw : List W) (xs : List (W × Fin 64 × Fin 64))
    (covers : xs.map Prod.fst = raw) (test : essentialRows g raw xs = true) : Essential g raw := by
  intro w hw
  rw [← covers] at hw
  obtain ⟨⟨v,i,j⟩, hv, rfl⟩ := List.mem_map.mp hw
  have both := Bool.and_eq_true_iff.mp (List.all_eq_true.mp test (v,i,j) hv)
  refine ⟨i,j,of_decide_eq_true both.1,?_⟩
  intro u hu ne
  have h := List.all_eq_true.mp both.2 u hu
  simpa [ne] using h

end SignedFrontier

namespace SignedFrontier.Packed

-- These packed integers only propose a negative input row. Every proposed
-- obstruction is tested on the original signals before a successor is skipped.
structure Columns where
  w : W
  pos : Nat
  neg : Nat

def fullLanes : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def positions (w : W) : Nat := w.toNat * 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
def equalRows (p : Columns) : Nat := fullLanes ^^^ (p.pos ^^^ p.neg)
def bothCols (a b : Columns) : Columns := ⟨a.w &&& b.w, a.pos &&& b.pos, a.neg &&& b.neg⟩
def notCols (a : Columns) : Columns := ⟨~~~a.w, fullLanes ^^^ a.pos, fullLanes ^^^ a.neg⟩
def orCols (a b : Columns) : Columns := ⟨a.w ||| b.w, a.pos ||| b.pos, a.neg ||| b.neg⟩
def variants (a b : Columns) : List Columns :=
  [bothCols a b,bothCols a (notCols b),bothCols (notCols a) b,orCols a b]

end SignedFrontier.Packed


namespace SignedFrontier.Vector
open SignedFrontier.Packed (Columns bothCols orCols notCols variants equalRows fullLanes)

-- Each successive 64-bit lane corresponds to one negative input row.
def lanes (rows : List Nat) (f : Nat → W) : Nat :=
  match rows with
  | [] => 0
  | r :: rs => (f r).toNat ||| (lanes rs f <<< 64)

theorem lane_bit (rows : List Nat) (f : Nat → W) (i j : Nat) (hj : j < 64) :
    (lanes rows f).testBit (64*i+j) =
      match rows[i]? with | some r => (f r).getLsbD j | none => false := by
  induction rows generalizing i with
  | nil => simp [lanes]
  | cons r rs ih =>
    cases i with
    | zero => simp [lanes,BitVec.getLsbD, Nat.not_le.mpr hj]
    | succ i =>
      have bound : 64 ≤ 64*(i+1)+j := by omega
      have sub : 64*(i+1)+j-64 = 64*i+j := by omega
      have off : (f r).toNat.testBit (64*(i+1)+j) = false := by
        change (f r).getLsbD (64*(i+1)+j) = false
        simp [BitVec.getLsbD_of_ge, bound]
      simpa only [lanes,Nat.testBit_or,Nat.testBit_shiftLeft,off,bound,decide_true,
        Bool.true_and,Bool.false_or,sub,List.getElem?_cons_succ] using ih i

def negativeLane (w : W) (r : Nat) : W := if w.getLsbD r then ~~~0 else 0

def coefficient : Nat → Nat
  | 0 => 0
  | n+1 => 2^64 * coefficient n + 1

theorem constant_lanes (rows : List Nat) (w : W) :
    lanes rows (fun _ => w) = w.toNat * coefficient rows.length := by
  induction rows with
  | nil => simp [lanes,coefficient]
  | cons r rs ih =>
    simp only [lanes,List.length_cons,coefficient,ih]
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt w.isLt, Nat.shiftLeft_eq]
    ring

def columns (rows : List Nat) (w : W) : Columns :=
  ⟨w, Packed.positions w, lanes rows (negativeLane w)⟩

def Valid (rows : List Nat) (c : Columns) : Prop :=
  ∀ i j r, j < 64 → rows[i]? = some r →
    c.pos.testBit (64*i+j) = c.w.getLsbD j ∧ c.neg.testBit (64*i+j) = c.w.getLsbD r

theorem columns_valid (rows : List Nat) (length : rows.length = 44) (w : W) : Valid rows (columns rows w) := by
  intro i j r hj hr
  have fast : Packed.positions w = lanes rows (fun _ => w) := by
    rw [constant_lanes,length]
    rfl
  simp only [columns,fast,lane_bit rows _ i j hj,hr]
  cases on : w.getLsbD r
  · simp [negativeLane,on]
  · simp only [negativeLane,on,ite_true,BitVec.getLsbD_not,hj,decide_true,
      Bool.true_and]
    simp

set_option maxRecDepth 9000 in
theorem full_bit {rows : List Nat} (length : rows.length = 44) {i j r : Nat}
    (hj : j < 64) (hr : rows[i]? = some r) : fullLanes.testBit (64*i+j) = true := by
  have hi := (List.getElem?_eq_some_iff.mp hr).choose
  have lt : 64*i+j < 2816 := by omega
  have val : fullLanes = 2^2816-1 := by decide +kernel
  rw [val, Nat.testBit_two_pow_sub_one, decide_eq_true lt]

theorem valid_and {rows : List Nat} {a b : Columns} (ha : Valid rows a) (hb : Valid rows b) :
    Valid rows (bothCols a b) := by
  intro i j r hj hr
  obtain ⟨ap,an⟩ := ha i j r hj hr
  obtain ⟨bp,bn⟩ := hb i j r hj hr
  simp [bothCols,ap,an,bp,bn]

theorem valid_or {rows : List Nat} {a b : Columns} (ha : Valid rows a) (hb : Valid rows b) :
    Valid rows (orCols a b) := by
  intro i j r hj hr
  obtain ⟨ap,an⟩ := ha i j r hj hr
  obtain ⟨bp,bn⟩ := hb i j r hj hr
  simp [orCols,ap,an,bp,bn]

theorem valid_not {rows : List Nat} (length : rows.length = 44) (bounds : ∀ r ∈ rows, r < 64)
    {a : Columns} (ha : Valid rows a) : Valid rows (notCols a) := by
  intro i j r hj hr
  have limit := bounds r (List.mem_of_getElem? hr)
  obtain ⟨ap,an⟩ := ha i j r hj hr
  simp [notCols,full_bit length hj hr,ap,an,hj,limit]

theorem variant_valid {rows : List Nat} (length : rows.length = 44) (bounds : ∀ r ∈ rows, r < 64)
    {a b c : Columns} (ha : Valid rows a) (hb : Valid rows b) (hc : c ∈ variants a b) :
    Valid rows c := by
  simp only [variants,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact valid_and ha hb
  · exact valid_and ha (valid_not length bounds hb)
  · exact valid_and (valid_not length bounds ha) hb
  · exact valid_or ha hb

def Mask (g : W) (rows : List Nat) (s : List W) (m : Nat) : Prop :=
  ∀ i j, j < 64 → m.testBit (64*i+j) = true → ∃ r, rows[i]? = some r ∧
    g.getLsbD j = true ∧ ∀ u ∈ s, u.getLsbD r = u.getLsbD j

theorem initial (g : W) (rows : List Nat) : Mask g rows [] (lanes rows (fun _ => g)) := by
  intro i j hj hit
  rw [lane_bit rows _ i j hj] at hit
  cases hr : rows[i]? with
  | none => simp [hr] at hit
  | some r => exact ⟨r,rfl,by simpa [hr] using hit,by simp⟩

theorem addMask {g : W} {rows : List Nat} (length : rows.length = 44) {s : List W}
    {m : Nat} {c : Columns} (mask : Mask g rows s m) (valid : Valid rows c) :
    Mask g rows (c.w :: s) (m &&& equalRows c) := by
  intro i j hj hit
  obtain ⟨old,added⟩ := Bool.and_eq_true_iff.mp ((Nat.testBit_and ..).symm ▸ hit)
  obtain ⟨r,hr,hg,same⟩ := mask i j hj old
  obtain ⟨ap,an⟩ := valid i j r hj hr
  have eq : c.w.getLsbD r = c.w.getLsbD j := by
    simp only [equalRows,Nat.testBit_xor,full_bit length hj hr,ap,an] at added
    cases hp : c.w.getLsbD j <;> cases hn : c.w.getLsbD r <;> simp_all
  exact ⟨r,hr,hg,fun w hw => (List.mem_cons.mp hw).elim (fun h => h ▸ eq) (same w)⟩

theorem survivor_complete (r j : Nat) (hj : j < 64) (s : List W) (m : W)
    (on : m.getLsbD j = true) (same : ∀ w ∈ s, w.getLsbD r = w.getLsbD j) :
    (survivors r s m).getLsbD j = true := by
  induction s generalizing m with
  | nil => exact on
  | cons w ws ih =>
    have ne : m ≠ 0 := by rintro rfl; simp at on
    rw [survivors,ite_eq_right ne]
    apply ih
    · have eq := same w List.mem_cons_self
      cases hv : w.getLsbD r <;> simp_all [rowMask]
    · exact fun u hu => same u (List.mem_cons_of_mem _ hu)

theorem clear {g : W} {rows : List Nat} {s : List W} {m : Nat}
    (mask : Mask g rows s m) (coveredRows : covered g rows s = true) : m = 0 := by
  apply Nat.eq_of_testBit_eq
  intro n
  cases hn : m.testBit n with
  | false => simp
  | true =>
    have split : 64*(n/64)+n%64 = n := by omega
    obtain ⟨r,hr,hg,agree⟩ := mask (n/64) (n%64) (by omega) (split.symm ▸ hn)
    have z := beq_iff_eq.mp (List.all_eq_true.mp coveredRows r (List.mem_of_getElem? hr))
    have p := survivor_complete r (n%64) (by omega) s g hg agree
    simp [z] at p


theorem weaken {g : W} {rows : List Nat} {s t : List W} {m : Nat}
    (h : Mask g rows s m) (sub : ∀ w ∈ t, w ∈ s) : Mask g rows t m := by
  intro i j hj hm
  obtain ⟨r,hr,hg,agree⟩ := h i j hj hm
  exact ⟨r,hr,hg,fun w hw => agree w (sub w hw)⟩

theorem foldMask {g : W} {rows : List Nat} (length : rows.length = 44) (xs : List Columns)
    (ok : ∀ c ∈ xs, Valid rows c) (s : List W) (m : Nat) (h : Mask g rows s m) :
    Mask g rows (xs.map Columns.w ++ s) (xs.foldl (fun n c => n &&& equalRows c) m) := by
  induction xs generalizing s m with
  | nil => simpa using h
  | cons c cs ih =>
    have rest := ih (fun z hz => ok z (List.mem_cons_of_mem _ hz)) (c.w :: s)
      (m &&& equalRows c) (addMask length h (ok c List.mem_cons_self))
    apply weaken rest
    intro w hw
    simpa [or_assoc,or_comm,or_left_comm] using hw

def branch (_g : W) (seek : List W → Bool) (k len m : Nat) (next : List W) : Bool :=
  decide (len ≤ k) && m == 0 && !seek next

theorem branch_of {g : W} {rows : List Nat} {seek : List W → Bool} {k len m : Nat}
    {next : List W} (dims : len ≤ k) (mask : Mask g rows next m)
    (cov : covered g rows next = true) (miss : seek next = false) :
    branch g seek k len m next = true := by simp [branch,dims,clear mask cov,miss]
def packedPair (g : W) (_rows : List Nat) (seek : List W → Bool) (k : Nat)
    (initialMask : Nat) (s : List W) (t : List Columns) (a b : Columns) : Bool :=
  let cs := variants a b
  cs.any (fun c => c.w == g) ||
    let base := t.filter (fun u => u.w != a.w && u.w != b.w)
    let rest := s.filter (fun u => u != a.w && u != b.w)
    let mask := base.foldl (fun m z => m &&& equalRows z) initialMask
    let ra := equalRows a
    let rb := equalRows b
    let len := rest.length
    cs.any fun c => c.w != 0 && !s.contains c.w &&
      let m := mask &&& equalRows c
      (branch g seek k len m (c.w :: rest) ||
       branch g seek k (len + 1) (m &&& ra) (c.w :: a.w :: rest) ||
       branch g seek k (len + 1) (m &&& rb) (c.w :: b.w :: rest) ||
       branch g seek k (len + 2) (m &&& ra &&& rb) (c.w :: a.w :: b.w :: rest))

theorem pair_of (g : W) (rows : List Nat) (seek : List W → Bool) (k : Nat)
    (s : List W) (t : List Columns) (a b : Columns)
    (initialMask : Nat) (start : Mask g rows [] initialMask)
    (length : rows.length = 44) (bounds : ∀ r ∈ rows, r < 64)
    (stock : t.map Columns.w = s) (valid : ∀ z ∈ t, Valid rows z)
    (va : Valid rows a) (vb : Valid rows b)
    (ha : a.w ∈ s) (hb : b.w ∈ s) (absent : g ∉ s)
    (slow : onePair s (fun u => u.contains g || (decide (0 < k) && decide (u.length ≤ k+1)
      && covered g rows u && !seek u)) a.w b.w = true) :
    packedPair g rows seek k initialMask s t a b = true := by
  have vw : (variants a b).map Columns.w = choices a.w b.w := rfl
  obtain ⟨w,form,test⟩ := List.any_eq_true.mp slow
  obtain ⟨fresh,keeps⟩ := Bool.and_eq_true_iff.mp test
  obtain ⟨ka,_,next⟩ := List.any_eq_true.mp keeps
  obtain ⟨kb,_,ok⟩ := List.any_eq_true.mp next
  rw [←vw] at form
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp form
  unfold packedPair
  apply Bool.or_eq_true_iff.mpr
  by_cases hit : c.w = g
  · exact Or.inl (List.any_eq_true.mpr ⟨c,hc,beq_iff_eq.mpr hit⟩)
  · right
    apply List.any_eq_true.mpr
    refine ⟨c,hc,Bool.and_eq_true_iff.mpr ⟨fresh,?_⟩⟩
    have na : g ≠ a.w := fun e => absent (e ▸ ha)
    have nb : g ≠ b.w := fun e => absent (e ▸ hb)
    have stop : (after s a.w b.w c.w ka kb).contains g = false := by
      cases ka <;> cases kb <;>
        simp [after,withWire,List.contains_eq_mem,Ne.symm hit,na,nb,absent]
    dsimp only at ok
    rw [stop,Bool.false_or] at ok
    obtain ⟨first,last⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨dims,cov⟩ := Bool.and_eq_true_iff.mp first
    have hl := of_decide_eq_true (Bool.and_eq_true_iff.mp dims).2
    have miss : seek (after s a.w b.w c.w ka kb) = false := by simpa using last
    let rest := s.filter fun u => u != a.w && u != b.w
    let base := t.filter fun u => u.w != a.w && u.w != b.w
    let m := base.foldl (fun n z => n &&& equalRows z) initialMask
    have shape : base.map Columns.w = rest := by
      change (t.filter (fun u => u.w != a.w && u.w != b.w)).map Columns.w =
        s.filter (fun u => u != a.w && u != b.w)
      rw [← stock, List.filter_map]
      rfl
    have core := foldMask length base (fun z hz => valid z (List.mem_filter.mp hz).1) [] _ start
    have trimmed : Mask g rows rest m := by simpa [shape,m] using core
    have vc := variant_valid length bounds va vb hc
    let mc := m &&& equalRows c
    have raw : Mask g rows (c.w :: rest) mc := addMask length trimmed vc
    have withA : Mask g rows (c.w :: a.w :: rest) (mc &&& equalRows a) :=
      weaken (addMask length raw va) (by simp [or_left_comm])
    have withB : Mask g rows (c.w :: b.w :: rest) (mc &&& equalRows b) :=
      weaken (addMask length raw vb) (by simp [or_left_comm])
    have withBoth : Mask g rows (c.w :: a.w :: b.w :: rest)
        (mc &&& equalRows a &&& equalRows b) :=
      weaken (addMask length withA vb) (by simp [or_left_comm])
    cases ka <;> cases kb <;>
      simp only [after,withWire,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at hl cov miss
    all_goals
      simp only [Bool.or_eq_true_iff]
      first
      | exact Or.inl (Or.inl (Or.inl (branch_of (by omega) raw cov miss)))
      | exact Or.inl (Or.inl (Or.inr (branch_of (by omega) withA cov miss)))
      | exact Or.inl (Or.inr (branch_of (by omega) withB cov miss))
      | exact Or.inr (branch_of (by omega) withBoth cov miss)

def packedClosed (g : W) (rows : List Nat) (initialMask : Nat) (words : Nat → Nat → List W)
    (count : Nat → Nat) (lookup : Nat → List W → Nat × Nat) (sym : Nat → List Switch) :
    Nat → Nat → Bool
  | 0,i => !(words 0 i).contains g
  | k+1,i =>
    let s := words (k+1) i
    let t := s.map (columns rows)
    !s.contains g && !(t.any fun a => t.any fun b => decide (a.w.toNat < b.w.toNat) &&
      packedPair g rows (found words count lookup sym k) k initialMask s t a b)

theorem closed_sound (g : W) (rows : List Nat) (initialMask : Nat)
    (maskSpec : initialMask = lanes rows (fun _ => g)) (words : Nat → Nat → List W)
    (count : Nat → Nat) (lookup : Nat → List W → Nat × Nat) (sym : Nat → List Switch)
    (length : rows.length = 44) (bounds : ∀ r ∈ rows, r < 64)
    (k i : Nat) (ok : packedClosed g rows initialMask words count lookup sym k i = true) :
    closed g rows words count lookup sym k i = true := by
  cases k with
  | zero => exact ok
  | succ k =>
    obtain ⟨absent,verified⟩ := Bool.and_eq_true_iff.mp ok
    apply Bool.and_eq_true_iff.mpr
    refine ⟨absent,?_⟩
    let s := words (k+1) i
    let t := s.map (columns rows)
    let seek := found words count lookup sym k
    have ng : g ∉ s := by simpa [s,List.contains_eq_mem] using absent
    by_contra! fail
    have h : moves s (fun u => u.contains g || (decide (0 < k) && decide (u.length ≤ k+1) &&
        covered g rows u && !seek u)) = true := by simpa [s,seek] using fail
    obtain ⟨a,ha,inner⟩ := List.any_eq_true.mp h
    obtain ⟨b,hb,both⟩ := List.any_eq_true.mp inner
    obtain ⟨lt,slow⟩ := Bool.and_eq_true_iff.mp both
    have st : t.map Columns.w = s := by simp [t,columns,List.map_map,Function.comp_def]
    have valid : ∀ z ∈ t, Valid rows z := by
      rintro z hz
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
      exact columns_valid rows length u
    have fast := pair_of g rows seek k s t (columns rows a) (columns rows b) _
      (maskSpec.symm ▸ initial g rows) length bounds st valid (columns_valid rows length a) (columns_valid rows length b)
      ha hb ng slow
    have yes : (t.any fun a => t.any fun b => decide (a.w.toNat < b.w.toNat) &&
        packedPair g rows seek k initialMask s t a b) = true :=
      List.any_eq_true.mpr ⟨columns rows a,List.mem_map.mpr ⟨a,ha,rfl⟩,
        List.any_eq_true.mpr ⟨columns rows b,List.mem_map.mpr ⟨b,hb,rfl⟩,
          Bool.and_eq_true_iff.mpr ⟨lt,fast⟩⟩⟩
    change (!(t.any fun a => t.any fun b => decide (a.w.toNat < b.w.toNat) &&
      packedPair g rows seek k initialMask s t a b)) = true at verified
    simp [yes] at verified

end SignedFrontier.Vector

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

namespace SignedFrontier

def rowMap (f : Fin 64 → Fin 64) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun r : Fin 64 => w.getLsbD (f r).val))).cast (by simp)

theorem rowMap_read (f : Fin 64 → Fin 64) (w : W) (r : Fin 64) :
    (rowMap f w).getLsbD r.val = w.getLsbD (f r).val := by
  simp only [rowMap, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]

theorem rowMap_form (f : Fin 64 → Fin 64) (a b w : W) (h : w ∈ choices a b) :
    rowMap f w ∈ choices (rowMap f a) (rowMap f b) := by
  have ab (u v : W) : rowMap f (u &&& v) = rowMap f u &&& rowMap f v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have rwAt := fun z => rowMap_read f z ⟨i,hi⟩
    simp only [rwAt,BitVec.getLsbD_and]
  have ob (u v : W) : rowMap f (u ||| v) = rowMap f u ||| rowMap f v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have rwAt := fun z => rowMap_read f z ⟨i,hi⟩
    simp only [rwAt,BitVec.getLsbD_or]
  have nb (u : W) : rowMap f (~~~u) = ~~~(rowMap f u) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have rwAt := fun z => rowMap_read f z ⟨i,hi⟩
    simp only [rwAt,BitVec.getLsbD_not,hi,(f ⟨i,hi⟩).isLt,decide_true,Bool.true_and]
  simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl <;> simp [ab,ob,nb]

-- Equality in the projected gate budget preserves every live image. A live
-- input becoming constant therefore forces at least one further saved gate.
theorem Cone.project {g : W} {k : Nat} {s : Finset W} (h : Cone g k s)
    (f : W → W) (hom : ∀ a b w, w ∈ choices a b → f w ∈ choices (f a) (f b))
    (nz : f g ≠ 0) : ∃ j t, j ≤ k ∧ Cone (f g) j t ∧ t ⊆ s.image f ∧
      (j = k → s.image f ⊆ t) := by
  induction h with
  | done => exact ⟨0,{f g},le_rfl,Cone.done,by simp,by simp⟩
  | @step k needed a b w rest want a0 b0 ab aw bw form ih =>
    obtain ⟨j,t,le,run,ht,full⟩ := ih
    let old := insert a (insert b (needed.erase w))
    have aa : f a ∈ old.image f := Finset.mem_image_of_mem _ (by simp [old])
    have bb : f b ∈ old.image f := Finset.mem_image_of_mem _ (by simp [old])
    have former (x : W) (hx : x ∈ needed) (ne : x ≠ w) : f x ∈ old.image f :=
      Finset.mem_image_of_mem _ (by simp [old,hx,ne])
    change ∃ j t, j ≤ k+1 ∧ Cone (f g) j t ∧ t ⊆ old.image f ∧ (j = k+1 → old.image f ⊆ t)
    by_cases sub : t ⊆ old.image f
    · exact ⟨j,t,by omega,run,sub,by omega⟩
    · have special (x : W) (hx : x ∈ t) : x = f w ∨ x ∈ old.image f := by
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp (ht hx)
        by_cases eq : z = w
        · exact Or.inl (congrArg f eq)
        · exact Or.inr (former z hz eq)
      have used : f w ∈ t := by
        by_contra bad
        exact sub (fun x hx => (special x hx).resolve_left (fun e => bad (e ▸ hx)))
      have fresh : f w ∉ old.image f := fun inside =>
        sub (fun x hx => (special x hx).elim (fun e => e ▸ inside) id)
      have nzW : f w ≠ 0 := fun e => run.noZero nz (e ▸ used)
      have op := hom a b w form
      have good : ¬(f a = 0 ∨ f b = 0 ∨ f a = f b) := by
        intro bad
        rcases constants (f a) (f b) bad _ op with e | e | e
        · exact nzW e
        · exact fresh (e ▸ aa)
        · exact fresh (e ▸ bb)
      let next := insert (f a) (insert (f b) (t.erase (f w)))
      have step : Cone (f g) (j+1) next := Cone.step run used (fun e => good (Or.inl e))
        (fun e => good (Or.inr (Or.inl e))) (fun e => good (Or.inr (Or.inr e)))
        (fun e => fresh (e ▸ aa)) (fun e => fresh (e ▸ bb)) op
      refine ⟨j+1,next,by omega,step,?_,?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact aa
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact bb
        have z := Finset.mem_erase.mp hx
        exact (special x z.2).resolve_left z.1
      · intro eq x hx
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
        rcases Finset.mem_insert.mp hz with rfl | hz
        · simp [next]
        rcases Finset.mem_insert.mp hz with rfl | hz
        · simp [next]
        have cond := Finset.mem_erase.mp hz
        have oldMem := former z cond.2 cond.1
        have dif : f z ≠ f w := fun e => fresh (e ▸ oldMem)
        have live := full (by omega) (Finset.mem_image_of_mem f cond.2)
        simp [next,dif,live]

end SignedFrontier

namespace SignedFrontier

-- Project signed truth tables along any map of rows. Canonicalization allows
-- complemented inputs and high pins as well as low pins.
def signedMap (f : Fin 64 → Fin 64) (w : W) := canonical (rowMap f w)

theorem canonical_choice (a b w : W) (h : w ∈ choices a b) :
    canonical w ∈ choices (canonical a) (canonical b) := by
  simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact operation a b
  · simpa only [canonical_not] using operation a (~~~b)
  · simpa only [canonical_not] using operation (~~~a) b
  · simpa only [BitVec.not_and,BitVec.not_not,← BitVec.not_or,canonical_not] using
      operation (~~~a) (~~~b)

theorem signedMap_choice (f : Fin 64 → Fin 64) (a b w : W) (h : w ∈ choices a b) :
    signedMap f w ∈ choices (signedMap f a) (signedMap f b) :=
  canonical_choice _ _ _ (rowMap_form f a b w h)

def signedLower (g : W) (raw : List W) (n : Nat) : Prop :=
  ∀ {k : Nat} {s : Finset W}, Cone g k s → s ⊆ insert 0 raw.toFinset → n ≤ k

-- Test a live suffix after some early gates have been fixed. Its starting
-- signals must all become raw inputs or constants on the chosen restriction.
-- If a live signal becomes zero, the suffix loses one further operation.
def cofactorReject (f : Fin 64 → Fin 64) (raw : List W) (n budget : Nat) (s : List W) : Bool :=
  let ws := s.map (signedMap f)
  ws.all (fun w => w == 0 || raw.contains w) &&
    (decide (budget < n) || (decide (budget ≤ n) && ws.contains 0))

theorem cofactorReject_sound (f : Fin 64 → Fin 64) (g : W) (raw : List W) (n budget : Nat)
    (nz : signedMap f g ≠ 0) (low : signedLower (signedMap f g) raw n)
    (s : List W) {k : Nat} (le : k ≤ budget) (run : Cone g k s.toFinset) :
    cofactorReject f raw n budget s = false := by
  by_contra! bad
  have both := Bool.and_eq_true_iff.mp (show cofactorReject f raw n budget s = true by simpa using bad)
  have stock : (s.map (signedMap f)).toFinset = s.toFinset.image (signedMap f) := by
    ext z
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_image]
  have sub : s.toFinset.image (signedMap f) ⊆ insert 0 raw.toFinset := by
    intro w hw
    rw [←stock] at hw
    have h := List.all_eq_true.mp both.1 w (List.mem_toFinset.mp hw)
    simpa [List.contains_eq_mem] using h
  obtain ⟨j,t,small,p,inside,full⟩ := run.project (signedMap f) (signedMap_choice f) nz
  have lower := low p (inside.trans sub)
  rcases Bool.or_eq_true_iff.mp both.2 with short | keep
  · have := of_decide_eq_true short
    omega
  · obtain ⟨h,z⟩ := Bool.and_eq_true_iff.mp keep
    have lim := of_decide_eq_true h
    have zero : 0 ∈ s.toFinset.image (signedMap f) := by rw [←stock]; simpa using z
    exact p.noZero nz (full (by omega) zero)

end SignedFrontier

namespace SignedFrontier

-- Masked rows suffice because every projected row lies on this slice.
theorem signedMap_eq_of_mask (f : Fin 64 → Fin 64) (mask a b : W)
    (covers : ∀ i, mask.getLsbD (f i).val = true)
    (eq : a &&& mask = b &&& mask) : signedMap f a = signedMap f b := by
  apply congrArg canonical
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin 64 := ⟨i, hi⟩
  change (rowMap f a).getLsbD r.val = (rowMap f b).getLsbD r.val
  rw [rowMap_read, rowMap_read]
  simpa only [BitVec.getLsbD_and, covers, Bool.and_true] using
    congrArg (fun w : W => w.getLsbD (f r).val) eq

theorem signedMap_zero (f : Fin 64 → Fin 64) : signedMap f 0 = 0 := by
  have h : rowMap f 0 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact (rowMap_read f 0 ⟨i,hi⟩).trans (by simp)
  rw [signedMap, h]
  rfl

theorem signedMap_ones (f : Fin 64 → Fin 64) : signedMap f (~~~0) = 0 := by
  have h : rowMap f (~~~0) = ~~~(0 : W) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (rowMap f (~~~0)).getLsbD i = (~~~(0 : W)).getLsbD (f ⟨i,hi⟩).val from
      rowMap_read f _ ⟨i,hi⟩]
    have zero (j : Nat) : (0 : W).getLsbD j = false := by simp
    simp only [BitVec.getLsbD_not, hi, (f ⟨i,hi⟩).isLt, decide_true, zero]
  rw [signedMap, h, canonical_not]
  rfl

def maskedCut (mask : W) (patterns : List W) (bound budget : Nat) (s : List W) : Bool :=
  s.all (fun w => patterns.contains (w &&& mask)) &&
    (decide (budget < bound) || (decide (budget ≤ bound) &&
      s.any (fun w => (w &&& mask) == 0 || (w &&& mask) == mask)))

theorem maskedCut_sound (f : Fin 64 → Fin 64) (mask : W) (patterns base raw : List W)
    (g : W) (bound budget : Nat) (s : List W)
    (covers : ∀ i, mask.getLsbD (f i).val = true)
    (pats : patterns = base.map (· &&& mask))
    (stock : ∀ w ∈ base, signedMap f w = 0 ∨ signedMap f w ∈ raw)
    (nz : signedMap f g ≠ 0) (low : signedLower (signedMap f g) raw bound)
    {k : Nat} (le : k ≤ budget) (run : Cone g k s.toFinset) :
    maskedCut mask patterns bound budget s = false := by
  by_contra! bad
  have both := Bool.and_eq_true_iff.mp (show maskedCut mask patterns bound budget s = true by simpa using bad)
  have yes : cofactorReject f raw bound budget s = true := by
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply List.all_eq_true.mpr
      intro y hy
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
      have h := List.all_eq_true.mp both.1 w hw
      have mem : w &&& mask ∈ base.map (· &&& mask) := by simpa [pats] using h
      obtain ⟨v, hv, eq⟩ := List.mem_map.mp mem
      rw [← signedMap_eq_of_mask f mask v w covers eq]
      simpa [List.contains_eq_mem] using stock v hv
    · rcases Bool.or_eq_true_iff.mp both.2 with small | tight
      · exact Bool.or_eq_true_iff.mpr (Or.inl small)
      obtain ⟨h, hz⟩ := Bool.and_eq_true_iff.mp tight
      obtain ⟨w, hw, value⟩ := List.any_eq_true.mp hz
      have z : signedMap f w = 0 := by
        rcases Bool.or_eq_true_iff.mp value with lo | hi
        · have eq : w &&& mask = (0 : W) &&& mask := by simpa using lo
          exact (signedMap_eq_of_mask f mask w 0 covers eq).trans (signedMap_zero f)
        · have eq : w &&& mask = (~~~(0 : W)) &&& mask := by
            change w &&& mask = BitVec.allOnes 64 &&& mask
            rw [BitVec.allOnes_and]
            simpa using hi
          exact (signedMap_eq_of_mask f mask w _ covers eq).trans (signedMap_ones f)
      apply Bool.or_eq_true_iff.mpr
      refine Or.inr (Bool.and_eq_true_iff.mpr ⟨h, ?_⟩)
      simpa [List.contains_eq_mem] using (List.mem_map.mpr ⟨w,hw,z⟩ : (0 : W) ∈ s.map (signedMap f))
  rw [cofactorReject_sound f g raw bound budget nz low s le run] at yes
  contradiction


-- Keep the executable mask and its correctness argument together. A lookup may
-- choose any certificate in this family; each choice has an independent proof.
structure CutCertificate (g : W) where
  mask : W
  patterns : List W
  bound : Nat
  sound : ∀ budget s {k}, k ≤ budget → Cone g k s.toFinset →
    maskedCut mask patterns bound budget s = false

def makeCutCertificate (g goal mask : W) (rows : Nat) (dimension bound : Nat)
    (base patterns raw : List W) (nz : goal ≠ 0) (low : signedLower goal raw bound)
    (f : Fin 64 → Fin 64 := fun r => ⟨(rows >>> (6 * (r.val % 2^dimension))) % 64,
      Nat.mod_lt _ (by decide)⟩)
    (covers : ∀ r, mask.getLsbD (f r).val = true)
    (pats : patterns = base.map (· &&& mask))
    (stock : base.all (fun w => signedMap f w == 0 || raw.contains (signedMap f w)) = true)
    (goalEq : signedMap f g = goal) : CutCertificate g where
  mask := mask
  patterns := patterns
  bound := bound
  sound budget s _ le run := by
    apply maskedCut_sound f mask patterns base raw g bound budget s covers pats _ _ _ le run
    · intro w h
      simpa [List.contains_eq_mem] using List.all_eq_true.mp stock w h
    · simpa only [goalEq] using nz
    · rw [goalEq]
      exact @low

-- A certified lower bound can discharge a frontier state without enumerating its successors.
theorem closed_excludes_or (g : W) (hg : g ≠ 0) (negative : List ℕ)
    (neg : ∀ r ∈ negative, r < 64 ∧ g.getLsbD r = false)
    (words : ℕ → ℕ → List W) (count : ℕ → ℕ) (lookup : ℕ → List W → ℕ × ℕ)
    (sym : ℕ → List Switch) (valid : ∀ j, ∀ op ∈ sym j, op.Valid)
    (fix : ∀ j, reindex (sym j) g = g) (cap : ℕ)
    (nd : ∀ k ≤ cap, ∀ i < count k, (words k i).Nodup)
    (checks : ∀ k ≤ cap, ∀ i < count k, closed g negative words count lookup sym k i = true ∨
      (∀ d ≤ k, ¬ Cone g d (words k i).toFinset)) :
    ∀ k ≤ cap, ∀ i < count k, ∀ d ≤ k, ¬ Cone g d (words k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro hk i hi d hd run
    rcases checks 0 hk i hi with check | reject
    case inr => exact reject d hd run
    have de : d = 0 := by omega
    subst d
    have terminal {t : Finset W} (p : Cone g 0 t) : g ∈ t := by cases p; simp
    have mem := List.mem_toFinset.mp (terminal run)
    simp [closed,mem] at check
  | succ k ih =>
    intro hk i hi d hd run
    rcases checks (k+1) hk i hi with check | reject
    case inr => exact reject d hd run
    obtain ⟨absent,reject⟩ := Bool.and_eq_true_iff.mp check
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


namespace SignedFrontier

-- Supplying intermediate wires costs at most the number of gates used to
-- compute them. This permits a projected branch to retain non-input wires.
theorem signedLower_after_prefix (g : W) (raw init supplied : List W) (n : Nat)
    (low : signedLower g raw n) (start : available init ⊆ insert 0 raw.toFinset)
    (p : List (Nat × Nat)) (stock : insert 0 supplied.toFinset ⊆ available (p.foldl add init)) :
    signedLower g supplied (n - p.length) := by
  intro k s run hs
  obtain ⟨m,t,hm,ht,exec⟩ := extract p init g k s run (hs.trans stock)
  have lb := low exec (ht.trans start)
  omega

theorem rowMap_zero (f : Fin 64 → Fin 64) : rowMap f 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact (rowMap_read f 0 ⟨i,hi⟩).trans (by simp)

theorem rowMap_not (f : Fin 64 → Fin 64) (a : W) : rowMap f (~~~a) = ~~~(rowMap f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have atRow := fun w => rowMap_read f w ⟨i,hi⟩
  simp only [atRow,BitVec.getLsbD_not,hi,(f ⟨i,hi⟩).isLt,decide_true,Bool.true_and]

theorem rowMap_and (f : Fin 64 → Fin 64) (a b : W) :
    rowMap f (a &&& b) = rowMap f a &&& rowMap f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have atRow := fun w => rowMap_read f w ⟨i,hi⟩
  simp only [atRow,BitVec.getLsbD_and]

theorem rowMap_getD (f : Fin 64 → Fin 64) (ws : List W) (j : Nat) :
    rowMap f (ws.getD j 0) = (ws.map (rowMap f)).getD j 0 := by
  by_cases h : j < ws.length
  · rw [List.getD_eq_getElem _ _ h,List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp; omega)]
    exact rowMap_zero f

theorem rowMap_add (f : Fin 64 → Fin 64) (ws : List W) (gate : Nat × Nat) :
    (add ws gate).map (rowMap f) = add (ws.map (rowMap f)) gate := by
  simp only [add,List.map_append,List.map_cons,List.map_nil,rowMap_not,rowMap_and,rowMap_getD]

theorem rowMap_prefix (f : Fin 64 → Fin 64) (ws : List W) (p : List (Nat × Nat)) :
    (p.foldl add ws).map (rowMap f) = p.foldl add (ws.map (rowMap f)) := by
  induction p generalizing ws with
  | nil => rfl
  | cons gate p ih => simp only [List.foldl_cons,ih,rowMap_add]

-- The concrete prefix executes on the original physical inputs. Its wires
-- restrict to the same program on the projected inputs, even with high pins.
def prefixCutCertificate (g goal mask : W) (f : Fin 64 → Fin 64) (base raw : List W)
    (n : Nat) (low : signedLower goal raw n) (nz : goal ≠ 0)
    (cover : ∀ i, mask.getLsbD (f i).val = true) (goalEq : signedMap f g = goal)
    (start : available (base.map (rowMap f)) ⊆ insert 0 raw.toFinset)
    (p : List (Nat × Nat)) : CutCertificate g :=
  let ws := p.foldl add base
  let supplied := ws.map (signedMap f)
  { mask := mask
    patterns := ws.map (· &&& mask)
    bound := n - p.length
    sound := by
      intro budget s k le run
      apply maskedCut_sound f mask _ ws supplied g _ budget s cover rfl _ _ _ le run
      · intro w hw
        exact Or.inr (List.mem_map_of_mem hw)
      · rw [goalEq]
        exact nz
      · rw [goalEq]
        apply signedLower_after_prefix goal raw _ supplied n (@low) start p
        rw [←rowMap_prefix]
        simp only [available,List.map_map]
        rfl }

end SignedFrontier

namespace SignedFrontier

-- Count distinct live original signals that the row restriction makes constant.
def zeroCount (f : W → W) (s : Finset W) : Nat := (s.filter fun w => f w = 0).card

theorem zeroCount_insert (f : W → W) (w : W) (s : Finset W) :
    zeroCount f (insert w s) ≤ zeroCount f s + (if f w = 0 then 1 else 0) := by
  by_cases h : f w = 0
  · simpa [zeroCount,Finset.filter_insert,h] using
      Finset.card_insert_le w (s.filter fun x => f x = 0)
  · simp only [zeroCount,Finset.filter_insert,if_neg h,Nat.add_zero,le_refl]

theorem zeroCount_erase (f : W → W) (s : Finset W) (w : W) (mem : w ∈ s) :
    zeroCount f (s.erase w) + (if f w = 0 then 1 else 0) = zeroCount f s := by
  have eq : (s.erase w).filter (fun x => f x = 0) = (s.filter fun x => f x = 0).erase w := by
    ext x
    simp [and_assoc,and_comm,and_left_comm]
  unfold zeroCount
  rw [eq]
  by_cases h : f w = 0
  · have hw : w ∈ s.filter (fun x => f x = 0) := by simp [mem,h]
    have pos := Finset.card_pos.mpr ⟨w,hw⟩
    simp only [h,ite_true,Finset.card_erase_of_mem hw]
    omega
  · have hw : w ∉ s.filter (fun x => f x = 0) := fun inside => h (Finset.mem_filter.mp inside).2
    simp only [if_neg h,Nat.add_zero,Finset.erase_eq_of_notMem hw]

-- Skipping a projected gate can introduce at most one extra constant in the
-- backward cone. Keeping a gate requires both of its operands to be nonconstant.
theorem Cone.project_count {g : W} {k : Nat} {s : Finset W} (h : Cone g k s)
    (f : W → W) (hom : ∀ a b w, w ∈ choices a b → f w ∈ choices (f a) (f b))
    (nz : f g ≠ 0) : ∃ j t, j + zeroCount f s ≤ k ∧ Cone (f g) j t ∧ t ⊆ s.image f := by
  induction h with
  | done => exact ⟨0,{f g},by simp only [zeroCount,Finset.filter_singleton,if_neg nz,Finset.card_empty,Nat.zero_add,le_refl],Cone.done,by simp⟩
  | @step k needed a b w rest want a0 b0 ab aw bw form ih =>
    obtain ⟨j,t,le,run,ht⟩ := ih
    let old := insert a (insert b (needed.erase w))
    have aa : f a ∈ old.image f := Finset.mem_image_of_mem _ (by simp [old])
    have bb : f b ∈ old.image f := Finset.mem_image_of_mem _ (by simp [old])
    have former (x : W) (hx : x ∈ needed) (ne : x ≠ w) : f x ∈ old.image f :=
      Finset.mem_image_of_mem _ (by simp [old,hx,ne])
    change ∃ j t, j + zeroCount f old ≤ k+1 ∧ Cone (f g) j t ∧ t ⊆ old.image f
    have ia := zeroCount_insert f a (insert b (needed.erase w))
    have ib := zeroCount_insert f b (needed.erase w)
    have ew := zeroCount_erase f needed w want
    have price : zeroCount f old ≤ zeroCount f needed + 1 := by
      change zeroCount f (insert a (insert b (needed.erase w))) ≤ _
      by_cases ha : f a = 0 <;> by_cases hb : f b = 0
      · have op := hom a b w form
        have hw : f w = 0 := by simpa [choices,ha,hb] using op
        simp only [ha,hb,hw,ite_true] at ia ib ew
        omega
      all_goals split_ifs at ia ib ew <;> omega
    by_cases sub : t ⊆ old.image f
    · exact ⟨j,t,by omega,run,sub⟩
    · have special (x : W) (hx : x ∈ t) : x = f w ∨ x ∈ old.image f := by
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp (ht hx)
        by_cases eq : z = w
        · exact Or.inl (congrArg f eq)
        · exact Or.inr (former z hz eq)
      have used : f w ∈ t := by
        by_contra bad
        exact sub (fun x hx => (special x hx).resolve_left (fun e => bad (e ▸ hx)))
      have fresh : f w ∉ old.image f := fun inside =>
        sub (fun x hx => (special x hx).elim (fun e => e ▸ inside) id)
      have nzW : f w ≠ 0 := fun e => run.noZero nz (e ▸ used)
      have op := hom a b w form
      have good : ¬(f a = 0 ∨ f b = 0 ∨ f a = f b) := by
        intro bad
        rcases constants (f a) (f b) bad _ op with e | e | e
        · exact nzW e
        · exact fresh (e ▸ aa)
        · exact fresh (e ▸ bb)
      let next := insert (f a) (insert (f b) (t.erase (f w)))
      have step : Cone (f g) (j+1) next := Cone.step run used (fun e => good (Or.inl e))
        (fun e => good (Or.inr (Or.inl e))) (fun e => good (Or.inr (Or.inr e)))
        (fun e => fresh (e ▸ aa)) (fun e => fresh (e ▸ bb)) op
      have ha : f a ≠ 0 := fun e => good (Or.inl e)
      have hb : f b ≠ 0 := fun e => good (Or.inr (Or.inl e))
      have cost : zeroCount f old ≤ zeroCount f needed := by
        change zeroCount f (insert a (insert b (needed.erase w))) ≤ _
        simp only [ha,hb,ite_false,Nat.add_zero] at ia ib
        split_ifs at ew <;> omega
      refine ⟨j+1,next,by omega,step,?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact aa
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact bb
      have z := Finset.mem_erase.mp hx
      exact (special x z.2).resolve_left z.1

end SignedFrontier

namespace SignedFrontier

def countedCut (mask : W) (patterns : List W) (bound budget : Nat) (s : List W) : Bool :=
  s.all (fun w => patterns.contains (w &&& mask)) &&
    decide (budget < bound + (s.filter (fun w => (w &&& mask) == 0 || (w &&& mask) == mask)).toFinset.card)

structure CountCertificate (g : W) where
  mask : W
  patterns : List W
  bound : Nat
  sound : ∀ budget s {k}, k ≤ budget → Cone g k s.toFinset →
    countedCut mask patterns bound budget s = false

theorem countedCut_sound (f : Fin 64 → Fin 64) (mask : W) (base raw : List W)
    (g : W) (bound budget : Nat) (s : List W)
    (cover : ∀ i, mask.getLsbD (f i).val = true)
    (stock : ∀ w ∈ base, signedMap f w ∈ raw)
    (nz : signedMap f g ≠ 0) (low : signedLower (signedMap f g) raw bound)
    {k : Nat} (small : k ≤ budget) (run : Cone g k s.toFinset) :
    countedCut mask (base.map (· &&& mask)) bound budget s = false := by
  by_contra! fail
  have yes : countedCut mask (base.map (· &&& mask)) bound budget s = true := by simpa using fail
  obtain ⟨pattern, cutoff⟩ := Bool.and_eq_true_iff.mp yes
  have sub : s.toFinset.image (signedMap f) ⊆ insert 0 raw.toFinset := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    have test := List.all_eq_true.mp pattern v (List.mem_toFinset.mp hv)
    obtain ⟨u,hu,eq⟩ := List.mem_map.mp (List.contains_iff_mem.mp test)
    have close := signedMap_eq_of_mask f mask u v cover eq
    exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (close ▸ stock u hu))
  have constant : (s.filter (fun w => (w &&& mask) == 0 || (w &&& mask) == mask)).toFinset ⊆
      s.toFinset.filter (fun w => signedMap f w = 0) := by
    intro w hw
    obtain ⟨inside,bit⟩ := List.mem_filter.mp (List.mem_toFinset.mp hw)
    refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr inside,?_⟩
    rcases Bool.or_eq_true_iff.mp bit with a | b
    · have eq : w &&& mask = (0 : W) &&& mask := by simpa using a
      exact (signedMap_eq_of_mask f mask w 0 cover eq).trans (signedMap_zero f)
    · have eq : w &&& mask = (~~~(0 : W)) &&& mask := by
        change w &&& mask = BitVec.allOnes 64 &&& mask
        rw [BitVec.allOnes_and]
        exact beq_iff_eq.mp b
      exact (signedMap_eq_of_mask f mask w _ cover eq).trans (signedMap_ones f)
  obtain ⟨j,t,price,exec,inside⟩ := run.project_count (signedMap f) (signedMap_choice f) nz
  have lb := low exec (inside.trans sub)
  have cc := Finset.card_le_card constant
  unfold zeroCount at price
  have threshold := of_decide_eq_true cutoff
  omega

def countedPrefixCertificate (g goal mask : W) (f : Fin 64 → Fin 64) (base raw : List W)
    (n : Nat) (low : signedLower goal raw n) (nz : goal ≠ 0)
    (cover : ∀ i, mask.getLsbD (f i).val = true) (goalEq : signedMap f g = goal)
    (start : available (base.map (rowMap f)) ⊆ insert 0 raw.toFinset)
    (p : List (Nat × Nat)) : CountCertificate g :=
  let ws := p.foldl add base
  let supplied := ws.map (signedMap f)
  { mask := mask
    patterns := ws.map (· &&& mask)
    bound := n - p.length
    sound := by
      intro budget s k le run
      apply countedCut_sound f mask ws supplied g _ budget s cover _ _ _ le run
      · intro w hw
        exact List.mem_map_of_mem hw
      · rw [goalEq]
        exact nz
      · rw [goalEq]
        apply signedLower_after_prefix goal raw _ supplied n (@low) start p
        rw [←rowMap_prefix]
        simp only [available,List.map_map]
        rfl }

end SignedFrontier

namespace SignedFrontier.SmallCert.Minor0

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0x8eee8eee8eee8eee
def negative : List Nat := [0, 4, 8, 12, 13, 14]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,9,13),(0xff00ff00ff00ff00,5,13)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xff00ff00ff00ff00f0f0f0f0f0f0f0f0f000f000f000f000ccccccccccccccccaaaaaaaaaaaaaaaa00f000f000f000f00000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x43 else 0
  | 3 => if page < 1 then 0x11cbc3 else 0
  | 4 => if page < 1 then 0xf else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xf else 0
  | 3 => if page < 1 then 0xf else 0
  | 4 => if page < 1 then 0x9 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 1
  | 3 => 3
  | 4 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 8
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 3)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 4)

def bucketCount : ℕ → ℕ
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 2
  | 3 => 6
  | 4 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 3
  | 4 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 4
  | 4 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x20 else 0
  | 4 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x4985 else 0
  | 4 => if page < 1 then 0x0 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let h := key xs
  let b := bucketCount k
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 4,slot % 4)

def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s23]
  | 2 => [s01]
  | 3 => [s01, s23]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s23_ok, s01_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 4 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 1 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 3 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 3 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 1 0 = true :=
  chunk4x0
theorem verified : ∀ k ≤ 4, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 5 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 4
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    4 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor0

namespace SignedFrontier.SmallCert.Minor1

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0xfee8fee8fee8fee8
def negative : List Nat := [0, 1, 2, 4, 8]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,2,3),(0xcccccccccccccccc,1,3),(0xf0f0f0f0f0f0f0f0,1,5),(0xff00ff00ff00ff00,1,9)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xfff0fff0fff0fff0ffccffccffccffccffc0ffc0ffc0ffc0ffaaffaaffaaffaaffa8ffa8ffa8ffa8ff88ff88ff88ff88ff80ff80ff80ff80ff08ff08ff08ff08ff00ff00ff00ff00fefefefefefefefefcfcfcfcfcfcfcfcfcecfcecfcecfcecfcccfcccfcccfcccfafafafafafafafafaf0faf0faf0faf0faaafaaafaaafaaaf8f8f8f8f8f8f8f8f0f0f0f0f0f0f0f0f000f000f000f000eeeeeeeeeeeeeeeeeaeaeaeaeaeaeaeadcccdcccdcccdcccccccccccccccccccaaeeaaeeaaeeaaeeaaaaaaaaaaaaaaaaaaa8aaa8aaa8aaa8aa00aa00aa00aa00a8a8a8a8a8a8a8a88aaa8aaa8aaa8aaa88aa88aa88aa88aa8888888888888888808080808080808055005500550055002aaa2aaa2aaa2aaa0ff00ff00ff00ff00ccc0ccc0ccc0ccc0aaa0aaa0aaa0aaa0a0a0a0a0a0a0a0a02aa02aa02aa02aa00fe00fe00fe00fe00ee00ee00ee00ee00aa00aa00aa00aa0088008800880088000a000a000a000a0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x2a898b2022c854b2052c5d4 else 0
  | 3 => if page < 1 then 0x2cae219d9392c688202978c0b1d302770c07d1a0193b00b0a301a28c0808c0092300783a0190b00b201000a1c0027700099c002570004f80010e0002f8000a70002380006e00015c0000f else 0
  | 4 => if page < 1 then 0xae9764ed9ce7688e643ea437483e30371c3e64ec023f019f018f015f011f00ff00ef00df008f004f003f002f001f0277008e else 0
  | 5 => if page < 1 then 0x67dde3f else 0
  | 6 => if page < 1 then 0xf else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x24 else 0
  | 3 => if page < 1 then 0x2d else 0
  | 4 => if page < 1 then 0x21 else 0
  | 5 => if page < 1 then 0x13 else 0
  | 6 => if page < 1 then 0x9 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 5
  | 3 => 27
  | 4 => 25
  | 5 => 3
  | 6 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 64
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 6)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 4)

def bucketCount : ℕ → ℕ
  | 2 => 5
  | 3 => 18
  | 4 => 19
  | 5 => 8
  | 6 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 20
  | 3 => 64
  | 4 => 73
  | 5 => 38
  | 6 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 4
  | 3 => 5
  | 4 => 5
  | 5 => 4
  | 6 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 8
  | 3 => 10
  | 4 => 10
  | 5 => 7
  | 6 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x102d5 else 0
  | 3 => if page < 1 then 0x2049823884c3691e018805 else 0
  | 4 => if page < 1 then 0x460189801bc0040a2309c00 else 0
  | 5 => if page < 1 then 0xc001010 else 0
  | 6 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x600023112c1088222600204d315000702f000030 else 0
  | 3 => if page < 1 then 0xc42c3c8600481c224280082828426058070a06d051300940006823000287644003a541000002306d18c555580000320002e5d2000001c42a5a13419098de0501d270000a8311002d100101182f21c6e4 else 0
  | 4 => if page < 2 then (if page < 1 then 0xac64490092002b000220182355200098312084e00028280a64a1c5000281341339c81118a86280004d8000814940c427020000010001e0b9a52103052840070568b0588000e10000034461626e0211a3 else 0xa031300304b005159800) else 0
  | 5 => if page < 1 then 0x50000b4040980034d240020b40003ac0002801282000000240004709800010caa2 else 0
  | 6 => if page < 1 then 0x0 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let h := key xs
  let b := bucketCount k
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 32,slot % 32)

def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s13 : Switch := ⟨6,0xcc00cc00cc00cc,0x3300330033003300⟩
theorem s13_ok : s13.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel
def s03 : Switch := ⟨7,0xaa00aa00aa00aa,0x5500550055005500⟩
theorem s03_ok : s03.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s23]
  | 2 => [s12]
  | 3 => [s12, s13]
  | 4 => [s13, s12]
  | 5 => [s13]
  | 6 => [s01]
  | 7 => [s01, s23]
  | 8 => [s01, s02]
  | 9 => [s01, s02, s03]
  | 10 => [s01, s03, s02]
  | 11 => [s01, s03]
  | 12 => [s02, s01]
  | 13 => [s02, s01, s13]
  | 14 => [s02]
  | 15 => [s02, s03]
  | 16 => [s02, s13]
  | 17 => [s02, s13, s01]
  | 18 => [s03, s01, s12]
  | 19 => [s03, s01]
  | 20 => [s03, s02]
  | 21 => [s03]
  | 22 => [s03, s12, s01]
  | 23 => [s03, s12]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s23_ok, s12_ok, s13_ok, s01_ok, s02_ok, s03_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 6 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 5 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 27 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 27 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 25 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 25 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 3 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 3 0 = true :=
  chunk5x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 1 0 = true :=
  chunk6x0
theorem verified : ∀ k ≤ 6, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 7 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 6
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    6 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor1

namespace SignedFrontier.SmallCert.Minor2

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0xfeeafeeafeeafeea
def negative : List Nat := [0, 2, 4, 8]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,4,6),(0xf0f0f0f0f0f0f0f0,2,6),(0xff00ff00ff00ff00,2,10)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffaaffaaffaaffaaff00ff00ff00ff00fafafafafafafafaf0f0f0f0f0f0f0f0ccccccccccccccccaaaaaaaaaaaaaaaa44444444444444440000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x1eb else 0
  | 3 => if page < 1 then 0x3b9d else 0
  | 4 => if page < 1 then 0xf else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x12 else 0
  | 3 => if page < 1 then 0xf else 0
  | 4 => if page < 1 then 0x9 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 8
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 3)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 4)

def bucketCount : ℕ → ℕ
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 3
  | 3 => 8
  | 4 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 2
  | 3 => 4
  | 4 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x8 else 0
  | 4 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x20 else 0
  | 3 => if page < 1 then 0x903c0082 else 0
  | 4 => if page < 1 then 0x0 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let h := key xs
  let b := bucketCount k
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 8,slot % 8)

def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s13 : Switch := ⟨6,0xcc00cc00cc00cc,0x3300330033003300⟩
theorem s13_ok : s13.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s23]
  | 2 => [s12]
  | 3 => [s12, s13]
  | 4 => [s13, s12]
  | 5 => [s13]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s23_ok, s12_ok, s13_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 4 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 1 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 2 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 2 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 1 0 = true :=
  chunk4x0
theorem verified : ∀ k ≤ 4, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 5 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 4
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    4 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor2

namespace SignedFrontier.SmallCert.Minor3

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0x80fe80fe80fe80fe
def negative : List Nat := [0, 8, 9, 10, 11, 12, 13, 14]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,1,9)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xffaaffaaffaaffaaff00ff00ff00ff00f3f0f3f0f3f0f3f0f2f2f2f2f2f2f2f2f0faf0faf0faf0faf0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeccccccccccccccccaaaaaaaaaaaaaaaaaa0aaa0aaa0aaa0aaa00aa00aa00aa008a8a8a8a8a8a8a8a88aa88aa88aa88aa88888888888888880f000f000f000f000a0a0a0a0a0a0a0a00aa00aa00aa00aa0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x59301f60eb06d82380dc05e else 0
  | 4 => if page < 1 then 0x47d7e7f278fc5e1f else 0
  | 5 => if page < 1 then 0xf else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x1b else 0
  | 4 => if page < 1 then 0x13 else 0
  | 5 => if page < 1 then 0x9 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 7
  | 4 => 7
  | 5 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 32
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 5)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 4)

def bucketCount : ℕ → ℕ
  | 3 => 4
  | 4 => 8
  | 5 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 17
  | 4 => 38
  | 5 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 3
  | 4 => 4
  | 5 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 3 => 6
  | 4 => 6
  | 5 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x180 else 0
  | 4 => if page < 1 then 0xc001010 else 0
  | 5 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x1402112932c601540000019030 else 0
  | 4 => if page < 1 then 0x2c0022028b000b230025160029c000cc83430000100008298c0030519 else 0
  | 5 => if page < 1 then 0x0 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let h := key xs
  let b := bucketCount k
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 8,slot % 8)

def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s12]
  | 2 => [s01]
  | 3 => [s01, s02]
  | 4 => [s02, s01]
  | 5 => [s02]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s12_ok, s01_ok, s02_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 5 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 7 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 7 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 7 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 7 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 1 0 = true :=
  chunk5x0
theorem verified : ∀ k ≤ 5, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 6 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 5
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    5 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor3

namespace SignedFrontier.SmallCert.Minor4

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0x88fe88fe88fe88fe
def negative : List Nat := [0, 8, 9, 10, 12, 13, 14]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f0,0,4),(0xff00ff00ff00ff00,1,9)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xfff0fff0fff0fff0ff00ff00ff00ff00fafafafafafafafaf0f0f0f0f0f0f0f0dcdcdcdcdcdcdcdcccfcccfcccfcccfcccccccccccccccccaaaaaaaaaaaaaaaa303030303030303000f000f000f000f00000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x34d9 else 0
  | 3 => if page < 1 then 0xab8b2b1b else 0
  | 4 => if page < 1 then 0xf else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xf else 0
  | 3 => if page < 1 then 0x11 else 0
  | 4 => if page < 1 then 0x9 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 2
  | 3 => 4
  | 4 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 16
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 4)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 4)

def bucketCount : ℕ → ℕ
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 2 => 7
  | 3 => 11
  | 4 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 2 => 2
  | 3 => 3
  | 4 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x0 else 0
  | 3 => if page < 1 then 0x1 else 0
  | 4 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x310 else 0
  | 3 => if page < 1 then 0x4740580 else 0
  | 4 => if page < 1 then 0x0 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let h := key xs
  let b := bucketCount k
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 2,slot % 2)

def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s01]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s01_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 4 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 2 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 2 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 4 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 4 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 1 0 = true :=
  chunk4x0
theorem verified : ∀ k ≤ 4, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 5 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 4
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    4 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor4

namespace SignedFrontier.SmallCert.Minor8

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xfee8e880fee8e880
def negative : List Nat := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · refine ⟨6,7,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨5,7,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨3,7,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨3,11,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨3,19,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 2 then (if page < 1 then 0xcccc0000cccc0000ccc0ccc0ccc0ccc0cc00cc00cc00cc00c0ccc0ccc0ccc0ccc0c0eaeac0c0eaeac0c0c0c0c0c0c0c0c0c04040c0c04040c0c00000c0c00000c000c000c000c000aaeeaaeeaaeeaaeeaaaafafaaaaafafaaaaaeeeeaaaaeeeeaaaaaaaaaaaaaaaaaaaa0000aaaa0000aaa0aaa0aaa0aaa0aa00aa00aa00aa00a8a8fcfca8a8fcfca8a8a8a8a8a8a8a8a0a0aaaaa0a0aaaaa0a0a0a0a0a0a0a088aa88aa88aa88aa8888f8f88888f8f88888aaaa8888aaaa88888888888888888880888088808880808088888080888880808080808080808000800080008000555500005555000054545454545454544444444444444444330033003300330030303030303030300fff00000fff00000f000f000f000f000ccc0ccc0ccc0ccc0c0c0c0c0c0c0c0c0aaa0aaa0aaa0aaa0a0a0a0a0a0a0a0a00ff000000ff000000fc00fc00fc00fc00f000f000f000f000eeeeee00eeeeee00ccaaee00ccaaee00cc00cc00cc00cc00aaccee00aaccee00aaaaaa00aaaaaa00aa00aa00aa00aa00888888008888880000fcfc0000fcfc0000f0f00000f0f00000eeee0000eeee0000cccc0000cccc0000aaaa0000aaaa0000a8a80000a8a8000088aa000088aa0000888800008888000080800000808000000aaa00000aaa000000ee000000ee000000aa000000aa00000088000000880000000a0000000a0000000000000000 else 0xfffffff0fffffff0ffffff00ffffff00fffffcfcfffffcfcfffff0f0fffff0f0ffffccccffffccccffffc0c0ffffc0c0ffffaaaaffffaaaaffff8888ffff8888ffff00ccffff00ccffff0000ffff0000fffefffefffefffefffcfffcfffcfffcfffafffafffafffafff8fff8fff8fff8fff0fff0fff0fff0fff0f0f0fff0f0f0ffccffccffccffccffaaffaaffaaffaaff00ff00ff00ff00ff000000ff000000fefefefefefefefefeeefeeefeeefeeefcfcfefefcfcfefefcfcfcfcfcfcfcfcfcfc5454fcfc5454fcfc0000fcfc0000fcccfcccfcccfcccfafafafafafafafafaaafaaafaaafaaaf8f8f8f8f8f8f8f8f888f888f888f888f0f0fff0f0f0fff0f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f00000f0f00000f000f0f0f000f0f0f000f000f000f000eeeefefeeeeefefeeeeeeeeeeeeeeeeeeee0eee0eee0eee0eaeaeaeaeaeaeaeaeac0eac0eac0eac0ccff0000ccff0000ccfcccfcccfcccfccccceeeecccceeeecccccccccccccccccccc4444cccc4444) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 6 => if page < 3 then (if page < 1 then 0x1427e8047c508feb0ffc01ff4c3fe607fca0ff581fe7c3fcc07f960ff201fe343fd406f8a0df9417e282ff684fc809fbc0ff5c1fe403fbd07f740fea01fd083f9d07f360fe641fc583fed05f500be2817f001f8a03fd79dec547a411f4c18f8c2bd5453cd0af0e14f0193e02cfc049f808ff0117e017fc02af804ff009be0127c015f8025f003fe004fc008f800df0017e0027c002f8003f else (if page < 2 then 0xbea3f4947e828fcf51f9aa3f2d47e528fb551f62a3eb547d528fe04ff509fea137f6a5fdd4bfb697ec12fd424fdb2bf9057f5c8fe411fba23f5047f6c7fd40ffeb19fc033f3067e50cfec15fd22bf9857f18afda15fb02bf5c57eb0afd515fa82bf1857e20afc315f7c2bef057dd8afba15f722bee057db8afb615f5c2beac57d28afa215f3c2be7057cd0af9715f282be4c57c70afd713f else 0x304851dd79d43f04a517c0c547adc823e992063e33a15ed15c53ebd514faee856f43a14faec8579d3215eae8c53dd2314f946857b41314f644c579013157ae3853f04851cc12944ebba15901ba47c06491f018a47c06091f016647c04991f01223fc06d8df017637c06069f014da7c0575ff01b577c05d5df01814fc05353f01b947c06251f018547c06051f)) else 0
  | 7 => if page < 1 then 0x3048fda91fa723f5d77f028fd351fa2a3f2947e428fac51f5097f6c8fe40cfea15fd02bf5c57e40afc215f802befc57dd0afb215f502be8c57cc0af9315f202be2c57d407f8a0ffda0fe281fe428ee814f642bc8c53e428e00b5f0123e0237c034f805df00a7e0147c025f8023f0033e0057c007f8007f else 0
  | 8 => if page < 1 then 0x91f51f15f else 0
  | 9 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 6 => if page < 1 then 0x3509c27 else 0
  | 7 => if page < 1 then 0x27 else 0
  | 8 => if page < 1 then 0x19 else 0
  | 9 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 6 => 171
  | 7 => 50
  | 8 => 3
  | 9 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 128
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 7)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 5)

def bucketCount : ℕ → ℕ
  | 6 => 102
  | 7 => 67
  | 8 => 14
  | 9 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 6 => 368
  | 7 => 242
  | 8 => 48
  | 9 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 6 => 6
  | 7 => 7
  | 8 => 5
  | 9 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 6 => 15
  | 7 => 13
  | 8 => 9
  | 9 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 6 => if page < 2 then (if page < 1 then 0x60204600810701b09900109e1574cf1c00021020011830ca0c8d810ca0401c078014804004110008008b04000c241309 else 0x3b00010088303a4c721378b05050304d4c128e043040000ec809b0cc) else 0
  | 7 => if page < 2 then (if page < 1 then 0xc198aa821430206745801e0a0042c641232a980082e000003e540020414000163c381120048102004042a91c0100000040a353001e70003 else 0xc813) else 0
  | 8 => if page < 1 then 0x22180791003e31c0b else 0
  | 9 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 6 => if page < 6 then (if page < 3 then (if page < 1 then 0x98972e00fa5bc36326049253003283000000028c95400863c000255e2e00000073b0d03426387ba26016c000000000fcf01658d185d00000244c4f604000596a900488063789438000501f7e309c026072f193c08dd227c90e88703cfcf8ec448be66b4466e1d0b201740050312c01e8e0bc202015034469 else (if page < 2 then 0x7f068600e4220803d960001b8f00003e1c8a211c4000098000001ec180000000f0c00002400241850088d401037d00000168dad121b0939a4840b18029b940019ee411857115150a41b3da86410402a8030bc4610000000008b073006e7930cb3836abb32a80003ab09e3e00014010000000000023de3820 else 0x38100000fc0150054620002404bb676bb400029cc0d006f06ac018000e08a10cc50a840220000013621f5e000000012cf00002d2200003369b5e4b0000006662a9f52c209b53ba46214e0000014689b904f2286904c0c00000009a553f813402f803c0236050861d1e62d80000000326c00004e027890000)) else (if page < 4 then 0x1062c02398535a531070f0e8c1b982aba86640001d80993909b400052ec551c60000002d0250360a3800000002db52a00000100318d8d969eb03f008c42a0885c0076902b4000000011825900cb6a49e0cdc15114e0274050221e00000248006005218526cac6543c6fb512613c04d197730ab2d2404d00 else (if page < 5 then 0x21305609b404d1c00010026a4232049e000f68d1897881e3254842009ae042050bc0000198139845c212a5b88300000000000294900006c2168fd100a6b84c6e2cf339ba3010c30100078c5e00f920b419b335ac062c24c032421f06a200e4094da660624f264054027913168224f16039832140050048bc else 0x68420001430030027420002a9e548107064aa6500281f9f007002018ac0072c2d36aa8c28120011478000000000001020235e34dca33f1480000080076c206220c03fda993326f1dc046802220dc31a2e800000001ac00000000))) else 0
  | 7 => if page < 4 then (if page < 2 then (if page < 1 then 0x5002e32324792b603c19ed36064ed4821e58f2a3c05af2836d8402ea775001099b4062130078816c0c0218012005404d7240cb060423d987db2686410206e4379b8813e19d012696c00002247600a010002a0322c91502200012800000002c04a060000000225800 else 0x60154112040000005a12a014805843400d00a8424f398010d6092908606e3cc08880586a240421301c488930184184a182c370987c4366623f7987805a05c24700751c485d051e08433031410f80000362120089854080019cc0026700001ed08126ce0582c07088) else (if page < 3 then 0x8400f8db0c000290016800163300000000000000000000000e9f0005e080000000004d69d456bd6cc2202b066027503a868060809c03a32c6522d000147800025d00000000b96184ee00005074002504018fc0000c015e6ac6138288f00019d0c801415608c00000 else 0x2e41000ac0243221988058030384b442020f301a50935d646506a4cc00c7002e08300b809408000001180000421050108174f0000000f089c18000b13783a0c5e0213800012e0fc1e5b6080000000000769)) else 0
  | 8 => if page < 1 then 0xe086661f3308d7ab0169a27a1e008880000804ca121284225100034c196618104c179400c980580400219002a590000000004f18000 else 0
  | 9 => if page < 1 then 0x0 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let h := key xs
  let b := bucketCount k
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 128,slot % 128)

def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel
def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s24 : Switch := ⟨12,0xf0f00000f0f0,0xf0f00000f0f0000⟩
theorem s24_ok : s24.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s13 : Switch := ⟨6,0xcc00cc00cc00cc,0x3300330033003300⟩
theorem s13_ok : s13.Valid := by unfold Switch.Valid; decide +kernel
def s14 : Switch := ⟨14,0xcccc0000cccc,0x3333000033330000⟩
theorem s14_ok : s14.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel
def s03 : Switch := ⟨7,0xaa00aa00aa00aa,0x5500550055005500⟩
theorem s03_ok : s03.Valid := by unfold Switch.Valid; decide +kernel
def s04 : Switch := ⟨15,0xaaaa0000aaaa,0x5555000055550000⟩
theorem s04_ok : s04.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s34]
  | 2 => [s23]
  | 3 => [s23, s24]
  | 4 => [s24, s23]
  | 5 => [s24]
  | 6 => [s12]
  | 7 => [s12, s34]
  | 8 => [s12, s13]
  | 9 => [s12, s13, s14]
  | 10 => [s12, s14, s13]
  | 11 => [s12, s14]
  | 12 => [s13, s12]
  | 13 => [s13, s12, s24]
  | 14 => [s13]
  | 15 => [s13, s14]
  | 16 => [s13, s24]
  | 17 => [s13, s24, s12]
  | 18 => [s14, s12, s23]
  | 19 => [s14, s12]
  | 20 => [s14, s13]
  | 21 => [s14]
  | 22 => [s14, s23, s12]
  | 23 => [s14, s23]
  | 24 => [s01]
  | 25 => [s01, s34]
  | 26 => [s01, s23]
  | 27 => [s01, s23, s24]
  | 28 => [s01, s24, s23]
  | 29 => [s01, s24]
  | 30 => [s01, s02]
  | 31 => [s01, s02, s34]
  | 32 => [s01, s02, s03]
  | 33 => [s01, s02, s03, s04]
  | 34 => [s01, s02, s04, s03]
  | 35 => [s01, s02, s04]
  | 36 => [s01, s03, s02]
  | 37 => [s01, s03, s02, s24]
  | 38 => [s01, s03]
  | 39 => [s01, s03, s04]
  | 40 => [s01, s03, s24]
  | 41 => [s01, s03, s24, s02]
  | 42 => [s01, s04, s02, s23]
  | 43 => [s01, s04, s02]
  | 44 => [s01, s04, s03]
  | 45 => [s01, s04]
  | 46 => [s01, s04, s23, s02]
  | 47 => [s01, s04, s23]
  | 48 => [s02, s01]
  | 49 => [s02, s01, s34]
  | 50 => [s02, s01, s13]
  | 51 => [s02, s01, s13, s14]
  | 52 => [s02, s01, s14, s13]
  | 53 => [s02, s01, s14]
  | 54 => [s02]
  | 55 => [s02, s34]
  | 56 => [s02, s03]
  | 57 => [s02, s03, s04]
  | 58 => [s02, s04, s03]
  | 59 => [s02, s04]
  | 60 => [s02, s13]
  | 61 => [s02, s13, s14]
  | 62 => [s02, s13, s01]
  | 63 => [s02, s13, s01, s04]
  | 64 => [s02, s13, s04, s01]
  | 65 => [s02, s13, s04]
  | 66 => [s02, s14, s13]
  | 67 => [s02, s14]
  | 68 => [s02, s14, s01, s03]
  | 69 => [s02, s14, s01]
  | 70 => [s02, s14, s03]
  | 71 => [s02, s14, s03, s01]
  | 72 => [s03, s01, s12]
  | 73 => [s03, s01, s12, s24]
  | 74 => [s03, s01]
  | 75 => [s03, s01, s14]
  | 76 => [s03, s01, s24]
  | 77 => [s03, s01, s24, s12]
  | 78 => [s03, s02]
  | 79 => [s03, s02, s24]
  | 80 => [s03]
  | 81 => [s03, s04]
  | 82 => [s03, s24]
  | 83 => [s03, s24, s02]
  | 84 => [s03, s12, s01]
  | 85 => [s03, s12, s01, s14]
  | 86 => [s03, s12]
  | 87 => [s03, s12, s04]
  | 88 => [s03, s12, s14]
  | 89 => [s03, s12, s14, s01]
  | 90 => [s03, s14, s02, s12]
  | 91 => [s03, s14, s02]
  | 92 => [s03, s14, s12]
  | 93 => [s03, s14, s12, s02]
  | 94 => [s03, s14]
  | 95 => [s03, s14, s01]
  | 96 => [s04, s01, s12, s23]
  | 97 => [s04, s01, s12]
  | 98 => [s04, s01, s13]
  | 99 => [s04, s01]
  | 100 => [s04, s01, s23, s12]
  | 101 => [s04, s01, s23]
  | 102 => [s04, s02, s23]
  | 103 => [s04, s02]
  | 104 => [s04, s03]
  | 105 => [s04]
  | 106 => [s04, s23, s02]
  | 107 => [s04, s23]
  | 108 => [s04, s12, s01, s13]
  | 109 => [s04, s12, s01]
  | 110 => [s04, s12, s03]
  | 111 => [s04, s12]
  | 112 => [s04, s12, s13, s01]
  | 113 => [s04, s12, s13]
  | 114 => [s04, s13, s02]
  | 115 => [s04, s13, s02, s12]
  | 116 => [s04, s13, s12, s02]
  | 117 => [s04, s13, s12]
  | 118 => [s04, s13, s01]
  | 119 => [s04, s13]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s34_ok, s23_ok, s24_ok, s12_ok, s13_ok, s14_ok, s01_ok, s02_ok, s03_ok, s04_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def pinBase : List W := [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff,0xffffffff]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut20 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor1.target 0x55555555
    (fun r => ⟨(0x210620a30e41251661a71e >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut21 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor1.target 0x33333333
    (fun r => ⟨(0x110520930d41151561971d >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut22 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor1.target 0xf0f0f0f
    (fun r => ⟨(0x108320928b41149361969b >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut23 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor1.target 0xff00ff
    (fun r => ⟨(0x1083105187411493515597 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut24 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor1.target 0xffff
    (fun r => ⟨(0x108310518720928b30d38f >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut41 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor1.target 0xffff0000
    (fun r => ⟨(0x7de75c6da6585d65544d2450 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut42 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor1.target 0xff00ff00
    (fun r => ⟨(0x7de75c6da6583ce34c2ca248 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut43 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor1.target 0xf0f0f0f0
    (fun r => ⟨(0x7de75c5d65543ce34c1c6144 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut44 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor1.target 0xcccccccc
    (fun r => ⟨(0x7de6da5d64d23ce2ca1c60c2 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut45 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor1.target 0xaaaaaaaa
    (fun r => ⟨(0x7dd6d95d54d13cd2c91c50c1 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p
def cutFor : Nat → List (Nat × Nat) → CutCertificate target
  | 22 => cut21
  | 23 => cut22
  | 24 => cut23
  | 25 => cut24
  | 42 => cut41
  | 43 => cut42
  | 44 => cut43
  | 45 => cut44
  | 46 => cut45
  | _ => cut20

def suppliedPrefix : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | j+1, z => if z=0 then [] else ((z%256)/16,z%16) :: suppliedPrefix j (z/256)
def selectCut (code : Nat) := cutFor (code%128) (suppliedPrefix 1 (code/128))
def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 6 => if page < 3 then (if page < 1 then 0x2ab25400a802aab2a00540152295002a00580152595002a00a800a8015452a005401544aa0057345400a802b342a005400a802b3a2a0054015002a002a005401580150054005400a802a005c006400a802a005600b4016c4ab342b346530a8015002a005624c1e15002a005400a8015002a00a800a8015 else (if page < 2 then 0x233000b914a9198232e465d14a802e002a005530ad595002a0056f0a8015562a005400ac4988931345400a9a15002aac5400a802aab5400a9155002a005400a8b15802e9a2b345668a80192c2e00b800c96172c2c5858d0a9a15342a0064b0b002e002a005400a802e0032585800a962b3b2a76540154d15 else 0x15656b0a9197ab2aac5624c9a159a2b3464b0b1a159a2a685668a9a15452a7654eca96169a5556548cb9616895400b40175595005a00b6255de16005d56580174d19bc2a0056aca8015235400baacad595)) else 0
  | 7 => if page < 1 then 0x2d002a00b00000015002a000000a8015002a00600168019002a000000a8015002a00640000015002a005400c8000002a006400a80150054005400a8015002a005400a802c002a005800b0015002a005400a80150054005400a8015 else 0
  | 8 => if page < 1 then 0x0 else 0
  | 9 => if page < 1 then 0x0 else 0
  | _ => 0

def label (k i : Nat) := field cutLabels k 15 i

def checked (k i : Nat) := decide (pool k i).Nodup &&
  (if label k i = 0 then fastClosed target negative pool counts lookup steps k i
   else let c := selectCut (label k i)
        maskedCut c.mask c.patterns c.bound k (pool k i))
theorem checked_sound (k i : Nat) (h : checked k i = true) :
    closed target negative pool counts lookup steps k i = true ∨
      (∀ d ≤ k, ¬ Cone target d (pool k i).toFinset) := by
  have h' := (Bool.and_eq_true_iff.mp h).2
  change (if label k i = 0 then _ else _) = true at h'
  split at h'
  · exact Or.inl (fastClosed_sound target nonzero negative pool counts lookup steps k i h')
  · refine Or.inr (fun d hd run => ?_)
    have no := (selectCut (label k i)).sound k (pool k i) hd run
    change maskedCut _ _ _ _ _ = true at h'
    rw [no] at h'
    contradiction

theorem root : pool 9 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x112 : span (checked 6) 59 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 171 0 = true :=
  (@span_join (checked 6) 112 0 59 chunk6x0 chunk6x112)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 50 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 50 0 = true :=
  chunk7x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x0 : span (checked 8) 3 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer8 : span (checked 8) 3 0 = true :=
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
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer7 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer8 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer9 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 10 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes_or target nonzero negative neg pool counts lookup steps valid fix 9
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => checked_sound k i (verified k hk i hi))
    9 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor8


namespace SignedFrontier.SmallCert.Sub12x0

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0]
def target : W := 0xe8e8e8e8e8e8e8e8
def negative : List Nat := [0, 1, 2, 4]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl
  · refine ⟨2,3,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,3,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xf0f0f0f0f0f0f0f0ccccccccccccccccaaaaaaaaaaaaaaaa0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x7 else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x7 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 3 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 4
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 2)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 3)

def bucketCount : ℕ → ℕ
  | 3 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 3 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 3 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 3 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 3 => if page < 1 then 0x0 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let h := key xs
  let b := bucketCount k
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 8,slot % 8)

def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s12]
  | 2 => [s01]
  | 3 => [s01, s02]
  | 4 => [s02, s01]
  | 5 => [s02]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s12_ok, s01_ok, s02_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 3 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 1 0 = true :=
  chunk3x0
theorem verified : ∀ k ≤ 3, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 4 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 3
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    3 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Sub12x0

namespace SignedFrontier.SmallCert.Minor12

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0x80e8fefe80e8fefe
def negative : List Nat := [0, 8, 16, 17, 18, 20, 24, 25, 26, 27, 28, 29, 30]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · refine ⟨0,1,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨0,2,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨0,4,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨19,27,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,17,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 4 then (if page < 2 then (if page < 1 then 0x10101010101010100f0f00000f0f00000f000f000f000f000e0e0e0e0e0e0e0e0e0e00000e0e00000e000e000e000e000c0c0c0c0c0c0c0c0b0b00000b0b00000b000b000b000b000a0a0a0a0a0a0a0a0a0a00000a0a00000a000a000a000a00080808080808080808080000080800000800080008000800070700000707000007000700070007000303000003030000030003000300030002ff020202ff02020202020202020202020200000202000002000200020002000101000001010000010001000100010000ff000000ff000000fefefe00fefefe00fe00fe00fe00fe00fe000000fe000000ef000000ef000000eeeeee00eeeeee00ee00ee00ee00ee00ee000000ee000000eaeaea00eaeaea00ea00ea00ea00ea00ea000000ea000000ae00ae00ae00ae00aa00aa00aa00aa00a800a800a800a8008a008a008a008a00880088008800880080008000800080007f0000007f0000002a002a002a002a000e000e000e000e000a000a000a000a000800080008000800020002000200020000ff000000ff000000fefe0000fefe0000eeee0000eeee0000eaea0000eaea0000aeae0000aeae0000aaaa0000aaaa0000a8a80000a8a800008a8a00008a8a0000888800008888000080800000808000002a2a00002a2a00000e0e00000e0e00000a0a00000a0a000008080000080800000202000002020000000000000000 else 0xcccc0000cccc0000cc00cc00cc00cc00c4c4c4c4c4c4c4c4c0c0c0c0c0c0c0c0bfbf0000bfbf0000bf00bf00bf00bf00babababababababab0b0b0b0b0b0b0b0afaf0000afaf0000af00af00af00af00aeaeaeaeaeaeaeaeaeae0000aeae0000ae00ae00ae00ae00acacacacacacacacabab0000abab0000ab00ab00ab00ab00aaaaaaaaaaaaaaaaaaaa0000aaaa0000aa00aa00aa00aa00a8a8a8a8a8a8a8a8a8a80000a8a80000a800a800a800a800a2a2a2a2a2a2a2a2a0a0a0a0a0a0a0a0a0a00000a0a000008f8f00008f8f00008f008f008f008f008a8a8a8a8a8a8a8a8a8a00008a8a00008a008a008a008a0088888888888888888888000088880000880088008800880080ff808080ff80808080808080808080808000008080000080008000800080007f7f00007f7f00007f007f007f007f007f0000007f00000070707070707070705f5f00005f5f00005a5a5a5a5a5a5a5a555500005555000055005500550055005454545454545454505050505050505044444444444444443f3f00003f3f00003f003f003f003f003c3c3c3c3c3c3c3c3333000033330000330033003300330030303030303030302f2f00002f2f00002f002f002f002f002e2e2e2e2e2e2e2e2a2a2a2a2a2a2a2a2a2a00002a2a00002a002a002a002a0022222222222222221f1f00001f1f00001f001f001f001f001111000011110000) else (if page < 3 then 0xffff2a2affff2a2affff0e0effff0e0effff0a0affff0a0affff0808ffff0808ffff0202ffff0202ffff0000ffff0000fffefffefffefffefff0fff0fff0fff0ffeeffeeffeeffeeffeaffeaffeaffeaffccffccffccffccffaeffaeffaeffaeffaaffaaffaaffaaffa8ffa8ffa8ffa8ff8aff8aff8aff8aff88ff88ff88ff88ff80ff80ff80ff80ff808080ff808080ff2aff2aff2aff2aff110000ff110000ff10ff10ff10ff10ff0eff0eff0eff0eff0aff0aff0aff0aff08ff08ff08ff08ff02ff02ff02ff02ff020202ff020202ff00ff00ff00ff00ff000000ff000000fefefefefefefefefefe0000fefe0000fe00fefefe00fefefe00fe00fe00fe00fe000000fe000000fd00fd00fd00fd00fcfcfcfcfcfcfcfcfc00fc00fc00fc00fafafafafafafafafa00fa00fa00fa00f8f8f8f8f8f8f8f8f800f800f800f800f5f50000f5f50000f500f500f500f500f3f30000f3f30000f2f2f2f2f2f2f2f2f0f0f0f0f0f0f0f0f0f00000f0f00000f000f000f000f000efef0000efef0000ef00ef00ef00ef00ef000000ef000000eeeeeeeeeeeeeeeeeeee0000eeee0000ee00ee00ee00ee00ee000000ee000000ececececececececeaeaeaeaeaeaeaeaeaea0000eaea0000ea00eaeaea00eaeaea00ea00ea00ea00ea000000ea000000e0e0e0e0e0e0e0e0d0d0d0d0d0d0d0d0cececececececececccccccccccccccc else 0xffffff00ffffff00fffffefefffffefefffff0f0fffff0f0ffffeeeeffffeeeeffffeaeaffffeaeaffffccccffffccccffffaeaeffffaeaeffffaaaaffffaaaaffffa8a8ffffa8a8ffff8a8affff8a8affff8888ffff8888ffff8080ffff8080)) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x1591ac3400c3a438060521c02f290e014944700ac8c380523d9c029168e014884700c02638051131c016898e01481c700260e38056069c0002bae00014d70000a1b80004fdc00023ae0001157000086b8000425c00017ae0000b1700002cb800012dc00008ee0000457000021b80000f5c000072e00002b7 else 0
  | 5 => if page < 6 then (if page < 3 then (if page < 1 then 0x5cfadfd6beb3f4dfa4fd23e8ff46fa2fd13e85f41f9e7cefe75f38f9bfcdbe67f32f98fcc3e5ff2bf957ca7e51f27f927c77e37f19f8c7c5be29f13f88fc43e1df0cf85fc27e11f06f82fc13e05f01fd7de9ef80fa27d05e3ef17785bad3d66e9bb24b8edc39e01f else (if page < 2 then 0x3c20b9b105e347ef103b77c1dbba8d79906bd461cf8d0e79006ddb02bca415e8d61e46b072753f33a9b97c4dc80657c031fe018bf00c3f80617c0303e017ff00bef805e7c02efe0173f00b6f805a7c02cbe0163f00aff8056fc02abe0151f00a7f8051fc028be0141f0090f8047fc0237e0111f0087f8042fc01efe00f5f0075f803a7c01cfe00e5f0071f80387c01b3e00d7f006af80337c0197e00c9f0063f80317c0187e00bbf else 0x6e3cf261e75dcdbcea6de9b36dcc9b6e50db74e6d79e36bce1b5e68daf166d78236db61b79a4dbcd06de6736f2b9b6d58dbcaa6de5536da91b7944db7366bb5135dc099f664cf7486776933f2b99ee50af74e577a42bbcf15de70aeefa57d6e2bf3615f950afca457ea326bc4135dd49aed84d76426bae935d189ae784d73326b95935e8c92f1a497c820bd1905e6c82f184178b20bc1905da082ec24174a20ba1905d0082e7e417)) else (if page < 4 then 0xac8dbd5c6de8a35f411b78f8dbd1c5de6e2ef1b177a488bc442de91d6f46dde886ef40b779d5bbd10dbec46cf51b67a35b3d48d979c6cbd9b27a3593d48c976e64f46b0f62587b02c3daf61be030be6986f30c378b61bb4b0fa3583b32bbbaf5dbe02ebe9176ec2b4f5d5a7b0acdd7566f3a9fb9d4ddbe26ee911aedc8de6d46f30a379751bd467db993edca1f6de4fb6f07db573edcc9eed5cf779279ba33cdcd9e6e90f2f16797 else (if page < 5 then 0x918d61e46c630f2362d8791b06c3ca48d61ac6c5b0d635b98791adac3c9b6861d46b0b07235857f91ac2bbc9d7c4fccebe276675f13733af88d99b683ed46b09f726da0f751ac27bc8d613ce524d9b4e6e68da73af86d99b6e36d4db41b6a91a0dad1ac26dc9b5436d4da89b6a9144da6d0a26da8d6133e4ebe176675f0b733af85798d6126e46b093566cd89a6d06c4d65136269c6b7105a35848391ac24158d4c20ac6a1905675f06b31ac235c8d6117e46b087f235843793af81598d610ae46b083f292358691b16c348d6126a46b090500276576017129b009d94d805251dc028e89e0147417 else 0x32e35879931ac3cc88d61e6246b0f30635879711ac3cb78d61e59c6b0f2c235879491ac3ca38d61e4dc6b0f26635879251ac3c))) else 0
  | 6 => if page < 3 then (if page < 1 then 0x8d0afbe057d842bea015f390af9b057d841fe6c07fa48dbc6c5de35bbd1ac3da461bcd9f6e6cdb7486d76e36f341b7950dbca26db8d26bb0935cd89af1a4178d61e00647c0307e017bf00b7f80587c02a7e0147f008df80467c022fe0111f0077f803b7c01d7e00d9f0064f8030fc0183e00bff005df8027fc013be008df003cf801b7c00d7e0069f0033f80177c00b7e0057f0020f800bfc004be001bf0007f8001fc022ee00417 else (if page < 2 then 0x613dfc69e7f2cdbf926dfc636fe21b7ef4dbf706dfb536fd99b7ea4dbf486df9d36fcd9b7e5cdbf2c6df9236fc89b7e34dbf026df7f36fbf1b7df4dbef86df6e36fb69b7da0dbec26df5436fa99b7d44dbe986df4b36fa51b7d0cdbe7c6df3d36f9c9b7cd8d7e6c69f6133f9b19fe74bbf3a5bf9d2bf9b15fe349bec24df3626fc6907e746bf1a35f7c1afb08d7d406be7235f361afb08bfcd84bf1a1ff610ff9b07fe3437f3a15f else 0x32e37f931bfc88dfe246fee237f6f1bfb38dfd246fe8e37f371bf8d8cfc6c5fe75bbf1addf9d6dfc6b6fe75b3f96c3fc961fe230ff0587f70c3fb361fd830fe9187f36c3f9961fc930fe4587f1ac3f6e61fb6b0fda187ec2c1f615ffb0aefdf13fef89df7c46fcd9f7e34fbed07df613efcd9efe34f7ed07bf)) else 0
  | 7 => if page < 1 then 0x197fc4fd9fe93f1bf6efb6fd87e7df3df9b7c9be35f0ff857e92e4d7 else 0
  | 8 => if page < 1 then 0x1f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x3b else 0
  | 5 => if page < 1 then 0xec3b0ac2b0ac1b else 0
  | 6 => if page < 1 then 0x2b0ac2b else 0
  | 7 => if page < 1 then 0x1b else 0
  | 8 => if page < 1 then 0xb else 0
  | _ => 0

def counts : ℕ → ℕ
  | 4 => 33
  | 5 => 334
  | 6 => 174
  | 7 => 17
  | 8 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 256
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 8)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 5)

def bucketCount : ℕ → ℕ
  | 4 => 11
  | 5 => 146
  | 6 => 72
  | 7 => 14
  | 8 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 4 => 43
  | 5 => 529
  | 6 => 261
  | 7 => 62
  | 8 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 4 => 4
  | 5 => 7
  | 6 => 7
  | 7 => 5
  | 8 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 4 => 9
  | 5 => 12
  | 6 => 11
  | 7 => 8
  | 8 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x1401f001200 else 0
  | 5 => if page < 3 then (if page < 1 then 0x1a0408408181010e0410118b80091a016808a19080009c50c100138300381090400309104c100080c7830640080000418000301010404180 else (if page < 2 then 0x8e000c0709f020138020245220a5450a060430a341d881340040b022c0890c3c799026400b0000980101c2040a1008200002020a04182 else 0x624104001861300447020028012)) else 0
  | 6 => if page < 2 then (if page < 1 then 0x5610014908c0b40c2000a0a2a08a0a1821304144840248114784000202008060c14200240400300040821414380424400306140010018081 else 0x100000654c8000) else 0
  | 7 => if page < 1 then 0x311002d0880120806 else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x1e0783824000500016140983000090e80c200102400001b040621b110f8542c0203869b2200e00000000305c0005000 else 0
  | 5 => if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x7880005c9792818611010450649908570a104b0a601c34089f872a5559e06d08901da5c07e8a1158a1d57382f01917330009607d044800000066a37b95818800034838b5cc4d00a854826816c51476b4e04786101e830069389a48866b74c920 else 0xa505893c87f82103285e04f09289507c81c13f86f81b82000000004c85283609b07dc0003835d00008581756200004107315530006008a222219467211869b6712d01a4a209936783501db9481b052c0005a05b02f86a81101f851017d508980) else (if page < 3 then 0x6730000007705d90c0a085208381602a01e03e86e02a93d042072083024b59d9b978070016981c25b5400238d04044c093857862c2210500d8a401309839d05858a019023864436842951a4301684806b82189c072b0b0760710008100 else 0x2094600220001bb8404c3574000000000a2861c0003304985a850066159027a39961200013a6c804c63405896c0f87f46c050c32080081016d4491280380000c80000000002625385196f171800020c2bc0006540000000000000000007c0000)) else (if page < 6 then (if page < 5 then 0x2e08680000e03c06680e82c05d44705181089101645f068014c76a6190005919186088e30985c80000005500a00006887084007288e059999b22c8788634a82087697a07222c81806b000000019c000338a301ba000000000000000161000000 else 0x7a28922b4819088040290a483708982204e898b7988c81cd9c82409e47a35580008910007c90002a25ed1a80002988482a86e85e23db0004341209307293405b80680700000005f80008d874824a0007b80183e0a383a30005095989d80b8283) else (if page < 7 then 0x1500000007730900001446f00000000000008f85fa0000008eb1389340003b08a863c0003181580008b82652a313b28ba680009f082aa580003583083900009e84128b000027858800027d8088b22703a888b9004a00600006646f20007788c0 else (if page < 8 then 0x802e87584686704407b07409a84587e09402d865c4384905d827b824a0087097c9708f39b80000780000309a03b841c4b8a185f28805847500000004f81f00007a854d31066016a9315750007680002345658500000f0224568530000000000 else 0x2256180d04110006a36d83f02539452485d54d8000614028)))) else 0
  | 6 => if page < 5 then (if page < 2 then (if page < 1 then 0x241005f84704f11a1c8148930b80c60009603c1041a89810ec002a32714e2944318a0b01783b04c01a2125687c0b41cc189a60081ec288740c80ed428117222883f8000002901580006008039b03000000478000da800560 else 0x6c0b6138053001341a2a9bab028194a302f0b21483c87804c1dc1689210d10c2f4150d4129540162740005009f64420400008620cba0dd4700a0001711303283a458341460ca44ba914e88c47a7d0101ca46a9e400230300) else (if page < 3 then 0x72200000000950c8a5c000000001314d8944d200050b5f088018203000000388006b13c0a04eb4b64a0003289a5044cc0007100415c0e35560001c380660356644a42e1408b00bc630ce1b81f33227e0498c3943010f5368 else (if page < 4 then 0x751488d84721d00025d0003d0000000000012007ca6b8867e8001b8aa4c403c1aa010f400000000000025ae884200000250610620002809c000000000390d01082423441620a108830de0b2b43940540001e3451540e039d else 0x24b658ac000060))) else 0
  | 7 => if page < 1 then 0x302000000000334c7360390000101300350000681812005b0831223c5338008040282370345232000049787b44500000007a7200414800585a00006461 else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let h := key xs
  let b := bucketCount k
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 8,slot % 8)

def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s12]
  | 2 => [s01]
  | 3 => [s01, s02]
  | 4 => [s02, s01]
  | 5 => [s02]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s12_ok, s01_ok, s02_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def pinBase : List W := [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff,0xffffffff]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut0 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub12x0.target 0x550055
    (fun r => ⟨(0x412516002106 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub12x0.raw 4 (@Sub12x0.lower) Sub12x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut1 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub12x0.target 0x330033
    (fun r => ⟨(0x411515001105 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub12x0.raw 4 (@Sub12x0.lower) Sub12x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut2 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub12x0.target 0xf000f
    (fun r => ⟨(0x411493001083 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub12x0.raw 4 (@Sub12x0.lower) Sub12x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut3 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub12x0.target 0xf0f00000
    (fun r => ⟨(0x71d79f515597 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub12x0.raw 4 (@Sub12x0.lower) Sub12x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut4 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub12x0.target 0xcccc0000
    (fun r => ⟨(0x69b79f493597 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub12x0.raw 4 (@Sub12x0.lower) Sub12x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut5 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Sub12x0.target 0xaaaa0000
    (fun r => ⟨(0x65b75f453557 >>> (6 * (r.val % 8))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Sub12x0.raw 4 (@Sub12x0.lower) Sub12x0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut7 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor4.target 0x55555555
    (fun r => ⟨(0x20a30e00210661a71e412516 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor4.raw 5 (@Minor4.lower) Minor4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut8 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor4.target 0x33333333
    (fun r => ⟨(0x20930d00110561971d411515 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor4.raw 5 (@Minor4.lower) Minor4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut9 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor4.target 0xf0f0f0f
    (fun r => ⟨(0x20928b00108361969b411493 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor4.raw 5 (@Minor4.lower) Minor4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut10 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor2.target 0xf0f0f0f0
    (fun r => ⟨(0x1d71961551143df39e35d31c >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 5 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut11 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor2.target 0xcccccccc
    (fun r => ⟨(0x1d71960d30923df39e2db29a >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 5 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut12 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor2.target 0xaaaaaaaa
    (fun r => ⟨(0x1d71550d30513df35d2db259 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 5 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut13 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor1.target 0xffff0000
    (fun r => ⟨(0x61969b71d79f411493515597 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut14 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor3.target 0xff0000ff
    (fun r => ⟨(0x7de75c6da6581c61440c2040 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor3.raw 6 (@Minor3.lower) Minor3.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut15 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor3.target 0xff00ff00
    (fun r => ⟨(0x7de75c6da6583ce34c2ca248 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor3.raw 6 (@Minor3.lower) Minor3.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut35 (p : List (Nat × Nat)) : CutCertificate target :=
  prefixCutCertificate target Minor1.target 0xff00ff
    (fun r => ⟨(0x1c61440c20405d65544d2450 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p
def cutFor : Nat → List (Nat × Nat) → CutCertificate target
  | 2 => cut1
  | 3 => cut2
  | 4 => cut3
  | 5 => cut4
  | 6 => cut5
  | 8 => cut7
  | 9 => cut8
  | 10 => cut9
  | 11 => cut10
  | 12 => cut11
  | 13 => cut12
  | 14 => cut13
  | 15 => cut14
  | 16 => cut15
  | 36 => cut35
  | _ => cut0

def suppliedPrefix : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | j+1, z => if z=0 then [] else ((z%256)/16,z%16) :: suppliedPrefix j (z/256)
def selectCut (code : Nat) := cutFor (code%128) (suppliedPrefix 2 (code/128))
def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 4 => if page < 1 then 0x50000020000040000080000400000a0000080000080000300000200001000000800004000008000014000008000010000080000040000080000100000c000004000008000010000020000100000200000300000200000800003000001 else 0
  | 5 => if page < 6 then (if page < 3 then (if page < 1 then 0x1000002000004000008000012000028000050000090000100000200000400000a00001400002c0000580000b00001600002c000040000080000100000200000580000b0000100000200000400000b00001600002c0000680000d000010000020000040000080000160000200000400000b00001a00003400004000008000010000020000058000080000100000200000400000800001600002c0000500000c00001a0000200000400000900001600003400005800008 else (if page < 2 then 0x180000340224780000d0034200000340000400000b0000180000300000400000d00001000002268d0700000b00001200002c0000680000d000010000020000040000080000160000200000400000b00001a000034000040000080000100000200000580000800001000002c0000580000b0000140000280000400000900001a000034000048000090000120000340000680000a00001a000034000040000080000100000280000500000800001000002000004000008 else 0x300000500000b0000100000200000400000800001000002c0000580000d000010000020000040000080000100000200000400000800001000002c000040000080000100000200000400000000001000002000004000008000000000020000058000080000100000200000400000b00000000000000000000000000000000000000000000000000000000000000580000c0000180000300000680000c0000180000300000680000c0000180000300000600000c)) else (if page < 4 then 0x300000600000c0000180000300000680000c0000000000340000000000d00001a0000200000680000d00001000002c000040000000000160000200000400000000001000002000004000008000010000020000068011a4000018000020000040000080000100000200000000000800001000002000004000009000012000024000000000080000100000200000400000b00001600002c0000000000a00001400002c0000500000b00001600002c0000000000c else (if page < 5 then 0x8923480000300000600000c89231c000030000040000080000100000200000400000800001200002400004800009000015124638000054491a40000191454380000580000a000010000020a890700000800001000002120a8700000800001000002c0000580000b89231d12463a28a8715120e482a1c0000340000600000c00001800003268d12000008000011124638000064d1a0e000010000022248c700000c89231c0000300000480000b0000160000000000580000b else 0x2248c744918e000018000020000044491a40000180000200000444918e0000180000200000444918e))) else 0
  | 6 => if page < 3 then (if page < 1 then 0x891c006838008c7001c0e003a1c005438008c700150e00891c0112900224700000000231c0114380000000150e002a1c00000000a8700000000891c00463800a870000000000000000380000700000e0000200000400000800000000891c0112380001200000000481c00009000000000000000000004638008c70000240000000068380001200000000000000543800a87000024000000013438000120000000000200000400000800000e00001c00003800012000010 else (if page < 2 then 0x234800000000a8700150e002a1c00543800a87001524002a4800549000a9200150e00000000000000a87001524002a1c00549000000000000002a1c00549000000000000002a1c00549000000000000002a1c0054900000000150e002a480000000000000150e002a4800000000a8700152400000000000002687004d240000000000000224700118e002a1c011290026920044a400344800469000e12001d24002a4800469000a9200448e00231c00543802247004d0e else 0x224700448e00891c011238022520044a40089480112380000000000000891c0112900268700448e009a480112900000000118e00231c004638008c70011a4002348004690008c7000000000000004638008d200000000231c0046900000000118e00234800000000d07001a240000000114380224700120e00231c01149002252001224)) else 0
  | 7 => if page < 1 then 0xe00001c0000900000700000000001c0000900000000000e0000480000000000700002400001c0000380000700000e else 0
  | 8 => if page < 1 then 0x0 else 0
  | _ => 0

def label (k i : Nat) := field cutLabels k 23 i

def checked (k i : Nat) := decide (pool k i).Nodup &&
  (if label k i = 0 then fastClosed target negative pool counts lookup steps k i
   else let c := selectCut (label k i)
        maskedCut c.mask c.patterns c.bound k (pool k i))
theorem checked_sound (k i : Nat) (h : checked k i = true) :
    closed target negative pool counts lookup steps k i = true ∨
      (∀ d ≤ k, ¬ Cone target d (pool k i).toFinset) := by
  have h' := (Bool.and_eq_true_iff.mp h).2
  change (if label k i = 0 then _ else _) = true at h'
  split at h'
  · exact Or.inl (fastClosed_sound target nonzero negative pool counts lookup steps k i h')
  · refine Or.inr (fun d hd run => ?_)
    have no := (selectCut (label k i)).sound k (pool k i) hd run
    change maskedCut _ _ _ _ _ = true at h'
    rw [no] at h'
    contradiction

theorem root : pool 8 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 33 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 33 0 = true :=
  chunk4x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x112 : span (checked 5) 112 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x224 : span (checked 5) 110 224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 334 0 = true :=
  (@span_join (checked 5) 112 0 222 chunk5x0 (@span_join (checked 5) 112 112 110 chunk5x112 chunk5x224))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x112 : span (checked 6) 62 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 174 0 = true :=
  (@span_join (checked 6) 112 0 62 chunk6x0 chunk6x112)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 17 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 17 0 = true :=
  chunk7x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x0 : span (checked 8) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer8 : span (checked 8) 1 0 = true :=
  chunk8x0
theorem verified : ∀ k ≤ 8, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer7 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer8 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 9 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes_or target nonzero negative neg pool counts lookup steps valid fix 8
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => checked_sound k i (verified k hk i hi))
    8 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Minor12


namespace SignedFrontier.SmallCert.Full

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def target : W := 0xfe80e880e8808080
def negative : List Nat := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 28, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 44, 48, 49, 50, 51, 52, 53, 54, 56]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw :=
  essentialOfRows target raw [(0xaaaaaaaaaaaaaaaa,6,7),(0xcccccccccccccccc,5,7),(0xf0f0f0f0f0f0f0f0,3,7),(0xff00ff00ff00ff00,19,27),(0xffff0000ffff0000,11,27),(0xffffffff00000000,11,43)] (by decide +kernel) (by decide +kernel)

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 6 then (if page < 3 then (if page < 1 then 0xe0e00000e0e00000e000e00ee00ee000c0c0c0c0c0c0c0c0b0b0a0a0b0b0a0a0b0b0000bbbb00000b0b00000b0b00000b000b00bb00bb000a0a0a0aaaaaaaaa0a0a0a0a0a0a0a0a0a0a00000a0a00000a0a0000000000000a000a000a000a000808080888888888080808080a0a0a0a08080808080808080808000008080000070700007777000007070000070700000700070077007700030300000303000003030000000000000300030003000300020202020a0a0a0a02020202020202020202000002020000010100000101000000ff000000ff000000ff00000000000000ee00ee00ee00ee00ea00c000ea00c000ae000c00ae000c00aa00aa00aa00aa00aa000000aa000000a800a800fc00fc008f0088008f00880088008800880088002f0022002f0022000f0000000f0000000e000e00ee00ee000a000a000a000a0000ff00ff00ff000000eeeeeeeeeeee0000aaaaaaaaaaaa000088888888888800000a0a0a0a0a0a00000000ffff000000000000ff00ff0000000000eeeeeeee00000000eaeac0c000000000aeae0c0c00000000aaaaaaaa00000000aaaa000000000000a8a8fcfc00000000a8a8a8a8000000008f8f8888000000008a8a8a8a0000000088888888000000002f2f2222000000002a2a2a2a000000000f0f0000000000000e0eeeee000000000e0e0e0e000000000a0a0a0a0000000000000000 else (if page < 2 then 0x7700770077007700757530307575303073737373505050507373505073735050707070707070707066666666666666665d5d5d5d0c0c0c0c5d5d0c0c5d5d0c0c55555555000000005555000055550000555500000000000055005500550055005454fcfc5454fcfc54545454fcfcfcfc50505050505050504f4f4f4f444444444f4f44444f4f444444444444444444443f3f00003f3f00003f3f0000000000003f003f003f003f003c3c3c3c3c3c3c3c3b3b3b3b0a0a0a0a3b3b0a0a3b3b0a0a333333330000000033330000ffff00003333000033330000333300000000000033003300ff00ff003300330033003300330000003300000032323232fafafafa313100003131000030303030f0f0f0f030303030303030302f2f2f2f222222222f2f22222f2f22222f2f00002f2f00002f2f0000222200002f0022002f0022002a2a2a2a2a2a2a2a2a2a0a0a2a2a0a0a2a2a00003f3f00002a2a00002a2a00002a002a003f003f0022222222aaaaaaaa22222222222222221f1f00001f1f00001f1f0000111100001f0011001f0011000f0f0f0f000000000f0f08080f0f08080f0f02020f0f02020f0f0000ffff00000f0f00000f0f00000f0f0000000000000f000f00ff00ff000f000f000f000f000f0000000f0000000e0eeeee0e0eeeee0e0e0e0eeeeeeeee0e0e0e0e0e0e0e0e0e0e0a0a0e0e0a0a0e0e0000eeee0000 else 0xb3b3b3b3a0a0a0a0b3b3a0a0b3b3a0a0b0b0b0b0b0b0b0b0afafaaaaafafaaaaafaf0000afaf0000afaf000000000000af00af00af00af00aeaeaeaeeeeeeeeeaeaeaeaeaeaeaeaeaeaeaeae0c0c0c0caeae0c0caeae0c0caeae0000aeae0000aeae00000c0c0000ae000c00ae000c00abab0000abab0000abab000003030000ab000300ab000300aaaaaaaafefefefeaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaa8080aaaa8080aaaa0808aaaa0808aaaa0202aaaa0202aaaa0000ffff0000aaaa0000aaaa0000aaaa000000000000aa00aa00ff00ff00aa00aa00aa00aa00aa000000aa000000a8a8fcfca8a8fcfca8a8a8a8fcfcfcfca8a8a8a8a8a8a8a8a8a88888a8a88888a8a80000fcfc0000a8a80000a8a80000a800a800fc00fc00a0a0aaaaa0a0aaaaa0a0a0a0aaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a0000000008f8f8f8f888888888f8f88888f8f88888f8f00008f8f00008f8f0000888800008f0088008f0088008a8a8a8a8a8a8a8a8a8a88888a8a88888a8a0a0a8a8a0a0a8a8a0000cfcf00008a8a00008a8a00008a008a00cf00cf008888aaaa8888aaaa88888888aaaaaaaa88888888888888888888888800000000888800008888000088880000000000008800880088008800808088888080888880808080888888888080808080808080808000008080000077777777000000007777000077770000)) else (if page < 4 then 0xf000f000ff00ff00f000f000f000f000f0000000f0000000efefeeeeefefeeeeeeeeeeeeeeeeeeeeeeeeeeee00000000eeeecccceeeecccceeeeaaaaeeeeaaaaeeee0000eeee0000eeee000000000000ee00ee00ee00ee00ececececfcfcfcfcececececa0a0a0a0ececa0a0ececa0a0eaeaeaeaeeeeeeeeeaeaeaeaeaeaeaeaeaeaeaeac0c0c0c0eaeac0c0eaeac0c0eaea0000eaea0000eaea0000c0c00000ea00c000ea00c000e0e0eeeee0e0eeeee0e0e0e0eeeeeeeee0e0e0e0e0e0e0e0e0e00000e0e00000dcdcdcdc50505050dcdc5050dcdc5050d5d5d5d5c0c0c0c0d5d5c0c0d5d5c0c0d0d0dddd00000000d0d0d0d0d0d0d0d0d0d00000d0d00000d000dd00d000dd00cfcfcfcf00000000cfcf0000cfcf0000cf00cf00cf00cf00cececececececececececece0a0a0a0acece0a0acece0a0accccffff00000000cccccccccccccccccccccccc00000000cccc0000ffff0000cccc0000cccc0000cccc000000000000cc00ff00cc00ff00cc00cc00ff00ff00cc00cc00cc00cc00cc000000cc000000c8c8fafac8c8fafac8c8c8c8fafafafac4c4c4c4c4c4c4c4c4c40000c4c40000c0c0f0f0c0c0f0f0c0c0ccccc0c0ccccc0c0c0c0f0f0f0f0c0c0c0c0c0c0c0c0c0c00000c0c00000bbbbbbbb00000000bbbbaaaabbbbaaaabbbb0000bbbb0000bb00bb00bb00bb00babababa30303030baba3030baba3030 else (if page < 5 then 0xffff0c0cffff0c0cffff0a0affff0a0affff0a0a0a0a0a0affff0000ffff0000ffff000000000000fffcfffcfffcfffcfff0fff0fff0fff0fff0ff00fff0ff00ffeeffeeffeeffeeffeaffc0ffeaffc0ffccffccffccffccffccff00ffccff00ffc0ffc0ffc0ffc0ffaeff0cffaeff0cffaaffaaffaaffaaffaaff00ffaaff00ffa8ffa8fffcfffcff8fff88ff8fff88ff88ff88ff88ff88ff33ff00ff33ff00ff2fff22ff2fff22ff22ff22ff22ff22ff0fff00ff0fff00ff0eff0effeeffeeff0cff0cff0cff0cff0aff0aff0aff0aff00ff00ff00ff00ff00ff0000000000ff000000ff000000ff00000000000000fefefefefefefefefefefcfcfefefcfcfefeeeeefefeeeeefcfcfcfcfcfcfcfcfcfcfcfc00000000fcfcf0f0fcfcf0f0fcfc0000fcfc0000fc00fc00fc00fc00fafafafafafafafafafaaaaafafaaaaaf8f8f8f8f8f8f8f8f8f8f8f888888888f8f88888f8f88888f5f5f5f500000000f5f50000f5f50000f5f5000000000000f500f500f500f500f4f4f4f444444444f4f44444f4f44444f3f3f0f0f3f3f0f0f2f2f2f2f2f2f2f2f2f2f2f222222222f2f22222f2f22222f1f1f1f100000000f1f1000011110000f100f10011001100f0f0ffff00000000f0f0f0f0f0f0f0f0f0f0f0f010101010f0f0f0f000000000f0f00000ffff0000f0f00000f0f00000f0f0000000000000f000ff00f000ff00 else 0xffffffffffff0000ffffffffff00ff00fffffffffcfcfcfcfffffffff0f0f0f0fffffffff0f00000ffffffffeeeeeeeeffffffffeaeac0c0ffffffffccccccccffffffffcccc0000ffffffffc0c0c0c0ffffffffaeae0c0cffffffffaaaaaaaaffffffffaaaa0000ffffffff8f8f8888ffffffff88888888ffffffff33330000ffffffff2f2f2222ffffffff22222222ffffffff0f0f0000ffffffff0c0c0c0cffffffff0a0a0a0affffffff00000000ffffff00ffffff00ffffff00ff00ff00fffffcfcfffffcfcfffff8f8fffff8f8fffff2f2fffff2f2fffff0f0fffff0f0fffff0f0ffff0000fffff0f0f0f0f0f0ffffeeeeffffeeeeffffeeeeeeeeeeeeffffeaeaffffeaeaffffeaeaffffc0c0ffffccccffffccccffffccccffff0000ffffccccccccccccffffc0c0ffffc0c0ffffaeaeffffaeaeffffaeaeffff0c0cffffaaaaffffaaaaffffaaaaffff0000ffffaaaaaaaaaaaaffffa8a8fffffcfcffff8f8fffff8888ffff8888ffff8888ffff888888888888ffff3333ffff0000ffff2f2fffff2222ffff2222ffff2222ffff0f0fffff0000ffff0e0effffeeee))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 7 => if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0x94fe4ff92fe47f90fe3ff8efe37f8bfe23f84fe0ff5afd67f58fd5ff56fd57f54fd4ff50fd3ff4efd33f4bfd0bf41fd03f3ffcfbf3cfceff3afce7f38fcdbf33fccbf31fcbff2efcb7f2cfca7f28fc8bf21fc7bf1dfc6ff19fc43f0ffc3bf0bfc2bf09fc23f07fc1bf05fc0ff02fc07f else (if page < 2 then 0x6816fd8a926f5f11bb3411bb9210df9190ef77845f77045f5b045f5a845f51045f50845f4b845f4b045f2e045f2d845f22045f21845f50835f00557f0054ff0054bf00537f00533f00523f0051ff0051bf0050ff00503f004fbf004dbf004cbf004bff004bbf004aff004a3f00487f0047ff003f3f003e3f003c7f003c3f003b7f003b3f003aff002f3f002e3f002dff002d3f002cff002cbf002c7f002c3f002bff002bbf002aff002abf002a7f00283f0027ff0027bf00277f00273f00257f else 0x50847f4b847f4b047f2e047f2d847f22047f21847f74843f21843f7703ff5a83bf79837f79037f77837f77037f73037f72837f72037f71837f6d037f6c837f67037f66837f5b037f5a837f51037f50837f4b837f4b037f3c837f3c037f39837f39037f38037f37837f2e037f2d837f22037f21837f5102ff3902bf4b027f60823f8b01ff4b81ff2d81bf77817f2200ff7480bf6d007f34807fa5bbaf923b9f91bbaf922d5f91ad6f92285f91a86f56285f92259f91a5af5225be9216df9196ef)) else (if page < 5 then (if page < 4 then 0x378dbf860cff668cbf5f8cbf8a8c7f340c7f8b0bff8a8bbf8b0b7f4b0b3f378b3f798a7f300a7f6c8a3f508a3f77897f77097f5b097f5a897f51097f50897f4b897f4b097f2e097f2d897f22097f21897f7708bf5a887f79083f77083f72883f71883f6c883f66883f5a883f50883f4b083f3c083f39083f37883f2d883f21883f5087bf4b077f2d86ff21867f7784bf7704bf5b04bf5a84bf5104bf5084bf4b84bf4b04bf2e04bf2d84bf2204bf2184bf77847f77047f5b047f5a847f51047f else 0x9410ff9210ff9190ff9090ff8c90ff8510ff8490ff8410ff8290ff8210ff8110ff7f10ff7d90ff5c10ff5610ff5390ff5210ff4c90ff4c10ff4510ff3390ff3290ff3110ff2690ff2490ff2310ff2190bf6c907f21903f220fff218fbf340f3f880eff878ebf880e7f880e3f218e3f8a8dff878dff858dff790dff770dff748dff728dff718dff6c8dff668dff600dff5f0dff5a8dff508dff4b0dff3f0dff3e0dff3c0dff390dff378dff340dff300dff2d8dff218dff770dbf750dbf600dbf) else (if page < 6 then 0x4c96ff4516ff4296ff2d96bf2e167f2d963f7195ff3415bf72157f71953f7214ff75143f7493ff7513bf4b133f2d92ff8b127f8a927f86127f85927f77927f77127f75127f74927f60927f60127f5f927f5f127f5b127f5a927f51127f50927f4b927f4b127f3e927f3e127f34927f34127f2e127f2d927f8a91bf8591bf7711bf7491bf6011bf5f11bf5a91bf5091bf4b11bf3e11bf3411bf2d91bfb990ffb910ffb810ffb710ffb410ffae90ffac10ffa590ffa010ff9d90ff9c90ff9890ff else 0x8225bf8125bf7f25bf7da5bf5e25bf5625bf53a5bf5225bf4b257f4ba53f4b24ff4b247f6ca43f66a2ff8aa2bf85a2bf7722bf74a2bf6022bf5f22bf5aa2bf50a2bf4b22bf60223f4b20ffb996ffb916ffb816ffb616ffb416ffb196ffae96ffac96ffac16ffa896ffa596ffa116ff9d96ff9c96ff9a96ff9896ff9596ff9216ff9196ff8f16ff8c96ff8216ff8116ff7f16ff7e16ff7d96ff7116ff7096ff7016ff6f96ff6b16ff6a16ff6816ff6496ff6396ff5e16ff5616ff5396ff5216ff))) else (if page < 10 then (if page < 8 then 0x772aff5aaabf79a9ff7929ff77a9ff7729ff7329ff72a9ff6d29ff6ca9ff5b29ff5aa9ff79293f77293f72a93f6ca93f5aa93fb9a87fb9287fb8a87fb6287fb4287faea87fa8a87fa5a87fa4287f9da87f9aa87f98a87f97a87f92287f91a87f8f287f7da87f7a287f6b287f6a287f68287f57287f56287f53a87f52287f50a83f8aa7ff50a7bf51277f50a73fb9a5bfb925bfb825bfb425bfb325bfaea5bfad25bfac25bfa5a5bfa325bf9da5bf9ca5bf98a5bf9725bf9225bf91a5bf8ca5bf else (if page < 9 then 0x63a9c55cb1cec2ae63cc713f2fb4509bc7da2849e4798e1fe5f68a0d78fb4505fc7da282de4798e15e5f68a0a78fb4504bc8f31c1bcc798e0ce5f68a027800b9bbbf005c9ddf802daeefc016c777e00b43bbf00575ddf802a2eefc014e777e00a5bbbf004edddf8026ceefc0135777e0098bbbf00491ddf80246eefc011e777e007dbbbf003e5ddf801e0eefc00ee76fe0077bb3f003b9d7f802e6b5fc01725afe00b82d7f005b16bf802d2b5fc01685afe00aead7f005616bf802a2b5fc014b5afe009fad7f004ed6bf80272b5fc01355afe00992d7f004c56bf80248b5fc01235afe00902d7f004796bf80232b5fc00fb5afe007cad7f002dd6bf8016ab4fc00b659fe005aacbf else 0x7dba11449e1f68a40126c813ed1442e1f68a2490b89dbed1412b276fb45045c823ed14117204fb45045c7da289a1171f68a24845c9dbed14107208fb45041c8f31d580de23cc73b83788f31cee0d66e73b7da28c00571f68af001587da2bc0055df68af001567da2bc00551f68af001457da2bc00505f68af001387da2bc004a5f68af001227da2bc0047df68af001157da2bc0040df68af001027da2bc00405f68af000ff7da2bc003f5f68af000fc7da2bc003edec8af0013b7aa2bc00409ea8af000fb74a2bc003edce8af000fb4b22bc003ed1487f000fb45213c003ed1482f0011e639b39004ee3c6ae4013b639ab9004794e6ae400c7539ab9004798e54e400fb4512bc003ed1449f000f545127c003ecf449f0008a3d127c003ed1448f000fb4511fc003ed1445f000fb4510fc003ed143ff000fb450cfc003ed1430f000fb450bbc004798e2be4013b638ab9)) else (if page < 12 then (if page < 11 then 0x8f31d4e27e5f68a2489bc9dbed1425f208fb45097c813ed1425f1f68a26897c7da289225f276fb45093c9dbed1423f204fb4508fc7da289223f2771e6388398f31d4e20e63cc73b08398f31d4e1fe676fb45073c813ed141cf1f68a24873c7da28921af276fb4505fc9dbed1416f2771e6385799dbed1414f276fb4504bc823ed1412f204fb4504bc7da289a12f1f68a2484bc9dbed1411f208fb45047c813ed1411f1f68a26847c7da289211f276fb45043c823ed1410f204fb45043c7da289a10f1f68a24843c9dc798e0de63cc75603798f31d4e0de63cc73b83798f31cec0de63cc75383399dbed1407f208fb4501fc813ed1407f1f68a2681fc7da289207f1f68a24813cb9cedf68a7277237da2acac409f68ae2b1027da2ac92409f68a7247027da2ac9dbedee8ab204fb7ba2ac813edd08ae2b0fb451278a33ed1449b248fb45125c91bed1449b204fb45126c else 0xaabed1449f28cfb45127c9dbed1449f272fb45127c9bbed1449f25afb45127c94bed1449f248fb45127c91bed1449f242fb45127c8bbed1449f20efb45127c823ed1449f204fb45127c803ed1449f1fcfb45127c7e3ed1449f1f6fa45127c7dbdd1449f1f6f545127c7dba91449f1f6e845127c7da591449f1f68a44927c7da291049f1f68a43127c7da290a49f1f68a41927c7da290249f1f68a40127c7da28fe49f1f68a3d927c7da28f449f1f68a26927c9dbed1448f1f68a24923c823ed1447f276fb4511bc813ed1446f1f68a2491bc7da289245f208fb4510fc9dbed1442f204fb4510bc7da289242f1f68a248ffc823ed1433f276fb450c7c813ed1431f1f68a248c7c7da289230f1f68a248bbc9dc798e2ce63cc7560b398f31d4e2ce63cc73b8b398f31cec2ce6771e638af99dc798e2ae63cc7538ab98f31cec2ae6771e638a398f31d4e28e63cc73b0a39) else (if page < 13 then 0xb9409f68af2e1027da2bcb7c09f68af2dd027da2bcb2c09f68af2bb027da2bcac409f68af2ab027da2bca3409f68af277027da2bc9cc09f68af271027da2bc9bc09f68af25b027da2bc92409f68af247027da2bc90c09f68af23f027da2bc8bc09f68af22b027da2bc82409f68af277017da2bc81405f68af276fe7da2bc813f9f68af204fd7da2bc9dbedee8af208fb7ba2bc813edee8af276fb7b22bc9dbedea8af204fb7aa2bc9dbedd08af204fb7422bc813edce8af276fb45223c823ed1488f204fb45223c9dbed1487f276fb4521bc813ed1486f276fb4520fc813ed1483f204fb4520bc9dc798e6de63cc7561b798f31d4e6de6771e639b399dc798e6be63cc7539af99dc798e6ae63cc7539ab99dc798e57e63cc75395f98f31d4e54e608fb4512bcb9bed1449f2e4fb45127cb83ed1449f2dcfb45127cb2bed1449f2c2fb45127caebed1449f2b0fb45127c else 0x2e73b7da2bcaecedf68af2b93b7da2bcac4edf68af2ad3b7da2bcaacedf68af2a93b7da2bca34edf68af28b3b7da2bc9dce5f68af277377da2bc9dcb5f68af277237da2bc9dc89f68af277217da2bc9dc5df68af2e7027da2bc)))) else 0
  | 8 => if page < 19 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x8f033f63833f1e833f9d81ff8201ff8101ff2681ff2481ff7d813f45013f28813f9d807f6b007f6a007f33807f32807f9dbdef8da9ef53a83ea3126f74127b40126f8110bb2490bb9d841f82041f7aa2bc8f1ab9639ab9638ab900553f00517f004f7f0047ff003f3f003dbf003bbf002ebf002d7f00287f00277f0025bf0023bf0021ff00213f0020bf001b3f0016ff00153f0010ff000fff000ebf000d7f000cff000cbf000c3f000bbf000aff000a7f0009ff0009bf0005bf00053f0004ff else 0x1b8b3f9d8aff8f0aff9d8abf538abf3b0abf6b0a7f1b8a7f9d8a3f6a0a3f538a3f3b0a3f248a3f8f09ff5389ff2489ff1b89ff7d89bf2489bf7d893f45093f1b893f9d88ff8108ff2488ff8f07ff6387ff1e87ff9d873f81073f24873f7d86bf4506bf2886bf9d863f6a063f32863f7d85ff4505ff1b85ff9d85bf7d85bf8f057f7d857f63857f45057f37057f1e857f1b857f9d853f45053f9d84ff1b84ff7d84bf4504bf1b84bf9d843f82043f81043f26843f24843f8f037f63837f1e837f) else (if page < 3 then 0x6a8dff6a0dff698dff688dff678dff658dff640dff630dff620dff530dff458dff440dff3a8dff340dff330dff328dff320dff318dff308dff2f8dff2f0dff290dff240dff9d8dbf8f0dbf7d8dbf6b0dbf6a0dbf638dbf450dbf370dbf338dbf328dbf2e8dbf288dbf1e8dbf9d8d7f1b8d7f9d8d3f6a0d3f328d3f820cff450cff338cbf1b8cbf9d8c7f810c7f538c7f328c7f248c7f538c3f450c3f248c3f1b8c3f450bbf248bbf9d8b3f7d8b3f560b3f538b3f450b3f3b8b3f3b0b3f370b3f else 0x96927f95127f90927f8b927f86927f7e127f7d927f7d127f7b927f7a927f75127f74127f62927f61927f61127f5e927f4b127f45127f44927f44127f43127f42927f41927f40927f40127f3f927f3d927f2d927f8c923f7d923f4c923f45123f7d91ff4511ff7d917f45117f8210ff7d90ff9d90bf8110bf2490bf7d8fff248fff248ebf7d8e3f450e3fae0dffab0dffa88dffa80dffa78dffa48dffa20dff9e8dff9d8dff9a0dff960dff910dff8e0dff890dff870dff808dff7c0dff6c8dff)) else (if page < 6 then (if page < 5 then 0x9da83f53a83f8f277f53a77f9da4bf53a4bf53a3bf8ca2ffae22bfac22bfaba2bfab22bfa4a2bfa2a2bfa0a2bf9da2bf9c22bf94a2bf9122bf8c22bf8aa2bf81a2bf8122bf80a2bf7fa2bf7ea2bf5e22bf5322bf4d22bf4b22bf9da23f8ca23f82223f81223f4ca23f9da1ff4521ff9da1bf8121bf45213f9da0ff53a0ff53a0bf4520bf9d9b7f561b7f539b7f9d9b3f639b3f9d9aff539aff9d95ff5395ff63953f53953f7d92bf4512bfb7127fb2927fb1127faa927fa3127fa1127f9b927f else 0x91bed1563ed14117001559dfe00aa4eff0051a77f8028b3bfc013e9dfe009eceff004ee6ff802772dfc013b937e009dc87f00571f7f802b0fbfc01577dfe00ab3eff00551f7f80292fbfc01417dfe009dbeff004e1f7f80252fbfc01227dfe008fbeff003f1f7f80232f8fc013b7bfe009dbdbf003ededf80276f5fc013b787e007daf3f004ed77f80276bafc013b5cfe009dadff0047951f802e2a7fc016a53fe00b029ff0056d4ff8029ca7fc013f53fe009d29ff004cd4ff8024ea7fc012153fe009029ff004794ff8023aa7fc011b53fe008d29ff003c14ff801dca7fc00de53fe006ea9ff003714ff8016ea7fc00b553fe008f29bf003ed4df8023ca5fc011e51fe008f287f) else (if page < 7 then 0x8122822fbec9a117d144d08befb24845f4512422fcec6e117dac3708bed41b845f338dc22f9946e117e76fb083f047d841f8f2b01bf31d580dfa3c7706fcc73b837e8f1dc1afb1cee0d7d583d06fc771e837e3b8f41afdce76fb3ee6fb45795d7da2bcac3ed15e555f68af28cfb45793b7da2bc9cbed15e4ddf68af25afb4579237da2bc90bed15e45df68af204fb4578fe7da2bc7dbdd15e3edea8af1f6e84579739da28f7da2911e3ed1486f1f68a41f91e639b798f31cd7cc798e6ae63cc72bf2fb45127c7da288de3ed1442f2e73b1b9efb450c7c8f31c59cc798e2ae63cc71472fb45097c7da2847e4798e20e5f68a0e78fb4504bc7da2823e3ed1410f23cc706f2fb4501fc else (if page < 8 then 0x91c794f7c7a36a7be3ca7507d3b7da2bd813ed15edce768a7e7723455f588122bbac409157c92048a7e4702455f3b5222be8129115f561f649ee48fb24bf237d926f813ec937bedd049edf68a24fb5845127ba3228937c9114497e468a24df0245126f5222893f2290049be76992376d44c91bb4c9948ddc09f642edf64921773b8c8dfbb9cec6efcee4637be76fe1bf7516a0dfd8cb506fdd45a837be48d41bbf236a0def7f3506fdced3237f9a8991bfd3b388dfb6a1c46fdd44ca37f632651bf724328ddf919946f7bf8ca37eda8651bde99328dfe389946fdcec8c37eda8461bf665230dfb9dbec257ced1412be7637095f3b7d845f8f2b022fc794e117e768a08bf0445045f else 0x338dc23f9946e11fe76fb087f047d843f813ec21fbec9a10fdf649087f3b8f037f9dbec1bfc65ac0dfe32d406ff3b63837f8f2b01bfb1d580dfe3ca706fec753837f9da281bfc11140dfe048a06ff1e3b837f639dc1bfc78ec0dfd8e7606ff3b37037f821b81bfc08dc0dfdf64d06fe8a26837f371341bfbec920dfd144906fe6e24837f9d8f41bfab07a0dfd4e3d06fe771e837f3b0f41bfcec6e0dfdac3706fed41b837f338dc1bf9946e0dfe3ca7067ec753833f538f419fced1407fe088a03ff024501ff451340ffa289207fdf649027e8a24813f2892409fcec6e01fdac3700fed41b807f338dc03f9946e01fee73b7dbf3b91beef9dbedef7d2e3ca7fa971e53df248f29df)))) else (if page < 14 then (if page < 11 then (if page < 10 then 0x9d9b841fc08dc20fdf649107e8a24883f3712441fcec7a20fd4e3d107e761e883f9d8dc41fb506e20fcca37107f1e5387ff63a9c3ffa9c7a1ffe768a0e7f0245073f4512439fbec921afd14490d7e512486bf9d8dc31fb506e18fcca370c7f3b7d85ff9da282ffcec6e17fe76fb0b7f3b8f057f9dbec2bfced8e15fe768a0aff3b37057f9d8f42bfcec6e15fe768a0a7f3b1b84ff9dbec25fc795812fe3ca7097f3b4504bf8222825fc091412fdf64d097e8a2684bf7d92425fa289212fe7637097ed61b84bf6a0dc25f99c6e12fcca37097f3b7d847f8f2b023fc794e11fe768a08ff0445047f8122823fbec9a11fd144d08fefb24847f4512423fcec6e11fdac3708fed41b847f else 0x338dc65fced1431fe048a18fe8a248c7f9d8dc63fb506e31fcca3718fe8a248c3f6a0dc61fa28922efe771e167f1e560b3f8f29c59fc78ee2cfe3c76167efb248b3f4512459f9b8922cfcca37167f3b8f0aff9dc7855fc794e2afe3c76157ed61b8a7f9dc7851fc794e28fe3c76147f3b1b8a3f6a0dc51f9946e28fe3ca713fe651b89ff7d9244dfcedf625fe3cac12ff1e53897f9da284bfc111425fe048a12fefb26897f451344bfbec9225fd144912ff3b1b897f6b0dc4bfb506e25fcce3712fe651b897f9dbec49fced1424fe7637127f3b7d88ff813ec47fbec9223fe771e107f3b7d883f8cb5041fced8e20fe3ca7107ec753883f9da2841fc091420fe3c76107ec73b083f) else (if page < 12 then 0x639946ffb10ca37fd58651bfea7328dff521946ffa64ca37fd18651bfe8a328dff3b9946ff9d8ca37fce8651bfe71328dff341946ff99cca37fe76641bfe65320dff6b18c6ffcecc437fda8621bfe65310dff329846ff994be37fdac5e1bff3b2e8dff6a1746ffa9cba37fcec5d1bfed6290dff9d9446ffb50a237fe76491bfefb248dff6b1246ffb509237fd14491bfe6e248dff339246ff9949237fca2491bff3b240dff9d9186ffb508c37fcca461bff3b1e8dff538f46ff9947a37fe3ca71b7ec7538dbf539746dfbec9236fd14491b7e6e248dbf289246dfa9c7a36fe76371b7ed61b8dbf6a0dc6df99c6e36fcca371b7f3b1b8d7f9d8dc69fb506e34fcca371a7f04450cff else (if page < 13 then 0x6a3186ffced4e37fe3ca71bfed6538dff6a29c6ffb1d4e37fe76a61bff3b520dff6a2906ffced3237fda8991bff3b450dff812286ffb511437fda8881bff3b3b0dff8f1d86ffb58ec37fda8761bfec73b0dff9d9d46ffcece837fda8741bff3b388dff6a1c46ffb58cc37fee6651bff72328dffb81946ffdb0ca37fed0651bff64328dffaf9946ffd74ca37feb0651bff51328dffa59946ffcf8ca37fe76651bff39328dff9a9946ffcc4ca37fe58651bff26328dff921946ffc8cca37fe3c651bff19328dff8a1946ffc4cca37fe22651bff0e328dff821946ffc08ca37fdfc651bfefb328dff6d9946ffb60ca37fdac651bfed4328dff691946ffb40ca37fd98651bfeca328dff else 0xa4cec6ffcfa7637fe7b3b1bff3b9c8dff9dcd46ffcee6237fe77261bff3b918dff9dc886ffcee3c37fe77191bff3b898dff9dc486ffcee2237fe77021bff3b808dff9dbf86ffcedf637fe04fb1bff3b6d8dffb9b506ffdc9a837fee0d41bff6c6a0dffb5b506ffda1a837febed41bff5d6a0dffac3506ffd45a837fe96d41bff3e6a0dff9db506ffce5a837fe6ad41bff346a0dff98b506ffc99a837fe48d41bff236a0dff8f3506ffc71a837fe32d41bff146a0dff89b506ffc45a837fe08d41bff026a0dff7f3506ffbeda837fdf0d41bfedb6a0dff6cb506ffb59a837fe76d31bfed4698dff9db406ffb51a037fda8cf1bff3b660dff6a3306ffb519637fe76c71bfed4638dff))) else (if page < 16 then (if page < 15 then 0x8222893fc091449fe008a24fefe45127f7da2893faf11449fd588a24fea745127f5222893fa6d1449fd328a24fe9645127f4522493fa291049fd148624fe8a42927f4520c93fa290249fd148024fe8a3f927f451ec93fbecce49fd146724fefb32927f4519493fbec9a49fd144d24ff3b8c923f9dbec91fced3248fe768a247efb24923f4512491fc11f647fe088a23ff3b8c91bf9dbec8dfc09f646fe3ca7237f3b4c91bf6a2648dfced1446fe048a237f193291bf4c9948dfbec9246fd1449237efb24917f451248bfc11f643fe76fb217f027d90bf7d92485fbec923ffe08fb1c7f04450e3fb9cec6ffd767637feb93b1bff589d8dffab4ec6ffd467637fe9f3b1bff4b9d8dff else 0x823ec95fc11144afe771924ff737d927fb93ec93fdc1f649fedcfb24ff687d927fb0bec93fd75f649feb0fb24ff557d927fa5bec93fcedf649fe72fb24ff377d927f98bec93fca5f649fe48fb24ff237d927f90bec93fc65f649fe0efb24ff047d927f813ec93fc01f649fdfcfb24fefc7d927f7dbe893fbedee49fdf6f524fefb75127f7dba093fbed7849fe3cac24fefb56127f8f29c93fbed4e49fdf6a424fefb4d927f9da6493fbed3249fdac9924fed44c927fb9a2893fdc91449fee08a24ff6845127fb2a2893fd851449feba8a24ff5845127fa5a2893fd191449fe768a24ff3945127f98a2893fcb51449fe528a24ff2445127f91a2893fc651449fe2e8a24ff0745127f) else (if page < 17 then 0x9dcc515fcee5a8afe7723457f3b9122bf9dc6515fcee2e8afee702457f728122bfb840915fdbe048afed102457f658122bfaec0915fd62048afe9702457f468122bf9dc0915fce6048afe7102457f318122bf96c0915fc92048afe4702457f198122bf8c40915fc5e048afe2b02457f048122bf9dc0515fc0a028afe76fe457f027f22bf813f515fcedf68afe04fb457f3b53a2bf8f29d15fc114e8afe04a7457f3b5322bf9da9115fc09488afe7699457ed44ca2bf8f29d11fb513288fe768a447f0445223f8122911fced1487fe768a437f024521bf9da2907fc091483fe048a417f3b639b7f63ab0dbfb1d4e6dfe76c7367f3b639aff63a9cd7fced8e57fd8ea72bfec753953f else (if page < 18 then 0xab4edf7fd5676fbfea93b7dff4b9dbeffa4cedf7fcee72fbfe77377dff3b98beff9dc8df7fcee44fbfe77217dff3b8cbeff9dbedeffcedf6f6fe76fb7aff738f29ffb94794ffdc63ca7fed91e53ff688f29ffb3c794ffd763ca7feb71e53ff518f29ffa5c794ffcee3ca7fe751e53ff358f29ff98c794ffcc23ca7fe491e53ff238f29ff90c794ffc823ca7fe3d1d53ff1e8da9ff8f4694ffcedf6a7fe3cfb53ff1e7ca9ff8cb594ffc65a8a7fe3cac53ff3b8f29bf9dbed4dfc794ea6fe771e527f3b7da93f8cb5149fc794ea4fe3ca751ff3b8f283f8f29d41fc794e9dfee73b457f5d9da2bfae4ed15fd62768afead3b457f4b9da2bfa4ced15fd1a768afe8b3b457f3b9ca2bf else 0xb9cedf7fd7676fbfeb93b7dff589dbeff))))) else 0
  | 9 => if page < 6 then (if page < 3 then (if page < 1 then 0xa4ff46fe83fcfbf9bff30fe5bfca7f937f22fe43fbeff7c7ef7fdebfbc3f5e7ebbfd73fadff547ea7fd4dfa97f51fea0fd25fa2ff457e88fd0dfa0ff36fe6bfcaff92bf24fe48fc8ff917f217e38fc6ff8dbf1a7e31fc59f8abf147e24fc47f87ff0e7e1afc31f85ff0afe12fc21f837f067e07fc09f807f else (if page < 2 then 0x45047f26847f24847f1b847f7d843f9d837f8f037f7d837f6b037f6a037f63837f56037f53837f45037f3b837f3b037f37037f26837f24837f1e837f1b837f53833f4501ff24813f1b807fb9cedf9dc8ef91beefa5a9fea5a9ef9229df91a9ef7da2bd91a2af5222beac127b92125f91926f81126f4c91bb8c8dfb918def7f0dfb4c8dfe388dfb230dfb9d84af9d845f7d845f56045f53845f45045f26845f24845f1b845f56037e3b837e3b835fb9cecf7da2bc00573f00557f0052ff0052bf else 0x520dff4c8dff450dff3b0dff3a0dff388dff328dff310dff2e8dff288dff248dff230dff1e8dff538dbf248dbf1b8dbf1b8d3f450c7f1b8c7f8f0b3f248b3f8f0abf8f0a3f1b8a3f9d897f7d897f56097f53897f45097f26897f24897f1b897f9d893f7d88ff9d883f8f083f7d883f6a083f63883f53883f45083f3b083f37083f24883f1e883f1b883f5387ff45073f2486bf1b863f9d85ff9d857f9d84bf7d84bf5604bf5384bf4504bf2684bf2484bf1b84bf9d847f7d847f56047f53847f)) else (if page < 4 then 0xa5927f9d927f9c927f98927f94927f92127f91927f8c927f83927f82127f81127f80127f7f127f7d927f5e127f56127f53927f52127f4d927f4c927f45127f33927f32927f26927f9d923f24923f8211ff9d91bf8c91bf8111bf7d91bf5391bf4c91bf4511bf3291bf2491bf24917f7d90bf820e3fb98dffae8dffac0dffa88dffa58dff9f0dff9d8dff9c8dff9a8dff988dff930dff918dff8f0dff8c8dff898dff888dff810dff7f0dff7d8dff6d8dff6a0dff680dff660dff638dff538dff else (if page < 5 then 0x7dbdff7dbd7fb9a9ffb929ffb629ffb429ffb3a9ffaea9ffa8a9ffa5a9ff9da9ff9aa9ff98a9ff9829ff9229ff91a9ff8f29ff7da9ff7ca9ff6b29ff6a29ff5629ff9da9bf53a9bf9da93f8f293f7da93f6a293f53a93f53a8ff8f283fb9a2bfaea2bfac22bfa5a2bfa322bf9da2bf9ca2bf98a2bf96a2bf91a2bf8ca2bf8ba2bf8122bf7f22bf7da2bf53a2bf5222bf4ca2bf53a23f45223f4521bf4520ff639b7f639aff6395ff8212bfb9927fb9127fb8127fb4127fb0927fae927fac127f else 0xb9ceffaeceffae4effa5ceffa4ceff9dcc7f9dc8ff9dc8bfb9beffaebeffac3effaabeffa5beff9dbeff9cbeff9bbeff98beff91beff90beff8cbeff))) else 0
  | 10 => if page < 1 then 0xb9ff5dfe97fceff98ff23fdf7fa9ff527e8afc93f91bf1bfe25fc41f84bf08fe0dfe477845f else 0
  | 11 => if page < 1 then 0x3f else 0
  | _ => 0

def poolFormat (k page : ℕ) : ℕ :=
  match k with
  | 7 => if page < 1 then 0x1545515455154430c4310c4310c4310c41d else 0
  | 8 => if page < 1 then 0x4310c4310c4310c4310c4310c4310c4310c310c4310c431 else 0
  | 9 => if page < 1 then 0xc4310c4310c41f else 0
  | 10 => if page < 1 then 0x1f else 0
  | 11 => if page < 1 then 0xd else 0
  | _ => 0

def counts : ℕ → ℕ
  | 7 => 849
  | 8 => 1156
  | 9 => 340
  | 10 => 20
  | 11 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 512
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 9)

def takeRaw : List W → Nat → List W
  | [], _ => []
  | x :: xs, m =>
    let rest := takeRaw xs (m / 2)
    if m % 2 = 1 then x :: rest else rest

def pool (k i : ℕ) :=
  let fmt := field poolFormat k 10 (i/64)
  let v := field encodedPool k (fmt/2) i
  if fmt%2=0 then decode (k+1) v else takeRaw raw v ++ decode (k+1) (v >>> 6)

def bucketCount : ℕ → ℕ
  | 7 => 331
  | 8 => 490
  | 9 => 197
  | 10 => 22
  | 11 => 1
  | _ => 1

def slotCount : ℕ → ℕ
  | 7 => 1193
  | 8 => 1771
  | 9 => 711
  | 10 => 81
  | 11 => 2
  | _ => 1

def shiftWidth : ℕ → ℕ
  | 7 => 7
  | 8 => 7
  | 9 => 7
  | 10 => 5
  | 11 => 1
  | _ => 1

def targetWidth : ℕ → ℕ
  | 7 => 14
  | 8 => 15
  | 9 => 13
  | 10 => 9
  | 11 => 1
  | _ => 1

def shifts (k page : ℕ) : ℕ :=
  match k with
  | 7 => if page < 6 then (if page < 3 then (if page < 1 then 0x22828a0e340000014187002c28008104000200901041c00c045808b00101040a000020c0000b021800006183000018091020020c021d407 else (if page < 2 then 0x121ce800c000060404391200068600280871a0000502002000e002800008180000810212140001e081850e000031200706000441b2004009 else 0x60048a62080931600882482c01b0c3810402241980814081000410118080070c0808207500260e087013a786811c5928a140400f2228404)) else (if page < 4 then 0xd400c100982000d401a0804e8f0610218044000d0800000640400108400080e2c6010244c120016f802600f80200c0040028003102000b else (if page < 5 then 0x86057ab02000800201713002018002082327620088000c6060094e0050c40060628086ba0080000357030400184280c780b4180004616583 else 0x5600516409404110aa))) else 0
  | 8 => if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x180240c7020000602040e1840084105201c1024000002120c001080c30106088820000080001400d0e04180000c83404000820030003 else 0x8100820e04085004810e5600182000da870000202240c003060c181147899d0a00000082c001120090004100800c0008100002861c00888) else (if page < 3 then 0x804414066838104000860434c06000418502382801600000040538008141a900081015a007000200e00020c40000043800200a800400012 else 0x81c0db12502060e9c482001410000044860404007044c6082a0478702180800618806280020f285408f0018084064800102104970604d03)) else (if page < 6 then (if page < 5 then 0x80c0af1e286941404300000c3000600109040113c0a447b416301011a0d38400140000028a0c001043f0a1cb870400c870400001041c386 else 0x200e2043843cd050102780083408383125000704041121200085142840228080000edc1810c303070a04288020d0000aa80080e60032) else (if page < 7 then 0x440c5141a00d8e001c5121c6cd80043c7001208180180020c06229180c3810900a80090c1ce8f0e980870c0c101006828b0804402160000e else 0x4028640080240410d120021a0c686150000500033288900040371e0498014e82053e2410d))) else 0
  | 9 => if page < 4 then (if page < 2 then (if page < 1 then 0x1620003000c4040e4c38302003910010702061458020100032a380800a0c0080000082081c0830a080000204500104c0010e04400000048a else 0x21208000150014983b05cc800e3c18b0800017000008404080800624213180808704000120c30d0714080891e000830200d840e00205) else (if page < 3 then 0x1e0001a007c1040a60c17040098f2c002884c40916120860b001c0422a00e0b24102070c140831800200020828906080a14800800161c09b else 0x1f0000283)) else 0
  | 10 => if page < 1 then 0x8034801200e74be22020aff780f else 0
  | 11 => if page < 1 then 0x0 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 7 => if page < 19 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0xcd800004d008100f82cb77a412e46343440b29d9206ed025491c20d06ec295605e1a3089829b13c400007340000b8804706bc2ee088406b6cc003ab1d462a27f1015053a17d0018f0b65e80a615be4af6c14200086822f01800f60c298622389800067c23504c5150241d3190cb01f16 else 0x5ec74d00e6a590a3c000097c1ad2d3c40005010cb02f42ae0ad813c0458000000000510003361104044abe00d608f00a30a8c40000000d01584c0002d409f606a56200002b8082805209c5c93100014b09301b843d14630289c0004a90086c6c400042a32b01492a2189003693f5915a) else (if page < 3 then 0x24e17a83180c3d816913847114b8317084834b06e91f4000000000000000000000043486c9b380070462346034412700001f20ccc1e6036907809fc13e00001e50258000076c80000002c7600000007708578714000029149c153488001fc00009f40000d0c0000bb400005c00ea1 else 0x9e81d10b541cd42cd90964c01da056cddd09e01c705c41bd00000000568850000000b06b2092081026a02a052020000000c980b34000138019862d200016e89d0435100000000709fb11a580006c621b084401c000031d062400000000720752aef00003350af05a006cd00005644000)) else (if page < 6 then (if page < 5 then 0x16a0bc13681ec066805b088c2430c9c30107112eb00000e0600013a03b042d66400000408287000019103a41d48d203370790acc00000000000000000004d00b1c9113de544000000009c000000001d0047aa2906503081b500bf069c12600a014441140a50cec26b00c401cb6f02810 else 0x5282ac0d242e30d082202030037946c0d86a002e00a7872f0a745ac264c18305f80198aec20203342e9009c31600c848e5c5429962a955781a874a020911745201dc0a5d8fe9c9471360280dd4c9068e0d000003c10085006240183cc96d90d01f6465c32804e42b265a826314668b88) else (if page < 7 then 0x2a9e570a4c199008c6546ba011027f82c3692c3310c882ec00e2dee0314020b0000f994912fd077829109782f300000000ab428d0bc826707ac0953618137053c10e03fd1fa0754036257c400076880d046a00008300376406d3041440ce100012b40000fa2c45a190422a326a901a20 else (if page < 8 then 0xd3050c2490131c791000275000000000002cf000005f0000000062000001c00000628000000000003185c80b5c08f836c1030b401052b642901ad4155235d0e81a5181a33ac2cb67bc021279000406d005c02c848a0a142af0d105c84b258000ac00fc321c2650 else 0x59641a45acc5e02f871f073c0df60ae5c306a42df057231e0a301b445844000bf02ba163c27b00000ac500018409684299a2c1b26af812d499801fa46a800083806702ad2f50b09ae60a7c00006a8ac160001c40aac24204bc22b014532e08ec0000304218003c23d6a0c00000000a70)))) else (if page < 14 then (if page < 11 then (if page < 10 then 0x8d073f0234ee508f98e7080c02e705151627f19fd70481e70d140192d3c14108d009a533c30305401602cc80610449111600021d09c9f3c00f697c0afd9490d2c5e80888313791861f26e524817d45310b74099472400005ddca1615805418045c041a04b9069809909b81ff04b427e0 else 0xb900ed00000000c1c00000320134000172978c2a802c1c00030061e00002a60000089087057f00001034b586060b4833800002db16140000ad1800089c20508b010c08e980000000d403e215801f60154ce415680002170654000009000003285e2078019805e08f6407500210712b36) else (if page < 12 then 0x8948530bd020809a02a906e8181018913b01fa07b00aa24a0044302067414c030c25365a64b1077c2c567a0ac464cc3210aa06b90c8031c10002b168e02f107cd0fc937594740000dc06a82f603f501486d42e70a9c52946e026f00dd29675d24e40c3982606a0af0000000000002820 else (if page < 13 then 0xa182de01e8000000032d043427710001210d300000850036300000000000cc1000000000005d0000000047ec00058c74e09ec51db2b5a51639407713541db028d00000000e246381532592064119429a06702931adc0f019b00b45a484a0700000001f4acd04161ce022004217b401db else 0x67818700002c06a344000c3594606941cc00cc06f1af4528042e9f369d440006dc1b24365857a5781d6059cf470c3186d09341c20431151026840000bc8448451a561be41320000000000c40007f54000d3440001960000cf80000cd01290a8c00000002a102dc2d8040880000003410))) else (if page < 16 then (if page < 15 then 0x3d500000000e104886c8721020b08cdcb6031c10f82a52250a1c4c21ba81eb24ac10867e197665a21d805d5c4a74a80ef083c1c008d99ae87e5e40600024f6d244b4722c13f0748684097023f6bdc15d99cde5b010022d0598952862c245012417381d000000000d2007265d08802090 else 0x20c180008815220001f04a61cba10001af229071c0c002890c6814205001dd2d40000000000008c003b40002070000000090593504c921303ee1360024400063010408dc2a01c942160c8c2dc09a462e04f40590be826106e42aa62a59ab066c260141880002300ae732061500f00000) else (if page < 17 then 0x166441a7001300002880a944bb026c000060822a007ac3f100007c2b19897600000000000ee100000000002997000145005093b4bec30967640147941873112da52640672a0000329000015505800100af412c0000306016116b1bfc1e1000026d151c000000011140000430a3067c0 else (if page < 18 then 0xbf450023241c103d1eda09d804805e5b3a006e4e30000000075c16533986f3174c000013c08209e840e0b4c25809e4712700009e548c16421d8113a0015f7507411368a01158990098106991b42405b6127500006580f241b056a2cf403c469015486841de2a7804679540de445d92f4 else 0x28a07180000c418f3821806e05b20c4125250f2bf81ca01541be000012506fc1b08000000000023900002620c502d11472c0000000d540c1ae1087c00000001cb016180008402310))))) else 0
  | 8 => if page < 28 then (if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0x832028e9e58047155411684588bc24600077c0f381cd0622023019a9388123c02980bd004b0000059c00000000000000812fa00000000d0598d83a900000000121047312a480000210c44554200000d98b2702c40000024080008b25141063800000000f38048842f08d80bc81e28206023031d00bf84430 else (if page < 2 then 0x41646581d143130399000000003cc07780e520000000059c03980f90204107e0031a04312904428045891022a60000000000047b48388f6818e806102e80bac21dc000000011b801d0000000003e0039021b461205940cec00000000000000040d05a0ca28144b40b00000c40932800000762000120017e0 else 0x31c0ef81ad000000ba000000000000000000020c026267e8000000000000291000003480fe28a8c000064904906210c2817a01fa11160fcd16c01666802c99c20a100006f2040800000000000000016e8426025602481e2015fa82023a0000033587444f5e553b1a400de00000ca823063c840000b001540)) else (if page < 5 then (if page < 4 then 0x240c6b1400012718ca0a70177015702380000052000004f4919085b83d724c6072e947045c00000f9e05401be104004ee00000000000045592180cd00000a78000000000b800000e1039200000a48000000008f40ff600003e8014480001ef023e06bc0e541210b2ca046ced0000000000000f54c4821c40 else 0x11e018815d828747f60895474847503da100da0a803701c30b7c475839c243404f802c83dc087200000eac40266460a21011322e506825e41e88000000008b500000ac00000000176830d02a6d080000017d0302c5b913ca2cd40000b8444d8000082223261eca000000004e0c00000000000abd09d41d18) else (if page < 6 then 0x75c0d5aa7d047e259462d02c9066204d4416802f01060645827816e06540490158b0d7033210ed0a8044400a6c0000000000000000000a233d8000007d0000001873ba0a059eb9a18033c009c491aa820552cd4c05480331248865c603b800000006341cc945f02aa8e340ab341d07f800001de83cf0 else 0x6fc118000002dd40000cc800002c406f0094c0fda02c0735000000002d200280d6c087307c60000e08223001e844eea605744192645e891442a0256076c857a80001af7470d11049e82c700000cd0000006305e6108419e935801ea08a1dbd032905740a3009783ef413e07c015b00000000037840003752))) else (if page < 10 then (if page < 8 then 0x772800016b00ed000000000c5347f000008d591080000898c8581048c6807f08db60988adb116a2b441e681ba160a0e940d38101287647ec090235108fc00c45b88ad706c00cbda1b835c0338074c1ab047c43d00dd60f9a43d159c88d9d8f0000011a8e320e4020a15cd10d51b100cb110ecce980001137 else (if page < 9 then 0x6d4501822373f406e4527090897ab262de40806887320780872819d03862d1819f0a0f138e21380d93ac50280e04c4f14261462a0e185ed209801e80ec8189000000c010199778bdb038a2edc000024901f800000c5b000030400001cd80e320000d1c22bbbe605f60d068ff0065614e012443c8bf20 else 0x3bc320c155b23b856000145120c2d073a285c4bc8a9411340c6813f30c801d411bc08d023753080ccd062844210000dac137006c000007f015b8341000010d809b03e0067e0ea92230800019e0f1c227a008003542f8a410800070e06c5d9e084690da0950400027f603e0c5817c0000000008381b5038b0)) else (if page < 12 then (if page < 11 then 0x860dfc0688200056af1e10000204050a052d9e101b7117d0000000009e86e0113403d341a554011999ae81d80000035183b81a5153c23641e80459062000000ac211368e00f50800029315d22ad58d38a3d00000a1d80001d900000e040ef016306f60d0011b2800000000000f301e382e0037019084550 else 0x7ee043d92f027367be0429800008a07dc0cb412b88c40080a96c19a20b8053a20001eb008348f60e280b98082737000001be000005280000235814102980000000020310a491900000194600003bc000000a151007fc1c7833002d410f005709ba0002000020c2249100001d808b83a8017cd058040b41d8) else (if page < 13 then 0x66605858e30166424a8fcc175001583d4000020e28000794000006183ea46aac48440000000156247481f3376645e0d7c0a322be02c811b404031d005fc0c3023e280002e330a103a80a510f0320062401f303a2400021880000000116017f8000079220001d5015c45c820000540a590012276d0c18bc60 else 0x2048d1d2c0bfd92930e9090902e30224ecf809490f264d00e920420222420a022422b20db91a4acb842403f5085008485cc443d00000d34000014f6184057ee3300be45a143e6170013f600000000cc045a40001044086b4320000000002f12f10660200020b80e002604a7c086308513f750d40950a0c0)))) else (if page < 21 then (if page < 17 then (if page < 15 then 0xfccd9c00748a6444cc00015938000000109417b02b4151a0cbe94a80f063c007961350453485608bc51c83e708a606d81cf833aa0b60fa2400000001ce03300550b4405c408a182503a747900cec23481a8040a29ac0498a9000000f94019043f05a24f000dd8374077490a805f8b1807da04b418a00340 else (if page < 16 then 0x5c20000000000001dc4dd0459804708e4100184e900000000c8015823fd21820000000005804f880840a138bc166c10ec0ea000000000a3c0e088990000000005f001c05d8000000000000000000012201db0000112c053927840000e0c000000004c8c034000042f112c2acc1530024648e05e01a181841 else 0x5f449a40e703b800000ff4e1f00000222cc144f7c000083641fc020b9a015780e0010401d6000009c41c992de05f80288071c27403fa00f50000087782440bc418005a05f20d5000001166000035421a03fa00000ae408c830e0000082822801c70032800000000000428c2bc23e8335082e91780f080000)) else (if page < 19 then (if page < 18 then 0x119c0aed000000000000fdc12c4456f1081a781f7049021c40d0837d06e6049410fabe1059a07e45e1847443d8096c567c06a0452c2180000393843e905523e0055628602859b080000000110d1b783dd3710abd406709d500000c041103319170a04e25433143404a05a20b4800000000b6480000030 else 0x6e208081dd027602de10cc0f703bf05b40c2c2341114089ecb811df880000000d380000000067a108c11aa23740540b0810388000398401992309cb05f505680a3c27701ac1015800000400000e7a40001dc07b0800004b817b11a00d8c23e0a1d443caab1972c45166dc0c701f8007b0474260c00000000) else (if page < 20 then 0x24627529ee2000000000001b6d0b91000110422b304a10000000085b2220000000000003020479298408ec46102ee073000db16d14a20e4410a8376a3820e2640001bd1796837e545c29b045a000008f893986a00e9816183f605aa110015e8000024c000000003d7800011dc5d081ef0312caa064000160 else 0x30421f59f2036807600b0401a930806d20e6081b014d0708275493db1a2040a08c9c0001d207f206b5537832504940ee4174028346e407e010e2bd2059482b404a0a1003a7462022c119a0194034e40002fd04c690a4000021110dc01911cbc000064804cd1c10bd90498068c096024f076e800000000000))) else (if page < 24 then (if page < 22 then 0x78e80000a70000082640000000365001eccac20e034203202254490833620000000099822514cc0c5c0e78297184811b4826817c04f800a00cf83ae00000fb00821280600007920ed03b541fe066c1170a91184e8f4c0da827502e40eec216025516a4103c1d603b607de0ae0157310718628df85122ae70 else (if page < 23 then 0x32e0000109a24c164411e40eb100004d84b244a882d4047a261c20b213200782c18129034800ac000019c8145400009819208850425011c415181e7440203c58000000035ce8d189e005203da8000126803c004d201c0ef898c06ee037400003490458f16c03993f803802e8c03a300000000a900be89e90 else 0x38a120820a43b106aa909c1f90b64063e0d3013801db62000a118f2945d08a403ec8e4818178250afc47210880098107c0c0004413940c641b723ea08700b2063b000003400f8c00b808646d810e8125894a6658d1110d308f608342f411a2833683002e1822280a01138815100002dc6000102420703900)) else (if page < 26 then (if page < 25 then 0x31e083422ba8f361c4028d9ff0af002b2c8c40000190088e07d40000337028810b11ed9389b29e87184b023d648940a880ce8bad059651695dc20d2100010c01ee8b03046e000002f802b03ec0362235029a100006981a50109671d26d2470930401ee05b085d033800000000169a39606be20001d783c90 else 0x7d207ac08300ec001606f0224811b0808d1f8611042e01760f7905b02cc63ad034ed0d0a5018ee07c405e82c611604970117a86704da0b004df8051655a1070435841306ec00a60bb03a9489c000002b839c81b5200005900fd02fc2000239802e089026c1d7b834b08c40318152b08e02b6e9444d500000) else (if page < 27 then 0x8b000007c9000016100000d480000326c0001bc0bd481dc10fd205018660cc1199c0e827246cc00001d38375025c0000206029b146e24d003bb41b05320c985c200b00220c00011c3a96004e061414183f108c600e00e8821917002c1c1578408775089685d00039135023e80bd819b12d711e01ab841e0 else 0x7f11f5832802060ed40ba813707284300009025d04b00c3c1f103ab02fe21c09ffca7d43c106205ac83c10000071054121f4434a0d540000000072e5065119899471680ecc17d01f90000078c80000000))))) else 0
  | 9 => if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0x15826c02eb4d32c41c711903383e804e05206590080decc463e08e01660cc09283e000c087089034c4000a706b0b222a007754100cd8d893723480000001010270cf42a023d178031000012c04eb499a30000000053456e153071941e45d41446a8000020cec3 else (if page < 2 then 0x93a3fa0c20ee08b8bf8936859000035447e11c06ec47c2222ab0000274146316821089623613906913e225e08917584d005e88b13e820440006510eb1d997234e43cbce8022948066846823820904d802808cf0c02201e85d922b76e900001008307984910000000 else 0x9e028041e000069023c09e24013f84b94f409e04a23665c804d000000002812945e0cec000022100037c84000007623dc22600009401a82a4254038b95217400000000f80000a3000000000012900003a500000e00004580780c5072c8000f00ef297b0341280000)) else (if page < 4 then 0x9ab9d5c9620000dc366da50296580bc10000ac618323016012544883319d907a54b804c2a0cf1488951c22a00000a939e05b4fd0a6051c56a2cb073846c8000df81a827180c2ab460081069ed1006451b400000006982f89ae14b00003d400012d06004382920785 else (if page < 5 then 0x6504fc40000763b23240cc0000a838000a6108614a1e99f046415d81440c00ee45f818c25604776f04dc1420ff09aa4501e808a13d21940000bc65781ec20609743728dc00202224b34b082d2000a02090de0278121050d2a08d265c050410421998301e598e10f4 else 0x8e8b0598c00007f185600e0c8098021000021f67481058160e1049a15c1888ca10d403d89e0cf088a8000392b926701c94b604c1a50d4423c14d0739480182036048042980006f7240d1d40000007c22184dc33b27e20924000000383000054c00069220c68d0720))) else (if page < 9 then (if page < 7 then 0x2c417857941163909fc4ba00006101244000dc0790b601fd200000000010e2b508ca0001882a9600034a80012e082814e8eac0009980000000ed0250000050e0006880000aa088085800021a200081a19863a0cca96914451c11049105414a011623d8bc0d32c680 else (if page < 8 then 0x184a826210006322c88720b980002a00642e803c252467000008ead1880013500003d81fc22f05638689de0c3076a10c0000a00528b505b40d40a904b926a20009f03da44cd32000032e1d80e604624d08c814740000141d849563100f062c8cd1538cbdcb04000 else 0xa274140022812407e109008420812701f088c8000bc00000000da82c47c1a900440b602b92e41c045a02f849183cc18077a2b821e00004209660668c1aa1000016407c02b0c85954cff42fa51024ece428684fc17a0d0084b4b8a9e86b114800009811f1)) else (if page < 10 then 0x46843890a07772e0518118cf58a281ac0000be0a700001f120008ea46e00008b00003a8168011000040800000004c000000000003d380007ecf9078805adae200075881d0000b145f438a00000002484a5a4600c06012d503400008a0d0c22200000000000740e48 else (if page < 11 then 0x4ac80000005300001fc11700004d54d8b4f00003a900003b02a150017a8b781881cc00434a02bc5085c001f7a73358022e0006408000ce20005683f025c21701a136c07e86912ea26923c25e0530bc800000000a1050614e000a40cd5a228fb039200022909d4 else 0x28853e00001901140a02000)))) else 0
  | 10 => if page < 2 then (if page < 1 then 0x480000000681d0011410c81a426309502310609c100b470b1104c78ab80acb628080c099203d222a23d2444f007b22082763c4c000c6504584a0018c5d26d8602c060f0490000000 else 0x1210026000240000000c5000000001082a00072) else 0
  | 11 => if page < 1 then 0x0 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let h := key xs
  let b := bucketCount k
  let shift := field shifts k (shiftWidth k) (h % b)
  let slot := field targets k (targetWidth k) ((h / b + shift) % slotCount k)
  (slot / 16,slot % 16)

def s45 : Switch := ⟨16,0xffff0000,0xffff00000000⟩
theorem s45_ok : s45.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s45]
  | 2 => [s12]
  | 3 => [s12, s45]
  | 4 => [s01]
  | 5 => [s01, s45]
  | 6 => [s01, s02]
  | 7 => [s01, s02, s45]
  | 8 => [s02, s01]
  | 9 => [s02, s01, s45]
  | 10 => [s02]
  | 11 => [s02, s45]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s45_ok, s12_ok, s01_ok, s02_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def goalColumns : Nat := 0xfe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080fe80e880e8808080
theorem mask_valid : goalColumns = Vector.lanes negative (fun _ => target) := by decide +kernel

def pinBase : List W := [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff,0xffffffff]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut0 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor2.target 0x5050505050505050
    (fun r => ⟨(0x10c18e51c59e92c9aed3cdbe >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 5 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut1 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor2.target 0x4444444444444444
    (fun r => ⟨(0x8a18e49a59e8aa9aecbadbe >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 5 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut2 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor2.target 0x3030303030303030
    (fun r => ⟨(0x10c14d51c55d92c96dd3cd7d >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 5 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut3 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor2.target 0xc0c0c0c0c0c0c0c
    (fun r => ⟨(0x8a0cb49a4db8aa8ebcbacfb >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 5 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut4 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor2.target 0x2222222222222222
    (fun r => ⟨(0x4914d45955d86996dc79d7d >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 5 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut5 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor2.target 0xa0a0a0a0a0a0a0a
    (fun r => ⟨(0x490cb4594db8698ebc79cfb >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 5 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut6 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor2.target 0x5555555500000000
    (fun r => ⟨(0x8288aa92c9aec38cbad3cdbe >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 5 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut7 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor2.target 0x5555000055550000
    (fun r => ⟨(0x41849a51c59ec38cbad3cdbe >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 5 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut8 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor2.target 0x3333333300000000
    (fun r => ⟨(0x82886992c96dc38c79d3cd7d >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 5 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut9 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor2.target 0x3333000033330000
    (fun r => ⟨(0x41845951c55dc38c79d3cd7d >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 5 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut10 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor2.target 0xf0f0f0f00000000
    (fun r => ⟨(0x8288698aa8ebc38c79cbacfb >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 5 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut11 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor2.target 0xf0f00000f0f0000
    (fun r => ⟨(0x41845949a4dbc38c79cbacfb >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor2.raw 5 (@Minor2.lower) Minor2.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut12 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor1.target 0x5500550055005500
    (fun r => ⟨(0x20a30e61a71ea2ab2ee3af3e >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut13 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor1.target 0x3300330033003300
    (fun r => ⟨(0x20930d61971da29b2de39f3d >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut14 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor1.target 0xf000f000f000f00
    (fun r => ⟨(0x20928b61969ba29aabe39ebb >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut15 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor1.target 0xffff00000000
    (fun r => ⟨(0x8218a39259a7a29aabb2dbaf >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut16 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor1.target 0xffff0000
    (fun r => ⟨(0x41149351559761969b71d79f >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut17 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor1.target 0xff000000ff00
    (fun r => ⟨(0x20928b30d38fa29aabb2dbaf >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut18 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor1.target 0xff00ff00
    (fun r => ⟨(0x20928b30d38f61969b71d79f >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut19 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor0.target 0xf0f00000f0f0
    (fun r => ⟨(0xb2dbaf9259a730d38f105187 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor0.raw 5 (@Minor0.lower) Minor0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut20 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor0.target 0xf0f0f0f0
    (fun r => ⟨(0x71d79f51559730d38f105187 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor0.raw 5 (@Minor0.lower) Minor0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut21 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor0.target 0xcccc0000cccc
    (fun r => ⟨(0xaabbaf8a39a728b38f083187 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor0.raw 5 (@Minor0.lower) Minor0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut22 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor0.target 0xcccccccc
    (fun r => ⟨(0x69b79f49359728b38f083187 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor0.raw 5 (@Minor0.lower) Minor0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut23 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor0.target 0xaaaa0000aaaa
    (fun r => ⟨(0xa6bb6f86396724b34f043147 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor0.raw 5 (@Minor0.lower) Minor0.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut25 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor4.target 0xf0f0f0f000000000
    (fun r => ⟨(0xdf6d749e6964ffef7cbeeb6c >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor4.raw 5 (@Minor4.lower) Minor4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut28 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor4.target 0xcccc0000cccc0000
    (fun r => ⟨(0xdf6cf25d64d2ffeefa7de6da >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor4.raw 5 (@Minor4.lower) Minor4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut29 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor4.target 0xaaaaaaaa00000000
    (fun r => ⟨(0xdf5cf19e58e1ffdef9bedae9 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor4.raw 5 (@Minor4.lower) Minor4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut30 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor4.target 0xaaaa0000aaaa0000
    (fun r => ⟨(0xdf5cf15d54d1ffdef97dd6d9 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor4.raw 5 (@Minor4.lower) Minor4.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut31 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor3.target 0xffff000000000000
    (fun r => ⟨(0xe39ebbf3dfbfc31cb3d35db7 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor3.raw 6 (@Minor3.lower) Minor3.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut34 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor1.target 0xf000f000f000f000
    (fun r => ⟨(0xffef7cbeeb6c7de75c3ce34c >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut35 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor1.target 0xcc00cc00cc00cc00
    (fun r => ⟨(0xffeefabeeaea7de6da3ce2ca >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut36 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor1.target 0xaa00aa00aa00aa00
    (fun r => ⟨(0xffdef9bedae97dd6d93cd2c9 >>> (6 * (r.val % 16))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor1.raw 7 (@Minor1.lower) Minor1.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut91 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor12.target 0xffffffff00000000
    (fun r => ⟨(0xe39ebbf3dfbfa29aabb2dbafc31cb3d35db78218a39259a7 >>> (6 * (r.val % 32))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor12.raw 9 (@Minor12.lower) Minor12.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut92 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor12.target 0xffff0000ffff0000
    (fun r => ⟨(0xe39ebbf3dfbf61969b71d79fc31cb3d35db7411493515597 >>> (6 * (r.val % 32))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor12.raw 9 (@Minor12.lower) Minor12.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def cut94 (p : List (Nat × Nat)) : CountCertificate target :=
  countedPrefixCertificate target Minor8.target 0xff00ff00ff00ff00
    (fun r => ⟨(0xffef7cefae78beeb6caeaa687de75c6da6583ce34c2ca248 >>> (6 * (r.val % 32))) % 64, Nat.mod_lt _ (by decide)⟩)
    pinBase Minor8.raw 10 (@Minor8.lower) Minor8.nonzero
    (by decide +kernel) (by decide +kernel) (by decide +kernel) p
def cutFor : Nat → List (Nat × Nat) → CountCertificate target
  | 2 => cut1
  | 3 => cut2
  | 4 => cut3
  | 5 => cut4
  | 6 => cut5
  | 7 => cut6
  | 8 => cut7
  | 9 => cut8
  | 10 => cut9
  | 11 => cut10
  | 12 => cut11
  | 13 => cut12
  | 14 => cut13
  | 15 => cut14
  | 16 => cut15
  | 17 => cut16
  | 18 => cut17
  | 19 => cut18
  | 20 => cut19
  | 21 => cut20
  | 22 => cut21
  | 23 => cut22
  | 24 => cut23
  | 26 => cut25
  | 29 => cut28
  | 30 => cut29
  | 31 => cut30
  | 32 => cut31
  | 35 => cut34
  | 36 => cut35
  | 37 => cut36
  | 92 => cut91
  | 93 => cut92
  | 95 => cut94
  | _ => cut0

def suppliedPrefix : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | j+1, z => if z=0 then [] else ((z%256)/16,z%16) :: suppliedPrefix j (z/256)
def selectCut (code : Nat) := cutFor (code%128) (suppliedPrefix 2 (code/128))
def cutLabels (k page : ℕ) : ℕ :=
  match k with
  | 7 => if page < 14 then (if page < 7 then (if page < 3 then (if page < 1 then 0x20000040000080000100000200000c00000800003000002000004000008000010000020000040000080000100000200001c000008000070000180000400000b0000010000020000040000080001000000200006800000800002000002000008000008000010000020000040000080001000000200006800000800001000002000034000008000070000020000040000680000700000e000004000038000010000020000040000080000100000200001c00000800001 else (if page < 2 then 0xa00000401a4680001400002e01123c0000f001a0d00003c0074340268800000700001600d4340000580350d00891e0000680000080000200000a00002000002000004000010000020000040000050000080000180000680000400001a000030000028000040000020000080000100000500000a0000140000800001000341a0000040000200000100000200000400000800001000002000004000028000010000020000040000080000100000e00000400003800001 else 0xe00001c01a86800007006a1a01123c0000b80000b00000800007c000008000020000040000040000080000100000200001400002800002000004000008000010000010000020000040000080000100000200000400000800001000002000004000008000010000020000180000300000800000200000400000800001000002000004000008000040000020000080000100000500341a00683400e8680001400002a01344c0000080350d006a1a00000401a86800016)) else (if page < 5 then (if page < 4 then 0x2000004000010000020000020000080000d0000010000340000040000080000200000600000800000801a0d0000280074340000a000008009a2200f43400006003d0d0000180000580224780001f0000020000080000080000100000a000008000010000010000020000040000080000100000200000400003000007000002000004000020000090000280000240000a00000800000e00001c000060000070000180000580000b80000900341a00002400e86804d10 else 0x800005c0224780000400000800001000002000004000008000010000020000040000080000100000300000600000c0000100000200000400000800001000002000004000008000010000020000030000080000100000200000200000400000800001000002000008000004000010000010000040000040000080000100000a0000080000100000100000400000400000800001000004000004000008000010000020000080000180000100000800000400000800001) else (if page < 6 then 0x2000004000008000010000020000040000280000200000a0000140000280000c00001600003000000800001000002000004000008000010000020000040000080000100000200000400002000004000002000004000008000010000020000040000080000100000600000c0000080000100000200000400000800001000002000010000008000010000020000040000180000100002e00005c0000200000400000c01123c0000200000600000800005c00002000006 else 0x200000400000800001000002000004000008000010000020000040000080000100000400000800000800001000002000004000008000020000020000040000080000100000200002001a8680000100000800000400000800008000002000004000020000010000020000300000080000400000200000401a8680000c00000200000400000800001000002000004000008000010000020000040000080000300000600000c0000080000100000200000400000800001))) else (if page < 10 then (if page < 8 then 0x20000040000100000200000200000400000800001000004000008000008000010000040000040000080000200000200001c000038000010000040000140268880000200000a00001c0000380000200000a00001c00003804d110000020000080000100000500000a000014000028000010000020000040000080000100000e00000400003800008006a1a00000400000800001000010000004000008000010000020000300000080000100000200d43400006000001 else (if page < 9 then 0x20000500000080000100001a0000040000080338d00002c000004000008000070000020000040000080000a00341a00007c000010000050000140000080000500000500002800007c0000100000500341a000050000008000020000040000140000a00001e00003e00002800e868000010000040000040000080000a00000200000800000800001000028000004000010000010000020074340000a0000010000020000040000080000100000200000400000800001 else 0x2c0000040000200000100000e00ce34011c680230d007a1a00d4340000b00000400000200002400000c491dc00001a0000040000400000100000400ce340000400000d00001a0000580000100230d00002c00001000002003d0d0000080000080000b00338d00461a00005c000020000010000020000040000080001400002800ce380000080130e0000020000580000080350d00002c0000040000080238d0000020000100000080000100000200000400000800014)) else (if page < 12 then (if page < 11 then 0x20000040000b00238d00002c00f4340000b00001600002c0000100000b00338e000002000004000008000070000020000040000080001600002c0000500000380000700000e0000580000380001600000e00001c01186800007006a1a00001c0000200000400000e000058000048000010000020000040000080000100000e00000400000800001000002000004000040000160000100000040118680001600002c0000100000200000100000200d4340000b000001 else 0x80000040000b0000010000080000040000080350d00002c00000400000800001000002000004000008000010000020000580000b0000160000020000040000080000100000200000400000800001000002000004000008000010000020000040000b00000100000800ce34000008000010000020000100000b0000010000020000040000080000700000200000400000800001000028000004000008000010000020000500000a00000100000200005000000800001) else (if page < 13 then 0x461a0000040000200000400461a0000200000080000400001000005800000800004000008008c3401186800016000002000010000008000040000080000580000200338d0000080000100000b0000040000080000580000b00000400002c000010000020000070000020000040000380000700000200001c00000800001000014004e380000500001400671c004c380000a00000100671c0000040000080000400001000d4340000080000400000200000400004000001 else 0x7000010000058000040000160000100000580000400001600671a000058019c680001600002c000058019c6800008)))) else 0
  | 8 => if page < 19 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x20000240000080001000001600002c0000080000100002c0000040000080001000000600000c000010000020000200000400000680001100001e000040000118000230000200000400000680002300001c00003800010000020000040000090000120000100000000000400000000000000001a0000000000680000d00001a0000340000800000000001a0000000000800001000001a0000340000680000d0000200000400000680000d0000200000800000680000d else 0x2000040000008000140000020000500000180000100002800000c00000800008000002000004000008000010000020000080000080000d00001a0000340000900000f00001e0000040000700000100002400003c0000080000d00000200000400009000003000004011248019c680338d00002c0000580000080000200341a00000400001000001000002000080000008000140000020000580000380000700002000002c0000580000b00002000000400004800001) else (if page < 3 then 0x2800000c00001803c8d00000600000c000030000030000040000040000080000100000c0000080000a000002000004006e3400001000002000006000004000008000100000020000080000180000300000600000400001000002000004000008000008000010000200000040000a000003000004000068000008000020000020000500000a00000100000400000400000800001000002000004000008000010000200000080000080000100000200004000008000002 else 0x1e00003c000008000010000020000300000b0000110000200112480000600000c00002200004001a87000003000002000004000008000010000020000040000080001100002000d434000008000010000020000580000080000100891e008e340000b0000010000080000100000a0000040000020000580000080000100000400000400006800001000004000020000010000060000100000180000a00000d00001a0000500000080000600000200001800003000003)) else (if page < 6 then (if page < 5 then 0x671a0000040000080000100671a0000040000080000100001a0000040000400000100000a00ce340000400338d00001a000034019c680000500461a0046400118680118f007a1a008c3400000800001000002000004000080000010000200000400000080001000000200ce340118680000100671a000004000008000010000200000400000800001000671c00ce3800d0680338d00000200683400000800016002320000040000080000100000180000300000600000f else 0x1a00003400008800016000022000080000088000140000240000480000900001400001a0000740000e8044a30000040000140000e80001600001a0000340000b0000020000040000140000800001000002c0112480000c000005000020000040019c7800018000028000004000038000070000020000200000400000100001a0000340000080000100000200004400008004d0d00003000007c0000880001000491a0000040000080000100000401344c00000800015) else (if page < 7 then 0x461a01124c01e86804490006a1a00ce3400dc6801b0d00791a00d2340000b0000040000020000240000a80000900000200001400000800009000002011372248ee00000d8923ba0000900000680000000001a0000340000680000d0000480000340000000000d000048000034000120011dc00001a0000340000680000e00001c0000380000700000000001a00009000aae00000d0000460000380001180000d00001a00003800006c491dc00001a00009268d2e00000d else (if page < 8 then 0x280000040000080001800000c000020019c6800008000002008c340118680338d00461a000058022490000160000080000580000080000100000200d43401a86800001000002000004019c6801b0d00691a0000100000b000014000010000050019c680000800000600000800d8680001400361a0000500000180001800000a0000080000100348d00002800d234000010000020000040000500000180001400002c00001c00003804490009a1a013434019c680238d else 0xe00d2340000b00000400000800005c0000b00001500002e000014000028000090000020000040000080000100000e0000040000080000100000a0000040000280000900000c00001800000800001000002000004000008000010000120000040000080000100000200001c000010000020000040000080000080000100000200001c000008000010000020000040000080000100000200001c000010000020000040000080000b00001600002c00005000000804d0d)))) else (if page < 14 then (if page < 11 then (if page < 10 then 0x300000180000080000100000200ce380000080000100000e00000800001000001000002000004000038000010000020000040000080000100000e0000080000100001600671a0000500000b00001400002c0068400000380001800002800001c0000380000700002c0000540000a00000700000e0000580000b80000700002c0000580000380000700002800001c0000a00001700002a0134340000380000700461a00005c00003804490006a1a00001c00003801b0d else 0x400001c0000080000100000e000008000010000010000040000040000a00000100000200000400000800001000002000004000010000140000280000040000080000200002800000400000800007000004000008000008000020000020000580268680001400002c008e340000b003d0d007a1a0000580000b00001400371a00005001e4680001400002c0000580000a000016000008000058019c700001800000a00ce380000080000100000e00000400000800005) else (if page < 12 then 0x40000080000100000200000400000800001000002000004000008000010000020000040000080000a00000200000600ce3400001000002000004000008000018000140000040000040000100000200000e0000080000a00000100000600000c0000080000100000600000c0000080001400002800000c000018000140000020000080000080000100000200000400000800001000002000004000038000020000040000080000100000700000e00000800001000001 else (if page < 13 then 0x600001c000008000020000040000040000380000700000400001c0000100000700000200000800001000008000002000014000028000050000280000600000280001400000600000c0000400348d00000600000800001000002000004000020000018000020000040000080000a0000030000040000080000100000200691a0000500000100000200000400000800001000002000008000010000020000020000040000080000100000200000400000800001000002 else 0x280000200000a00001400671a0000600000a0000140000280000500000a0000080000280000500000a00001400002800006000002000014000010006c3400001800002000006000014000018000080000060000080000280000300002800000c0000100000300000a00000c00d8680001400000400000c0000180000300000600000c000018000030000060000080000180000200000600000c0000a00000300671a00000c0000180001400000400000c0000a000003))) else (if page < 16 then (if page < 15 then 0x20000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000010000018000040000060000040000080001400002c0000500000b000001000002000010011c68000140089240000100000080001400000600ce3400000800003000008000004000008000010000020000100000b0000040000020000040000200000100000e0000200000a0000080000280000200000a000008 else 0x800463c0000a000016006a1a0000040000200000600002c0000580000080000400000c0000580000080000400000c000058022480000160000020000040000b0000040000080000580000200000400002c0000580000b00001600000800000400000800001000002000004000008000010000180000040000180000300001000d43400000800001000002000004000040000010000020000040000b0000010000020000040000080350d00002c00000400000800001) else (if page < 17 then 0x3000ce340000b00001600003000ce340000400230d00000200463c0000300230d0000100000040000300000800002c0000040118680000600461a008c340000b00000100000c0000040118680000400002c000010019c6800004000008000058000020000070000020000040000080000700000e000004000038000020000020000080000380000100000200001c0000380000100000e0000040000080000a00271c0000280000a00338e00341a00ce3800000800001 else (if page < 18 then 0x2c0000580000b00001600002c00ce340000b00001800002c0000580000b00001800002c0000580000b000014009a1a00000400001000001000002000050000008000020000020000500000080000200000200000402686800014000002000004000008000010000020000580000080000100000a0000140000080001400002c0000040268900001800000a000004000008000140000020000040000380000800671a000020008c8000008000030000020019c680338d else 0x2c0000580000b000016))))) else 0
  | 9 => if page < 6 then (if page < 3 then (if page < 1 then 0x4a0000440000880001100001a0000340000680000d00001a0000400001180002400004a0000400001200002500004a000040000078000250000200000340000680001300001a0000340000680000d00001a0000340000680000d00002000003800006800010000020000040000078000100000460000340000680000d00001a0000340000800002300001a0000340000680000d00001a0000340000680001200001a0000400000800000d00001a0000340000800000d else (if page < 2 then 0x1a0000400000800000d000048000040026ae00000d00002000004000d2e00000d00001a0000340000680000d00001a00004000008001d5c00001a0000340000680001000001a000040000080000240000200000340000680000d00001a000034000068000100000240000400000780000d00001a0000340000680000d00001a000034000080000100000480000340000680000d0000260000400000680000d0000200000340002e00000000001a00004400008800011 else 0x1a0000340000680000d00001a0000340000000000d00001e0000340001180000d0000460000340000800000d00001a0000340000680002300002000008c0001180000d0000200000340000680000d00001a00003c0000780000d0000200000340000900000e00001a0000380000700000d00001a0000340000680000f00001c0000340000680000d00001e00003400008000010000020011370000080000100023b80000400000800155c0000200000900000680000d)) else (if page < 4 then 0x200000400000780000f00001e0000400000800002300002000003c0000780001000001e000000000080000100000200000480000800000f000000000040000080000100000200000400000780001200001e00003c0001200000d00001a0000340000900000f0000200000900000780155c00001a00008c00aae80000d00001a0000000000680000d00001a0000340000680002300001a0000340000680000f00001a0000340000680000000001a0000340000780000d else (if page < 5 then 0x480000900000800000d0000200000340000680000d0000200000340000800000d00001a0000340000680000d000000000034000068000100000200000340000800000d00002400008c0000680000e00001a000034000118011dc00001a0047740000680000d0000000000340000680000d00001a0000340000680000000001a0000340000680000d00001a0000340000680000d00001a0000380000700000e00001e0000400000780001000002000004000007800010 else 0x2000004000008000010000020000048000080000100089b80000340226e80002400004a0000000000680000d00001a00009000012000025))) else 0
  | 10 => if page < 1 then 0xb80001740002e8000000000be00017c000000000000000be0000000000000005f00000000017c0002f80005c0000b80001700002f80005f else 0
  | 11 => if page < 1 then 0x0 else 0
  | _ => 0

def label (k i : Nat) := field cutLabels k 23 i

def checked (k i : Nat) := decide (pool k i).Nodup &&
  (if label k i = 0 then Vector.packedClosed target negative goalColumns pool counts lookup steps k i
   else let c := selectCut (label k i)
        countedCut c.mask c.patterns c.bound k (pool k i))

theorem checked_sound (k i : Nat) (h : checked k i = true) :
    closed target negative pool counts lookup steps k i = true ∨
      (∀ d ≤ k, ¬ Cone target d (pool k i).toFinset) := by
  have h' := (Bool.and_eq_true_iff.mp h).2
  change (if label k i = 0 then _ else _) = true at h'
  split at h'
  · exact Or.inl (Vector.closed_sound target negative goalColumns mask_valid pool counts lookup steps
      (by decide +kernel) (fun r hr => (neg r hr).1) k i h')
  · refine Or.inr (fun d hd run => ?_)
    have no := (selectCut (label k i)).sound k (pool k i) hd run
    change countedCut _ _ _ _ _ = true at h'
    rw [no] at h'
    contradiction

theorem root : pool 11 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x112 : span (checked 7) 112 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x224 : span (checked 7) 112 224 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x336 : span (checked 7) 112 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x448 : span (checked 7) 112 448 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x560 : span (checked 7) 112 560 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x672 : span (checked 7) 112 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x784 : span (checked 7) 65 784 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 849 0 = true :=
  (@span_join (checked 7) 448 0 401 (@span_join (checked 7) 224 0 224 (@span_join (checked 7) 112 0 112 chunk7x0 chunk7x112) (@span_join (checked 7) 112 224 112 chunk7x224 chunk7x336)) (@span_join (checked 7) 224 448 177 (@span_join (checked 7) 112 448 112 chunk7x448 chunk7x560) (@span_join (checked 7) 112 672 65 chunk7x672 chunk7x784)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x0 : span (checked 8) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x112 : span (checked 8) 112 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x224 : span (checked 8) 112 224 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x336 : span (checked 8) 112 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x448 : span (checked 8) 112 448 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x560 : span (checked 8) 112 560 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x672 : span (checked 8) 112 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x784 : span (checked 8) 112 784 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x896 : span (checked 8) 112 896 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x1008 : span (checked 8) 112 1008 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x1120 : span (checked 8) 36 1120 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer8 : span (checked 8) 1156 0 = true :=
  (@span_join (checked 8) 560 0 596 (@span_join (checked 8) 224 0 336 (@span_join (checked 8) 112 0 112 chunk8x0 chunk8x112) (@span_join (checked 8) 112 224 224 chunk8x224 (@span_join (checked 8) 112 336 112 chunk8x336 chunk8x448))) (@span_join (checked 8) 336 560 260 (@span_join (checked 8) 112 560 224 chunk8x560 (@span_join (checked 8) 112 672 112 chunk8x672 chunk8x784)) (@span_join (checked 8) 112 896 148 chunk8x896 (@span_join (checked 8) 112 1008 36 chunk8x1008 chunk8x1120))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk9x0 : span (checked 9) 112 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk9x112 : span (checked 9) 112 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk9x224 : span (checked 9) 112 224 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk9x336 : span (checked 9) 4 336 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer9 : span (checked 9) 340 0 = true :=
  (@span_join (checked 9) 224 0 116 (@span_join (checked 9) 112 0 112 chunk9x0 chunk9x112) (@span_join (checked 9) 112 224 4 chunk9x224 chunk9x336))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk10x0 : span (checked 10) 20 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer10 : span (checked 10) 20 0 = true :=
  chunk10x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk11x0 : span (checked 11) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer11 : span (checked 11) 1 0 = true :=
  chunk11x0
theorem verified : ∀ k ≤ 11, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer7 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer8 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer9 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer10 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer11 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 12 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes_or target nonzero negative neg pool counts lookup steps valid fix 11
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => checked_sound k i (verified k hk i hi))
    11 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Full



namespace SignedFrontier.CliqueLink
def target := SmallCert.Full.target
def raw := SmallCert.Full.raw
def initial : List W := [0, ~~~(0 : W)] ++ raw ++ raw.map (fun w => ~~~w)
theorem lower (p : List (ℕ × ℕ)) (o : ℕ) (hit : canonical (evaluate p initial o) = target) : 12 ≤ p.length := by
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
    (lower : ∀ p o, canonical (evaluate p CliqueLink.initial o) = CliqueLink.target → 12 ≤ p.length)
    (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : ∀ x, ThresholdReplacement.signed p o x = ThresholdReplacement.sliceTarget x) : 12 ≤ p.length :=
  lower p o (wordOfSolution p o hit)

end TableLink

end PEqualNP.Outside.L_meta_12262_aux

open PEqualNP.Outside.L_meta_12262_aux

theorem PEqualNP.Outside.L_meta_12262 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860992 * 2 ^ 32 + 3900735616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860992 * 2 ^ 32 + 3900735616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s existsC
  obtain ⟨C,ok,bound,hit⟩ := existsC
  obtain ⟨D,mono,small,evaluates⟩ := ThresholdReplacement.replacement
    (TableLink.sliceRequirement SignedFrontier.CliqueLink.lower) C ok hit
  exact ⟨D,mono,small.trans bound,evaluates⟩
