import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12355_aux

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
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2))
    (varies : ¬ ∃ b : Bool, ∀ x : α, C.eval (v.map fun a => a.1 x) = b)
    (sensitive : C.eval (v.map fun a => a.2.1) ≠ C.eval (v.map fun a => a.2.2)) :
    ∃ (p : List (ℕ × ℕ)) (o : ℕ),
      p.length < (C.gates.map fun g => ite (g.op.eval [false] = true) 0 (ite (g.inputs.length = 2) 1 0)).sum ∧
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
  have lo : out.lo = C.eval (v.map fun u => u.2.1) := by
    simpa [out,a,make,List.map_map,Function.comp_def] using outputMap Wire.lo rfl (fun _ _ => rfl) C a
  have hi : out.hi = C.eval (v.map fun u => u.2.2) := by
    simpa [out,a,make,List.map_map,Function.comp_def] using outputMap Wire.hi rfl (fun _ _ => rfl) C a
  have lt : k < (C.gates.map Paid).sum := by
    by_contra! ge
    have eq := Nat.le_antisymm limit ge
    have impossible : Stable out := get_property _ _ _ _
      (Or.inl ⟨false,fun _ => rfl⟩ : Stable (K (α := α) false)) (stable eq (fun u hu => (old u hu).2))
    rcases impossible with ⟨b,h⟩ | e
    · exact varies ⟨b,fun x => (values x).symm.trans (h x)⟩
    · exact sensitive (lo.symm.trans (e.trans hi))
  have zero : Good t (K false) := ⟨run.keep _ (base false).1,run.keep _ (base false).2⟩
  have usable : Good t out := get_property _ _ _ _ zero accepted
  obtain ⟨o,ho,eo⟩ := List.getElem_of_mem usable.1
  obtain ⟨p,len,sim⟩ := run.program
  refine ⟨p,o,by rw [len]; exact lt,?_⟩
  intro x
  change (p.foldl addPair _).getD o false = _
  rw [sim,List.getD_eq_getElem _ _ (by simpa using ho),List.getElem_map,eo]
  exact values x

end PetersenSignedSlice

namespace ThresholdReplacement
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) := Nat.testBit (4278124032 * 2 ^ 32 + 4276676608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[
  ⟨.and, [0,1]⟩,
  ⟨.and, [3,4]⟩,
  ⟨.or, [3,4]⟩,
  ⟨.or, [2,6]⟩,
  ⟨.or, [5,7]⟩,
  ⟨.or, [9,10]⟩,
  ⟨.and, [9,10]⟩,
  ⟨.or, [0,12]⟩,
  ⟨.or, [1,13]⟩,
  ⟨.and, [11,14]⟩,
  ⟨.and, [8,15]⟩], 16⟩
theorem size : witness.size = 11 := by decide +kernel
theorem legal : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel
theorem value : ∀ x, circuitFun 6 witness x = target x := by decide +kernel

abbrev Input := Fin 5 → Bool
def slot : Fin 6 → Nat := ![0, 1, 2, 3, 4, 5]
def held : Fin 6 → Bool := ![false, false, false, false, false, false]
def lift (x : Input) (j : Fin 6) : Bool := if h : slot j < 5 then x ⟨slot j,h⟩ else held j
def sliceTarget (x : Input) := target (lift x)
def signedStart (x : Input) := [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not
def signed (p : List (ℕ × ℕ)) (o : ℕ) (x : Input) :=
  (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false

-- A five-input restriction gives the signed binary lower bound. The two explicit sensitivity rows certify that the restriction removes a binary gate.
theorem pinSlice (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 6 C x = target x) :
    ∃ p o, p.length < (C.gates.map PetersenSignedSlice.Paid).sum ∧
      ∀ x, signed p o x = sliceTarget x := by
  let raw := List.ofFn (fun j : Fin 5 => fun x : Input => x j)
  let pool := [(fun _ : Input => false), (fun _ : Input => true)] ++ raw ++
    raw.map (fun u x => !(u x))
  let pin := fun j : Fin 6 => (fun x : Input => lift x j, Nat.testBit 9 j.val, Nat.testBit 41 j.val)
  let v := List.ofFn pin
  have constants (b : Bool) : (fun _ : Input => b) ∈ pool := by cases b <;> simp [pool]
  have pins : ∀ a ∈ v, a.1 ∈ pool ∧ (fun x => !(a.1 x)) ∈ pool ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2) := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    by_cases h : slot j < 5
    · let i : Fin 5 := ⟨slot j,h⟩
      have pos : (fun x : Input => x i) ∈ raw := List.mem_ofFn.mpr ⟨i,rfl⟩
      have neg : (fun x : Input => !(x i)) ∈ pool := List.mem_append_right _ (List.mem_map_of_mem pos)
      have both : (fun x : Input => x i) ∈ pool := List.mem_append_left _ (List.mem_append_right _ pos)
      have stable : ∀ j : Fin 6, slot j < 5 → Nat.testBit 9 j.val = Nat.testBit 41 j.val := by decide +kernel
      refine ⟨?_,?_,Or.inr (stable j h)⟩
      · simpa [pin,lift,h,i] using both
      · simpa [pin,lift,h,i] using neg
    · refine ⟨?_,?_,Or.inl ⟨held j,fun x => ?_⟩⟩
      · simpa [pin,lift,h] using constants (held j)
      · simpa [pin,lift,h] using constants (!(held j))
      · simp [pin,lift,h]
  have slice (x : Input) : C.eval (v.map fun a => a.1 x) = sliceTarget x := by
    simpa [v, pin, sliceTarget, circuitFun, List.map_ofFn, Function.comp_def] using hit (lift x)
  have varies : ¬ ∃ b : Bool, ∀ x : Input, C.eval (v.map fun a => a.1 x) = b := by
    rintro ⟨b,h⟩
    have first := (slice (fun _ => false)).symm.trans (h _)
    have second := (slice (fun _ => true)).symm.trans (h _)
    exact (by decide +kernel : sliceTarget (fun _ => false) ≠ sliceTarget (fun _ => true)) (first.trans second.symm)
  have diff : C.eval (v.map fun a => a.2.1) ≠ C.eval (v.map fun a => a.2.2) := by
    have a := hit (fun j => Nat.testBit 9 j.val)
    have b := hit (fun j => Nat.testBit 41 j.val)
    simp only [v,pin,List.map_ofFn,Function.comp_def,circuitFun] at a b ⊢
    rw [a,b]
    decide +kernel
  obtain ⟨p,o,small,eval⟩ := PetersenSignedSlice.compile Input C ok pool v constants pins varies diff
  refine ⟨p,o,small,fun x => ?_⟩
  change (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false = sliceTarget x
  have start : pool.map (fun u => u x) = signedStart x := by
    simp only [pool,raw,signedStart,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  rw [← start]
  exact (eval x).trans (slice x)

theorem replacement
    (sliceLower : ∀ p o, (∀ x, signed p o x = sliceTarget x) → 9 ≤ p.length)
    (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 6 C x = target x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ ∀ x, circuitFun 6 D x = target x := by
  by_cases mono : Monotone2 C
  · exact ⟨C, mono, le_rfl, hit⟩
  · obtain ⟨p,o,sz,ev⟩ := pinSlice C ok hit
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

namespace SignedFrontier.SmallCert.Restricted

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xfee8e800fee8e800
def negative : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 16, 17, 18, 20, 24]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · refine ⟨10,11,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨9,11,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨9,13,by decide +kernel,?_⟩
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
  | 0 => if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0x10001000100010000ffffaa00ffffaa00ffff0000ffff0000ff00f000ff00f000ff00aa00ff00aa00ff000000ff000000fe00fe00fe00fe00eeeeee00eeeeee00cc00cc00cc00cc00aaffaa00aaffaa00aaccee00aaccee00aaaaaa00aaaaaa00aa00aa00aa00aa0088aaaa0088aaaa0088888800888888000ffff0000ffff0000aaaaa000aaaaa000a0a0a000a0a0a0000fffe0000fffe0000ffee0000ffee0000ffea0000ffea0000ffcc0000ffcc0000ffaa0000ffaa0000ff880000ff880000ff0a0000ff0a0000ff000000ff000000fefe0000fefe0000feee0000feee0000fcfc0000fcfc0000eeee0000eeee0000eeaa0000eeaa0000ee000000ee000000eaea0000eaea0000cccc0000cccc0000afaa0000afaa0000af000000af000000aeae0000aeae0000aaee0000aaee0000aaaa0000aaaa0000aa880000aa880000aa0a0000aa0a0000aa000000aa000000a8a80000a8a800008a8a00008a8a000088aa000088aa00008888000088880000880000008800000080800000808000003f0000003f0000002a2a00002a2a00000f0a00000f0a00000f0000000f0000000e0e00000e0e00000aaa00000aaa00000a0a00000a0a00000a0000000a00000008080000080800000300000003000000020200000202000000ee000000ee000000aa000000aa00000088000000880000000a0000000a0000000000000000 else 0xf00fff00f00fff00f00ff000f00ff000f00afaa0f00afaa0f00af000f00af000f003f000f003f000f000f0a0f000f0a0f000f000f000f000f000a000f000a000f0003000f0003000f0000000f0000000e0eeeee0e0eeeee0e0e0e0e0e0e0e0e0e0a0e0a0e0a0e0a0e000e000e000e000ccccccc0ccccccc0c0c0c0c0c0c0c0c0b0a0b0a0b0a0b0a0b000b000b000b000aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa0a2aaaaa0a2aaaaa0a2a2a2a0a2a2a2a0a0aff0a0a0aff0a0a0afafa0a0afafa0a0acece0a0acece0a0aaaaa0a0aaaaa0a0aaa0a0a0aaa0a0a0a8a8a0a0a8a8a0a0a2a2a0a0a2a2a0a0a0f0a0a0a0f0a0a0a0e0e0a0a0e0e0a0a0aaa0a0a0aaa0a0a0a0a0a0a0a0a0a0a0a000a0a0a000a080a080a080a080a020a020a020a020a00ff000a00ff000a00aaaa0a00aaaa0a00aa000a00aa000a000f000a000f000a000a0a0a000a0a0a000a000a000a000a0000000a0000000808aaaa0808aaaa080888880808888808080a0a08080a0a0808080808080808080008000800080007070700070707000706070607060706070007000700070006060606060606060303fcfc0303fcfc030303000303030003020302030203020300ff000300ff0003000f0003000f000300030003000300030000000300000002aaaaaa02aaaaaa0202aaaa0202aaaa02020a0a02020a0a02020202020202020200020002000200) else (if page < 3 then 0x3e3e3e3e3e3e3e3e3c3cfcfc3c3cfcfc3c3ccccc3c3ccccc3c3c3c3c3c3c3c3c33333330333333303333332233333322333333003333330033330000333300003300ff003300ff00330033003300330030303030303030302f222f222f222f222f002f002f002f002e2e2e2e2e2e2e2e2aaaaaaa2aaaaaaa2a2aeaea2a2aeaea2a2aaaaa2a2aaaaa2a2aaa2a2a2aaa2a2a2a2aaa2a2a2aaa2a2a2a2a2a2a2a2a2a2a2a222a2a2a222a2a2a0a2a2a2a0a2a2a2a002a2a2a002a0a2a0a2a0a2a0a2a002a002a002a002222aaaa2222aaaa22222222222222221f00ff001f00ff001f001f001f001f001e1e1e1e1e1e1e1e1a1a1a1a1a1a1a1a11110000111100000fffff000fffff000fff00000fff00000ff0ff000ff0ff000ff0f0f00ff0f0f00ff00ff00ff00ff00f0fff000f0fff000f0ff0f00f0ff0f00f0ff0000f0ff0000f0faaaa0f0faaaa0f0f3c3c0f0f3c3c0f0f0ff00f0f0ff00f0f0faa0f0f0faa0f0f0f0e0f0f0f0e0f0f0f0a0f0f0f0a0f0f0f080f0f0f080f0f0f020f0f0f020f0f0f000f0f0f000f0f0a0a0f0f0a0a0f0f00000f0f00000f0e0f0e0f0e0f0e0f0e0f0a0f0e0f0a0f0e0f000f0e0f000f0e0e0e0f0e0e0e0f0c0f0c0f0c0f0c0f0affaa0f0affaa0f0a0f0a0f0a0f0a0f0a0f000f0a0f000f0a0a0a0f0a0a0a0f080f080f080f080f070f000f070f000f030f000f030f000f020f020f020f02 else (if page < 4 then 0x8f8f8f008f8f8f008f888f888f888f888f008f008f008f008aaaaaaa8aaaaaaa8a8aaaaa8a8aaaaa8a8a8a8a8a8a8a8a8a888a888a888a888a0a8a0a8a0a8a0a8a008a008a008a0088aaaaaa88aaaaaa8888ff888888ff888888f8f88888f8f88888aaaa8888aaaa8888aa888888aa888888a8a88888a8a888888a8a88888a8a888888aa888888aa88888888888888888888880088888800888088808880888088088808880888088800ff008800ff008800aaaa8800aaaa8800aa008800aa008800888888008888880088008800880088000000880000008080aaaa8080aaaa8080888880808888808080808080808080008000800080007f00ff007f00ff007f007f007f007f00777700007777000070707070707070706e6e6e6e6e6e6e6e6a6a6a6a6a6a6a6a5f5f00005f5f00005a5a5a5a5a5a5a5a55ff000055ff00005555aaaa5555aaaa5555550055555500555550505555505055554444555544445555000055550000555055505550555055005500550055005500000055000000545454545454545450f050f050f050f05050f0f05050f0f050505050505050504c4c4c4c4c4c4c4c44444444444444443f3fc0c03f3fc0c03f3f3f003f3f3f003f3c3f3c3f3c3f3c3f2a3f2a3f2a3f2a3f0f33003f0f33003f0c3f0c3f0c3f0c3f00ff003f00ff003f003f003f003f003f000f003f000f003f0000003f000000 else 0xaaaaaa00aaaaaa00aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaaa2222aaaa2222aaaa0a0aaaaa0a0aaaaa00aaaaaa00aaaaaa0000aaaa0000aaa8aaaaaaa8aaaaaaa8aaa8aaa8aaa8aaa8aa88aaa8aa88aaa8aa00aaa8aa00aaa8a8a8aaa8a8a8aaa0aaa0aaa0aaa0aa8aaa8aaa8aaa8aaa88ffccaa88ffccaa88aaaaaa88aaaaaa88aa88aa88aa88aa88aa00aa88aa00aa888888aa888888aa80aa80aa80aa80aa5aaa5aaa5aaa5aaa55ff00aa55ff00aa55aaaaaa55aaaaaa55aa00aa55aa00aa2aaaaaaa2aaaaaaa2aaa2aaa2aaa2aaa2aaa0aaa2aaa0aaa2aaa00aa2aaa00aa2a2a2aaa2a2a2aaa22aa22aa22aa22aa0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa0aaa00aa0aaa00aa0a0a0aaa0a0a0aaa08aa08aa08aa08aa02aa02aa02aa02aa00ff00aa00ff00aa00eeccaa00eeccaa00ee00aa00ee00aa00af00aa00af00aa00aaaaaa00aaaaaa00aa88aa00aa88aa00aa0aaa00aa0aaa00aa00aa00aa00aa008800aa008800aa000a00aa000a00aa000000aa000000a8a8fcfca8a8fcfca8a8aaaaa8a8aaaaa8a8a8a8a8a8a8a8a888a888a888a888a800a800a800a800a2a2a2a2a2a2a2a2a0f0a0f0a0f0a0f0a0aaa0aaa0aaa0aaa0a0aaaaa0a0aaaaa0a0a0aaa0a0a0aaa0a0a0a0a0a0a0a0a0a00000a0a000009a9a9a9a9a9a9a9a9999aaaa9999aaaa998899889988998898989898989898988f8f8f888f8f8f88))) else (if page < 8 then (if page < 6 then 0xcccc0000cccc0000ccc8ccc8ccc8ccc8cc00cc00cc00cc00cacacacacacacacac4c4c4c4c4c4c4c4c0ccc0ccc0ccc0ccc0c0c0ccc0c0c0ccc0c0c0c0c0c0c0c0c0c00000c0c00000c000c000c000c000bfaabfaabfaabfaabf00ff00bf00ff00bf00bf00bf00bf00bebebebebebebebebcbcbcbcbcbcbcbcafafafaaafafafaaafafaf00afafaf00afaeafaeafaeafaeafaaffaaafaaffaaafaaafaaafaaafaaafaaaaaaafaaaaaaafa0afa0afa0afa0af8caf8caf8caf8caf50af50af50af50af0faa00af0faa00af00ff00af00ff00af00af00af00af00af00aa00af00aa00af000f00af000f00af000000af000000aeaeeeeeaeaeeeeeaeaeaeaeaeaeaeaeaeaaaeaaaeaaaeaaae0cae0cae0cae0cae00ae00ae00ae00acacacacacacacacabaaabaaabaaabaaab00ab00ab00ab00aaffff00aaffff00aaff0000aaff0000aaeeeeeeaaeeeeeeaaeaeaeaaaeaeaeaaaaaffeeaaaaffeeaaaaffaaaaaaffaaaaaaff00aaaaff00aaaafefeaaaafefeaaaaeeeeaaaaeeeeaaaaeeaaaaaaeeaaaaaaeaeaaaaaeaeaaaaaccccaaaaccccaaaaafaaaaaaafaaaaaaaeaeaaaaaeaeaaaaaaeeaaaaaaeeaaaaaaaaaaaaaaaaaaaaaaa8aaaaaaa8aaaaaaa0aaaaaaa0aaaaaa8aaaaaaa8aaaaaaa88aaaaaa88aaaaaa80aaaaaa80aaaaaa2aaaaaaa2aaaaaaa22aaaaaa22aaaaaa0aaaaaaa0aaaaaaa08aaaaaa08aaaaaa02aaaaaa02 else (if page < 7 then 0xeeeeeecceeeeeecceeeeeeaaeeeeeeaaeeeeee00eeeeee00eeeecccceeeecccceeee0000eeee0000eeeaeeeaeeeaeeeaeeeaeaeaeeeaeaeaeee0eee0eee0eee0eecceecceecceecceecccccceecccccceeaeeeaeeeaeeeaeeeaaffaaeeaaffaaeeaaeeeeeeaaeeeeeeaaeeaaeeaaeeaaeeaacc00eeaacc00eeaaaaaaeeaaaaaaee66ee66ee66ee66ee22ee22ee22ee22ee0eee0eee0eee0eee00ff00ee00ff00ee00eeeeee00eeeeee00ee00ee00ee00ee00aa00ee00aa00ee000000ee000000ecececeeecececeeececececececececececccccececcccceccceccceccceccceaeaeeeeeaeaeeeeeaeaeaeeeaeaeaeeeaeaeaeaeaeaeaeaeaeaeac0eaeaeac0eaeaeaaaeaeaeaaaeaeaea00eaeaea00eaeaaaaaeaeaaaaaeae8eae8eae8eae8eac0eac0eac0eac0eaaaeaaaeaaaeaaaea00ea00ea00ea00e8e8e8e8e8e8e8e8e6e6e6e6e6e6e6e6e4e4e4e4e4e4e4e4e0e0e0e0e0e0e0e0dddd0000dddd0000dd00dd00dd00dd00dcdcdcdcdcdcdcdcd500d500d500d500d0d0d0d0d0d0d0d0cececececececececceecceecceecceecceccceccceccceccccceeeecccceeeeccccececccccececccccccfcccccccfccccccceecccccceeccccccccccccccccccccccc0ccccccc0ccccccaaccccccaacccccc88cccccc88cccccc44cccccc44cccccc0ccccccc0ccccccc00cccccc00cccc4c4ccccc4c4ccccc4444cccc4444 else 0xfcfc0000fcfc0000fcf0fcf0fcf0fcf0fcecfcecfcecfcecfce8fce8fce8fce8fcccccccfcccccccfc00fc00fc00fc00fafafafafafafafafaf8f8f8faf8f8f8faf0faf0faf0faf0faf0f8f0faf0f8f0faf0f0f0faf0f0f0fa00fa00fa00fa00f8f8f8faf8f8f8faf8f8f8f8f8f8f8f8f8f8f8f0f8f8f8f0f8f8f888f8f8f888f8f8f800f8f8f800f8f0f8f8f8f0f8f8f8f0f8f0f8f0f8f0f8f0f0f0f8f0f0f0f870f870f870f870f800f800f800f800f5f50000f5f50000f500f500f500f500f3f0f3f0f3f0f3f0f300f300f300f300f2f2f2f2f2f2f2f2f2f0f0f0f2f0f0f0f0ff0000f0ff0000f0f8f8f8f0f8f8f8f0f0fff0f0f0fff0f0f0fafaf0f0fafaf0f0f8faf0f0f8faf0f0f8f8f0f0f8f8f0f0f8f0f0f0f8f0f0f0f1f0f0f0f1f0f0f0f0fef0f0f0fef0f0f0fcf0f0f0fcf0f0f0faf0f0f0faf0f0f0f8f0f0f0f8f0f0f0f2f0f0f0f2f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0c0f0f0f000f0f0f000f0f0e0e0f0f0e0e0f0f0a0a0f0f0a0a0f0f07070f0f07070f0f05050f0f05050f0f03030f0f03030f0f000f0f0f000f0f0f00000f0f00000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f070f070f070f070f050f050f050f050f000ff00f000ff00f000f000f000f000f0000000f0000000efeeefeeefeeefeeefaaefaaefaaefaaef00ef00ef00ef00eeeeffeeeeeeffeeeeeefefeeeeefefeeeeeeeeeeeeeeeee)) else (if page < 9 then 0xffaa0000ffaa0000ffa8ffa8ffa8ffa8ffa0ff00ffa0ff00ff8aff8aff8aff8aff88ffaaff88ffaaff88ff88ff88ff88ff88ff00ff88ff00ff888888ff888888ff80ff80ff80ff80ff55ff00ff55ff00ff55aa00ff55aa00ff550000ff550000ff3fff00ff3fff00ff2aff2aff2aff2aff22ff22ff22ff22ff0fff0aff0fff0aff0fff00ff0fff00ff0ff000ff0ff000ff0faa0aff0faa0aff0f0000ff0f0000ff0eff0eff0eff0eff0affaaff0affaaff0aff0aff0aff0aff0aff00ff0aff00ff0a0a0aff0a0a0aff08ff08ff08ff08ff03ff00ff03ff00ff02ff02ff02ff02ff00ffeeff00ffeeff00ffaaff00ffaaff00ff88ff00ff88ff00ff0aff00ff0aff00ff00ff00ff00ff00fe00ff00fe00ff00fc00ff00fc00ff00f800ff00f800ff00f000ff00f000ff00ef00ff00ef00ff00ee00ff00ee00ff00ea00ff00ea00ff00cc00ff00cc00ff00af00ff00af00ff00aaaaff00aaaaff00aa00ff00aa00ff008800ff008800ff005500ff005500ff003f00ff003f00ff000ff0ff000ff0ff000f00ff000f00ff000a00ff000a00ff000300ff000300ff0000aaff0000aaff000000ff000000fefefefefefefefefefe0000fefe0000fef0f0f0fef0f0f0feeefeeefeeefeeefeaafeaafeaafeaafe00ff00fe00ff00fe00fe00fe00fe00fe00ee00fe00ee00fcfcfcfcfcfcfcfcfcfcfcccfcfcfcccfcfcfc00fcfcfc00 else (if page < 10 then 0xffffffeeffffffeeffffffccffffffccffffffaaffffffaaffffff88ffffff88ffffff0affffff0affffff00ffffff00fffff0f0fffff0f0fffff000fffff000ffffeeeeffffeeeeffffccccffffccccffffcc00ffffcc00ffffc000ffffc000ffffaaaaffffaaaaffffaa00ffffaa00ffffa800ffffa800ffffa000ffffa000ffff8888ffff8888ffff8800ffff8800ffff8000ffff8000ffff5500ffff5500ffff0f00ffff0f00ffff0a0affff0a0affff0800ffff0800ffff0100ffff0100ffff00aaffff00aaffff0002ffff0002ffff0000ffff0000fffefffefffefffefffcfffcfffcfffcfffc0000fffc0000fffafffafffafffafffa0000fffa0000fff8fff8fff8fff8fff80000fff80000fff0fff0fff0fff0fff0ff00fff0ff00fff0f0f0fff0f0f0fff00f00fff00f00fff00000fff00000ffeeffeeffeeffeeffeeffaaffeeffaaffeeff00ffeeff00ffeeeeeeffeeeeeeffee0000ffee0000ffeaffeaffeaffeaffea0000ffea0000ffccffccffccffccffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc0ff00ffc0ff00ffc0c0c0ffc0c0c0ffafffaaffafffaaffafff00ffafff00ffaeffaeffaeffaeffaaffeeffaaffeeffaaffaaffaaffaaffaaff88ffaaff88ffaaff0affaaff0affaaff00ffaaff00ffaaeeaaffaaeeaaffaacc88ffaacc88ffaaafaaffaaafaaffaaaaaaffaaaaaaffaa5500ffaa5500 else 0xfffffff0fffffff0)))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x20b801a182e0267a627e9a1995fa6725280999995fc6666581198 else 0
  | 3 => if page < 1 then 0x9961f6884a9961f8059f82dd660d3f82d824fc8f82dd46093f82dd66093f9ea5b7ed4a8fdd6609149961f809a29961f809b99961f809a09961f8099f82dd66f4ee9ea4d8094a9961f80956951d66a8ee995cc6a8ee99604654ee9d21f809a199602684c39961f805a182def6214a9961f7f5a1979ea6214a9961f6844a9961f801a19961f7004f9961f8099e9ea0b809a187df27002c9961d809a19961f7004e9961f8099c996637e9a187e026842b99618809a19961f684499961f7f1a1996538099987e026842599604809a19961f829989961f809a1 else 0
  | 4 => if page < 7 then (if page < 3 then (if page < 1 then 0x9ea6587e026866587e02684269961f82e026866598e1f809a19961f809a111a6587df2700229961f809fa6866594e1f809a19961f7c9c01366587e026841f9961f809a16666587e0a809a19961f7c9c01326587e02684419961f809a1662658c9d6621149961f620bc2b26587e022f0ac9961f5e0bc2b26587dd6620b09d21f759882b2657598830cac9961f7ad8852a6587e02684ac9961f620ac23e6587dd6608ac9961f6214a3fe6587dd6620a99ea0b759882b265945d65f4ac996327598829e6587dd665cee9961f6217152a6587e025c54a9961f759971466587dde6214a9a61f7598852a65759885d14a9961f7b58852a6587df2700519961f759a63ea6587dd63b8dc9961f809a138a6587dd6620db9961f7c9882b26587dd6621269b61f7598852a6575988528e09961f759882be6587dd66214a9961f759a617e6587df96994a9961f6214a2f26587df96985f9961f809a152a6587df2700ee0026587e026866587e025e0ac9961f759c01466587e02528bc9961f5e14a2f26587dd6700ee9961f7c98852a6587dd6620ac else (if page < 2 then 0x9961f809782be6e87dd66214a9961f7758852a6587dd662127995d66214a30e6587dec6214a9961f759882c66587dd66206d9d1d66214a30a6e87ded6214a995d66758830e65939d6620af995d6620c32be658f5d6620669961f759a519a1f759885282b996187598852a6587dd6621379961f759c01326587e026614a9961f7c9c01d26587e026850e9965d7a98852a6587dd66992f9964887e026866587df2700799961f809a10666587e02685149961f7c9c017e6587e02684ee9961f685882f26587e02684bc9961f685782f26593e1f809a19961f809a130a6587df2700129961f7c9c039a6e87df26214a995d66858830e6587d885284f9961f7bd8852a6587da65288f9961f7c9884fe7a82df26214a87dd6685880ae65871f26214a9961f6858821a6587df2621379965f7a98852a6587df26314a9961f759a64826587df76994a9961f759a619a6587df263d4a9961f7e58843a6587df26994a9965187e026866587e02684799961f7e5a60666587df9699149961f809c06866587e026845f9961f7e5a61066587df96990e else 0x9961f759884126587d88529009961f7c18852a6587dd66f8ee9961f7c58852a6587dd6620ad9961f7b98852a6587dd6620ae9ea387598852a6587de26214a9961f7598848e6587dd66e8ee9961f759882866587e025f14a9961f700ee23e6587dd4700ee9961f5e14a12a6587dd66f4ee9961f8094a3226587dd6700ed9ea0b759c03ba659361f8094a9961f759c00c66587d78528499961f759b83ba6587dd6700f49961f759c03ae6587e0266d4a9961f759c014e1f759c03b82c99619759c03ba6587dc03b88c9961f731c03ba6587e02528c79961f759c040a65961d66a8ee87dd6700ee09665811d6700ee9961f8094a2fe6587dd6701019961f829953ba6587e025c94a9961f6214a2466587dd6621459961f7598851a7a84dd66214a995d66094a30a6587d885288f9961f6214a20a6587dd6621249e9d66214a3026587dd66bcee9961f779c03ba6587dca700ee9961f7618852a6587dd6621449961f7598850a6587dd6635209961f5e14a2fa1f75988528c99ba1f759c03ba6f8e5d66214a996025e14a30e6587ded700ee)) else (if page < 5 then (if page < 4 then 0x87dcc6214a0b26287dd6621379821f6214a21a6587d7e528869961f7718852a6587dd662138865d66214a08a1f74d885282282dd66214a0126587ddb6214a9961f7598850254759aa6214a995fa759884de1f759885284b9965b7d18852a657f9f46214a95a0b7598852a6587d885288a9961f759884d66587e086214a9961f759881121f759885282d9961e7598852a6887dd66214a9960575988529d66214a0e425811d66214a09609811d66214a996046214a1d265811d66210e9961f6214a28a6587df76210e9c61f7598852a6575988528a4995fa79d8852a6587df9620a19961f655882866587e026545f9961f6214a24a6587d88528909961f759885066587dd66213f9961f7658852a6587dd76214a9961f7598851e658c5d66212f9961f7598e4be65759885a14a9961f7d58852a6587de46214a9961f759883f26587dd66f0f387dd66214a0b265865d66214a9961f809f97026587d885288c87dd66214a09665811d66214a9961f795c017e6587df97004199a1f7598852a65869d66214a9961f7958843a6587dd665c5f else 0x99617759884fe6586d885288f9521f759884be6587dcc6212f9961f6214a25a6c851d66214a995d66214a4aa65905d66211b9961f7598840e6587ddf6214a9961f7598849665849d66213f9961f7658952a6587dd6629429961f7598350a6587dd96213f9961f759844fe65841d66214a9961f759884ae6587de062d4a9961f7d98852a6587dd66206b99646759884526587dd6621289ea3f7598845265921d6609149d6147598852a65915d66212f9e21f6214a2621f73588528989ea0b7598852a6587d88528989e20f7598852a65915d662117995d66214a2767287df56214a995fb7594a1fa6587df56d94a9961f7edd61b66587dd61c46d9961f7d5880d265901d6621149961f6214a22e6587dd6621369961f759bc4be6587dd6528bd9c21f7dd8852a6587df76914a87dd66214a2666587d885289999645759884526587dd6700ef82dd66f58852a6587d88528899961f759884d26587dd67012d9961f759c03c61f7598852824996037598852a6587dd67010d9961f6214a24e6587dd66214987d885288c0b25487d885288c) else (if page < 6 then 0x9961f6213f24a6587dd66153f9961f6214a2566587d82528929961f759874fe6587d88528949961f4fcb923e6587dda6213f9961f759834fe6587dd66194a9961f6093f23e6587dd46093f9961f759be3b66e87dd66213f9961f7c5884fe6587dd6608ad9961f528b923e6587d884fc8f9961f759824fe1f759824fc269961f759884a61f6214a23c3d87dd66213f0f61f82dd66093f9e9d66214a0fa7a82d88528929ea0b7598851a7a6214a23c3d82d885288f0f67a82d4a2e48f9ea0c7598852a7a82dd96214a9ea0b7598850a7a759884fc3d82dd66213f0f67a82d884fc8f82dd66094a00e7a82dd66093f82dd66094a4fc0082dd66093f82dd46214a23e1f759885283d9e9d66214a0f60b759885283d9ea0b6214a23e7a82dd66213f9961f7e18852a6587dd66206a82dd66215952a0b759885289f9ea41759884466587d885289c9ea0b7d58852a6596e1f7ed4a9ea0b759881b66587d4a2e8929961f6154a24a6587dd5621469961f528bb23e6587d885208f87dd66154a0a61f7598852830996177598851a1f7598252829 else 0x9961f528ba23e6587d885188f9961f358b923e6587df36214a9961f759882aa6587da75288f9961f620ab23e6587d795284a9961f6254a23e6587d8a5288f9961f6214223e6587d8850c8f))) else 0
  | 5 => if page < 15 then (if page < 7 then (if page < 3 then (if page < 1 then 0x9961f759885f4ac9961f809d6620ac9963287dd6620ac9961f75991620ac9961f759882b00e9961f759882b0a79961f759c0620ac9961f759885ecac9961f759882b05f9961f759882b0519961f759c03b8519961f6214a374519961f7c988528ee9961f7598842cee9961f75988528e29961f759c0528510026587dd6700519962687dd66214a9961f759885cd4a9961f75988528079961f75988528509961f759a16214a9961f7c988528510026587df26214a9961f7598842c519961f759c03b8e29961f7c988528e29961f759885e0ac9961f759883b8ac9963787dd66214a9961f75988528df9961f75988528109961f75988528e19961f75988528ac9961f75988388ac0026587dd6620ac9961f759a65285f9961f7594a32c5f9961f759c06205f9961f759882945f9962987dd66214a9961f759885954a9961f75988528099961f75988528569961f759c06214a9961f7e5885285f9961f759885814a9961f75988528fa9961f75988528419961f75988528519961f759884185f9961f6214a3305f9961f621063305f9961f759a66205f9961f759a64185f0026587dd66985f9961f7590632c5f9961f75988294519961f759c0528ee9961f7e5884185f0026587dd6700ee9961f75988528ee9961f759885285f0026587dd66214a else (if page < 2 then 0x26587dd6620af9961f75988528669961f75988414669961f7c9d6700ee9965387dd66214a9961f759885284d9961f759885281f9961f759996214a9961f809a16214a0026587e026854a9961f759885290e9965d87df26214a9961f7c988528799961f759a1620199961f759a1621149961f7c9885285f9961f759a6528ee9961f7c9c0528ee0026587df2700ee9963a87df26214a9961f759a1620c29961f7c988528129961f7c988528e69ea6587df26214a9961f7c988528269961f82df26214a9965f87df26214a9961f7c9885284d9961f759a16201f9961f7c9ea6214a9964887df26214a9961f759a6528799961f7c988528199961f7c988529149961f7e5f26214a9961f759a16205f9961f7c988528419961f7c9885290e9961f7c9c06214a0026587df96994a000009961f809a19961f80978528ac9964887dd6620ac9961f6214a374799961f759882b0199961f75988450ac9961f6214a3745f9963287dd66214a9961f75988528fd9961f759885280e9961f75988528a79961f809885e0ac0026587e025e0ac9964f87dd6620ac9961f75988308ac9961f6214a374129961f759885d8ac9961f759a1620ac9ea6587dd6620ac9961f759882b0269961f82dd6620ac9965187dd6620ac9961f759882b0799961f7594a32c19 else 0x9961f84dd66214a9ea6f87dd66214a9963a75988528269961f75988528839961f759885292c9961f759885292f9be1f75988528199963a75988529149961f80978528c29ea6575988528c2995d66214a3082687dd66214a36819995d66217d528c29963387dd66214a9961f75988528ea9961f759885280f9961f75988528c09964887dd66214a9961f75988528f39961f75988528799961f759885d54a9961f75988528e49961f759c03b81287dd66214a378129961f77988528ee9961f72988528ee9961f75988488ee9961f75988528e69963a87dd66214a9be1f75988528129962187dd66214a9961f845d66214a9961f75988528029961f7598853d4a9961f77988528120026587dde6214a9961f75988529269961f74588528120026587dd6621269961f75988529209961f759884f0129961f759c03b8e69963a75988528e69ba1f75988528ee995d662178528c39961f7b588528ee9961f759885e0af9961f75988418669961f75988528129963987dd66214a9ba1f75988528e60026e87dd66214a9961f75988528c3995d662177528c30026575988528c39961f75988528119961f75988528e59961f75988528c2995d662176528c29961f7599a6214a9961f7b588528e60026587ded6214a9961f75988528af9961f759885dcaf)) else (if page < 5 then (if page < 4 then 0x9961f7598f528519961f7598842c5f9961f6214a3b88f9961f75188528ee9961f6214a4188f9961f759884fcee9961f75988528c89961f75988528ed9961f75988528f59961f75988528e79ea0b75988528ee9963887dd66214a9961f75988528319961f62178528869961f759884ccee9961f75988528c69961f75988528ec9961f75988528fe9961f75988528e39961f75988528f49961f75988528eb9961f7599b6214a9961f75988528539961f75988528c49961f759885a94a9961f7598c528ee9964875988450ee9961f759b7528ee9961f75988528b29961f759885714a9961f7598f528ee9961f75988528bc9964887dd6700ee9961f7e588418799961f759c03b8199961f759c0450ee9961f7e5d6700ee9961f809785285f9961f759c03b85f9961f7e588418ee9961f80988528bc9961f62178528bc0026587d88528bc9ea6587dd6700ee9961f759c03b8269961f82dd6700ee9965d87dd6700ee9961f759c03b8799961f80978528199961f759c7700ee9965887dd6700ee9961f80978528469961f759c03b8229961f759c06a8ee9961f829d6700ee9961f80978528419961f759c03b8749961f759c0654ee9961f80978528bc0026587e02528bc0026587d78528bc9963a87dd6700ee9f26587dd66214a9961f7598852828 else 0x9961f759884cc5f9aa1f75988528099962087dd66214a9961f859d66214a9961f75988528019961f759885454a9961f78188528099961f759885314a9961f75988529329961f759884f8099962975988528569961f7dd885285f9961f759884205f9962887dd66214a9961f759885994a9961f75988528089961f7598852855995e875988528569961f759b26214a9961f7dd88528569961f7598857d4a9961f75988528fb9961f75988424569965887dd66214a9961f75988528469961f75988528229961f759aa6214a9961f809f96214a9961f7e5883305f9961f7e5c06205f9961f7e5882945f9961f795882945f9961f809885814a9961f759926205f9964a87dd66214a9961f759885286e9961f759885281b9961f759885754a9961f829d66214a9961f75988528749961f809e56214a9961f759885805f9961f7597b2945f9961f641885285f9961f759906205f9961f759c0620fa9963c87dd66214a9961f75988528b39961f75988528149961f75988528f79961f7e588528fa9961f759c017c419961f7597b528419961f795885285f9961f759884385f9961f7e588528419961f7594a328419962487dd66214a9961f759c36214a9961f75988528059961f75988528409961f79588528419961f75988438419961f759c017c51) else (if page < 6 then 0x9961f759884fc5f9961f759885bd4a9961f759885285e9961f75988528699961f75988528579ea0b759885285f9964187dd66205f9961f7598817c349962787dd66214a9961f759885282e9961f759883485f9961f759885b05f9961f75988528689965d71d885285f9961f759ae6214a9961f6214a2205f9961f72d885285f9961f759885a54a9961f759885285d9961f75988528b49961f75988528529961f759885445f9961f759884885f9961f75988528679961f759885285c9961f759b26205f9961f759882985f9961f759885794a9961f75988528429961f7598833c5f9961f725885285f9961f6214a3345f9961f759883645f9961f6214a3645f9961f759956205f9961f809d67005f9961f759c01c05f9961f809885714a9961f759966205f9ee6587dd66214a9961f75988528279961f839d66214a9961f75988528869e66a87dd66214a9962975988528799961f75988528809961f759885291d9aa1f759885281999629759885291487dd66518852819995d664d88529149964b87dd66214a9961f759885285b9961f759885281c9961f759885894a9961f759c46214a9961f759885285499648759885954a995e675988528799961f759885b14a9961f75988528199961f759885291487de975988528099961f781885285f else 0x9de1f75988528229962387dd66214a9961f835d66214a9961f75988528049961f759885494a9961f759885291c99658759aa6214a87dd66ed88528269960b759aa6214a87dff7598852819995fa75988529149965687dd66214a9961f75988528489961f75988528209961f759a86214a995fa75988528469961f819d66214a9961f759885284387dd6701885282599604759c06214a9966487dd66214a9961f759885283f9961f759885282587e0a75988528250021f75988528259961f811d66214a9960a811d66214a00265811d66214a9961f7598833c419961f6214a1e4749961f71d88528749962b87dd66214a9961f759885694a9961f759885280b9961f75988528729961f82988528749961f829d66210e9961f65588528799961f759884510e9963e87dd66214a9961f75988528a39961f75988528159961f759885290c9ce1f759885282299648759aa6214a9961f7e588528869961f759c06212f87dd66214a2e022995f475988528799961f809e76214a9961f759c0620f39961f7e588528749961f759c06210e9961f809c0528749961f809f96210e9961f7e5885290e0026587df96210e9961f809f97014a0026587e027e5c09961f6214a23c5f9961f751885285f9961f7594a2e45f9961f759825285f9961f759883585f))) else (if page < 11 then (if page < 9 then (if page < 8 then 0x9961f75988528039961f75988528169961f759884e4199961f7598834c1987dd66213934c199964887dd6621149ce1f759884e4199963487dd6621149961f759884e4169961f701885288f9961f809d66213f9961f759885284a9961f759bd6214a9961f7e5885288f9961f759c06213f9961f759c26214a9961f759ab6214a9ea0b759c06214a9965587dd66214a9961f75988528389965b87df96214a9961f759c0620349961f75988528499961f759b86214a9961f759c56214a9961f75988529109961f759c16214a9961f759ad6214a9961f809e06214a9961f759c0621209961f81dd66214a9961f75988528759961f809f76214a9961f759c06206687dd6701885282c99619759c06214a9961f701885288c9961f809d6621379fe6587dd66214a9961f759885282c9621f759885282c0021f759885282c9961f865d66214a9de65865d66214a00265865d66214a9965887d885288c9961f759885288c0026587d885288c9966387dd6621379961f75988529370026587dd6621379966187d88528869962587dd66214a9961f759ac6214a9961f75988528069961f75988528459961f79d88528469961f7598856d4a9961f759885290f87dd66214a2802287dd66214a0982287e0b759885282287dd66214a08c1987dd67358852822 else 0x9ca1f75988528169961275988528169961f759885414a9961f75988529219961f75988529179961f759884e8169ca1f7598852911995d671d885287e9961f7d588529149961f759c76206d9961f75988450349961f759885287e995d6719885287e9961f759b06214a9961f7d588529110026587df56214a9961f759885286d9961f759c66206d0026587dd66206d9961f75988528349961f75988444349961f6214a234799961f73588528799962f87dd66214a9961f759885291b9961f759885280c9961f7598852876995d671d88528799965d87d8852879995c76214a23479995cd71d88528799965d71d88528799965787dd66214a9961f75988528479961f75988528219961f759a96214a9961f75988528739961f759885290d9e66587df76214a9961f759b2620199961f7dd88528799961f759b2621149961f7598834c669964887dd6620669961f759881b0199962a87dd66214a9961f7598858d4a9961f759885280a9961f75988528599961f759885854a9961f75988528f89961f6214a338569961f759884e4f39961f759b7528e69ba1f7598852914995d66217f528c39961f7b588529149961f759885fcaf9961f759884e46699648759885291487dd66214a34c199ce1f75988528199962287dd66214a9961f83dd66214a) else (if page < 10 then 0x9961f75988528e89961f75988545149961f759884ed149961f759885291a9961f75988529129961f759b16214a9961f75988528979961f759885b1149961f759885394a9961f759885287f9962e87dd66214a9963687dd6621149963587dd6621149965a87d88528799962275988529149961f759884e5149961f75988528999961f735885280c9963f87dd6621149ea65921d6621149964875988450269da1f7597f52819996517597d529149e66587d88528999961f73588528990026587d88528999ce65921d6621149964875988450199e61f759885289987dd673588528990021f75988528999961f759884fd149ca1f759884e5149961f851d66214a9ca1f75988528269ca1f82dd66214a9961f75988528859961f759885292e9da7287dd66214a9964575988528799964587dd66213f9961f759885293f0026587dd66213f9965c87d88528799ca1f75988528199964587dd66211499645759885291400265915d662114995cd71d885287e87dd66214a278269960b759885287e87dd66214a3601999648759885287e995d66214a2dc799ea6587dd66214a9961f75988528269961f759885b54a9961f75988528e987dd66214a360169961275988529149961f759884e9149961f75988529119961f7598834c169964587dd66214a else 0x9961f75988528299ea6787dd66214a9962275988528269961f759885287a9961f75988529169ea6583dd66214a9960f75988528269961f82dd66214a9962c87d88528798d21f75988528199964287dd66214a9961f759885283299612759885280399e1f75988528199961f76588528199961f75984528199961f759884fc1999e1f75988528039961f7598852d4a9961f76588528030026587dd96214a9961f75988529429961f75984528030026587dd6621429961f759884fc039962275988528169961f759884e8199964987dd66214a9961f75988528779961f759885281a9961f75988529199961f75988528619961f75988528f19e66587de06214a9961f75988544199961f78188528799961f73d88528799964887dd6621209964687dd66214a9961f759885287c9961f75988528179961f759b56214a9961f75988528649961f74188528099961f759884f4199961f7598c528129961f77988528199961f75981528199961f759884ec199961f6214a4508f9961f75982529149961f71d885288f9961f759885289a9961f7598854d4a9961f75988551149ea0b75988529149964187dd66211487dd66217f528299961775988529149961f73588528869961f759884f5149961f75988528879961f75988529139961f7598859d4a)) else (if page < 13 then (if page < 12 then 0x9962f87d88528799962f75988528799961f75988528819961f759885291f995c86214a2347987dd662158528269960b759885291b99648759885291b9961f759b46214a9961f759885285a87de3759885280c9961b75988528799961f78588528799ae1f759885280c9961b759885280c9961f759885514a9961f785885280c9961f759885354a9961f75988529309ae1f7598852876995d672188528799965b87d8852879995d672188528769964187dd66214a9965b87d88528769961f759885ad4a9961f75988528f69961f6214a2340c9965987d88528799964c87dd66214a9961f75988528589961f759885281d9961f759885914a9961f759885286f9961f75988528f99961f6214a428799963b87dd66214a9961f75988528c19961f759a36214a9961f75988528a89961f7597a528469961f79d88528799961f759885b0569961f6214a23c199961f75982528199961f75988358199961f75988528369961f75988550199ea0b75988528199961f855d66214a9961f759883501987dd66214a0a8199421f75988528199962d87dd66214a9961f75988528189961f759885287d9961f75988528139961f75988528359961f6214a26c799961f7598835c19995d66214a26c7987dd66214a35c199ce1f7598834c199f66587dd66214a else 0x9961f75988528920026587d88528929fa6587dd6621469961f75988529460026587dd662146a026587d885288f995d66214a0f00c9f61f75988528299961f759885554a9961f75988529159f665851d66214a9964487dd66214a9961f759885282f9ea1f75988528299ea65851d66214a9964887d885288f9965187dd66213f9965d87d885288f9964887dd66213f995d66214a0ec269961475988528269e66587de16214a9964887dd6621179ea4882dd66214a9964387dd66214a9221f759885282c9ce65865d66214a9964887d885288c9965187dd6621379963087dd66214a9961f75988529189961f759885280d9961f759885b94a9961f75988528f09961f75988354099965887dd66212f9964787dd66214a9961f759885287b9961f759ba6214a9961f75988528639965d87d88528869964887dd66212f9ce1f759885282999648851d66214a9961f75188528799961f7594a2e4799961f759884fc799961f73988528799ea0b75988528799961f759883443487dd66214a34c299961f6214a238799961f74988528799961f75988529319961f75988528789961f75988528c59961f6214a23c799ae1f6214a234799ae1f75988528269ae1f82dd66214a9962f87d885288f9961f759885288f0026587d885288f9e66b87dd66214a) else (if page < 14 then 0x9961f759825293f0026587dd66093f9961f751885288f9961f759be6214a9961f75988528609961f759884fc169961f759bf6213f9961f75188528609961f759884fc5e9961f759884fced995d66214a0f42687dd66214a0f4269961f6214a23c269961f759884fc269ea6587d885288f9ea6587dd66213f9e9d66214a0e8269ea1f6214a23c269ea1f759884fc269961f75988528629961f75988528f29961f759b36214a9961f75988528659961f739885280c9961f75988550169961f759885283d9961f82d885288f9961f82dd66213f9ea1f759885283d87e0b759885283d0021f759885283d9ea1f82d885288f9ea1f82dd66213f9ea0b759885283d0027a759885283d0020b759885283d9f67a82dd66214a9ea0b759885288f0027a82d885288f9ea0b75988528039ea0b759885293f0027a82dd66213f9ea1f75988528269960b759885282687dd66214a0e82682dd66214a0e8269ea1f82dd66214a9ea0b75988528260027a82dd66214a9ea4182dd66214a9961f75988528849961f759885292d9ea0b75988528769ea0b75988528349961f75988340349961f7598855d4a9961f759885291e9ea0b75988529119964187dd6621119961f82df56214a9961f82dd66206d9964887d88528929965187dd6621469f66587d8852892 else 0x9ea6587d88528929ea6587dd6621469f66587d885288f9ea6587d4a2e48f9961f6214a2e48f0026587d4a2e48f9961f759885c14a9961f75988528ef9961f6214a23c0c9961f621705288f9961f6214a41c8f9961f6214a23c4a9961f6214a23c5e9961f6214a23c039961f75988358039ea6587dd96214a9ea6587dd6621429961f6214a4fc8f9f66587dd66213f9fa6587dd66213f9ea6587d884fc8f9961f759884fc8f0026587d884fc8f9961f75982528039ea6587dd66093f)))) else 0
  | 6 => if page < 5 then (if page < 2 then (if page < 1 then 0x26587dd67018817e6587dd66214a2d45f9961f75988528a517c009961f759882945f9962987dd66214a17c009962987dd66214a9961f7a1d66214a17c009961f759885954a9961f759885285f024009961f75988528099961f759885285f158009961f75988528569961f7e5d66214a17c009961f759c06214a0026587df96214a17e6587dd663d885285f0026587dd66216052a6587dd66217b5285f0026587dd66214a3ea6587dd66214a17c410026587dd66214a1066587dd66214a17c510026587dd66214a3ba7a9961f75988528ee9961f75988528ee09a6587e0b75988528ee9965d87dd66214a3ba6587dd66214a3b8799961f759885e14a0666587dd671d88528ee9964887dd66214a3ba6587dd66214a418799961f75988528ee0666587dd66214a450ee9961f7e5d66214a3ba6587dd6621785285f9961f75988528ee17e6587dd66214a418ee9961f759c06214a3b8009961f759c0528ee000009961f759c03ba658ea1f75988528ee002658ea1f7598852a6587dd662178528c20026587dd66214a30a6587dd66214a3b8120026587dd66214a04a6587dd66214a3b8e60026587dd66214a39a6587df275988528ee0026587dd668588528009961f7c988528ee000009961f7c98852a6587dd662178528ac0026587dd66214a2b0009961f759885e0ac000009961f759882b26587dd66214a3b8510026587dd66214a1466587dd66214a3b8e20026587dd66214a38a6587dd66214a4185f0026587dd66214a17c009961f759884185f else 0x9961f7598852914058009961f75988528169961f7598852914444009961f75988529119961f759c76214a1e4009961f759885287900265759c76214a1e66587dd66dd88529140026587dd66c98852a6587dd673588528660026587dd66214a19a6587dd66214a450569961f759885291439a6587dd66214a4e4190026587dd66214a064009961f759884e4199ea6587dd67018852a6587dd670188528269961f82dd67018852a659761f759c06214a9961f759c06214a1e66587e0275988528199961f809d66214a452659621f759c06214a002659621f7598852a6587e0275988528460026587dd66214a11a6587dd670188528220026587dd66214a08a6587dd6701aa6214a0026587dd66a98852a6587e0a759c06214a0026587e0a7598852a6587e0275988528419961f759c06214a1d0009961f75988528749961f809d66214a438009961f759885290e9964887dd67018852a6587df975988528799961f759c06214a0666587dd670188529149961f7e5d670188528009961f809f96214a9ea6587dd66214a17e6587dd66214a17c269961f82dd66214a17e659761f759885285f9961f759885287917e6587dd66214a328199961f759c76214a17e659461f759885285f9961f75988528b617e6587dd66214a1c0199961f759885f54a17e6587e02759885285f9961f759885287017e659221f759885285f9961f75988528d117e6587dd66214a17c199961f759885291417e6587dd66214a3305f0026587d88528cc17e6587dd6701885285f) else (if page < 3 then 0x9961f759885b14a1e4009961f759885b14a9961f75988529091e4009961f75988528f39961f759885287911a6587dd66214a1e4569ea6587dd66214a0666587dd66214a0e8199961f75988528260666587e0b75988528199da6587dd66214a0666587dd66214a234199961f759885281e066659461f75988528199961f75988528790666587dd66214a0dc199961f75988528d3064009961f7598834c190021f75988528d3066659221f75988528199961f75988528d10666587dd66214a0cc199ce6587dd66214a064009964887dd66214a0027387dd66214a0666588a1f75988528190026588a1f7598852a6587e1275988528190026587e0f7598852a6587dd66214a064030026587dd66214a00e6587dd66214a064169961f7598c6214a064009961f759885454a9961f759886014a064009961f75988529209961f75988528190266587dd66214a064120026587dd66214a4527a9961f75988529149961f759885293909a6587dd66214a450269961f82dd66214a452769961f75988529149961f75988529391e66587dd66217d528199961f759885fd4a452659461f75988529149961f75988529141e66587dd66217f528199961f759885f54a452739961f75988529149961f759cd6214a1e4009961f73588528799961f75988529140666587dd66214a4e5140026587dd662139452659221f7598852914002659221f75988450009964875988529149ca6587dd66214a450009964587dd66214a9961f759cd6214a1f8009961f759885287e else (if page < 4 then 0x21f759885283a09a7a9961f75988528260027a9961f75988528009ea1f75988528260026587e0b7598852a6587dd662154528260026587dd66215452a6587dd66214a4e8260026587dd66214a45e6587dd66214a0980c9961f759885282605a7a9961f82dd66214a0027a87e0b75988528000027a82dd66214a9961f82dd66214a098009961f75988528260026582dd66214a09a659061f82dd66214a002659061f7598852a6587e0b75988528769961f82dd66214a0d0009961f75988528349961f82dd66214a4467d9964887dd66214a0027d9961f7598852a799961f759885280c9964887dd66214a0a4009961f75988528299ce6587e1475988528009961f851d66214a9ea659221f7598852a739961f75988528269964887dd66214a09a659221f82dd66214a9da659221f7598852a659624887dd66214a9964887dd66214a218009961f75988528869e66587dd66214a026659461f759885292f0026587dd66214a4be659464887dd66214a9ce659221f7598852a7a9961f75988528799961f759885288d09a6587dd66214a1e4269961f82dd66214a1e6799961f75988528799961f759885288d1e4009961f6214a234799ce6587dd66214a1e66587dd66214a2e0799964887dd66214a1e66587dd66214a2d8799ae6587dd66214a1e4009962f87dd66214a9961f78dd66214a1e4009961f759885291b9961f7598852879030009961f759885280c9961f75988528791d8009961f75988528769965d87dd66214a1e4009965d87d8852879 else 0x27d9ea6587dd66214a9ea6587dd66214a23c009ea6587d885288f0026587dd66214a23c000026587d885288f9ea6587dd66214a00e7a9961f759885293f0027a9961f759884fc009961f759885293f000009961f759884fe6587dd66214a0e826))) else 0
  | 7 => if page < 1 then 0x9ea6587dd66214a000009961f7598852826000009961f82dd66214a000009964887dd66214a000009961f7598852879000009961f7598852819000009961f7598852914000009961f759c06214a000009961f759885285f000009961f75988528ee else 0
  | 8 => if page < 1 then 0x26587dd66214a else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 7
  | 3 => 43
  | 4 => 396
  | 5 => 921
  | 6 => 267
  | 7 => 10
  | 8 => 1
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
  | 2 => 15
  | 3 => 80
  | 4 => 754
  | 5 => 2010
  | 6 => 644
  | 7 => 40
  | 8 => 1
  | _ => 0

def keys (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xfd46aeb1e9a04606d7aa9904c65acfcdc4778d30bfe11ceca5b92b0ba3410b029426d3bc93d83cde827ba2ff6da78e6c1ac2c079080b84bc071b53c6 else 0
  | 3 => if page < 2 then (if page < 1 then 0xc3198c97c2fa510ec29e134ac26eb98cc238f73dbcb4c1beb4b99fcdb1564eaead50d99ba69beeb5a1b72ec7a12b3737a0bf74669b72a1749b3d7be69a6d5d6499e1aee2993f35e9971da81e96caf49995bc98e895b991a190a11a887e78e4ca7c53c0cd7bb54e0f78925bc97702b7a0751fe72474e801c574d150467429b7fa72b456eb701d691169bc52e76966216968b97d77671ee0506401b0fe62720cd55e094a2459aac38c57008aac56f4ddd74b7253b54903ed66397254b138cc9218360b441d33de8cda2f8a00e42c1326ad2a83828427a1582a26c2140426b5a53e254f5c161f0452801ee16f9b1e555e4c1b4427970694389e056a3ebb003ac192 else 0xf519d910f249e759f1c8ad2bf0694986ea27c6cce367e3b6dfbe7d42def68afadebb9a26de065a04d17bc4a6d08e8fb3c94ee2aec8f1449ec6eb344ec3c89b66) else 0
  | 4 => if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0xfbdc1b00fa983c00f3aebd40f2a23770e0baec20e0126340db7c1bb0d79fc2d0d6155e40cf64a5b0cce04290c53c1270bea58040bdc02110bd1748e0ba2bc010b8d611a0b11bdf80a7706720a0d54530937ae43087259c3085e519c084e6e6c081405e10808ed7907cf8b8d07948baf077f2b56076f85a70709a4f0070646e906e6c7d006bf1b4405fb531205dfe17e055723a70541e2cd04e8fe1c04a275500497a17604726803045370ec043e22c3043bc3460417ffb103d18ebf039973b70303c5e302fe2ceb02e1843a02bfd5f002ac1f1d0298cac0024806dd021e72fe01f37b6501ef7fd501d522b50172f76f0144dcd2013031c7003de835002af814 else (if page < 2 then 0x26bb2c9526b5f703269f97b525f46e9a254e6c4b24f6412724ee96f52465b0642458d34b242144b1241dd9a323ccb31a238569812308ff6522d9d8db229658f0228795b222456ab121c5d51b21aea31a2185e1ef215a2f852149712d210d288820e86abc2097341020239f0320098d611ffed6bc1fbfbcf31ef175d41e383a781e08ec991dfaf45f1d945c101d8fd48a1d630db61d5b9f381cfc20851c2e008c1c2ca21a1c15a1e71ac567a11a4f9e6919cedb9e181963de17b64260163e283016394c0d161899f715996dbd14ba02b413d4efc513cf24131342456312ee693312454b9c1215f74111d2235111727bdd110bb31e10d2c37f10c13e45105ffed6 else 0x3c862bc73c3fe7093bfe74693aecb73c3a1b8ade39c3ad0639b7274b3927664a38f5e1943881f724388190c63840092037ff5a2f37a0a07537586f8a374b21353741412f364cbef635c2338a35b7069034f6da1c349cd57a34759a33340db7ee33de8cda33d0f209337f6bcb337e6fb63337ddc432be775932659f3f3232adf331cdf52c313dbd8730fba7e030e5dfaf30cb595230347d3b2fce04cb2f4aeea52f07398e2ebc45172e59043d2e34f5172dc0b9532d59ecc82cbc10bf2bd968be2b9af60d2aceddfb2ab3c6e32a712b752a13d4902a0c444529c2910a29a1c3fb29815276294eacd4289a8dba28121fd227df1fb327ae6611270bda1126c443b1)) else (if page < 4 then 0x52030fbf51141ce0508e8f155081989b505ca12d502cf42a4fc946944f4d73fe4f21ac774edc05ab4df2fd534dc0fb8a4d92791e4d6460fd4d5f10454d5a14384c597fd24c2c4b7b4ba96c654b925d5f4b79c80b4b5edc454b33409b4b14be384adeb36f4a19c83c49f0766e491ed69448bda19c484df859481e581947cfaec646bb1c124643df2045fe8c3a459267bd458cd0684563f91e455ef24744acbdb54415dc7143ca849343c7f28343c5551043c485264391465243284a4641d3aeeb40aeb9c040809b194064bf643f25cd8d3f1d3f4f3eecfbde3eeae6873e94d3e73e92f9373e09e68e3d8e18923d4565a03d0179173ca2b9283c98c0073c97c480 else (if page < 5 then 0x6c75361f6c5a344a6c4358826bf556236bc6db776b560aba6aee6cf66aa6a2cf6a9cc01b6a86a63a69ff445269e5afac69b1ef8b6966805e68fe98ab678c20c666f5c3df66f2a31a66d907ee6688349e6644519b66339c66640268d46401b0fe63fa34326385d5cf6326347662fb7dfa62b4aa8c62a3e95962a1e13062720cd55f0da96c5e6fb08a5e5962255e3daaf95e01c4635de974f05dd692505cda37d25c3db2f35a7273cf5a5c125259e904f459d94b095974d20a58a29e05585c797c57f817b25772b3b95711ad095645ea8856376197558cb757556fdb3c5563eb08546dede05436128953365149530f79c952ba59b85270cddf524d51365216e167 else 0x812710bd811b02ab80f9451c80c0703a8049145b8027c9e0800682227ffcdb0f7ffa87197f47d3ae7e5e6fd57e3269717d75438e7d25f5057ccecbac7cb0c4487c523c1d7bb67cd47b866eaa7b6670cc7b1ecfbd7a53f1f97a26351b7a231f35795fbd92795105cc790244ae77e5c7657783714b776c6cc9776a2153770fe123767caac77674b87876342b43760ef3ae7534bdcb752ba97574ffdcf67466b201745d8f4e74375a84739d73c77344731d72eb04b272b456eb71ff1d8971f5e2c771b5e5c0713a0738712f14067115f09b70fb573f70f97aa770f090c970c98d9870bc3af770a5d0a9705988546fa8ba3c6ea908f06e1ac4cd6d7c99be6d43049e))) else (if page < 9 then (if page < 7 then 0x9c1baad59bf5ddef9a9273aa9a5ec7259a4641af993db74e992625fc984013dc97af6271974327b496a64ce29684af539677816f96594391962c035395b991a195a83cfb94a2aa889436f3e9939fc7fc9248493491eaf7338f35089c8e1aa0558d82f64e8ce475358cb2c2378c1849838ba4a60b8b1dac0c8abaf6008a29332d89ffd7c189cc9ebe89a341b5888a914887ee505f871036c886bef20d869bcd06866eb934862dac8a85af85db859105ca85813b948576481f8533c98185206a0784e4295c847eddfc84503ba3844147b3843bdfd983c938ae83c009798389a7e183572aae8282bb5781efb31981ce4c5481b892d1819cb91981873995813792a7 else (if page < 8 then 0xb0f8e614b0baf3f0b060bf1db037cec3af9c0051af45d744af20c71eaf206c29af1d2abbaf0f9435ae7dd79cae39024eada1d879ad3b77a3ad2a71aeaca58b77ac65a03bac553c52abf60cb4ababd37aab4e2638ab49e604ab192efdaa75283aaa5c6771aa5ae357aa069a12a9900196a98a3cb5a94bfd96a91523d4a8e794f4a8e1d449a8de1861a8bcab80a8a3b6f5a86babe0a7b299caa7890c4da77995f1a6ed9c80a6e4cb87a6429ed2a4b45fa6a4ab41a8a428c44ba3704101a334a016a1ee2e96a1bb3998a0691c21a0548c05a051c47aa04eb70aa0365f14a02c1f659feb76869fe369cf9ee3d8fa9db0373a9d8850b69d19d4619cb0cab69c8410c3 else 0xc3a8413bc395a523c34f12ffc2cf54dac281478dc2463feac206f766c1ee6212c1bef787c1518421c12c066ec0ca2e3dc0a30933c0a1140cc056b75ac041bdbac0325254c002ca7dbfe58434bfadd0acbfa8d49fbebff5efbe50ad57bcb87927bcb19fbdbca8a810bc66a617bbee1d90bbdcab36bb8808efbb7992e2ba7145a8ba52e9f4b995690cb98a26e1b8fef596b8ecb1d0b8ea9be1b89c6e8cb8491bd0b8165431b7f5590bb7f4e3e0b7adb2aeb6e552c1b69c783ab6022eccb5dbcbbfb5ba8797b562a333b52cef8cb523a9e7b4ea7e90b404ce3bb3b1b92bb315f200b30d5a0eb21e50e1b1f06346b1b57b99b16e9997b13bbc45b136bd82b11da49d)) else (if page < 10 then 0xd9ddeb3fd9b087ffd83e83b3d7da00d7d74c6183d7397d19d72c07a7d706884ad6aedf8ad60fc402d5c9376ad58a26cfd3fa82a6d339857ad32cf550d3278d79d284a609d1ddb963d1d568b3d1c90fa3d1b49252d19b9808d13fb193d11a3534d0cc0594d02fbf16cf5c4526cf51411bceea5840cee6f7fdcec6ef35cd8eae2accf5b0a6ccf5b067cceaf226cccb0ab1cc8075fbcc05669acbf5399fcbe3046ecb3ff88ecae4c4bdca86fb77ca81a87dc9fe63f7c929f8f3c8a75555c82a6e8bc7adb944c6dc6329c6bf88f3c6bcae47c650b510c61191c0c6092aa6c5ea46eec596467ec592262bc5527cdbc4dd4dd5c4781d35c407a417c3e3035cc3dd5890 else (if page < 11 then 0xf1461923f06857f9ee819c66ee353d37ed9601eded42763fecdcc2caecb2c067eca7d441ec554b78ebe3577beba0437cea77de85ea5146b4e973006de8ba7cc0e8903fcce8229c66e8104c6be7bacb37e78a8aa2e755e04fe6f129a0e6ed19e6e66d0717e5c007b0e5a5d1bfe5a43d75e55013b0e4ef05a4e4850a00e4370e84e42a6d1ce406fbf6e3c06f87e3b9465ee3b1cba1e37162afe33f5130e2f565d7e2cc7f3ee2817b09e1dde21ee1837dabe164fde9e07bb590dfe2bec5df8caa52df3a0a3bdf04dfc4deef5101dece3109de73880dddf7af3add0339c5dcedf4addce76b74dc84d878dbef01dedbcc377fdbad1babdb5b8afbdb34f41bdacfc2a9 else 0xfff57c80ffc10cd6ff4daf90ff3fd4a3fe6e117afe5c07f5fe571042fe45d39dfde387e4fdc87c3ffd84d0cffd32fdbffcfc6c92fcdabb2dfca1ee46fc7e5d5efc65324dfc49864efbe438defb3f7f2cfa0b73e3f94f3336f94280adf9287374f8f7555ef8b0fdf4f7cf55fbf717bff7f7020fc2f6fb2954f6bcdc46f6ac4408f67e375ef6601e43f63d72b7f6268a11f61d3b5af5ef58bef58155f0f56b6277f5340054f4dc2370f4a70378f47eb612f4553068f402b99df3ba5470f38166fef2e78d15f2766b4f)))) else 0
  | 5 => if page < 32 then (if page < 16 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x790ab26078ff13407312e7e072fd62707158d91070a570506fde88d06e4ce2706d88cb406b5c1f9069285f1068d8698068cf04f06841509067f578d063c4bea0632dedd060aa05e0605067906018bfc05f23fcc05f2092305c7923405b3e8d10571db9405602310054b497d053c177704a58d60048e51cc046916550467c9de037a2dbc037209d3036efddb036dbf7c0366b03403641b5c034d853c03344f010331fb160309786e02cb1a8802b51fb702a21b7f028960dd02879e2102685b21025ca4a401e7497901b9e439017826f7015c31b301501ad600fedace00f74a8300e6eeac00bef6d300ad9748008cca3900887dd00085c6f6007a5eb30031e36d else 0xe340bd00e2c7aa60e1470d10df2e2170ded48200de56d930dd9b2660db7c1bb0dac0e360d9b676f0d9b33cb0d15ef310d1183680cdf08a10cd671c90ccbe7a90cb9400c0cad82140c869bbc0c85c1300c16f02f0bf8f3da0ba2002e0b54d7550b4b675b0b4aeb5a0b29761d0ae0dfd80ab165380aab78300aa72b6f0a802d0d0a6398880a526ff50a170b6f0a1460160a055ac809e7d16b09b7ee4409b7254309a87a7e098f8ab0098d9302098d0f7309749d180965680d094db4e40937ae4309314c01092485bb08b8fb6a0899e809089383d508731d03085e997a07fdc3af07ef6f5f07e8543007dd9f3c07dbb0c607d203b507d145f507b65f9007968831) else (if page < 3 then 0x1716f07e17140bae170b73a016ef146216c902a616c8e3a816c336f416aa0bd816a63d92168b8caf16652b3415ee443915d91bfb15c8659f15838edd153339b514fb3daf14face1b149a34791483c5441452408e1414b66313d4efc513d4616a13bd1eee13b1538a1389c79013424563133411ae13255cfa13112279130e6be512a7b511129d96a11298bb66124cef6c12454b9c12289a9b12228d5c11f36b3111c0552511afd4b1115d8a80112571731107499e10f5f8e510ea93ac10d5272410d2c37f106e0f0e103a988a0f5f2e460f4767df0f3aebd40f03c24f0ef73cd40eea606d0ee72c3a0ee3afa40ed014f20eb416c70ea85f000e9c2a590e910b5d else 0x1e01d9a21e00492b1df3730d1dd520631db1afc21daa0e5e1da99c1d1da455611d945c101d8fd48a1d5c840a1d5331431d5193bf1d2d7e381d263a111cf08e631cc800771c8425f31c7765ba1c751f6f1c4cf3fb1c36eb551c2aead11bf767f61bf592c21bf08f1c1bbf41811b825ba01b6ee8ef1b591bea1b1e60bf1b11cc4d1afdc4fd1ad1e8591ac3e4691aafd6111aa9050f1a5dd1481a5daa8d1a50534b1a23bc8c1a0f991119eae06419bb598519ab432b19a750fd199fb3571983a81c195dd8241935aee71919258b18fbda6b18f3e8b018e578ee18d59da018d494a818b5273918a3fc93188d9b161864f9cb17f01a6217e18fa617e08e9817474b94)) else (if page < 6 then (if page < 5 then 0x266c28d72648ae8f264818b02628bdaa25ed166625e9982325cdb0ef257a84ef25760ed62559cb09252512f72521152425147e3c25119b3a250b226924cd351f24b9bd62249110272465e3e82465b0642458d34b2437759724340c6b2417036e2413f9f724129cba240eb112240a994b2403685a23e8947a23a36f892322f40f2317b1e422abdcd722aad42022a80a60229472a32290263a22705f89220196b921f5f7de21c9b9ad21c8d5da21a03e1a216eccb62140384a210cc47420ff335420e92f62207358511ffed6bc1f87d92f1f6c059f1f485bdc1f33566f1f24517d1f164c591e9db2691e915c651e88900a1e6e9d0e1e6c7bb91e07b2b21e07305f else 0x2f04cbdc2ec094ef2ebc48862e89da552e7934a62e6872b12e5f30c62e50c81c2e40eef82e1736a62e05a8382e037a2e2dfa55742dd8ce082da39f042d96ec3e2d803d432d653e562d59ecc82d0c03372d0aac292d06adae2d0057262cf968782cb6a3eb2c95d6dc2c2d53172c2420312be2045a2b9e634f2b8371f42b821b202b6d10772b5875a42b3901b92b34d4252b2249a22b1b1e982ac81ae32ab3c6e32a7fd7cc2a7e0b712a7090992a4e63ee2a15c4de2a13d49029b5356629afe241299ab33f298a43c52921a482291d5a84290c92272901e7a5281480922812a00727d12ed427aab4a02788aa75270aee5926c5f7d426a5b423269b0bdd2680e1a2) else (if page < 7 then 0x37274eb4371ec41e36e3758f36d1508636b615a336a7674c3648044d36385af23619f49c36191ecc35f5907435793cea354ac2e23512bc433508001e3501cf9f34fba70e34d05dc034a5234b34527feb344adbfc3414867a3413f56033bf6c33335dacf23334566b332a69753313401b32b9aada329994413295578a326f809232659f3f31cdf52c31c1433e31af992431ae308f31a6269531a3b67d315d2f15313dbd8730ede0f130e5dfaf30dcc7f730c82cbb30c4514730c3d08630afb2ba30835264307d8629307c15eb30732f8d302f4de6301d27812ffb08a72fe5375d2fd9c0e92f9f5a252f97c7052f92d1f22f8765002f3af41a2f27d10a2f27ab85 else 0x3ea222a53e0ee1063e03414a3e0048533de0ca1d3dd163733dc884de3dbcc5e33db7032e3da5c66e3d9594dd3d82f0a23d5db0493d3bd2293d374b793d10d8f33ce5a91c3cde4b093cbdff1d3c862bc73c33cc1c3bfa7cf03b9e723c3b942f033b9111ca3b8becc53b711b1e3b62f3b63b6267d93b569aa63b50cef43b16caec3b0e5ec13b0a66bd3af1a2233aecb73c3ad49cf33a91120c3a2e52a53a28fac23a113ab439e7906d39d3210239c3ad063976085639677e433941cba73910fe5a390d11b438f5e19438c2e72138bfa3ce38bd420938bcbe3a38a577ac3899ad33384958b237f11ae7379932c33792eefa3792cdef377ef30d37457c663741412f))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x45dbb4eb45db741c45c69e6245954029455ef247455e9c6a4557e8a744e677b444db3f4e44b3854144ac6da744a1e3e844744b814461f53c443af6da4417b97b440bcc2f43d27c6e43c55510439146524356e4e4433cc4c4433a149f432f66e542f58e6d42dfded842c10b2442aab3974295b5c0428b3535425ace134234fc3d42039eb24201df1c41ef76be41cc0eb641c125dd41bb71e64195be074151c3644118a2e740acc3ba40a027d340822b7340668fad405679ea4051869c40195d9c40160a3d4005b7ea3ff748fa3fee151e3fd67ec23fab243e3f929c8e3f803cd73f67d21d3f36ebd23f3353883f17b1d23efe71c63eecfbde3ee234c93ea44c4a else 0x4d60434f4d5f10454d5b21e34d5a14384d5816a54d5408f74d3fc2934d296fe34d122cb44ced13284ce4894f4cd698644c744cb34c1f4d734c1ed7884c181daf4bfd034b4bd672454b9a7c5e4b7383174b6748bf4b4bfae74b47de094b429e864b153bbd4aca51c84a7cf85d4a43c1234a188e9d49f709fc49b0737b498c22ee498626dd496d262d4968739c492e2bba4916a5e948f498b14882ab1b4879207d4859ecbc4812166947f4ba9347f141c547f08e2647e417924790d6e747448e92473c402b47120c7d46f92cb946e4b0ff46e4a93046d22e5746be97744693c07a46689ad8465b6b364656ca754643df2046425bde45fc204845f8384f45e393e3) else (if page < 11 then 0x5682d4e3567b2eb756672eb55637619755ec69fb55da0a1055d0440d55cde015559183565590c9d5558aa2bf558a62a15582a04f55497613553eee475532c4e754e48608546dede0543a332d542879f853d97a11536bc3c0535fa4675347eb8553476c56531b481453026f9152e8e80f52978f60528d4f73526d2d41523b31685221bc9d521d0de751efd20e5197d8925195c7bc5179c346514cf7b651077d9e50ef5e6050dfa78d505eec4a5055a107505079bf502fce7e4feeda914fa124864f8da80b4f7200a34f5cf5284f5212944f1197cf4edd9eb34ed7d3014eb3e0c34ea9aafa4e9d7f464e6aa6c24e5c13004e22b5d04df2fd534dd2c6504dc0fb8a else 0x5d963bb65d74ccf05d4dfe865d173e215d0eb66a5cf28b6f5c93f1a15c7c0c085c4b84905c2102755c1ecfbf5bf5ae385bce2e6e5ba674035ba573555b8428da5b819da05b769e195b7667705b508c5d5b326edb5b2c4df15b26faf75af770af5af74cad5add194f5ad00c515acf15985ac9a1925a9fea445a9fa0b95a4230ec5a3246b95a2e221e5a23888d59fa0bd659ca747e5958752e5941515459286389590ead5f5901335f58cf338d58cbc3b8589625005861462d585c797c585066795809685557f817b257c800b357bb6c0a57b14d7d57a85480579c29ad5787737e5780c5635760e19b57542acb56f4d0b856f1886056d9b23956bb2aef568c3cba)) else (if page < 14 then (if page < 13 then 0x67da31246726f8f56706f71a66f5c3df66f2ff1c66e4629c66cbe17f666a9fee665c298b6630c45666308dad662f794965f0865565ef90db65da24d8656f4fea655c36bb6545c8436506f15864e41b6664d408f064ca1ad164aa72e9646f311664477e96640bebb86401b0fe63e91bb563da09b063d08eab63b064e4636e497e63526ac56311496962eb2f0c62d0617f6298ac706264b5b9622f82d1620cc8e56208918861ea417e61cbc0ee61b0b3b0618e9f6061845ee161661e1960fb1c7860b7a4fc60b3179c60949f23604cf71a5fff3a5b5fd485b15fd024c35f5d306b5f3956df5ec88bc95ec24cc05e059f6c5dee05295ddf1a515dd7bf855dc2857e else 0x7180919a7175b991715522697141ab5b7115f09b710f15e170f090c970ecf17570e3ff8270abeccc70a87eb07099542270962a9a7084a546707452d3706d662f705435c17037177f6fcf90e76fced7906efa7bb06edad3276e9a68af6e211a0e6df7e0206ded89046dcff3d46d9f77096d5741426cf121e76ceea62e6ce21ba06c8b81456c48c8506c3f5ba36c1200f96c0dc2016bb78b3d6b1066686b0d2e9b6afce1076aed57ad6acc86926acc80306a4a3d826a44846f6a26dd7169cb733869bd5f8669b8a82f6991e71b696e34f9693b7eed68e3d62d68b771f868a5230b689961bb6875633f685eb7d86815fe5e68123a48680de3a467ee5cf667e992f8) else (if page < 15 then 0x7a195bbc7a18e9767a18b0a479fb201279f67b1179e093c479d672e979c7977779a8e90879734d267956b2f87932ca9978f1f39b78dbf16c78b3c533788fc07d77f1033e77d5e69677c193f777b9010077b1f32c77915bec77885c3277307e5a76f4671e76cbaa18767e4a7c762a862276266ca475f05d0475bfbe4575a65952759ad931752a5c7a7511fd6f74f3306a74dff2fe74cb78fe74b2163974a8f4d4748b847c74853e9f747d47e574375a8473f9e25a73ed8d8873c6e75e73855d14736bec2a734d9b357344731d73440f4d731603d472dc1b2b72d8a4b672c61ec37296ab5c7219bee1721217f07206472471ce995f71cd976971bc0d0d718eb6fc else 0x813755e7812d03948105303a80d99e3c80ae738a80a0d173808e1ae5806394d180545187802d44318027c9e0800c0073800682228004ccea7fed9ef37fde245d7fc9274b7fa547707f7c22637f56b21e7f2c6fcf7f1ec4cc7ef2410f7ee7b70a7ed491f77ed333817e9c4b9f7e786e537e33e3a47e3269717e0829d17dd8a2be7d68447f7d4d26bb7d380cd17d181a4e7cfd49bc7ce6ccee7ce6765a7c877ddc7c844b9a7c0649c77bfc4d7f7bdb6adb7bb67cd47b99f5fc7b7c911e7b708e707b6447e77b5050d77b489f107b3b06597b07bbd17ae328817ad6cde27ad528a37a8fe4467a86a5547a77842c7a6a32607a3075b67a2481f27a1fa6547a1a9631)))) else (if page < 24 then (if page < 20 then (if page < 18 then (if page < 17 then 0x8bda55c48b9f76468b7458c28b1c7aea8b038cf08afe316e8af85f4b8a1d68478a0ff3bb8962cc158943044889403c3d8905e20588db698488a081d78896a545884ec1a8883d89d68827dc628816dc7e87c49cea877a381f87449023873cf0b18725cd7f871feb1e871036c886b05dc3869654ac8653986d85e9b39185af85db858646e2857d0012852ff377850ae54184ea000e84c18fc8849619ee846beb97844147b384267de184223178840f158c840b52c983e50cf683b77d6a83a63dbd837b6b0e83572aae833e6d4c833496748327f39e82d1ca91828ef25e82588c248258557b821a151e81f5654781c3c69481ad8d1f81ab446f815282b681418e42 else 0x95abed7295627dc795235277950a9fef94f6cc1b94e3753d94e115c0941e2d8d9403d22c93fcf7b993c7fe279393ae4e9365286a93413c1692fac89392cb18f192bcb1fa929963a1925f89c7925cf83592519a7292029ebe91b6ce3791b40758919f93b2917edb3d9177dc6a915b6e50913126b29102d5d190f98b7c90e12a5890894e8690665f50903e2e63902fbef790083cd0900504dd8fbaa6408f9c2b9a8f5fe9198f17fd4e8f0e18258f0a7a858ee837d78ea9b5408e98b8ec8e9805168e8c508e8e3b1abd8e2ce2c78e194c858deec1e78dc29de28db89f7d8d9e37ad8d8c702a8d800da78d78e35b8d12f81d8cff1bb58cdbae268c9c3a7a8c931c7c) else (if page < 19 then 0x9d1196e19cf57ba99cdb59099cb3ccb89c8200429c6534049c424af69c3bb3189baf741c9ba50b4b9b7d295b9b4dc28d9b4b5f1b9b3d5eed9b1a01579b140f039b0f2e7c9ace099a9ac261099aac0f9e9a9273aa9a8736c19a6da3849a5bfdc99a4f0feb9a48fc849a447ba39a04823099db7b4099c5fe83999560219938308c992de5989923971998ebb0a9988f2848987b2588986352a2986089329825c153981cde069819bac29814d82197f45e5d97e78c4597c3051197bf2c1e97a33e24979808d9978c1a4a977818a59775f51a9765185f975f262d9745994e972cc3f896bbdba39693dadd965de4fe965ddafe962e8af4961f5f2995f31d7695ac43f9 else 0xa550e2eba546bf5ea53dc812a5364b97a4cb76baa4b8116ca4987c7da47a55c6a476960ba4768976a467b237a460348ea45bf673a4286f2fa3e30907a3ce0d26a365dc0aa3566885a3364ca1a33080efa2c63358a293f512a27f4ea9a26e5580a24cd0afa24c56cfa231a5dda1dd6327a1964021a16caebba1540ac6a14d396ea12a5475a107235ea0f2a578a0deffaaa0be1d96a06748baa05ab1bca03571d1a01f825ba00f6ae2a00c44b29fc898b59fbe0f989f84200f9f6ad9579f11777c9f051c2c9ebc55d79ead3e549e98c51e9e91228a9e42d8a39e1f4ea79e0131539dfbf04b9de3718f9dbee3179daaabf79d6c16919d59f74b9d39f8af9d19d461)) else (if page < 22 then (if page < 21 then 0xac553c52ac3a6422ac3650d4ac2ab7e4ac081ab6ac03d241ac022995abf9f006abdd732aab97c9d6ab6f5cd7ab67cc4bab623742ab5fbec1ab218516aacf4869aa8c1647aa888f67aa66ade3aa5ae357aa186e38aa16426faa00753fa9f72d71a9ed0bc7a9e350ada9e1af61a9c74e70a98326f2a93e2b93a927ea85a923b5e7a91c538ba8b82fc5a8b415e1a8a39889a8107689a7d07295a7b28e3ba7a3e8aaa795ab80a77f26bea74c0ad2a73a4b5aa709083aa6fd1bfea6e559cda6dc86c5a6aa9d1fa6a5c516a690cbeaa6850694a6823e0da660bab2a6429ed2a60c610ca5e6c9faa5d501aca5aa7b5ca5a8dea9a5a735fda5a28ee9a58d4181a555f217 else 0xb54dcae1b4fbdc8ab4f806e9b4e47627b4a98e7ab4956a24b45380dcb4290b7db3a80749b39d433cb39b1ee9b38b73acb36e9403b3665cbeb33f7ce2b33b483ab326575bb30d5a0eb2eee043b2e09ba5b2a8c07db2980285b28e66b4b24a875db23670ffb22b46d0b2130c43b20c3942b1d9b059b1c11689b17b5246b16938b1b1259664b0f30cb1b0b667f0b08c56dab0655878af9c54caaf9c0051af625219af59c883af2d656baf2989f1af17a434aefd3d72aea4891bae9efefeae956877ae6a6097ae5e327eae3aad1cae39024eadf1d403adb107bfad58ee80ad40628aad3b77a3ad1fc6e4ad1ae368accd6585acbd3f67acba034fac891523ac752d0d) else (if page < 23 then 0xbd54e820bd3eba93bcb87927bc957c0abc897bedbc64d608bc5ee441bc383f09bc26a9c1bc13251dbbf73723bbf6de38bbf1a850bbdc28e2bbb49ca7bba8d45ebb7e7119bb70103ebb6eb201bb69b5f4bb5d7169bb269341bb167defbb120fb8bb0d8d92bafab202baf9fb1fbac4332bbab31648bab196bfba7c366dba7145a8ba67e384ba4b0eaeba471675ba2c6170b9e3e0cab9aeaea6b9a1408ab98c02f2b97fc10fb970d56bb93030c2b924c941b8d46160b878848ab8569c25b8165431b80b3c0db7e81d51b7d955c3b7a3241eb7426515b73bef26b7300ceab70d4f1db6d2e41bb6cdf2b6b6c72fc5b5a7ed8fb59c438bb58f0927b56fbf3eb556ced0 else 0xc65d6ba6c62e1565c5e9d194c5e75f0cc5c1d87ac5ada5aec5abe35bc596467ec583c79cc52d6acec50be55fc5018c29c4e40425c4b86f54c47d081cc467a496c4431840c3fce08cc3e1684bc3c7c908c39c745fc392da7fc38cd112c372f666c36cab65c346a067c3409d83c2e42e29c2c8bc89c2bea69fc2b7a8d6c2b411d8c29f3a26c2819d59c27d8f9cc25be738c2217496c206f766c1ee6212c1bef787c170abccc1454317c0fce31fc0e6b614c0a1140cc09f5da9c023e306c0217e85bfadf8ddbf9da839bf81bc3ebf46468ebf3cd7c3bf0e2a9bbec24353bec08c12bead5444be55766cbe4e8655be37b89cbe308944be0d7240bdc9e6d2bdb241eb))) else (if page < 28 then (if page < 26 then (if page < 25 then 0xce97c5f3ce943fabce6cbb82ce336b0ccded5b35cdddfb93cdba1e47cd98ddb5cd819426cd7b0e58cd75bb5ecd575f08cd192a3acd16b69dcc84ecf8cc56e53acc460c09cc235470cc211bb9cbde84bacb785486cb612f5dcb57713fcb46d7dfcb272c04caf69de8cad43c0fcab6edc7cab498e2ca93de81ca6e3274ca4e1418ca16c7b6c9f53742c9bee9dec9bdd72cc9ba3033c9899ca6c95caa72c9337399c8f51d19c8e31bf3c8df8307c8a4aca9c8570e4fc84e3873c8311f61c82fb243c82cb8b4c8073ce8c7f6c721c7d160b6c7ca5308c7a35e94c782f59dc76c3016c72b435ac6ea3db1c6c3998cc6b1fb29c67ed69ec67e31e0c675c2fec6608f68 else 0xd56363acd55ca577d51220c9d4f07e50d4dfe679d4d5c033d4c97b94d4c73a0cd4ab9230d49c96e4d498bdebd47b876ad45b2fddd453b458d43ad550d438ef2bd42c1212d4273c32d41511dfd3f4feb8d3c5c16bd3c25502d3c00440d39e3823d396d9e0d38c1fbfd37b6364d378a1c7d357d4b8d3088ba8d2f6013bd2d82fd3d2aa542cd284a609d2731308d26997b7d1ee25a3d1ddd304d1976835d177cfcfd166eb89d13faaaad11ff1f7d0c7c171d06ea5ddd02561d6d0146befd01379b2d000e50ecffbe279cfde557fcfba17a3cfa404a1cf9e3834cf9a9b3bcf6096eacf3fb4e6cf324609cf1a15eecf0f5e3ccef9797bcee94c80cee109e7ceb4ad4c) else (if page < 27 then 0xdb227d1bdb175718db0bb292db086f5ddab608b6dab233c2da95c8e8da85b747da816a0fda7ed32fda673e0fda5e2adeda2dae04da195c91d9e71357d9ddeb3fd9aadc2ed9a68fc5d98c35b8d9857cb7d977176bd96b3b7ad952a4d6d950f4d3d9467a64d93457e0d932a543d931ab90d92cbe4bd8d90505d8947a43d881272dd87e39b0d869c0e8d86904acd82e3c65d80903fdd7dab2bdd7da00d7d79f2f63d77289b5d748f079d71df0d0d70f77d7d6ee399cd6eaebd5d6c612f8d6b139b7d6ac1314d6963efdd675ef53d62f6babd61f4f12d60a2cc4d5eb2815d5e95e82d5e2a9a7d5d5818dd5bcfb0ed5b6ae02d59732b0d5868b8fd573cb6dd56a779f else 0xe1c09f84e1b3f7bfe1a3b6ade1a133f3e182f92ce1318f31e118eba4e110fc4ee10e8991e1055e5fe0e952c4e0ccea85e017a2b3e0118fcae00ce95de00bedb7dff40070dfe62116dfdb7e55dfcec6fddfad986edf8caa52df4f16f9df003285def08061decfd242debf7b5edebb8187de9f66c1de9f07adde5a8be5de4430ffddfc7305dde0ddacddd1ce0eddc632a5dd9905addd7be4afdd5bef02dd5941e1dd3dd58add3181afdd28a62fdd2406d7dcc03e0fdc8dd58adc65205cdc63b63ddc52d400dc4ebedfdc4baad4dc244938dc02bee6dbceedc2dbcc377fdbc189d1db8cb936db8a40c8db8405e9db5692dbdb48c24adb3a6141db292901db26c984)) else (if page < 30 then (if page < 29 then 0xeabba99aea96eaaeea868271ea0cfff8e9fb4650e9e01c53e9d2420ee9cf704de97c1c9fe974e00ce8fd2a94e8f1405ee88e58e8e88125f2e87ae12be85233f0e8442691e81bc207e813aa94e80e3f6ae78a8aa2e77a0aece779ea7be7791ce1e76eb519e7652e3ae7539dbfe737b0d2e72ade64e6c76b9ee69493fee655ec4ee62162fbe5c97278e5c20329e5b161c9e55013b0e52c8c36e5229618e51f4988e514dad1e4ef6008e4bf60c2e465026be460b602e434cc75e3ff6758e3f6e5f5e3d84ee1e3c07b88e3ac65e3e3881022e3476658e33b2f6de2c415d7e29ee47fe287febae283b251e2837a02e2601955e2591c87e25729b1e20ffbd4e1cee7b8 else 0xf3799ea5f338b76af30b79e1f2fc17e3f2c075d9f2990b2bf2611d4bf254b735f236bfaef231f492f21ee260f19f2fe9f195ab07f18f9951f18a1ad2f1850431f174f8f1f1581007f1480d73f1367771f1257b2bf115cab6f08c0fe7f07bc5fcf079bd68f075b802f0649ea2f0462c70f03ed090f0224e6aefbadf42ef9be722ef92a303ef8f68b9ef860d43ef1dc909eee9c482eeb729d2eea9c652ee902b70ee7bfb8dee51e87aee2d0f9beddd058eedd7e08ded911a78ed8d7424ed6d8615ed5bf4a4ed3da03feccbdce4eca5b324ec366526ec33bf80ec0829b9ebf9c816eba0437ceb801330eb60a03eeb609c8eeb226cbeeb155e32eafe1803eabbdacb) else (if page < 31 then 0xfd04df86fcbd8d07fcb698fafca1ee46fc48dac8fc45f954fb960945fb65ec5bfb2630f6fb21f069faf8f943faea00cafad2ef23facd1154fac677f0faa17fe1fa25493bf9e137c9f9d55d17f9d20444f9c4df19f9b56f08f8f7555ef88df132f858c007f849959ff843618af825cea8f8147404f7cb5206f7ad37fef772c8f3f7555a26f72a20e0f717bff7f6fe9d93f6efeb2ff6ddd084f6dd1858f6d4ba6af6b8c616f68b8d61f685f2acf64568b5f6171de7f5ed8addf5bd9ba1f5bc25e7f5b68e8df585bd36f575de9ff5674a5ef55f7d22f4dc2370f4a70378f4989494f46c3af7f4655a9cf4553068f41eb3adf3ef4784f3e726c3f39893d7f386850d else 0xfff4626afff18af7ffd1c2feffcece0effc8e4e1ff960127ff91d9caff7f1304ff5a29b0ff0b0ab7ff012703feb818ecfeb6f6dafeb5c273feb223ddfe71b54ffe622f53fe571042fe53533efe3d7c32fdf6accbfde85718fd84d0cffd66b82bfd5ab073fd485309))))) else 0
  | 6 => if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0x15646ec2154d192a148579ca147db1b01414b66313e8816c13e549e113d4616a1387dabd12a7b511125c215c11c0552511097f560fa7c4780f03c24f0e7b03440e4266000e0366a90dd9b2660db7c1bb0dac0e360d58d6ba0d48d9da0d1992e00cdf08a10c49a77e0be6ad4c0b5767a10b4740e30aaa72710a055ac8099d4df20905303708b8fb6a0835c8bd07ef6f5f07dd9f3c079d60ee073e635406fde88d069285f106698b9105dc36c605602310054b497d0468f12104504494040aa0f303eb5d6403e638ca03a1aa290380dd1a03724785036dbf7c0300d75102eb17bf02e8754b02d7a00202a874650299f33702440ee700fedace009ba4170001be8b else 0x2e05a8382dba1fef2c3e32992b8ee5642b5875a42b34d4252ac81ae32a53d2a42a4e63ee2a3d71272a15c4de29844ba2291d5a84286a06472860023927742eff273bc77826c571ea26a5b423264c07b12649de0c25ec024c259ee7012588858425846ede24bdcc8e2484af5322995d8a22558bb32250ac7d224c2e362241082a21f5f7de21a03e1a218f4bd4216883a220de0abe20bafb641f21c9521f164c591ea2a7a91e915c651d8739031d78d4ab1d6f241d1cde98c11cc5a3f81cb838941c8425f31bd4e5ce1b591bea1b10e02a1b0a8fc31aefa4641a50534b18983123183cc66017f01a6217c0c13917140bae16c902a616aa0bd8162630ea15d91bfb) else (if page < 3 then 0x44744b814461f53c4452ff494408dd4943ff81f042c4f42342b17c66425c3121425ace13418d2350411f3ce8410272fa40eaca2b40a027d340737f1f406350523fce96503fb01f9f3fab243e3f17b1d23ea222a53e5960ef3df50b6a3de4be3f3dc884de3d2f8df13cdd73993c7c5d3e3c35de883b99d6f13b569aa63af1a2233aecb73c3aca6f773ac149093a3207a839be34cf3910fe5a384eea69384958b237be22953792eefa36f858d636d2fd13369bbb9736855a1a367d0b3036699373362b469136274af53619f49c35ce85d8351b552534cc642334a5234b339f3ab2336040f03350a78732ae9fd23296654531c81f8d31b4a7d030ede25030e5dfaf else (if page < 4 then 0x5f57e0cd5f12e2a05ed10a585ec24cc05e8452985db4eb1e5d1c834f5cf274975ce8795e5cd217e15c59d1a05baec2325b8b57725b8428da5b5090375b508c5d5b26faf75a8128bd59e8c0ee590e73a859010b2158c4a379583d88f4581ef25356f18860568c3cba55e1ffd75590c9d55582a04f5580e0ec554e60fa54444f4453ef881e532020a452b4ea0252978f605287b8d5524d1e8b51f2c20f505079bf4f939c314f66d93f4ed7d3014dd734b04d32b31e4ca5a9224b79f6ea4b784a124b710cb44b1737834afa262c4aec16724ad16d1a4ab1ed9c4a5d75cf4a38a1734a161d844882ab1b4879207d4859ecbc46e4b0ff466dc6d845ba962545930d7e else 0x7d4d26bb7ccb20f47c9f32a47c88d1277b0ce3d17ad6cde27a6a32607859551677c193f777915bec767660517601275975eaa36075bfbe4575967d4e753e2a8b752a5c7a7527c90e74b2163973c65f47737f70e5736089c1732a83eb7328828f72c61ec37229ff0271bc0d0d714aa6e96fe4aa266f1b1c2f6eab9e1e6dbbe8c16cf44e376c800ead6c1200f96bf6f0606a88266069be559c69b93e66693a5d8a6911b1ea68fe3a2d68e3d62d67e992f866f5c3df66e29af8668f7271662f7949656f4fea650452c364f4e22264ca1ad164aa72e96498be20648ec91e64477e9663d08eab63bf61a463526ac563271e476326f9d5622daf5560fb1c785fd485b1))) else (if page < 8 then (if page < 6 then 0x97a9e5929745994e9669ec8c95f31d7695283d5e94980f65941e2ba89365286a93362a2b9206a41791f32c5a915b6e5090665f508fb622878f871b518f6d78958ea9b5408e40548d8deec1e78d12f81d8c92fe928bfc2d918be8b5d48bd522128bcf7c658b9494b88af85f4b88e0546b88c86b3088b4f373888ce60787de12ef87d642b5869654ac85e37c1285dd6b8b85cea27f85c70a0e85af85db8569ed72849d3710849619ee842b68c884267de183ea065d83258fa283215712824ac4ff822ef22881fb7ff9816763178153eb5a8105303a80ccb59f808c3820800c00737fd2f5057fbc93887fa872b47ee7b70a7ed333817e70a3ff7e3269717e2d4d82 else (if page < 7 then 0xb22b46d0b1f5cf7fb1ccf2dfb1bf40f3b147870fb05d1465afb93b8aaf693feeaf625219af3dd497adc1e741ad0a5550ace60aabacba034facad6b99aba828c2aaf07226aa888f67aa8714faaa7725fdaa6bbd36a98326f2a9186733a9067417a7dccc7ea6ba7600a5f5307ba4e5fba0a467b237a460c19ca39d946aa3715297a3364ca1a2be3956a293f512a21ff886a2058a5da1eed1dca1b2393fa1566a0da0f2a578a05ab1bc9f99a55b9f6b90209daaabf79d59f74b9d4fa8f69d077ef59ccc50fb9c7463129c73590c9c4de5209c424af69ba50b4b9b61ef119aac0f9e9a51312699bac7aa997741b2994475e19907b3e898dae785981765589814d821 else 0xcb3bd903caf69de8ca93de81c8dfac22c82cb8b4c8217dafc7f6c721c716c226c686ed60c67ed69ec5abe9c1c543c9d6c542d74dc4d16719c40cdbc3c3ae708dc3190ec2c2819d59c26c33dfc170abccc0661484bf3860c7bf27a54cbe7e19d1be64231fbe4ae1a8be0729e6bcb87927bca4fd58bc87a1e0bc61bd59bc049e66bb74fb25bb41e977bb167defbab196bfba6ae96fba67e384ba471675ba17e081b92dfaf8b8fbe0e3b8d46160b87c0d7eb82a2caab8165431b7523a80b7245965b70d4f1db6d2e41bb69f09cdb5ba365cb5a7ed8fb556ced0b4ff1a6fb4e3f598b4a3964db446f540b4322619b41e2b91b39b1ee9b3025ef3b2980285b27196f8)) else (if page < 9 then 0xe2f1bb1fe2cfc808e289778be25385f8e21220f3e153dab2e14e9ec6e0da3a1bdede5e92deaf2889de5f76ccde1adc65dd9905addd556516dc9eef0fdc65205cdc4d3570db8405e9db6ebfefdb2bb46bdaa3d34ada95c8e8da21a2b5d9a025f5d9857cb7d950f4d3d94f1cbad94b10a2d91e5245d8a4b203d812f7f4d783c1f6d77d5679d6b9d44cd60a2cc4d5733cc6d570efa2d4dfe679d4df3593d4a3d54cd453b458d40b6d7dd3caac52d3088ba8d2c09a9cd1c7f727d1737ce1d16a0df4d036144fd0229c92d0054c7dcf60f7b5ceea22a8cee109e7ce6cbb82ce336b0cce0fe789cd575f08ccd66952cc84ecf8cc6fcb1acc460c09cb54214acb5060da else (if page < 10 then 0xfeb6f6dafeb223ddfde85718fdd07fbdfd84d0cffd510461fca998dafc399861fb4cd2e8fb476c4cfb1bc5dbfa25493bf9fa1163f905d600f855e9e2f7f5c484f72c16e4f6dd1858f6c1df33f6ab7db6f678e631f5cadc1df5674a5ef4bdd1fcf256647ff24b735cf1ad162ff1a4cde7f05cfc2eef972ac6ef8f68b9ef17b0fbef11e549eed3dce8ed9bc3a5ec0e00efeb90879deb48a993eae42df1ea30fd3eea1ef145e9d2420ee9cf704de9236f6de91fe25ee87ae12be875e909e8442691e81c9779e7b6a8e2e78a8aa2e759154ce6b2d24be62f424ee6038a69e5f2a8ece57c119be5344b96e4aad2efe469ed52e453e7ade3c0fd66e3ac65e3e35fdb9c else 0xff960127ff6b100cff088378fefc5f08)))) else 0
  | 7 => if page < 1 then 0xf2fc17e3e88e58e8e87ae12bdc65205cdc4ebedfca4e1418bb167defba471675b9aeaea6b2130c43a0e52aa09e1f4ea79cf57ba99c424af69a8736c19814d82194e115c09365286a8d800da782169a357ee7b70a7d4d26bb752a5c7a6b0d2e9b662f794963d08eab626e621d58cbc3b84edd9eb34295b5c03ea44c4a3de0ca1d3af1a22339e7906d3536dd5a2571d7791bca8c1e18f3e8b00f03c24f017826f7 else 0
  | 8 => if page < 1 then 0xf4a70378 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x4600410036006600300060002100400010002000010050000000560026 else 0
  | 3 => if page < 2 then (if page < 1 then 0x1d00076014a024a003001770186009001c600d0011601910124024001100040028001b100a6029601080252010001f60166028400260020005002350071004600040270006000c602880226000600000120024801a8023200b000f00190029a02060250003100e600e00131026001700148021600d8016a014602a0009601b0 else 0x230008001a002a400a000f60010015000210130019801d601e000c100b80036) else 0
  | 4 => if page < 12 then (if page < 6 then (if page < 3 then (if page < 1 then 0x1360068216d015b4072913b8000606300c100bd0091008c104200178022614b004640d130d8206710c600cfa09c011900350059003600cc0127003f60ec006f10402123907c703f006a01302146004a016000f700796038604520030078004b90f2705400a6800a8065000f01810174013d00a4016200c820536063804d300f1 else (if page < 2 then 0x88603a80044135b145013800af6002200d0026217f006c0092010c20aa6049a00c00a600eb616c00e600e260bc40cb113e81078061616540d92103013730b4014d00300078a10f8168213ca0a460f5600a00b281670047506b808720d58172115701578040014aa00c204d9019004500090170616c10428139700b40e3801f4 else 0xd500ee003400010027216f006e015a2154003780ca8150a0370002816b116940cb00be00a70093012d9019203c109b1158001b0132806900af001990c800390009600001264090005b004d216900e000ab0185401f806c61170093611e115d617c00a5000120646005005e6015604361440127117b604321804125410481198)) else (if page < 4 then 0x173418441208029813f60d0b01c8142915c2028001271524004017b20ca107b701f615b2044215e017500dd2128704f00286064006a616e800340b87129007470fd015200c0007f01592183207e00e30177805621602001801360cf01241163202d000ca0fd9182a145406e60a8014420ed6188003460d9812290d2212f20ce2 else (if page < 5 then 0x10800a100d42075714e80857011011b80b5610400fd3187a16a807f70e5005800020056007b6046806d810c00e210076076015960a31051a11d9166006e40070143402b614020cc314580f120917094618b00082044006d00b00077612e800d8093413401774066810d011c00e020bb00c700c3105f015e411660af40e710ad6 else 0xf4103a0110208e00ef115380066050001200bc003d60d600b2002b003d009f808470d5209a0038015fa147408900c580988071010010c520130113314350588181a0a5900580c88163012f0101014b203b0006000f5003603100074051618a003a905d00de916d208d604800c610fc60f1008b00180035609120521027006b0))) else (if page < 9 then (if page < 7 then 0xf8002a10d90138713bb09e6169614210ac002660bf8117209780996141615821840105118a405970916071317a815f012db0df007e1005205a010000ef002e015c40c4002910ba6138616e200880d74039606e10d6408000e40164805c1109602c707000f0400460b601260082116c20c9015c010d60f30095003910ff015b6 else (if page < 8 then 0xdd8069806700610152613460ad016a20101181802c6000414110080176214c80e310cf214a8062013e00cf807820f0614f610e913180a2017f202400f900504035101d0064104c205c0066914040b7005e700da15600a000ae0143218b20b10168113e10cd8107012c217d80fe007a014980510113102f0116710d106000a86 else 0x8631330179017c415d00260155016e40c710f890b0814140474049210a008a1144411b014050a1108170fc011c2121000aa0430162406240210168001a716e0057004b305f6044112f607b00ea01180090818300469083017e21860112b13a611b9033815940c2815e6161015f81112087a0b90047605d70c1209f010b01286)) else (if page < 10 then 0xb60f360412078815a008690fc403c003201060023600a2042216b708a00d1110f901c20172043a0f2606510dd0025811290361012511b4172018021430178401c107d004340fa112b006880554149001461642060605b115d4108208f817a00770073017e409b0096013000870148015320b44018803c6055007230c440121 else (if page < 11 then 0xa9016e613f4016009d809320c5003e1067613d502460878027415b00b3a07e910260f40166213790d661146041003b10b380200149a126200c8084603e612ab0f60022000c407201590037909a103e00f1116a0045117e00e32043811f804900e180e8017101150038100641209176004e00dba071910e811600d0a08d00d23 else 0x182805d60e910dca0970056801c0164014701650090218900da8066000d2140016380e20081011a00ca0023004960a3015300fb80f1800f707500c4601e6074012810b2401980ff813f1151002a0165604b0049400e0013416f400940d3813c00da00fe7)))) else 0
  | 5 => if page < 32 then (if page < 16 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x133239421c940dd00ee024c0256401a432f217aa1270090918441790318b17123724251032e829720f500e142cb500482050226223b5236a186417681e32215021e419100860014136a623881deb37620a510f6028900b760bf11fb02fe02430110b36460eb0143707160fb800e006c033101530025005d01df81cc01cc81d10 else 0x1ed22c80339908800a202b302c0401c6017107b02c71214019662e801f462cb01ce638c011f034e4009038f032f3145403b01fb725212e002ae00bb632802f800d402ad631c0136012d6011a1b1007d019c01e12385631d024b005da29f61a4037c4160a02a6113204893721383221f624202f40354027370882360806900e10) else (if page < 3 then 0x2ae1125031101ee0005026a00a552c002e1b32c01920139808f103a124631c7218f02c9421093802366022680582227715da13842132082028b902c1315024b920370f1026511f28076008d02249097412600221232627801692240617d434900d540d9037b830a738a637e02b802f3806402a463320032420f028f121920df1 else 0x2865163109f012ea2bf11e8025b230e622da26181eb213792d6811112e12183816512f04164405a434c628112eb115c21ad12b1209b726e02dc6014017b90e6422761e2b13f20b8034a62e640e7a00c008a70340239013001b810aa1197912261de011d119600232002805202f2128300a800fb028e0293113a4365210f938e0)) else (if page < 6 then (if page < 5 then 0x170421022fa600a831722d3032d116b904f821b003f3235119810548167b28c1312838d41b500032008036d11c3030e10b453112352005601a112856200907e30d661eba06f2284905e0216014842d6025e104661ae73700113a30812c5925c037f2263933e2396236b60ce80b6038921fe435b61550311400642af008f317bb else 0x23380608217806e410e01892215b213117a20872256019911a8001f1232430300af00ce033b61540019620900c2019a902600db02eb011722cf12a9006f6275907101fd02370354111d41de9351102821ee8384232f11fc0202102f00b001fe1048812020cb1370435840f9604361e09245017f0381218c2374022581bf02d35) else (if page < 7 then 0x1980114238722c731ab12b502a400f0622a024d8279932f618f22c900fe0208715c00c861ff033760bc00d7636d0096011282f8718602a341fa11022309218a21d0007661e52223928f8390010470b8401c03344301022ea13b00fc01150165237512860310002010460123035a810a204c62e17257003f001e428e4181020a0 else 0x7e904070b07398000201b37012800622d271e30036038b21290350006362b612b903496172a2ab02f200e5032f0170036d421e210c001022db012421e29078112c2297b1421028031642ef8368831f40e910ac910b03930332114d605e408f01ea035c0201125c10158121227f3373800ca343a07380a3112d311f435f61d60))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x920ad024e12df108c0328628162a3a02722870284028d62e843510227000e220001f120288230004f9387428d5234027b829e209d011a10ae0297008670b3204c2340218b010821f5637c60f612e2105b421d008f20c900a381220091707d312f004901c8432211500011413630149114a0a4337a0012216011cd637f6001a else 0x13a71d311293089725a61890360238c416ea25110c60193402b01f702d10369b23d628a7043033022e90194028103650241006211a5110593964221936300cc01c210ad41a912a3234662416019022482230176a110a00a420f923300a700290128304143501010835a22fa10fb206200b7027f413d035602b211b600a4829b4) else (if page < 11 then 0x1611388a18c8250036991b5630402b6030f02008024004711280066024700fb412221a700a210a06181423f1104012f42b020a8937ba396022c606b0276800b004802ff102d70f7030c039242f48050131242ea817822f6b12772d501944112014f0155833d609802c61013009890d821b000dc02b982bc01182099705663564 else 0x2cd72f7429e030b006e02cf0381609201bd60ca106a11010285404261b413718314117a810a800d816840e060a41205327a10ce115fa13920de82c791af6124028f226f914d2377026d01152109222f80ba022892fd2143400da040600882d202d2633b40eb91f2201a012102bd000e81ec00e70331114460246231034a02c06)) else (if page < 14 then (if page < 13 then 0x10411c97360100300fe227901458197800a617a0116000120fa20f2a260023b7384419d12cf51f9030900151124820cb1276195105761c092c10143122911ac007eb1e1812c02c3930f2079102e103c004131f9118a8312318001f7124a21ff4108021642c9623a113ba01802ba028621ba70e2420101f40344038402e9127c4 else 0xf6218062ba817d237e218e21a4131e938b0162607b128141408310918821a3034500c702f10320207e02e410f802be036e8342205000d8028d00be02aa83196011016a41aa0203030d7060316d40ac130912b2010f210e42cb738701f8709830b901e9021491675128800f029c02b542fc40e3633f023e60338372603e63028) else (if page < 15 then 0x162a19e0233933d42ed901f013e029a90f8229e81400329024b43486336b1c60276934d035310b6715c81281052128e104e718a00549188431291fa6015b07a925a424800f200f26222034b0240102002a100b42204104b001d406f00cf702202ca903500c3626b01aa113f01ca9270004e128d729d0313832a001a622992431 else 0x5e124d924262aaa036236001be03130324006093598016b04b62dc403c1019814e716b0335006a0055034e622982481330030220db215aa2daa2550373206c135760ae62f30194104a02f18306028d42ac02c40019217ea2ab226d105c62ce1391816a03416051a07c0180a098b19612e392be102301fa004d032840fd00b30)))) else (if page < 24 then (if page < 20 then (if page < 18 then (if page < 17 then 0x2b0026f803901f602d370153370607d907110ca002b10b560739061006b70b47178038300a9111702d322d7029400a5225d0220038220e862238107023d425541d92120032601c8605ca25f014441e960c4603300e440cb0304102c02dd429910380185018f80b212886244604701ee211782ea0238016f021e813a00d200148 else 0x10f0040405902d4427e407b614300348116423721c51077000181d20264033a037902cc617a409a0321b26792942074812a917281dd03530109018300f121a6037f4086634b20c0034a41bf1383400701880269038882e7823e022c009401350102004461c490cf60a42070a38f403d125310ac03380014406f432361db01f30) else (if page < 19 then 0x10d0143515b01e5825f12e580ae11b6711d01fd10f3232511a810fe435861c7026a51084175a355133e00ac22a5126502e20078038d0079024f8378814bb333912e01da61522364005d636802d8b1c901d702a602490064102703954172011401c0007501e381e673850210b22690a6123cb09370556312026c01b7101201b20 else 0x1d800ab0010010881e7010e129642a440f521ea21282288014a03944158022612348287101941695037220400fc8182215142ea90b9136c2009806912e7033f236c0103037121ea4212005311fe6386018a42d4136441cf628c8014a2b4305f403e006511f242e3029102a2100102e4005d818c42d4213a636d60ba638b42501)) else (if page < 22 then (if page < 21 then 0x23022a000de90b66163b118802a401430c800e402829314003040a903061195026e8355003d02669139005f11df017b219f700740c211b7022812d112d6228b01bb6106105d425d124f004d6385404111dc134783071010425931820090025300210029805402f501a2119c23610240034140ed23464162000a019a011ca2d36 else 0x5c215d80adb0df00b7724a435f114c111c610f122900bd008e136e213b837a12ee42a8a072125903800127417b1348414e22f060ae417b02fe1044014aa373004560daa30d030f82eb810e83566015924a803b105b018b431131ad00c1021eb210117151d4101c404022f9618b20dc106d036f0238927201ab022502ee001b2) else (if page < 23 then 0x19560de034f0340009032ff02e2420c010762046010a3050222111ea2ac22059044106701d5108b72d0037311426394028842a50130225b028a00a3018943820031015e00132262904221425280132e027e019d0269621f4015201792ce0301833810ef02e1038e41eb8258005102e8612612f6903a01fe0113024402ed32566 else 0x1304175021a633741a00381029c8359211c20671167217c008172e1426011258258202e0080710a0245707400600313939820af6298b10282fd832a8192200600cc700f61a903291394835d038241a710a4019b02de214601872362013312f970e8423122368144a20d937f018162710042332e103862cc02a701c202c201c96))) else (if page < 28 then (if page < 26 then (if page < 25 then 0x20f217922020119035f00040159005a22c170c560961014234c408501fc71ef1224009e632d027d80ef227f009f237921ac12f001c1607a80ff023b100a20014041015703070336936b42cf71cc22b671a203000097307a024c700760f30183a22522bb422c40cd0241723f012c80fa030c134d235a034420ad323501f761739 else 0x211a1058217034e02349247403202fb004502d742f0719001903371015d0005201b005260e2a3390073004a62d9632f413211000149a01d603961ff617402fc030e02619365818b6027431db21f50530293011b12d40397617d01df229320e903460051806373920182827472cc4199036a428d226e935740f140fa4015004e0) else (if page < 27 then 0x218023b0292039120370156107560c6804760e5220f4184019f633a803000d5601b8134804052bf01479317013f1144033c42d45295904d12001055121c1330100421a011f1011a013e10cf022d8191423c914ab041215012f9036e13122149006b60cc60be107540dd100d035b4335124d013b219c811cb18f40856277735f4 else 0x275116c217380776106027060da001e008460f582bc20602385207723901083038901f140e601bc00ba3187011e61a61221812f2206735b0019a0e04068031c432b0252005a01f00242404210d01193016b13950032233052b10378a002235e020b0142018d3367025402591266823a019a81cb101e60b952dc92cd0065005f0)) else (if page < 30 then (if page < 29 then 0x12d016323814254827460cd112511552161a27b40e321904142734200ac81f4400540116176204912556131b0b190d301c78021124e82fb1061536e0220819b6277427d130311340058828e225e02ef0107224f929b9070016600ec8072031511a1827b012d416d00b0605f51a50141106112198070813ca0ed12d3402d6347a else 0x4a116fa2a92142420e42f76221030013438005622b0297937d021f13200103137d8228010d80d3127f626941541333b32701c800b361b9018d02bb617f20d1032b60170283118e81ed034b804202e9830b9330429022b4901462469317829a02af105c019e12b7114102a381f811f502a88087022fa074922e81c102b7911b0) else (if page < 31 then 0x2ad41fe7358000820b501b801110397433c6146a3209207000f4377229d40160016a1f02192817600f401e2035900382061426892e60376038a012b403f2023428c0316007f701d018e003920ad92e5225e61a101f2003f1357028e527b118c032c104c00236226003f6187400003111122a0d113934177030510ea602a02ec0 else 0x5e50a1009500d00334600d226a71e491c401b0631ab31b10ba4372030201d90097009c020b325711a36118030122c72285017a6))))) else 0
  | 6 => if page < 11 then (if page < 5 then (if page < 2 then (if page < 1 then 0xb70069604f105500c48052805650c6701b40ad702c00630064103d00fb00d4103710d200e74007603a10954044109330ed00594048010980b40010007760532090600d6059207c00ef009450b9110240650044206f80c420f75105402200aa001600cf0004001d0092603410740095701e50d1806a00e0604a4005002280d60 else 0x10200b1004b8050107000ef10f3102120ae008600a7103911034060005210e500ee005000c2804da07690ba401a001e00e1700a6040408800fe10b520e9010920e21103008b90e040f560e160b8007e405200da00b220b850bf404960e0005e60f940b67034009d20d220d0004100fe004c409e40d31061001800e700c100111) else (if page < 3 then 0xed40f300e15062104b0069705880c90013705300b500ec80904011209240b950d130e1102f40312075904400d4209f203180b0003e80a9001e409660542099100b006e20b1209740cd401100b90041a0db2015104f0053801d2056009470c180f500b660ce00b450cd005b60a1004e00ca002680fa60df4022102080d401060 else (if page < 4 then 0xbd001210ee40a50098606f209850de002720960083006a704c010880922000800f1057208e009b2051a1046026005d000860e760a000a3806700e1409510d1907b0058009310ea609340b2000e0065705160b5709c9043205640d840fa007210bb40f80076b0cb40524023704c10060069003f007980c0002d804a504610c30 else 0xa8606d801f2089004d809cb085003700ff10671105606a60f60036b073202000f0008f00821047009640cd301d80b6408700bf008a906200e3109b0020305340eb60db00ad0064004a009420b2606d009760d2802b0107801700258097100120f7702360902036105480e8004d0065607110330075b04f4049101a40a1403c0))) else (if page < 8 then (if page < 6 then 0xde60c490984031005610f6805890018092004d104500ff001360bd40f1004860ea00c5000f20344050a09870d4808f402100147103608c108e20ab0094001ca0d090c080f6200200f84043010140d1108e50be401e100c008c004c60209012008f20b8708b00ca407c601610512038b0282098005830f01107201c610100b61 else (if page < 7 then 0xf96049402040a9110a406c80680002203690b60051801f103510c200c7001d404e70fc0066702a010440c8107300eb00d100b240d320b970672010103900dc003f408d20840109001f405620b020910108207e60f540bb009e60d7607f00fa4059004900de70b760a8107010e960fc10af7090002780f1103b0048a01900fd0 else 0xd620f900f710d430c2202710ea40ec002500bc30b4206b104e6035001e20d9b0df002b601c000f003320b96052a066602700cc005710f200554081902880b3209700de5099601500d380030032210a002300cd10362051009f010680b6503b10ed606310de1052607e0102607420d120ab602410ba0046208a0057406540f40)) else (if page < 9 then 0x6e80ac00ec20eb4053a0508028009a204e203e0098101f007c40d490028029206c100960cb0072008d005a60af001460e400be00b7409a006e10536105006c0045a02400000095604a208090a2006d21080095509300a160cc4068110400ee6091207b80dd206e004b103600a7005f0045603420e010ae70de4079007800251 else (if page < 10 then 0xd74107005c00df610620d990b410b94021405840595038a10a60b3004000e9405750bc90262095005910a400c4005820dc206f007820b1402e007d003a0057009d00dd0033804600d300d860b550d50021506110da2030008e707a80cb20184042006b0101601b0052201f50e100f8602110e69051404310b81020207740451 else 0x2100004b20a60)))) else 0
  | 7 => if page < 1 then 0x3400370058000200300014003600220035006400650010004500610052009000400018005000670081006600800051001200410028004400200060001a000000310059001600530046000800700047 else 0
  | 8 => if page < 1 then 0x0 else 0
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
  let slot := field targets k 16 ix
  (slot / 16,slot % 16)

def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s34]
  | 2 => [s12]
  | 3 => [s12, s34]
  | 4 => [s01]
  | 5 => [s01, s34]
  | 6 => [s01, s02]
  | 7 => [s01, s02, s34]
  | 8 => [s02, s01]
  | 9 => [s02, s01, s34]
  | 10 => [s02]
  | 11 => [s02, s34]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s34_ok, s12_ok, s01_ok, s02_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 8 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 7 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 7 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x16 : span (checked 3) 16 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x32 : span (checked 3) 11 32 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 43 0 = true :=
  (@span_join (checked 3) 16 0 27 chunk3x0 (@span_join (checked 3) 16 16 11 chunk3x16 chunk3x32))

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
theorem chunk4x48 : span (checked 4) 16 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x64 : span (checked 4) 16 64 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x80 : span (checked 4) 16 80 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x96 : span (checked 4) 16 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x112 : span (checked 4) 16 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x128 : span (checked 4) 16 128 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x144 : span (checked 4) 16 144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x160 : span (checked 4) 16 160 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x176 : span (checked 4) 16 176 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x192 : span (checked 4) 16 192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x208 : span (checked 4) 16 208 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x224 : span (checked 4) 16 224 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x240 : span (checked 4) 16 240 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x256 : span (checked 4) 16 256 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x272 : span (checked 4) 16 272 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x288 : span (checked 4) 16 288 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x304 : span (checked 4) 16 304 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x320 : span (checked 4) 16 320 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x336 : span (checked 4) 16 336 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x352 : span (checked 4) 16 352 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x368 : span (checked 4) 16 368 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x384 : span (checked 4) 12 384 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 396 0 = true :=
  (@span_join (checked 4) 192 0 204 (@span_join (checked 4) 96 0 96 (@span_join (checked 4) 48 0 48 (@span_join (checked 4) 16 0 32 chunk4x0 (@span_join (checked 4) 16 16 16 chunk4x16 chunk4x32)) (@span_join (checked 4) 16 48 32 chunk4x48 (@span_join (checked 4) 16 64 16 chunk4x64 chunk4x80))) (@span_join (checked 4) 48 96 48 (@span_join (checked 4) 16 96 32 chunk4x96 (@span_join (checked 4) 16 112 16 chunk4x112 chunk4x128)) (@span_join (checked 4) 16 144 32 chunk4x144 (@span_join (checked 4) 16 160 16 chunk4x160 chunk4x176)))) (@span_join (checked 4) 96 192 108 (@span_join (checked 4) 48 192 48 (@span_join (checked 4) 16 192 32 chunk4x192 (@span_join (checked 4) 16 208 16 chunk4x208 chunk4x224)) (@span_join (checked 4) 16 240 32 chunk4x240 (@span_join (checked 4) 16 256 16 chunk4x256 chunk4x272))) (@span_join (checked 4) 48 288 60 (@span_join (checked 4) 16 288 32 chunk4x288 (@span_join (checked 4) 16 304 16 chunk4x304 chunk4x320)) (@span_join (checked 4) 32 336 28 (@span_join (checked 4) 16 336 16 chunk4x336 chunk4x352) (@span_join (checked 4) 16 368 12 chunk4x368 chunk4x384)))))

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
theorem chunk5x704 : span (checked 5) 16 704 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x720 : span (checked 5) 16 720 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x736 : span (checked 5) 16 736 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x752 : span (checked 5) 16 752 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x768 : span (checked 5) 16 768 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x784 : span (checked 5) 16 784 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x800 : span (checked 5) 16 800 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x816 : span (checked 5) 16 816 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x832 : span (checked 5) 16 832 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x848 : span (checked 5) 16 848 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x864 : span (checked 5) 16 864 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x880 : span (checked 5) 16 880 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x896 : span (checked 5) 16 896 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x912 : span (checked 5) 9 912 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 921 0 = true :=
  (@span_join (checked 5) 464 0 457 (@span_join (checked 5) 224 0 240 (@span_join (checked 5) 112 0 112 (@span_join (checked 5) 48 0 64 (@span_join (checked 5) 16 0 32 chunk5x0 (@span_join (checked 5) 16 16 16 chunk5x16 chunk5x32)) (@span_join (checked 5) 32 48 32 (@span_join (checked 5) 16 48 16 chunk5x48 chunk5x64) (@span_join (checked 5) 16 80 16 chunk5x80 chunk5x96))) (@span_join (checked 5) 48 112 64 (@span_join (checked 5) 16 112 32 chunk5x112 (@span_join (checked 5) 16 128 16 chunk5x128 chunk5x144)) (@span_join (checked 5) 32 160 32 (@span_join (checked 5) 16 160 16 chunk5x160 chunk5x176) (@span_join (checked 5) 16 192 16 chunk5x192 chunk5x208)))) (@span_join (checked 5) 112 224 128 (@span_join (checked 5) 48 224 64 (@span_join (checked 5) 16 224 32 chunk5x224 (@span_join (checked 5) 16 240 16 chunk5x240 chunk5x256)) (@span_join (checked 5) 32 272 32 (@span_join (checked 5) 16 272 16 chunk5x272 chunk5x288) (@span_join (checked 5) 16 304 16 chunk5x304 chunk5x320))) (@span_join (checked 5) 64 336 64 (@span_join (checked 5) 32 336 32 (@span_join (checked 5) 16 336 16 chunk5x336 chunk5x352) (@span_join (checked 5) 16 368 16 chunk5x368 chunk5x384)) (@span_join (checked 5) 32 400 32 (@span_join (checked 5) 16 400 16 chunk5x400 chunk5x416) (@span_join (checked 5) 16 432 16 chunk5x432 chunk5x448))))) (@span_join (checked 5) 224 464 233 (@span_join (checked 5) 112 464 112 (@span_join (checked 5) 48 464 64 (@span_join (checked 5) 16 464 32 chunk5x464 (@span_join (checked 5) 16 480 16 chunk5x480 chunk5x496)) (@span_join (checked 5) 32 512 32 (@span_join (checked 5) 16 512 16 chunk5x512 chunk5x528) (@span_join (checked 5) 16 544 16 chunk5x544 chunk5x560))) (@span_join (checked 5) 48 576 64 (@span_join (checked 5) 16 576 32 chunk5x576 (@span_join (checked 5) 16 592 16 chunk5x592 chunk5x608)) (@span_join (checked 5) 32 624 32 (@span_join (checked 5) 16 624 16 chunk5x624 chunk5x640) (@span_join (checked 5) 16 656 16 chunk5x656 chunk5x672)))) (@span_join (checked 5) 112 688 121 (@span_join (checked 5) 48 688 64 (@span_join (checked 5) 16 688 32 chunk5x688 (@span_join (checked 5) 16 704 16 chunk5x704 chunk5x720)) (@span_join (checked 5) 32 736 32 (@span_join (checked 5) 16 736 16 chunk5x736 chunk5x752) (@span_join (checked 5) 16 768 16 chunk5x768 chunk5x784))) (@span_join (checked 5) 64 800 57 (@span_join (checked 5) 32 800 32 (@span_join (checked 5) 16 800 16 chunk5x800 chunk5x816) (@span_join (checked 5) 16 832 16 chunk5x832 chunk5x848)) (@span_join (checked 5) 32 864 25 (@span_join (checked 5) 16 864 16 chunk5x864 chunk5x880) (@span_join (checked 5) 16 896 9 chunk5x896 chunk5x912))))))

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
theorem chunk6x256 : span (checked 6) 11 256 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 267 0 = true :=
  (@span_join (checked 6) 128 0 139 (@span_join (checked 6) 64 0 64 (@span_join (checked 6) 32 0 32 (@span_join (checked 6) 16 0 16 chunk6x0 chunk6x16) (@span_join (checked 6) 16 32 16 chunk6x32 chunk6x48)) (@span_join (checked 6) 32 64 32 (@span_join (checked 6) 16 64 16 chunk6x64 chunk6x80) (@span_join (checked 6) 16 96 16 chunk6x96 chunk6x112))) (@span_join (checked 6) 64 128 75 (@span_join (checked 6) 32 128 32 (@span_join (checked 6) 16 128 16 chunk6x128 chunk6x144) (@span_join (checked 6) 16 160 16 chunk6x160 chunk6x176)) (@span_join (checked 6) 32 192 43 (@span_join (checked 6) 16 192 16 chunk6x192 chunk6x208) (@span_join (checked 6) 16 224 27 chunk6x224 (@span_join (checked 6) 16 240 11 chunk6x240 chunk6x256)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 10 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 10 0 = true :=
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
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer7 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer8 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 9 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 8
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    8 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Restricted



namespace SignedFrontier.CliqueLink
def target := SmallCert.Restricted.target
def raw := SmallCert.Restricted.raw
def initial : List W := [0, ~~~(0 : W)] ++ raw ++ raw.map (fun w => ~~~w)
theorem lower (p : List (ℕ × ℕ)) (o : ℕ) (hit : canonical (evaluate p initial o) = target) : 9 ≤ p.length := by
  have inside : {target} ⊆ available (p.foldl add initial) := by
    apply Finset.singleton_subset_iff.mpr
    rw [←hit]
    exact available_read _ _
  obtain ⟨k,s,le,access,run⟩ := extract p initial target 0 {target} Cone.done inside
  have start : available initial = insert 0 SmallCert.Restricted.raw.toFinset := by decide +kernel
  rw [start] at access
  have bounded := SmallCert.Restricted.lower run access
  omega
end SignedFrontier.CliqueLink

namespace TableLink
open SignedFrontier

def assignment (r : Fin 64) (v : Fin 5) : Bool := r.val.testBit v.val

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
    (lower : ∀ p o, canonical (evaluate p CliqueLink.initial o) = CliqueLink.target → 9 ≤ p.length)
    (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : ∀ x, ThresholdReplacement.signed p o x = ThresholdReplacement.sliceTarget x) : 9 ≤ p.length :=
  lower p o (wordOfSolution p o hit)

end TableLink

end PEqualNP.Outside.L_meta_12355_aux

open PEqualNP.Outside.L_meta_12355_aux

theorem PEqualNP.Outside.L_meta_12355 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124032 * 2 ^ 32 + 4276676608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124032 * 2 ^ 32 + 4276676608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s existsC
  obtain ⟨C,ok,bound,hit⟩ := existsC
  obtain ⟨D,mono,small,evaluates⟩ := ThresholdReplacement.replacement
    (TableLink.sliceRequirement SignedFrontier.CliqueLink.lower) C ok hit
  exact ⟨D,mono,small.trans bound,evaluates⟩
