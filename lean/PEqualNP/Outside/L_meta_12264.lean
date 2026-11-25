import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12264_aux

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

def target (x : Fin 6 → Bool) := Nat.testBit (4269860992 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[
  ⟨.and, [4,5]⟩,
  ⟨.or, [1,2]⟩,
  ⟨.and, [1,2]⟩,
  ⟨.and, [6,7]⟩,
  ⟨.or, [8,9]⟩,
  ⟨.and, [3,10]⟩,
  ⟨.or, [6,7]⟩,
  ⟨.and, [3,12]⟩,
  ⟨.or, [8,13]⟩,
  ⟨.and, [0,14]⟩,
  ⟨.or, [11,15]⟩], 16⟩
theorem size : witness.size = 11 := by decide +kernel
theorem legal : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel
theorem value : ∀ x, circuitFun 6 witness x = target x := by decide +kernel

abbrev Input := Fin 5 → Bool
def slot : Fin 6 → Nat := ![0, 1, 2, 3, 5, 4]
def held : Fin 6 → Bool := ![false, false, false, false, true, false]
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
  let pin := fun j : Fin 6 => (fun x : Input => lift x j, Nat.testBit 41 j.val, Nat.testBit 57 j.val)
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
      have stable : ∀ j : Fin 6, slot j < 5 → Nat.testBit 41 j.val = Nat.testBit 57 j.val := by decide +kernel
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
    have a := hit (fun j => Nat.testBit 41 j.val)
    have b := hit (fun j => Nat.testBit 57 j.val)
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
def target : W := 0xfe80e880fe80e880
def negative : List Nat := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 19, 20, 21, 22, 24]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
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
  · refine ⟨9,25,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 18 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0xffee0000ffee0000ffea0000ffea0000ffcc0000ffcc0000ffae0000ffae0000ffaa0000ffaa0000ffa80000ffa80000ff8a0000ff8a0000ff880000ff880000ff800000ff800000ff2a0000ff2a0000ff0e0000ff0e0000ff0a0000ff0a0000ff080000ff080000ff020000ff020000ff000000ff000000fefe0000fefe0000feee0000feee0000feaa0000feaa0000fe000000fe000000fcfc0000fcfc0000f0f00000f0f00000f0000000f0000000eeee0000eeee0000eeaa0000eeaa0000ee000000ee000000eaea0000eaea0000cccc0000cccc0000bfaa0000bfaa0000bf000000bf000000afaa0000afaa0000af000000af000000aeae0000aeae0000aaee0000aaee0000aaaa0000aaaa0000aa880000aa880000aa0a0000aa0a0000aa000000aa000000a8a80000a8a800008a8a00008a8a000088aa000088aa00008888000088880000880000008800000080800000808000007f0000007f0000003f2a00003f2a00003f0c00003f0c00003f0000003f00000033000000330000002a2a00002a2a00001f0000001f0000000f0a00000f0a00000f0000000f0000000e0e00000e0e00000aaa00000aaa00000a0a00000a0a00000a0000000a00000008080000080800000300000003000000020200000202000000ee000000ee000000aa000000aa00000088000000880000000a0000000a0000000000000000 else 0xff00ea00ff00ea00ff00cc00ff00cc00ff00aa00ff00aa00ff008800ff008800ff000a00ff000a00ff000000ff000000fefefe00fefefe00fe00fe00fe00fe00fe00ee00fe00ee00fc00fc00fc00fc00eeffee00eeffee00eeeeee00eeeeee00ee00ee00ee00ee00ee00aa00ee00aa00ee000000ee000000ea00ea00ea00ea00cc00cc00cc00cc00af00aa00af00aa00af000000af000000ae00ae00ae00ae00aaffee00aaffee00aaffaa00aaffaa00aaff0000aaff0000aaccee00aaccee00aaaaaa00aaaaaa00aa88aa00aa88aa00aa0aaa00aa0aaa00aa00ee00aa00ee00aa00aa00aa00aa00aa008800aa008800aa000a00aa000a00aa000000aa000000a800a800a800a8008a008a008a008a0088ffaa0088ffaa0088ff880088ff880088aaaa0088aaaa0088888800888888008800aa008800aa00880088008800880088000000880000008000800080008000550000005500000044004400440044003f0000003f0000002a002a002a002a000ffff0000ffff0000fff00000fff00000f000a000f000a000f0000000f0000000e000e000e000e000afffa000afffa000affaa000affaa000aff0a000aff0a000aaaaa000aaaaa000a0a0a000a0a0a000a00aa000a00aa000a000a000a000a000a0000000a00000008000800080008000300000003000000020002000200020000fffe0000fffe0000fff00000fff0) else (if page < 3 then 0xa0aaa0a0a0aaa0a0a0a8a8a0a0a8a8a0a0a2a2a0a0a2a2a0a0a0f0a0a0a0f0a0a0a0e0e0a0a0e0e0a0a0aaa0a0a0aaa0a0a0a0a0a0a0a0a0a0a0a000a0a0a000a0a08080a0a08080a0a02020a0a02020a0a000a0a0a000a0a0a00000a0a00000a080a080a080a080a020a020a020a020a00ff000a00ff000a00aaaa0a00aaaa0a00aa000a00aa000a000f000a000f000a000a0a0a000a0a0a000a000a000a000a0000000a00000008aa08aa08aa08aa0888088808880888080a080a080a080a0808ff080808ff080808aaaa0808aaaa080888880808888808080a0a08080a0a080808080808080808080000080800000800ff000800ff0008000800080008000707000007070000070007000700070003ff000003ff000003fc03fc03fc03fc030f0000030f00000303fcfc0303fcfc03030300030303000303020203030202030300000303000003020302030203020300ff000300ff0003000f0003000f000300030003000300030000000300000002aaaaaa02aaaaaa02aa02aa02aa02aa020a020a020a020a0202aaaa0202aaaa02020a0a02020a0a02020202020202020202000002020000020002000200020001010000010100000100ff000100ff00010001000100010000ffffaa00ffffaa00ffff0000ffff0000ffaaaa00ffaaaa00ff0ff000ff0ff000ff00fe00ff00fe00ff00f000ff00f000ff00ee00ff00ee else 0xf0e0f0e0f0e0f0e0f0e0f0a0f0e0f0a0f0e0e0e0f0e0e0e0f0c0f0c0f0c0f0c0f0b0f0a0f0b0f0a0f0affaa0f0affaa0f0a0f0e0f0a0f0e0f0a0f0a0f0a0f0a0f0a0f080f0a0f080f0a0f000f0a0f000f0a0e0a0f0a0e0a0f0a0a0a0f0a0a0a0f0a00000f0a00000f080f0a0f080f0a0f080f080f080f080f030f000f030f000f0300000f0300000f020f020f020f020f00fff00f00fff00f00ff000f00ff000f00f0f00f00f0f00f00f0000f00f0000f00afaa0f00afaa0f00af000f00af000f003f000f003f000f000f0a0f000f0a0f000f000f000f000f000a000f000a000f0003000f0003000f0000000f0000000eee0eee0eee0eee0e0eeeee0e0eeeee0e0e0e0e0e0e0e0e0e0e0a0a0e0e0a0a0e0e00000e0e00000e0a0e0a0e0a0e0a0e000e000e000e000ccccccc0ccccccc0c0c0c0c0c0c0c0c0b0b0a0a0b0b0a0a0b0b00000b0b00000b0a0f0a0b0a0f0a0b0a0b0a0b0a0b0a0b000b000b000b000aff0a0a0aff0a0a0aff00000aff00000afa0afa0afa0afa0ace0ace0ace0ace0aaaaaaa0aaaaaaa0aaa2aaa0aaa2aaa0aaa0aaa0aaa0aaa0aaa0a0a0aaa0a0a0aaa00aa0aaa00aa0aaa00000aaa00000a8aaaaa0a8aaaaa0a8a0a8a0a8a0a8a0a2a0a2a0a2a0a2a0a0f0a0a0a0f0a0a0a0f00000a0f00000a0e0a0e0a0e0a0e0a0aff0a0a0aff0a0a0afafa0a0afafa0a0acece0a0acece0a0aaaaa0a0aaaaa)) else (if page < 6 then (if page < 5 then 0x2f2f22222f2f22222f2f00002f2f00002f222f222f222f222f002f002f002f002e2e2e2e2e2e2e2e2aaaaaaa2aaaaaaa2aaa2aaa2aaa2aaa2a2aaaaa2a2aaaaa2a2a2a2a2a2a2a2a2a2a0a0a2a2a0a0a2a2a00002a2a00002a0a2a0a2a0a2a0a2a002a002a002a0022aa22aa22aa22aa22222222222222221fff00001fff00001f3f00001f3f00001f1f00001f1f00001f1100001f1100001f0f00001f0f00001f001f001f001f001f0000001f0000001e1e1e1e1e1e1e1e111100001111000011001100110011000ffff0f00ffff0f00ffff0000ffff0000fff0f000fff0f000fff0aaa0fff0aaa0fff00f00fff00f00fff00000fff00000ff0ff000ff0ff000ff0f0f00ff0f0f00ff00ff00ff00ff00faf00aa0faf00aa0faf00000faf00000faa0faa0faa0faa0fa00fa00fa00fa00f3f0f0c0f3f0f0c0f3f00000f3f00000f3c0f3c0f3c0f3c0f2e0f2e0f2e0f2e0f2a0f2a0f2a0f2a0f0fff000f0fff000f0ff0f00f0ff0f00f0ff0000f0ff0000f0faaaa0f0faaaa0f0f3c3c0f0f3c3c0f0f30300f0f30300f0f0ff00f0f0ff00f0f0f0e0f0f0f0e0f0f0f0a0f0f0f0a0f0f0f080f0f0f080f0f0f000f0f0f000f0f0e0e0f0f0e0e0f0f0e0a0f0f0e0a0f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f0a000f0f0a000f0f08080f0f08080f0f03000f0f03000f0f02020f0f02020f0f000a0f0f000a0f0f00000f0f0000 else 0x555550505555505055554444555544445555000055550000555055505550555055445544554455445500ff005500ff0055005500550055005500000055000000545454545454545450f050f050f050f05050f0f05050f0f0505050505050505044444444444444443fff00cc3fff00cc3fff00c03fff00c03fff00003fff00003fc03fc03fc03fc03fbf00aa3fbf00aa3fbf00003fbf00003f7f00003f7f00003f3fc0c03f3fc0c03f3f3f003f3f3f003f3f3c3c3f3f3c3c3f3f2a2a3f3f2a2a3f3f0c0c3f3f0c0c3f3f08083f3f08083f3f002a3f3f002a3f3f000c3f3f000c3f3f00003f3f00003f3c3f3c3f3c3f3c3f3b00003f3b00003f3300003f3300003f2f00003f2f00003f2a3f2a3f2a3f2a3f2a00003f2a00003f1f00003f1f00003f1500003f1500003f0f33003f0f33003f0f00003f0f00003f0c3f0c3f0c3f0c3f0c00003f0c00003f00ff003f00ff003f003f003f003f003f000f003f000f003f0000003f0000003e3e3e3e3e3e3e3e3cfc3cfc3cfc3cfc3ccc3ccc3ccc3ccc3c3cfcfc3c3cfcfc3c3ccccc3c3ccccc3c3c3c3c3c3c3c3c3c0c3c0c3c0c3c0c3c003c003c003c0033ff000033ff0000333333223333332233332222333322223333000033330000333233323332333233303330333033303322332233223322330033003300330033000000330000003030f0f03030f0f03030303030303030) else (if page < 7 then 0x88ff000088ff000088f888f888f888f888aaffaa88aaffaa88aaaaaa88aaaaaa88aa88aa88aa88aa88aa888888aa888888aa00aa88aa00aa88aa000088aa000088a888a888a888a8888a888a888a888a8888fff88888fff88888ffaa8888ffaa8888ff888888ff888888ff008888ff008888f8f88888f8f88888aaaa8888aaaa8888aa888888aa888888a8a88888a8a888888a8a88888a8a888888aa888888aa8888888888888888888888008888880088888080888880808888080888880808888800888888008888880000888800008880fff08880fff0888088808880888088088808880888088800ff008800ff008800aaaa8800aaaa8800aa008800aa0088008888880088888800880088008800880000008800000080aa80aa80aa80aa80888088808880888080ff808080ff808080aaaa8080aaaa8080888880808888808080808080808080800000808000008000ff008000ff0080008000800080007fff00007fff00007f7f08087f7f08087f7f00007f7f00007f3f00007f3f00007f0f00007f0f00007f00ff007f00ff007f007f007f007f007f0000007f0000007777000077770000770077007700770070707070707070706e6e6e6e6e6e6e6e6a6a6a6a6a6a6a6a5f5f00005f5f00005f005f005f005f005a5a5a5a5a5a5a5a55ff000055ff000055aa55aa55aa55aa5555aaaa5555aaaa5555550055555500 else (if page < 8 then 0xaa08aa08aa08aa08aa02aa02aa02aa02aa00ff00aa00ff00aa00eeccaa00eeccaa00ee00aa00ee00aa00af00aa00af00aa00aaaaaa00aaaaaa00aa88aa00aa88aa00aa0aaa00aa0aaa00aa00aa00aa00aa008800aa008800aa005500aa005500aa000a00aa000a00aa000000aa000000a8fca8fca8fca8fca8aaa8aaa8aaa8aaa8a8ffa8a8a8ffa8a8a8fcfca8a8fcfca8a8aaaaa8a8aaaaa8a8a8a8a8a8a8a8a8a88888a8a88888a8a80000a8a80000a888a888a888a888a800ff00a800ff00a800a800a800a800a5a0a5a0a5a0a5a0a2a2aaaaa2a2aaaaa2a2a2a2a2a2a2a2a0f0a0f0a0f0a0f0a0aaa0aaa0aaa0aaa0a0ffa0a0a0ffa0a0a0f0f0a0a0f0f0a0a0aaaaa0a0aaaaa0a0a0a0a0a0a0a0a0a00000a0a00000a000a000a000a0009f9f88889f9f88889a9a9a9a9a9a9a9a99aa99aa99aa99aa9999aaaa9999aaaa99998888999988889988998899889988990099009900990098989898989898988f8f88888f8f88888f8f00008f8f00008f888f888f888f888f808f808f808f808f008f008f008f008c8ccccc8c8ccccc8aaaaaaa8aaaaaaa8aaa8aaa8aaa8aaa8a8aaaaa8a8aaaaa8a8aaa8a8a8aaa8a8a8a8a8a8a8a8a8a8a8a88888a8a88888a8a0a0a8a8a0a0a8a8a00008a8a00008a88aaaa8a88aaaa8a88aa888a88aa888a888a888a888a888a0a8a0a8a0a8a0a8a008a008a008a0088ff888888ff8888 else 0xaaaaaa8aaaaaaa8aaaaaaa88aaaaaa88aaaaaa80aaaaaa80aaaaaa0aaaaaaa0aaaaaaa00aaaaaa00aaaaa8aaaaaaa8aaaaaaa8a8aaaaa8a8aaaaa888aaaaa888aaaaa0a0aaaaa0a0aaaa8a8aaaaa8a8aaaaa88aaaaaa88aaaaaa8888aaaa8888aaaa8800aaaa8800aaaa8080aaaa8080aaaa5a5aaaaa5a5aaaaa55aaaaaa55aaaaaa5500aaaa5500aaaa2aaaaaaa2aaaaaaa2a2aaaaa2a2aaaaa2222aaaa2222aaaa0aaaaaaa0aaaaaaa0a0aaaaa0a0aaaaa0a00aaaa0a00aaaa0808aaaa0808aaaa0202aaaa0202aaaa00aaaaaa00aaaaaa0088aaaa0088aaaa000aaaaa000aaaaa0000aaaa0000aaa8aaaaaaa8aaaaaaa8aaa8aaa8aaa8aaa8aa88aaa8aa88aaa8a8a8aaa8a8a8aaa2aaa2aaa2aaa2aaa0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aa8caa8caa8caa8caa8aaaaaaa8aaaaaaa8aaa8aaa8aaa8aaa8aaa88aa8aaa88aa88ffccaa88ffccaa88aaaaaa88aaaaaa88aaa8aa88aaa8aa88aa8aaa88aa8aaa88aa88aa88aa88aa88aa80aa88aa80aa88aa00aa88aa00aa88a888aa88a888aa888888aa888888aa880000aa880000aa80aaaaaa80aaaaaa80aa88aa80aa88aa80aa80aa80aa80aa5aaa5aaa5aaa5aaa55ff00aa55ff00aa55aaaaaa55aaaaaa44aa44aa44aa44aa2aaa2aaa2aaa2aaa22aa22aa22aa22aa0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa0aaa00aa0aaa00aa0a0a0aaa0a0a0aaa0a0000aa0a0000)))) else (if page < 13 then (if page < 11 then (if page < 10 then 0xafaeafaeafaeafaeafaaffaaafaaffaaafaaafaaafaaafaaafaaaaaaafaaaaaaafaa0f00afaa0f00afaa0000afaa0000afa0afa0afa0afa0af8caf8caf8caf8caf50af50af50af50af0faa00af0faa00af0f0000af0f0000af00ff00af00ff00af00af00af00af00af00aa00af00aa00af000f00af000f00af000000af000000aeeeaeeeaeeeaeeeaeaeeeeeaeaeeeeeaeaeaeaeaeaeaeaeaeaeaaaaaeaeaaaaaeae0c0caeae0c0caeae0000aeae0000aeaaaeaaaeaaaeaaae0cae0cae0cae0cae00ae00ae00ae00acacacacacacacacababaaaaababaaaaabab0000abab0000abaaabaaabaaabaaab00ab00ab00ab00aaffaaeeaaffaaeeaaffaaaaaaffaaaaaaffaa00aaffaa00aaff88ccaaff88ccaaff5500aaff5500aaff0000aaff0000aafeaafeaafeaafeaaeeeeeeaaeeeeeeaaeeaaeeaaeeaaeeaaeeaaaaaaeeaaaaaaee00ccaaee00ccaaee0000aaee0000aaeaaaeaaaeaaaeaaaccaaccaaccaaccaabfaaaaaabfaaaaaaafaaaaaaafaaaaaaaf0000aaaf0000aaaeaaaeaaaeaaaeaaaaffeeaaaaffeeaaaaffaaaaaaffaaaaaaff00aaaaff00aaaafefeaaaafefeaaaafcfcaaaafcfcaaaafafaaaaafafaaaaaeeeeaaaaeeeeaaaaeeaaaaaaeeaaaaaaeaeaaaaaeaeaaaaaccccaaaaccccaaaaafaaaaaaafaaaaaaaeaeaaaaaeaeaaaaaaeeaaaaaaeeaaaaaaaaaaaaaaaaaaaaaaa8aaaaaaa8aaaaaaa0aaaaaaa0 else 0xcccfcccccccfccccccceccceccceccceccccffeeccccffeeccccffccccccffcccccceeeecccceeeecccccccccccccccccccccc88cccccc88cccccc00cccccc00ccccc8c8ccccc8c8ccccaaaaccccaaaacccc4444cccc4444cccc0044cccc0044cccc0000cccc0000cccacccacccacccaccc8ccc8ccc8ccc8ccc4ccc4ccc4ccc4ccc0ccccccc0ccccccc0ccc0ccc0ccc0cc8ccc8ccc8ccc8ccc88cccccc88cccccc88cc88cc88cc88cc80cc80cc80cc80cc44cc44cc44cc44cc00cc00cc00cc00c4c4ccccc4c4ccccc4c4c4c4c4c4c4c4c3c0c3c0c3c0c3c0c0f0c0f0c0f0c0f0c0ccc0ccc0ccc0ccc0c4c0c4c0c4c0c4c0c0ccccc0c0ccccc0c0c0c0c0c0c0c0c0c00000c0c00000c000ff00c000ff00c000c000c000c000bfff0000bfff0000bfbfaaaabfbfaaaabfbf8888bfbf8888bfbf8080bfbf8080bfbf0000bfbf0000bfaf0000bfaf0000bfaabfaabfaabfaabfaa0000bfaa0000bf3f0000bf3f0000bf0f0000bf0f0000bf00bf00bf00bf00bf000000bf000000bbbbaaaabbbbaaaabbbb0000bbbb0000bbaabbaabbaabbaabb88bb88bb88bb88bb00bb00bb00bb00b0b0b0b0b0b0b0b0afffaaaaafffaaaaafff0000afff0000afaff0f0afaff0f0afafafaaafafafaaafafaf00afafaf00afafaeaeafafaeaeafafaaaaafafaaaaafafa0a0afafa0a0afaf8c8cafaf8c8cafaf5050afaf5050afaf0000afaf0000) else (if page < 12 then 0xeeeeffeeeeeeffeeeeeefefeeeeefefeeeeef0f0eeeef0f0eeeeeeeeeeeeeeeeeeeeeeaaeeeeeeaaeeeeee00eeeeee00eeeeeaeaeeeeeaeaeeeee0e0eeeee0e0eeeecccceeeecccceeeeaeaeeeeeaeaeeeeeaaeeeeeeaaeeeeeeaaaaeeeeaaaaeeee6666eeee6666eeee2222eeee2222eeee0e0eeeee0e0eeeee00eeeeee00eeeeee0000eeee0000eeeaeeeaeeeaeeeaeee0eee0eee0eee0eecceecceecceecceecccccceecccccceeaeeeaeeeaeeeaeeeaaffaaeeaaffaaeeaaeeeeeeaaeeeeeeaaeeaaeeaaeeaaeeaacc00eeaacc00eeaaaaaaeeaaaaaaeeaa0000eeaa0000ee88ee88ee88ee88ee66ee66ee66ee66ee44ee44ee44ee44ee22ee22ee22ee22ee0eee0eee0eee0eee00ff00ee00ff00ee00eeeeee00eeeeee00ee00ee00ee00ee00aa00ee00aa00ee000000ee000000ecececececececececcceccceccceccceaeeeaeeeaeeeaeeeaeaeeeeeaeaeeeeeaeaeaeaeaeaeaeaeaeac0c0eaeac0c0eaeaaaaaeaeaaaaaeaea0000eaea0000eac0eac0eac0eac0eaaaeaaaeaaaeaaaea00ea00ea00ea00e6e6e6e6e6e6e6e6e0e0e0e0e0e0e0e0dddd0000dddd0000dd00dd00dd00dd00dcdcccccdcdcccccdcccccccdcccccccd0d0d0d0d0d0d0d0cfcecfcecfcecfcecececececececececececccccececcccccffccccccffccccccfcccfcccfcccfccceecceecceecceeccddccccccddccccccdcccdcccdcccdc else 0xf5f50000f5f50000f500f500f500f500f3f3f0f0f3f3f0f0f3f30000f3f30000f3f0f3f0f3f0f3f0f300f300f300f300f2f3f0f0f2f3f0f0f2f2f2f2f2f2f2f2f2f2f0f2f2f2f0f2f2f2f0f0f2f2f0f0f2f0f0f0f2f0f0f0f0fff0f0f0fff0f0f0ff0000f0ff0000f0fcf0fcf0fcf0fcf0faf0faf0faf0faf0f7f0f0f0f7f0f0f0f5f0f0f0f5f0f0f0f50000f0f50000f0f4f0f4f0f4f0f4f0f3f0f2f0f3f0f2f0f3f0f0f0f3f0f0f0f3f0c0f0f3f0c0f0f2f0f2f0f2f0f2f0f2f0f0f0f2f0f0f0f1f0f0f0f1f0f0f0f0fff0f0f0fff0f0f0fafaf0f0fafaf0f0f8f0f0f0f8f0f0f0f1f0f0f0f1f0f0f0f0f2f0f0f0f2f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0c0f0f0f000f0f0f000f0f0e0e0f0f0e0e0f0f0c0c0f0f0c0c0f0f0aaaaf0f0aaaaf0f0a0f0f0f0a0f0f0f0a0a0f0f0a0a0f0f05050f0f05050f0f00ff0f0f00ff0f0f000f0f0f000f0f0f00000f0f00000f0e0f0e0f0e0f0e0f0d0f0d0f0d0f0d0f0c0f0f0f0c0f0f0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f080f080f080f080f050f050f050f050f030f030f030f030f000ff00f000ff00f000f0f0f000f0f0f000f000f000f000f0000000f0000000efefeeeeefefeeeeefefaaaaefefaaaaefef0000efef0000efeeefeeefeeefeeefaaefaaefaaefaaef00ef00ef00ef00eeffeeeeeeffeeeeeeffaaaaeeffaaaaeeff0000eeff0000eefeeefeeefeeefe)) else (if page < 15 then (if page < 14 then 0xff00af00ff00af00ff00aaaaff00aaaaff00aa00ff00aa00ff00a800ff00a800ff008888ff008888ff008800ff008800ff008000ff008000ff007f00ff007f00ff005500ff005500ff003f00ff003f00ff000ff0ff000ff0ff000f00ff000f00ff000a00ff000a00ff000800ff000800ff000300ff000300ff000100ff000100ff0000aaff0000aaff000000ff000000feff0000feff0000fefefefefefefefefefeeeeefefeeeeefefeaaaafefeaaaafefe00fefefe00fefefe0000fefe0000fef0f0f0fef0f0f0feeefeeefeeefeeefeee0000feee0000feccccccfeccccccfeaafeaafeaafeaafeaa0000feaa0000fe00ff00fe00ff00fe00fe00fe00fe00fe00ee00fe00ee00fe000000fe000000fcfcfcfcfcfcfcfcfcfcf0f0fcfcf0f0fcfcccccfcfcccccfcfc0000fcfc0000fcf0f0f0fcf0f0f0fcdcccccfcdcccccfcccfcccfcccfcccfcccccccfcccccccfcc0fcc0fcc0fcc0fc00fc00fc00fc00fafafafafafafafafafaf0f0fafaf0f0fafaaaaafafaaaaafafa0000fafa0000faf8faf8faf8faf8faf2f0f0faf2f0f0faf0faf0faf0faf0faf0f8f0faf0f8f0faf0f0f0faf0f0f0faaafaaafaaafaaafaaaaaaafaaaaaaafa0afa0afa0afa0afa00fa00fa00fa00fa000000fa000000f8f8f8f8f8f8f8f8f8f0f8f0f8f0f8f0f8f0f0f0f8f0f0f0f808f808f808f808f7f70000f7f70000f5f5f0f0f5f5f0f0 else 0xff880000ff880000ff80ff80ff80ff80ff80ff00ff80ff00ff808080ff808080ff800000ff800000ff7f0000ff7f0000ff770000ff770000ff5f0000ff5f0000ff550000ff550000ff44ff44ff44ff44ff3fff00ff3fff00ff3fc000ff3fc000ff3f000cff3f000cff3f0000ff3f0000ff330000ff330000ff2f0000ff2f0000ff2aff2aff2aff2aff2a0000ff2a0000ff1f0000ff1f0000ff110000ff110000ff0fff0aff0fff0aff0fff00ff0fff00ff0ff000ff0ff000ff0faa0aff0faa0aff0fa000ff0fa000ff0f8808ff0f8808ff0f00f0ff0f00f0ff0f000aff0f000aff0f0000ff0f0000ff0eff0eff0eff0eff0e0000ff0e0000ff0b0000ff0b0000ff0affaaff0affaaff0aff0aff0aff0aff0aff00ff0aff00ff0a0a0aff0a0a0aff0a000aff0a000aff0a0000ff0a0000ff08ff08ff08ff08ff080808ff080808ff080000ff080000ff070000ff070000ff03ff00ff03ff00ff030000ff030000ff02ff02ff02ff02ff020000ff020000ff01ff00ff01ff00ff010000ff010000ff00ffeeff00ffeeff00ffaaff00ffaaff00ff88ff00ff88ff00ff80ff00ff80ff00ff0aff00ff0aff00ff02ff00ff02ff00ff00ff00ff00ff00fe00ff00fe00ff00fc00ff00fc00ff00fa00ff00fa00ff00f000ff00f000ff00ef00ff00ef00ff00ee00ff00ee00ff00ea00ff00ea00ff00cc00ff00cc00ff00c000ff00c000) else (if page < 16 then 0xffeeccccffeeccccffeeaaaaffeeaaaaffee00eeffee00eeffee00aaffee00aaffee0022ffee0022ffee0000ffee0000ffeaffeaffeaffeaffeac0c0ffeac0c0ffea0000ffea0000ffdd0000ffdd0000ffd5c0c0ffd5c0c0ffcf0000ffcf0000ffccffccffccffccffccccccffccccccffcc00ccffcc00ccffcc0000ffcc0000ffc3c0c0ffc3c0c0ffc0ffc0ffc0ffc0ffc0c0c0ffc0c0c0ffc00000ffc00000ffbf0000ffbf0000ffbb0000ffbb0000ffafffaaffafffaaffafff00ffafff00ffafaaaaffafaaaaffafa0a0ffafa0a0ffaf00aaffaf00aaffaf00a0ffaf00a0ffaf0000ffaf0000ffaeffaeffaeffaeffae0000ffae0000ffab0000ffab0000ffaaffeeffaaffeeffaaffaaffaaffaaffaaff88ffaaff88ffaaff0affaaff0affaaff00ffaaff00ffaaeeaaffaaeeaaffaacc88ffaacc88ffaac080ffaac080ffaaafaaffaaafaaffaaaaaaffaaaaaaffaa88aaffaa88aaffaa8888ffaa8888ffaa5500ffaa5500ffaa0f0affaa0f0affaa00aaffaa00aaffaa0088ffaa0088ffaa000affaa000affaa0000ffaa0000ffa8ffa8ffa8ffa8ffa8a8a8ffa8a8a8ffa80000ffa80000ffa0ffa0ffa0ffa0ffa0a0a0ffa0a0a0ff8f8888ff8f8888ff8f0000ff8f0000ff8aff8aff8aff8aff8a0000ff8a0000ff88ffaaff88ffaaff88ff88ff88ff88ff88ff00ff88ff00ff888888ff888888ff880088ff880088 else (if page < 17 then 0xffff8888ffff8888ffff8880ffff8880ffff8808ffff8808ffff8800ffff8800ffff80aaffff80aaffff8088ffff8088ffff8080ffff8080ffff8000ffff8000ffff3f00ffff3f00ffff2a2affff2a2affff2222ffff2222ffff2020ffff2020ffff0f0affff0f0affff0f00ffff0f00ffff0e0effff0e0effff0aaaffff0aaaffff0a0affff0a0affff0a00ffff0a00ffff08aaffff08aaffff0888ffff0888ffff080affff080affff0808ffff0808ffff0800ffff0800ffff0300ffff0300ffff0202ffff0202ffff0100ffff0100ffff00feffff00feffff00f0ffff00f0ffff00eeffff00eeffff00eaffff00eaffff00ccffff00ccffff00aeffff00aeffff00aaffff00aaffff00a8ffff00a8ffff008affff008affff0088ffff0088ffff0080ffff0080ffff0050ffff0050ffff0044ffff0044ffff0030ffff0030ffff002affff002affff0022ffff0022ffff000effff000effff000affff000affff0008ffff0008ffff0002ffff0002ffff0000ffff0000fffefffefffefffefffe0000fffe0000fffcfffcfffcfffcfffc0000fffc0000fffafffafffafffafffa0000fffa0000fff5f0f0fff5f0f0fff50000fff50000fff0fff0fff0fff0fff0f0f0fff0f0f0fff000f0fff000f0fff00000fff00000ffef0000ffef0000ffeeffeeffeeffeeffeeffaaffeeffaaffeeff00ffeeff00ffeeeeeeffeeeeee else 0xfffffff0fffffff0ffffffeeffffffeeffffffccffffffccffffffaaffffffaaffffff88ffffff88ffffff0affffff0affffff00ffffff00fffffefefffffefefffffcfcfffffcfcfffffafafffffafafffff8f8fffff8f8fffff0f0fffff0f0ffffeeeeffffeeeeffffeeaaffffeeaaffffee00ffffee00ffffeaeaffffeaeaffffe0e0ffffe0e0ffffcceeffffcceeffffccccffffccccffffc0c4ffffc0c4ffffc0c0ffffc0c0ffffc000ffffc000ffffafaaffffafaaffffaf00ffffaf00ffffaeaeffffaeaeffffaaeeffffaaeeffffaaaaffffaaaaffffaa88ffffaa88ffffaa0affffaa0affffaa00ffffaa00ffffa8fcffffa8fcffffa8aaffffa8aaffffa8a8ffffa8a8ffffa888ffffa888ffffa800ffffa800ffffa0aaffffa0aaffffa0a0ffffa0a0ffffa080ffffa080ffffa000ffffa000ffff8a8affff8a8affff88f8ffff88f8ffff88aaffff88aaffff88a8ffff88a8ffff888affff888a))))) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xfd5aa242700d55213806ba82e2bb54416fb5aa242 else 0
  | 3 => if page < 1 then 0x6fac855d2307e4e25acae580ee25ab0cf702c8559a13814e25ac2426dcaacfb0f86dcc45559f680ee25b22426dcc856e20f80efc9aa24280ee25ab24280ee2564a4280ee25652426dcc85569f6782c85541f67dae25aba42792d1d5d242822d7d909ab7eae25aea42706c85779ab712c79779ab7dae2521093782c857e0737dee25aea427dad75aa242822fb5aa2427dae25aa2427dadb9aa242782c856e1ab000fb5aa2426dcc856e05a746c856e1ab712da1669ab822d81669ab712c857e1db6f4c856e1ab704c855d23277ec856e1ab822c416e1ab700c855d20b7dce01aea428aee25aaa428aefb9aa2428aee25aea0b6dcc85551f66dcc85559f66a8a81211538aeef9aea42822ef9aead57dae25aea426dcc856e1ab else 0
  | 4 => if page < 18 then (if page < 9 then (if page < 4 then (if page < 2 then (if page < 1 then 0x822e3190aba485045bc321574909c4b21574908c8c1177ac855d242822c855d24231ce2590aba4840ddddb89642ae9213be642ae92103177cdb990aba485045c4b2157482e08bbe642ae8fb43977cc855d24277cc855d242322ef990aba4840dddf3bb642ae92141177cae9210e5822ef990aba416c855d24231a0c5b7321574908c6b89642ae921014712c855d2423190e590aba48463590aba484644c6b21574908c6814642ae92118d31906dc4b21574909dd389642ae92141177cc855d242870e2590aba484e2590aba48464e08b21574908c6c11712c855d139822ef990aba26f045c4b3657490a08b89642ae8e5b89642ae921034734e2590aba485045c4aba4843e20a389642ae9213e3712c855d242822e2594aba485045c4b2157486615389642ae921389642ae94c242822e2590aba484f25c4b215742e608b89642b80d5c1167cae8ef0e5822e2590ae7357045c4b2157484e08b89574908a6b89642bf0d5831712db990afc357045c4aa048424e08b89642b70d5c3f712c857e1ab712d75502422c7045c4b5d48453608b89540908a6c11712c857e1ab87ee2590aba484e2590aba48458dc4b2157490818b896dcc855d242 else 0x712db990aba273115c4b2157433608b89642b6066c11642ae92107f822e0990aba485045c4b215748e5c4b215749081f3f7712c855d242822e2590aba442db990aba4841c211389642ae921396712c855d2426dcc8567aba48512dc4b21574909c4b2157490897411712c856ca138aee25aea4226f045c4b215564ddc4b215749081b3ae712c855d24282ee2590aba484f1dc4b2157490a08b89642b38d5c2a712c857e1ab712d0590afc35711dc4b21574725c4b2157490853b98712c855d242822e25a12ba484e25b9321574909c4b2157490850b89642ae92103372ee2590aba485045c4aba4843c5c4b2157490811b89642ae948a42826e2590aba484fadc4b2157490a14b89642ae921389642ae94e242822e25a22ba4850d1c4b2157472608b89642b64e4c11712c84d59888aee25aea4232ee2590aba484649c4b21574a6521411712d756a997822e2590aba30f0e5c4b215f86adc4b215f86acc8c1177cc857e1ab87eef990aba484ef990aba48458e08bbe68aae921411642bf0d598d87ec855d24231ac855d24231a58dc4b21574908cd3bc712c855d242822e255d2423a0e25bcb21574909c4b21574908cac39712c855d242) else (if page < 3 then 0x822e2590aab3ed045aa2a048455608b89540908a5b896baa8121011712c855d242366e25aeaa048454de0b89642ae921411642aad21155700c855d2422aae0190aba48404590aba53c908aab21574a7921153712c855d242076f39c4b2157490a21389642ae921389642ae921159712c855d242048e2590aba52a90a1db89642ae921389642ae92118f822e2590ae23570fdc4b215f81620e389642bf0d5bb9712c857e1ab712c855d2420b8f01c4b2157490a08b895749088d389642ae92103877ee2590aba485045c4aa0484545c4b21574908b8bb4712c855d242822c855d2422df0f1c4b215f86adc4b5d540908b8411712d117e1ab87ee25a22ba484e2590ad057458e08bc3688ae921411712d75501398aee2590aba272e2590aba2c64e623b89642ae866c1c712c855d242764e2590aba484e25bd321574909c4b21574908d143c712c855d242822e25922ba485045c4b215748b9c4b21574908b8411712d0d5d242822e2590aba275045c4b2157433dc4b2157490808b89642ae921153878e25a22ba484e2590ad05745c208b215a0ae8aab89688ae921031712db9a22ba485159c4b215744e5c4b215745c09cb89642ae89c831 else 0x712c855d2422bae2590aba4845b9c4b21574908adb89642bf0d5963712c855d29a484e259a2ba48458dc4b2155e908b1b89642ae929963712c855d20d2c6e25ae2ba48458dc4b215749b0b1b89642ae8e5963712c855d29b26ae25a92ba48458dc4b2154e908b1c11712c85799ab712ded90aba484dd990aba4840c608b89540908a7b89642ae92116b712c855d242364db990aba484559c4b215f86ac1c3bf712c857e1ab822e257e1ab1e3045c4b105f86ae08b89642b8cd5c11786c856e1ab786de990aba4850fdc4aba4843c62bb89642ae905c3f712c855d2138aefb9c4b5d484e2590aae48458df7321550908b1b89574908c58f1712c855d20b2c6f0d90aba48468a08b8957490885c11712c855d23d822e2590aba47d045c4b2157485a08b89660ae921411712c855d20d712ae9210f1070efdc4aba4843c5c4aba4843c418b896dcae9210f1712c415d242070fb1c4b2157482dc4b2157482c18b896dcc855d20b822c415d2421cae2590aba4260e1dfb89642ae909c11712ae9098f1822e2590aae417045c4b2155684dc4b2157484c18b896dcc855d213822e255d20b1cb045c4aba438395e1b6e642ae8fb411712c85551f6)) else (if page < 6 then (if page < 5 then 0x712d752114d062e25b735d484535c4aa048453418b896dca812114d822e25909d5356de990aba4840c628b89642ae919447712c855d23488ee255d2794850fdc4b215ce6ae2bb89574908a6b896f4c857e1ab8aee25502421270fdc4b215b86ae2bb896ba908a6c57712a812114d87ee255d24221715dc4b215748f623b895749088543f712c855d23e8aec855d2420ff15dc132157490a2bb895749088343f712c855d2398b8e2590aba464e2590aba48404dec389642ae921457712ae9210f888ee2590aba426e0190aba48418e21b89642ae9213a6712c855d242700c855d2423ed11dc4b2557490a28b89642ae91a389642ae9210127a8e2590aba4850fdc4aba4843e22bb89642ae909c47712ae9210f874ee2590aba48511dc4b4d57490a23b89670ae921447712c857e1ab712c855d2422ccdb990aba484689c4b21574a6d11b896aea8121163712ae92116329ae25502422c624dc4b54540908b1b896ba908b194d712a812116329ae2590afc35668a2bb896ba908b1b89574908c30f8712ae92118b1f0e2590aba42658dc4b21574908da389642ae921157712c855d2422e4e255d2422c63e1c4b21556908b1b89642ae9211a5 else 0x712c857e1b3357045f6b896ba90a08b89642bf02d36e642bf0d58317dae25b735d484f05c4b215f86ac003ed712d75213896dcc857e05a822e2550242131045c4b215f06ae08b89642bf0e9c11712c857e198822e25b5b21357045c4b21356381c4b5d5409081dc05712c857e1ab822e255024212d045c4b215da6ae08b896ba908af411712c857e1a4848e2590afc356e8dc4b215f86ae08b89642c00d5c11712c856f9ab822e25aead1485045c4b215f82a608b215f86ac40411706c857e1ab822e257e1ab213045c4b1e5f86ae08b896ba908b4c11712c857e1d78bee2590aef356e2590afc3560fdfd389642bf0d5c11712bf0d58ff822e258aafc357045c4b5d48458a08b89642bf0eb38954090849831712db950242127045c4b213ac6ae08b8954a90849b6e642bf0d5873846e2590afc356eb1c4b215f86adb73215f8b70d5c11642b70d587a712c856e1ab063045b73215b86adc4b6e642b70d58006dcc856e1ab822d51502420c704590b0b5b86ae08b5454090849b89642bf0d5830712da190afc35704590afc3561e208b60642bf0d5c11712d7521152822e2590afc3a9045c4b6c59a6ae2db89642bf0d5b89642bf0d592e) else (if page < 7 then 0x822e2990aba485045c2321574909c4b2157490819392712c855d242726db990aba484db990b0457490a09389642ae921404712c855d242822e259c2ba3d9045c4b2157476a1a389670ae921411712c857d9ab822e2590ae8356e25922ba4840c5c4b215748b818b896dcd0d5d242712db990aba274e25b732157433e08b89642be4d5c11712c85371ab712c855d24236afe1c4b2157490a08b89642bb8d5c3e712c855d242712c855d2422d90e9c4b21574909c4b21574908c8389642ae921165790e2590aba485045c4b215d46ae1eb89642ae921389642ae92116d858e2590aba484e2590aba52890a2cb89642bd0d5b89574908f08e5792e255d2421cb045c4aba3cc395c4b21574908b23e6712c855d242712c855d1f6366f05c4b215747d9b73215507d8d5c11712ae92114c712c85739ab062e25b73215ce6ae08b896ae908a6411712a812114c792e25a9aba485045c4b21484759b73215b8908d5b89642bf0d583b79ce2590afc357045c4afc3563e208b89622bf0d5c1168eae8ef0e583ee2590afc356ec5c4b215f86adc4aba48453418b896dcae92114d822e2550242133045c4b215f46ae08b89642c0cd5c11712c856e9ab else (if page < 8 then 0x822e259b2ba361045c4aba48443208b89656ae9213895749087c034734e255d2421f0e255d2421f00c5c4b6e5749087c42d712c855d242712c855d29348507dc4b21574909d1b89642ae921411642b2d5d213712c855d242094e6dc4b21574909b730b57490823411712c855d207822e25912ba485045c4b215748fe08b89650ae921411712c855d21a82ce2594aba484fd9c4b29574909c4b2957490818b896dcca55d242830e2590aba432fd1c4b2157486608b89642b0d0cb89642ae90c831712db990aba433045c4aba43c39608b89642ab4fb416712c855d2137ece2590aba427045c4b2158484e08b89652ae909c11712c515d213822c855d277485045c4b4b57490a08b8966aae921411712c855d1cd822e2590aec37704590aba48420208b83642ae921389642ae92103f7f4e2590aba484db990aba4841ce11b89642ae921394712c855d2426dcc856e2ba484db9a3aba4842e608b8957490884b89642ae92103c7c2e2590aba485045c4aba4843fe10389642ae9213a0712c855d242712c855d242060e25b432157490a08b215749083c4116c0c855d242712c855d242072f15c4b2157490a0eb89642ae9213b0712c855d242 else 0x6c0c855d242060da1b0321574909b032157490816b606bcc855d242712c855d24206ae85c4b2157490a0ab89642ae9213e0712c855d242712da15d2421bf045b02ba48437dc4b68642ae8f64116c0c855d1ec822e255d242252e2590aba4847bde6389642ae921411712d355d1ec712df190aba48516dc4aba48440225b89642ae91cb89642ae9211e8712c855d242074f2dc4b21574909c4b2157490807389642ae92112a83ce2590aba484eb5c4b2157490a24b89642ae921389642ae921130712d699eaba484f3990aba4841ce08b1157490839bce642b715d242822d5190aba427045a3aba4843e208b8966eae921411712c855d1ca712cdd5d242062e2590aba3940c5eb389642ae855b896dcd2d5d242712db99aaba484e25b732157473615b89642ae921389642ae94ba426e6c855d242062db990aba4842c5c4b2157490887b7f642ae92103186ae2590aba469045c4b215768d1c4b21574a0521435712cd95d2427ace2590aba168e2590aba510909b73215749d121389642b2940242712cd95d242062e25b733657490a28b8966cae921389642b2921100822e25adb21396e2590aba3960c5c4b6e642ae8e5c11712c857b9b0)))) else (if page < 13 then (if page < 11 then (if page < 10 then 0x822e2590aba483045c4b2757490a08b89642ae9113895749087f83f7f4e255d2421fee255d2421fe0c5c4b6e5749087fb8962aae92103f81ae2590aba442e2590aba4420c5c4b6e642ae910b89642908a203f816e255d2421f1045c4a4228c3e208b895629087c411712c8d5d242822e2590aba475131c4b21574909c4b2157490896389642ae9210757fae2590aba484ff5b7321574909feb2157490839ba3642ae921073846c855d24210108db7321574909fd32157490839c1162aae9210737f4c856e2ba485045aa32157488608b215749084e3836dcc855d24280edb9a3aba484db990adc57419dd1b215b8ae92136e642ae921027822e25b3aba485045c4b21574245c4b21574908173896c4c855d242712da590aba484e2590aba4841e608b2157490841411710c855d242822e4590aba485045b0b21574909c4b70642ae921389642ae921088712c855d24208303dc4b2157490a13389642ae9213896dac855d242642ae921078062db990aba4841e212b89642ae921390712c855d242642ae921078060da190aba4841e212b215749083c390642ae9210786c0c855d242062db9b0321574909c4b2157490816b896bcc855d242 else 0x6dcc8573aba3ed045c4b2148454222b8969aae921411712d356c242712c855d2420d4f45c4b2157490a08b215749088f389642ae8fb06a7a2e2590aba3ecf79b73215747da08b895749088f3de76ec855d1f6712c8d5d242062e2590aba4740c608b895749087ec11712c855d21f822e2590afc41edb990af0574909c4b6e5749087eb896dcc855d21f712db9b3aba484e25b732157424603b8968cae9213896dcc857e20f80efc9c4b5d485045c4b215f872208b215749083bc116bec855d242822e2590afc36d135c4b21574909c4b2157490896b89642ae92102f712d9590aba485045c4b215f87a5c1b2157490813b83642ae9210316dcc855d2421010455d24221220208b8357490884b8957490884831712db95d2422130458f2ba48420208b87642ae91cb89642ae91c831712db990aba473181c1b2157490a28b89642ae91cb83642ae921100712c795d242201045c32ba48441a08b8956e908833956dcc855d2426dcc856f2ba484e2590aba496909c1b2157490814b8963cae9210296e2c855d242062e0d90aef574909c4b5a642ae91cb89642ae92109a80ee25a82ba484e2590afd574909b73215749084ac11712ae92110d) else (if page < 12 then 0x822e2590aba414e258baba484031b7321574938fb411712d315d242822e2590aba19cdb990aab4847d990aba48447818b6e642ae92111e7bcc855d1f60d4db990aba3ec1a9ef36e5747d87c389642aacfb03b79ce2590aab3ecf79b73215567da08b895567d87c411712c45559f66dcc855d2ab3ed04590aab3ec1e9c4b215567d818c116dcc85559f6712db990aab3ec001b73215567d9c4b215746081dc05712ae92111e810db95d24223d045c4aba3043e208b895748708f36e616ae92111e712ae92111e062e25b72ba484479e7321556908fb411622aad211f6642ae92118207701590aba48447a08aba4846087c411642ae90e11e6fac855d242063139c4b215748d1b7321574908feb89642ae9211126e8c855d242063145c4b2157489a27389642ae913389642ae92112589ce25a5aba484f59c4b215747c9c4b215749089336e642ae9210ec712d5990a42243045c4b4b5d6909c4b4b57490818c51712d2d5d242712d5990a42201045c4b5664233e08b8964236867b89642ae867831822e25a5aba0cf04585aba43839608b8957490884411712c855d238894e2590aba484e2590aba4844be08b8569aae921411712c8576234 else 0x848e255d24221507d90aba48420210b7d642ae921452712c855d2257a0e2590aba485085c4aba4843e212389642ae909c24712ae9210f8748e2590aba485091ba321574909f3b89642ae911ba3712ae92111e746c855d24223ce8dc4b34574909d8b89656ae9213b1712c855d2166dcc855d242062e8d90aba4843b1dbb89696ae9213a3712c855d0cf7cee2590aba400e8dc4b52574909dbb89642ae867bb1712d395d242762e2590aba192e2590aba484175d1b895749087c3b1712ae9210f8746e2590aba426f95c4b21574909c4b6f642ae92141171cc855d23b74ae2590aba484e2590aba4841a5b732155690831c1f712ae9210f8842e2590aba426eddc4aba4843e1d8b89642ae909b895749087c03b79ce255d2421f1045c4a422883e1c4b215569081dbf0712c855d213822e2555a421f1045c4b1257484de732155690831c11622aad21063882e2590aba484e2590aba48457208b89642b0d09c11712c8555a03822e25a72ba485045c4b215743260fb89652ae9213b7712ca55d242848e2590aba432e8dc4b2157486608b89642ab501c1f712c855d21376ee2590aba427045c4b1157480dd9b89642ae9213e4712c855d242)) else (if page < 15 then (if page < 14 then 0x822e2590aab3f2db990aba4260c608b896b6c8509c11712c85558c0822e2590aeb427045c4b115743020e389642ae909bb9712c855d213822e2590aee349119c4b2157484dc4b21556908b641177cc855d213822e2590ad8426f3dc4b21574909c4b2157490825b895749087e03b7e0e255d2421f1045c4b2157486dc4b2155c9081dc05712c855d213822e255d24222ae2590aba2f60ee02b895749087c411712908a28f8822e25572421f0e2590aba4260ede7389642ae909c11712ae9098f8822e2590aae427045c4aba4383e1beb215749081dc11642aad2107d822e0590aba426f3990aba4847f5ef37d642ae911c59712c8559a13712c855d24245ee258d2ba48403208b8564cae921451712c855d235712c855d25d484e2590aba4843adeb389642ae911c07712ccd5d242712c8555979077015c4aba43839608b8943851472c11712ab90e0e5712ae90e0e5062e25b72ba43839608b89672ae921411712c855d1c5712c855d24237af55c4b2157490a08b89642ae8ecb89642ae92106b7f8e2590aba484e2590aba2f21aa0338957490872c51712c855d225848e255d24223d09190aba48447a0fb8957490886421712c855d23e else 0x822e255ca421f1045c4ac14843e208b895589087c3d1712ae9210f8712ae9210f80d4e255d2421f00fdfd3895749087c3894845107c03b79ce25211441f0e25211441f00c5c4b6e4845107c440712c855d242712c855d2422bedb95d2421f00c60a3895749087c409712ae9210f8822e255f2421f1045c4ab04843e22c3895749087c389574908b08f8822e255124212ce2590aba484131fdb89642ae921419712ae9210f8834e255d2421f0f8dc4aba4843e1f53895749087c38965aae92103b7e0e2594aba485045c4ac04843e1c4b2155a9081dbf0712c855d219822e2556a421f0e2590aba4260fdfd389642ae909c11712ae9098ff822e258aaba427045c4aba48445e08b8955690886411712c815d213822e255d242233045c4b2b57484e08b89626ae909c11712ca95d2427e2e2590aba426e2590aab4841a9c4b115749081fc0d712c855d213822e255d24222ce2555a421f00ede73895569087c3895569087c031712db955a421f1061c4b2157484dfa389642ae909c11712c8559242712c4555a42076fc1c4b1257484dc4b1257484c18b896dcc495d213822e2590af7427045c4aba43842a08b89642ae109c11712c8562213) else (if page < 16 then 0x712c595d2421d7181c4aba4844522cb89642ad921389642ae9211f480edb95d2421d8db990aba2f419dc2b2157490876389642ae9210ea642c355d2421d901dc4aba4843b208b895749086b411712c855d1c4822c855d24224101dc4b5157490a08b8964273860411712c852114e712c855d242226e25bf32157488e08b8957490889c11712908a490c822c855ca420fb045c4ab948443208b89640ae91f411712ae92010a822e2597ac1485045c4b2158885a08b89656ae90b411712c4d5d216712cbd5d242076e2590aac4840edc4aba4844301db89642ae52103b712c855d2420a2f39c4aba484431f8389642ae91f3f0712cad5d2427e0e2590aba42d015c4b4b574909c4b215748ec1dbce712c855d1f9712ae92110c062e2590aba47c0c5c4b2b57490818b89642ae90b031712c855d2420a0e2590aba484219c4b6e574908863896dcc855d23e712db995aba484e25b732157485a08b89658ae921411712c855d214822e255d2421f7045c4b2157486208b895749087cc11712c855d215822e255d2421fd045c4b21574881e7389642ae8603895749087f83b79ce255d2421fee2590ab14840edf8389642ae910c11712908a48f8 else (if page < 17 then 0x822e255d24223f04603b896ac909b73215749380dbd6712c855d2267ace2590aba41ee25b72ba48447dc4b215749088fc07712ae92111f712c295d24223f01d852ba4843b203b89692ae9213d6712d2d5d1f26dcd5990a421d8e25b734b5d6909b734b57490818c07712db9ab2427ace25a5aba48400203b896ac909c4b5664290871407712c295d0cf6dcc855d0ec19ee25b735664233dc4b6e64236867b6e642ae867831712db9a5aba0cf04590aba48420e08b81642ae91f411712ae9210f5822e2590aba420e15932ba4840c5beb2157489818b896fac855d2268c0e255d242224e258baba48444a28b89642ae907c11706c855d234822e258f2ba469045c4aba484441eb389642ae91a411712ae9210f7822e2590aba424e05beb21574909c4b7d642ae91a460712ae92110f712c755d24221ef59b73215747f5b73215747f433b81642ae9211fd712d2d5d2423fb145c4b2157432e08b2157490904c51712c855d1c8822e255d2421e5045c4b2157483208b89642ae8ec411712d01652426e8c995d242062ddd90aba44c0c5c2b74642ae921377642ae9211fd822dd590aba484db990aba4847ee08b89642ae918c07712ae9210eb else 0x411712c855ca3b822e255d24221d045c4b215587e608b89642ae904411712c855d230712c855d23044ce258c2ba484031c2b1757490806389636ae92100c712c855d242460e2590aba4600c5c4b2157490842c11642ae921085))))) else 0
  | 5 => if page < 35 then (if page < 17 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x872e2590aba4846adc4b21574908d5991822ef990aba4846ae08b21574908d598d822e2590aba3564ddc4b21574908cb831712db990aba48465e08b89574908cb8e5822e2590aba3ec65e1cc11712c855d242872e2590aba48465c00439712c855d242822e2590aba484645c4b21574908cb991000e2590aba48464608b89642ae921015822e2590aba48465a08bbe712c855d242822ef990aba48465c0041177cc855d242822e2590aba48463608b21574908cb98d00104590aba48463608b89642ae921056822e2590aba48465208b89642ae921137822e2590aba32e4de23b89642ae9210b9712c855d24230c2e5c4b215749085c831712db990aba4842e608b89574908728b9822e2585aba4842e617c11712c855d242822e2590aba50090a08b89642ae921009822e2590aba4842d208b9e712c855d242822e2590aba4e690a08b89642ae921046822e2590aba4842b208b89642bf15d242822e25a9aba4842e608b89642ae936a42822e2590aba48472608b89642ae92108c822e2590aba48428e08b89642ae8ef0b9712c855d1de1720c5c4b6e642ae8ef0b9822e255d1de1ca2e608b89616ae8ef0b988ee2590aba3bc2e5c4b21574778c30b9822e255d2422e82e608b89574778ba0b9822e2590a8c4846ae08b89642ae8ef0ac822e2590afc4846ae08b896a6ae8ef0b9001045c4b215f86ae08b89642ae9211ab822e2590aba4842e400411712c855d242 else 0x712c856aaba4840c5c4b6e642b555d2428b9045c4b2157490a08b89642ae92109f822e2590aba48409a08b89642b495d242822fe5c4b2157490a08b89642ae92109e822e2590aba4841c208b89642b3d5d242822e2590aba4847b208c08712d155d242822e2590ad557418e08b8968aae9210b9822e2590ad94846ae08b896baa81211378aee2590aba4844ddc4b21574908b1937712c855d24226e0c5c4b6e642ae921137822e255d24226e39608b89642aa121137822f79c4b215744de08b89642ae89b863822e255d2423122e61b411712c855d242822e2590aba48474a08b89642ae92100f822e2590aba4844d608baf712c855d242822e2590aba48473e08b89642ae921052822e2590aba4844ce08b89642bf0d58a387ee2590aba48428dc4b21574908c58a3822e255d24231228e15389642ae9211ab712d0590aba4846ae08b89642ae8f21ab822e2590aba48465dc4b2157490851831712db990aba48428e08b89574908728a3822e2585aba48428e15411712c855d242854e2590aba48428c0042a712c855d242822e2590aba530909c4b41642ae9210a3000e2590aba53090a08b89642ae921007822e2590aba48428a08b99712c855d242822e2590aba52490a08b89642ae921044822e2590aba48428208b89642b555d242822e25a2aba48428e08b89642ae8f20a3822e2590afc35665e1fb89642ae921197712c855d24232e58e08b8968aae921197) else (if page < 3 then 0x822f79c4b2157490a08b89642ae9211bb822e2590aba48439608b89642ae94b242822e2590aba48467208b89642bf0d585887ee2590aba484161c4b21574908c5858822c855d2423141620e389642ae9211ab772e2590aba4846ae08b89642ae9029ab822e2590aba484679c4b215749082c031712db990aba48416208b89642908a1858822e2590aba3ec1620e411712c855d242838e2590aba4841600041c712c855d242822ec9c4b21574909dcb89642ae921058000ec9c4b2157490a08b89642ae921002822e2590aba48415e08bc3712c855d242822f0d90aba48416208b89642ae92aa42822e2590aba48481a08b89642ae921203822e2590aba40a16208b89642bf0d599e87ee2590aba484679c4b21574a7521163822f0d90aba48467a1e389642ae9211ab712c855d2a04845c208b89688ae9211ab822e2590aba5404e608b89642ae8ef0cd822e2590aba484161c4b21574908cf031712db990aba48467a1e411712c855d242878e2590aba4846780043c712c855d242822e2590aba4845c1c4b21574a7521170000e2590aba4845c208b89642ae921016822e2590aba48467608b89642ae921155822c855d29d48455608b89642b415d242822e25a22ba48467800411712d115d242822e2590aba4844e608b89642ae94e939001045c4b215744e608b89642ae9210cd822e2590aba3b833608b8968ac857e1ab8aee2590ad5574909c4b215aaae921163 else 0x822e2590aba48458dc4b21574a7d21163000e2590aba48458e08bc2712c855d242822e2590aba48455a08b89642b4d5d242822e2590aba4844e208b89642ae9210c0822e2590aba3ba301c4b21574908d583877ee2590aba4846ae08b89574908d58f1822e25882ba4846ae08b89642ae9099ab822f0d90aba3ec6ae08bc3712c857e1ab87ef0dc4b21574909f7389642ae9211638cf045c4b2157490a08b89642ae921053822e2590aba4840e1e1b89642ae921038000e2590aba4840e208bbf712c855d242786efdc4b21574908003bf712c855d242786e2590aba4840c5e1b896dcc855d242822f0dc4aba4843c608b89642ae9210f1001045c4aba4843c608bee712c855d20b822e2590aba48482c00411712c855d20b823021e1b2157490a08bc3642ae9210e5822f0dc4b2157484e08b89642ae921213001045c4b2157484e08bca712ae9210e5822f0d90aba48418e08bc3712c855d1f6822f0d90aba4847da08b21550a8121155822e25aeaa04845562bb89642ae921155712c855d2422c6555c4b21574a8121011712c855d2a048454e08b89574908ef0e5712c855d2422aa0c5c4b6e642ae921155822c855d24230a18e08b21574aa121155822f7990aba48455608b21574908c50e586f045c4b2157490a08b89642ae9211bf822e2590aba484045c4b21574908aa811000e2590aba48404608b89642ae921153712c855d2422aa54c00389642ae921153)) else (if page < 6 then (if page < 5 then 0x712c855d2422c6079c4b2157490911963822ed5c4b2157490a08b89642ae9211a28a3045c4b2157490a08b89642ae9211b0822e2590aba48440208b89642ae94da42822e2590aba484665c4aba540908b18e5712c85542a048458dc4b5d574a8121163000e25aeaa048458dc4b21574908d59a28aee2590aba48458df9b89642ae921163712c855d2422c6395c4b21574908c3063712c855d2a848458dc4b5d642ae9211637bce2590aba48458dc4b21574908c58e5712c855d2422c618dc4b21574908fb163712c857e2ba48458dc4b21574908c58b9712c855d2422c62e5c4b21574908d596376ae2590aba48458dc4b21574a7921163000e2590aba484689c4b21574908b1853712c855d2422c654e2cb89642ae921163712c855d2a148458dc4b21574908b1900712c855d24230c2d1c4b21574a6d21163712c855d24233258dc4b21574908c589f712c855d2422c64d608b89642bf0d5817712c855d24231605e1fb89642ae9211ab822e2590aba4586ae08b89642ae9211a6712c855d24206205dc4b6e642ae92101787f045c4b2157490a1fb89642ae9210170010fdc4b2157490a08b8d712c855d242822e25bb32157490a08b89642ae923a42822e2590aba4848b608b89642ae92122a822e2590aba45805e08b89642bf0d59a687ee2590aba484699c4b21574a8121163822e2590aba3bc30208b89642ae921017712c855d24234c0c5c4b6e642ae9211a6 else 0x1045c4b215b86ae08b896d8c857e1ab822e25aeaa048423208b89642bf0d58df822e2590afc59a6ae08b896baa812114d001045c4b5d48453400411712a812114d87f045c4b215f86ae08b89642ae92107c822e25bd32157490a32c3f712c855d24287ee2590aba4841ea1fb89642ae92103187ee25b732157490a08b89642ae921104822e2590aba4848ca3043f712c855d24287ee2590aba4844022bb89642ae92101e8aee2590aba48488e08b89642ae92123487ee2590aba48407a1fb89642ae921223712de990aba4846ae23b89574908ef0e587ee2590aba3ec6ae1fb89642bf1211ab0010fdc4b215f86ae33c3f712c855d24287ee2590aba4841f22bb89642ae92101187ee25bd321574908003896f4c855d2428c30fdc4b2157490a1fb89642ae9211048aee2590aba48403e2bb89642ae9212328aef79c4b2157490a1fb89642ae9210e58aee2590aba48418e2bb89642ae9211f68a30fdc4b2157490a23b89642ae92110088ee2590aba4840261fb89642ae92123487ef79c4b2157490a23b89642ae9210e587ee2590aba48418e1fb89642ae9211f688ee2590afc57490a2bb89642ae9210b987ee2590aba4842e623b89642ae9211ab87ee2590afc57490a08b896baa81211638cae2590aba48458dc4b21574908b187a712c855d2422c60c5c4b6e642ae921163712c855d24230c079c4b21574acd211638a2e2590aba48458dc4b21574908c5900) else (if page < 7 then 0x822e255d1de1ca2b208b89642a35211ab822e255d2794843960fb89642ae9211ab762e2590aba4846ae08b89642b09211ab822e2590aba3ec6ae08b89642bb1211ab712c855d1f63560c5c4b6e642ae8fb1ab822e255d1f63bc39608b89642aa0fb1ab822c2d5d2423bc39608b89642b9d211ab822e2590aec3ec6ac00411712c85739ab822e2585aba3bc33608b89642ae9099f6822e2590aba4844ee08b89642ae933242822e2590ac64846ae08b89642ae92114d712c857e2423560c5c4b6e642bf1211ab822e255d2a048424e08b89642b71211ab8a3045c4b215f86ae08b896a6ae8ef100822e2590afc35607a08b89642bf1119ab822f79c4b215f86ae08b896a6ae8ef0e5822e2590afc35618e08b89642bf0fb1ab822e25a9b215f86ae08b896baa81210b9822e2590afc3562e608b896a6ae8ef1ab822e25aeaba48453608b89574a812114d001045c4aba48453632c11712c857e1ab822e2590afc3561ea08b89642bf0d5831000e2590afc3560c608b896dcc857e1ab000e25b73215f86ae30411712c857e1ab822e2590afc35640208b896baa812101e822e2590b165f86ae08c08712c857e1ab822e2590afc35639608b896baa8121063822e2590b0b5f86ae2fc11712c857e1ab822e25aeaa048425e08b89642bf0d5829822e2590afc5de6ae08c03712c857e1ab822e25aeaa048424c00411712a8121093822e2590afc3561ce08b89642bf16e1ab else 0x822e2590aba4846ce08b89642ae9211a7712db990aba4846adc4b21574908d99ab712c855d2423660c400389642ae9211b3712c855d24234e0c5c4b2157490818811712c855d24206205a08bc1712c855d242822e2590aba484169c4b21574908d58316dcc855d2423560c5e0b896dcc855d242782e2590aba4846ac003c1712c855d242712db990aba48454dc4b6e642ae92105a712db990aba48467608b89574a8121106822e2590aba46e6ae08b89642ae921168822e2590aba4846a608b89642ae9211d3822e2590aba48466208b89642ae9211b1822e2590aba4846a208b896b6c85211ab822e2590aba35630208b89642b515d242822e2590aba484295c4b21574a812103b80ae2590aba4846ae08b89574a81210f8822e2590aba4386ae08b89642ae92115e822e2590aba48469208b89642ae9211d1822e2590aba48466e12389642ae9211ab746e2590aba4846ae08b89642b0d211ab822e2590aba4066ae08b89642ae9211be822e2590aba48468e08b89642b455d242822e2590aba4842a608b89642ae921167822e2590aba50690a08b89642aed211ab8a2e2590aba4466ae08b89642bdd211ab712c855d2423560ede7389642ae9211ab822e255d2423563e208b89622ae9211ab822e255d2423bc3e208b89642ae921158822e2590aba4f2909c4aba48477872831712db95d2423bc39608b89540908a18e5822e2590a8e4846ae08b8954090872893))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x822e25a9aba2e82e5c4b215749b521031712db990aba4da90a29c11712c855d242822e2590aba48435e08b89642ae921020822e2590aba4d490a08be2712c855d242822e2590aba48435208b89642ae92106c822e2590aba4ce90a08b896d8c855d242822e2590aba48437e30411712ce15d242822e2590aba4da07a08b89670ae9210e5822e2590aba4da7da08b896bace15d242822e2590aba4da2e5c4b21574908e4831712db990aba48472608b89574908f20e5822e2590aa848472628c11712c855d1c9822e2590aba39207a08b89574a2d210e5822e2590aba3ec72608b89590ae9210b9822e2590afc57472622411712c855d242822e2590aba4844fa08b89642ae921019822e2590aba48471a08bc6712c855d242822e2590aba4844f208b89642ae92105e822e2590aba48470608b89642a992108c822e259c2ba4842e608b89642ae8f60b9712c855d2421180c5c4b6e642ae92108c84f045c4b2157490a08b89642c1d5d242822e2590aba48401608b89642ae92108b822e4dc4b2157490a08b89642c115d242822e2590aba48410a08b89642ae92108a822e259c2ba48423208b89642ae8f608c822e2590ac648428e15389642ae9210b9712d0590aba4842e608b89642ae8f20b9822e255d2423bc42a08b89642ae91d9ab822e2590aba4845aa08b89642ae9211aa822e2590ac44846ae08b89642ae8fc9ab822e2590aba48470208b89642ae92119f else 0x822ce990aba48439608b895749cd210b9822e2590aba4fa90a08b89642ae921063822e2590aba4847da08b3e642ae921046828e2590aba4842e604b89642ae9210b9822e2598aba4842e608b89642af9210b9822e2590ab04842e608b89642ae90e0b9712c855d24208c0c5c4b6e642ae921046822e255d2421ca11a08b89616ae921046829045c4b2157490a0a389642ae921046001051c4b2157490a08be3712c855d242812e2590aba484118003e3712c855d242822e2590aba48400608b89642ae921045822e7990aba48411a08b89642ae92ca42822e2598aba48411a08b89642ae928242822e2590abe48411800411712ca55d242822e2590aba48486608b89642ac121046001045c4b2157486608b89642ae90e046822e7990aba4842b208b8969aae9210b9822e2590aba3c42e5c4b2157490856031712db990aba4842b208b89642ae8ba0ac85d045c4b2157490a08b89642ae944a42822e2590aba48402208b89642ae9210ab822cf990aba4842b208b89642b9d5d242822e25a6aba4842b208b89642ae934a42822e2590aba48473208b89642ae8f10ac712c857e2ba4840c5c4b6e642bf15d2428bf045c4b2157490a08b89642ae921097822e2590aba4840a608b89642bbd5d24282300dc4b2157490a08b89642ae921093822e2590aba4841ce08b89642b715d242712d4d5d2421720c5c4b6e6a6ae9210b9822e255d2421b224e08b8968eae9210b9) else (if page < 11 then 0x822e25bfb2157490a08b89642ae924a42822e2592aba48402608b89642ae922242822e2590aba4848da08b89642ae91b80985ee2590aba4842d208b896a4ae9210b9822e2590ac54842e608b89642a9d210b9822e2590aba3be2e5c4b215749085a031712db990aba4842d228b89642ae9210b4712c855d2422fa2d1c4b3f642ae9210b4822e75c4b2157490a08b89642ae93a242822e2590af457490a08b896a4ae9210b4822e2590aba4d890a08b89642b15210b4001045c4b3657490a08b89642ae9211cb822e2590aa74842d000411712c855d1cb822e2590aba3be2d1c4b215749085c834734e2590aba4842e608b895749087c0b9822e795d2421ca2e633411712c855d242822e2590aba4841b608b89642ae92103473ce2590aba4840d000389642ae921034822e69c4b21574909cf39a712c855d242000e69c4b21574909cf389642ae92103173ce25b732157490a08b9e712ae9210f8822e2590aba4843e000411712ae9210f8823021cf32157490a08b9e712ae9210e5822e7990aba48439608bb6712c855d1f6822e2590aba4843ba08b89642ae9211ff822e7990aba48418e08b9e642ae9211f6822cf95d2421ca2e5c4b215749cd21031712db990aba4e690a08b21596ae921063822c8565aba4847da2a411712c855d242822e2590aba48434a08b89642ae921021822e2590aba4e090a08b89642c155d242822e2590aba4842aa08bde642ae939a42 else 0x822e2590aba4842a210b89642ae9210b9762e2590aba4842e608b89664ae9210b9822e25872ba4842e608b89642ae9210d0822e2590aba4842ca08b89642b9d5d0b9822e2590aba2642e608b89642ae934242822e2590aba48423e08b89642ae8bb8b9822e258caba4842e608b89574908ba8b9712c855d2421720ede7389642ae9210b9822e2588aba4842e608b89642908a20b9822e2590aab4842e60fb89642ae9210b976ee2590aba4842e608b8961eae9210b9822e255d2422ec2e5c4aba4845d05c831712db95d2422e82e608b89642ae8c20b9822e255d2423082e608b89642ae92107b822e25b9b2157490a17b89642ae92103185ee25b732157490a08b89642ae9211068c10bdc4b2157490a17b89642ae921100822e2590aba48440a08b89642ae9212288b30bdc4b2157490a1ab89642ae92110085ee2590aba48407a17b89642ae921223712c855d2804840c5c4b6e642ae940242712c85662ba484079c4b21598ae9212238b2e2590aba500909c4b21574a3d21100822fa1c4b2157490a08b89642ae9210b1822e2590b0857490a08b89642ae9210a68a2e2590aba500909c4b3c642ae921100822e2590aba50890a08b89642ae92101e822e2590aba48488dc4b3f642ae921009822e2592aba4842e608b89642ae91b8b9712c855d242062025c4b6e642ae9210098a2e2590aba484025c4b21574908be80985ee2590aba48402608b8b712c855d242)) else (if page < 14 then (if page < 13 then 0x712c855d24216a0c5c4b2157490818821712c855d24206202208bd6712c855d0b9822e2590aba17219e08b9c712c855d242822e2590aba484121b73215749085c8317ace25b73215742e5c4b6e642ae85c867738e25b7321574909c4b6e642ae938242712db990aba484121c4b6e642ae9210ab822e2590aba2fe2e608b89642ae9420b9822e2590aba48430a3038962cae9210b9822e2590af2574909c4b21574908b983b80ae2590aba4842e608b89642908a28b9822e2590aae4842e608b89642ae8be0b9822e2590aba4fa2e5c4aba4843945c831712db95d2421ca2e608b895749f5210b9822e255d27d1ca2e608b89574788728b9822e255d2421f039612389642ae9210b9746e2590aba4842e608b89642ae9210d1822e2590ae0574909c4b0b5749085c831712db985aba4842e608b0b574908728b9822e25a52ba4842e608b89642b855d1f6822e25a42ba4842e608b89574908838b9822e258eaba4842e608b89642ae941242822e2590aba4842de08b89642ae9480b9822e2590aba3602e608b89642ae92113f822e2590aba48429208b89642ae9210c1822e2590aba4842da08b896b8ae9210b9822e255d2422822e608b89642ae935a42822e2590aba484235c4b215749086c83b7e0e2590aba4842e608b895749087e0b9822e25892ba4842e608b89642ae8bd8b9822e2590aba4262e608b89642ae93c242822e2590aba4842ce08b89642ae92113d else 0x822e2590aba4c890a08b89642ae92100b822e2590aba48437608ba2712c855d242822e2590aba4c490a08b89642ae92104d822e2590aba48436e08b896d8ae9210df822e25b63215747b22db89642bf15d242712c857e2ba4844b9c4b21574908f6031712db990aba4847b208b8959aae921100822e2590aba4467b208b8959aae9210e5822e2590aba3ec7b225c11712c855d242896e2590aba4847b00044b712c855d242822e2590aba4844b9c4b2159aae92112e000e2590aba4844ba08b89642ae92101a822e2590aba4847aa08bcd712c855d242822e2590aba4844ae08b89642ae92105f822e2590aba48479e28b89642ae9210298a2e2590aef57490a08b896a6ae921106822e2590afc5748d1c4b21574908a3829712d4190aba48440208b896bacf55d242822e2590afc5746c1c4b215f8ae92103b79ce2590afc57490a08b895f8ae9210f8822e25aeb2157484e08bde642ae921073822f7990adc57490a08b896a6ae9210f8822e2590afc57484e08b21574908a1873822d1d90aba48439608b896baced5d242822e2590afc5746ee0fb89642bf15d242762e2590afc57490a08b896a6ae9210df822e2590afc5747b208b89574908850b9822e258faba4842e608b89642ae943242822e2590aba4842e208b89668ae9210b9822e25862ba4842e608b89642ae9210d3822e2590aba4842b608b89642ae9210c3822e2590aba4842d5c4b2157490861831) else (if page < 15 then 0x822c855d2420f41cdc4b2157490839831822db990aba4841cdc4b6e642ae921073000db990aba4841ce08b215749083b063822c8585aba4841ce11c11712c855d242846e2590aba4841cc00423712c855d242822e51c4b21574909d6389642ae921073000e51c4b2157490a08b89642ae921004822e2590aba4841c608c03642ae921073822e2590aba4b690a08b89642ae9211fe6dcc857e2dc57490a08c03642b715d242822c856e2ba4841e9c4b215b8ae921031822db990adc574909c4b6e642b715d242000db990adc57490a08b54642ae921063822d5190aba4847da2ec11712c855d242822e2590aba48427608b89642ae921027822e2590ada57490a08b54642ae921093822e25b1b2157490a08b89642ae921090712c857e2ba4840c1c4b68642bf15d242822c857e2ba4841e208b60642bf15d242712db190aba4840c5c4b6e6d8c855d2428c9045c4b2157490a08b89642ae921089822e2590aba4840c1c4b6c642ae921030000e2590aba4840c208b896d0c855d242712db1b4321574908003896d0c855d242823041c4b2157490a08b89642ae921087822e2590aba4841e208b6c642ae92107800104590aba4841e208b896c0c855d242822db1b0321574908004116c0c855d242822e2590aba2ee231c4b215749086f831712db990aba48437e08b89574908800df822e258b2ba48437e08b89574908728df822e2585aba48437e18c11712c855d242 else (if page < 16 then 0x8c5045c4aba484419c4b215749084b831712db990aba48425e28b89642ae921097712c855d2422fa25e08b95712c855d242822e2590ade57490a08b8967aae921097822e2590aba4ca90a08b89642ae9211ed712c855d2422500a5c4b2157490818829712db990aba4840a5c4b215749081601e712c858b2ba4840a62fb89642ae921029822e3dc4b2157490a08b896e2c855d242822e2590aba49890a08b89642ae9212278bee2590aef574909c4b215deae921031712db990aef574909c4b5a642ae92101e712d6990aba48488dc4b5a642ae921097823005c4b2157490a08b89642ae921095822e25b532157490a08b89642ae92108e712c857e2ba4840fdfd389642bf15d242822e257e2ba4843fe08b896bac855d2218d5045c4b2157490a08b89642ae921043822e2590aba4840fe01b89642ae92103f000e2590aba4840fe08bfa712c855d242806fe9c4b21574908003fa712c855d242806e2590aba4840c601b896dcc855d24282300dc4aba4843fe08b89642ae9210ff001045c4aba4843fe08c0e712c855d221822e2590aba48488400411712c855d221823031c4aba4843e1c4b2157490849831712db990aba48424e14411712c855d242822e2590b0157490a08b89642ae921006822e2590aba48424a08b89676ae921093822e2590aba4c690a08b89642ae9211f06dcc857e2ba4841ce08b2157490893873846e2590afc574909d6389642bf15d242 else 0x822e2590add57490a08b89642bfd5d242822e2590af0574909c4b215feae921031712c85782ba4840c5c4b2157490818806712c855d24206209e08c00712c855d242822e2590aba4841d208c07712d4d5d242822e2590afc57419db73215f8ae921031800e25b7321574909c4b6e642ae921092712db990aba4841d1c4b6e642b695d24280ee25b7353574909c4b6e642bf15d067822e2590aba48426208b89642be15d242822e2590b0957490a08b89642ae9211ee822e25a9b3d57490a08b896a6c855d1b0822e2590afe57490a08b89642bc55d242822e25b5b2157490a08b89642ae9210e0712d7590aba4840ee02b89642bf15d242822e2590aba48425a08b89642bb55d242822e25aeaba4843e208b896a6c855d213822e2590b0657490a08b89642ae9211f1848e2590afc574909d1b89642bf15d242822e2590b0057490a08b89642b7d5d242822e25b332157490a08b89642ae9210e1822e25aeb4d57490a08b89642bf15d0cd822c857e2ba48420208b83642bf15d242822e257e2ba48442608b896bac855d2398bf04590aba48420208b89642ae92108000104590aba4842022fc11706c855d242822e25c1b2157490800411706c855d2428bee2590aba4840c62fb896dcc855d2428bf045c4aba48442608b89642ae921109001045c4aba48442631c11712c855d239822e2590aba4848e400411712c855d2398c7145c4b2157490a2fb89642ae921100))))) else (if page < 26 then (if page < 21 then (if page < 19 then (if page < 18 then 0x822e2590aba48438a08b21616ae9210e5823021c4aba48439608c08616ae9210e5712c8573aba4840c5c4b6e642b9d5d2428bd045c4b2157490a08b89642ae92109b822e2590aba4840a208b89642b915d242822e2590aba48437208b89642ae9211e9822e2590aec57484e30411712d355d242822e2590ae757407a08b8969aae9210e5822e2590ae75747d9c4b2157490866831712db990aba48433628c11712c855d0cd822e2590aba19a07a08b89642ae8bc8cd861045c4b2157490a08b89642ae93aa42822e2590aba48402a08b89642ae9210ca822e2590aba4de90a08b89642ae9211c2822e255d2422ec2b208b89642ae8fb1bb822e2590aec48467a1e389642ae9211f6712c855d2a84845c208b89688ae9211f6822e2590aba5504e608b89642ae8fb0cd83ee2590aba4847d9dbb89642ae9211f6822f7990aba4847d9c4b2157490831831712db990aba48418e08b21574908bc86383f045c4b2157490a0fb89642ae92106300107dc4b2157490a08ba3712c855d24276ee2590aba48418c003a3712c855d242822e2590aba48400e08b89642ae921060822f7990aba48418e08b89642ae8fb063712c855d1f60c60c5c4b6e642ae8fb063822e2590aba2f218e08b215747d8bc86383ee2590aba3ec18ddbb89642ae8fb063822f79c4b215747da08bde642ae8fb063822e2590aba5527da08b89642ae921099822e2590afa57490a08b89642c0d5d242 else 0x822e2590aba48441608b89642ae9212338b3139c4b2157490a27389642ae921100822e2590aba4848ee27389642ae92101e89ce2590aba48488dc4b2157490890831712db990aba484485c4b21574908c181e712c858b2ba48448628b89642ae921121712c855d24229440232c11712c855d242822e2590aba4847f608b89642ae92107a822e2590aba4847e608b89642ae945242822e2590aba484685c4b21574908c181b822ddd90aba4847da08b89642ae9131f6822e2590aba4847c9c4b215749081881b712db990aba48406e28b89642ae92101b712c855d2422fa06e27411712c855d24289ce2590aba48406e08b896e8c855d242822ddd90aba48406e08b89642ae924242822e2590aba4848ae08b89642ae921226822e2590aba44c06e27389642ae9211f2822c8585aba4843b208b89696ae9211f6822e2590b0b57433e08b89642ae8fb067822e2590aba48406dc4b21574908f9031712db990aba4847ca28b89642ae9211f2712c85852ba48440208b89642ae921121712c85852ba48448608b89642ae9210ec822c85852ba4843b208b89642b955d242822e25a5aba4847c800411712d2d5d242822e2590aba48433e08b89642c295d0cf001045c4b2157433e08b89642ae921067822e2590aba3e419d90b0b574908728316dcc8585aba484395c4b2157490872831712db990aba48439619411712c855d242822e2590aba4b890a08b89642ae92100c) else (if page < 20 then 0x712db990aba48438a08b21574aa12107d822e0590aba4847da08b89616ae921106822e2590aba4687da08b89642ae921123822e2590aba4847d608b89642ae9421f6822e2590aba3ec6c208b89642ae93b242822e2590aba48468208b89642ae9211fc822e2590aba4847ce08b89642b995d242822e2590aba4842bdc4b21574aa12103b7e0e2590aba4847da08b89574aa1210f8822e2590aae4847da08b89616ae9210f8822e2590aba48446e08b89642ae93e9f66dcc855d2a848418e10b89642ae9211f6746e2590aba4847da08b89642ae92a2426dcc855d2a84847da08b89642ae921122822ea5c4b2157490a08b8e642ae9211f6822f6d90aba4847d9c4b21574908fb03b79ce2590aba4847d9ef321574908fb0317bcdb990aba4847da08b89574908fb0f8822e2590aab4847da08b89642ae92111e7bce2590aba3ec0edef3ce712c855d1f6822f7990aba3ec1e9ef389642ae8fb031822f79b73215747d9ef3896dcc855d1f6000f79b73215747da08bde712ae8fb0f8822f79c4b215567da08b89642ae9559f6001045c4b215567da08c08712ae92111e822e2585aba48447800411712ae92111e7bcc855d2423ec0edef3ce642ae9211f6822f795d2423ec3e208bde642aad211f682302185aba48440208bde642ae9119f682302190aba48447a08b21616ae92111e00104590aba48447a08b896fac855d24289ce2590aba4840c6273896dcc855d242 else 0xf39c4b21574909ef389642ae9210317bce25b732157490a08bde712ae9210f8822fcdc4b2157484def3215749083183b7bcf3990aba48418e08bde5749087c063822f7990aab48418e08bde642ae8bc86383ef7990aba48418def3b7642ae921063842e2590aba4b2909d8b89642ae92ca42712c855d2594840c5c4b6e642ae92ca428a5045c4b2157490a08b89642ae9210ef822e2590aba48407e08b89642ae92b242822e2590aba48431208b89642ae9211b7823021c4b3157490a08b89642ae92c863848e2590aba48480dd1b89642ae921203712c855d2424060c5c4b6e642ae921203822e255d24240639608bde712c855d20389f045c4b2157490a08b89642ae92111c822e2590aba48407208b89642ae921200822e2590aea57490a08b89642ae9210c883ee2590aba484119dbb89642ae921046822e2587aba48411a0a389642ae9210637ece2590aba48418e08b89652ae921063822e2590ab048418e08b89642ae90986383ee2590aba484161d8b89642ae921058822e2590ac24841620e389642ae921063770e2590aba48418e08b89642ae901863822e2590aba48449208b89642ae92fa42822e2590aba49c7d9c4b6e642ae9211f6712c855d24e3ec0c5c4b21574898fb031712c855d2423fa0c5c4b215749081880c822f59c4b215747d9c4b21574908fb0316dcc855d2423ec0c5eb3896dcc855d1f6712db990aba3ec19dc4b7d6dcc855d242)) else (if page < 23 then (if page < 22 then 0x8a2e8dc4b21574909d8b89642ae921100746e2590aba484079d1b89642ae921223822f9dc4b2157490a08b89642ae92105b76ee2590aba2f218ddbb21574908bc863848e8dc4b21574909d53a3712c855d242746e2590aba484139d1b89642ae921031000e2590aba4840c5d1b896dcc855d242000e25b732157490a303a3712c855d242746e2590aba484401dbb89642ae92106776ee2590aba4847c9d1b89642ae9210e57cee8dc4b21574909d8b89642ae9210ef762e2590aba48416dd1b89642ae9212007bce8dc4b21574909d8b89642ae9210e5746e2590aba48418ddbb89642ae921003822e3990aba48418e08b89642ae91d863712c855d24206200dc4b6e642ae92100383ee2590aba48400e08b8e712c855d242822e3990aba48400e08b89642ae921a42822e2590aba4848f208b89642ae91d80383ee2590aba48418208bdb642ae921063822e2590aba3f218dc4b2157490830031712db990aba484181dbb89642ae921060822f6dc4b2157490a08bdb642ae921060822e2590aba4b090a08b89642ae921204822e2590aba3f2181c4b215749083183b79ce2590aba48418def321574908318317bcdb990aba48418e08b895749087c063822e2590aab48418e0fbde712c855d242810e8dc4b2157490a34411712c855d242822e2590aba48413a08b89642ae92103b7bce2590aba4840ec00389642ae92103b822f39c4b21574909ef3ce712c855d242 else 0x822e0590aba48418e08ba8712c855d242822e2590aba48418a08b89642ae92111d822e2590aba48416608b89642ae921068822e2590aba48418608b89642bd15d063822e2590aba18018e08b89642ae92ba42822e2590aba48411dc4b215749083783b7e0e2590aba48418e08b895749087e063822e2590aae48418e08b89642ae8bd8636dcc855d2420de18e08b77642ae9210638a2e2590aba44618e08b21574908bd063642ae9211790c60c5b7321574908bc863712c855d1790c60c5c4b6e642ae8bc863822e255d24223c39608b89642ae8c1063822c855d24223c39608b21574908c1063822e2590aba4841f632c1f712c855d24283ee2590aba4841ea08b89642ae921101822e2590aba4848962cc1f712c855d24283ee2590aba48440210b89642ae92101e842e2590aba48488e0fb89642ae92101e83ee2590aba48488e0fb89642ae8bc86383ec855d2422f218e3441f712c855d24283ee2590aba4841f60fb89642ae92103183ee25b732157490a2d41f712c855d24283ee2590aba48440612389642ae92101c842e2590aba48489610bde712c855d24283ee2590aba48439610b89642ae9210638a307dc4b2157490a12389642ae92110083ee2590aba48406e0fb89642ae921226848e2590aba48439632ba3712c855d242746e2590aba4841ea08baa712c855d242822e2590aba4840c608b896dcc855d24276ee2590aba484079dbb89642ae921223) else (if page < 24 then 0x822c8586aba48439608c07712ae9210e5712c855d2421c40c5c4b21574908bc01e712c858b2ba48438a28b89642ae9210e2712c855d24228e389c4b33642ae9210e2822c8586aba48438a08bd6712c855d24282301dc4aba48438a08b89642ae93e242822e2590aba4846f1c4b21574908bc83b80ae2590aba48439608b89642908a28e5822e2590aba438395ef389642ae8bc83b811015c4aba4843960438957490872831810e25b72ba48439608c08712908a28e5823021c4aba43839608b895749090e0e5001045c4aba438395c4b215749f521031712db990aba4fa90a2ac11712c855d242822e2590aba48431608b89642ae921022822e2590aba4f490a08b895749f5210f8822e2590aba48435608b89642ae9211c3890e2590aba484395c4b21574908b00e5712c855d2423760c5c4b6e642ae9211bb822e255d2423c639621411712c855d242884e2590aba4846ec00442712c855d242822e2590aba484565c4b21574a9121159000e2590aba48456608b89642ae921018822e2590aba4846e208b89642b5d5d242822e2590aba4844d208b89642a8d21093822e259daba48439608b89642ae93e8ac822e2590aba30018e08b89642ae930063822e2590aba4841a9c4b2157490835063712c855d2420d40c400389642ae92106a822f45c4b21574909b7321574908318317a2e25b7321574909e8b89642ae921063000f45c4b2157490a08b215749083f063 else (if page < 25 then 0x712c855d2424460ede7389642ae921223822e255d2424463e208b89642ae959a138a2f79c4b2157488e08b8962eae9210e5712c995d2421ca0c5c4b1757490872831712c855d2421d80c608b89642ae8bc8676dcc855d2421ca0c603b896dcae9210e5712db990aba2f219dc4b746dcc855d242822c855d2422f21f608baa642ae9210e5822e2590aba4843b608bd3712c855d242822e255d24220c39608b89634ae9210e5822e2590aba4bc90a08b89642ae9210e4822e259eaba48439608b89574908f00e5822e2590aba48456a08b89642ae9210ae822e2590aba4843a608b89642ae9210e3822e2590aba4f690a08b89642ae921094712c855d2421ca0ede7389642ae9210e5822e2588aba48439608b89642908a20e5822e2590aba42639619389642ae921031864e25b732157490a08b89642ae92110a8c10c9c4b2157490a19389642ae921100822e2590aba48440e08b89642ae921229712c855d25c4840c5c4b6e642ae92e242822e2590b0257490a08b89642ae9210b08a2e2590aba4b8909c4b33642ae921100822e2590aba4c0909c4b33642ae92100c822e1590aba48439608b8964cae9210e5712db990aba484031c4b215749081580c712c858b2ba48403228b89642ae92100c712c855d24228e03219389642ae92100c822e1590aba48403208b89642ae927242822e25932ba48403208b89642ae922a42822e2590aba4848d619389642ae9210e2 else 0x7e6e25b732157484e08c0e712c855d213822f79c4aab4843e208b89642aad210f8001045c4aab4843e208b89642ab921046822fcdc4b1257484e08b89624ae921213001045c4b1257484e08b89622ae9210f8712c855d2424260c5c4b6e642ae9212138a3045c4b2157484e08b89622ae921100822e2590aba42607a08b89642ae911a138a1045c4b2157490a08b89642ae921118822e2590aba48407608b89642ae92120e822e2590aee57490a08b89642ae9210c78cb045c4b2157484e08b89642ae90987a822e2590aba4260c400389642ae909831822e25b732157484c003896dcc855d2138c1045c4b2157484e08b89642ae909900822e2590aae48407a08b89642c595d2138a1045c4b2157484e08b89624ae921118822e2590aba42607608b89642ae909a0e822e2590aba42616208b8969ec855d213822e25892ba48431e08b89642ae9098b3822e2590aba43869208b89642ae90e0ac7e6e2590aba4840edf9bce712c855d242822fcdc4aba4843e208c08712c855d213823021c4aba4843e208bde712c855d2138a2e2590aba4840ee28bce712c855d242822f7990aba4841f608bde6fac855d2428a3045c4aba4843e22cc11712c855d213712c855d2422fa0ee02b89642ae921100822e255d2422fa3e208b89642ae90e100823021d532157490a08bde642ae9211fd712c855d242076079e7389642ae92101e822e255d2421f007a08b89642aad2101e)))) else (if page < 30 then (if page < 28 then (if page < 27 then 0x7bce255d2421f00ec003895749087c03b822f39c4aba4843e1ef3ce712ae9210f8000f39c4aba4843e1ef3895749087c0317bce25b72ba4843e208c03712ae9210f8822f79c4a422883e208b89574908a20f8001045c4a422883e1c4b215749087c031712db990aba4843e230411712ae9210f8822e255d2422003e208b89642ae8bd81e822e258b2ba4843e219c11712c855d242822e2590aba4a290a08b89642ae92100d822e2590aba4843ce08b89642ae93fa42822e2590aba4846da32c11712ae9210f8822e255d2421f01ea08b895749087c031000e255d2421f00c608b896dcae9210f8000e25b72ba4843e22cc11712ae9210f8822e255d24228e3e208b895749087e01e822e255d2b34843e219c11712ae9210f8822e25972ba4843e208b895749087c00d822e255d2421f03ce08b895749087c046822e2563aba4843e208b89574a89210f8822e255d2421f025a08b895749087e0b3822e255d2421f824dc4b215749082a03b80ae2590aba48411a08b89642908a2846822e2590aba2f811a0cbde712c855d2427c6f79c4b2157490a08bf3712ca55d242822fcdc4b21574865c4b21574aad2103b7e0e2590aba48484e08b89574aad210f882300dc4b2157484e34c11712c855d213822e2590aba43813a08b89642aad2103b7bce2590aab4840ec00389642aad2103b822fc1c4b2157484df9bf0712c855d213000fc1c4b2157484df9b89642ae909831 else 0x712c855d242080032343ce712c855d24280ae2590aba48413a08bfe712c855d242822e2590aba484125e7389642ae92103b7b6f39c4b21574909e7389642ae9210607fef39c4b21574909e7389642ae9210f380ae2590aba484125f8389642ae92120e7acf39c4b2157490a02b89642ae9210e28cae2590aba4840ee32bce712c855d242823021c4aba48442a08bde712c855d23b712c855d2420f40ede7389642ae92107a823021c4b3457490a08bde712c855d1f98d0e2590aba4840c5c4b2157490827031712c855d2420760c5e7389642ae9210317bcf45c4b21574909e8b89642ae9210318d0e25b7321574909c4b6e642ae92104e712db990aba4840ede73896dcc855d2427bce2590aba4841a9c4b6e642ae92106a7bcdb990aba4840c608b89642ae92104f822f65c4b2157490a2cb89642ae92103b8b2f39c4b21574909c4b215749088003b79ce2590aba48440208be9712c855d242822e2590aba48485dc4b215749081e81e7e0e2590aba48407a08bdf712c855d242822f49c4b21574909c4b21574acd2103b7e0e2590aba48488e08c02712c855d242822e2590aba4843ea08c08712d495d242822f79c4b21574301ef389642ae92103f7f4f79c4b2157490a01b89642ae92103b806f39c4b2157490a08bde712ae9210ff822fcdc4b21574885c4b215749087c03b79ce2590aba4843e234411712ae9210f8822e2590a4228a13a08b895749087c03b) else (if page < 29 then 0x822e2590aba4841ca08b89642b6d5d242822e2590aba48437a08b89642ae9211eb8b2e2590af4574909c4b51642ae921100822e25a92ba48440208b89642bd15d223712c855d2421800c5c4b6e642ae9210c0822e2590aba2fa30208b9f712c855d242822e2590aba4e290a08b89642ae937242822e2590aba48471e08b89574908ba8b4822e259b2ba48488e08b89642c595d1cb822e2590aba4466c208b89642bdd211a6822e2590aba44630228b89642ae921223712c855d242062079c4b6e642ae92101e712c855d2422fa07a28b89642ae92101e822e2590aba446079c4b2157488c1881e712db990aba44607a08b89642ae8be81e712c855d2232fa07a28c11712c855d2238a2e2590aba44607a08bde712ae92110c822fcdc4b215748fa34411642ae92107d8d1045c4aba48443208b89642ae92110c001045c4aba48443234c11712c855d23e822e2590aba4848f800411712c855d23e8d7045c4aba48442a08bf3712cad5d242822fcdc4b2157485a08baa642ae92104e822e259a2ba48413a08b89642ae929242822e2590abf48413800411712cad5d242822e2590aba48485a08b89642ae90e84e001045c4b21574859c4b215749082a83b8d0e2590aba4840ee08b89642ae927a42822e2590aba484891c7389642ae92103b712c855d24207600dc4b2157aae92103b712c855d2b44840edc4b215749081d80d712c855d24207a075c4b215749392103b else 0x822e2590abb48405e08b89642ae91501e822e2590aba48445208b89642ae930223822e2590aba49a909c4b6e642ae921223712c855d24e48488dc4b2157493521223712c855d24d4840c608bd6712c855d2236dcc855d2424460c5eb3896dcc855d2237ace2590aba48488c003d6712c855d223712db990aba44619e08b89642ae921111822e2590aba50888e08b89642ae923242822e2590aba48444e32c51712c855d2238a2e2590aba4461ea2cb89642acd2101e8b2e2590ab348488e30411712ae921113822e258b2ba48444c00411712ae921113712df590aba48488e30389642ae921113712c858b2ba48444c00389642ae921113712c855d2422000c5c4b6e642ae9211008a2e2590aba484401c4b21574908a3900712c858b2ba48440230411712ae921100712c855d2424467f63038962cae9211007b6db990aba48488e08bdb642ae92107a7b6e2590aba4840c608bdb6dcc855d2427b6e25b732157490a08b89642ae9210f6822e2590aba484845b732162cae9210ec712c855d2424460c608b215749087607a822db990aba4843b1c4b6e642ae9210ec000db990aba4843b230389642ae9210ec712c855d2422003b1c4b21574908760e2822e2590aba4fc90a08b89642ae9211b9822c855d2422f418208b89642ae9119f9822f6d90aba4847ca08b89696ae921223822e2590b1657433e08b89642ae911867712c857a2ba4840c5c4b6e642bd15d242)) else (if page < 32 then (if page < 31 then 0x822e2590ac548440208b89642ae8f2900822e2590aba30007a08b89642ae921084822e2590aba49c079c4b215749392101e712c855d24e062079c4b215748981881e822e25bf321574909b73215749081881e7ace2590aba484079c4b7e6dcc855d242712df990aba48407a08b89642ae8bf01e822e255d24222640208b89642ae8c081e712c855d2423fa079c4b2157490889900712c855d24230207a28b89642ae9210318a2e25b732157490a2cc51712c855d242712df590aba48407a28b89642ae8be81e71cc855d24206207a32c1171cc855d242822e3990aba4840c5c7389642ae92103171ce25b732157490a08b89642ae9210e6822e2590aba4847e1bbb215749081881e8cb045ba32157490a08b74642ae921031712dd190aba4840c400374642ae921031712dd190aba484032303896e8c855d242712dd190aba48440208bd7712c855d242822e2590aba48419a08b77642ae921003822e2590aba47607a08b8e642ae92101b822e2590aba44c079c4b2157492521031712db990aba49290a2cb89642ae924a42712c855d24a48440208b89642ae921064822e2590aba4847ee08b89642ae9210bb822e2590aba4846ba30411712c955d242822e2590aba492079c4b2157490915031712db990aba4848aa28c11712c855d22a822f71c4b2157490a08b89642ae9210e8822e2590af657490a08b89642ae9210be822e258caba48402608b89642ae91a01e else 0x712c858baba484401c4b2157493921100712c855d242228401c4b215749088a031822e2590aba2fa19db73215749088003180ee25b72ba484401c4b6e642ae8be867712c855d2422fa19deb389642ae921100712df590aba484401c4b21634ae921100712c855d2422904022cb89642ae923242712c858e2ba484401d536e642ae921100822ea990aba4841e9d5389642ae921031822ea9b7321574909d53896dcc855d242822e2590aba4843c208b89642ae9212026dcc8586aba48440208b21574908fe87a822db990aba4847f5c4b6e642ae9211fd000db990aba4847f62cb89642ae9211fd712c855d2423fa401c4b21574908fe9f2822e2590ae957490a08b89642ae9210cb822c8586aba48413a08b89668ae921100822e2590abf48440208b89642ae90e900822ea990aba48438a08c07712ae9211008c0e255d2422000c6303896dcae9211008c1145c4aba48440230389574908a3900712cf55d24228e401c4b21574a1121031712db990aba50890a2cb89642ae942242712c855d29048440208b89642ae92106e822e2590aba4e490a08b89642ae9210d8822e2590aba484721c4b21542908a3900712c855d2423600c5c4b6e642ae9211b0822e255d2423c0401c4b21574908f01008a2e2590aba4846c208bc4712c855d242822e2590aba48455208b89642b595d242822e2590aba4844da08b89642a8521097822e259eaba48440208b89642ae9420b4) else (if page < 33 then 0x712db990b0a57433c003896dcc855d0cf712db990aba48419dc4b6e642ae8f90678a3045c4aba4844322cc11712c855d23e822e2590aba4c290a08b89642ae9211f7822c855d242102032344116fac855d242712df590aba48406e08bda712c855d242822e2590aba48419632c11642ae92107d8cb045beb2157490a30411712ae92110a8a3045c4b215748ee08b215749083e831822df590aba4840c630411712c995d2428a3045c4b2157489a28b215749083e831712c855d2420fa0c628b7d642ae921031712df590aba4840c40037d642ae9210318b2e2590aba49c90a3038964cae9210318a2e2590aba48489a28b89642ae913031001145c4b21574899c4b6e642ae92107d8a2e2590aba484211c4b6e642ae9210848a2db990aba4840c62cbd6712c855d2428a2e2590aba48419e28c11642ae9210808a3045c1b2157490a28c11712ae9211098b3045c4b215748e5c4b2157490883031712db990aba48441a08bab712c855d242822e2590aba4847ea08b89642ae942a42822e2590aba4846b608b89642ae8bf8098bf045c4b215748d1c4b215749091a031712db990aba4848d208bdd712c855d242822e2590aba48439e08b89642be55d242822e2590aba4842f630411712ae9211068a3045c4b215748d22cb896fac855d2428b2e2590aba48441a30451712ae9211068b3145c4b215748d228b89642ae921234001145c4b215748d208b89618ae921100 else (if page < 34 then 0xe2590aba484215c4b6e642ae92110a712db990aba4848edc4b6e642ae92107a8cb04590aba4841ea32b6e642ae92107a712db990aba4c0909c4b6e642ae9211f98cae25b7321574909c4b215749083d0318cae2590aba4840c608b6e642ae921031822c855d2420f40c5b73215749083d0318cb045b732157490a32b6e642ae921031822e2590aba4843d208b89642ae92120f822e2590aba2f019e08b89642ae92d242822e2590aba48480608bd6712c855d1f2822e25b734b57490a08b896dcc855d0cf712db990aba49c909c4b6e642ae921226000db990aba4840c5c4b2157493921031712c855d24244c0c5c4b6e642ae9210316dcc855d24e4840c5b7321574909130316dcc855d242062031b73215749081881b7ace2590aba4840c5eb36e642ae921031712db990aba4843d1c4b6e642ae92120f7e4f59c4b21574909b7321574908710317ace2590aba484389c4b21574908a10e26dcc8586aba48438a03b896dcae9210e2712db990aba4f8909c4b6e642ae9211bc712c855d2420ce0c5b732157490833831712db990aba2f019dc4b21574908bc0677ace25b7321574909eb389642ae921067712db990aba4b4909c4b6e642ae9212016dcc855d2423e40c5eb3896dcc855d1f27ace2590aba4847c8003d6712c855d1f26dcc85852ba4843b1c4b21614ae9210e2712db990ae5574909c4b6e696ae9211f2000e25b734b574909c4b6e642ae9210cf else 0x232c11712ae92110c8cb045c4b215748fa08b89642ae943a42822e2590aba4846b208b89642ae8c00038d1045c4b215748ee08b89642bed5d242822e2590aba4842ea08b89642ae9210c6822e2590aba4846ea08b89642ba15d242822e2590aba48433208b89618ae92104e822e2595aba4841ea08b89642ae90b07a822e2590aba4c018208b215749084287a822c855d24210a0c5c4b2157498121031712c855d2423f20c5c4b215749084287a712c855d24210a0c632b215749083d031712c855d2422140c5c4b215749091d831822e2590aba4842f208b89642ae9211af822e2590af557490a08b89642ae9210bf822e258baba48403208b89642ae92701b712c855d2421780c5c4b21574908d7831712c855e2ba49c909c4b215eaae921031712c855d24217e0c5c4b2157493921226712c858baba484031c4b175749081880c000e258baba484031c4b215749392100c712c855d242020031c2b215749081880c712c995d242062031c4b2157491521031712c855d24246a0c5c4b215749392101b712c855d24e06206dbbb215749081881b712c855d2484840c5c4b2157490915831712c855d22606206dc4b215749081500c822e2590aba48421632c11642ae921085822db990aba48421400411642ae9210858cae2590aba484215c4b6e642ae921085)))))) else 0
  | 6 => if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x822e2590aba4842e451800822e2590aba4846ae32c11712c855d242357045c4b21574908d587a822e2590aba4846ac18800712c855d2423560c608b896dcc855d242356001c4b6e642ae9211ab8c1045c4b21574908d5c11712c855d24235640208b89642ae95024203d045c4b2162cae9211ab823021c4b21574908d5c11712c855d24235639608b89642ae9502420c7045c4b21616ae9211ab8a3045c4b21574908d5c11712c855d2423bc40208b89642ae9211ab03d045c4b21574909119ab822f79c4b21574908d5c11712c855d2423bc39400411712ae9211de1cb045c4b21574908d5863822e2590aba4847d8d5800822e2590aba3ec6ae08b896a6c855d242357045c4b21574a81210b9822e2590aba4846ac5cc11712c855d2423bc6ae08b89642bf15d24235600208b89642bf1211ab00000208b89642bf0d5c3f822e2590aba4846ac0043f822e2590aba4840021fb89642ae9211ab0000021fb89642ae921411712c855d2a048458c00411712c855d2422c6001c4b21574a8121163000001c4b21574908b1c11712c855d24235605c00411712c855d24202f045c4b21574908d59a6001045c4b21574908d3411786e2590aba4846ac00411786e2590aba485045c4b21574a8121155001045c4b21574908aac11712c855d24235616000411712c855d2420b1045c4b21574908d599e001045c4b21574908cf411712d1590aba4846ac00411712c856aaba485045c4b21574a8121137001045c4b215749089bc11712c855d24235628c00411712c855d242147045c4b21574908d5997001045c4b21574908cbc11712c855d2423bc2e400411712c855d24217200208b89642ae8ef0b9 else 0x8cb045c4b215749085cc11712c855d2421721ea08b89642ae9210b9062001c4b215749085c831822e25b73215749085c800712db990aba4842e630411712c855d242173045c4b21574908800b9822e2590aba4845cc0f411712c858b2ba4842e608c08712c855d242173045c4b21574908728b9001045c4aba4843945cc11712c855d2422e618e08b89642c2d5d24217200208b89616ae9210b98b3045c4b215749085cc11712c855d24228e2e608b89642ae9210d903d045c4b21574acd210b9822fcdc4b215749085cc11712c855d2422862e608b89642ae9210d90c7045c4b21574aa1210b9822e25aeb215749085cc11712c855d2421b22e628c11712c855d242173045c4b21574908be8b9822e2590aba4842e40f411712c855d2424462e608bde712c855d242173045c4b21574908bc8b9822e2590aba4842e431c11712c855d2423ec2e608b89642ae92117417200208b89574908ba0b9822e2590afc5749085cc11712c855d2422802e608b89642ae9211311730be08b89642ae9210b90010be08b89642ae921411712cfd90aba4842e400411712c855d280485045c4b215749085c809001045c4b2157490804c11712c855d2421722d000411712c855d242169045cf389642ae9210b9001045cf389642ae921411712cf990aba4842e400411712c855d273485045c4b215749085c846001045c4b2157490823411712c855d2421722b000411712c855d242159045c4b53642ae9210b9001045c4b215f8ae921000822e25a9aba4842e608b89642b195d24217200208b89642ae936a42822e2590aba54c9085c800822e2590aba48472608b89642ae9210b911800208b89642ae92108c) else (if page < 3 then 0x822e2590b0b57490890800822e2590aba48448608b89642ae9211f603600208b89642ae92101b822e2590aba4847d8f9000822e2590aba4847ca08b89642c2d5d2421ca00208b89642ae9210e500104590b0b57490872c11712c85762ba4847d800411712c8573aba485045c4b21616ae9210cd001045c4b2157490866c11712c855d2423ec2b208b89642ae9211f633d045c4b21574908fb063001045c4b2157490831800822e2590aba3ec18e32c11712c857e2ba485045c4b215f8ae92107a822e2590afc57490818800712c857e2ba4840c608b896dcc857e2ba484001c4b6e642bf15d2428c1045c4b215f8ae921411712c857e2ba48440208b896bac855d24203d045c4b5d642ae921223823021c4b215f8ae921411712c857e2ba48439608b896bac855d2420c7045c4b5d642ae9211f68bf045c4b215f8ae9210008bf045c4b2157490a08b896bac855d24212e00208b89642ae921097822e2590afc57490814800822e2590aba4840a608b89642bf177aba48400208b89642bbd5d24282300dc4b215f8ae92100082300dc4b2157490a08b896bac855d24212600208b89642ae921093822e2590afc57490839800822e2590aba4841ce08b89642bf16e2ba48400208b89642b715d242822e25b63215f8ae921000822e25b632157490a08b896bac855d242119045c4b215f8ae9210df001045c4b215749086fc11712d7590aba4847b000411712c855d2423d914608b89642bf15d242822e25a9b2157490880411712c857e2ba48407a08b89642bf15d242447045ef389642bf15d242822e25a9b2157490872c11712c857e2ba48418e08b89642bf15d2423ed045c4b53642bf15d242 else 0x822e2590aba4841e831c11712c855d2420c60c400389642ae921063063045c4b6e642ae921063000e25b732157490831c59822e2590aba48418e08b89642ae9211000c7045c4b215749083781e822e2590aba56690831c117e6e2590aba48418e08b89642ae9210e50c7045c4b21574908378638a3045c4b2157490831c11712c855d2422fa18e08b89642ae92106303d045c4b2157490911863822e2590aba4845e431800822e2590aba2f218c00411642ae9211790c707e08b89642ae92106300107e08b89642ae92100083ee2590aba48418c0000083ee2590aba485045dbb89642ae921063001045d1b89642ae92100076ee2590aba48418c00000746e2590aba485045c4b2157490831803001045c4b2157490801c11712c855d2420c618000411712c855d2420c1045ef389642ae921063001045ef389642ae921000822f7990aba48418e08b89642b095d2420c600208b89642ae92ca42822e2590aba55290831800822e2590aba48480e08b89642ae92106308d045c4b2157490831858001045c4b21574908fb465822e2590aba4847da08b89642ae9211f60f5045c4b21574908fb031000e2590aba4847d818c11712db990aba4847d8003896dcc855d2423ed16608b89642ae9211f6822e2590aba4847d880411712c855d2a848407a08b89642ae959a423ed045f9b89642ae9211f6822e2590aba4847d872c11712c855d2a848418e08b89642ae9542423ed14608b89642ae9211f6822e2590b0b57490880411712c855d2423ec07a08b89642ae9212233ed045ef389642ae9211f6001045ef389642ae8fb000822f7990aba4847da27411712c855d2423ec00227411712c855d242)) else (if page < 6 then (if page < 5 then 0xf79c4b215749081d800000e2590aba4840ee08bde79ce2590aba48400208bce712c855d242000f79e7389642ae921000000f39c4b2157490a32c117bce2590aba485045ef389642ae92107a822f79c4b21574908188007bce2590aba4840c608bde712db990aba484001ef3896dcc855d2428b3045ef389642ae9214117bce2590aba48440208bf3712c855d24203d045f9b89642ae92122382300def389642ae9214117bce2590aba4843e0004117bce255d2421f000208b89642ae9210f800000208b895749087c411810e2590aba48411a08bf3712c855d24242600208bf3712c855d213001045c4b2157490909800001045c4b2157484e08bf37bce2590aba48514608bde712c855d242823021c4b21574908804117bce2590aba48407a08bde712c855d24244719608b89642ae9210e5822e2590aba4843943d411712c855d2421ca0c400389642ae9210e5063045c4b6e642ae9210e5000e25b732157490872c60822e2590aba48439608b89642ae9211001cb045c4b21574908bc81e822e2590b1657490872c51822e2590aba48439608b89642ae9211471cb045c4b215749087281e822e2590aba48488c72c117bce2590aba48439608b89642ae9211431cb0ca08b89642ae9210e50010ca08b89642ae921411712ccd90aba48439400411712c855d25c485045c4b215749087280c001045c4b2157490806411712c855d2421ca38800411712c855d2421c504604389642ae9210e50010460438957490872c11712c855d27d48439400411712c855d27d485045c4b21574908f10e5001045c4b21574908ddc11712c855d2421ca24e08b89642ae9210e515919608b89642ae921063 else 0x822e2590aba4841e80f411712c855d24206207800389642ae92103103d045c4b6e642ae92101e000e25b73215749080f459822e2590aba48407a08b89642ae92110003d045c4b215749081281e822e2590aba4845f40f000822e2590aba2fa07800389642ae92117d03d14608b89642ae92101e00114608b89642ae9210008a2e2590aba48407a08b8e712c855d24203c00208b8e712c855d242822e25bbb215749080f000822e25ba32157490a08b89642ae92101e007045c4b215749080f01b822e2590abb5749080f000822e2590aba49290a08b89642ae95aa4203c00208b89642ae92122a822e2590aba48407804c11712c855d24203c05c00411712c855d24244719608b89642ae921223822e2590aba48488c3d411712c855d2424460c400389642ae921223063045c4b6e642ae921223000e25b732157490911c59822e2590aba48488e08b89642ae921223201045c4b21574acd2101e822e2590aba56690911c51822e2590aba48488c00451822e2590aba44600228b89642ae921223822e2590b1657490880000822e2590aba48440000389642c595d242201045edb89642ae921223001045edb89642ae921411712c858b2ba4843b000411712c855d2421d9045c4b2157490911860822e2590aba48488cf9411712c857baba48488c00411712c857a2ba485045c4b2162cae9210c0001045c4b2157490860411712c855d2424462d208b89642ae92122334d045c4b215749091181e001045c4b215749080f000822e2590aba44607a344117bce2590aba48400234411712c855d242823021c4b2157490827000822e2590aba48413a08bde712c855d24207600208b89642ae92103b) else (if page < 7 then 0x822e25b73215749083d000822e2590aba4841e8003896dcc855d2420f5045c4b6e642ae921031001045c4b2157490818800822db990aba4840c608bd6712db990aba48400208bd6712c855d242822e25b732157490871411712db990aba48419c00411712c855d2420cf045c4b6e642ae9211f2000e25b732157490818800000e2590aba4840c4000006dcc855d242062001eb3896dcc855d242000e25b732157490871000712db990aba48419c003896dcc855d2423e51a228c11712c855d2428a3045c4b215749083e800822e2590aba4841f630411712c855d24201914608b896fac855d242001045c4b7d642ae9214658a3045c4b2157490a28c11712c855d2420f514608b89642ae921031001145c4b2157490818c51822e25b732157490800451712db990aba48517e28c11712c855d2428a3045c4b2157490883000822e2590aba48441a30411712c855d24201316608b89642ae921234001045c4b215749091a4598a3045c4b21574908004598a2e2590aba48519608b89642ae921100822e2590aba4844003d411712c855d2422000c400389642ae921100063045c4b6e642ae921100000e25b732157490880451822e2590aba48440000451712c855d242201045c4b21574908a3900000e2590aba48451c80411754e2590aba48440000411754e2590aba485045c4b2161aae921100001045c4b21574908fec11712c855d24220013a08b89642ae9211001c518208b89642ae92110000118208b8957490880411712c855d28448440000411712c855d284485045c4b21574908ef900001045c4b21574908d8411712c855d24220025e08b89642ae92110016919608b89642ae92101e else 0x4688cb045c4b2157490a32c11712c855d24221400208b89642ae92110a8cb045c4b2157490801c65822e2590aba4848ec00411712c855d24247719608b89642ae92107a00119608b215749083d411712c855d2604841e800411712c855d260485045c4b21574908fc87a001045c4b21574908fcc11712c855d2420f413a08b89642ae92107a0c1045c4b215749083d03100104590aba4841e818800712c855d2420f40c632c11712c855d24206200232c11712c855d242001195c4b2157490818800822e25b732157490a08b89642ae92724206200208b89642ae927242822e2590aba48489818800822e2590aba48489a08b89642ae921031019045c4b215749081881b000001c4b6e642ae921000712c855d24e4840c400389642ae921226062001c4b215749081880c000e2590aba4840c40dc65822e25b732157490800465822db990aba48400232b896dcc855d242))) else 0
  | 7 => if page < 1 then 0x232c11712c855d24200000208b89642ae92107a00000208b89642ae92103100000000389642ae92103100000208b896dcc855d242000000003896dcc855d24200000228c11712c855d24200000208b89642ae92110000000208b89642ae92101e00000208b89642ae92122300000208bde712c855d24200000208b89642ae9210e500000208b89642ae92106300000208b89642ae9211f600000208b89642bf15d24200000208b89642ae9210b900000208b89642ae9211ab else 0
  | 8 => if page < 1 then 0x411712c855d242 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 5
  | 3 => 51
  | 4 => 1101
  | 5 => 2235
  | 6 => 483
  | 7 => 17
  | 8 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 2048
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 11)

def pool (k i : ℕ) := decode (k+1) (field encodedPool k (11*(k+1)) i)

def entries : ℕ → ℕ
  | 2 => 9
  | 3 => 99
  | 4 => 1862
  | 5 => 4050
  | 6 => 1013
  | 7 => 42
  | 8 => 1
  | _ => 0

def keys (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xf5572805c3cc7ccda50823ef81a4fa677b5d6870708fd9fe5017360042a6bc0628234752 else 0
  | 3 => if page < 2 then (if page < 1 then 0xa52a66cca173fc85a12b37379ff106ec9c01b93e995751a8993f35e99640139a93d7c5ff928dea8a91c773938efcbf7e8ed8d4278d8f4d388c45bcea865b6c2a81a4fa677fae48e07d00a41a6f3721e16d2784a76b115f9d6778e88b657870b76366c9c160c787d05eb4d8265c713e3f5b368e8559a6ea5c594f442053cfd1e050a842064f8dc3404b7957d74ae5c1574998fe4f476e2b1042f8ab1e40adf3c23e90eeaa3de66af83ad0778a397254b13934a72c38ce24e83752331936ece92635fec68d33deabb12eef90d92e8a39442c05d0c3211968571df8cddc0fb3e6dc0f8a451a0ea268db0d3835330c7af56a094e767c0812aff807214337015ec996 else 0xf92fcb2df594a3d2f5572805efbae54fefb49c23ef6c590cef4c9bade9cd2487e6aaa74bdf922a47ded5e079de202724dcb9fee8da0d4568d9e0b1ced2dd312ed17bc4a6c84fc562c741afa9c52b0963c5116f32c2079729be3d83f4bab6d693ba9cc23ab982befdb8e6efa1b4ca371fb4c76173b2da041fb226ccc2ab29d28aa9fdc8a5a7553403a6aa60f8) else 0
  | 4 => if page < 30 then (if page < 15 then (if page < 7 then (if page < 3 then (if page < 1 then 0x70646e906f3fa2106e13a2a06d760af06960f170678f8160674a148066a0e19062ac7f606269a320612b90405fb531205e0a8b005cb480c05b54f5c05a2ac33057bf83f057862f7055983570545efe6052a9f2c051a49a605046e4a04ec9f4204e8fe1c04cab86e04b6a36d04871276047e10a7045370ec044534cd042f52ca0429a2d1041b579c0417ffb1040d12ea0409d94304087aa003d18ebf03a310a7038b7edb038a088303662eb5034499bc0303c5e302d3cec6028434ae0280c390026a38840261fd4a02449405023ed72f0238464301f37b6501ef7fd5017a6c8c0172f76f011d05fa00c7ea3e00a6abd3009aedda00763649002af814001fbd56 else (if page < 2 then 0xe6936b40e3842550e0baec20e0126340dbae8430dace2620da807a30d9f6cd80d669a460d6155e40d60ecb40d2538540d11829b0ce8fcef0ce627360c7f2b290c53c1270c246d2c0c1cbde70be3f5310bdc02110bda6fbf0bc004850bb2af260b7864ba0b7819330b24b53a0b1b4a550b11bdf80adade530ad89b050a9350560a67b05c0a36920b0a1a2d650a11e02b0a1017ab09f9673a09e6983e09b7b27a098b773d095745110937ae430926f27608eabb5708e04e0d08bbef16089e3ba7087259c30851ca22084e6e6c081a076d0818922707d222b007c110ed07948baf078f95f50780554107622fbd0742b14907252e91071ababe070b94600709a4f0 else 0x175f997c17376a5c1729b46517232fe31717cce616f3bfea16c51df216ba213c168bb6f7166d995f1645460515eef35c15e3b26c15c039cc15b7b27d156056ae1550ce6115503cc11547860c14d10db614ce2ab614ba02b414a22b121459fb5d14241b0a13ca5f831378e48e1342e0fa13424563132941f2132625091300991912e7dd8912cbb4e912c78cba12c5f782129eaf5a1227f0d411f41a9111bb7dc811b1e28c1198ed2311614b2d115b25871135c061111804f4110bb31e10d2c37f10c8e32a10c13e4510acae7f109f3d19106db196102feadb10046ae11003b10c0fbaa6610fa983c00f4bd0de0f424f650ed059b90ec372760ea39c9d0e6c7dcd)) else (if page < 5 then (if page < 4 then 0x20b8613c20a08576200a461b1ffed6bc1feaf15e1fccf11c1fbfbcf31f9190381f01210a1ef175d41ecc01071ec9c45d1e507c821e4019e21e383a781e0c90741dfda6541dd904c11d945c101d8fd48a1d8747d31d5b9f381d579f4c1d540a731d37344f1d1578bb1d0958121cfc20851ced36a51cc8a8881cb69c741c835ce11c6213991c4a94fc1c0a52bc1beb85d31bd6f0b01bab65891b6afe1e1b5cb3761b1302ee1afbf8981af477401ac7c4f21ac418c51ac2318b1a9bf9fa1a6b92691a10c88119d5e703199ab44c19781ff4196bc768196b68e4195b7e7d18c2533a18aa385b18a7ad77186f0a58184e934417b1a8b0179d7cac178993c51768272f else 0x282a65a127f8c3aa27e28e3427cf641627c06045279d85092788d5c2276ebb8e27582526270bda1126d15a2426c443b1269f97b526422051263516892620c10525e71fb525e6dbba25b5fca925a161fd2589455b2581e4bb254274dd252e713e251f607925192268251597f824ee96f524e2044624d803df2485a470247f098b2465b06424400e3b2427f5f02413f1b323dbe95223b9f27f23b05d9f23aeb64b2380b6a4236930a023671c732354045a23467ac522d9d8db22a52087228f8e302236b24522201d3b22116c06220fd4b821f0ae6121f08cf921c5d51b218ec9482185e1ef21677266215a2f852149712d2129bada21264081210d2888210c5b8c) else (if page < 6 then 0x322194c331fcff4831f999d631c3685731b6819831ac567431790a393174d850316d87223153e12930d5cb6e308e64ce307dbeae3079452f306e4372306941163043047c300813562ff103ab2fdc7feb2f8c1d792f4aeea52f2c30da2f2a53ba2ea2bac82e9b0e942e04599f2dc0b9532d9a4e952d886dd52d59ecc82d0112a82cf4f8fa2cd461782cbc10bf2ca8842d2c3549ea2c20bbb22c0be84b2c05d0c32bf1bfd32bb969c52ba52c9e2b98723f2b31ec9d2b233c802aa292df2a5930162a53b0e62a49634f29c2910a29b5b1432997d0ad298152762959f082293d0d8c292dbbce28d957ce28acc0dd287bed4e28729b0e28550de22845bfea2840647d else 0x3a6b2ee33a624dfd3a541df63a43f0fb3a3929e53a2d4a8b39cab17539b7274b399f158c394d04d2392d9daa392d03a039258772391d52ff38c59d3938b5d797389325d1388190c6385fc9a83841d46938380a9737a0a075379d11bd378cd9ae376abcf337586f8a3748b7123741412f373e98ad373a4cf736d967aa369149ac36226d91361899d135f46dea35dad3b935c2338a35b7069035a95f2e354e1ee13546c6c934f6da1c349cd57a349cc126346c43763454133a3448cee7343b6d7a3417b59c34141189340db7ee340aeb1433d0f209338cde7c337a44963337ddc4331c7407330c5c913309e87832f627ec327ac9a532728e0232702a5d32659f3f))) else (if page < 11 then (if page < 9 then (if page < 8 then 0x4307c24c4301ed5b42d1cc6e425ba28e41de597741dc738441cb3c9d419fe820412d128e4127da044105bff740cacb5e40bdb31840994cd6408f3af64067cd674064bf64404c119b404a570e3fd9e9133fcf52eb3fcda40e3fa166033f99795f3f8f68923f430e963f2826393f1431883efe52de3eecfbde3eeae6873ecb82b83e94d3e73e8d4f883e865f593e555e7d3e237aab3e21c33d3e0884d83de66af83db561033d67e39f3d5d57613d4565a03d2e2aa33d082db13d0205cc3cdf34023cce44303ca7e6d23ca1082a3c97c4803c715f893c19982c3bda14c03bd20da53bb7acb43b6df9dd3b5ae1943b46e4883af95aab3ac980b63ac8c5283a8be522 else 0x4a2cc20a49cd204549cc26d049c3bc0449537d8c4931d19e4926e4e3491de06f48ed00ca48ebd83b48d342da48bda19c489cfb86488b85924862cb8a482bff0e482abdd64820bce34812873b47f8ed0a47f0538a47e8cd9947dba25547cfaec647c60635473899aa4733c74046df90c546bb1c1246b04ef446ac7d2b4699ecbe46870f4f465c8aa0465665c3462433784622c0ad4622281f461d87e44603cc3445d782b145b811184591954b455ef24745356954452ee3ad452d3a214519ecd94501070c44fb34a844f61ee444d9568544acbdb544200dba43ede108439146524367bd4043526998434a2c9b4342109d43284a4643274140432495114317f6cc) else (if page < 10 then 0x51e93fef51de55a251abb0be51a4a52351a35c955185cfd9517c365a51618ba05160b324515b367e513bed88512ed6df511161e35110e6bf50e7cef450cc78d750c51837507a16c3506470fc50616a4a5055806a50533ea4502cf42a501ccfc04f8d59e44f880bb24f52eb484f4d73fe4f1a52e84ee516cf4ed99de54ea9e2434e9db3c84e70e0a54e6662074e6268a04e0ec21c4ddeb3714dc545884d92791e4d6b99ce4d6a74674d5f10454d5a14384d13e1514ce600cc4cd8dfd84cd759804cb6393c4c793c804c722aae4c71f5df4c2ade914c132f924becea304bebdef74bbd7d094af5480c4af380dc4ae5c1574ae064c94ab1c4de4a80c0294a4185a9 else 0x5af612fd5a7c7f5a5a3006c659e9288a59d1c6545984c63d5924063a591d91795919191658f2a89258a29e0558a2596d589b61c4584f43cd58443f13584329cf5823f3e657f817b257af556d57ac748c5797031f57664c18573eb61e56eed91c56ee921e56ea2b9156cdeee456c2f82456ac316b56a800725694dc97567d9fbf562ef0b95604fd9855d6f73d55ccbfc8558cb75755888bb3556fdb3c5545082b5538d2865536feab54a8b5e55493904a546dede0545737765450cba5544c457c5436128954339a7d53e9f37553cfd1e053bd15ae53af59a25374d615530e0ae15308ae2952e470b05275b7de5270cddf524d51365244ddee52111bde520afd1f)) else (if page < 13 then (if page < 12 then 0x630dca2762fd403062b4aa8c62a1e1306281616d627b73c3627ab6a862688133621c199961e8b76e61c34a3861a68f7e618a2de36153d24460f5931f60e9a77260a436a4608ee88f608b8c31606bfeb5606530576055b5d6603c4109600630645fecbb745fdd58625f8754dc5f76a5225f60bb4b5f5f23e05f4d54b45f0da96c5f033fdc5ede14865ec7492b5e958d565e7f8c555e3daaf95e2aa1665d9817485d9545eb5d912c7a5d910c2e5d86a4a45d5eb2c35d5e97c35cda37d25c9e29585c6d0f625c5be97e5c2b88b55c1b414d5c1a84105bf5c11a5be595865bdca8be5bcbf4c35b6c06805b4636b95b2f14805b263b415b0c44555b09f6505b02f950 else 0x6b47adac6b1d1c8f6aee6cf66aec37606ae3187c6ad851f26ab87f036a86a63a6a6bcef86a584dc56a513f3e6a2d2bc16a2838ed6a2731df69ff445269c3f553699cc1f7699a3601697f01736966805e6965ff69692e175868fe98ab68e292b868de97e068810d9b687ac1426828f243682825c167e1034867dd961467d307eb67c2013166f5c3df66d0c67c66cf3918669ba7ea667e97ce666ea17c66634d9265f4267565ea2aa465d034a965c4140165aad15e657c5d61656ad00165462dad6537b8fc64defa7764c0b55264bcfa0664b6ad1464a99193649d75e6649638eb640268d463fa343263c9980063905e45635adf566340301d6338cf7d63263476) else (if page < 14 then 0x74b3b0a274a96fe37494b84d748fd0df748d9796747c6372742d97be7423f4b773cd0a9973ae1570739dd443739d73c7738d34717383c5d67344731d72aa440b720d368871d20fa4713b0071712f1406710caaef70f090c970eee35270ec3f7570c98d98709eb597708a6a05705ae5d97049c74b7040132070158a956fff08406fecd1496fe7ddd26f9e308d6f18bea36f04a1ae6eb7f7b86e9cdd406e3700ee6e0c14a26df22f3c6dea49846d8d480c6d4206a76d2a54866cce6abc6ca7b5046ca3d4756ca292066c75361f6c5a344a6c4fe7986c4358826c2a789b6c27fc9a6bf556236ba11b856b9c6f306b7e01766b75dafb6b6b4f066b560aba6b513957 else 0x7e3107407e17b85e7d9527c27d6894287d5bf1057d4292d47d1cec147d00fadf7cbeb4ce7cb0c4487c7ab2d67c5fa3c27c523c1d7c349cf97c1ceb7b7bdad0387bd0cd6f7b9e5e367b866eaa7b2b4e867af4c4e17ae430ae7a6583727a58e0067a53f1f97a2a64cd7a1bbb137a1a5c4a7a0fd15479f4830b796f606c79697b25795fbd9279558c7e791c0c95790244ae78f24f14787a20cb786d662478290b9d77dfc76177b097407787e58e778500f7776c6cc9776a21537758f46076fd933276d03dfb764d14e5762d87cf760ef3ae75b5eb9275b0ed1775ab03c9759cf3537577160e757371447569b2077537c49c7526416e751d275f74ffdcf674b4ad25)))) else (if page < 22 then (if page < 18 then (if page < 16 then 0x88a87c3e882fe11f882792df8811e16487e174d387d77e84870856bf86d98f388672db71862dac8a862b085a86118b8985df8d6885d3c60285bfb2d685b82a63859105ca85813b948556b8a28547981485206a07847eddfc846cfcd98459421b844147b384271df284221e3d840debb283f575ac83de750483bb99c883977b66839013e18369f4c5835cf5bd834339c98336d1c88302898c82c8eb8e8238ed7a8210f22081f82d9f81ce4c5481b892d18195b2128187399581830147813af6d7812710bd8119f20c80f9451c80ec48cf806725448061809c8057e3298052d5937fcccb0a7f7174d87f47d3ae7f47b0857f19d79e7ed1c3247e84a5787e668f93 else (if page < 17 then 0x94a2aa88949279c394841034947095fd946edda294690bb5940a752793f7b19193e2feba9371705e935f55ee935be8ef93390b52932be34d92826a6192522c20923009b9921be3d4920a7f2d91eaf73391c773ed91c3f8b391ba25c1917c8730914fe1719123abb19028ffd39023c06d8fefe85e8fdc4b6e8f99a93a8f9277398f917e118f554b078ed35b088ecd05c78ebe1f938e22961e8dd98df88db90dab8d832bbc8d82f64e8cf50a738cf29df78ce8b8578ce475358cdfe6858ca9851d8ca8c4798c62d5b88c5c70968bccdfd78bb53d5d8b1dac0c8b08928c8a5d298c8a509a518a4fd2428a1a34d789f94cf489c693f689b3f0958913120b88df9777 else 0x9c1baad59bbef7299ba7bf5b9b8f3b7f9b778f2c9b6b888d9b5692789b51963b9b29145e9ad5107c9a93fe0a9a9273aa9a7298139a5ec7259a4641af9a3341c39a15727f9a0dec8e9a0948a899dfddc799cdfd809999e2ee9985f85e99820728995f17ff9941e126993db74e993a261599358510992f2582990779eb98eb56ad98c6cb2c98c5fb9198a163d0984075a7984013dc9828fe1a981ee5f097e5291b97d1d8d797a508ab978ace0f97745117973f050796e3ef4c96cdae3f96c93bb996b4fef996a64ce29684af539677816f96692cf29662b21a9659439196535945962ce2cf962c035396227d6496066d8b95ee7c5195ab7d3e94dff57394ad3e2f)) else (if page < 20 then (if page < 19 then 0xa4ca503da4bbf76fa4b45fa6a4ab41a8a4932a06a4916a8ca469fce3a456b132a428c44ba41c7316a41b8880a3f38fada3d36956a3afaa10a3a032f5a364dd12a364835ca3598719a30185b5a2d420ada2c7893fa258c0dda22f82dca1de0318a1beb880a16a99d1a0f42093a0e7b8aaa087685da07851d4a06dce2ca0691c21a0605adba04eb70aa03fdfcba0365f14a02c1f65a003f9539fb4e9769f9ec1dc9f9ebb4e9f90b8c39f8ee52d9f7011e99f539dcb9f0dd3669ee3d8fa9e75b0299e4660459e4019c29e2cf23a9e2850d99e0cf0fb9dbb00b09d93363e9d4d00589d2c909e9cf5e93f9cf29a3b9ca626249c8ec3ae9c8410c39c4fde6b9c2f70e8 else 0xad46b972ad2f47dfad21c889ad062af0aca58b77aca1e93fac7cffeeac78152fac65a03bac553c52ac21f350abf60cb4ab90119bab49e604ab29e33aab1b4b52ab192efdaaefe30daae1adebaac97108aaa92591aa84e5deaa5ae357a9da5d52a9bb3c63a997285da9900196a97d2504a9471468a93b6e98a9364292a93476c2a924ff9da91523d4a907f8dba8f888c7a8aad54ea896f52ea890e7f6a849f31ea840d10da8378549a811a82aa7f81f95a7de74a3a78c9c47a753acb9a6e44d43a6aa60f8a686c11fa659ab7ba65890fea64f14aca6429ed2a63fa962a5dfe30fa5c330c2a5bc67a3a59f811da59db893a599f50aa5757a08a56ddfd5a4f15799) else (if page < 21 then 0xb6a63fc4b6a15d23b6368961b6022eccb5bbd361b5ba8797b5a4e4acb593cdcdb58f4ae3b584cb5eb545bc8db53d10c8b523a9e7b4ca371fb4bf76deb49b8b87b47fcbd1b453d844b4162c71b405a901b3e65622b3af4cd8b3ad80a0b398ca25b356c20bb315f200b2e778a0b2ce04adb2894378b238f011b2252d95b2193befb2127922b1eef77fb1a1f934b171b71cb16e9997b141edc2b13bbc45b11a431fb0c119cdb0a08e07b0651cccb063b80bb05f15b9b0470df4b01eabdab011a5b7afb6a406afa8a3ffaf6b9f66af31dbfcaf2df469af20ebe1af1d2abbaf163934aef439f9aec395b1aec0700daeba3505ae6f77f8ae066d1bada1d879ad84e2a1 else 0xbfadd0acbfa8d49fbf8f627ebf82a750bf709b87bf07d713beec9d8abec8f398bec2fa40bebff5efbe9b20ddbe8e068abe50ad57be1414f7bde77532bdd59f29bd5138d4bd4db2a9bd243747bd1fe09abcfbbd5fbcf33f68bceebc31bcce9a9dbcbe01ffbcb0a1a9bcad4cfdbc5db4a1bc26d081bc0e4f04bbd44405bbaf25debba593aabb8c6866bb7992e2bb272fefbb0cb9f7ba4fe4ffba4a25d7b9ff4e37b9f2ccdfb9d13a69b902cc16b8f5e571b8f56313b8a2da47b89c6e8cb87e7f62b86bc862b859270cb84d831fb8491bd0b803aa45b7e22357b7d44845b7bdc989b7adb2aeb767a463b71fd436b704dc80b70300bdb6e8a700b6e552c1b6c73475))) else (if page < 26 then (if page < 24 then (if page < 23 then 0xc9274987c903b98fc8f88509c8f55cf0c8c0a6c5c8afea20c8a07dd7c86f2199c8097d10c80420d7c7b0c80ec793efbac785bf12c7549f6ac73b314ec6c4de62c6bf88f3c6bcae47c6a18267c629744fc613e9b9c5ea46eec592262bc576753fc50f2beac4ec4f61c4e90327c49f225ac407a417c389b9fdc37c0254c35feb84c334d113c313d89ec2bb5618c2b975d7c2b78493c286252ac21c5b45c2070645c1fe8f0dc1df739cc1c68a3bc1bef787c1a1d2c0c19a7220c1693314c1567de0c1518421c1391a68c11d4853c1163910c1071fcfc0f59700c0ca2e3dc0bb3afdc0b82ac5c098ad83c056b75ac0325254c0047e41c002d1dfbfdd5b80bfb9524c else 0xd1b49252d194d38ad1830116d1663f83d1435e42d0cc0594d0b32cf4d0b2cd7fd0a0d4d5cffbd366cfcdd3bfcfb5dc49cfb4398ecf8db31dcf680daecf405b46cf26f5f6cf2136d0cf1e1b50cf1057f8cee1111eced60760cec6ef35cebb1cfdce8092fdce6e7d4dce44cd48ce36a546ce12f236cdfa5087cdcd3f2fcd5a45a3cd18a358ccf5b067cccb0ab1ccc1fd5bccb14727cc8075fbcc55503bcc4bf3d7cc342409cc1eb0e9cc05669acc008708cbf409bdcb849850cb82fc4acb8009decb778d68cb511ef1cb4e3e25cb3ff88ecb3a3abacab34565ca47602cca3fb8f2ca0839d8c9e1792bc9b9cca0c9b2dbfac9834d3ec963cffcc9401efec929f8f3) else (if page < 25 then 0xdadcc3fbdacfc2a9da3308ddda0dd66eda0a8be7d9ef9a68d9ebbe95d9e0b1ced9ddeb3fd9b087ffd9a709e3d986a8e7d9754971d96aa204d9696339d924f6e8d8cd5835d84b7b65d840483fd81eac31d7fe4350d7da00d7d7cb1dc8d7bb032cd7b0188cd772c128d7301aefd72c07a7d712d9a0d71004fcd6b4885bd67b8b95d620a0f5d60fc402d5f23030d5b1cb87d572f1b3d52b3bd9d51e3492d4f4d1ddd4e2bfcad4dcfad8d4a22afdd4879cb6d44b2c57d447f186d432aecdd3cf8a73d3a292abd34ccc46d339857ad336945fd32be6ecd3278d79d31160ccd2921174d28f3d6cd284a609d277f488d2611a95d25112c6d237dbebd224667dd1d568b3 else 0xe28aea70e277f7a5e2748e3fe2710278e25ac315e238ff93e20423abe2016a63e1ddc795e1d6e12ae1837dabe164fde9e15b6659e0fd1713e0be5a4de062479de05b0506e04dd4e5e040f675df89f530df7807d1df6967addf4fe51edf44cf44df3ec1f7df3e2966df3a0a3bdf04dfc4def726b2def2b529dece3109deb2bc5ade812665de0f35ccddf9738fddc49b62dd98f056dd93a3a2dd79afbfdd6bdcf6dd5d5da3dcff2f91dcf50326dce97902dccaaa4ddca92a4adca5a070dc7ba425dc61f4fcdc28e89fdbef01dedbd90f8adbd78742dbcc377fdbc4c449dbc457bfdba8c254db894641db816370db794df5db768521db5b8afbdb553caedaf81f96)) else (if page < 28 then (if page < 27 then 0xebfa602debdbe0ffebd5ac4febbf36f9eba44ce5eb3a18f9eaee895beaa6be22ea836afbea4db81dea3dca4ee9f6316fe9736a95e941dafae93449c1e92c511de90b459ce8f67d08e8e4e19be8d3a182e8be7ca4e8b8405ae8903fcce87ae578e85fa203e8498a91e8479c59e8229c66e81e8f29e7ff11e7e7bacb37e7868503e777867ce757da12e755e04fe715bfc1e6fa0a5fe6eb288fe6e6ffa0e6754b58e63aaab3e6044466e5ec94aae5ea8022e5e0e214e5ca4643e5c007b0e5ad3cc0e5779164e55c7967e55afbcfe4f85d4fe4ef05a4e49b80a0e47f1748e472b9a7e4370e84e42766b4e41a3a7ce3e03052e39e28f3e38836d6e33f5130e2cc7f3e else 0xf5ec123ff568844bf50140f4f4fc67c8f4e4b9bef4a70378f4626119f46018f6f4376babf41fe115f4097a6ff4071506f3dead3ff3dd6ad0f3ba5470f38166fef35fedd8f32a4cddf329a383f2fd6c0ff2f0cbedf2e66e42f27f2b62f2766b4ff241aa0df1fc4ebff1f189e6f1d58f99f1a4f1e9f1739f22f15293a1f1461923f0fe0a32f0fa8640f04c1fe2f033baa0efde636def59177cef40287eeece0060eecb4519eec35bd0ee73e274ee692882ee68bab0ee387b8fee353d37ee0ead4bee0e396eedd85a01edd5e1f6edd5dbdeedd591b4edb9a9bfed9601eded513de8ed4283b4ed42763fed11fae4ec993f72ec55657cec554b78ec51a285ec350b95) else (if page < 29 then 0xfea549e9fe9f30a7fe6e117afe6c71a5fe4f9845fe2c4e88fe03fdc4fde387e4fdcdd575fdcbbb62fdc6e18afdc2e422fdaaf2d6fd40b19bfd1995f2fd123552fce90af1fcc65af1fcc590e8fc7e6f9afc49864efc35cbedfc104a09fbc78054fbc48b0ffbbcd69bfb3f7f2cfb36af96fb2be825faee9cbefae4a848fad9c2bffacb9412fab9001efab766bafa78409dfa212a08fa0b73e3fa00467df9df9639f9d214f1f9baf838f9982240f963f780f95947e7f941fa2af910aefaf8b0fdf4f88d6acaf86b82cff856cea9f846873af7f74fa5f7f4fa61f7cd48ccf79144e3f743e8def73746b2f7196a75f717bff7f6a53840f63d72b7f6268a11f60b18a9 else 0xff85b22aff4daf90ff010f0dfefe5973feeb2405fec5dd5b))))) else 0
  | 5 => if page < 64 then (if page < 32 then (if page < 16 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x3f626be03d75e1603cde27e03cbc74d03828015037a2dbc037209d3036efddb036dbf7c0366b03403641b5c034d853c0331fb16032bc3100328c3ab0326cf540309786e0307f69c02e9c74902dfc76902d959d502d3cec602cb1a8802ba065f02b51fb702a21b7f029bb9c8028960dd02879e21026f8ecd02685b21025ca4a402449405023ed72f02031fff01e16c6301dde6f001d5086a01cfbd6a01b9e43901b85e7601afe34e017826f7015a17ca01501ad601456f07013fae6f012d686900fedace00e6eeac00bef6d300ba1b2e00ad97480099214100887dd00085c6f6007a5eb30077b86b0070fdcf0068d91a005765f9003636980031e36d002206cb else 0x7dd9f3c07db01a407d2330507d203b507cf6ce907c110ed07a947ba079da9780796883107955c250791a8e40790ab260788cece0774181207622fbd074e1ecd07312e7e072fd627071ababe0716aade07158d91070a570506fde88d06f6291f069e7f35069285f1068d8698068cf04f06841509067f578d063c4bea0627fa2b060c4b1d060aa05e0605067906018bfc05fef1d905f2092305c7923405b3e8d105a561bb05a2cce5057580a40571db94056fcf2905602310055de0b5055bca7a054b497d053c17770537bb520518e0d305030ccc04fc748304ef9481048e51cc04828b190467c9de044ee52a0436b133041f8443041c57bf040980a604066bc3) else (if page < 3 then 0xc54ef0f0bf4532d0bf255620beee2440bb0f6500bafed430b9464c80b8066d80b740e240b572ed70b5673510b54d7550b51fa400b4aeb5a0b431f470b20e1fa0b1271620b0f69db0ae0dfd80ace623e0ab165380aab78300aa22a500a9649f20a802d0d0a6398880a526ff50a33ffed0a170b6f0a1460160a1327200a055ac809ea961309e7d16b09db418109b7ee4409b7254309afa9a009a87a7e098f8ab0098d0f73098232e40976a41c0950cf9e094db4e40937ae4309314c01092c7d5c09252354092485bb08f788b308bb1fe308b8fb6a08b514770895dfab08927f48086cafa90861038e083a22640804e32707fdc3af07ef6f5f07ee4de907e85430 else 0x10046ae10ff3d25a0fcdebe90fca69080f9f87e00f89e60e0f5f2e460f4a07b90f4767df0f31444d0f03c24f0efaae520ef73cd40ef4a8900ee72c3a0ee3afa40ed014f20ec84d0f0ec3da330ebfb7cf0ebb7f380eb617440eb416c70ea85f000ea751f00e9c2a590e947d6d0e910b5d0e8af1380e6ffc970e6d52630e541bbb0e4d0da40e3a21980e340bd00e3121020e2c7aa60e1cf15d0e1470d10df2e2170ded48200de56d930de3cfc30dd9b2660dc383640db6ac770dac0e360d9b676f0d9b33cb0d998bcf0d60ecb40d602ed80d4839930d2c1d7b0d1d75220d15ef310d1537270d1183680cdf08a10cd671c90ccbe7a90cb9400c0c9cee6c0c990081)) else (if page < 6 then (if page < 5 then 0x13bb5da813b365b513b1538a1389c7901380961013729214136b94c01358c55e135882891342e0fa13424563133411ae13255cfa13112279130ef43f130e6be51302353512f4947e12d39d3912bd13e312b8640d12b6098e12a7b511129d96a11298bb66128dd4a2127c9664124b4a8b123016cf12289a9b12228d5c1209b86d11f958ca11f36b3111f1770011c0552511bc6d0511bb810611afd4b111acc405115d8a8011560e44112aae201125db2311257173111737ec10fde41010fd4fd810faa0bd10f5f8e510ea93ac10d8fb0f10d5272410d2c37f10b5c37a10949bb110837234106e0f0e105c0e5e103a988a103428a3101dabc6101c5519100a2a4e else 0x1702cd3d16f6a62b16e9780b16c902a616c8e3a816c336f416aae8fb16aa687916aa0bd816a63d92168b8caf166dff3516652b34164d0a8616419e57162e5825161e3875161add35160a20901602979d15ee443915e5c82715e2b52115e176c215d91bfb15d851c815ccc36515838edd1582a202157931c3156e1460153ed1ce15359208153339b51530f3481519319514fb3daf14face1b14ee262a14dc126714ce2ab614c1f2f914bf34c314bda9ed14b08e3714a3670f149a3479149567be14935897148c5ada147c9322145c3e4c1452408e144c50cf14399cfc1436b0131428cece1414b66313ed0c0a13ebde3d13d4616a13d1afbc13c4532c13bf918d) else (if page < 7 then 0x1ac3e4691aafd6111a95cb021a8bbdca1a81b93d1a6b3f841a6326a51a5ed8951a5dd1481a5daa8d1a50534b1a4aee331a45bafb1a44263d1a23bc8c1a0f991119f4289619ecf39919eae06419bb598519ab432b19a750fd19a4e5c4199fb35719846e8a19719fd31962cc9519577040193b453b1935aee71919258b19063d3718fbda6b18f3e8b018f3a89218eaf62518d89e6018d59da018d494a818c779c218b5273918a3fc9318a1f7ad1864f9cb1857aba2180b166217fed96817fd4e0e17f01a6217e08e9817d3da5617bf00c317b4022317ab7298178818c71771ff86175b43b7175a4bb6174d06a41741fc57173717d9173492ae1716f07e17140bae else 0x1e98bd051e961a101e915c651e74578b1e6c7bb91e50c0081e249f821e07b2b21e07305f1e01d9a21e00492b1df3730d1de7e6431dd520631dcfea0d1db1afc21daa0e5e1da99c1d1da455611da2a6701d9e411d1d94fc7a1d945c101d8fd48a1d8646601d8618b61d84f2fc1d7c65651d5c840a1d5331431d5193bf1d422cf01d2d7e381d263a111d1918b71d16b9401d0c5f551cf08e631cc800771cb69c741ca152dc1c8425f31c79120e1c7765ba1c75f3c91c6b3fca1c6725151c4cf3fb1c36eb551c2aead11c2839231bfa6c2b1bf592c21bca8c1e1bbf41811b6ee8ef1b591bea1b4798cb1b391bc11b3689ba1b2cb2b01b1e60bf1b11cc4d1afdc4fd))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x239a6b37236c853c235de7d0235b2c7223511b842322f40f2317b1e4230fe15522fd45b922c6ad1322c5e60522abdcd722aad42022a80a602290263a227de194227420c322705f89226da79c224479cb2239de9f22201d3b221712012216d62a220cdb60220263d8220196b921f5f7de21f28bb721c8d5da21c193c921adb4c721777995217686c0216af41a214882002140384a2126408121131a9e210d6246210d2888210cc474210834b320ff335420d668d120ca1be320c31abb2084ffd3207358512066995d2065bf48204d69ac2036336a201fc57c1ffed6bc1fb1f4aa1fad23511fa199bb1f6c059f1f52bfe71f485bdc1f164c591f01210a1ecb1370 else 0x26c5f7d426b74f7b26ad544226a5b423269b0bdd269091fd26886da9266c28d72648ae8f264818b026422051263a2dad263348d32631299c262c2a4225ed166625cdb0ef25b6e526257f9cfb257a84ef25760ed62571d779256f2da4256ecbf32559cb092539eb7625290e872526008325211524251f6079251b6c572519226825147e3c250f9f06250b22692503dba62500b6f424f601ae24e9e0a024daaf5a24cc3b2524bd59002465e3e82465b06424340c6b242f384c242b1e7e242303b1242115852417036e2413f9f72413f1b3240eb112240a994b2403685a23f8ac8923f375ed23e8947a23e6c0af23de790723b9e87923aeb64b23a36f89239f629d) else (if page < 11 then 0x2bde16f62bd9459d2bc9c7372b8371f42b821b202b679ff62b5d54652b5875a42b5585c22b3b05002b3901b92b34d4252b2249a22b20509c2b1b1e982ae582c32ac81ae32ac3db862aba65f92ab0812a2a63d1a82a53b0e62a50d8c32a4e63ee2a4c81452a4b240c2a3d1b112a3c33b12a15c4de29eefbbe29d1dc7529c44e5829bec79a29b5b14329b5356629afe24129a6bb50299a43d62987c2f4293cb9ec2921a482291dc31e290c4a5029067e1e2901e7a528e1e3c628cec95e28c60026288cfa092889255a28577e95284cd3412812a0072800c77a27d12ed427c0604527bdab8b27755b2f273fdf64273d943d2723eafd27126dd2270aee5926e0df57 else 0x2f27ab852f04cbdc2efc3d8a2ef7dd392ef2f0202ed805a52ebfc6b32ebc48862eaa79172e81c7922e7934a62e6732392e63b7502e5f30c62e50c81c2e3e43642e2e86242e1a90b52e1736a62e05a8382e037a2e2dfa55742df8618a2dd8ce082dccd3302dc860e02dc395872db2e2342da80d7e2da39f042d9218052d803d432d717c432d70ca022d653e562d59ecc82d52ebd92d524d552d3e97662d19f6f72d107eff2d0c03372d06adae2d0057262cf968782cc40a912cc1fd7b2cc1b50e2cc18ed82cb6a3eb2c9add582c95d6dc2c892b152c80f6da2c773ddc2c591d8e2c3efda22c391ba02c32e2892c2f10cb2c2d53172c2420312bfde8142bf9f8f0)) else (if page < 14 then (if page < 13 then 0x3334566b3328901c3313401b330b56e633030d3332e371c732d61ed632d3d73532b9aada32a707af329994413295578a3291b70332659f3f3255f61c3210275831e5557231e191db31dfbce531c1433e31af992431ae308f31ab50de31a3b67d318c9706318a039f315d2f153158025c314f390f313ecab6313bc152312fee1e3123509a3115edf8310513ab30ede0f130e3370930dcc7f730c82cbb30c2a7e230bd2f8c30835264307d8629307c15eb307b69f8307ae7a530732f8d30694ff430363e8e302cd623302567083024c7bd301d27813016992230117aa3300344bd2ff01cab2fe5375d2fd6e0d22fc7c3002f9f5a252f8765002f37fe052f2c30da else 0x3801434037f11ae737e58ebf37b84878379eb68c3792eefa3792cdef376e953d376d487e376b15e0374ee47a374b4e89374aabe33741412f37274eb4371ec41e36ee4bb136d1508636b615a336ab055536a7674c368b737a3648044d364386a336385af236191ecc361726cf360f8f5e35f6d4f935f5907435cba46a35c4d95735ad205c35a39176356f099235670866354ac2e23546c6c93541dcd0353d3bb03515a7a43512bc433508001e3501cf9f34ff10ef34e6bc8434d05dc034a5234b349bdec3349943fa3469af2434527feb344adbfc3414867a3406051933d3deb433d3945133d0af4833bf6c333395cfca33911b04337c222a336b9510335dacf2) else (if page < 15 then 0x3c5973fe3c3bbb363c33cc1c3c2c210e3c2399873c218f503bfa8b853bd20da53bbcf80a3bb7acb43b942f033b8becc53b8243b53b62f3b63b6267d93b5797a03b16caec3b0e5ec13b0bc30f3b0a66bd3af6d25b3af1a2233ad65cbe3ad49cf33acb54313acb23d63acb15533a91120c3a71cded3a6aec923a3bdf023a2e52a53a28fac23a113ab43a080fc83a06228b39e7906d39dcd09839d3210239cd2ac239a9850a3986e7553976085639677e4339601538391dafb639196b693910fe5a390d11b4390b54f638d218ad38c2e72138bfa3ce38bd420938acd87138a577ac388d5b2f388c22723883351b387aa40a387800e0386cd39e384958b23813de73 else 0x3f8080843f803cd73f6e33db3f67d21d3f65fe6e3f53ef503f36ebd23f301eed3f2f0ebf3f17b1d23f166c8a3f09792d3efe71c63eecfbde3eebc8d23ecb82b83ec593bf3ec2ceb03eb78d913eb73e503ea44c4a3ea222a53ea1356e3e880f523e6203383e5e19143e5840a23e57953b3e56abde3e3cf8bf3e2709b43e24fd093e0546043e03414a3e0048533df110893de0ca1d3dd163733dcc2cea3dc884de3db7032e3d85b9473d67e39f3d5db0493d59a7ba3d3bd2293d2438703d1b87853d193ff73d10d8f33cf9653e3cebbc443ce5a91c3cdf34023cde4b093cbedb523cb6368f3cb37c6b3cb3254c3ca7e6d23c8c79653c897c243c8317013c715f89)))) else (if page < 24 then (if page < 20 then (if page < 18 then (if page < 17 then 0x42efcd3142e1b8e642dfded842c732b842aab3974295b5c0428b3535427b5296427b3225425ace1342403a91423e19d44234fc3d422dbb2842261df3421e36b9421c75b1421478c742068d454201df1c41ef76be41ee15bf41c5756b41bb71e641ae313c41a7f7344195be07417b1521416a1871416944fe4155ecdf4151c364412e32db412bbe3241277648411ceb9b4119708840c42d2f40acc3ba40a1b33040a027d3408caeaf40822b7340795f7e40668fad4051869c40195d9c40160a3d3ff748fa3fee151e3fe978613fe957563fdcb8273fd8d4243fd67ec23fd4815f3fc9fb1f3fc71e913fb245853fae30c93fab243e3fa166033f929c8e3f87e748 else 0x46f92cb946e4b0ff46d453dc46d3225c46d22e5746be977446b04ef44699ecbe4674c461466ae56a46689ad8465c8aa0465b6b364656ca754644b6d846425bde463f26ef462c544a460c24a84608411345fc204845f8384f45f3de4045f3d5ec45ed850c45db741c45d5a75645cb28ef45c69e62459540294581abc4455ef2474557e8a74506285444e677b444db3f4e44d1cc7a44b3854144ac6da74498f5ea44744b81446676b44461f53c445881974443d4c4443af6da4423506a4420edf24417b97b440bcc2f4405e74543f04dec43d9376543bda9734392b669439146524374b78a4373276f4356e4e4434648af433c391d432f66e5430fa20b42f58e6d) else (if page < 19 then 0x4bda93a24bd672454bad7d784b85f04c4b84b5a04b76e8194b6748bf4b5da7d64b5712704b4bfae74b47de094b369e674b30f94f4b0d8e0d4b00e79a4abd0ff84ab1577a4aacfc6f4a9190834a7cf85d4a6c6bc24a64a0d14a5143d84a4bef504a43c1234a3c26c74a39071e4a06a64049f7c91249d8a60a49b0737b49a71466498c22ee498626dd497580e0496d262d4968739c49443400494298c4492e2bba492d77e849170d0b48d342da48b2511f488f68114879207d4868159e4859ecbc481216694801502847f9938a47f548dd47f5086b47f4ba9347f2286647f08e2647e4179247ca467647aa94a0477506984748961f47448e92473c402b4718da91 else 0x4f8da80b4f7200a34f6780034f5cf5284f5212944f1ba1e14f1a2ca24f1197cf4eeabcb04ee3aa284ee1122d4edd9eb34ed7d3014eb3e0c34ea9aafa4e9d7f464e9973ea4e75286d4e6cd7fc4e6aa6c24e5c13004e397b0b4e2dc4ca4e22b5d04dd2c6504dad989b4da82f914da127e14d6af4c84d6559694d60434f4d5f86da4d5f10454d5b21e34d5a14384d5816a54d574ab64d40d3174d38c0ff4d3247bb4d2c1cc54d27d2224d122cb44d0a79ca4d04c9524cf838254cf5b8744ced13284ce4894f4cd698644ccad4e84cbf60514ca943414ca7ced74ca209eb4c9180414c744cb34c6255964c5b47b34c2fde024c1ed7884c181daf4bfd034b4beafbc3)) else (if page < 22 then (if page < 21 then 0x5313df195311a09453026f9152db397352c4d7f652b3b9c752a47b145298c42f52978f60527ffb77526d2d41525ca3f052597e2752433bcf523b316852297081521edb845209f33f51f77b8351efd20e51e0fd5751aeaa9951aaa318519c0df55197d8925195c7bc518b6918518ae52d5189e6c9517bc0245179c346514cf7b6514b398b511803905115d9eb51077d9e50fad79250f97a4750dfa78d50d6b61650cc78d750c53ebe50c5183750c3a69150b4cf525082a068505eec4a5055a107505481635052fbc25052890b505079bf503c3c24502fce7e5028c902501b2a415017327150110c1f4feeda914fbd7d204fb2f9254fa385a04fa124864f967f95 else 0x56f2e3fb56e802c756e266bc56d9b23956cdfac756bdb2cf56aeae205692aa4e568c3cba5684ebf85682d4e3567f837556672eb5560fcbb555ec69fb55dc2f5255da0a1055d0440d55cde01555ac30a055a31e2b5590c9d5558b48ae55888bb35582a04f557995c055596f9c5550e205553eee47553b0fc15536feab5532c4e755096d065504cbf654f3f8f754ce855954896abf546dede054550a215451f2bf544c457c544ba23954420f1e543a332d543990c8542879f85420686a541e4ab2541bbbff5409754d53fb7d7653e8a24153cc43d953cb32d453c400d053bf0378536bc3c0535fa467535968a85347eb855343fa075333f7df531d9662531b4814) else (if page < 23 then 0x5af74cad5aee18c75aecd7c35ae8b9895add194f5ad50b995ad00c515acf15985acee7975acda4025ac9a1925aac2ab35a9fea445a9fa0b95a9d0d0a5a5e63165a57ff205a3246b95a2e221e5a23888d59e9f35259d9bae759ce66af59c6896b59aff7715986fd4a597fa4d659586845595867db5941515459286389591854aa590ead5f5907206a5901a2765901335f58d024af58cf338d58cbc3b858b8255658a7032658a2596d589625005876a2135869b40558506679584f2b6258470d215846fd625822dc2258215dd95809685557f817b257c800b357c4a276579c29ad579b3d3d5787737e5780c5635760e19b57542acb575240d8573a064b56f4d0b8 else 0x5f49b8ae5f3956df5f1ae75d5f0c18fc5f0471ff5efd7d3b5ef0fa425ee51fa05ed5a8ae5ece603c5ec88bc95ec24cc05e97a4785e928ece5e8bdfe95e7863eb5e70ba915e60295e5e17ae075e059f6c5df31d295dee05295de561db5de245fe5dd7bf855dc2857e5da743125d963bb65d74ccf05d6d511a5d5ea1515d4dfe865d2f154b5d173e215d1326fb5d0acaa75cf254c65cf14f9a5caef90a5c9949f55c91d5a05c8071b45c7c0c085c77ae245c75726a5c4b84905c34ce535c3449255c2102755bf5ae385be595865bce2e6e5bba5d5b5baf6f345ba848525ba573555b819da05b7667705b508c5d5b4f9efc5b326edb5b2c4df15b26faf75af770af))) else (if page < 28 then (if page < 26 then (if page < 25 then 0x6404853d63fa6ed963e91bb563defabb63da733563da09b063d08eab63a704e1639aebdb638f8230638c4f94636e497e636bc13063682e10635a6c3863526ac56338cf7d632001366311496962eb2f0c62d0617f62c4310562bcdcfe62ad9137628f5be662729ab46264b5b9625c576d62470d67623cda2b622f82d1621fa0ac621c19996208519e61f50aaa61ea417e61d347bc61d1f4f561c5c9da61bac31461b4c8d761b488b961a3ebeb615155f9614b8a476135b28a610a735b60fb1c7860b3179c609e47d060949f23604fd151604cf71a603d77f760247d4a5fff3a5b5ffd9b3b5fd809945fd3fa955fd024c35fb19baf5fa736125f6e107d5f5d306b else 0x680dfb476804811b67ff33b467f6579567e992f867da312467d307eb67ce291e678af74767639b0a673498f16726f8f56705febe66feb3da66f5c3df66f2ff1c66e4629c66cbe17f66c5fdd866bde6e666b5009f66a7776366943390668f7345667e97ce666a9fee6668ca2566308dad662f7949661754fa65fbcbc165f0865565ef90db65ee45e465daa07965cdea39657c5d61656f4fea654bb3b66545c8436542a91665217e7b65104f8f650b46a66505827164fa637664e41b6664d408f064ca1ad164be2bcc64ad0c1264a76e0564a3b940649d893d6498a2ea648b6c45646f3116645389fc644844ff64477e96643cf4d5643c26ec640bebb8640b8fd8) else (if page < 27 then 0x6ceea62e6ce21ba06ca292066c8b81456c53c45f6c3f5ba36c33b4b86c1200f96c0dc2016bec589c6beac5546bcf16e66b8264a56b7681966b75dafb6b72e1206b59e3e06b3f7afe6b21d70e6b1d1c8f6b116a9a6b1066686b0d2e9b6afce1076aed57ad6ad7f2286acc86926acc80306abbfe376ab87f036a9ae8b46a4a3d8269db338169cb733869caef6669bd5f8669b8a82f6991e71b697230fa69716a57696e34f9696113016955a6af693b7eed692c14a86906619468fff40068e3d62d68df069668de97e068bdf7ec68a5230b689961bb68810d9b6875633f6866bd4c685eb7d86858f25568417230683f3dbf683cf631683ae7af6817ddc76815fe5e else 0x710f15e170f090c970ecf17570e2d59d70abeccc70a9123e70a87eb07099542270962a9a709378ae7084a546707f4d9a706d662f7068b37a70575815705435c1704e78eb7037177f701d97f06ffc53586fecd1496fde1e906fcf90e76fced7906fc7c5656fbad8896fb06ec06faae90f6fa9f5c26f9e16a96f995f796f93bd826f7535946f750e206f6380876f4601df6f33500c6efa7bb06edb81956eceba746eafe76c6ea1a4c36e9a68af6e4bc2f86e4319c66e32b7a06e211a0e6e1663ca6df0d3026ded89046dcff3d46dc5d9516dc443a36dbdc8e76da01bc46d9f77096d9ab23d6d6b7cd36d53b2bc6d2436866d2028126d1dc1296cf2e2dc6cf121e7)) else (if page < 30 then (if page < 29 then 0x7511fd6f7505ee1f74f3306a74e651fa74e2196374db973074b2163974aa4dc674a8f4d4749dce78748b847c74853e9f74822cd9747e3c7c747ddef6747d47e57479d5cf7443e43c742b909474066f3d73f9e25a73ed8d8873c6e75e739dd44373855d14737d3a4a736ed3be736bec2a73688449734d9b357344731d73375acc7333a61e731603d47301bd9672ffd69872fb986d72fb87c672dc1b2b72d8a4b672cbf3b972cb4efb72c8209772c388977296ab5c72551c21724e8ce37248d8a1721217f071de8e4171d4757571d1c56f71ce995f71b14d38718eb6fc718114347180919a715522697152ba5171525eed7141ab5b71360406712ed31b711e94bc else 0x79558c7e79370ec37932ca9979221089791b2ea97914204c7905fe4c78ee015078dbf16c78d20a1378b3c53378a3308f78932924788fc07d788ccfa9788ad9aa78858dad7883d5377846fe7a7836935e781615d977f1033e77ee400e77e8a0dd77e66e6e77e3073077dfc76177d5e69677c193f777b9010077a4638b77915bec7786c2257743bb03773dd2177728fa9b76f4671e76f16c8d76ec657176ebc77576e0fb9c76d5f56d76cdf63776bb35dc769b31337678c8ea76656766764445f176411d6a76095e2075f05d0475d0b2a975c6220b75c1746675bfbe4575b546bd75af128d75a65952759ad9317585ce5d754161237537c49c752a5c7a7521487d) else (if page < 31 then 0x7d181a4e7d12edc17d089fa07d0169dd7cf5cc577ce6ccee7c8a77e77c5fa3c27c480d647c0a617a7c0649c77bf1efb07be673d57bdb6adb7bdad0387bcbda457b9fcbee7b708e707b6447e77b578d737b565fd37b489f107b43c3c37b3efe127b3b06597b3027107b2e27027b2a22137b07bbd17af4c4e17ae15cc67ad6cde27ad528a37abb8c2a7ab2f5057a9b78fb7a86a5547a8088277a77842c7a72eafa7a6a32607a5d4a3e7a55d0997a3075b67a1a96317a195bbc7a18e9767a18b0a479fb201279f67b1179e093c479d866cf79d672e979c7977779c39f3b79a8e90879a47c23799c10657986691f79734d2679697b257968f73a796647557956b2f8 else 0x81bb916881b4eff881ad8d1f81ab446f818fec38818c1a64818301478175b8e7816e32f6815282b681447b5581418e42812d0394811843678105303a80f8bb0a80e5db0680d99e3c80d331818095174e808e1ae58061809c80545187800cbfa6800c00738004ccea7fe7e5537fc9274b7fc8807f7fb7fa0c7fa547707f7c22637f6c53097f6719de7f55a8c37f2c6fcf7f2c38047eff388b7ef771477ee7b70a7ee325d37ee27f387ed333817eb98a6e7e9c4b9f7e5cd08a7e55c3877e4a8cee7e33e3a47e140c9d7dfff1437df7bd817deb3f207ddd6f847dc377867daff0bc7da07df67d80e5e17d7aa4b77d6894287d4d26bb7d44b1b97d380cd17d32a4e0))))) else (if page < 48 then (if page < 40 then (if page < 36 then (if page < 34 then (if page < 33 then 0x87449023873cf0b18725cd7f871feb1e871e77f58717622386ef560986e2e60386c9441c86b05dc386a1aa44869654ac868901bb864dbeba8646996e8633d99d861ac0448618faa785f0050085e9b39185d299d2859e11ee858646e28579db668574a985856ac597852ff377850ae54184dc803f84c41ea7849619ee846beb97844147b38427f60c84271df284223178840f158c840b52c983eaee8883e50cf683b77d6a83b2824a83a63dbd837b48c483677efd833e6d4c83349674832fafdd82ddcc7282d1ca9182bfffb582a8709482a5720682697c468265503b8258557b825749df8243482d821a151e82169a3581f5654781ebca2881e1690981c3c694 else 0x8c931c7c8c7451268c6a32578c61dc308c498ac98bc9a59e8bb53d5d8bb42f7c8b9f76468b95c7cf8b63747c8b5695e78b3ade6d8b3947fa8b30a9078b1cef5d8afe316e8ae5eb288ae38de68ab43db18a96991a8a8415fb8a344b358a1d68478a05133289ed41b189e622c889dc130889dc116089dbe4fd89d911f789cb268089c69a3989b1b44c898d66c2896c51358962cc15895c4872895bb9a18943044889276fd4891dd00688f4bfb588ec803088b23d77889bdbfa8896a545886289da884ec1a88833758b8828fe038827dc62881f4e308816dc7e8805495d87f1438487d1230487b477d88784e97d877a381f87652c7187647433874c737f87467d43) else (if page < 35 then 0x8fdc4b6e8fdc0b1b8fd206af8fc3c59c8fc2c0338fc0de018fbaf0938fabc4178f8de0858f729d008f6a01c78f442d4a8f35e23d8f23603b8f1c6f978f0cfaf48f0a7a858ee837d78ee6d78e8eda6fa68ecd05c78eb918768ea9b5408e98b8ec8e9805168e8c508e8e8af86c8e7e18c08e77a99c8e63ce2d8e4409868e2ce2c78e1c04d38e194c858deec1e78de445b68dc29de28db552f08db1d02d8db0ab268da761c18da1db338d8c702a8d8451d58d800da78d78e35b8d5e19698d5cee048d587b818d4d35238d4a85288d32c5008d2731878d12f81d8cff1bb58cf9bbe88cdfe6858cdde9a68cdbae268cd8e18f8cd8d8c88cc807748ca8c4798c9c3a7a else 0x941e2d8d94120b3a9403d22c93fcf7b993d1cda493ced99f93c7fe279378e7809365286a93413c16932f0235932508fd931bf559930ac71892ee133792dfcdb492d8417e92cb18f1929963a1927fb7b9926c3d0f926b668892519a729240a535923c0325923653b49223936f920a7820920687cf92029ebe91fe081391d8179591b6ce3791b4075891a31737919f93b29177dc6a916fb3339163067e915b6e509154f219914b491c91483d399146eac7913126b29125ea959122bfdc9102d5d190f98b7c90e7ba9e90e329ff90e12a5890665f5090535862904dcbcc9035f9e6902fbef7901e501090054c99900504dd8ffe1a3f8ff982fe8ff2c7b58fdffa69)) else (if page < 38 then (if page < 37 then 0x982311eb981cde06981c7b429819bac29814d8219810c83a97f3578e97e78c4597cd304b97c552ff97adbd5997a33e2497a330d197a29506979e7eda979808d9978c1a4a9775f51a976f89d9975f262d9745994e970fb6e29709d1349708c6b596f150ed96c7103c96c284f096bbdba39693dadd965de4fe964cf59296470f81961f5f29961c8d689605a52c95f31d7695ee47ef95d0020195b3776b95ac43f995abed7295a49b93956033e8955ada19954553309536ea34951633d594e3753d94e115c094dff57394db760394c7fe4694ad4262949279c3949143ac948a517b947095fd9460c7af945d48189455204f944b3ce8942a95259425c3cc941efbb5 else 0x9be7f0909bdc85d49bdc811e9baf741c9ba50b4b9ba473069b8e11899b7f4d8b9b7d295b9b6876fb9b4dc28d9b4b5f1b9b3d5eed9b36e19d9b36aaee9b140f039b0f67cc9b0dd4c89b02c3cc9acbdb879ac261099ac1f4d49abaa6ce9aae11179aac0f9e9a98c2649a9273aa9a8e44669a8c48789a8736c19a6da3849a6101879a55bf9e9a4f0feb9a48fc849a4717549a0c0c639a04823099fededc99eef7a599eb3f5499cdfd8099c2083e99ab83ae99a3ff619995602199922f3b998207289938308c992de59899239719990a0bf298fcb90198f4092498ebb0a998c4cf6198b59d4798b190799894b932986352a298608932985d6ad79840d1039825c153) else (if page < 39 then 0xa0e52aa0a0e49c61a0deffaaa0d578b1a0be1d96a0a0206ea08e2511a06bd0c8a06748baa062792da0605adba05ab1bca05a5605a04853a5a03571d19ff3c4ed9fe5b0f29fc898b59f9ec1dc9f86af639f84200f9f6bf5749f6b9c889f6ad9579f4934fe9f2a5dde9f0dd3669f0abf4a9ec9e3249eb3ca7f9e70c5509e6bff7b9e60bb3e9e42d8a39e2ec10a9e1f4ea79e02c73c9df2fea79defcf019de3718f9de284249dcca6fc9daefe7d9daaabf79da52d229d9d39119d982c449d8784859d71e8b49d59f74b9d3b89349d22c4089d0f4c4b9d05d0c99cf57ba99cc2d51d9cb3ccb89c9aed7b9c6534049c4fde6b9c424af69c40aefc9c3bb3189c0c29dd else 0xa583a96ea550e2eba546bf5ea53dc812a53647fba4fd18fda4cb76baa4b8116ca498d45da4987c7da4907ea5a48cad74a47e2f66a47a55c6a4768976a467b237a45ffde5a45bf673a4425422a3f780fca3e30907a3e0e459a3d4d51ca3ce0d26a3a032f5a37e0f7fa365dc0aa3566885a3319ad7a32a3573a321d785a315a871a2e628f8a2da1696a2d9572ca2c0ad97a2b54f12a2a9b12ca296d43fa293f512a25224b4a24cd0afa24c56cfa245810ca231a5dda21f94e8a1dd6327a1c4c9baa1b46779a1a6bb61a195ed6aa18ca3dfa18ad976a16234a3a15bef1da1540ac6a14d396ea12a5475a11d6c86a116f2c5a114d4aba107235ea0f42093a0f3b5fc))) else (if page < 44 then (if page < 42 then (if page < 41 then 0xa8b82fc5a8b7aedba8b6a49da8b13b23a8a39889a86a3c6aa866d4bca866b844a831ab77a81ffb3fa81bef2ea813083da7f2130aa7ddc85da7d12d97a7d07295a7cfc888a7ce915fa7cdab92a7ba33d5a795ab80a7908303a77f26bea77e9370a771e65da754cd06a752ed15a73a4b5aa7058350a6f96b05a6f0ab31a6ee9cfca6e559cda6dc86c5a6ca2ba8a6c55b8da6c48379a6aa9d1fa6a5c516a69f20ffa68a9d81a68534b9a6850694a6823e0da6726656a66dc32ba660bab2a6429ed2a62db920a61f215fa611fc34a611f520a60c610ca6073236a5fd1387a5e6c9faa5df6a21a5d8dfb0a5d501aca5cc7687a5a8dea9a5a3403ca5a28ee9a58d4181 else 0xac1dc24fac0f8a51ac081ab6ac05b4ddac03d241ac022995abf9f006abe7b3b4abe31e42abdd732aabacf671ab97c9d6ab90119bab8e30fbab77855bab73faceab6f5cd7ab67cc4bab5fbec1ab35a0bdab2f4244ab21576eab0413f5aaff40f8aafbb372aad709e8aad42281aacf4869aab7888eaa997899aa888f67aa871d18aa724385aa711637aa5ae357aa357433aa343459aa186e38aa16e817aa07fc4aaa00753fa9ffd190a9f72d71a9ed0bc7a9e1af61a9c74e70a9b95094a9910877a98dddbba98326f2a967ab80a940d816a93e2b93a93bb407a93b6e98a9363c36a92f92e9a927ea85a923b5e7a91c538ba90ec2f7a90aaa22a8fe13e4a8ca425f) else (if page < 43 then 0xb044c4ecb01e633dafcdae91afbc1af6afbadc97afb85e73afb26de9af9c54caaf6d2077af6954a5af6932efaf625219af59d5faaf34cb1daf17a434aef05970aecbac46aeb62406aeb6023caea4891bae9efefeae956877ae8d0c64ae7b3148ae6a6097ae6549d6ae63287eae5e327eae3aad1cae30e159ae18c291adf50debadd1a247adc54412adbf45abadb39032adb107bfad943ae5ad8ccb8aad700507ad58ee80ad4bf7e9ad40628aad3287bbad2aa5d0ad1fc6e4ad1ae368ad166967acfaee07acdb2474acbd3f67acba034fac916ed2ac8d7453ac891523ac682602ac553c52ac54d98eac3a6422ac390184ac3650d4ac346f4fac300fe2ac2a453e else 0xb3959223b36e9403b3676d42b358e1e6b34c840cb34b05a8b33f7ce2b326575bb30b19cdb30985f7b2eee043b2eb6c0db2e09ba5b2dfa30cb2dc740cb2d78aacb2d7558eb2d13224b2ce6902b2adb64bb2a70d8db2980285b28e66b4b28c79e9b2716249b25b00ccb24a875db23b6a8db23670ffb22b46d0b217d2ccb216e0f2b2130c43b20c3942b20602a9b1e50197b1d9b059b1c079a6b1bad440b1ad402bb1a0b50eb19cc10bb1986698b184d86db17b5246b17a3f4eb1693180b167bb3ab1416a22b13ffaf0b12b08a5b12781c5b0f30cb1b0db6ee7b0b667f0b09305edb08c2031b08834deb083ce4eb07a938cb0655878b0604fafb05f321ab05da984)) else (if page < 46 then (if page < 45 then 0xb7d955c3b7b17f58b7acf347b7426515b7356e84b7300ceab70d4f1db704dc80b6e2e496b6db697db6d2e41bb6cdf2b6b6c08a32b685fad0b66fbfe3b66581bab65277e3b641c46cb6103e7eb60d76c5b60c9217b6079126b6050b5fb5f3836bb5dc61ceb5d99350b5a7ed8fb593cdcdb58fa6a3b58f0927b58ed465b58325f5b575e698b57323cdb56fbf3eb55b901bb556ced0b53d10c8b51a6561b507ac58b5061885b4fcfbd4b4f806e9b4e9d877b4e47627b4afa1a0b4ab0699b4a98e7ab46c2c5cb456e334b4511a6db43c8c7ab4290b7db42004ebb41731b5b4165defb3ef83e2b3e8e238b3e65622b3d502c7b3ce0ec2b3a80749b39e0bbbb39d433c else 0xbbae3dedbba8d45ebba593aabba23ff7bb976d2dbb6eb201bb69b5f4bb5d7169bb3051d9bb2b6621bb167defbb13c2adbafab202baf9fb1fbae77bd6bae6176dbade3f12bac4332bbab31648bab196bfbaabce4bba9c2ebaba821a63ba8128ebba8087a9ba67e384ba539559ba4b0eaeba471675ba44e4ddba2c6170ba26cf81b9f92b51b9f1dbfcb9e59da3b9b826a3b9aeaea6b9a1408ab9a128c9b98c02f2b970d56bb96a1b98b9648d43b94a82abb93bb06bb9383abfb92f46a5b92c25bcb9299ca9b924c941b90bced7b902cc16b8d46160b8c23f67b8915e8eb8801852b878848ab8569c25b8310341b823b01eb8227ca3b80b3c0db7fcce0db7e81d51) else (if page < 47 then 0xbfeea36abfdd5b80bfd9c9dbbfb2f89cbfadf8ddbfa63f01bf9da839bf81bc3ebf709b87bf46468ebf3cd7c3bf2dba95bf095612befccc69bef4d22cbed16f22bec08c12beb2a7bdbeaec941be9a9ad5be8c76dcbe872318be718b41be6da74cbe673979be55766cbe3a85dfbe37b89cbe308944be1ae2b8be0d7240bdf64984bdeb3ca1bdeaa76dbde9b9f7bdceec60bdc9e6d2bdbd9cd4bdb241ebbdaaa79bbd6aa2aebd5ef2afbd5d9307bd572af1bd54e820bd4db2a9bd3eba93bd22443fbd207057bcddc87cbcd9700bbcb1d5f7bc957c0abc897bedbc5ee441bc574769bc383f09bc1bad86bc13251dbc09493bbbf73723bbf6de38bbf2e7bebbaf25de else 0xc4b86f54c4b78727c49f225ac49efe16c49273f4c486c389c46ab7d2c467a496c4647313c44fe556c43d4661c43d377dc3fce08cc3fae0b4c3ef098cc3eb62b8c3e1684bc3c7c908c3b332d3c39c745fc3982d6fc392da7fc38cfd9fc3897f0bc36cab65c36128c9c346a067c3409d83c3161fc1c2f728f3c2e42e29c2c8bc89c2bea69fc2b7a8d6c2b78493c29f3a26c28f5323c2819d59c27d8f9cc26e1d86c25be738c24d8e08c2263916c1d6095fc1c995f6c1bef787c1ab1ffbc170abccc1454317c1032d47c0fce31fc0f18626c0e82f90c0e6b614c0b779a1c0b75ac9c09f5da9c086ba17c061d37ec023e306c0217e85c00caea8c00c66cbbff336cc)))) else (if page < 56 then (if page < 52 then (if page < 50 then (if page < 49 then 0xc8355b02c83281c7c8311f61c82fb243c82cb8b4c81ba4d5c817a939c8097d10c8073ce8c7f6c721c7e37684c7d861a9c7d79751c7d160b6c7ca8616c7a89731c7a63905c7a35e94c79a1e3ac793efbac78ebf82c782f59dc775f183c76c3016c761da5cc74ae218c72e7b27c72b435ac71af5c6c6ea3db1c6b2131bc6b1fb29c6aaee63c6aa90d6c6a25acdc69d7066c67ed69ec67e31e0c6608f68c65d6ba6c65883bcc63c03ddc62e1565c60e06e2c5e9d194c5e75f0cc5d6bceec5d3fd21c5c1d87ac5ac7636c59a0ea1c58e0bcfc583c79cc578b5afc553b7cac54105cbc52b1c08c51782ccc50be55fc50bb9cbc5021dfac5018c29c4f681dfc4e40425 else 0xcc0ba0cfcbe124d9cbde7e4ecbdcd3e4cbccae2bcb9d53efcb8b3ec6cb785486cb636974cb612f5dcb57713fcb574670cb4818a6cb39a50acb272c04cb18308bcb088e55caf69de8cade7980cad77a5ccad43c0fcab6edc7cab498e2cab34565ca98d181ca93de81ca80d91cca6d8e0dca6d871bca54cfcdca4e1418ca2ed9ddca023d43c9feccddc9f53742c9f1727cc9e30076c9e1792bc9cf98a9c9c98280c9bdd72cc9ba3033c9b4340ec9a9a125c9834d3ec9810663c963cffcc95caa72c9469b61c9337399c90da877c90859d0c8f51d19c8efe557c8e37729c8e31bf3c8df8307c8d1430ec8a9abb0c8a87006c8a4aca9c89a1116c88bd267c8570e4f) else (if page < 51 then 0xcf8db31dcf77ad71cf6096eacf5658fbcf41dccfcf3fb4e6cef9797bcef8f9f2cee94c80cee109e7ced60760ceb4ad4ccead630dcea41784ce97c5f3ce943fabce82695dce6cbb82ce4314f9ce3895eace336b0ccde2ae27cdddfb93cdd46f7ecdd128afcdcd3f2fcda87fc9cd8c2a5fcd8a3535cd8853d0cd819426cd7db56acd7b0e58cd75bb5ecd6e6948cd6db265cd5b331ccd575f08cd49a692cd27017acd26cd8ecd254e05cd192a3acd16b69dcd0b0634cce3f543ccdb9acaccbacdbbccbaa7f7ccb35151ccb1609acc983597cc89db3bcc84ecf8cc56e53acc5177d2cc460c09cc32d780cc235470cc2265eccc211bb9cc1eb0e9cc1e5b4bcc14e00f else 0xd4c97b94d49c96e4d498bdebd4814cc9d47b876ad4785e8bd4724aedd45b2fddd44b2c57d4402c16d43ad541d438ef2bd420d87bd41511dfd3f4feb8d3e46312d3c00440d39bf4dcd396d9e0d38bff1dd37b6364d378a1c7d34d274fd3139d20d3088ba8d2f6013bd2f2d13ed2d82fd3d2aa542cd2921174d284a609d26997b7d21adb89d1ee25a3d1ddd304d1bef494d1976835d1945020d16e323fd166eb89d1487139d13faaaad0f97f48d0f955cdd0cb5675d0c7c171d0c11e89d0b32cf4d0aef53dd083421bd06ea5ddd067407bd0642089d05ef73ed025f931d02561d6d0146befd01379b2cffbe279cffaf049cff08ca4cfba17a3cf9a9b3bcf9a3ae6)) else (if page < 54 then (if page < 53 then 0xd7b538eed7aa98ced7a592bfd79f2f63d78468e4d775436fd77289b5d76c1699d76376a6d748f079d73651b9d70f77d7d6fd9e45d6ee399cd6e816e3d6c5e650d6bc7159d6b139b7d6984127d6963efdd688471fd67ac3d2d662e1f9d65470bdd64d86e2d64531fcd641614ad640edced62f6babd61f4f12d61dce2bd6155f18d60a2cc4d5fcff5cd5e95e82d5e2b3c6d5e2a9a7d5db2494d5d5818dd5d1b63dd5bcfb0ed5b6ae02d59f74bad59732b0d5912443d5868b8fd573cb6dd56363acd55ca577d5325de5d531b4f4d52e73ebd5251ad1d5210a26d51220c9d5099b4fd50856a5d4f5549fd4f53446d4ef0402d4ec612fd4dfe679d4d5c033d4cf9e7e else 0xdb0bb292db09dec8db086f5ddb05cbc9daf5bcb9dae07373dab233c2daa06ffada9f662eda9eaab5da95c8e8da8d0adfda85b747da7f5bbeda70d062da6a7e67da673e0fda6453c1da5e2adeda5dd762da52c553da46a7c2da2dae04da195c91da064299d9f0bc1fd9e0b305d9ddeb3fd9d8ec79d9b43297d9a68fc5d9a3aa8cd986a8e7d9857cb7d977176bd9729c1ad96b3b7ad952a4d6d950f4d3d9467a64d93d39a0d932a543d931ab90d92cbe4bd8f28de4d8e47b34d8d122ecd8cb5433d8c8329cd8c820bfd89f228bd8947a43d88244bcd87e39b0d87099a8d869c0e8d866827fd85cd6b9d845a029d8333b5ad82e3c65d80903fdd7dab2bdd7da00d7) else (if page < 55 then 0xde9f07adde92494cde6476c1de4430ffde34aef4de0f35ccddfcb63fddfc7305ddd0af0fddcc4068ddcafdb6ddc632a5ddb8f742ddad5c50dda1f5e7dd9bb15cdd9905addd954530dd833643dd6a552edd5bef02dd5a5ce4dd5941e1dd530fb9dd3dd58add366fe0dd29e512dd28a62fdd1244b2dd09a2c5dd0795c7dcfe50ccdcf49062dcf181ccdcc1cb5edcbbb80fdca59260dc6afdd4dc65205cdc52d400dc4ebedfdc4baad4dc2de779dc260891dc244938dbeba9a8dbe28884dbcc377fdbc4c449dbc189d1dbbb6094dba3cfbddb9f8eeedb8cb936db8a40c8db8405e9db768521db5692dbdb51e8f7db48c24adb3a6141db37cc62db227d1bdb175718 else 0xe2601955e2591c87e20ffbd4e2016a63e1e852ebe1dfa85be1dc061ee1cee7b8e1c09f84e1b3f7bfe1b2bca2e1a55859e1a3b6ade1a0b15ae183fa75e18347b2e182f92ce154c12de118eba4e110fc4ee10e8991e1001808e0f24066e0eca92ee0e952c4e0e3c253e0d5b848e0a72252e0a303ade0a28cf8e05b0506e0189c2be00bedb7e00a961cdff64e11dff278e2dfe04633dfdb7e55dfcec6fddfcb164edfb7ddc5dfad986edf77b696df5ae5a3df4fe51edf4f4e2edf4662fddf436756df21aa5ddf205a98df0e8a75df06cc61df003285deff6fa1def9b41bdef8a43edef47d07dee738bedecfd242deca9c80debf7b5edebb7a90deb9c34fdea35f94))) else (if page < 60 then (if page < 58 then (if page < 57 then 0xe69493fee69280d2e655ec4ee645a911e63fd256e637e4bfe634ad88e62c60e0e62162fbe5ef691de5e96087e5e93699e5e70b25e5e506cde5b65bd0e5b161c9e58595c8e57ce130e57c42eee55e1b75e55a2ecfe53b8e80e5229618e51f4988e51a0590e510043ce50a5f24e5032b1de4d068dce4c20116e4b12a23e49675cde465026be460b602e434cc75e4176385e400aeb1e3f6e5f5e3e59a0fe3e03052e3e00c15e3d84ee1e3cb4652e3c46814e3c07b88e3bd80bfe3ae291ce3ac65e3e39a54eae38836d6e3881022e36c4676e36a7c4be34816e8e3476658e307c425e2c9d155e2c415d7e2b4696be29ee47fe29b9677e283b251e2837a02e26ea78f else 0xea2f3d2fea2de738ea28f034ea2705e1ea15a1f9e9ea71f4e9e640fbe9e01c53e9d2420ee9cf704de9cb487ae9a72763e9a60ac7e99e2266e99b4589e98991f0e97c1c9fe974e00ce973c105e9602a51e9551788e93e66fee92b6824e91478b3e90d5522e904669de8fd2a94e8f1405ee8ef34ebe8b89a72e88e58e8e88125f2e87de40ae87ae12be85d2449e85b6a14e85233f0e8442691e8329f02e82ab082e81bc207e813aa94e7dd780ae7d8a6b1e7bcafc8e7852c5be781bc84e77a0aece779ea7be7791ce1e76f8fb3e76eb519e7652e3ae7539dbfe73ebf3ee736ceb9e70c7531e700de56e6e63447e6e02ecee6d5cdf9e6be2d7de6b67763e69daf13) else (if page < 59 then 0xedf7bd2fedddeb35eddd058eedd7e08dedd6e768edd03276edab83a8ed911a78ed8d7424ed8b0e5eed791f7fed6d8615ed6bb36fed5bf4a4ed11fae4ed09802eeced44eeecd9f99aeccbdce4ecb64dc5ec9570d1ec921f5bec8e95c8ec632758ec4fb352ec449e50ec446615ec366526ec33bf80ec0cacabebf933fdebf84159ebe55de8ebdbe0ffebcd91c4ebcab294ebc4ac19ebb6ec92eba54c6ceba07591eb986937eb8408edeb801330eb728549eb6aeb81eb64ceedeb60a03eeb37ee61eb226cbeeb155e32eb028f33eaf16965eaef3fc0eae888bbead38dc0eabbdacbeabba99aeab565c1ea9cac96ea96eaaeea82e0a2ea810cb1ea656c2eea5692e9 else 0xf1d6ce0bf19f2fe9f190bb7df18f9951f18c06e6f18a1ad2f1850431f175a569f1581007f13909e3f1367771f1257b2bf100a25cf0ff2a7ff0f6c0c1f0e4e24ff0c1689cf0a6d5e4f098f4dff08c0fe7f08813f5f07bc5fcf079bd68f075b802f0649ea2f058e94af0462c70f03ed090f039e9ebf03807a8f0224e6af00cbcf3efde636defbd10f3efb8447cefb7167aef9be722ef92a303ef8f68b9ef860d43ef833d29ef829cb6ef7c8400ef759138ef339351ef21059bef1dc909ef002a9deee9c482eee2d2dbeed8d7a2eec27625eea7eb2eee9caeeeee98007eee902b70ee828403ee7bfb8dee712258ee6faf31ee443c83ee3fc000ee354117ee2280a4)) else (if page < 62 then (if page < 61 then 0xf5bc25e7f5bb1d9ef5b68e8df598e27df591eda0f57d44daf575de9ff5674a5ef55dd021f55a3729f5151788f5127d30f4dd5cdef4d7555df4c63d98f4a709d7f4a70378f4763004f4655a9cf45f3384f4376babf432ece0f41fe115f41eb3adf41bfe3ef413f49ff40498bbf3ef4784f3e726c3f3d6be89f3cebf4bf3c33fd2f3bdf1aff39a6471f39893d7f3895d46f386850df384b394f373cf4ef363ae0df342cd89f338b76af331ce1af321975ef2fc17e3f2f9dba6f2c1c12df2c075d9f2bbf876f29fdafdf2990b2bf286135ff275353df2637baaf2600722f254b735f24b8e09f23c6024f236bfaef23687fff231f492f2289137f21ee260f1e54577 else 0xfa4c5df7fa3d6366fa3375e0fa30f4cdfa28f557fa25493bfa0b73e3f9f573caf9e137c9f9d55d17f9d20444f9c4df19f9afb176f9ad606af9a21117f980c7f7f9780c0af9489308f926e317f9139068f901b0c0f90056def8f468a1f8e571b8f8c6fe4df8c61a63f8b2073ef8ae94a5f89eba1cf88cb34cf86bf4a3f8605fb5f85ceddff849959ff843618af81ff514f8147404f7cb5206f7be8968f7b465daf7964d5ef79300cef77b4951f772c8f3f72a20e0f72629fdf717bff7f7020842f6fe9d93f6efeb2ff6dd1858f6d4ba6af6b8c616f6a54b80f6a51eadf696ae0ef68b8d61f6882cb7f6838dbbf67465f7f66d2b85f6201d29f5e2ca2ff5bd9ba1) else (if page < 63 then 0xfecd9472feb818ecfeb6f6dafeb235abfeb223ddfeb209d1feacf8c6fe71b54ffe688270fe622f53fe556790fe53533efdf6accbfdf2bdc0fdebed2afde85718fde39ef4fda1c7b5fd66b82bfd652c2ffd5ab073fd2f60e0fd2cc4a8fd210e74fd201cc7fd123552fd04df86fd033f5ffcdca783fcbd8d07fcb625d3fcb5a2f4fcac0965fc9d96dafc45f954fc432793fc25ddf9fbfd4936fbde6c78fbc48b0ffb9f2faffb960945fb7e1966fb65ec5bfb317655fb2abbcefb2630f6fb24f01cfb21f069fb02102efaf8f943faee9871faea00cafad45ac2fad3ec6afad2ef23fac677f0fac288cffab7ddd7faaef56afaa17fe1fa942b01fa512f50fa4e213f else 0xfff18af7ffe73339ffd1c2feffcece0effc8e4e1ffbc242effa3c4bdff960127ff9508a0ff935f30ff7f1304ff5a29b0ff477450ff0b0ab7ff012703fee4ac7bfee0b112fedf8233)))))) else 0
  | 6 => if page < 16 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0xdd9b2660dcac0c70dac0e360d58d6ba0d48d9da0d1992e00cdf08a10c574dc70c49a77e0c1f06dc0be6ad4c0b6bd6290b5767a10b4740e30aaa72710a09a99b0a055ac809cb538d09b0c1f4099d4df20905303708b8fb6a0835c8bd07ef6f5f07dd9f3c07db01a4079d60ee078dda4d073e6354071ababe06fde88d069285f106698b9105dc36c6056fcf2905602310054b497d0537bb520518e0d30468f121045044940436b133040aa0f303eb5d6403e638ca03a1aa290380dd1a03724785036dbf7c0300d75102eb17bf02e8754b02d7a00202a874650299f337028eb39d02440ee701d5086a01611c9a00fedace009ba4170091b52000670b360001be8b else 0x1d7c65651d78d4ab1d6f241d1cde98c11cc5a3f81cb838941c8425f31bd4e5ce1b591bea1b10e02a1b0a8fc31afdc4fd1aefa4641a76ad781a50534b1a34384918983123183cc66017f01a6217d3da5617c0c13917bf00c3175a4bb61759e11f174b55c317140bae16c902a616aa0bd8162630ea15d91bfb15646ec2154d192a148579ca147db1b014399cfc1414b66313ebde3d13e8816c13e549e113d4616a13bf918d1387dabd135ba6cc12bd13e312a8761912a7b511127c9664125c215c12228d5c11c0552511097f5610ed61e410cb77c71098b2c3101dabc6100eb5d30fda853d0fa7c4780f03c24f0ebb7f380e7b03440e4266000e095bf40e0366a9) else (if page < 3 then 0x2ac81ae32ab0812a2a53d2a42a4e63ee2a4b240c2a4009222a3d71272a15c4de29b1e1b329afe241299a43d629844ba22970a1a828d839d928793766286a06472860023927742eff273bc77827362f3b26c571ea26a5b42326886da92682fe88264c07b12649de0c25ec024c259ee7012588858425846ede24e86e3924c7ea5324bdcc8e24bd59002484af532421158523a36f892398b2de23202e7222afbf0722995d8a22558bb32250ac7d224c2e362241082a21f5f7de218f4bd421864ce021777995216883a2213c977620de0abe20bafb641f2ca36a1f21c9521f164c591ecb13701ea2a7a91e915c651e07b2b21db1afc21da5dbfc1d8739031d84f2fc else 0x3aca6f773ac149093a3207a839e7906d39dcd09839cd2ac239be34cf39a5bf9e39779f4b3946b68e3910fe5a38c2e72138bd4209384eea69384958b237e58ebf37be22953792eefa36f858d636d2fd13369bbb9736855a1a367d0b3036699373362b469136274af535ce85d8351b552534cc642334a5234b339f3ab2336040f03350a78732b9aada32ae9fd23296654531c81f8d31b4a7d031af9924318a039f317ca9123105370b30ede25030ad4198309007333014d9c92ef7dd392ed8f7932ec57fd62e63b7502e3e43642e2449392e0ec0b82e05a8382dcc5b2f2dc860e02dba1fef2d524d552c3e32992b8ee5642b679ff62b5875a42b34d4252b25de32)) else (if page < 6 then (if page < 5 then 0x4a6c6bc24a5d75cf4a38a1734a161d8449b85e27494298c4488f68114880721e4879207d4859ecbc47c2c5a247aa94a0473c402b46e4b0ff46d453dc466dc6d845ba962545930d7e455731814490c3274487ca0744744b814461f53c4452ff494408dd4943ff81f043ef623842c4f42342b17c664295b5c0425c3121425ace13423e19d442227e3f418d2350412e32db411f3ce8410272fa40eaca2b40b43f3b40a027d340737f1f406350523fce96503fb245853fb01f9f3fab243e3f36ebd23f17b1d23ea222a53e5960ef3df50b6a3de4be3f3dc884de3d2f8df13cdd73993c7c5d3e3c53bfd53c35de883b99d6f13b5fb6333b006fe83af6d25b3af1a223 else 0x5cf274975ce8795e5cd217e15c59d1a05baec2325b8b57725b5090375b508c5d5b26faf75a8128bd59e8c0ee59ae53c1590e73a85907206a59010b2158c4a379583d88f4581ef25357b7e41b57a46c5e5707033d568c3cba55e1ffd75590c9d55582a04f5580e0ec554e60fa55096d06548ec7aa54444f44541bbbff53ef881e532020a452cb4b7f52b4ea0252978f605287b8d5524d1e8b51f2c20f519df7855118039050c5183750548163505079bf4f939c314f66d93f4ed7d3014e3a0e0a4dd734b04d6559694d60434f4d32b31e4d3247bb4ca5a9224c5b47b34b8eab8f4b79f6ea4b784a124b710cb44b1737834afa262c4aec16724ad16d1a4ab1ed9c) else (if page < 7 then 0x6c1200f96bf6f0606bbc76246b75dafb6b3f7afe6a88266069be559c69b93e6669624306693a5d8a692c14a86911b1ea68fe3a2d68e3d62d68810d9b683f3dbf67e992f867be3b2a67639b0a66f5c3df66e29af866a5d3ee66943390668f7271662f794965fbcbc1656f4fea65580aaa650452c364f4e22264ca1ad16498be20648ec91e64477e9663d08eab63bf61a4635a6c3863526ac563271e476326f9d562b1c56d62ad913762729ab4622daf556225a31662152ac961e25df3615155f96149f62460fb1c78604fd1515f57e0cd5f3e875b5f12e2a05efd7d3b5ef4840b5ee10c4e5ed9717d5ed10a585ec24cc05e8452985e60295e5db4eb1e5d1c834f else 0x80322f18800c00737fd2f5057fbc93887fa872b47ee7b70a7ed333817e70a3ff7e2d4d827d80e5e17d6894287d4d26bb7d3ccb757ccb20f47c9f32a47c88d1277c0a617a7b817c057b0ce3d17ad6cde27a6a326079d3ea9f7922108978a3308f7859551677e3073077de521a77c193f777915bec769b31337678c8ea76766051764445f17601275975eaa36075bfbe4575b546bd75967d4e753e2a8b752a5c7a7527c90e74e2196374b21639747d47e57479d5cf7443e43c73c65f47737f70e5736089c1732a83eb7328828f72cf0c7a72bb94bd7229ff0271e95b96714aa6e970a1b22a6ffa80ec6fe4aa266f1b1c2f6eab9e1e6dbbe8c16cf44e376c800ead))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x8fc0de018fb622878f871b518f786ee48f6d78958f5a13d38ea9b5408e7764c58e40548d8df49ea38deec1e78d847e178d313de58d12f81d8cbddd968c92fe928bfc2d918be8b5d48bd522128bcf7c658bb8da898b9494b88afe316e8af417518a25bcb089e622c888f4bfb588e0546b88c86b3088b4f37388b23d77889bdbfa888ce607881d73e387de12ef87d642b586fe4099869654ac868901bb85e37c1285dd6b8b85cea27f85c70a0e85818a7d8569ed728502a72e84eeeaf5849d3710849619ee842b68c8840067da83ea065d83258fa283215712824ac4ff822ef22882169a3581fb7ff981e16909816763178153eb5a8105303a80ccb59f808c3820 else 0xa1566a0da0f42093a0f3b5fca05ab1bc9ff3c4ed9f99a55b9f6b90209f4934fe9f1662639eb3ca7f9daaabf79d59f74b9d4fa8f69d077ef59ccc50fb9c7463129c73590c9c4de5209c424af69bd8029c9ba50b4b9b61ef119aac0f9e9a975f619a665aaa9a51312699cdfd8099bac7aa997741b29974af3f994475e19907b3e898dae78598d96d74981765589814d82197a9e59297a330d19745994e96c284f09669ec8c95f31d76955ada1995283d5e94e115c094db760394c7fe46949b62ac94980f65948a517b941e2ba89365286a93362a2b92ccfabc9230b741920a78209206a41791f32c5a9163f020915b6e5090665f509035f9e69029a066901628a9) else (if page < 11 then 0xb05d1465b04dbb90afb93b8aafb28b0baf693feeaf6932efaf625219af3dd497aeb6023cadcdd77dadc54412adc1e741ad3287bbad0a5550acfaee07ace60aabacba034facad6b99ac7a17f4abf9f006aba828c2ab9d087daaf07226aa888f67aa8714faaa7725fdaa6bbd36aa1b2d56a98326f2a93bb407a9186733a9136e75a9111ba0a9067417a8b900c8a7ec7254a7dccc7ea7d12d97a771e65da754cd06a6c48379a6ba7600a60c610ca60b3fb0a5f5307ba5d8dfb0a4e5fba0a498d45da467b237a460c19ca460688da3ceae7ea3ce0d26a39d946aa3715297a365dc0aa3349c42a2be3956a293f512a21ff886a2058a5da1eed1dca1b2393fa17199a2 else 0xc0661484bf7790ecbf3860c7bf27a54cbe7e19d1be64231fbe4ae1a8be455356be0729e6bca4fd58bc89ce82bc87a1e0bc61bd59bc049e66bbaffde1bba23ff7bb74fb25bb41e977bb167defbae77bd6bab196bfba6ae96fba67e384ba471675ba17e081b9648d43b92dfaf8b92c25bcb8fbe0e3b8d46160b87c0d7eb82a2caab7523a80b7245965b70d4f1db6d2e41bb69f09cdb66fbfe3b5ba365cb5a7ed8fb593cdcdb556ced0b50a776db4ff1a6fb4e3f598b4a3964db446f540b43c8c7ab4322619b41e2b91b3f095d3b3e65622b358e1e6b3025ef3b2ce6902b2980285b27196f8b22b46d0b1f5cf7fb1ccf2dfb1bf40f3b157cd46b147870fb09305ed)) else (if page < 14 then (if page < 13 then 0xd16a0df4d036144fd0229c92d0054c7dcffaf049cf8db31dcf60f7b5cf31eedbceea22a8cee109e7ce6cbb82ce336b0cce0fe789cd8a3535cd575f08cd0d1ef7ccd66952ccbacdbbcc84ecf8cc6fcb1acc460c09cc2265eccb574670cb54214acb5060dacb3bd903cb39a50acaf69de8cab34565ca93de81ca80d91cc9834d3ec8e4ffdcc8dfac22c86138e0c82cb8b4c8217dafc81ba4d5c817a939c7f6c721c7f54eebc716c226c686ed60c67ed69ec5abe9c1c54cf740c543c9d6c542d74dc54105cbc53255b5c4d16719c49efe16c486c389c4647313c42843ffc40cdbc3c3ae708dc397c566c365d39cc3190ec2c2819d59c26c33dfc170abccc08f302e else 0xe183fa75e182d7ebe153dab2e14e9ec6e0da3a1be0d1d56ce0588987dede5e92deaf2889de5f76ccde1adc65dd9905addd6a552edd556516dd0795c7dcd224d8dcc1cb5edc9eef0fdc95a46cdc65205cdc4ebedfdc4d3570db8405e9db6ebfefdb37cc62db2bb46bdb175718daa3d34ada95c8e8da70d062da36b9ceda21a2b5d9afc715d9a025f5d9857cb7d950f4d3d94f1cbad94b10a2d91e5245d8d48d40d8a4b203d812f7f4d783c1f6d77d5679d6b9d44cd60a2cc4d5733cc6d570efa2d559047cd4dfe679d4df3593d4a3d54cd498bdebd44b2c57d40b6d7dd3f3a604d3caac52d3088ba8d2f2d13ed2c09a9cd1c7f727d1bef494d197ed50d1737ce1) else (if page < 15 then 0xef883bacef17b0fbef11e549eee2d2dbeed8d7a2eed787a9eed3dce8eec27625ee11423ded9bc3a5ecee44c9ecaf15afec76b1eeec56ffb7ec0e00efeb90879deb48a993eaf16965eae42df1ea9084e3ea30fd3eea2de738ea1ef145e9d2420ee9cf704de9b07ab5e9236f6de91fe25ee88e58e8e87ae12be875e909e8442691e81c9779e7dd780ae7b6a8e2e781bc84e759154ce73ebf3ee72fc94be6b2d24be63f93c8e634ad88e62f424ee6038a69e5f2a8ece5e93699e57c119be5344b96e5229618e4aad2efe469ed52e453e7ade400aeb1e3c0fd66e3ac65e3e35fdb9ce3401a54e30c774ae2f1bb1fe2cfc808e28ce9a1e289778be25385f8e21220f3 else 0xfff94d51ff960127ff6b100cff088378fefc5f08fee4ac7bfeb6f6dafeb223ddfde85718fdd07fbdfd510461fcbd8d07fca998dafc399861fb4cd2e8fb476c4cfb2abbcefb1bc5dbfb02102efaee9871fa27bca1fa25493bf9fa1163f905d600f87cc558f85daaeef855e9e2f7f5c484f72c16e4f6dd1858f6c1df33f6ab7db6f678e631f5cadc1df5674a5ef54de22df5151788f4bdd1fcf3b351def2708c9df256647ff24b735cf2448eb1f1ad162ff1a4cde7f1581007f1402568f0e4e24ff0c1689cf0702cdbf05cfc2eef972ac6ef8f68b9)))) else 0
  | 7 => if page < 1 then 0xf2fc17e3e88e58e8e87ae12bdc65205cdc4ebedfca4e1418bb167defba471675b9aeaea6b2130c43a0f42093a0e52aa09e1f4ea79cf57ba99c424af69a8736c19814d82194e115c09365286a8d800da782169a357ee7b70a7d4d26bb752a5c7a6b0d2e9b662f794963d08eab626e621d58cbc3b84edd9eb34295b5c03ea44c4a3de0ca1d3af1a22339e7906d3536dd5a2571d7791bca8c1e18f3e8b00f03c24f071ababe017826f7 else 0
  | 8 => if page < 1 then 0xf4a70378 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x3001b00100000000b0008002300180020 else 0
  | 3 => if page < 2 then (if page < 1 then 0x11101740090017800b8003100f8003800db0001014801420180004000f0005800a8014000c30053000a014a015900ea00cb017b001801350013001001500000011b00d300e8002a011d00680175003300b00144003b00880094013c0151013d0168004800e4016200290184009800bb0103017a004b00f400c000230030015c else 0x43018a00ab006000c800d000e0001b002b0193011000a0002001280028009c008c005b0070012a0032005000040141007801080120000b01600080012d0158013400080145) else 0
  | 4 => if page < 30 then (if page < 15 then (if page < 7 then (if page < 3 then (if page < 1 then 0x3c01c0a0740203c01f81730203006901bf90dd801f0047312e8030c1d041c1022550d2b1b201a9017c007d309c800fb1f481c3009c105c01968045b1e82094d1af30e700028154c07e3099004500c68170200ba1a0310f1130b007819cb093b05d0148016900e8300e91ce80b3816580e510c7421e8081a09d0189b01000758 else (if page < 2 then 0x10310c9a03f420d4167a0b5c1d910c710c200db815d01ee110610948129014e0078003710be01d6002ac0f8c08bc21ad07c807d8159c0e82107105700d62096007aa12f91d090f641108177117820de0040318010e201f911b800cc10cb207880ed5179216500ce10e451158049010001693216c05f90e100ee50008063912d8 else 0xca81eea06080a4b00f2219c0af8216009e81b501640027015c020831da00d601cad19940c980d530fc921f516180cf8039305500b61005802b81d68075306e417a9068010a5198904001c881d18070b18d00bb01f08178818e800791abb006a165a11b4186c01580181122018b81bb11c8003811ab408f0086b09281fa91e01)) else (if page < 5 then (if page < 4 then 0x5f005a81b300ff114b80f2c140009e301081a4900901b000848050b0d480128059a082304551f7c1a8c1cdd05e8064a05891b1112f80b3b173c0ce0005206db204c215a060319d805bb121802880cb8064005841f9c1c180f80165c017802d81b601769082814b01d8814901cc5154010800cd20d8b0809153b146018bc1bec else 0xf421ac0c32179018b90fb20ce417e8042b14f418e01654003205fa0c58030012f00d6a042008d01a801b101e43171808ea06b120780c1b14530b580870210b00211ed118880e880a48091b01a800b900b01cb901b01cc80c2a0bf30f981bf20500052020a51a300ccb146b12d30bbb1238163411a30da2174818a00eb006f1) else (if page < 6 then 0x2480630180a0a80097306b01c4c017015631178110c09f3118803101fdc08381ff41645099801841f84118000480ac216e807b21a02163816e021da06bb14e800a0096216a80f89089409cb17a017510e7100d321030c7321651ae00e740e8017f0108d0283062220d81f4021b41d9d0b4c17720abb095300f80fe81c831860 else 0x10c810f41b181c0818a11dd8136c03b80804102519841c200cea0ca40ca5176a13500eac1afb1ad81a9800240dc81ea11615224014280ea01f3108b1006120e00f490c7c0f2006680b7006b8059b19311aa8200c02b902501f8a12b8036820930881017b0a30001902c81edc02eb0c18172c09b919a8221b14981eb90d230e50))) else (if page < 11 then (if page < 9 then (if page < 8 then 0xc8b0540213907e80b400c48188a0a780f1c1fe312c010551a700f34048411901474084b146818c918801eb316cb1bba1e5908f81ac1205804d003bb0b7804a01f4118e105eb18ca0d3012881230217421d8001008c10ff413440e600c3801b30de818a214580ec90fec0210191000400e781dc007100d40013817351ea80529 else 0x1d301733221003e816f804a8064811b9067c04b0001c002a1e79116806a004a91eb009830f11061917601be007780413168c0fa115f81e881398189a191c003b08fb18a90f4005dc06e00718095b181b07b31a91180b048015b8021c01d807fb1d141e9c00ea13d011b01ea0075c0ed01899207008e305f316d0216804c01240) else (if page < 10 then 0x1dd921bc1f1a0dc404c8101c21891a2c13b31b7a099b21a01f1109421aa4061200d0133820280b0b1c70202c106d12b007d01fc8066b21341b691eac03e011000ee81f951c541bf006580fa30aa000301ae200910e98046b1a64052d08581d0a10b40d8011740d1013b0041022520fcc1d1514e400bc1752185905a006eb1419 else 0x184018910d5c17fd1ef002d31c62098b1c0b21d4201c10c10208189209802184115006ba0581146a10c40d7115301ad018fc00dc21c4212805c1171409782179033816680bf81834169806201181204513e8044306b201900e3804b80ef116b00df8056803780a60174b1d4018da208819221a38216a0c1a126007020ef01208)) else (if page < 13 then (if page < 12 then 0x1e12136016a403ba1d4a1f3010900f6900f11d29206b0bb81758048804301bd819000cba192c03311a42187520bb09f80f1209c4053006ac0b1004680b6b1f0205581b4c1ac80ff903d80eb9026006d40b98181413900f3c01d0147c06c31ca41fd8060a1deb0dd0099a103000e0031c19cc02e316e417780e9c1c1909401f12 else 0x19a40fa80118183c04081f1808e814f01eb2067810fb076b18181549147122240ee117441de004c308e906b511f801aa16c800d11b2807a419d203a422531680023000201c90209d11e802f0034005b81510223004891d541c8c05930820094b07501e691b8c15a32053058d0c79214811a8043800411e9818e91a7a0fd00b30) else (if page < 14 then 0x601202317fc10390a901798142b007b1fb820740e6801020c281df3002b19e014942033211011241cb10e301b011da8138b1a080198008909680b441848152816d820d51a331aab1e7405b3090c07d112500a50004907201969108500ed1a28156800d815780b2021980f79100c06d80433053808e008f105981d39051317c8 else 0x17a1070000b20072042819901660214411400adc1854005304fb03d21e0006231af0219a0a28052c0fd10cf318101d201f5211d01b821a7109a01791132000600a1c01e8221814c8068811bc1cc00a00058520041878090816011f5a11c321581c4a188918ea0e54061a062119c4058a1541008005ab044b10950ef913e01bf3)))) else (if page < 22 then (if page < 18 then (if page < 16 then 0x5cc0ba00e080ab813281b4003b010240a0803d00c2314c003181c58007409eb04e011f015fa1bc0158303c80084021800330d741b1b051c1acc1db819d01a58174016090e6c189c10481b7510011b940f88028b131006c8072813c016db1de114300a5815e116ed1a1c003800b10f021d7810450da018200c4017c406e81e28 else (if page < 17 then 0x14f805181d19061007480f90194d06981c79199c1dd00b2808a918d5082c16c404ac00d20f0103e91b5316f40aa81548024007b808c0178016eb062a151c1632065c224b0ac318a3100819fc207912f20f0d200d1144096c09131128189005b0220011d800dd004405c813d802b11a991819032020fc20ea089b17d011ab06f3 else 0x14401fc41029198119c11d000c442223079801a015b30ff003341aa01cd51bab17611bd000b816fb1978004c0810048c149b13f40ad30d031f85201002f8008a19641c6814a01908213001b820b01c04170a13bb1b651ca90e051d581f09114809fb0db416390a1421140a980a2308600c83212b1c9a21081ed91be800b400e1)) else (if page < 20 then (if page < 19 then 0x180522280ae00c100d9815db08cb1cbd1f0112fc0ab419b4172a0148020003fb113400ac1fe8150c109804e818d3017a0988152000001fc00f0a1efc06020ec400c5225c1ee013b8046014d006d000d402281ae318f018211c2815b016001cd401600919179a1fcc09041fb40bc02222210013700012170818bb0b7b0fe91a22 else 0x1ee419e201301eb821fc12280f4803f811b80ed11a6921f4038c0ed4186513a004511adb06520c4201b208d815ac08780c081ed80af01dc81f190070153a1e2000941448080b2140206217b01a1405a31ec307c00c920b8b07b021900f241a78217503f008a0130010592208139113581ffc0eb81340058018db056400fa0920) else (if page < 21 then 0x172416081c3a15f51e11167c11c80fac0789121009a805f80df40bcb10c5215006380a5b1df81bf80590175915a020a8155815e9198c06700fb31fd0211b1c110fd407c91e081a810db908110ad8054810e40d7b09e0082918220cd90d701b0b07e000f02020083307300c900110204907911ea90fbd09ab0b880a881ee81882 else 0xae804eb04181c920440171003981669077013881c6a2038169903281fe90da9035800c81e640c2202e805831cfd171c11700d120921114c057804980e480628044821a902c31ce21d4912e0182d037021a1195405881c91176206fb1278129820f4029b170016480fe02060177009dc04f000821fa2039016b3018022611330))) else (if page < 26 then (if page < 24 then (if page < 23 then 0xb140aba09b80efb0fd81b7801401d3516840360176818c005d301e01928091022620a40179908081bbb1f600d4a0d3b02b419bc21e018b003f10cb01bfa1d2210d40c502145018806b4140b103805fb1c120a700ba80e281a921b4806141941132413991e2c0c0021851cfa212a079302581ba115881f4217381cf200ec1488 else 0x1423091a10a81e71209015f4049b005909b20f410f180cdc066000730f511c400bdb1dea1c380790101816b81f001f5906f021b01050105415530150061114d820e8047813781f29003a17e00f831e8917d217f40384116304bb01c81a8802531f100e180168027b00880fb01af802f414a80d751fb016f00018007116281579) else (if page < 25 then 0x842107910f221381c0012800b901750006b13131e831898037b09380d6810c90738007510f009d41a2004540b80035409b01d2b104d138a1db01a5006500e581cea1500223b0b041a9b1ea40c6a108c12001f341e781fea00131b0812581ae808501df4224316301dfa1070215418aa175a15cc1c53096910140f8d1e5202a9 else 0x1ad40883037300e8086813a21e80062b1b381f94226011b1111c0b601f70134816bc1b3b1a7912480b680d9018c1049415901ef1119c1268192107731e3813c8196515d81e700c600220153105c30b50139411190e691cb00673197414380854144417b803ec17d106291f6c00500c3020dd1c011b5d0a680e900edd20c81623)) else (if page < 28 then (if page < 27 then 0x1c6001201cf019ea026813ab1b0211381ec016441b6b16e211e00930102806630e7c1fe010b920c01e7c218813fb10e9083c15181c9b131804d81b991a4c05e317280d9a1e33143b1ce01c4407f00d181afa13a80b181118166102900348221321641d3d145c17cc0763184101ab12a817dd141c1f3b00a308eb05d80a381418 else 0x1d9014781ec807eb101000980b481d4318a800a80fea0890191a02380f741cd81bc80fc01f211c5a193c04d31f8d14ab140808301ac002e01e18063b10f80be81d70157018f30cd810c013a10642181517090d08061821cc11100ac002a000c005031cca195800b50ba121780acc1470038906b903d31eeb0f5920e20c2b0c4c) else (if page < 29 then 0x23305e00a10167801c01e0b0bd01f5017201c981bd4105812ec1fbc1a720fc808880ca319501d8011a018cc224807f8007a1b4416701be217a810d91c7d02f1109d177a1ff003a806e90ea80dd409f0177918490a5412c81f5808a1084013840b540ee9139c21201fd312a014b400cc1414208019f001030cd002bc13c41a09 else 0x14a312701e900ce81e481ca2))))) else 0
  | 5 => if page < 64 then (if page < 32 then (if page < 16 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0x2b60096921883f702a3c31121a98046000d8458324dc20a5089826880208421010000939070330a0371b0d802858198d069b0740165b390831800a102550110d42301d9b14c03eb231942a001ea00e982fd109a013e330f0103c2d9000e837ad00884188148814f80200215320ac1e681e6c02883bf03a03293c20081e9029a8 else 0x43a028303c30047122400af0334200740d5821a409e415a939bd0800267912011e420d182b9830b00ed025b025da3f19365c123004c41a5219e0335518e9397403f82708377c28f912040d5a2dfa0024278203594204395828222401152033a024f224cd257b3942130029b92f2219cc403139a831083078411833ea28a833b4) else (if page < 3 then 0x21e13fc818523541109b321815b8349444c32be819c113fa1ff8224317f3050844bc3d182f1029742af806fb2bd8430332200cb02ae31960344815d00a6312933ad400a517ec1d0807b82be91bc020b940801898216b2edc3c5b1c4045a2413b412817952e2032090233409218600e1016180f18294813813673254839533068 else 0x35d82c540b401a6a236d28b9315b184d45b32ab32c103711306419583693378802c22d800aa40e19126434aa278828701975239131d40d282c30136512083a942993395c21c1329831281ac83850047008703cb00e682a32274b303900f003c82dd80a9c2e0832022b02454826a8365814501b432fb0221336981e7b2aaa1455)) else (if page < 6 then (if page < 5 then 0x168816b815e223590a6502b02b2a08e203530c880440286c02403278011a25a4101133f8233008a02bf83ee822b30ee831d835b80109256942b004983aec00791770083a1152124843330ff101b02b422473310933aa4518275013902cc82b313ac82a9b1a3a404143680cba12711e5b13580cd81c30459c3fd022b832590840 else 0x1ab84018455000283b50089a057b45402a302f1d417026491aa008db30ea130c41c41518183816f015ec3363066815a004b831e334f83a4135f81928005828483fb01e3110b022011a88336a1788284035193638359105c4190537e82dac18f80039406a33e207e0442825b80dc943f4346124040de022c3240b12442da000da) else (if page < 7 then 0x13a106a80a1340102fc444c924b029182fa20e2d00482b490fb92ba8048302d82b5a05a824e012a81d5805d821d21b5c2d30451226581bac2e8b11e01b401e6001d9001408940f5911e8389027d80e4008a810382a4028a02953369a2124171815f210e42831431a36d0453b41400a882bfa3b003d483439098b27602ae81220 else 0x2f7a330514a82c883ca80df83a1c04b91a0d27f217a805404460129d33f02d1821003aa131b3320038823f43244d3b141561346c082329db21b115dc2e6c08d01110313106a02f483e441a4c17b80c124240302223db17b23ad8303c031b4373336030801aea32231cd81653084b2ecb00b839b040c0364103fb1a0c0e72258b))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x20f1299b1b0820d4403004210cc32a681a920d9a18dd21b5038927e423783c4036eb14120de811480983074809b83b3c13950db02e682a0808b81cf33ed82114431032d031cc17e53139340825b339da20683d8c31c42600334a402415800dd2262c0fb80675374a0323171038c9221923103310450342e80c4c24ba01481332 else 0x452826a00db923fc1f80456928341832233930ab267a329515a234a0424b3289417828d008eb17fc030c09c91fe8178123a8294c425b09213a10400a2d5b38591b700940186d3252316438a11a703ff21bb422881d2800191fa00fc92db242d8393b3fd8065a1db0439003801c1808e8309427eb37b820400a48131122943661) else (if page < 11 then 0x291d2ecc1139038b31700fa413783928264039c224d043e011c243f120a416e2438823c425993ae03c9244980f20391036b805141f3037b0226805b803701abb3338332206282270339a29eb1d500d480c08374813b8347d102b32a83b5221582b512b3a1fea059020b41b0a256035d92e1833e82e5840eb3c3d2ec01a611768 else 0x2308247c2fcc432230402ce225232384051b096310d831a03d5b23552db8394b0e1c3b78046925d81b881ca03c88017812d03af0308428600b4a247219fc0610283b13700c4838b30ae824ab35f902c83e0c16f8230007801b9417400fe03ccc09b002181f130ce80718313528c016b540e13e710d3b19e82ff8117136f82bf2)) else (if page < 14 then (if page < 13 then 0x308b05a03122443036e12f5c40a844b0390031a8106931512fd81e883500003b2781329044d321393ae43bf43a28107b22d3254206aa21930a11298a09542f1925f31ad135a041a22f2a245513482d781a694530368031d0059119fd014033f33559005c41482be211f8442000320828340310c9138815c02f1b013219480bf8 else 0x263c43453b0906b223c20878156901ba25e139690b3113910a6c1ec81b30112129782dd91cb833183cc0268036903df20ee33a7c2ba439803e4a275c097a08ac1e1836002f003eac1a893b901625037801e83368104022fb349d343a0beb227819b0405d3730384307100ccb05f213292d68428005003042273233402980111c) else (if page < 15 then 0x4001761303039f02ab0101b1dd30b1809681d3818303111257200993e3042a403d0128901212dcd41e8164828d83282166807f3408c301c25f2058004a944ec35520e883db03eb409cc22a010d0241826c012f04190143b12ca3ee22fec081021a82630426022a83ab000e40a782e8928a119c40e3820dc158526e0004d41a8 else 0x188800dc169811252b4c28c90891259c39c000a901903da817481e73304105601fda055b3e622a49000d042417a925f90d7c0ead13a8406b2e0217dc376039cc1b23076345d006c000101d1b392000ac2e5b067307e8127002d043803ec80a920ae02d701590366c3cf006f3436b292c3820066333c0340a32a12a6043c23874)))) else (if page < 24 then (if page < 20 then (if page < 18 then (if page < 17 then 0x31c018653c51169311c805f828f83ef81c1c07fb12103af2065141d834280e622e2230e8214c38d91a5837dd380045a32d20192a0ff024a0203040e836c92f20394015441afa18402ce818fa23b83432081138180bf04510053404cb041912a01e3a35700b6839d02879358016c82c2c32300ec9010c31a900a23f2b12f1114c else 0x43d0009c241936643f40103933da099b294001180698342127aa160015782b183054404040ea13411f40059c3390348335b009d02f6c29423a802f0842f3049027cb0f28312502213afb282835782f842fb23c7943b800332f4025883ecc1af100892510386c3e981b98156437142460097106da032c19c01969248018d8279c) else (if page < 19 then 0x16d8286314b03a58088838782fb8389c21411b1027c82ca0162c40e035c817450a000af80b281c88010840212a8433c810a4390b09730b903c8b13c0440833a30c181de8338809d21c683f9922ba312127b01820086c42943d5823f42d0023e819cd0e82177c221b089910ed2250233424780f7101132d892083022812592b08 else 0x146014ac3e8038c305102f7927702dd23b58274926e800b008440cd11d000cf03fcc1b542b323cf43d102f1809a111990383057834e042a018483a88133336011eb01529047b3a9b36e03e512e403d5a2172286818154085447c4564459025c80bd81aaa3fb231003348253b44a43f1802383cc83b0c06882e48457d250328d1)) else (if page < 22 then (if page < 21 then 0x88943ca459d0dd927381818195c427024433b84317c36ab3aa8304400400acb11f229d91104027b42c003e008091a1d0ff83168121911582a4a3c8245c2306c28740115237403300b3839592ff433982f3a3a3814a021711ea1168519d93f050fa01fd809101253121c2e6026e137104150333b1b1209b23a743ba011182b70 else 0xb7042ea42b8246814e80b34283824082a3337ec17983ce81a64412a457c05791d2b30d82c082dea31b8251440f033201238325009ab26893a4817e20603103a29f03a002d080a2b3f231c98409d18fc41082a8a209005282778085b32102d40156b0fc820cc08194254174d0b980e182a9010982c7312a200300e59270005bc) else (if page < 23 then 0x27923fbb243429490c683450173515e942f02f600d0433c52ddc1cfb07383e8909a93bf126d414391b68058233433101204905393e9a1164189110c1245c287106d027f82c3424142fe03f5916523eb11fdb4209008503eb31423de83e58159916a12cf110123deb38b20f2c0a203d280690008c21b80e283780430b36ea13eb else 0x2f901f630f3817582c033af92b341e5a3baa0ea40d622af0425a2e380a33433b444b29ea0350221035e04348185c2b2c2fc027a244902d833f0a138017803c502b8431600d3829e41188095b3e09345b223008da04d027f11e001f732d9a42e30c28106014e027ea3a90139421401d20327010cc0084372818720d53089022e1))) else (if page < 28 then (if page < 26 then (if page < 25 then 0x20a023451dcc3a1d3b1c3d4013e036393f21217c2c681cd03cd01974426b042535281de020bc12883d741ff335c92a293a60067103b80ac034302f7802902218154905832538222026502bfc29280a0b082007f043eb12683c4442c928d9227a237a3621336b22722a78281b36c8134d0568233c298b3cf841843ed021a13681 else 0x2dc03cec24901ea830d410783a682bb014d028530db21ee344340720001810413b8013fc13c8003101c829d812613a0b07081b2c2914116800091f283bd210310ef523683fb82fe329fb24f337c81be80693162126d8428b3ea9309b38f8315000c0189a263837e23da023381ae80a1b398511943682123311813eb81b380fd8) else (if page < 27 then 0x2adc335b14c800a03b731c702b403938318b32aa4211275833a811332a1039d107b0394a352022802ea5180a09c835582cd008c8110110da39d2400811912dfb407a084127800b4821082364273a1904186a01a815b0123c010030a8374b00903eba3f282bc83cc23f5214a10d6b30f838d0381001240b520b8001e03b60250b else 0x1a811c80354c155017a342b203e827ca163c2c69400437a21c382f52167a43501dab0be04308202341303ebc30283561320143001fe3276b1f3b18b006440f7b2fc819c20a8106d81fc407c020f010b31018349c1020291c31e008e12d1029b03ea838f103103ff8007c04a844910cd00808134242c1095008a4428237ac0ba0)) else (if page < 30 then (if page < 29 then 0xef030b20ef30e21126c3c7d25203f8801800e003c680a192e8a0f701010395027f941ea17602a85012a03880c5320280170239a2b0a368c2da902f00bc342d92aa31cb02c622b3c0a58334b13a01e4c2ed1280836102ab2030042b92c5837b93c48386211440a7a416022383a300f4910013cfc0df132a01a393d2007b90aa8 else 0x18806d13750125034000f581778367a43632d43383d011124281e280f65343833093e122da13bdb3afc2724228b35830659431b2e9d437843980a3b33fa125818dc43381398325303032cf020fd161c433039f839b41e63010a00fd3d7822c008f813bc222b0ba823750aaa00c50dc835e103e43a9a34601a2d061b2c183741) else (if page < 31 then 0x1ab00d9225e026b82060302c2e100c132d5012523d8044ac08f31a453323331b19302e2845bc10b817b938eb20983048033d12c5162018ad0410352919b908451b202deb40722be43d301cc001d825c02228451c277b02f8065017a51bf0248c38c2300c01382db916083c342772102112c905381ac93c540c980b0842d21638 else 0x39e82058311415f035080f994133281839b80c902b5400bc25bc2b58254b11db43cb2add18ea3d001f780998363032b900ed2eca2000144319a54020187841b02f503e382b03034827e011f0319825800f03176a30d1232a0ce91b0000501e083e2d35e840e2011b0c6c2cc0093027b82f413b08264106ca05fb0a5030603ef0))))) else (if page < 48 then (if page < 40 then (if page < 36 then (if page < 34 then (if page < 33 then 0x3c0805a1260823e0133016a30a8a1b9b27480e33092023ec1700248809b129c02149079820fb250237082f281ee92b9001c0200a36501e3b2df844c813ea210b0bcb23c141f40dc20c303f682fca02602ef209f029080b103b441a8c06381b903521255b424a0a0418c83f2034621174007044802ff009db24d832b106741828 else 0x22082168446c3f801fb0380a0f802c483b6c1ff01af8095817ea2f491910199100c12d6037fc3e4b3412361128c8041c20483eb924aa314431883a2039e306a33d383b4a183a45580c002f73249802580770256c00e518e50fe92850065b166219d8139d0db805d02c72117005b02c9003631fb83e542e70093543c029ba2764) else (if page < 35 then 0x33320f1a0f530b2a0f0029f32cda31c8077837580ddc021034180a693cd429682fac250817ca10e1340b04f0244004e012e810680b421ff242ba18b2120a1e1442550c730599372003953bab3ff10a9939db31ac2ac0076005e83848036009d5104840683c453a502da200ba038a329333b826b0362b34882528367044101ef8 else 0x2dc25e9116a24d113183a021e2024b3000c1e98403a0064323d3e603bc0057a28b138a836a316bd081c35b1356d2c0b1a7840a91dc00b53132c266c1a1c00d43c0903a42200127c1f082800064b43b0182316151980451910c01f8c27431a480ee92bc00d701c5004631a710e1a257a0758308816111d80342a23d20ab3211b)) else (if page < 38 then (if page < 37 then 0x281a1ed032c03ca0259044883c2802200f68332a42051120165815c409381f8803a820e341fc2dad2a2c31e82f3223d0200b2c6000f824fd04db034b04f834c81f483599323800a81d6835e93e421d1011001138362001022d791b04156003cb165012fc3bd3241c40bb07300d423d632f38199927f00e24342929252ed03c90 else 0x2bf114b8349011c022600e5126f83ee00fa9162d36481c601042219828f21e301ee020c42c890d201945052309433be043d815a838c842f8212905e92ab83fa0077336b003b00da9020b03d80e4800dd093b432805111ae13ef4142d2988090c419c12981ef32f6440b00f13147937d006a10f40297544e83e1d444a23981e40) else (if page < 39 then 0x9da29d021aa3adb39a02c403f1a19a8034004b1135524bb17f202e445a8242003f01e8314a412d200bd166d34423cb928520a5a269811d91e1029e0067b41e01a353c702d3c000819183e4329c11a621f231f1b39ad15f33f60101a10501890139906d322d0330030fc114013e22190213c42732f9c387109d836c11d3334f0 else 0x2e001ed805e0009828f4132220e810f83af828ea42980bb04073369221a91239117814201720207815000eb42bd12a2801a02bda24843bb03bc82ed4429104181f43066b2e031d731631453a1ae022c8375c14723ed4158d06b8323b45093ffc305840c806400a1a25a039b544502fa838d145084288006804f310702b8809d1))) else (if page < 44 then (if page < 42 then (if page < 41 then 0x10a815682070252b3ac018a512183979390321c82972271c18d03fa9224802fb404d1932367b2f8c1f0026da435c3fc30670394833e0009a4418129110081448081825d00c50448a307a0158022c2e233bec233d30701c20144d40121bc143f825a219980f9016102a982cb83a8438ea3f9301140f3934a317a025631b8011bd else 0x358324b17ad1841119c023200d91d3000710be8175b0dc01b4c41c507f8382827d4326008b03e080960382133a243f01ac044a02e831b18341a21d043a842f943020aa026641c28179d15e83ea0235820a81ba01a191bfb0bb81d4837440d3912d924102b64274a3de03afa06c818e044452e693be81f6b36192aab21f82935) else (if page < 43 then 0x1a303c9333ab0660159807a007bc10dc0e600ad322c200c4456144921a5a092931e90ef83d601ce8076823c5295830502da809e815c8196a1eb817cd22582880400022bb389937dc3f3b138516b01ae41a5902a80d10165a2de0452025ac4248242105701c7823f809481ae930100e69246134713c603e880d242eb808392960 else 0x32f504a03e593d6232f843ea134c301201bb37e3039811e225e81e5836783eea29b819b825431fe00d9012321a0815750de122d84362277a16a930234238297105fa1a1842e0297a30c031f80e39305935c00168433243c314253fe823602be00a5133620a7035d00ce5199c3248011011843ad043c80d322ffc037b1fc12bf4)) else (if page < 46 then (if page < 45 then 0x313011602c9121b426d903382fb31b60087c1ea912283f041ad9167429e1406023d337402ee800522d8b3f48218038880a9031bc24b822840e0225582f8212c041bc196130092c7a25db2678175d26f003f3192005f535020d080e58231d0a4334310eb844d924a814302144407807884591273c29f82ee208e011bb44d810e0 else 0x6e822e406183d513fe01ec0048b3dd825f83a0813db32cd3c9812a90dca23cb201b3aa03bd805301869149007c1219932a202b816ab172800b12d482624371a17082c840e2016e9164a3118042037781bc81df82a181fc042fc45422f68426844f536722b382eb000e123483b4b3ab800f43db83fa40b03303838e00ab80ed8) else (if page < 47 then 0x2a5015343c8021100e323ea2246924cc060013ed398c2fe80eb344702d531b01271039d428882cdb20f82c3c068315a108c44180169d36a02ad00f9c1f98345a0a281ffc293d09943d6830951e43421b0b5b0e833b280a841b1b13680d0042780b2223323b48117a38d804c136b23c3823180c3822cb0923009d30e0096b3330 else 0x3132402835a843232f8029f21da01224391310fa42f23c8a0250169119f5112c043310c831e23a3b332803a02e50175045d11d40061329050d403718106c3f5c41641aa1385c0c3b01f000931ca83440415817710588139c0eb51c58430a05981bb81aec2ef93db334d014002d9b1fcc44000db1305c12d830a3159a27a92769)))) else (if page < 56 then (if page < 52 then (if page < 50 then (if page < 49 then 0x40d809f30fa81a4d23f9254039433a6c3d0a244244690a722ce00c2045130a3012c8251841d935f00e9c128c1842103027293f3334b2358834d84379456c4349429a125c0792173805f124c018f412aa2d2c40531940098123a3384234b812091be01ad0447241ca11b907cb20d00fec3b2438a417c91e6219f81a102d01043b else 0x2a006e04224360a42c444bd25700ed9253a27a8054129da162900fc1ce0298242203020359808f11f9303c4105822983fd124f007c4062032d80589000a050a1a2c410014f0319b2c8541f5115133fb383c450206482179086842eb06c91e691df02d732b7327421c102bd435d130c80509433a30b940d003c042d33c142d63) else (if page < 51 then 0x6cb27c01b781fac2bea45820eea217d103200e03ce0032000601538278919e12f9339303700060811a04574002020883dc82f39314800db28230e4429b3402a0bd308303dc019e90dba00b90eac13b03bb807284372045834c00a8001d01269401a39602c7b303a0d3a224b21e8364023f01a2008533a8a3770449c37982370 else 0x2c02e72307b09c01af0005300591a9107eb38600f5a002918d20d6541b804b03e231d8812b82a0b141d012b3ff040a0227b193827fc3f5031b03422261c1a5b2f420222348d3b0123ca3c253b883c00353011b034580f2232e045cb1790054b0e782fc91a3816d13fc0330b21d320a93c010f08033c22b02b9445c036a23fb1)) else (if page < 54 then (if page < 53 then 0x44fa2a5139181a9a2c631a0024fc1f33380b14fd3c8314683ec03f38403228923cd8141829240c1b2690158a2a580abb13f009000e7d097803aa0cf808e9268200802aa837f0158b3a7802e813493e901bc411dd34981a8a3830045b2733399d108441241950268137a3458b23801a900dcb10bb41d30f88386924943a4a4110 else 0x3bf8369b45b9353818c9360814d82fe92a70158803ab0b7b0bdc3e393d50428a278a0f691a5019c343e82b281bdb38ac3231421a0ebc0cbb2c24035112e40f6333d82a20140c2f4a3288163013e838ba211828e4031822902ed91a6c19ea198827b940382b2923b03df8002116641c0034fa2de80f480efc11a813380c70244c) else (if page < 55 then 0xd5234103e10344a35902e303ec44168361807a8340221f03f1b18e409f82dc8254a040b012043200c78458a1aa8264217f8259a41fd02c111280f604318178939bc3a640112341317e915080011396813d81a7944d2093444e007d332403b340c1024e82d98314c20c91b841e5001331dd806ba422c3e4c3d9009d423882578 else 0x15fd0ec8024b333318b80d9c36c0435d3173180141cb1441197c297b010b2b78108816280ce0013004530b502b002e7d3d111a280a381cc802e00f233ce43ba80448329a20f406803d930e701d9012d129920b51120033d335f12cfa0da806c11963249c3fd41b3b1c900d3001c12d4b2893350912a121d822eb09a82430187c))) else (if page < 60 then (if page < 58 then (if page < 57 then 0x23e445701bbb2fd01db80d983b0409223b722ead357c170116c03794097212e0159127182b0b08802170309a261030183b982c9816240a083853015036b9173d039017c00f3431150672326828fc026b0b881c0c19c53d4327980678268a129219700fd018080d88155a0979062b0f9840f81c482f5413d04044239403942d58 else 0xd780fe844c2212c1214332b44440c40124014a9194b32e808f0190842e21a091755279a3f10138a29c81134427b05810b6035310d691af237c00ea8164b38f0007805ec04033e782212002a1483075000a319c9051505f036e81ff9156a12b506340ca02df41e34019825c43bd013844543145839d809280b303e920dd03811) else (if page < 59 then 0x36b165d3cbc00bb25a80a543e5c3a44328c45383fa829103eb02b1020131ba3088101f81bd02cb01ab22a4834a11990304c38802192164031241f38373811ea289801603b533e6a2f30412b0b202ba0387a080104680e121dd01211245d293424541f9029a0010d236c2fd2170411d0129005c82aa018490d3c3d9817d24129 else 0x2ce32dcc344323c804c03560109022e02c2026c80ca827ab281032081d7b3ae8426a0b6340e314983f30419d36d81e38065331901d601ad821e002703d0b24b24208376317da13280c60416b00d03380195438193a7037b125303c7c1a840ec421c029e80fa128200a2342c844582fbc07db33940a4034e826913f9844382a03)) else (if page < 62 then (if page < 61 then 0x1a600fc337681dc82b2005c001db24002c2815d107c50adb2e88299a242c2f580000183b0c80199d34203540028019d032a9289921a03f780e9328fd33122a382ca818a802302041300003684070360c0e09182d115c1a3413da1fd0353939920da03a213f0b06b0079010fc161932280a6001b8434405a2002b3e5024380550 else 0x2ed81510188131f0185800cd20503a0a21f11aa419c80fb02bbc29830298216033b0078a32442d922e9444fb2e9036d1232430bc3e611ee244f42b8036f0325840b126742fa044a845b01282428342a8413844782b6b01da32800918042b388c01281a8005f42f99261330f12cfb3e001c08203834520e2209a323da33d028f0) else (if page < 63 then 0xdda337806d206c430d026481f581ee801c408382f8823111c3b3db2333a1198195d23502e912f7027e823d831a43dd00e5035182ae23510341b2273134039c819b11feb1f5035a1323219f92c000d82292010f02ce945ca3fdb126038bb3c3c14053a8b36e4242422f02b7c098000923c4a2a8b0d4a3c1a00c8035a292d0aa1 else 0x860152804e80c5841a32ac809880081199241d221341fa827281d03337541eb2fdc18c3)))))) else 0
  | 6 => if page < 16 then (if page < 8 then (if page < 4 then (if page < 2 then (if page < 1 then 0xa22032902b8069202f806790dc00d2b042207a0033807980f0c0bc80060053c05ab037407a903f90663004b042105d00dd00e20098209c308000d900eea04a00319056c069a08590e520ebb0bda0efa01800ec80788009008c8002001280673028805900b03016208e405280d230390036a09d8066b0028018404290bd20928 else 0x94307f2083203430d20046b0e6207e302480b4908f10c5b08d00ec202e00c500e88035a0b520e2108f80e2a0c980c200c92048001000a20084000680bf0050303c004000131085c07eb03ec042a086b028a011a07ca00e00c90076b03d102080aac04d0049808a90a64036207d807d00ce202c80e7005440cc002600c3008f0) else (if page < 3 then 0xe080c3801590bb006d40651062006f00cd1070809a302b0041107b80992047803f00a080dc807fa03a8084c0e240d28038d05a4080a011001380d33099b08f90043073002da0bab073c0c320c48016106280ee00bd10da00f0909e0063c0eb40d980d2207b00e4309cb0d000bf805e206e203e8096000690d5003f4098900c3 else 0x55908a10b120ab4075008d808b20ce30348066a00a80758029c0c0002e50ca9097100e803a003fc01290408098308440e400be307aa08b00453071803b8088801cc0ac80e6b09ba01a001540c3c0e1a06380ed2090004380ced0aea0e320ad908bc0d0b0beb0cf80eb00ee80a700c7808a00d6b035403c801d40a300de80d2a)) else (if page < 6 then (if page < 5 then 0x3d00378003005000a5007da0d080cd005bc083807bb03e304f1021408d9034a0328085006ab07d205610dc20e000d3204c803500b1a0523041c06f8088000cb0c7a08b103f80bd80bd00dbc066203c200a9067208020ca103d40d30022200990231059c031809010b59023407c002d40ba009c2013a06a30a6503cc0d700b28 else 0x9a801d906a00608050b035806710004009804310ae0099a0b390d7803dd0ef301c8046007b9077806d90a230b600b7404b009ca0b0009b003f20ca40a6b05c80418017006780dab089a098800500c2203e5095801d004e303db07b30b440a7802f10b0806e3040a0d0a094a0cac01410e68058008120e5805a5089203ea018b) else (if page < 7 then 0xba804d80ae909f00bea03680681098b067a054803980b1308f4020009590cda0f040c70068b00f8019c01e1054106a800090afa0e530ec001ab066102580a28038804a3057802400d83059d03a2036006830a110149011206500ae3044105500af2071a070a082001a400700c890ab808ac0ed30dca0b8006b309a205690b22 else 0xabc02ad01e906b004390df00f01012307e00ca8093206fb06aa054c0169063004e20363038c0b4506180c0804e003e102a00e2b07930e9804f003d203850efb07e8052b0e48025d0130058901500dd80658055406000ac00d790d72033006a20991012c0be20b1b08fc0830037a048807a10a8009e80b38017103fa0db30970))) else (if page < 12 then (if page < 10 then (if page < 9 then 0x9b308220de00ec3033b01720da80ed0086006e800590cf906c1024a0d4003ad0b230904065a015807fb00d3025907c30c0a0d6a029d09080ae108c001c10688068001880125091c0eab083c0cf00e4900100e5a02f00a490ca006c003b50652082a016001790640035b017400b006590b9b07f3014c08b8088a05d300f003d9 else 0x6680e380c1905e308e80e420810068a0ae209680b53093b05e80e6a042003400d130bf30b980c8005700da30ed806820a71077b0d88066001dc06d80df80280033d071001080e8009ab0c280a14038006b20230039a04280a380afb08dc07c90e4c0d1b043c000c067007400bbb0cdb03b003000c600e90007b0eba0af308d4) else (if page < 11 then 0x51c0c8204b80cb9001107ea025c0be00d18039107db03dc0c2a014008e902900848087003110289012a032303930e7804eb01f80ef2078008780c8a058807d307900db00520076008e0077001480be80eca098a0a980bfb0cb103e408030c8804b100a0034907200a10027009780a8c01e4064906100f08016a040907c10a48 else 0x24103f30c0303ed04ab01d808a80d600410040206e905fc01ec0bc10d4c0cc90b100d1206bb013200880cb4001802390f1009f801a80d800990029903d80b5807e202c00dc304900d10096903eb05e0072c0eeb0325059108e108c301b00d68080803090ea809d00d1a04320e1b04a20e100e630342015207000ae80f1203e0)) else (if page < 14 then (if page < 13 then 0xdcb066905cc09990768093305580bca037002980b9004700303069b02490c9109c00551077309aa05b80b0a094205b001b8092903840e6007480e500a5c00d803f50cc10af1084901e00e180bdb0daa07c20db8019808190bc90d58053003bb01c40b1802500e3309b20bb30cbc0139095509810bd309b802030120005801bc else 0x3d30c4403ac01e80b3108990cec03b902d00b20016805d20e300cc40e28037b03e20014037101f106b80538003b08900c1c0a400eb80648044b0cc807c80bb803b400830a0008280bf20b300560043a03fb0ef805180305019000000693036902f905f40b6805490ecb00bb0b0206c80898071b0d7c08aa04f80c9905080ef0) else (if page < 15 then 0xc1004300b4809a001d10d010998069807f802440eb1056407b10aa003080cb0094b03d507b20eaa092001c0017a04c009610a94022806530b2b05c40891010202e806d505100a6a01180af80af003e903cd0c9c014209c80e5b0cf101780a1c0d3803da031007f0014a015105aa032007ba0bfa055c09100ad00db90db203fd else 0xad800010ea003510b880d73093a0f00045809bb0954070b07a80c02015a041a054004420b0b08ec06c9026d0f130bc00c40098002d80da20412081c01c9069004400b7808580cb80a5d041909180c12097905680a5105b108a20c6807d10aa80d8203f1021805d80278)))) else 0
  | 7 => if page < 1 then 0x1a003b002c00010018000a001b0011003a003200580052000800220050002900800040000c002800530078003300700048000900200014004200100030000d00000038004c000b004900430004006000680023 else 0
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
theorem root : pool 8 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 5 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x16 : span (checked 3) 16 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x32 : span (checked 3) 16 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x48 : span (checked 3) 3 48 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 51 0 = true :=
  (@span_join (checked 3) 32 0 19 (@span_join (checked 3) 16 0 16 chunk3x0 chunk3x16) (@span_join (checked 3) 16 32 3 chunk3x32 chunk3x48))

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
theorem chunk4x384 : span (checked 4) 16 384 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x400 : span (checked 4) 16 400 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x416 : span (checked 4) 16 416 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x432 : span (checked 4) 16 432 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x448 : span (checked 4) 16 448 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x464 : span (checked 4) 16 464 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x480 : span (checked 4) 16 480 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x496 : span (checked 4) 16 496 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x512 : span (checked 4) 16 512 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x528 : span (checked 4) 16 528 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x544 : span (checked 4) 16 544 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x560 : span (checked 4) 16 560 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x576 : span (checked 4) 16 576 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x592 : span (checked 4) 16 592 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x608 : span (checked 4) 16 608 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x624 : span (checked 4) 16 624 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x640 : span (checked 4) 16 640 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x656 : span (checked 4) 16 656 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x672 : span (checked 4) 16 672 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x688 : span (checked 4) 16 688 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x704 : span (checked 4) 16 704 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x720 : span (checked 4) 16 720 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x736 : span (checked 4) 16 736 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x752 : span (checked 4) 16 752 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x768 : span (checked 4) 16 768 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x784 : span (checked 4) 16 784 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x800 : span (checked 4) 16 800 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x816 : span (checked 4) 16 816 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x832 : span (checked 4) 16 832 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x848 : span (checked 4) 16 848 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x864 : span (checked 4) 16 864 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x880 : span (checked 4) 16 880 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x896 : span (checked 4) 16 896 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x912 : span (checked 4) 16 912 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x928 : span (checked 4) 16 928 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x944 : span (checked 4) 16 944 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x960 : span (checked 4) 16 960 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x976 : span (checked 4) 16 976 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x992 : span (checked 4) 16 992 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x1008 : span (checked 4) 16 1008 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x1024 : span (checked 4) 16 1024 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x1040 : span (checked 4) 16 1040 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x1056 : span (checked 4) 16 1056 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x1072 : span (checked 4) 16 1072 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x1088 : span (checked 4) 13 1088 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 1101 0 = true :=
  (@span_join (checked 4) 544 0 557 (@span_join (checked 4) 272 0 272 (@span_join (checked 4) 128 0 144 (@span_join (checked 4) 64 0 64 (@span_join (checked 4) 32 0 32 (@span_join (checked 4) 16 0 16 chunk4x0 chunk4x16) (@span_join (checked 4) 16 32 16 chunk4x32 chunk4x48)) (@span_join (checked 4) 32 64 32 (@span_join (checked 4) 16 64 16 chunk4x64 chunk4x80) (@span_join (checked 4) 16 96 16 chunk4x96 chunk4x112))) (@span_join (checked 4) 64 128 80 (@span_join (checked 4) 32 128 32 (@span_join (checked 4) 16 128 16 chunk4x128 chunk4x144) (@span_join (checked 4) 16 160 16 chunk4x160 chunk4x176)) (@span_join (checked 4) 32 192 48 (@span_join (checked 4) 16 192 16 chunk4x192 chunk4x208) (@span_join (checked 4) 16 224 32 chunk4x224 (@span_join (checked 4) 16 240 16 chunk4x240 chunk4x256))))) (@span_join (checked 4) 128 272 144 (@span_join (checked 4) 64 272 64 (@span_join (checked 4) 32 272 32 (@span_join (checked 4) 16 272 16 chunk4x272 chunk4x288) (@span_join (checked 4) 16 304 16 chunk4x304 chunk4x320)) (@span_join (checked 4) 32 336 32 (@span_join (checked 4) 16 336 16 chunk4x336 chunk4x352) (@span_join (checked 4) 16 368 16 chunk4x368 chunk4x384))) (@span_join (checked 4) 64 400 80 (@span_join (checked 4) 32 400 32 (@span_join (checked 4) 16 400 16 chunk4x400 chunk4x416) (@span_join (checked 4) 16 432 16 chunk4x432 chunk4x448)) (@span_join (checked 4) 32 464 48 (@span_join (checked 4) 16 464 16 chunk4x464 chunk4x480) (@span_join (checked 4) 16 496 32 chunk4x496 (@span_join (checked 4) 16 512 16 chunk4x512 chunk4x528)))))) (@span_join (checked 4) 272 544 285 (@span_join (checked 4) 128 544 144 (@span_join (checked 4) 64 544 64 (@span_join (checked 4) 32 544 32 (@span_join (checked 4) 16 544 16 chunk4x544 chunk4x560) (@span_join (checked 4) 16 576 16 chunk4x576 chunk4x592)) (@span_join (checked 4) 32 608 32 (@span_join (checked 4) 16 608 16 chunk4x608 chunk4x624) (@span_join (checked 4) 16 640 16 chunk4x640 chunk4x656))) (@span_join (checked 4) 64 672 80 (@span_join (checked 4) 32 672 32 (@span_join (checked 4) 16 672 16 chunk4x672 chunk4x688) (@span_join (checked 4) 16 704 16 chunk4x704 chunk4x720)) (@span_join (checked 4) 32 736 48 (@span_join (checked 4) 16 736 16 chunk4x736 chunk4x752) (@span_join (checked 4) 16 768 32 chunk4x768 (@span_join (checked 4) 16 784 16 chunk4x784 chunk4x800))))) (@span_join (checked 4) 144 816 141 (@span_join (checked 4) 64 816 80 (@span_join (checked 4) 32 816 32 (@span_join (checked 4) 16 816 16 chunk4x816 chunk4x832) (@span_join (checked 4) 16 848 16 chunk4x848 chunk4x864)) (@span_join (checked 4) 32 880 48 (@span_join (checked 4) 16 880 16 chunk4x880 chunk4x896) (@span_join (checked 4) 16 912 32 chunk4x912 (@span_join (checked 4) 16 928 16 chunk4x928 chunk4x944)))) (@span_join (checked 4) 64 960 77 (@span_join (checked 4) 32 960 32 (@span_join (checked 4) 16 960 16 chunk4x960 chunk4x976) (@span_join (checked 4) 16 992 16 chunk4x992 chunk4x1008)) (@span_join (checked 4) 32 1024 45 (@span_join (checked 4) 16 1024 16 chunk4x1024 chunk4x1040) (@span_join (checked 4) 16 1056 29 chunk4x1056 (@span_join (checked 4) 16 1072 13 chunk4x1072 chunk4x1088)))))))

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
theorem chunk5x912 : span (checked 5) 16 912 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x928 : span (checked 5) 16 928 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x944 : span (checked 5) 16 944 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x960 : span (checked 5) 16 960 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x976 : span (checked 5) 16 976 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x992 : span (checked 5) 16 992 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1008 : span (checked 5) 16 1008 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1024 : span (checked 5) 16 1024 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1040 : span (checked 5) 16 1040 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1056 : span (checked 5) 16 1056 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1072 : span (checked 5) 16 1072 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1088 : span (checked 5) 16 1088 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1104 : span (checked 5) 16 1104 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1120 : span (checked 5) 16 1120 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1136 : span (checked 5) 16 1136 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1152 : span (checked 5) 16 1152 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1168 : span (checked 5) 16 1168 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1184 : span (checked 5) 16 1184 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1200 : span (checked 5) 16 1200 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1216 : span (checked 5) 16 1216 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1232 : span (checked 5) 16 1232 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1248 : span (checked 5) 16 1248 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1264 : span (checked 5) 16 1264 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1280 : span (checked 5) 16 1280 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1296 : span (checked 5) 16 1296 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1312 : span (checked 5) 16 1312 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1328 : span (checked 5) 16 1328 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1344 : span (checked 5) 16 1344 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1360 : span (checked 5) 16 1360 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1376 : span (checked 5) 16 1376 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1392 : span (checked 5) 16 1392 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1408 : span (checked 5) 16 1408 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1424 : span (checked 5) 16 1424 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1440 : span (checked 5) 16 1440 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1456 : span (checked 5) 16 1456 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1472 : span (checked 5) 16 1472 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1488 : span (checked 5) 16 1488 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1504 : span (checked 5) 16 1504 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1520 : span (checked 5) 16 1520 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1536 : span (checked 5) 16 1536 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1552 : span (checked 5) 16 1552 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1568 : span (checked 5) 16 1568 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1584 : span (checked 5) 16 1584 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1600 : span (checked 5) 16 1600 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1616 : span (checked 5) 16 1616 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1632 : span (checked 5) 16 1632 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1648 : span (checked 5) 16 1648 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1664 : span (checked 5) 16 1664 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1680 : span (checked 5) 16 1680 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1696 : span (checked 5) 16 1696 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1712 : span (checked 5) 16 1712 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1728 : span (checked 5) 16 1728 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1744 : span (checked 5) 16 1744 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1760 : span (checked 5) 16 1760 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1776 : span (checked 5) 16 1776 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1792 : span (checked 5) 16 1792 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1808 : span (checked 5) 16 1808 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1824 : span (checked 5) 16 1824 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1840 : span (checked 5) 16 1840 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1856 : span (checked 5) 16 1856 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1872 : span (checked 5) 16 1872 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1888 : span (checked 5) 16 1888 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1904 : span (checked 5) 16 1904 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1920 : span (checked 5) 16 1920 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1936 : span (checked 5) 16 1936 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1952 : span (checked 5) 16 1952 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1968 : span (checked 5) 16 1968 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x1984 : span (checked 5) 16 1984 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2000 : span (checked 5) 16 2000 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2016 : span (checked 5) 16 2016 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2032 : span (checked 5) 16 2032 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2048 : span (checked 5) 16 2048 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2064 : span (checked 5) 16 2064 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2080 : span (checked 5) 16 2080 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2096 : span (checked 5) 16 2096 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2112 : span (checked 5) 16 2112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2128 : span (checked 5) 16 2128 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2144 : span (checked 5) 16 2144 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2160 : span (checked 5) 16 2160 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2176 : span (checked 5) 16 2176 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2192 : span (checked 5) 16 2192 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2208 : span (checked 5) 16 2208 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x2224 : span (checked 5) 11 2224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 2235 0 = true :=
  (@span_join (checked 5) 1120 0 1115 (@span_join (checked 5) 560 0 560 (@span_join (checked 5) 272 0 288 (@span_join (checked 5) 128 0 144 (@span_join (checked 5) 64 0 64 (@span_join (checked 5) 32 0 32 (@span_join (checked 5) 16 0 16 chunk5x0 chunk5x16) (@span_join (checked 5) 16 32 16 chunk5x32 chunk5x48)) (@span_join (checked 5) 32 64 32 (@span_join (checked 5) 16 64 16 chunk5x64 chunk5x80) (@span_join (checked 5) 16 96 16 chunk5x96 chunk5x112))) (@span_join (checked 5) 64 128 80 (@span_join (checked 5) 32 128 32 (@span_join (checked 5) 16 128 16 chunk5x128 chunk5x144) (@span_join (checked 5) 16 160 16 chunk5x160 chunk5x176)) (@span_join (checked 5) 32 192 48 (@span_join (checked 5) 16 192 16 chunk5x192 chunk5x208) (@span_join (checked 5) 16 224 32 chunk5x224 (@span_join (checked 5) 16 240 16 chunk5x240 chunk5x256))))) (@span_join (checked 5) 144 272 144 (@span_join (checked 5) 64 272 80 (@span_join (checked 5) 32 272 32 (@span_join (checked 5) 16 272 16 chunk5x272 chunk5x288) (@span_join (checked 5) 16 304 16 chunk5x304 chunk5x320)) (@span_join (checked 5) 32 336 48 (@span_join (checked 5) 16 336 16 chunk5x336 chunk5x352) (@span_join (checked 5) 16 368 32 chunk5x368 (@span_join (checked 5) 16 384 16 chunk5x384 chunk5x400)))) (@span_join (checked 5) 64 416 80 (@span_join (checked 5) 32 416 32 (@span_join (checked 5) 16 416 16 chunk5x416 chunk5x432) (@span_join (checked 5) 16 448 16 chunk5x448 chunk5x464)) (@span_join (checked 5) 32 480 48 (@span_join (checked 5) 16 480 16 chunk5x480 chunk5x496) (@span_join (checked 5) 16 512 32 chunk5x512 (@span_join (checked 5) 16 528 16 chunk5x528 chunk5x544)))))) (@span_join (checked 5) 272 560 288 (@span_join (checked 5) 128 560 144 (@span_join (checked 5) 64 560 64 (@span_join (checked 5) 32 560 32 (@span_join (checked 5) 16 560 16 chunk5x560 chunk5x576) (@span_join (checked 5) 16 592 16 chunk5x592 chunk5x608)) (@span_join (checked 5) 32 624 32 (@span_join (checked 5) 16 624 16 chunk5x624 chunk5x640) (@span_join (checked 5) 16 656 16 chunk5x656 chunk5x672))) (@span_join (checked 5) 64 688 80 (@span_join (checked 5) 32 688 32 (@span_join (checked 5) 16 688 16 chunk5x688 chunk5x704) (@span_join (checked 5) 16 720 16 chunk5x720 chunk5x736)) (@span_join (checked 5) 32 752 48 (@span_join (checked 5) 16 752 16 chunk5x752 chunk5x768) (@span_join (checked 5) 16 784 32 chunk5x784 (@span_join (checked 5) 16 800 16 chunk5x800 chunk5x816))))) (@span_join (checked 5) 144 832 144 (@span_join (checked 5) 64 832 80 (@span_join (checked 5) 32 832 32 (@span_join (checked 5) 16 832 16 chunk5x832 chunk5x848) (@span_join (checked 5) 16 864 16 chunk5x864 chunk5x880)) (@span_join (checked 5) 32 896 48 (@span_join (checked 5) 16 896 16 chunk5x896 chunk5x912) (@span_join (checked 5) 16 928 32 chunk5x928 (@span_join (checked 5) 16 944 16 chunk5x944 chunk5x960)))) (@span_join (checked 5) 64 976 80 (@span_join (checked 5) 32 976 32 (@span_join (checked 5) 16 976 16 chunk5x976 chunk5x992) (@span_join (checked 5) 16 1008 16 chunk5x1008 chunk5x1024)) (@span_join (checked 5) 32 1040 48 (@span_join (checked 5) 16 1040 16 chunk5x1040 chunk5x1056) (@span_join (checked 5) 16 1072 32 chunk5x1072 (@span_join (checked 5) 16 1088 16 chunk5x1088 chunk5x1104))))))) (@span_join (checked 5) 560 1120 555 (@span_join (checked 5) 272 1120 288 (@span_join (checked 5) 128 1120 144 (@span_join (checked 5) 64 1120 64 (@span_join (checked 5) 32 1120 32 (@span_join (checked 5) 16 1120 16 chunk5x1120 chunk5x1136) (@span_join (checked 5) 16 1152 16 chunk5x1152 chunk5x1168)) (@span_join (checked 5) 32 1184 32 (@span_join (checked 5) 16 1184 16 chunk5x1184 chunk5x1200) (@span_join (checked 5) 16 1216 16 chunk5x1216 chunk5x1232))) (@span_join (checked 5) 64 1248 80 (@span_join (checked 5) 32 1248 32 (@span_join (checked 5) 16 1248 16 chunk5x1248 chunk5x1264) (@span_join (checked 5) 16 1280 16 chunk5x1280 chunk5x1296)) (@span_join (checked 5) 32 1312 48 (@span_join (checked 5) 16 1312 16 chunk5x1312 chunk5x1328) (@span_join (checked 5) 16 1344 32 chunk5x1344 (@span_join (checked 5) 16 1360 16 chunk5x1360 chunk5x1376))))) (@span_join (checked 5) 144 1392 144 (@span_join (checked 5) 64 1392 80 (@span_join (checked 5) 32 1392 32 (@span_join (checked 5) 16 1392 16 chunk5x1392 chunk5x1408) (@span_join (checked 5) 16 1424 16 chunk5x1424 chunk5x1440)) (@span_join (checked 5) 32 1456 48 (@span_join (checked 5) 16 1456 16 chunk5x1456 chunk5x1472) (@span_join (checked 5) 16 1488 32 chunk5x1488 (@span_join (checked 5) 16 1504 16 chunk5x1504 chunk5x1520)))) (@span_join (checked 5) 64 1536 80 (@span_join (checked 5) 32 1536 32 (@span_join (checked 5) 16 1536 16 chunk5x1536 chunk5x1552) (@span_join (checked 5) 16 1568 16 chunk5x1568 chunk5x1584)) (@span_join (checked 5) 32 1600 48 (@span_join (checked 5) 16 1600 16 chunk5x1600 chunk5x1616) (@span_join (checked 5) 16 1632 32 chunk5x1632 (@span_join (checked 5) 16 1648 16 chunk5x1648 chunk5x1664)))))) (@span_join (checked 5) 272 1680 283 (@span_join (checked 5) 128 1680 144 (@span_join (checked 5) 64 1680 64 (@span_join (checked 5) 32 1680 32 (@span_join (checked 5) 16 1680 16 chunk5x1680 chunk5x1696) (@span_join (checked 5) 16 1712 16 chunk5x1712 chunk5x1728)) (@span_join (checked 5) 32 1744 32 (@span_join (checked 5) 16 1744 16 chunk5x1744 chunk5x1760) (@span_join (checked 5) 16 1776 16 chunk5x1776 chunk5x1792))) (@span_join (checked 5) 64 1808 80 (@span_join (checked 5) 32 1808 32 (@span_join (checked 5) 16 1808 16 chunk5x1808 chunk5x1824) (@span_join (checked 5) 16 1840 16 chunk5x1840 chunk5x1856)) (@span_join (checked 5) 32 1872 48 (@span_join (checked 5) 16 1872 16 chunk5x1872 chunk5x1888) (@span_join (checked 5) 16 1904 32 chunk5x1904 (@span_join (checked 5) 16 1920 16 chunk5x1920 chunk5x1936))))) (@span_join (checked 5) 144 1952 139 (@span_join (checked 5) 64 1952 80 (@span_join (checked 5) 32 1952 32 (@span_join (checked 5) 16 1952 16 chunk5x1952 chunk5x1968) (@span_join (checked 5) 16 1984 16 chunk5x1984 chunk5x2000)) (@span_join (checked 5) 32 2016 48 (@span_join (checked 5) 16 2016 16 chunk5x2016 chunk5x2032) (@span_join (checked 5) 16 2048 32 chunk5x2048 (@span_join (checked 5) 16 2064 16 chunk5x2064 chunk5x2080)))) (@span_join (checked 5) 64 2096 75 (@span_join (checked 5) 32 2096 32 (@span_join (checked 5) 16 2096 16 chunk5x2096 chunk5x2112) (@span_join (checked 5) 16 2128 16 chunk5x2128 chunk5x2144)) (@span_join (checked 5) 32 2160 43 (@span_join (checked 5) 16 2160 16 chunk5x2160 chunk5x2176) (@span_join (checked 5) 16 2192 27 chunk5x2192 (@span_join (checked 5) 16 2208 11 chunk5x2208 chunk5x2224))))))))

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
theorem chunk6x480 : span (checked 6) 3 480 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 483 0 = true :=
  (@span_join (checked 6) 240 0 243 (@span_join (checked 6) 112 0 128 (@span_join (checked 6) 48 0 64 (@span_join (checked 6) 16 0 32 chunk6x0 (@span_join (checked 6) 16 16 16 chunk6x16 chunk6x32)) (@span_join (checked 6) 32 48 32 (@span_join (checked 6) 16 48 16 chunk6x48 chunk6x64) (@span_join (checked 6) 16 80 16 chunk6x80 chunk6x96))) (@span_join (checked 6) 64 112 64 (@span_join (checked 6) 32 112 32 (@span_join (checked 6) 16 112 16 chunk6x112 chunk6x128) (@span_join (checked 6) 16 144 16 chunk6x144 chunk6x160)) (@span_join (checked 6) 32 176 32 (@span_join (checked 6) 16 176 16 chunk6x176 chunk6x192) (@span_join (checked 6) 16 208 16 chunk6x208 chunk6x224)))) (@span_join (checked 6) 128 240 115 (@span_join (checked 6) 64 240 64 (@span_join (checked 6) 32 240 32 (@span_join (checked 6) 16 240 16 chunk6x240 chunk6x256) (@span_join (checked 6) 16 272 16 chunk6x272 chunk6x288)) (@span_join (checked 6) 32 304 32 (@span_join (checked 6) 16 304 16 chunk6x304 chunk6x320) (@span_join (checked 6) 16 336 16 chunk6x336 chunk6x352))) (@span_join (checked 6) 64 368 51 (@span_join (checked 6) 32 368 32 (@span_join (checked 6) 16 368 16 chunk6x368 chunk6x384) (@span_join (checked 6) 16 400 16 chunk6x400 chunk6x416)) (@span_join (checked 6) 32 432 19 (@span_join (checked 6) 16 432 16 chunk6x432 chunk6x448) (@span_join (checked 6) 16 464 3 chunk6x464 chunk6x480)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x16 : span (checked 7) 1 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 17 0 = true :=
  (@span_join (checked 7) 16 0 1 chunk7x0 chunk7x16)

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

end PEqualNP.Outside.L_meta_12264_aux

open PEqualNP.Outside.L_meta_12264_aux

theorem PEqualNP.Outside.L_meta_12264 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860992 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860992 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s existsC
  obtain ⟨C,ok,bound,hit⟩ := existsC
  obtain ⟨D,mono,small,evaluates⟩ := ThresholdReplacement.replacement
    (TableLink.sliceRequirement SignedFrontier.CliqueLink.lower) C ok hit
  exact ⟨D,mono,small.trans bound,evaluates⟩
