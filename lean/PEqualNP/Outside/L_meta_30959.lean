import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30959_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenSignedSlice

abbrev Signal (α : Type) := α → Bool
def inv {α} (a : Signal α) : Signal α := fun x => !(a x)
def meet {α} (a b : Signal α) : Signal α := fun x => a x && b x

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

namespace GraphSignedFrontier

abbrev W := BitVec 128

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

theorem same_choice (a b w : W) (hw : w ∈ choices a b) (i j : ℕ) (hi : i < 128) (hj : j < 128)
    (ha : a.getLsbD i = a.getLsbD j) (hb : b.getLsbD i = b.getLsbD j) :
    w.getLsbD i = w.getLsbD j := by
  simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_or,hi,hj,decide_true,
      Bool.true_and,ha,hb]

theorem Cone.agree {g : W} {k : ℕ} {s : Finset W} (h : Cone g k s)
    (i j : ℕ) (hi : i < 128) (hj : j < 128)
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

theorem survivor_sound (r j : ℕ) (hj : j < 128) (s : List W) (m : W)
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
    (rows : List ℕ) (neg : ∀ r ∈ rows, r < 128 ∧ g.getLsbD r = false) :
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
    (neg : ∀ r ∈ rows, r < 128 ∧ g.getLsbD r = false)
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
  ∀ w ∈ raws, ∃ i j : Fin 128, g.getLsbD i.val ≠ g.getLsbD j.val ∧
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
    (rows : List ℕ) (neg : ∀ r ∈ rows, r < 128 ∧ g.getLsbD r = false) (ess : Essential g raws)
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
  ∀ r : Fin 128, ¬ (s.low.getLsbD r.val = true ∧ s.high.getLsbD r.val = true) ∧
    (s.high.getLsbD r.val = true → s.distance ≤ r.val) ∧
    s.source r.val < 128 ∧ s.source (s.source r.val) = r.val

theorem Switch.read (s : Switch) (ok : s.Valid) (w : W) (r : ℕ) (hr : r < 128) :
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
  | nil => simpa [GraphSignedFrontier.reindex] using h
  | cons op tail ih =>
    have step := h.switched op (ok _ List.mem_cons_self)
    have result := ih step (fun u hu => ok u (List.mem_cons_of_mem _ hu))
    simpa only [GraphSignedFrontier.reindex,Finset.image_image,Function.comp_def] using result

def found (words : ℕ → ℕ → List W) (count : ℕ → ℕ)
    (lookup : ℕ → List W → ℕ × ℕ) (sym : ℕ → List Switch) (k : ℕ) (s : List W) :=
  let (i,j) := lookup k s
  decide (i < count k) && (s.map (reindex (sym j))).isPerm (words k i)

end GraphSignedFrontier

namespace GraphSignedFrontier

set_option maxRecDepth 2200 in
def rowMap (f : Fin 128 → Fin 128) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun r : Fin 128 => w.getLsbD (f r).val))).cast (by simp)

set_option maxRecDepth 2200 in
theorem rowMap_read (f : Fin 128 → Fin 128) (w : W) (r : Fin 128) :
    (rowMap f w).getLsbD r.val = w.getLsbD (f r).val := by
  simp only [rowMap, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]

set_option maxRecDepth 2200 in
theorem rowMap_form (f : Fin 128 → Fin 128) (a b w : W) (h : w ∈ choices a b) :
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

set_option maxRecDepth 2200 in
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

end GraphSignedFrontier

namespace GraphSignedFrontier

def signedMap (f : Fin 128 → Fin 128) (w : W) := canonical (rowMap f w)

theorem canonical_choice (a b w : W) (h : w ∈ choices a b) :
    canonical w ∈ choices (canonical a) (canonical b) := by
  simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact operation a b
  · simpa only [canonical_not] using operation a (~~~b)
  · simpa only [canonical_not] using operation (~~~a) b
  · simpa only [BitVec.not_and,BitVec.not_not,← BitVec.not_or,canonical_not] using
      operation (~~~a) (~~~b)

theorem signedMap_choice (f : Fin 128 → Fin 128) (a b w : W) (h : w ∈ choices a b) :
    signedMap f w ∈ choices (signedMap f a) (signedMap f b) :=
  canonical_choice _ _ _ (rowMap_form f a b w h)

def signedLower (g : W) (raw : List W) (n : Nat) : Prop :=
  ∀ {k : Nat} {s : Finset W}, Cone g k s → s ⊆ insert 0 raw.toFinset → n ≤ k

def cofactorReject (f : Fin 128 → Fin 128) (raw : List W) (n budget : Nat) (s : List W) : Bool :=
  let ws := s.map (signedMap f)
  ws.all (fun w => w == 0 || raw.contains w) &&
    (decide (budget < n) || (decide (budget ≤ n) && ws.contains 0))

theorem cofactorReject_sound (f : Fin 128 → Fin 128) (g : W) (raw : List W) (n budget : Nat)
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

end GraphSignedFrontier

namespace GraphSignedFrontier

theorem signedMap_eq_of_mask (f : Fin 128 → Fin 128) (mask a b : W)
    (covers : ∀ i, mask.getLsbD (f i).val = true)
    (eq : a &&& mask = b &&& mask) : signedMap f a = signedMap f b := by
  apply congrArg canonical
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin 128 := ⟨i, hi⟩
  change (rowMap f a).getLsbD r.val = (rowMap f b).getLsbD r.val
  rw [rowMap_read, rowMap_read]
  simpa only [BitVec.getLsbD_and, covers, Bool.and_true] using
    congrArg (fun w : W => w.getLsbD (f r).val) eq

theorem signedMap_zero (f : Fin 128 → Fin 128) : signedMap f 0 = 0 := by
  have h : rowMap f 0 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact (rowMap_read f 0 ⟨i,hi⟩).trans (by simp)
  rw [signedMap, h]
  rfl

theorem signedMap_ones (f : Fin 128 → Fin 128) : signedMap f (~~~0) = 0 := by
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

theorem maskedCut_sound (f : Fin 128 → Fin 128) (mask : W) (patterns base raw : List W)
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
            change w &&& mask = BitVec.allOnes 128 &&& mask
            rw [BitVec.allOnes_and]
            simpa using hi
          exact (signedMap_eq_of_mask f mask w _ covers eq).trans (signedMap_ones f)
      apply Bool.or_eq_true_iff.mpr
      refine Or.inr (Bool.and_eq_true_iff.mpr ⟨h, ?_⟩)
      simpa [List.contains_eq_mem] using (List.mem_map.mpr ⟨w,hw,z⟩ : (0 : W) ∈ s.map (signedMap f))
  rw [cofactorReject_sound f g raw bound budget nz low s le run] at yes
  contradiction

structure CutCertificate (g : W) where
  mask : W
  patterns : List W
  bound : Nat
  sound : ∀ budget s {k}, k ≤ budget → Cone g k s.toFinset →
    maskedCut mask patterns bound budget s = false

def makeCutCertificate (g goal mask : W) (rows : Nat) (dimension bound : Nat)
    (base patterns raw : List W) (nz : goal ≠ 0) (low : signedLower goal raw bound)
    (f : Fin 128 → Fin 128 := fun r => ⟨(rows >>> (7 * (r.val % 2^dimension))) % 128,
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

end GraphSignedFrontier

namespace GraphSignedFrontier

def feasibleWith (g : W) (rows : List ℕ) (reject : ℕ → List W → Bool) : ℕ → List W → Bool
  | 0, s => s.contains g
  | k+1, s => s.contains g ||
    (decide (s.length ≤ k+2) && covered g rows s && !reject (k+1) s &&
      moves s (feasibleWith g rows reject k))

theorem feasibleWith_complete {g : W} (hg : g ≠ 0) (rows : List ℕ)
    (neg : ∀ r ∈ rows, r < 128 ∧ g.getLsbD r = false) (reject : ℕ → List W → Bool)
    (safe : ∀ budget s {k}, k ≤ budget → Cone g k s.toFinset → reject budget s = false)
    (cap : ℕ) (s : List W) (unique : s.Nodup) (k : ℕ) (bound : k ≤ cap) (h : Cone g k s.toFinset) :
    feasibleWith g rows reject cap s = true := by
  induction cap generalizing k s with
  | zero =>
    have hz : k = 0 := by omega
    subst k
    have final {t : Finset W} (c : Cone g 0 t) : g ∈ t := by cases c; simp
    simpa [feasibleWith] using final h
  | succ cap ih =>
    simp only [feasibleWith,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    cases k with
    | zero =>
      left
      have final {t : Finset W} (c : Cone g 0 t) : g ∈ t := by cases c; simp
      simpa using final h
    | succ k =>
      right
      have size := h.size
      rw [List.toFinset_card_of_nodup unique] at size
      refine ⟨⟨⟨by omega,h.covered rows neg⟩,by simp [safe _ _ bound h]⟩,?_⟩
      exact moves_complete _ _ hg unique h rfl (fun t nd ht => ih t nd k (by omega) ht)

theorem lowerWith (g : W) (hg : g ≠ 0) (raw : List W) (unique : raw.Nodup)
    (essential : Essential g raw) (rows : List ℕ) (neg : ∀ r ∈ rows, r < 128 ∧ g.getLsbD r = false)
    (reject : ℕ → List W → Bool)
    (safe : ∀ budget s {k}, k ≤ budget → Cone g k s.toFinset → reject budget s = false)
    (cap : ℕ) (checked : feasibleWith g rows reject cap raw = false) :
    signedLower g raw (cap+1) := by
  intro k s cone sub
  by_contra! short
  have ini := cone.initial hg raw essential sub
  rw [ini] at cone
  have yes := feasibleWith_complete hg rows neg reject safe cap raw unique k (by omega) cone
  simp [checked] at yes

end GraphSignedFrontier

namespace GraphSignedFrontier

namespace GraphSeven

def target : W := 0xfffffffefffefffefffffefafefaeca0
def raw : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]
def negative : List ℕ := [0, 1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 32, 34, 40, 64, 80, 96]

theorem positive : target ≠ 0 := by decide +kernel
theorem unique : raw.Nodup := by decide +kernel

theorem neg : ∀ r ∈ negative, r < 128 ∧ target.getLsbD r = false := by
  intro r hr
  have yes : (negative.all fun j => decide (j < 128 ∧ target.getLsbD j = false)) = true := by decide +kernel
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp yes r hr

theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨4,5,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : W) ∨ z.getLsbD 4 = z.getLsbD 5)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨8,10,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xcccccccccccccccccccccccccccccccc : W) ∨ z.getLsbD 8 = z.getLsbD 10)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : W) ∨ z.getLsbD 1 = z.getLsbD 5)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨2,10,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xff00ff00ff00ff00ff00ff00ff00ff00 : W) ∨ z.getLsbD 2 = z.getLsbD 10)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,17,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffff0000ffff0000ffff0000ffff0000 : W) ∨ z.getLsbD 1 = z.getLsbD 17)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,33,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffffffff00000000ffffffff00000000 : W) ∨ z.getLsbD 1 = z.getLsbD 33)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,65,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffffffffffffffff0000000000000000 : W) ∨ z.getLsbD 1 = z.getLsbD 65)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd

def projectZero (v : Fin 6) (r : Fin 128) : Fin 128 :=
  let x := r.val % 64
  let p := 2 ^ v.val
  Fin.ofNat 128 (x % p + (x / p) * (2*p))

def maskZero (v : Fin 6) : W := ~~~(raw.getD v.val 0)
def base : List W := [0, ~~~(0 : W)] ++ raw ++ raw.map (fun w => ~~~w)
def patterns (v : Fin 6) : List W := base.map (· &&& maskZero v)

def leafRaw : List W := raw.take 6
def cut (budget : ℕ) (s : List W) : Bool :=
  (List.finRange 6).any fun v => maskedCut (maskZero v) (patterns v) 10 budget s

set_option maxHeartbeats 0 in
theorem checked : feasibleWith target negative cut 11 raw = false := by decide +kernel

end GraphSeven

end GraphSignedFrontier

namespace GraphSignedFrontier.GraphSeven

def goals : List W := [0xfffefefeffececa0fffefefeffececa0, 0xfffefefeffeeee88fffefefeffeeee88, 0xfffefefeffeaeac0fffefefeffeaeac0, 0xfffefefefffafaa0fffefefefffafaa0, 0xfffefffefefaeca0fffefffefefaeca0, 0xfffefffefefaeca0fffefffefefaeca0]
def leafGoal (v : Fin 6) : W := goals.getD v.val 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem covers (v : Fin 6) (r : Fin 128) : (maskZero v).getLsbD (projectZero v r).val = true :=
  (show ∀ v : Fin 6, ∀ r : Fin 128, (maskZero v).getLsbD (projectZero v r).val = true by decide +kernel) v r

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem aligned (v : Fin 6) : signedMap (projectZero v) target = leafGoal v :=
  (show ∀ v : Fin 6, signedMap (projectZero v) target = leafGoal v by decide +kernel) v

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem stock (v : Fin 6) (w : W) (hw : w ∈ base) :
    signedMap (projectZero v) w = 0 ∨ signedMap (projectZero v) w ∈ leafRaw := by
  have success : ∀ v : Fin 6, (base.all fun w => decide (signedMap (projectZero v) w = 0 ∨
      signedMap (projectZero v) w ∈ leafRaw)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp (success v) w hw)

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem nonzero (v : Fin 6) : signedMap (projectZero v) target ≠ 0 := by
  rw [aligned]
  exact (show ∀ v : Fin 6, leafGoal v ≠ 0 by decide +kernel) v

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem rejectSafe (lower : ∀ v : Fin 6, signedLower (leafGoal v) leafRaw 10)
    (budget : ℕ) (s : List W) {k} (le : k ≤ budget) (cone : Cone target k s.toFinset) :
    cut budget s = false := by
  by_contra! no
  have yes : cut budget s = true := by simpa using no
  obtain ⟨v,_,tripped⟩ := List.any_eq_true.mp yes
  have h : signedLower (signedMap (projectZero v) target) leafRaw 10 := by rw [aligned]; exact lower v
  have reject := maskedCut_sound (projectZero v) (maskZero v) (patterns v) base leafRaw
    target 10 budget s (covers v) rfl (stock v) (nonzero v) h le cone
  simp [reject] at tripped

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem lowerFromLeaves (lower : ∀ v : Fin 6, signedLower (leafGoal v) leafRaw 10) :
    signedLower target raw 12 :=
  lowerWith target positive raw unique essential negative neg cut (rejectSafe lower) 11 checked

end GraphSignedFrontier.GraphSeven

namespace OneNot30959
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List ℕ := [0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7]

def posted (x : Fin 8 → Bool) : Bool := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def witness : List Gate := [
  ⟨.or, [0, 3]⟩,
  ⟨.or, [8, 2]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.or, [10, 7]⟩,
  ⟨.and, [9, 11]⟩,
  ⟨.and, [0, 3]⟩,
  ⟨.and, [5, 6]⟩,
  ⟨.and, [1, 4]⟩,
  ⟨.or, [1, 4]⟩,
  ⟨.and, [7, 16]⟩,
  ⟨.or, [12, 13]⟩,
  ⟨.or, [14, 18]⟩,
  ⟨.or, [15, 17]⟩,
  ⟨.or, [19, 20]⟩
]

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem witness_size : witness.length = 14 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem witness_legal : ∀ g ∈ witness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;>
    first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem witness_eval : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨witness, 21⟩ (List.ofFn x) = posted x := by decide +kernel

abbrev Input := Fin 7 → Bool

def lift (x : Input) (j : Fin 8) : Bool :=
  Fin.cases false x (Equiv.swap (1 : Fin 8) 2 (Equiv.swap (0 : Fin 8) 2 j))

def restriction (x : Input) : Bool := posted (lift x)

def signedStart (x : Input) : List Bool := [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not

def signed (p : List (ℕ × ℕ)) (o : ℕ) (x : Input) : Bool :=
  (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem restrict (C : Circuit) (ok : FanInTwo C)
    (hit : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = posted x) :
    ∃ p o, p.length < (C.gates.map PetersenSignedSlice.Paid).sum ∧
      ∀ x, signed p o x = restriction x := by
  let raw := List.ofFn (fun j : Fin 7 => fun x : Input => x j)
  let pool := [(fun _ : Input => false), (fun _ : Input => true)] ++ raw ++
    raw.map (fun u x => !(u x))
  let pin := fun j : Fin 8 => (fun x : Input => lift x j, decide (j = 5), decide (j = 2 ∨ j = 5))
  let v := List.ofFn pin
  have constants (b : Bool) : (fun _ : Input => b) ∈ pool := by cases b <;> simp [pool]
  have pins : ∀ a ∈ v, a.1 ∈ pool ∧ (fun x => !(a.1 x)) ∈ pool ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2) := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    change (fun x : Input => lift x j) ∈ pool ∧
      (fun x : Input => !(lift x j)) ∈ pool ∧
      ((∃ b, ∀ x : Input, lift x j = b) ∨ decide (j = 5) = decide (j = 2 ∨ j = 5))
    unfold lift
    cases h : Equiv.swap (1 : Fin 8) 2 (Equiv.swap (0 : Fin 8) 2 j) using Fin.cases with
    | zero => exact ⟨constants false, constants true, Or.inl ⟨false, fun _ => rfl⟩⟩
    | succ i =>
      have pos : (fun x : Input => x i) ∈ raw := List.mem_ofFn.mpr ⟨i,rfl⟩
      refine ⟨List.mem_append_left _ (List.mem_append_right _ pos),
        List.mem_append_right _ (List.mem_map_of_mem pos), Or.inr ?_⟩
      have ne : j ≠ 2 := by
        intro this
        subst j
        have zero : Equiv.swap (1 : Fin 8) 2 (Equiv.swap (0 : Fin 8) 2 2) = 0 := by decide +kernel
        exact Fin.succ_ne_zero i (h.symm.trans zero)
      simp [ne]
  have slice (x : Input) : C.eval (v.map fun a => a.1 x) = restriction x := by
    simpa [v, pin, restriction, List.map_ofFn, Function.comp_def] using hit (lift x)
  have varies : ¬ ∃ b : Bool, ∀ x : Input, C.eval (v.map fun a => a.1 x) = b := by
    rintro ⟨b,h⟩
    have first := (slice (fun _ => false)).symm.trans (h _)
    have second := (slice (fun _ => true)).symm.trans (h _)
    exact (by decide +kernel : restriction (fun _ => false) ≠ restriction (fun _ => true))
      (first.trans second.symm)
  have diff : C.eval (v.map fun a => a.2.1) ≠ C.eval (v.map fun a => a.2.2) := by
    have a := hit (fun j => decide (j = 5))
    have b := hit (fun j => decide (j = 2 ∨ j = 5))
    simp only [v,pin,List.map_ofFn,Function.comp_def] at a b ⊢
    rw [a,b]
    decide +kernel
  obtain ⟨p,o,small,eval⟩ := PetersenSignedSlice.compile Input C ok pool v constants pins varies diff
  refine ⟨p,o,small,fun x => ?_⟩
  change (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false = restriction x
  have start : pool.map (fun u => u x) = signedStart x := by
    simp only [pool,raw,signedStart,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  rw [← start]
  exact (eval x).trans (slice x)

open GraphSignedFrontier
open GraphSignedFrontier.GraphSeven (leafGoal leafRaw)

def assignment (r : Fin 128) (v : Fin 7) : Bool := r.val.testBit v.val
def rawWords : List W := [0, ~~~(0 : W)] ++ GraphSeven.raw ++ GraphSeven.raw.map (fun w => ~~~w)

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem rawTable : ∀ r : Fin 128, rawWords.map (fun u => u.getLsbD r.val) =
    signedStart (assignment r) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem goalTable : ∀ r : Fin 128, GraphSeven.target.getLsbD r.val =
    restriction (assignment r) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem readDefault (xs : List W) (j r : ℕ) :
    (xs.getD j 0).getLsbD r = (xs.map (fun u => u.getLsbD r)).getD j false := by
  by_cases hj : j < xs.length
  · rw [List.getD_eq_getElem _ _ hj,List.getD_eq_getElem _ _ (by simpa using hj)]
    simp
  · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp; omega)]
    simp

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem addRow (xs : List W) (ij : ℕ × ℕ) (r : ℕ) (hr : r < 128) :
    (add xs ij).map (fun u => u.getLsbD r) =
      PetersenSignedSlice.addPair (xs.map (fun u => u.getLsbD r)) ij := by
  simp only [add,PetersenSignedSlice.addPair,List.map_append,List.map_cons,List.map_nil,
      BitVec.getLsbD_and,BitVec.getLsbD_not,hr,decide_true,Bool.true_and,readDefault]

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem foldRow (p : List (ℕ × ℕ)) (xs : List W) (r : Fin 128) :
    (p.foldl add xs).map (fun u => u.getLsbD r.val) =
      p.foldl PetersenSignedSlice.addPair (xs.map (fun u => u.getLsbD r.val)) := by
  induction p generalizing xs with
  | nil => rfl
  | cons ij tail ih =>
    simp only [List.foldl_cons,ih,addRow _ _ _ r.isLt]

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem wordOfSolution (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : ∀ x, signed p o x = restriction x) :
    canonical (evaluate p rawWords o) = GraphSeven.target := by
  have eq : evaluate p rawWords o = GraphSeven.target := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Fin 128 := ⟨i,hi⟩
    change ((p.foldl add rawWords).getD o 0).getLsbD r.val = _
    rw [readDefault,foldRow p rawWords r,rawTable r]
    exact (hit (assignment r)).trans (goalTable r).symm
  rw [eq]
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem programBound (leaves : ∀ v : Fin 6, signedLower (leafGoal v) leafRaw 10)
    (p : List (ℕ × ℕ)) (o : ℕ) (rep : ∀ x, signed p o x = restriction x) : 12 ≤ p.length := by
  have hit := wordOfSolution p o rep
  have sub : {GraphSeven.target} ⊆ available (p.foldl add rawWords) := by
    apply Finset.singleton_subset_iff.mpr
    rw [← hit]
    exact available_read _ _
  obtain ⟨k,s,cap,stock,run⟩ := extract p rawWords GraphSeven.target 0 {GraphSeven.target} Cone.done sub
  have start : available rawWords = insert 0 GraphSeven.raw.toFinset := by decide +kernel
  rw [start] at stock
  have enough := GraphSeven.lowerFromLeaves leaves run stock
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem paidFacts (gs : List Gate) :
    (gs.map PetersenSignedSlice.Paid).sum ≤ gs.length ∧
    ((gs.map PetersenSignedSlice.Paid).sum = gs.length → ∀ g ∈ gs,
      (g.op = .and ∨ g.op = .or ∨ g.op = .not) → (g.op = .and ∨ g.op = .or)) := by
  induction gs with
  | nil => simp
  | cons g t ih =>
    have cap : PetersenSignedSlice.Paid g ≤ 1 := by
      unfold PetersenSignedSlice.Paid
      split <;> (first | decide | split <;> decide)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have tail := ih.1
    refine ⟨by omega, ?_⟩
    intro eq u mem kind
    rcases List.mem_cons.mp mem with rfl | small
    · rcases kind with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · simp [PetersenSignedSlice.Paid, h, GateOp.eval] at eq
        omega
    · exact ih.2 (by omega) _ small kind

set_option maxHeartbeats 0 in
set_option maxRecDepth 3000 in
theorem replacement (leaves : ∀ v : Fin 6, signedLower (leafGoal v) leafRaw 10)
    (gates : List Gate) (o : ℕ) (legal : ∀ g ∈ gates,
      (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hit : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = posted x) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧
      g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates',o'⟩ (List.ofFn x) = posted x := by
  by_cases mono : ∀ g ∈ gates, g.op = .and ∨ g.op = .or
  · exact ⟨gates,o,fun g h => ⟨mono g h,(legal g h).2⟩,le_rfl,hit⟩
  · obtain ⟨p,out,save,table⟩ := restrict ⟨gates,o⟩ legal hit
    change p.length < (gates.map PetersenSignedSlice.Paid).sum at save
    obtain ⟨cap, plain⟩ := paidFacts gates
    have pad : (gates.map PetersenSignedSlice.Paid).sum < gates.length := by
      by_contra! h
      apply mono
      intro g hg
      exact plain (by omega) _ hg (legal _ hg).1
    have floor := programBound leaves p out table
    exact ⟨witness,21,witness_legal,by rw [witness_size]; omega,witness_eval⟩

end OneNot30959

namespace GraphSignedFrontier

def OnePrep (raw : Finset W) (w : W) : Prop :=
  ∃ a ∈ raw, ∃ b ∈ raw, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ w ∈ choices a b

theorem Cone.expandRaw {g : W} (raw : Finset W) (t : Finset W) (k : ℕ)
    (run : Cone g k t) (stock : ∀ w ∈ t, w ∉ raw → OnePrep raw w) :
    ∃ j u, j ≤ k + (t \ raw).card ∧ Cone g j u ∧ u ⊆ raw := by
  classical
  by_cases sub : t ⊆ raw
  · exact ⟨k,t,by omega,run,sub⟩
  · obtain ⟨w,wt,wn⟩ := Finset.not_subset.mp sub
    obtain ⟨a,ar,b,br,az,bz,ab,gate⟩ := stock w wt wn
    have aw : a ≠ w := by rintro rfl; exact wn ar
    have bw : b ≠ w := by rintro rfl; exact wn br
    let next := insert a (insert b (t.erase w))
    have decrease : next \ raw = (t \ raw).erase w := by
      ext z
      simp only [next, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      aesop
    have size : (next \ raw).card + 1 = (t \ raw).card := by
      have mem : w ∈ t \ raw := Finset.mem_sdiff.mpr ⟨wt,wn⟩
      rw [decrease, Finset.card_erase_add_one mem]
    have legal : ∀ u ∈ next, u ∉ raw → OnePrep raw u := by
      intro u um un
      simp only [next, Finset.mem_insert, Finset.mem_erase] at um
      rcases um with rfl | rfl | a
      · contradiction
      · contradiction
      · exact stock u a.2 un
    obtain ⟨j,u,cap,valid,inside⟩ :=
      Cone.expandRaw raw next (k+1) (Cone.step run wt az bz ab aw bw gate) legal
    exact ⟨j,u,by omega,valid,inside⟩
termination_by (t \ raw).card
decreasing_by
  have h : (insert a (insert b (t.erase w)) \ raw).card + 1 = (t \ raw).card := size
  omega

def prepProjection (f : Fin 128 → Fin 128) (s : Finset W) := s.image (signedMap f)

theorem preparedCut_sound (f : Fin 128 → Fin 128) (g : W) (raw : List W)
    (n budget : ℕ) (s : Finset W) (nz : signedMap f g ≠ 0)
    (low : signedLower (signedMap f g) raw n)
    (stock : ∀ w ∈ prepProjection f s, w ≠ 0 → w ∉ raw.toFinset → OnePrep raw.toFinset w)
    (limit : budget + ((prepProjection f s).erase 0 \ raw.toFinset).card <
      n + (if 0 ∈ prepProjection f s then 1 else 0))
    {k : ℕ} (le : k ≤ budget) : ¬ Cone g k s := by
  intro h
  obtain ⟨j,t,jk,run,inside,full⟩ := h.project (signedMap f) (signedMap_choice f) nz
  have legal : ∀ w ∈ t, w ∉ raw.toFinset → OnePrep raw.toFinset w :=
    fun w wt nraw => stock w (inside wt) (fun wz => run.noZero nz (wz ▸ wt)) nraw
  obtain ⟨l,u,small,expanded,final⟩ := run.expandRaw raw.toFinset t j legal
  have nle : n ≤ l := low expanded (final.trans (Finset.subset_insert _ _))
  have sz : (t \ raw.toFinset).card ≤ ((prepProjection f s).erase 0 \ raw.toFinset).card := by
    apply Finset.card_le_card
    intro w wm
    obtain ⟨wt,notRaw⟩ := Finset.mem_sdiff.mp wm
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_erase.mpr ⟨fun wz => run.noZero nz (wz ▸ wt),inside wt⟩,notRaw⟩
  split at limit
  case isTrue zero =>
    have strict : j < k := by
      by_contra! none
      have equal : j = k := by omega
      exact run.noZero nz (full equal zero)
    omega
  case isFalse => omega

end GraphSignedFrontier

namespace GraphSignedFrontier

def maskSignature (mask : W) (origin : ℕ) (w : W) : W :=
  (if w.getLsbD origin then ~~~w else w) &&& mask

set_option maxRecDepth 3500 in
theorem rowMap_not (f : Fin 128 → Fin 128) (w : W) :
    rowMap f (~~~w) = ~~~(rowMap f w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have atRow := fun z => rowMap_read f z ⟨i,hi⟩
  simp only [atRow,BitVec.getLsbD_not,hi,(f ⟨i,hi⟩).isLt,decide_true,Bool.true_and]

set_option maxRecDepth 3500 in
theorem rowMap_mask (f : Fin 128 → Fin 128) (mask w : W)
    (covers : ∀ r, mask.getLsbD (f r).val = true) :
    rowMap f (w &&& mask) = rowMap f w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have atRow := fun z => rowMap_read f z ⟨i,hi⟩
  simp only [atRow,BitVec.getLsbD_and,covers,Bool.and_true]

set_option maxRecDepth 3500 in
theorem maskSignature_sound (f : Fin 128 → Fin 128) (mask w : W)
    (covers : ∀ r, mask.getLsbD (f r).val = true) :
    rowMap f (maskSignature mask (f 0).val w) = signedMap f w := by
  rw [maskSignature, rowMap_mask f _ _ covers, signedMap, canonical]
  have bit : (rowMap f w).getLsbD 0 = w.getLsbD (f 0).val := rowMap_read f w (0 : Fin 128)
  rw [bit]
  by_cases h : w.getLsbD (f 0).val
  · simp only [if_pos h,rowMap_not]
  · simp only [if_neg h]

set_option maxRecDepth 3500 in
theorem rowMap_zero (f : Fin 128 → Fin 128) : rowMap f 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact (rowMap_read f 0 ⟨i,hi⟩).trans (by simp)

def prepSignatures (src : List W) (mask : W) (origin : ℕ) : List W :=
  src.flatMap fun a => src.flatMap fun b => (choices a b).map (maskSignature mask origin)

def rawSignatures (src : List W) (mask : W) (origin : ℕ) : List W :=
  0 :: src.map (maskSignature mask origin)

end GraphSignedFrontier

namespace GraphSignedFrontier.SixRules

def raw6 : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000]
def raw5 : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000]

def project (pin : Fin 6) (high : Bool) (r : Fin 128) : Fin 128 :=
  let x := r.val % 32
  let p := 2 ^ pin.val
  Fin.ofNat 128 (x % p + (x / p) * (2*p) + if high then p else 0)

def mask (pin : Fin 6) (high : Bool) : W :=
  if high then raw6.getD pin.val 0 else ~~~(raw6.getD pin.val 0)

set_option maxRecDepth 3800 in
set_option maxHeartbeats 0 in
theorem covers (pin : Fin 6) (high : Bool) (r : Fin 128) :
    (mask pin high).getLsbD (project pin high r).val = true :=
  (show ∀ (pin : Fin 6) (high : Bool) (r : Fin 128),
    (mask pin high).getLsbD (project pin high r).val = true by decide +kernel) pin high r

set_option maxRecDepth 3800 in
set_option maxHeartbeats 0 in
theorem rawStock (pin : Fin 6) (high : Bool) (w : W) (hw : w ∈ raw6) :
    signedMap (project pin high) w = 0 ∨ signedMap (project pin high) w ∈ raw5 := by
  have ok : ∀ (pin : Fin 6) (high : Bool), (raw6.all fun w => decide (
    signedMap (project pin high) w = 0 ∨ signedMap (project pin high) w ∈ raw5)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp (ok pin high) w hw)

structure Rule (goal : W) where
  test : ℕ → List W → Bool
  sound : ∀ budget s {k}, k ≤ budget → Cone goal k s.toFinset → test budget s = false

end GraphSignedFrontier.SixRules

namespace GraphSignedFrontier

set_option maxRecDepth 4000 in
theorem rowMap_meet (f : Fin 128 → Fin 128) (u v : W) :
    rowMap f (u &&& v) = rowMap f u &&& rowMap f v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have atRow := fun z => rowMap_read f z ⟨i,hi⟩
  simp only [atRow,BitVec.getLsbD_and]

set_option maxRecDepth 4000 in
theorem rowMap_join (f : Fin 128 → Fin 128) (u v : W) :
    rowMap f (u ||| v) = rowMap f u ||| rowMap f v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have atRow := fun z => rowMap_read f z ⟨i,hi⟩
  simp only [atRow,BitVec.getLsbD_or]

set_option maxRecDepth 4000 in
theorem controls (lo hi : Fin 128 → Fin 128) (x a b w : W)
    (low : rowMap lo x = 0) (high : rowMap hi x = ~~~0)
    (terms : a = x ∨ b = x) (form : w ∈ choices a b) :
    ∃ e : Bool, signedMap (if e then hi else lo) w = 0 := by
  simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at form
  rcases terms with rfl | rfl <;> rcases form with rfl | rfl | rfl | rfl
  · exact ⟨false, by simp [signedMap,rowMap_meet,low,canonical]⟩
  · exact ⟨false, by simp [signedMap,rowMap_meet,rowMap_not,low,canonical]⟩
  · exact ⟨true, by simp [signedMap,rowMap_meet,rowMap_not,high,canonical]⟩
  · refine ⟨true, ?_⟩
    change canonical (rowMap hi (a ||| b)) = 0
    rw [rowMap_join,high]
    change canonical (BitVec.allOnes 128 ||| rowMap hi b) = 0
    rw [BitVec.allOnes_or]
    decide +kernel
  · exact ⟨false, by simp [signedMap,rowMap_meet,low,canonical]⟩
  · exact ⟨true, by simp [signedMap,rowMap_meet,rowMap_not,high,canonical]⟩
  · exact ⟨false, by simp [signedMap,rowMap_meet,rowMap_not,low,canonical]⟩
  · refine ⟨true, ?_⟩
    change canonical (rowMap hi (a ||| b)) = 0
    rw [rowMap_join,high]
    change canonical (rowMap hi a ||| BitVec.allOnes 128) = 0
    rw [BitVec.or_allOnes]
    decide +kernel

set_option maxRecDepth 4000 in
theorem Cone.extendProjection (f : Fin 128 → Fin 128) (g a b w : W)
    (needed t : Finset W) (j : ℕ) (nz : signedMap f g ≠ 0)
    (form : w ∈ choices a b) (run : Cone (signedMap f g) j t)
    (sub : t ⊆ needed.image (signedMap f)) :
    ∃ q u, q ≤ j+1 ∧ Cone (signedMap f g) q u ∧
      u ⊆ (insert a (insert b (needed.erase w))).image (signedMap f) := by
  classical
  let m := signedMap f
  let stock := (insert a (insert b (needed.erase w))).image m
  have useA : m a ∈ stock := Finset.mem_image.mpr ⟨a,by simp,rfl⟩
  have useB : m b ∈ stock := Finset.mem_image.mpr ⟨b,by simp,rfl⟩
  have only (z : W) (zt : z ∈ t) (no : z ∉ stock) : z = m w := by
    obtain ⟨u,un,rfl⟩ := Finset.mem_image.mp (sub zt)
    by_contra! diff
    have different : u ≠ w := fun h => diff (congrArg m h)
    exact no (Finset.mem_image.mpr ⟨u,by simp [different,un],rfl⟩)
  have plans : ∀ z ∈ t, z ∉ stock → OnePrep stock z := by
    intro z zt no
    have out := only z zt no
    have form' : z ∈ choices (m a) (m b) := by rw [out]; exact signedMap_choice f a b w form
    have good : ¬ (m a = 0 ∨ m b = 0 ∨ m a = m b) := by
      intro bad
      rcases constants _ _ bad _ form' with h | h | h
      · exact run.noZero nz (h ▸ zt)
      · exact no (h.symm ▸ useA)
      · exact no (h.symm ▸ useB)
    exact ⟨m a,useA,m b,useB,fun h => good (Or.inl h),fun h => good (Or.inr (Or.inl h)),
      fun h => good (Or.inr (Or.inr h)),form'⟩
  have limit : (t \ stock).card ≤ 1 := by
    have sub : t \ stock ⊆ {m w} := by
      intro z hz
      obtain ⟨zt,notStock⟩ := Finset.mem_sdiff.mp hz
      simpa using only z zt notStock
    simpa using Finset.card_le_card sub
  obtain ⟨q,u,size,cone,valid⟩ := run.expandRaw stock t j plans
  exact ⟨q,u,by omega,cone,valid⟩

set_option maxRecDepth 4000 in
theorem Cone.twoPinLoss (lo hi : Fin 128 → Fin 128) (x g : W)
    (xLow : rowMap lo x = 0) (xHigh : rowMap hi x = ~~~0)
    (positive : ∀ e : Bool, signedMap (if e then hi else lo) g ≠ 0)
    {k : ℕ} {s : Finset W} (run : Cone g k s) :
    x ∈ s → (∀ u ∈ s, u ≠ x → rowMap lo u = rowMap hi u) →
    ∃ (e : Bool) (j : ℕ) (t : Finset W), j+2 ≤ k ∧
      Cone (signedMap (if e then hi else lo) g) j t ∧
      t ⊆ s.image (signedMap (if e then hi else lo)) := by
  induction run with
  | done =>
    intro use _
    have equal : x = g := by simpa using use
    subst x
    exact False.elim ((positive false) (by simp [signedMap,xLow,canonical]))
  | @step k needed a b w rest want _ _ _ _ _ form ih =>
    intro xUse same
    by_cases involves : a = x ∨ b = x
    · obtain ⟨e,zero⟩ := controls lo hi x a b w xLow xHigh involves form
      let f := if e then hi else lo
      let m := signedMap f
      have nz : m g ≠ 0 := positive e
      obtain ⟨j,t,jk,next,inside,full⟩ := rest.project m (signedMap_choice f) nz
      have liveZero : 0 ∈ needed.image m := Finset.mem_image.mpr ⟨w,want,zero⟩
      have strict : j < k := by
        by_contra! bad
        exact next.noZero nz (full (by omega) liveZero)
      refine ⟨e,j,t,by omega,next,?_⟩
      intro z zt
      obtain ⟨u,un,he⟩ := Finset.mem_image.mp (inside zt)
      have no : u ≠ w := by
        intro eq
        subst u
        have z0 : z = 0 := he.symm.trans (show m w = 0 from zero)
        exact next.noZero nz (z0 ▸ zt)
      exact Finset.mem_image.mpr ⟨u,by simp [no,un],he⟩
    · push_neg at involves
      have xErase : x ∈ needed.erase w := by
        simp only [Finset.mem_insert] at xUse
        exact (xUse.resolve_left (Ne.symm involves.1)).resolve_left (Ne.symm involves.2)
      have xBefore : x ∈ needed := (Finset.mem_erase.mp xErase).2
      have sameA := same a (by simp) involves.1
      have sameB := same b (by simp) involves.2
      have sameW : rowMap lo w = rowMap hi w := by
        simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at form
        rcases form with rfl | rfl | rfl | rfl <;>
          simp [rowMap_meet,rowMap_join,rowMap_not,sameA,sameB]
      have before : ∀ u ∈ needed, u ≠ x → rowMap lo u = rowMap hi u := by
        intro u hu ux
        by_cases h : u = w
        · simpa [h] using sameW
        · exact same u (by simp [hu,h]) ux
      obtain ⟨e,j,t,cost,subRun,inside⟩ := ih xBefore before
      obtain ⟨q,u,lim,next,valid⟩ := subRun.extendProjection
        (if e then hi else lo) g a b w needed t j (positive e) form inside
      exact ⟨e,q,u,by omega,next,valid⟩

end GraphSignedFrontier

namespace GraphSignedFrontier

theorem signedLower_of_saved_pin (goal : W) (positive : goal ≠ 0)
    (raw : List W) (essential : Essential goal raw) (cofactorRaw : List W) (floor : ℕ)
    (f : Fin 128 → Fin 128) (nz : signedMap f goal ≠ 0)
    (stock : ∀ w ∈ raw, signedMap f w = 0 ∨ signedMap f w ∈ cofactorRaw)
    (drops : ∃ w ∈ raw, signedMap f w = 0)
    (bound : signedLower (signedMap f goal) cofactorRaw floor) :
    signedLower goal raw (floor+1) := by
  intro k s cone sub
  have exactInputs := cone.initial positive raw essential sub
  rw [exactInputs] at cone
  obtain ⟨j,t,cap,projected,inside,full⟩ := cone.project (signedMap f) (signedMap_choice f) nz
  have smallStock : t ⊆ insert 0 cofactorRaw.toFinset := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (inside hw)
    simpa using stock v (List.mem_toFinset.mp hv)
  have enough := bound projected smallStock
  obtain ⟨w,hw,off⟩ := drops
  have zero : 0 ∈ raw.toFinset.image (signedMap f) :=
    Finset.mem_image.mpr ⟨w,List.mem_toFinset.mpr hw,off⟩
  have strict : j < k := by
    by_contra! no
    exact projected.noZero nz (full (by omega) zero)
  omega

end GraphSignedFrontier

namespace GraphSignedFrontier.Vector

structure Columns where
  w : W
  pos : Nat
  neg : Nat

def fullLanes (rows : List Nat) : Nat := 2^(128*rows.length)-1
def equalRows (rows : List Nat) (p : Columns) : Nat := fullLanes rows ^^^ (p.pos ^^^ p.neg)
def bothCols (a b : Columns) : Columns := ⟨a.w &&& b.w, a.pos &&& b.pos, a.neg &&& b.neg⟩
def orCols (a b : Columns) : Columns := ⟨a.w ||| b.w, a.pos ||| b.pos, a.neg ||| b.neg⟩
def notCols (rows : List Nat) (a : Columns) : Columns :=
  ⟨~~~a.w, fullLanes rows ^^^ a.pos, fullLanes rows ^^^ a.neg⟩
def variants (rows : List Nat) (a b : Columns) : List Columns :=
  [bothCols a b, bothCols a (notCols rows b), bothCols (notCols rows a) b, orCols a b]

def lanes (rows : List Nat) (f : Nat → W) : Nat :=
  match rows with
  | [] => 0
  | r :: rs => (f r).toNat ||| (lanes rs f <<< 128)

set_option maxRecDepth 3000 in
theorem lane_bit (rows : List Nat) (f : Nat → W) (i j : Nat) (hj : j < 128) :
    (lanes rows f).testBit (128*i+j) =
      match rows[i]? with | some r => (f r).getLsbD j | none => false := by
  induction rows generalizing i with
  | nil => simp [lanes]
  | cons r rs ih =>
    cases i with
    | zero => simp [lanes,BitVec.getLsbD, Nat.not_le.mpr hj]
    | succ i =>
      have bound : 128 ≤ 128*(i+1)+j := by omega
      have sub : 128*(i+1)+j-128 = 128*i+j := by omega
      have off : (f r).toNat.testBit (128*(i+1)+j) = false := by
        change (f r).getLsbD (128*(i+1)+j) = false
        simp [BitVec.getLsbD_of_ge, bound]
      simpa only [lanes,Nat.testBit_or,Nat.testBit_shiftLeft,off,bound,decide_true,
        Bool.true_and,Bool.false_or,sub,List.getElem?_cons_succ] using ih i

def negativeLane (w : W) (r : Nat) : W := if w.getLsbD r then ~~~0 else 0

def coefficient : Nat → Nat
  | 0 => 0
  | n+1 => 2^128 * coefficient n + 1

set_option maxRecDepth 3000 in
theorem constant_lanes (rows : List Nat) (w : W) :
    lanes rows (fun _ => w) = w.toNat * coefficient rows.length := by
  induction rows with
  | nil => simp [lanes,coefficient]
  | cons r rs ih =>
    simp only [lanes,List.length_cons,coefficient,ih]
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt w.isLt, Nat.shiftLeft_eq]
    ring

def columns (rows : List Nat) (w : W) : Columns :=
  ⟨w, w.toNat * coefficient rows.length, lanes rows (negativeLane w)⟩

def Valid (rows : List Nat) (c : Columns) : Prop :=
  ∀ i j r, j < 128 → rows[i]? = some r →
    c.pos.testBit (128*i+j) = c.w.getLsbD j ∧ c.neg.testBit (128*i+j) = c.w.getLsbD r

set_option maxRecDepth 3000 in
theorem columns_valid (rows : List Nat) (w : W) : Valid rows (columns rows w) := by
  intro i j r hj hr
  have fast : w.toNat * coefficient rows.length = lanes rows (fun _ => w) := (constant_lanes rows w).symm
  simp only [columns,fast,lane_bit rows _ i j hj,hr]
  cases on : w.getLsbD r
  · simp [negativeLane,on]
  · simp only [negativeLane,on,ite_true,BitVec.getLsbD_not,hj,decide_true,
      Bool.true_and]
    simp

set_option maxRecDepth 4000 in
theorem full_bit {rows : List Nat} {i j r : Nat}
    (hj : j < 128) (hr : rows[i]? = some r) : (fullLanes rows).testBit (128*i+j) = true := by
  have hi := (List.getElem?_eq_some_iff.mp hr).choose
  have lt : 128*i+j < 128*rows.length := by omega
  rw [fullLanes, Nat.testBit_two_pow_sub_one, decide_eq_true lt]

set_option maxRecDepth 3000 in
theorem valid_and {rows : List Nat} {a b : Columns} (ha : Valid rows a) (hb : Valid rows b) :
    Valid rows (bothCols a b) := by
  intro i j r hj hr
  obtain ⟨ap,an⟩ := ha i j r hj hr
  obtain ⟨bp,bn⟩ := hb i j r hj hr
  simp [bothCols,ap,an,bp,bn]

set_option maxRecDepth 3000 in
theorem valid_or {rows : List Nat} {a b : Columns} (ha : Valid rows a) (hb : Valid rows b) :
    Valid rows (orCols a b) := by
  intro i j r hj hr
  obtain ⟨ap,an⟩ := ha i j r hj hr
  obtain ⟨bp,bn⟩ := hb i j r hj hr
  simp [orCols,ap,an,bp,bn]

set_option maxRecDepth 3000 in
theorem valid_not {rows : List Nat} (bounds : ∀ r ∈ rows, r < 128)
    {a : Columns} (ha : Valid rows a) : Valid rows (notCols rows a) := by
  intro i j r hj hr
  have limit := bounds r (List.mem_of_getElem? hr)
  obtain ⟨ap,an⟩ := ha i j r hj hr
  simp [notCols,full_bit hj hr,ap,an,hj,limit]

set_option maxRecDepth 3000 in
theorem variant_valid {rows : List Nat} (bounds : ∀ r ∈ rows, r < 128)
    {a b c : Columns} (ha : Valid rows a) (hb : Valid rows b) (hc : c ∈ variants rows a b) :
    Valid rows c := by
  simp only [variants,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact valid_and ha hb
  · exact valid_and ha (valid_not bounds hb)
  · exact valid_and (valid_not bounds ha) hb
  · exact valid_or ha hb

def Mask (g : W) (rows : List Nat) (s : List W) (m : Nat) : Prop :=
  ∀ i j, j < 128 → m.testBit (128*i+j) = true → ∃ r, rows[i]? = some r ∧
    g.getLsbD j = true ∧ ∀ u ∈ s, u.getLsbD r = u.getLsbD j

set_option maxRecDepth 3000 in
theorem initial (g : W) (rows : List Nat) : Mask g rows [] (lanes rows (fun _ => g)) := by
  intro i j hj hit
  rw [lane_bit rows _ i j hj] at hit
  cases hr : rows[i]? with
  | none => simp [hr] at hit
  | some r => exact ⟨r,rfl,by simpa [hr] using hit,by simp⟩

set_option maxRecDepth 3000 in
theorem addMask {g : W} {rows : List Nat} {s : List W}
    {m : Nat} {c : Columns} (mask : Mask g rows s m) (valid : Valid rows c) :
    Mask g rows (c.w :: s) (m &&& equalRows rows c) := by
  intro i j hj hit
  obtain ⟨old,added⟩ := Bool.and_eq_true_iff.mp ((Nat.testBit_and ..).symm ▸ hit)
  obtain ⟨r,hr,hg,same⟩ := mask i j hj old
  obtain ⟨ap,an⟩ := valid i j r hj hr
  have eq : c.w.getLsbD r = c.w.getLsbD j := by
    simp only [equalRows,Nat.testBit_xor,full_bit hj hr,ap,an] at added
    cases hp : c.w.getLsbD j <;> cases hn : c.w.getLsbD r <;> simp_all
  exact ⟨r,hr,hg,fun w hw => (List.mem_cons.mp hw).elim (fun h => h ▸ eq) (same w)⟩

set_option maxRecDepth 3000 in
theorem survivor_complete (r j : Nat) (hj : j < 128) (s : List W) (m : W)
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

set_option maxRecDepth 3000 in
theorem clear {g : W} {rows : List Nat} {s : List W} {m : Nat}
    (mask : Mask g rows s m) (coveredRows : covered g rows s = true) : m = 0 := by
  apply Nat.eq_of_testBit_eq
  intro n
  cases hn : m.testBit n with
  | false => simp
  | true =>
    have split : 128*(n/128)+n%128 = n := by omega
    obtain ⟨r,hr,hg,agree⟩ := mask (n/128) (n%128) (by omega) (split.symm ▸ hn)
    have z := beq_iff_eq.mp (List.all_eq_true.mp coveredRows r (List.mem_of_getElem? hr))
    have p := survivor_complete r (n%128) (by omega) s g hg agree
    simp [z] at p

set_option maxRecDepth 3000 in
theorem weaken {g : W} {rows : List Nat} {s t : List W} {m : Nat}
    (h : Mask g rows s m) (sub : ∀ w ∈ t, w ∈ s) : Mask g rows t m := by
  intro i j hj hm
  obtain ⟨r,hr,hg,agree⟩ := h i j hj hm
  exact ⟨r,hr,hg,fun w hw => agree w (sub w hw)⟩

set_option maxRecDepth 3000 in
theorem foldMask {g : W} {rows : List Nat} (xs : List Columns)
    (ok : ∀ c ∈ xs, Valid rows c) (s : List W) (m : Nat) (h : Mask g rows s m) :
    Mask g rows (xs.map Columns.w ++ s) (xs.foldl (fun n c => n &&& equalRows rows c) m) := by
  induction xs generalizing s m with
  | nil => simpa using h
  | cons c cs ih =>
    have rest := ih (fun z hz => ok z (List.mem_cons_of_mem _ hz)) (c.w :: s)
      (m &&& equalRows rows c) (addMask h (ok c List.mem_cons_self))
    apply weaken rest
    intro w hw
    simpa [or_assoc,or_comm,or_left_comm] using hw

def branch (_g : W) (seek : List W → Bool) (k len m : Nat) (next : List W) : Bool :=
  decide (len ≤ k) && m == 0 && !seek next

set_option maxRecDepth 3000 in
theorem branch_of {g : W} {rows : List Nat} {seek : List W → Bool} {k len m : Nat}
    {next : List W} (dims : len ≤ k) (mask : Mask g rows next m)
    (cov : covered g rows next = true) (miss : seek next = false) :
    branch g seek k len m next = true := by simp [branch,dims,clear mask cov,miss]
def packedPair (g : W) (rows : List Nat) (seek : List W → Bool) (k : Nat)
    (initialMask : Nat) (s : List W) (t : List Columns) (a b : Columns) : Bool :=
  let cs := variants rows a b
  cs.any (fun c => c.w == g) ||
    let base := t.filter (fun u => u.w != a.w && u.w != b.w)
    let rest := s.filter (fun u => u != a.w && u != b.w)
    let mask := base.foldl (fun m z => m &&& equalRows rows z) initialMask
    let ra := equalRows rows a
    let rb := equalRows rows b
    let len := rest.length
    cs.any fun c => c.w != 0 && !s.contains c.w &&
      let m := mask &&& equalRows rows c
      (branch g seek k len m (c.w :: rest) ||
       branch g seek k (len + 1) (m &&& ra) (c.w :: a.w :: rest) ||
       branch g seek k (len + 1) (m &&& rb) (c.w :: b.w :: rest) ||
       branch g seek k (len + 2) (m &&& ra &&& rb) (c.w :: a.w :: b.w :: rest))

set_option maxRecDepth 3000 in
theorem pair_of (g : W) (rows : List Nat) (seek : List W → Bool) (k : Nat)
    (s : List W) (t : List Columns) (a b : Columns)
    (initialMask : Nat) (start : Mask g rows [] initialMask)
    (bounds : ∀ r ∈ rows, r < 128)
    (stock : t.map Columns.w = s) (valid : ∀ z ∈ t, Valid rows z)
    (va : Valid rows a) (vb : Valid rows b)
    (ha : a.w ∈ s) (hb : b.w ∈ s) (absent : g ∉ s)
    (slow : onePair s (fun u => u.contains g || (decide (0 < k) && decide (u.length ≤ k+1)
      && covered g rows u && !seek u)) a.w b.w = true) :
    packedPair g rows seek k initialMask s t a b = true := by
  have vw : (variants rows a b).map Columns.w = choices a.w b.w := rfl
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
    let m := base.foldl (fun n z => n &&& equalRows rows z) initialMask
    have shape : base.map Columns.w = rest := by
      change (t.filter (fun u => u.w != a.w && u.w != b.w)).map Columns.w =
        s.filter (fun u => u != a.w && u != b.w)
      rw [← stock, List.filter_map]
      rfl
    have core := foldMask base (fun z hz => valid z (List.mem_filter.mp hz).1) [] _ start
    have trimmed : Mask g rows rest m := by simpa [shape,m] using core
    have vc := variant_valid bounds va vb hc
    let mc := m &&& equalRows rows c
    have raw : Mask g rows (c.w :: rest) mc := addMask trimmed vc
    have withA : Mask g rows (c.w :: a.w :: rest) (mc &&& equalRows rows a) :=
      weaken (addMask raw va) (by simp [or_left_comm])
    have withB : Mask g rows (c.w :: b.w :: rest) (mc &&& equalRows rows b) :=
      weaken (addMask raw vb) (by simp [or_left_comm])
    have withBoth : Mask g rows (c.w :: a.w :: b.w :: rest)
        (mc &&& equalRows rows a &&& equalRows rows b) :=
      weaken (addMask withA vb) (by simp [or_left_comm])
    cases ka <;> cases kb <;>
      simp only [after,withWire,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at hl cov miss
    all_goals
      simp only [Bool.or_eq_true_iff]
      first
      | exact Or.inl (Or.inl (Or.inl (branch_of (by omega) raw cov miss)))
      | exact Or.inl (Or.inl (Or.inr (branch_of (by omega) withA cov miss)))
      | exact Or.inl (Or.inr (branch_of (by omega) withB cov miss))
      | exact Or.inr (branch_of (by omega) withBoth cov miss)

end GraphSignedFrontier.Vector

namespace GraphSignedFrontier.Table

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

end GraphSignedFrontier.Table

namespace GraphSignedFrontier.Table

theorem block2 {f : ℕ → Bool} {i : ℕ} (h0 : f i = true) (h1 : f (i+1) = true) : span f 2 i = true := by
  simp [span, Nat.add_assoc, h0, h1]

theorem block3 {f : ℕ → Bool} {i : ℕ} (h0 : f i = true) (h1 : f (i+1) = true) (h2 : f (i+2) = true) : span f 3 i = true := by
  simp [span, Nat.add_assoc, h0, h1, h2]

theorem block4 {f : ℕ → Bool} {i : ℕ} (h0 : f i = true) (h1 : f (i+1) = true) (h2 : f (i+2) = true) (h3 : f (i+3) = true) : span f 4 i = true := by
  simp [span, Nat.add_assoc, h0, h1, h2, h3]

end GraphSignedFrontier.Table
open GraphSignedFrontier.Table (span span_join span_member block2 block3 block4)

namespace GraphSignedFrontier

def closedUsing (g : W) (negative : List ℕ) (words : ℕ → ℕ → List W) (count : ℕ → ℕ)
    (lookup : ℕ → List W → ℕ × ℕ) (sym : ℕ → List Switch) (cut : ℕ → List W → Bool) : ℕ → ℕ → Bool
  | 0, i => !(words 0 i).contains g
  | k+1, i =>
    let s := words (k+1) i
    !s.contains g && !(moves s fun t =>
      t.contains g || (decide (0 < k) && decide (t.length ≤ k+1) && covered g negative t &&
        !(cut k t || found words count lookup sym k t)))

theorem closedUsing_excludes (g : W) (hg : g ≠ 0) (negative : List ℕ)
    (neg : ∀ r ∈ negative, r < 128 ∧ g.getLsbD r = false)
    (words : ℕ → ℕ → List W) (count : ℕ → ℕ) (lookup : ℕ → List W → ℕ × ℕ)
    (sym : ℕ → List Switch) (valid : ∀ j, ∀ op ∈ sym j, op.Valid)
    (fix : ∀ j, reindex (sym j) g = g) (cut : ℕ → List W → Bool)
    (sound : ∀ budget t {d}, d ≤ budget → Cone g d t.toFinset → cut budget t = false)
    (cap : ℕ)
    (nd : ∀ k ≤ cap, ∀ i < count k, (words k i).Nodup)
    (checks : ∀ k ≤ cap, ∀ i < count k, closedUsing g negative words count lookup sym cut k i = true) :
    ∀ k ≤ cap, ∀ i < count k, ∀ d ≤ k, ¬ Cone g d (words k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro hk i hi d hd run
    have de : d = 0 := by omega
    subst d
    have terminal {t : Finset W} (p : Cone g 0 t) : g ∈ t := by cases p; simp
    have mem := List.mem_toFinset.mp (terminal run)
    simpa [closedUsing,mem] using checks 0 hk i hi
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
        covered g negative t && !(cut k t || found words count lookup sym k t))
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
        simp [positive,show t.length ≤ k+1 by omega,ht.covered negative neg,no,sound k t (by omega : d ≤ k) ht])
      change (!moves (words (k+1) i) test) = true at reject
      simp [next] at reject

namespace Vector

def packedUsing (g : W) (rows : List Nat) (initialMask : Nat) (words : Nat → Nat → List W)
    (count : Nat → Nat) (lookup : Nat → List W → Nat × Nat) (sym : Nat → List Switch)
    (cut : ℕ → List W → Bool) : Nat → Nat → Bool
  | 0,i => !(words 0 i).contains g
  | k+1,i =>
    let s := words (k+1) i
    let t := s.map (columns rows)
    !s.contains g && !(t.any fun a => t.any fun b => decide (a.w.toNat < b.w.toNat) &&
      packedPair g rows (fun s => cut k s || found words count lookup sym k s) k initialMask s t a b)

theorem closedUsing_sound (g : W) (rows : List Nat) (initialMask : Nat)
    (maskSpec : initialMask = lanes rows (fun _ => g)) (words : Nat → Nat → List W)
    (count : Nat → Nat) (lookup : Nat → List W → Nat × Nat) (sym : Nat → List Switch)
    (bounds : ∀ r ∈ rows, r < 128)
    (cut : ℕ → List W → Bool)
    (k i : Nat) (ok : packedUsing g rows initialMask words count lookup sym cut k i = true) :
    closedUsing g rows words count lookup sym cut k i = true := by
  cases k with
  | zero => exact ok
  | succ k =>
    obtain ⟨absent,verified⟩ := Bool.and_eq_true_iff.mp ok
    apply Bool.and_eq_true_iff.mpr
    refine ⟨absent,?_⟩
    let s := words (k+1) i
    let t := s.map (columns rows)
    let seek := fun s : List W => cut k s || found words count lookup sym k s
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
      exact columns_valid rows u
    have fast := pair_of g rows seek k s t (columns rows a) (columns rows b) _
      (maskSpec.symm ▸ initial g rows) bounds st valid (columns_valid rows a) (columns_valid rows b)
      ha hb ng slow
    have yes : (t.any fun a => t.any fun b => decide (a.w.toNat < b.w.toNat) &&
        packedPair g rows seek k initialMask s t a b) = true :=
      List.any_eq_true.mpr ⟨columns rows a,List.mem_map.mpr ⟨a,ha,rfl⟩,
        List.any_eq_true.mpr ⟨columns rows b,List.mem_map.mpr ⟨b,hb,rfl⟩,
          Bool.and_eq_true_iff.mpr ⟨lt,fast⟩⟩⟩
    change (!(t.any fun a => t.any fun b => decide (a.w.toNat < b.w.toNat) &&
      packedPair g rows seek k initialMask s t a b)) = true at verified
    simp [yes] at verified

end Vector

end GraphSignedFrontier

namespace GraphSignedFrontier

def sameMembers (a b : List W) : Bool := a.all b.contains && b.all a.contains

set_option maxRecDepth 3500 in
theorem sameMembers_sound (a b : List W) (test : sameMembers a b = true) :
    ∀ w, w ∈ a ↔ w ∈ b := by
  obtain ⟨ab,ba⟩ := Bool.and_eq_true_iff.mp test
  intro w
  exact ⟨fun ha => by simpa [List.contains_eq_mem] using List.all_eq_true.mp ab w ha,
    fun hb => by simpa [List.contains_eq_mem] using List.all_eq_true.mp ba w hb⟩

set_option maxRecDepth 3500 in
def preparedLookupCut (raws plans : List W) (mask : W) (origin floor budget : ℕ) (run : List W) : Bool :=
  let values := run.map (maskSignature mask origin)
  values.all (fun w => raws.contains w || plans.contains w) &&
    decide (budget + (values.toFinset \ raws.toFinset).card <
      floor + (if (0 : W) ∈ values then 1 else 0))

set_option maxRecDepth 3500 in
theorem preparedLookupCut_sound (f : Fin 128 → Fin 128) (mask goal : W)
    (src raw raws plans : List W)
    (rawsExact : ∀ w, w ∈ raws ↔ w ∈ rawSignatures src mask (f 0).val)
    (plansExact : ∀ w, w ∈ plans ↔ w ∈ prepSignatures src mask (f 0).val)
    (floor budget : ℕ) (s : List W)
    (covers : ∀ r, mask.getLsbD (f r).val = true)
    (rawStock : ∀ w ∈ src, signedMap f w = 0 ∨ signedMap f w ∈ raw)
    (nz : signedMap f goal ≠ 0) (lower : signedLower (signedMap f goal) raw floor)
    {k : ℕ} (le : k ≤ budget) (run : Cone goal k s.toFinset) :
    preparedLookupCut raws plans mask (f 0).val floor budget s = false := by
  by_contra! failed
  let signature := maskSignature mask (f 0).val
  let values := s.map signature
  have both := Bool.and_eq_true_iff.mp (show preparedLookupCut raws plans mask (f 0).val floor budget s = true by simpa using failed)
  have view (w : W) : rowMap f (signature w) = signedMap f w := maskSignature_sound f mask w covers
  have data (w : W) (mem : w ∈ raws) : rowMap f w = 0 ∨ rowMap f w ∈ raw := by
    have memo := (rawsExact _).mp mem
    rcases List.mem_cons.mp memo with rfl | tail
    · exact Or.inl (rowMap_zero f)
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp tail
      rw [view]
      exact rawStock u hu
  have facts (w : W) (mem : w ∈ plans) (wnz : rowMap f w ≠ 0) (notRaw : rowMap f w ∉ raw.toFinset) :
      OnePrep raw.toFinset (rowMap f w) := by
    rcases List.mem_flatMap.mp ((plansExact _).mp mem) with ⟨a,ha,second⟩
    rcases List.mem_flatMap.mp second with ⟨b,bmem,form⟩
    obtain ⟨cs,hcs,rfl⟩ := List.mem_map.mp form
    rw [view] at wnz notRaw ⊢
    have trans := signedMap_choice f a b cs hcs
    have ax := rawStock a ha
    have bx := rawStock b bmem
    have good : ¬ (signedMap f a = 0 ∨ signedMap f b = 0 ∨ signedMap f a = signedMap f b) := by
      intro impossible
      rcases constants _ _ impossible _ trans with h | h | h
      · exact wnz h
      · exact ax.elim (fun z => wnz (h.trans z)) fun use => notRaw (List.mem_toFinset.mpr (h.symm ▸ use))
      · exact bx.elim (fun z => wnz (h.trans z)) fun use => notRaw (List.mem_toFinset.mpr (h.symm ▸ use))
    have hna : signedMap f a ≠ 0 := fun h => good (Or.inl h)
    have hnb : signedMap f b ≠ 0 := fun h => good (Or.inr (Or.inl h))
    exact ⟨_, List.mem_toFinset.mpr (ax.resolve_left hna), _, List.mem_toFinset.mpr (bx.resolve_left hnb),
      hna, hnb, fun h => good (Or.inr (Or.inr h)), trans⟩
  have each : ∀ w ∈ prepProjection f s.toFinset, w ≠ 0 → w ∉ raw.toFinset →
      OnePrep raw.toFinset w := by
    intro w hw wz wr
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hw
    have sig : signature a ∈ values := List.mem_map.mpr ⟨a,List.mem_toFinset.mp ha,rfl⟩
    have opts := Bool.or_eq_true_iff.mp (List.all_eq_true.mp both.1 (signature a) sig)
    cases opts with
    | inl seen =>
      have bad := data _ (by simpa [List.contains_eq_mem] using seen)
      rw [view] at bad
      exact False.elim (bad.elim wz fun h => wr (List.mem_toFinset.mpr h))
    | inr seen =>
      have h := facts (signature a) (by simpa [List.contains_eq_mem] using seen)
      rw [view] at h
      exact h wz wr
  have ext :
      ((prepProjection f s.toFinset).erase 0 \ raw.toFinset).card ≤ (values.toFinset \ raws.toFinset).card := by
    apply le_trans (Finset.card_le_card (t := (values.toFinset \ raws.toFinset).image (rowMap f)) ?_) Finset.card_image_le
    intro w hw
    obtain ⟨present,notRaw⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨notZero,hw⟩ := Finset.mem_erase.mp present
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_image.mpr
    refine ⟨signature u,Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨u,List.mem_toFinset.mp hu,rfl⟩),?_⟩,view u⟩
    intro has
    have lost := data _ (List.mem_toFinset.mp has)
    rw [view] at lost
    exact lost.elim notZero fun h => notRaw (List.mem_toFinset.mpr h)
  have before : budget + (values.toFinset \ raws.toFinset).card <
      floor + (if (0 : W) ∈ values then 1 else 0) := of_decide_eq_true both.2
  have size : budget + ((prepProjection f s.toFinset).erase 0 \ raw.toFinset).card <
      floor + (if 0 ∈ prepProjection f s.toFinset then 1 else 0) := by
    by_cases mem : (0 : W) ∈ values
    · obtain ⟨w,hw,emptyword⟩ := List.mem_map.mp mem
      have zero : 0 ∈ prepProjection f s.toFinset := Finset.mem_image.mpr ⟨w,
        List.mem_toFinset.mpr hw, (view w).symm.trans (by rw [emptyword,rowMap_zero])⟩
      rw [if_pos mem] at before
      simp only [zero, if_true]
      omega
    · rw [if_neg mem, Nat.add_zero] at before
      split <;> omega
  exact preparedCut_sound f goal raw floor budget s.toFinset nz lower each size le run

end GraphSignedFrontier

namespace GraphSignedFrontier

namespace Table

def wordHash (salt : ℕ) (w : W) : ℕ :=
  let x := w.toNat % 2^64
  let y := ((x ^^^ (x >>> 30)) * salt) % 2^64
  let z := ((y ^^^ (y >>> 27)) * 0x94d049bb133111eb) % 2^64
  (z ^^^ (z >>> 31)) % 2^48

def hintKey (salt : ℕ) (ws : List W) : ℕ := (ws.foldl (fun a w => a+wordHash salt w) 0) % 2^48

end Table

namespace SixRules

def knownRule (goal : W) (pin : Fin 6) (high : Bool) (leaf : W) (floor : ℕ)
    (raws plans : List W)
    (rawsOK : sameMembers raws (rawSignatures raw6 (mask pin high) ((project pin high) 0).val) = true)
    (plansOK : sameMembers plans (prepSignatures raw6 (mask pin high) ((project pin high) 0).val) = true)
    (equal : signedMap (project pin high) goal = leaf) (nz : leaf ≠ 0)
    (lower : signedLower leaf raw5 floor) : Rule goal where
  test := preparedLookupCut raws plans (mask pin high) ((project pin high) 0).val floor
  sound budget s k le cone := by
    have positive : signedMap (project pin high) goal ≠ 0 := by rwa [equal]
    have direct : signedLower (signedMap (project pin high) goal) raw5 floor := by rwa [equal]
    exact preparedLookupCut_sound (project pin high) (mask pin high) goal raw6 raw5 raws plans
      (sameMembers_sound _ _ rawsOK) (sameMembers_sound _ _ plansOK)
      floor budget s (covers pin high) (rawStock pin high) positive direct le cone

end SixRules

end GraphSignedFrontier

namespace GraphSignedFrontier.Compact

structure PoolData where
  width : ℕ
  scale : ℕ
  indexBits : ℕ
  dictionary : ℕ → ℕ
  pages : ℕ → ℕ → ℕ
  count : ℕ → ℕ

def dictionaryWord (table : PoolData) (idx : ℕ) : W :=
  let bits := table.width
  let word := (table.dictionary (idx / 32) >>> (bits * (idx % 32))) % 2^bits
  BitVec.ofNat 128 (word * table.scale)

def pool (table : PoolData) (k i : ℕ) : List W :=
  let bits := table.indexBits
  let size := bits * (k+1)
  let row := (table.pages k (i / 16) >>> (size * (i % 16))) % 2^size
  ((List.range (k+1)).map
    (fun j => dictionaryWord table ((row >>> (bits*j)) % 2^bits))).filter (fun w => w != 0)

structure CodeBook where
  keyBits : ℕ
  valueBits : ℕ
  pages : ℕ → ℕ → ℕ
  count : ℕ → ℕ

def codeField (book : CodeBook) (k i : ℕ) : ℕ :=
  let bits := book.keyBits + book.valueBits
  (book.pages k (i / 32) >>> (bits * (i % 32))) % 2^bits

def binaryFind (book : CodeBook) (depth key : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | k+1, lo, hi =>
    if lo+1 < hi then
      let m := (lo+hi)/2
      if ((codeField book depth m) >>> book.valueBits) ≤ key then
        binaryFind book depth key k m hi
      else binaryFind book depth key k lo m
    else lo

def code (book : CodeBook) (salt k : ℕ) (s : List W) : Option ℕ :=
  let key := Table.hintKey salt s % 2^book.keyBits
  let idx := binaryFind book k key 16 0 (book.count k)
  let entry := codeField book k idx
  if idx < book.count k ∧ entry >>> book.valueBits = key then
    some (entry % 2^book.valueBits)
  else none

def lookup (table : PoolData) (book : CodeBook) (salt k : ℕ) (s : List W) : ℕ × ℕ :=
  match code book salt k s with
  | some value => (value / 16, value % 16)
  | none => (table.count k,0)

structure CutIndex where
  bucketCount : ℕ → ℕ
  slotCount : ℕ → ℕ
  shifts : ℕ → ℕ → ℕ
  rules : ℕ → ℕ → ℕ

def candidate (table : CutIndex) (salt k : ℕ) (s : List W) : ℕ :=
  let key := Table.hintKey salt s
  let bucket := (key >>> 24) % table.bucketCount k
  let delta := (table.shifts k (bucket / 32) >>> (16 * (bucket % 32))) % 2^16
  let slot := (key % 2^24 + delta) % table.slotCount k
  (table.rules k (slot / 128) >>> (4 * (slot % 128))) % 16

def reject (goal : W) (rules : List (SixRules.Rule goal)) (table : CutIndex) (salt k : ℕ)
    (s : List W) : Bool :=
  if table.slotCount k = 0 then false else
    match rules[candidate table salt k s]? with
    | none => false
    | some rule => rule.test k s

theorem safe (goal : W) (rules : List (SixRules.Rule goal)) (table : CutIndex) (salt k : ℕ)
    (s : List W) {d} (le : d ≤ k) (cone : Cone goal d s.toFinset) :
    reject goal rules table salt k s = false := by
  unfold reject
  split
  · rfl
  · cases hr : rules[candidate table salt k s]? with
    | none => simp [hr]
    | some r => simpa [hr] using r.sound k s le cone

def check (table : PoolData) (g : W) (rows : List ℕ) (start : ℕ)
    (find : ℕ → List W → ℕ × ℕ) (switches : ℕ → List Switch)
    (cut : ℕ → List W → Bool) (k i : ℕ) : Bool :=
  decide (pool table k i).Nodup &&
    Vector.packedUsing g rows start (pool table) table.count find switches cut k i

theorem lower (table : PoolData) (goal : W) (positive : goal ≠ 0)
    (raw : List W) (essential : Essential goal raw) (negative : List ℕ)
    (neg : ∀ r ∈ negative, r < 128 ∧ goal.getLsbD r = false)
    (start cap : ℕ) (startEq : start = Vector.lanes negative (fun _ => goal))
    (rootNumber : 0 < table.count cap) (root : pool table cap 0 = raw)
    (find : ℕ → List W → ℕ × ℕ) (switches : ℕ → List Switch)
    (valid : ∀ j, ∀ op ∈ switches j, op.Valid)
    (fixed : ∀ j, reindex (switches j) goal = goal)
    (cut : ℕ → List W → Bool)
    (safe : ∀ budget t {d}, d ≤ budget → Cone goal d t.toFinset → cut budget t = false)
    (checks : ∀ j ≤ cap, ∀ i < table.count j, check table goal negative start find switches cut j i = true) :
    signedLower goal raw (cap+1) := by
  intro k s cone sub
  by_contra! short
  have eq := cone.initial positive raw essential sub
  rw [eq, ← root] at cone
  have nd (j : ℕ) (hj : j ≤ cap) (i : ℕ) (hi : i < table.count j) : (pool table j i).Nodup :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp (checks j hj i hi)).1
  have checked (j : ℕ) (hj : j ≤ cap) (i : ℕ) (hi : i < table.count j) :=
    Vector.closedUsing_sound goal negative start startEq (pool table) table.count find
      switches (fun r hr => (neg r hr).1) cut j i (Bool.and_eq_true_iff.mp (checks j hj i hi)).2
  exact closedUsing_excludes goal positive negative neg (pool table) table.count find switches
    valid fixed cut safe cap nd checked cap le_rfl 0 rootNumber k (by omega) cone

end GraphSignedFrontier.Compact

namespace GraphSignedFrontier

namespace LeafK4

def target : W := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def raw : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00]
def negative : List ℕ := [0, 1, 2, 4, 8]

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem positive : target ≠ 0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem unique : raw.Nodup := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem neg : ∀ r ∈ negative, r < 128 ∧ target.getLsbD r = false := by
  intro r hr
  have yes : (negative.all fun j => decide (j < 128 ∧ target.getLsbD j = false)) = true := by decide +kernel
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp yes r hr

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · refine ⟨2,3,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : W) ∨ z.getLsbD 2 = z.getLsbD 3)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,3,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xcccccccccccccccccccccccccccccccc : W) ∨ z.getLsbD 1 = z.getLsbD 3)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : W) ∨ z.getLsbD 1 = z.getLsbD 5)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,9,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xff00ff00ff00ff00ff00ff00ff00ff00 : W) ∨ z.getLsbD 1 = z.getLsbD 9)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd

def dictionary : ℕ → ℕ
  | 0 => 0x88eeeaeaaaaaeafe008888eecc5500eeaa3300eaeabf007f003f001f00f0f000fef0000ff0ccccaaaa7070ff88fafaeeecfaf8ff00f0f8f8f8eeee77000000
  | 1 => 0xfefe22220c0c00ccc0c0aafaaaee88cc88aa80800aaa00ee00aa000aaa000f0000f0fcfcfaf0aa88a8a86666
  | _ => 0

def packed : ℕ → ℕ → ℕ
  | 2, 0 => 0x2430852071460850c2144083081
  | 3, 0 => 0x15031c15030b6d030b4026814192d841731641531240c50b40c2d340c2d240c2d140c2cd40c2cf38c2cd30b04a0050c2
  | 3, 1 => 0x16420216364b14340214308c14308b14309a1500a21500a115009a1500a015009f15078c15054c15074c
  | 4, 0 => 0x15030bb8540c2ed15030b68540c2ec15030bac540c2ea15030ba4540c2df15030ba1030b9d840c2da05030b5a640c2e694015009a00541530040c2d2
  | 4, 1 => 0x17540c2c521008c15008c2c54022da15008bd054022f315008bc8541533115054c2c540cc0b15032f2c540c2e1
  | 5, 0 => 0x540230b00540c2da00540c2e9
  | 6, 0 => 0x15030b
  | _, _ => 0

def count : ℕ → ℕ
  | 2 => 6
  | 3 => 30
  | 4 => 28
  | 5 => 3
  | 6 => 1
  | _ => 0

def table : Compact.PoolData := ⟨16,0x10001000100010001000100010001,6,dictionary,packed,count⟩
def startMask : ℕ := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
def swap0x3 : Switch := ⟨7, 0xaa00aa00aa00aa00aa00aa00aa00aa, 0x55005500550055005500550055005500⟩
def swap1x2 : Switch := ⟨2, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 0x30303030303030303030303030303030⟩
def swap0x2 : Switch := ⟨3, 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 0x50505050505050505050505050505050⟩
def swap2x3 : Switch := ⟨4, 0xf000f000f000f000f000f000f000f0, 0xf000f000f000f000f000f000f000f00⟩
def swap0x1 : Switch := ⟨1, 0x22222222222222222222222222222222, 0x44444444444444444444444444444444⟩
def swap1x3 : Switch := ⟨6, 0xcc00cc00cc00cc00cc00cc00cc00cc, 0x33003300330033003300330033003300⟩

def switchPool : List (List Switch) := [[swap0x3, swap1x2], [swap0x2, swap2x3], [swap0x1, swap1x3], [swap0x1, swap1x2], [swap0x3, swap2x3], [swap0x1, swap2x3], [swap0x2, swap1x3], [swap0x2, swap1x2], [swap0x3, swap1x3], [swap1x2, swap2x3], [swap1x3, swap2x3], []]
def switches (i : ℕ) : List Switch := switchPool.getD i []

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem valid (j : ℕ) : ∀ s ∈ switches j, s.Valid := by
  intro s hs
  by_cases inRange : j < switchPool.length
  · have actual : switchPool[j] ∈ switchPool := List.getElem_mem inRange
    have checked : (switchPool.all fun xs => xs.all fun q =>
        @decide q.Valid (by unfold Switch.Valid; infer_instance)) = true := by decide +kernel
    rw [switches, List.getD_eq_getElem _ _ inRange] at hs
    letI : Decidable s.Valid := by unfold Switch.Valid; infer_instance
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked _ actual) s hs)
  · rw [switches, List.getD_eq_default _ _ (by omega)] at hs
    simp at hs

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem fixed (j : ℕ) : reindex (switches j) target = target := by
  by_cases inRange : j < switchPool.length
  · have checked : (switchPool.all fun moves => decide (reindex moves target = target)) = true := by decide +kernel
    rw [switches,List.getD_eq_getElem _ _ inRange]
    exact of_decide_eq_true (List.all_eq_true.mp checked _ (List.getElem_mem inRange))
  · rw [switches, List.getD_eq_default _ _ (by omega)]
    rfl

def hintPage : ℕ → ℕ → ℕ
  | 2, 0 => 0x828c500881aa60347ef0500b7e4d30406ed820266d9ec0185fc570115b23b03858d07002537d80195059b044505520104b52f027453a20483c5370063712f0303311600032aa504a3267405b2bae9013285ba04626c0305826b1902320f4202b1df8f0431d67c03615ecd04510fd10320e9670030e3b0001058e102a02065042
  | 2, 1 => 0xf450401aec0eb039ead77031e4292052e30f3005e2b41047df3fd03adbcac037dbb95009d8fa4041d72b0025d6b92004d0632014cf31b024cdb37022cbb7b017c8c9904bc4a8c020bbcbf029b7352050b6c4a028b2f7803bb08ac01ba5353012a29a10219ec8e0338bc7d0158afc20168802a05787b390518626203582d22049
  | 2, 2 => 0xfae87007f7c0000a
  | 3, 0 => 0x207861841f5b21201efa21821a5f714b18f440861821d05317f4e07b1737c1291725016b16303091118a20c41169e02b1148f158108000c7107900a41030f16a0feb91510f95d1970cdcb1930c6dd0b40b1771a50a02b15208c03012077ce148074971cb071f41ab069971a6058e100a0391f0a0037ae0ca031e21b40138c061
  | 3, 1 => 0x3d67c0a73c2bb0f43bacf1263a5b61b1397a819a371a3054368a012436237099355b303634b3a1d634156018331b0196327b1188321c3044317e11b730e2f1222fe4005b2f5430972def11712d7621412d2131872ce160922c3150272a3a710129dd0162293a50582788f08526b1900325b1406324c8a0a123f740d620f4200b
  | 3, 2 => 0x5fd830345e00a06b5c6a11905b35411b5a9e01b354e0919b538d41b9529cb0a550b9e0825044d0434e85f1984e2800f64e1531304d59c1614d1610204c3b11754b52f0074ade10a24a7d00f84a2520f248987131459ea01743971069432d4135431a209b42beb0904252711341e37066416e80c64056517b3fafe0883f0a212a
  | 3, 3 => 0x7858f0d078065134761bc0eb73f331507395518572abf04970ed91816eec51b56ed820066e0660c56de030876b7341676b4fd08a6ab4905268a82119684db06566f3019466dcf191667f91866615e1786574c1a263d5f08b635b6127631590966294f0f16222315b61fca0b66189c0b76168a13260eea0f760ea8157603240fb
  | 3, 4 => 0x8c91711a8c6b20a68c3130bb8b1331118a7c71398a1d11368a0fe137893f616488eba1a088c531a1880d7176878ee11486aec089865da16085df502884cc20f983b2e0a881fff06481e3b0748144818a80d7e0c980c870db800ed1a97fd0f1697f3f61a77f0221c17da3306a7bf6a1407bceb0487b8c80c17b0781b8788f21db
  | 3, 5 => 0xb2b91173b1ffb010b183c045b10521c4ae597177ae55d080ab88f166aad3e1b0a2c491b6a29a1001a188e1c39dfcf1339db6f04a9d9a31899d4f61aa9b7751429b4b813898d3f083980ed021974de11696d6e0409647317a96092068951fb0c2949080b5944920f09418e09a937310949318f0b191f651b28de960b88dc2e0fa
  | 3, 6 => 0xcc97a1d0c9a19011c81b4163c70d9170c52c0050c4ee0165c4a8c000c3f43100c315b0bac2cde174c2b730f3c272a042c115c047c01e60cbbfc91125be78c112bd5e718bbd562195bc503180bc3741c5bbcbf009b7fe1059b7f22172b75a60a3b719a13ab6c4a008b69d30aab5658070b55cd1a4b419b041b3de9192b2cb7118
  | 3, 7 => 0xe389405ae30e3128e2cb21c2e25bd0c0e1bcb060e0545168dffe0022dffc201bde05504bdd20b076dd10a0c8dd0fb10bdaff80b2d9a7c1d4d8ad0056d8494095d72b0005d71dc110d5a220d4d4d980f5d417f067d34c912bd33be102d2ca4123d2b8d098d1580117d0896179cf31b004ceff0055ce5cd121cdb37002cd7c00b9
  | 3, 8 => 0xfffd9081ff5f9147fc14a0b0f804b0abf7d070c3f68670b3f55cb03bf51f2030f5051183f26a4051f1e7f093efb86199ebb931baeaf471a3eab111a8e932d084e756f057e740113be6175115e61420a9e53701bbe4983046e4846062
  | 4, 0 => 0x1fb9d0761f6a30471f5031341ec860821e6a40551de250fa1baa90aa18bdb0311870d0bb17ec417715a920ba153ce1a61531711a13045146128610db11ab31601148f02810a100c40feb90210ecef09b0eaa10690bb481800b18f0340ae1f0e40a1931170a02b022077f805706beb0940379117101c890710138c001011b51a0
  | 4, 1 => 0x36a87192362a312735661084352530b9351fa0e934d670723425f0ab32d5b06332cc7164314140a93095f1552fe931b42f8a11622e83a1a92e4350782c9090b12c5420532bb321a82b05d07329c230b52988c14b28f301a7287d9133280e90b3270d80ea266820f825ee70a225b14003252d61872420b14323f931442081003a
  | 4, 2 => 0x5698f06054b3c03553b1e17452efc11652c69176527f705250f430f14f5611314e3f50404aa8e0914a8cc138484d518547e53080469f21044642d0b64535618a44963165446f40d143c33156439710094347107a430850a14252701341e610b741e370063c9501bb3c2940753b3e805639fb21533836118637bba17936dc40e7
  | 4, 3 => 0x6bd940b06b2f01786aae516b6a4d212168a82019684db0056834406a6783212566a4d0676635d0fb65f6b062636350f66272c107623f90416232217a6222302b61cdc1456140419860ea8027604f91495f9570425e00a00b5dc6d1125d9ed0935b90c1365b35401b5a77f0e05a6f81285a21e15a59c2d046586ae09257ea00d7
  | 4, 4 => 0x81dd710181a4d0f4817bf0898135503b810f60878107b1b68101617b809b0119802da1007e69d1667dcda0707dca80657da3300a7d1c20817c3440b27bd4c0887aa84039795670e17950509877d76059774b919776d071097551e10573f3302073b9e0967231f04b7082405b6f8ea1a36edf11306dc330d06dc251476d8c7077
  | 4, 5 => 0x97a3f08b97a2e08a974de016970781aa967410a0960ea18b96092008959ae13794d6f1899499b148904f50eb8f21b13b8e3221758c91701a8b55c0a58b1330118a0ba1a489f761a1896930c0886460a48853b097878ee014875d9120866a31728652d0f3860c9074841c80cb8404204483ed108682faf11182abb0a681fff004
  | 4, 6 => 0xb83c1122b8282115b82500e2b71b4123b6203142b4e8d033b4b0e158b3f6f090b3aa70a3b2cb7018b206c168b0a6d159b0103051ad4530e8ad12d1abacd89043abdb8030aa99e0e5a90a4188a8b08061a7f7a118a791507ba5714140a558f106a4b00170a4a3e132a1c401849c9491399b6f603298cd3173989df04597ec106b
  | 4, 7 => 0xd84ff190d769c0e3d71dc010d42e7181d417f007d280a083d1580017cf4e2066cee9e054ccb3816acc427135cabc3167c9121037c8ba6068c788e10bc76270d2c667a1a2c540a169c40e10f9c204b126c1aef04ac1875154c0dd9108c07de13ac00070a7be78c012bdf8912abdd311b0bd99e058bd7290b4bbb84064ba3101a5
  | 4, 8 => 0xf34e20f7f3103114f202b0c6f1d230d8f0ba310af02dd182ee551110ed63911bed5e0161ec061191eb3df0e6e8fb2079e89a3150e87db049e82a1151e73cc102e725c095e6175015e4846002e404205ae349c048e26560f5e1bcb000e127615bdfcf719bddd8214add64e0f0dcc25152dc59e141dc2bd050dc125157db85012b
  | 4, 9 => 0xff0bd113fe98c038fd9e20f2fd78d099fce910a8fc9ef103fc6fd124fc505163faceb09af99cd036f616b183f5c1f0b8f508b129f3912085
  | 5, 0 => 0xfd78d009faceb00af1d23018ec061021e725c005dfcf702bd84ff020c7627012b3f6f0008853b00779505008774b902773b9e0066dc33010614040285d9ed003586ae00257ea00174aa8e001446f401136a870221286101b0ecef00b06beb004
  | 6, 0 => 0x761bc00b
  | _, _ => 0

def hintCount : ℕ → ℕ
  | 2 => 66
  | 3 => 279
  | 4 => 302
  | 5 => 24
  | 6 => 1
  | _ => 0

def hints : Compact.CodeBook := ⟨20,12,hintPage,hintCount⟩

def locate : ℕ → List W → ℕ × ℕ := Compact.lookup table hints 0xbf58476d1ce4e5b9
def check : ℕ → ℕ → Bool := Compact.check table target negative startMask locate switches (fun _ _ => false)

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page2at0 : span (check 2) 4 0 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page2at4 : span (check 2) 2 4 = true := by apply block2 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer2 : span (check 2) 6 0 = true := span_join (page2at0) (page2at4)

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at0 : span (check 3) 4 0 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at4 : span (check 3) 4 4 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at8 : span (check 3) 4 8 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at12 : span (check 3) 4 12 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at16 : span (check 3) 4 16 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at20 : span (check 3) 4 20 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at24 : span (check 3) 4 24 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at28 : span (check 3) 2 28 = true := by apply block2 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer3 : span (check 3) 30 0 = true := span_join (span_join (span_join (page3at0) (page3at4)) (span_join (page3at8) (page3at12))) (span_join (span_join (page3at16) (page3at20)) (span_join (page3at24) (page3at28)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at0 : span (check 4) 4 0 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at4 : span (check 4) 4 4 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at8 : span (check 4) 4 8 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at12 : span (check 4) 4 12 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at16 : span (check 4) 4 16 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at20 : span (check 4) 4 20 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at24 : span (check 4) 4 24 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer4 : span (check 4) 28 0 = true := span_join (span_join (span_join (page4at0) (page4at4)) (span_join (page4at8) (page4at12))) (span_join (span_join (page4at16) (page4at20)) (page4at24))

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at0 : span (check 5) 3 0 = true := by apply block3 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer5 : span (check 5) 3 0 = true := page5at0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at0 : span (check 6) 1 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer6 : span (check 6) 1 0 = true := page6at0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem validated (k : ℕ) (hk : k ≤ 6) (i : ℕ) (hi : i < count k) : check k i = true := by
  have e : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [count] at hi
  · simp [count] at hi
  · exact span_member layer2 i (by omega) (by simpa [count] using hi)
  · exact span_member layer3 i (by omega) (by simpa [count] using hi)
  · exact span_member layer4 i (by omega) (by simpa [count] using hi)
  · exact span_member layer5 i (by omega) (by simpa [count] using hi)
  · exact span_member layer6 i (by omega) (by simpa [count] using hi)

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem bound : signedLower target raw 7 :=
  Compact.lower table target positive raw essential negative neg startMask 6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) locate switches valid fixed (fun _ _ => false)
    (by intros; rfl) validated

end LeafK4

end GraphSignedFrontier

namespace GraphSignedFrontier

namespace LeafSeed8

def target : W := 0xfeeefee8feeefee8feeefee8feeefee8
def raw : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000]
def negative : List ℕ := [0, 1, 2, 4, 8, 16, 20, 24]

set_option maxHeartbeats 0 in
set_option maxRecDepth 3600 in
theorem positive : target ≠ 0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 3600 in
theorem unique : raw.Nodup := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 3600 in
theorem neg : ∀ r ∈ negative, r < 128 ∧ target.getLsbD r = false := by
  intro r hr
  have yes : (negative.all fun j => decide (j < 128 ∧ target.getLsbD j = false)) = true := by decide +kernel
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp yes r hr

set_option maxHeartbeats 0 in
set_option maxRecDepth 3600 in
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · refine ⟨2,3,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : W) ∨ z.getLsbD 2 = z.getLsbD 3)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,3,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xcccccccccccccccccccccccccccccccc : W) ∨ z.getLsbD 1 = z.getLsbD 3)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : W) ∨ z.getLsbD 1 = z.getLsbD 5)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,9,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xff00ff00ff00ff00ff00ff00ff00ff00 : W) ∨ z.getLsbD 1 = z.getLsbD 9)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,17,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffff0000ffff0000ffff0000ffff0000 : W) ∨ z.getLsbD 1 = z.getLsbD 17)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd

def pin (r : Fin 128) : Fin 128 := Fin.ofNat 128 (r.val % 16)

set_option maxHeartbeats 0 in
set_option maxRecDepth 3600 in
theorem imageGoal : signedMap pin target = LeafK4.target := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 3600 in
theorem bound : signedLower target raw 8 := by
  apply signedLower_of_saved_pin target positive raw essential LeafK4.raw 7 pin
  · rw [imageGoal]
    exact LeafK4.positive
  · intro w hw
    have test : (raw.all fun w => decide (signedMap pin w = 0 ∨
        signedMap pin w ∈ LeafK4.raw)) = true := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp test w hw)
  · refine ⟨raw.getD 4 0, ?_, ?_⟩ <;> decide +kernel
  · rw [imageGoal]
    exact LeafK4.bound

end LeafSeed8

namespace LeafSeed9

def target : W := 0xfffffee8fffffee8fffffee8fffffee8
def raw : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000]
def negative : List ℕ := [0, 1, 2, 4, 8]

set_option maxHeartbeats 0 in
set_option maxRecDepth 3600 in
theorem positive : target ≠ 0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 3600 in
theorem unique : raw.Nodup := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 3600 in
theorem neg : ∀ r ∈ negative, r < 128 ∧ target.getLsbD r = false := by
  intro r hr
  have yes : (negative.all fun j => decide (j < 128 ∧ target.getLsbD j = false)) = true := by decide +kernel
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp yes r hr

set_option maxHeartbeats 0 in
set_option maxRecDepth 3600 in
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · refine ⟨2,3,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : W) ∨ z.getLsbD 2 = z.getLsbD 3)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,3,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xcccccccccccccccccccccccccccccccc : W) ∨ z.getLsbD 1 = z.getLsbD 3)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : W) ∨ z.getLsbD 1 = z.getLsbD 5)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,9,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xff00ff00ff00ff00ff00ff00ff00ff00 : W) ∨ z.getLsbD 1 = z.getLsbD 9)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨0,16,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffff0000ffff0000ffff0000ffff0000 : W) ∨ z.getLsbD 0 = z.getLsbD 16)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd

def pin (r : Fin 128) : Fin 128 := Fin.ofNat 128 (r.val % 16)

set_option maxHeartbeats 0 in
set_option maxRecDepth 3600 in
theorem imageGoal : signedMap pin target = LeafK4.target := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 3600 in
theorem bound : signedLower target raw 8 := by
  apply signedLower_of_saved_pin target positive raw essential LeafK4.raw 7 pin
  · rw [imageGoal]
    exact LeafK4.positive
  · intro w hw
    have test : (raw.all fun w => decide (signedMap pin w = 0 ∨
        signedMap pin w ∈ LeafK4.raw)) = true := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp test w hw)
  · refine ⟨raw.getD 4 0, ?_, ?_⟩ <;> decide +kernel
  · rw [imageGoal]
    exact LeafK4.bound

end LeafSeed9

end GraphSignedFrontier

namespace GraphSignedFrontier

namespace LeafSix1

def target : W := 0xfffefefeffeeee88fffefefeffeeee88
def raw : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000]
def negative : List ℕ := [0, 1, 2, 4, 5, 6, 8, 12, 16, 20, 32, 40, 48]

set_option maxRecDepth 3800 in
set_option maxHeartbeats 0 in
theorem positive : target ≠ 0 := by decide +kernel
set_option maxRecDepth 3800 in
set_option maxHeartbeats 0 in
theorem unique : raw.Nodup := by decide +kernel

set_option maxRecDepth 3800 in
set_option maxHeartbeats 0 in
theorem neg : ∀ r ∈ negative, r < 128 ∧ target.getLsbD r = false := by
  intro r hr
  have yes : (negative.all fun j => decide (j < 128 ∧ target.getLsbD j = false)) = true := by decide +kernel
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp yes r hr

set_option maxRecDepth 3800 in
set_option maxHeartbeats 0 in
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨2,3,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : W) ∨ z.getLsbD 2 = z.getLsbD 3)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,3,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xcccccccccccccccccccccccccccccccc : W) ∨ z.getLsbD 1 = z.getLsbD 3)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨32,36,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : W) ∨ z.getLsbD 32 = z.getLsbD 36)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,9,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xff00ff00ff00ff00ff00ff00ff00ff00 : W) ∨ z.getLsbD 1 = z.getLsbD 9)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,17,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffff0000ffff0000ffff0000ffff0000 : W) ∨ z.getLsbD 1 = z.getLsbD 17)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,33,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffffffff00000000ffffffff00000000 : W) ∨ z.getLsbD 1 = z.getLsbD 33)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd

def x : W := raw.getD 2 0
def lo := SixRules.project 2 false
def hi := SixRules.project 2 true

set_option maxRecDepth 3800 in
set_option maxHeartbeats 0 in
theorem condition (e : Bool) : signedMap (if e then hi else lo) target =
    if e then LeafSeed9.target else LeafSeed8.target := by cases e <;> decide +kernel

set_option maxRecDepth 3800 in
set_option maxHeartbeats 0 in
theorem positivePin (e : Bool) : signedMap (if e then hi else lo) target ≠ 0 := by
  rw [condition]
  cases e <;> decide +kernel

set_option maxRecDepth 3800 in
set_option maxHeartbeats 0 in
theorem stable (u : W) (h : u ∈ raw) (ne : u ≠ x) : rowMap lo u = rowMap hi u := by
  have checked : (raw.all fun v => decide (v = x ∨ rowMap lo v = rowMap hi v)) = true := by decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp checked u h)).resolve_left ne

set_option maxRecDepth 3800 in
set_option maxHeartbeats 0 in
theorem bound : signedLower target raw 10 := by
  intro k s cone sub
  have initial := cone.initial positive raw essential sub
  rw [initial] at cone
  have live : x ∈ raw.toFinset := by decide +kernel
  obtain ⟨choice,j,t,gap,out,foot⟩ := cone.twoPinLoss lo hi x target (by decide +kernel)
    (by decide +kernel) positivePin live (fun v hv => stable v (List.mem_toFinset.mp hv))
  have start : t ⊆ insert 0 SixRules.raw5.toFinset := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (foot hw)
    have hs := List.mem_toFinset.mp hv
    cases choice
    · simpa [lo] using SixRules.rawStock 2 false v hs
    · simpa [hi] using SixRules.rawStock 2 true v hs
  have enough : 8 ≤ j := by
    have exactWord := condition choice
    rw [exactWord] at out
    cases choice
    · exact LeafSeed8.bound out start
    · exact LeafSeed9.bound out start
  omega

end LeafSix1

end GraphSignedFrontier

namespace GraphSignedFrontier.DeskCases

open GraphSeven (leafRaw leafGoal)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem transfer (a b : W) (path : List Switch) (valid : ∀ sw ∈ path, sw.Valid)
    (target : reindex path a = b)
    (raw : (insert 0 leafRaw.toFinset).image (reindex path) = insert 0 leafRaw.toFinset)
    (ordinary : signedLower b leafRaw 10) : signedLower a leafRaw 10 := by
  intro k s cone sub
  have allied := cone.reindex path valid
  rw [target] at allied
  have same := Finset.image_subset_image (f := reindex path) sub
  rw [raw] at same
  exact ordinary allied same

def x0x4 : Switch := ⟨15, 0xaaaa0000aaaa0000aaaa0000aaaa, 0x55550000555500005555000055550000⟩
set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem x0x4Valid : x0x4.Valid := by unfold Switch.Valid; decide +kernel

def x1x5 : Switch := ⟨30, 0xcccccccc00000000cccccccc, 0x33333333000000003333333300000000⟩
set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem x1x5Valid : x1x5.Valid := by unfold Switch.Valid; decide +kernel

def x2x3 : Switch := ⟨4, 0xf000f000f000f000f000f000f000f0, 0xf000f000f000f000f000f000f000f00⟩
set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem x2x3Valid : x2x3.Valid := by unfold Switch.Valid; decide +kernel

def x4x5 : Switch := ⟨16, 0xffff000000000000ffff0000, 0xffff000000000000ffff00000000⟩
set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem x4x5Valid : x4x5.Valid := by unfold Switch.Valid; decide +kernel

def x0x2 : Switch := ⟨3, 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 0x50505050505050505050505050505050⟩
set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem x0x2Valid : x0x2.Valid := by unfold Switch.Valid; decide +kernel

def x1x2 : Switch := ⟨2, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 0x30303030303030303030303030303030⟩
set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem x1x2Valid : x1x2.Valid := by unfold Switch.Valid; decide +kernel

def x3x4 : Switch := ⟨8, 0xff000000ff000000ff000000ff00, 0xff000000ff000000ff000000ff0000⟩
set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem x3x4Valid : x3x4.Valid := by unfold Switch.Valid; decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem from0to2 (h : signedLower (leafGoal 0) leafRaw 10) :
    signedLower (leafGoal 2) leafRaw 10 := by
  refine transfer _ _ [x0x4, x1x5, x2x3, x4x5] ?_ (by decide +kernel) (by decide +kernel) h
  intro sw mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl <;> first | exact x0x4Valid | exact x1x5Valid | exact x2x3Valid | exact x4x5Valid

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem from1to3 (h : signedLower (leafGoal 1) leafRaw 10) :
    signedLower (leafGoal 3) leafRaw 10 := by
  refine transfer _ _ [x0x2, x1x2, x3x4] ?_ (by decide +kernel) (by decide +kernel) h
  intro sw mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl <;> first | exact x0x2Valid | exact x1x2Valid | exact x3x4Valid

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem from4to5 (h : signedLower (leafGoal 4) leafRaw 10) :
    signedLower (leafGoal 5) leafRaw 10 := by
  refine transfer _ _ [x0x2] ?_ (by decide +kernel) (by decide +kernel) h
  intro sw mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl <;> first | exact x0x2Valid

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem allCases (zero : signedLower (leafGoal 0) leafRaw 10)
    (four : signedLower (leafGoal 4) leafRaw 10) :
    ∀ v : Fin 6, signedLower (leafGoal v) leafRaw 10 := by
  intro v k s cone stock
  have e : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by omega
  have one : signedLower (leafGoal 1) leafRaw 10 := LeafSix1.bound
  rcases e with rfl | rfl | rfl | rfl | rfl | rfl
  · exact zero cone stock
  · exact one cone stock
  · exact from0to2 zero cone stock
  · exact from1to3 one cone stock
  · exact four cone stock
  · exact from4to5 four cone stock

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem deskStatement (zero : signedLower (leafGoal 0) leafRaw 10)
    (four : signedLower (leafGoal 4) leafRaw 10) :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _notUnique hit
  exact OneNot30959.replacement (allCases zero four) gates o legal hit

end GraphSignedFrontier.DeskCases

namespace GraphSignedFrontier

namespace LayerSeed0

def target : W := 0xfeeefaa0feeefaa0feeefaa0feeefaa0
def raw : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000]
def negative : List ℕ := [0, 1, 2, 3, 4, 6, 8, 10, 16, 20, 24]

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem positive : target ≠ 0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem unique : raw.Nodup := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem neg : ∀ r ∈ negative, r < 128 ∧ target.getLsbD r = false := by
  intro r hr
  have yes : (negative.all fun j => decide (j < 128 ∧ target.getLsbD j = false)) = true := by decide +kernel
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp yes r hr

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · refine ⟨4,5,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : W) ∨ z.getLsbD 4 = z.getLsbD 5)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨16,18,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xcccccccccccccccccccccccccccccccc : W) ∨ z.getLsbD 16 = z.getLsbD 18)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : W) ∨ z.getLsbD 1 = z.getLsbD 5)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,9,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xff00ff00ff00ff00ff00ff00ff00ff00 : W) ∨ z.getLsbD 1 = z.getLsbD 9)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,17,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffff0000ffff0000ffff0000ffff0000 : W) ∨ z.getLsbD 1 = z.getLsbD 17)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd

def dictionary : ℕ → ℕ
  | 0 => 0x5500ff0000fa00faeeeeeeeeccff000055ff00000fff00000000eeeeaaaa000033330000fffff0f0fff0fff0faaafaaaccccccccffccff00fcfcf0f0ffff00003300ff00fafaf0f0cccc000000ff00000000aaaaccee0000f0f0f0f0eeee00001100ff00ffeeff00aaaaaaaafefef0f0ff00ff00f0fff0f0eeeeaaaa00000000
  | 1 => 0xfffff000ffffaaaaffffa0a0ffff3030f000f000fcccfcccfaf0faf0eeeeccccececececcceecceeccccfcfccccceeee0aaa0aaaccccc0c0cccc8888cccc4444cccc00cc2222aaaac4c4c4c4bbbbaaaabbbb000044cc44cc4444cccc44444444444400003333303033332222111100000ccc0cccfa00fa00f000ff005f005f00
  | 2 => 0xffffccccfcfcfcfcfafafafaf0f00000c0c0c0c0a0a0a0a0888888885555000050505050303030302222222200f000f000cc00cc00aa00aa0000f0f00000cccc
  | _ => 0

def packed : ℕ → ℕ → ℕ
  | 2, 0 => 0x60814184020c101
  | 3, 0 => 0x2c0c4812054a132048885200c881200c481202408f0610405063868506086850624088062408c062408b0624405062440b06245051220287
  | 4, 0 => 0x20249851e404930a788091a1478312744050624e85320c4882614189384c283124c29b0624985340c4930a641891a14c0312342970624685180c48d0a2c01006240800624405
  | 4, 1 => 0x200c4ad0a40189581480312ac29006242aa200c48552401890aa0803121539006242a6200c4854a401890a5c803121521006242a320884930a404a126148092615010124c29f
  | 4, 2 => 0x200c4812640189023480312042900624405200c4b70a401896c1480312d42900625a05200c4935c4018926cc80312c82900625885200c4b00a401895e14803123429006246ae
  | 4, 3 => 0x7e0c4930af88031275e83124c2bc06249852055d930a401912614803223429006e8485200c7130a401b9261480328249900608985200c49d0a401893aa080312745900625c05
  | 4, 4 => 0x160624685
  | 5, 0 => 0x200c4930b1c803124c2a8200c4930a5c803124c2c6200c4930b14803124c28c200c4930b10803124c2c3200c4930b08803124c2c1200c4930b00803124c28b00401893a14010062468500401890aa00100624297
  | 5, 1 => 0xb1006249859e401892615f100624985205418926148039c24985200e68926148031330985200c4bb26148031274985200c4931a14803124e585200c4930a60803124c2ca200c4930b24803124c2c8
  | 6, 0 => 0x100624985
  | _, _ => 0

def count : ℕ → ℕ
  | 2 => 3
  | 3 => 16
  | 4 => 65
  | 5 => 31
  | 6 => 1
  | _ => 0

def table : Compact.PoolData := ⟨32,0x1000000010000000100000001,7,dictionary,packed,count⟩
def startMask : ℕ := 0xfeeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0
def swap2x3 : Switch := ⟨4, 0xf000f000f000f000f000f000f000f0, 0xf000f000f000f000f000f000f000f00⟩

def switchPool : List (List Switch) := [[swap2x3], []]
def switches (i : ℕ) : List Switch := switchPool.getD i []

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem valid (j : ℕ) : ∀ s ∈ switches j, s.Valid := by
  intro s hs
  by_cases inRange : j < switchPool.length
  · have actual : switchPool[j] ∈ switchPool := List.getElem_mem inRange
    have checked : (switchPool.all fun xs => xs.all fun q =>
        @decide q.Valid (by unfold Switch.Valid; infer_instance)) = true := by decide +kernel
    rw [switches, List.getD_eq_getElem _ _ inRange] at hs
    letI : Decidable s.Valid := by unfold Switch.Valid; infer_instance
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked _ actual) s hs)
  · rw [switches, List.getD_eq_default _ _ (by omega)] at hs
    simp at hs

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem fixed (j : ℕ) : reindex (switches j) target = target := by
  by_cases inRange : j < switchPool.length
  · have checked : (switchPool.all fun moves => decide (reindex moves target = target)) = true := by decide +kernel
    rw [switches,List.getD_eq_getElem _ _ inRange]
    exact of_decide_eq_true (List.all_eq_true.mp checked _ (List.getElem_mem inRange))
  · rw [switches, List.getD_eq_default _ _ (by omega)]
    rfl

def hintPage : ℕ → ℕ → ℕ
  | 2, 0 => 0xfcafc011dfc20000d4113010be1eb001933cd021
  | 3, 0 => 0xfb4120a0dea0d0d1d9cf6091c9e660c1c96c9050c8bb7080be8f7011bd352000b130d090b112102196f6601091e9108183ab2070782b80a171f3805168f3e0e1642370016207d07160d620b1602630f14c5a50c04404f0f043da00311aa3c06107dee041
  | 4, 0 => 0x448e812143da00014156b1e13df5c2c13db2d1413c6e32b13bff31c1374c7161359d23012e4f73702a0520a129a3b0802766a1b12747d3d023380131225ae0e12170d1511fcd01111da251911c14a0d11b7b028115dca03110e9c2510db0d2410d7142200b3690610aa280f004bf4211044bd081040f540103a6a3c0024f73f1
  | 4, 1 => 0xad8db0c1ad3e7171ace73360abc80021a222c3219f2a40d09e3e71819704f23194c292d19169a3619024e1c08ebf20b18d35a100878ce0f182418201744b83e16f1e23c16e0ef3b16dcf83916d55b0306c5b81a164e4d1f162c3e3516269711060f8231160d620115c3412905bbbb3a0518370e04d69d2914d0cf180470142f1
  | 4, 2 => 0xf91f8071f85db250f77d1371f3d3f090f3c01331f0437390efc371d1edb9c271e93f2340e7ee1400e03312b0dea02261db8902e1db31d130d947c3a1ce6cb221cc18c2a0cc15a1f0cb0be2a1c79bd341c5ff5101b8948381b7e39041b7724120b48e3051aeb143d1ada44091
  | 5, 0 => 0xbc3b8051ae12b0f0a8c1e061a5c7a060826f70917b70a0a17906d101736c10c0716751916dd5a0c16c5b801169a351e167def1715b5c019057ba908152aa01d15286a0e15205c1214d8211e044c4a0f13e8b01413c24f180374c700130c431a024af61c11d7790d11a223131115c00410ca1d11108eab07104bf402100da7090
  | 5, 1 => 0xf79490b1f4ea7070f3c01031ebedf120eaea6151e621d1a1e58e8181e1418080d9eb3161d2e9b0a0d26bb1b1c17e3140
  | 6, 0 => 0x70378001
  | _, _ => 0

def hintCount : ℕ → ℕ
  | 2 => 5
  | 3 => 25
  | 4 => 91
  | 5 => 44
  | 6 => 1
  | _ => 0

def hints : Compact.CodeBook := ⟨20,12,hintPage,hintCount⟩

def locate : ℕ → List W → ℕ × ℕ := Compact.lookup table hints 0xbf58476d1ce4e5b9
def check : ℕ → ℕ → Bool := Compact.check table target negative startMask locate switches (fun _ _ => false)

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page2at0 : span (check 2) 3 0 = true := by apply block3 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer2 : span (check 2) 3 0 = true := page2at0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at0 : span (check 3) 4 0 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at4 : span (check 3) 4 4 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at8 : span (check 3) 4 8 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at12 : span (check 3) 4 12 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer3 : span (check 3) 16 0 = true := span_join (span_join (page3at0) (page3at4)) (span_join (page3at8) (page3at12))

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at0 : span (check 4) 4 0 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at4 : span (check 4) 4 4 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at8 : span (check 4) 4 8 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at12 : span (check 4) 4 12 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at16 : span (check 4) 4 16 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at20 : span (check 4) 4 20 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at24 : span (check 4) 4 24 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at28 : span (check 4) 4 28 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at32 : span (check 4) 4 32 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at36 : span (check 4) 4 36 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at40 : span (check 4) 4 40 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at44 : span (check 4) 4 44 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at48 : span (check 4) 4 48 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at52 : span (check 4) 4 52 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at56 : span (check 4) 4 56 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at60 : span (check 4) 4 60 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at64 : span (check 4) 1 64 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer4 : span (check 4) 65 0 = true := span_join (span_join (span_join (span_join (span_join (page4at0) (page4at4)) (page4at8)) (span_join (page4at12) (page4at16))) (span_join (span_join (page4at20) (page4at24)) (span_join (page4at28) (page4at32)))) (span_join (span_join (span_join (page4at36) (page4at40)) (span_join (page4at44) (page4at48))) (span_join (span_join (page4at52) (page4at56)) (span_join (page4at60) (page4at64))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at0 : span (check 5) 4 0 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at4 : span (check 5) 4 4 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at8 : span (check 5) 4 8 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at12 : span (check 5) 4 12 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at16 : span (check 5) 4 16 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at20 : span (check 5) 4 20 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at24 : span (check 5) 4 24 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at28 : span (check 5) 3 28 = true := by apply block3 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer5 : span (check 5) 31 0 = true := span_join (span_join (span_join (page5at0) (page5at4)) (span_join (page5at8) (page5at12))) (span_join (span_join (page5at16) (page5at20)) (span_join (page5at24) (page5at28)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at0 : span (check 6) 1 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer6 : span (check 6) 1 0 = true := page6at0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem validated (k : ℕ) (hk : k ≤ 6) (i : ℕ) (hi : i < count k) : check k i = true := by
  have e : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [count] at hi
  · simp [count] at hi
  · exact span_member layer2 i (by omega) (by simpa [count] using hi)
  · exact span_member layer3 i (by omega) (by simpa [count] using hi)
  · exact span_member layer4 i (by omega) (by simpa [count] using hi)
  · exact span_member layer5 i (by omega) (by simpa [count] using hi)
  · exact span_member layer6 i (by omega) (by simpa [count] using hi)

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem fullBound : signedLower target raw 7 :=
  Compact.lower table target positive raw essential negative neg startMask 6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) locate switches valid fixed (fun _ _ => false)
    (by intros; rfl) validated

end LayerSeed0

end GraphSignedFrontier

namespace GraphSignedFrontier.ExampleSix

def target : W := 0xfffffeecfffffeecfffffeecfffffeec
def raw : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000]
def negative : List ℕ := [0, 1, 4, 8]

theorem positive : target ≠ 0 := by decide +kernel
theorem unique : raw.Nodup := by decide +kernel

theorem neg : ∀ r ∈ negative, r < 128 ∧ target.getLsbD r = false := by
  intro r hr
  have yes : (negative.all fun j => decide (j < 128 ∧ target.getLsbD j = false)) = true := by decide +kernel
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp yes r hr

theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · refine ⟨4,5,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : W) ∨ z.getLsbD 4 = z.getLsbD 5)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨0,2,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xcccccccccccccccccccccccccccccccc : W) ∨ z.getLsbD 0 = z.getLsbD 2)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : W) ∨ z.getLsbD 1 = z.getLsbD 5)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,9,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xff00ff00ff00ff00ff00ff00ff00ff00 : W) ∨ z.getLsbD 1 = z.getLsbD 9)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨0,16,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffff0000ffff0000ffff0000ffff0000 : W) ∨ z.getLsbD 0 = z.getLsbD 16)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd

set_option maxHeartbeats 0 in
theorem checked : feasible target negative 5 raw = false := by decide +kernel

theorem bound : signedLower target raw 6 := by
  intro k s cone sub
  by_contra! small
  have eq := cone.initial positive raw essential sub
  rw [eq] at cone
  have yes := feasible_complete positive negative neg 5 raw unique k (by omega) cone
  simp [checked] at yes

end GraphSignedFrontier.ExampleSix

namespace GraphSignedFrontier

namespace LeafSeed2

def target : W := 0xfeeef888feeef888feeef888feeef888
def raw : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000]
def negative : List ℕ := [0, 1, 2, 4, 5, 6, 8, 9, 10, 16, 20, 24]

theorem positive : target ≠ 0 := by decide +kernel
theorem unique : raw.Nodup := by decide +kernel

theorem neg : ∀ r ∈ negative, r < 128 ∧ target.getLsbD r = false := by
  intro r hr
  have yes : (negative.all fun j => decide (j < 128 ∧ target.getLsbD j = false)) = true := by decide +kernel
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp yes r hr

theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · refine ⟨2,3,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : W) ∨ z.getLsbD 2 = z.getLsbD 3)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,3,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xcccccccccccccccccccccccccccccccc : W) ∨ z.getLsbD 1 = z.getLsbD 3)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨8,12,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : W) ∨ z.getLsbD 8 = z.getLsbD 12)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨4,12,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xff00ff00ff00ff00ff00ff00ff00ff00 : W) ∨ z.getLsbD 4 = z.getLsbD 12)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,17,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffff0000ffff0000ffff0000ffff0000 : W) ∨ z.getLsbD 1 = z.getLsbD 17)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd

set_option maxHeartbeats 0 in
theorem checked : feasible target negative 5 raw = false := by decide +kernel

theorem bound : signedLower target raw 6 := by
  intro k s cone sub
  by_contra! small
  have eq := cone.initial positive raw essential sub
  rw [eq] at cone
  have yes := feasible_complete positive negative neg 5 raw unique k (by omega) cone
  simp [checked] at yes

end LeafSeed2

end GraphSignedFrontier

namespace GraphSignedFrontier

namespace LeafSeed10

def target : W := 0xfefeee88fefeee88fefeee88fefeee88
def raw : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000]
def negative : List ℕ := [0, 1, 2, 4, 5, 6, 8, 12, 16, 24]

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem positive : target ≠ 0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem unique : raw.Nodup := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem neg : ∀ r ∈ negative, r < 128 ∧ target.getLsbD r = false := by
  intro r hr
  have yes : (negative.all fun j => decide (j < 128 ∧ target.getLsbD j = false)) = true := by decide +kernel
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp yes r hr

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · refine ⟨2,3,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : W) ∨ z.getLsbD 2 = z.getLsbD 3)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,3,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xcccccccccccccccccccccccccccccccc : W) ∨ z.getLsbD 1 = z.getLsbD 3)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨16,20,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : W) ∨ z.getLsbD 16 = z.getLsbD 20)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,9,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xff00ff00ff00ff00ff00ff00ff00ff00 : W) ∨ z.getLsbD 1 = z.getLsbD 9)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,17,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffff0000ffff0000ffff0000ffff0000 : W) ∨ z.getLsbD 1 = z.getLsbD 17)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd

def dictionary : ℕ → ℕ
  | 0 => 0xf0f0000ffffaaaafafafafafafa0000f0f0a0a0f0f000f030300000ffffee00ffff8888fff0ff00ff88ff88f0f0f0f0eeeeeeee0f00ff000000ff00f0f0ff00ffff0000ff0fff00fefe0000ff00ff0000ff0000f0f00000aaaaaaaa0f0fff00fefeaaaafcfcccccfafaaaaa0c0cccccffffff00ccccccccbabaaaaa00000000
  | 1 => 0xf0f0fafa88888888eeeeaaaaeeaaeeaa44cc44cc4444ccccf0f0f000f0f03030f030f030babababab0b0b0b0afafaaaaafaf0000707070703232323230f030f03030f0f0101010100f0f0f000f0f0a0a03030000f0f0fff0ee00ee00aa00ff00770077003300ff0000ee00eef000ff0030303030f0ff00007777000033ff0000
  | 2 => 0xfffff0f0fff0fff0ffaaffaaff000000f000f000aaaa0000aa00aa00a0a0a0a033003300222222220f000f000a0a0a0a00f000f000aa00aa333300000000f0f0ffffaa00ffff0f00ffaaff00ff33ff00fefefefe505050500000aaaafafaf0f0faf0faf0f8f8f8f8f2f2f2f2f0faf0fa
  | _ => 0

def packed : ℕ → ℕ → ℕ
  | 2, 0 => 0xc38206182830a08185080c101
  | 3, 0 => 0x1e582821e54a131e303821e303051e302821e302841e301011e141121e141111e401091e084881c281091834109181410b1408488000c282
  | 3, 1 => 0x678e82063c28206302820614a02061450206141090670109066c1090668109062810906284840608499060848830501092e30a13
  | 4, 0 => 0x1e50109243ca021294794042488f34084911e28109243c50212447a40424f8f04251911e0849f22311140424614042508c28084a018281093e30502122c00314084801e30282
  | 4, 1 => 0x1e30109603c60212bc78c042518f18084991e301095c3c60212b478c042560f180849f1e30109563ce8212447aa042488f28901091e51482123ca0212a0794042538f28084a6
  | 4, 2 => 0x1e30a09763c61412e878c282420f18e41091e30d82123c638042478c340848f18281091e30509083c637042478c04d848f1809a891e30134123c602662478c042590f18084b1
  | 4, 3 => 0x1e30e828c3c61d051478c880848f1814a021e3028a043c605042478c380848f190c1091e32102123c641042478c800848f18a81091e31f82123c61426f878c28f410f1851e02
  | 4, 4 => 0x6501099a0ca021244194042661e1e30e829630a02125c614042650c280848f2c501091e58502123e4940424795280848f90501091e38a02123c702127c78c8e0848f1874109
  | 4, 5 => 0x19e28084831e74109063ca02120c7b9042418f14084831e084a3063c1095a0c782127c18c14084832828109
  | 5, 0 => 0x1e30a02134878c280849f1e30a02134478c28084d01e30a02122c78c28084cf1e30a02133878c28084911e30a02133078c28084c5000c794042400f1874109003c60a042400f18084a3003c602127c00f2808491
  | 5, 1 => 0xb63c6140424f0f18501091f6861404247d918501091e32c14042478c3a501091e30a0a042478c295c1091e30a13042478c28084d61e30a02135478c28084d41e30a0212f878c28084cd1e30a02134c78c28084a3
  | 5, 2 => 0x18f1850109
  | 6, 0 => 0xf1850109
  | _, _ => 0

def count : ℕ → ℕ
  | 2 => 5
  | 3 => 31
  | 4 => 90
  | 5 => 33
  | 6 => 1
  | _ => 0

def table : Compact.PoolData := ⟨32,0x1000000010000000100000001,7,dictionary,packed,count⟩
def startMask : ℕ := 0xfefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88fefeee88
def swap0x1 : Switch := ⟨1, 0x22222222222222222222222222222222, 0x44444444444444444444444444444444⟩

def switchPool : List (List Switch) := [[swap0x1], []]
def switches (i : ℕ) : List Switch := switchPool.getD i []

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem valid (j : ℕ) : ∀ s ∈ switches j, s.Valid := by
  intro s hs
  by_cases inRange : j < switchPool.length
  · have actual : switchPool[j] ∈ switchPool := List.getElem_mem inRange
    have checked : (switchPool.all fun xs => xs.all fun q =>
        @decide q.Valid (by unfold Switch.Valid; infer_instance)) = true := by decide +kernel
    rw [switches, List.getD_eq_getElem _ _ inRange] at hs
    letI : Decidable s.Valid := by unfold Switch.Valid; infer_instance
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked _ actual) s hs)
  · rw [switches, List.getD_eq_default _ _ (by omega)] at hs
    simp at hs

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem fixed (j : ℕ) : reindex (switches j) target = target := by
  by_cases inRange : j < switchPool.length
  · have checked : (switchPool.all fun moves => decide (reindex moves target = target)) = true := by decide +kernel
    rw [switches,List.getD_eq_getElem _ _ inRange]
    exact of_decide_eq_true (List.all_eq_true.mp checked _ (List.getElem_mem inRange))
  · rw [switches, List.getD_eq_default _ _ (by omega)]
    rfl

def hintPage : ℕ → ℕ → ℕ
  | 2, 0 => 0xfbe39010f84c8020cccd2000c76d204181078031801d202153d5300145e2d040342d0011
  | 3, 0 => 0xa03780419b548080900dd1c08c4520f184700101815fa090801d20017c2941617bffa0d17a38e1d1791d61e176a4f130705031406da381a06d01a1706cb921516993d1e05a9580114aadd07049d0913145cd002144c9b031446001b1359a00c134afa0b12eaca1712325208120c9014117de71c10d31b0610867b091047480f0
  | 3, 1 => 0xfa7550d0f84c8000f57421a1f26841d0e8bf80a1df5a4051de77a190d27e7071d146c0e1c5584111c2891121bdfc6020bc8f61b0b4099191b07610a0acdf00b0a8c2d181a2266180
  | 4, 0 => 0x359d231034d3e4a134afa0013269002130fc050130bbc2912e4f74612dafe4c12b3771c029acd2202766a2e12747d4b124e2b270244762d1223603b021def400219422b0214ba2812116d2611e5090801e2654c01a5c83e117ac51211561b2a1133dc2600fc120b10ea6d1810e0650d10aa281e1047a7511044bd04003e4c041
  | 4, 1 => 0x6eca32316cb920116c03135068e514f1689c13a167683580671a220166d4e5516438d230626971f060c443305ead00f15dfaf1a15d5553915cc5b1715cb7a1905c3df3215bbbb46056b8e3905592b1b1543015214dc523f14bfae0614af341614761908147014311448e81413ff213513bff32f13951f3f03853649136a41221
  | 4, 2 => 0xaf2f5240ad247401acdf0000ac75a071aa06a3b1a992c1d1a8f99131a8aa22c1a89b42a0a38435319e178590968060e1930a23a09169a3818df8f1518d35a1e089e2103187b7d3e087ae7421878ce10186ad3301852ef38081aaa4518081c1d07c1bb21178e1320078e1247177bef1f173ce92d0726de4117121e3c0701ce591
  | 4, 3 => 0xf2adb581f13524e1f02a2341ef1c0541ee336561ee14f250edb9c2e0e93f2431e67c9331e33f22b1e2fdd091e1f95120e1d4c170e0331300dcd14441d947c3d0d55b8271ce8a90c1ce33b111cbd8d191cb73c371c7cd0481c60b0540c5ff5100c47454f0bfadc160bf1a70a1b8d3d360b67a74b0b673e251b5c0c571b2c57051
  | 4, 4 => 0xfe6311c1fb5482f0f9e6f241f8f283c1f7dd9361f77d13d1f7064440f42f64d1
  | 5, 0 => 0xa8c1e071a5c7a081826f70a18081c0207b70a0b17906d120736c1111716751a16dd5a10169a351f167def1815b5c01c157ba909052aa01e05286a0f05205c1414d82120144c4a1003e8b01403c24f1b130c431c024af61e121def040214ba0311d7791211a223161115c00610ea6d0110e0650010ca1d13108eab09100da70d1
  | 5, 1 => 0xf79490f1f4ea70c1ebedf151eaea6160e621d1a0e58e8191e14180c0d9eb3171d2e9b0e1d26bb1d1c17e3150bc3b8060b5c0c051ae12b110ad247041a992c021
  | 6, 0 => 0x70378001
  | _, _ => 0

def hintCount : ℕ → ℕ
  | 2 => 9
  | 3 => 50
  | 4 => 136
  | 5 => 48
  | 6 => 1
  | _ => 0

def hints : Compact.CodeBook := ⟨20,12,hintPage,hintCount⟩

def locate : ℕ → List W → ℕ × ℕ := Compact.lookup table hints 0xbf58476d1ce4e5b9
def check : ℕ → ℕ → Bool := Compact.check table target negative startMask locate switches (fun _ _ => false)

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page2at0 : span (check 2) 4 0 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page2at4 : span (check 2) 1 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer2 : span (check 2) 5 0 = true := span_join (page2at0) (page2at4)

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at0 : span (check 3) 4 0 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at4 : span (check 3) 4 4 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at8 : span (check 3) 4 8 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at12 : span (check 3) 4 12 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at16 : span (check 3) 4 16 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at20 : span (check 3) 4 20 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at24 : span (check 3) 4 24 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at28 : span (check 3) 3 28 = true := by apply block3 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer3 : span (check 3) 31 0 = true := span_join (span_join (span_join (page3at0) (page3at4)) (span_join (page3at8) (page3at12))) (span_join (span_join (page3at16) (page3at20)) (span_join (page3at24) (page3at28)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at0 : span (check 4) 4 0 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at4 : span (check 4) 4 4 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at8 : span (check 4) 4 8 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at12 : span (check 4) 4 12 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at16 : span (check 4) 4 16 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at20 : span (check 4) 4 20 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at24 : span (check 4) 4 24 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at28 : span (check 4) 4 28 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at32 : span (check 4) 4 32 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at36 : span (check 4) 4 36 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at40 : span (check 4) 4 40 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at44 : span (check 4) 4 44 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at48 : span (check 4) 4 48 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at52 : span (check 4) 4 52 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at56 : span (check 4) 4 56 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at60 : span (check 4) 4 60 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at64 : span (check 4) 4 64 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at68 : span (check 4) 4 68 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at72 : span (check 4) 4 72 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at76 : span (check 4) 4 76 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at80 : span (check 4) 4 80 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at84 : span (check 4) 4 84 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at88 : span (check 4) 2 88 = true := by apply block2 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer4 : span (check 4) 90 0 = true := span_join (span_join (span_join (span_join (span_join (page4at0) (page4at4)) (page4at8)) (span_join (span_join (page4at12) (page4at16)) (page4at20))) (span_join (span_join (span_join (page4at24) (page4at28)) (page4at32)) (span_join (span_join (page4at36) (page4at40)) (page4at44)))) (span_join (span_join (span_join (span_join (page4at48) (page4at52)) (page4at56)) (span_join (span_join (page4at60) (page4at64)) (page4at68))) (span_join (span_join (span_join (page4at72) (page4at76)) (page4at80)) (span_join (page4at84) (page4at88))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at0 : span (check 5) 4 0 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at4 : span (check 5) 4 4 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at8 : span (check 5) 4 8 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at12 : span (check 5) 4 12 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at16 : span (check 5) 4 16 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at20 : span (check 5) 4 20 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at24 : span (check 5) 4 24 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at28 : span (check 5) 4 28 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at32 : span (check 5) 1 32 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer5 : span (check 5) 33 0 = true := span_join (span_join (span_join (span_join (page5at0) (page5at4)) (page5at8)) (span_join (page5at12) (page5at16))) (span_join (span_join (page5at20) (page5at24)) (span_join (page5at28) (page5at32)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at0 : span (check 6) 1 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer6 : span (check 6) 1 0 = true := page6at0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem validated (k : ℕ) (hk : k ≤ 6) (i : ℕ) (hi : i < count k) : check k i = true := by
  have e : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [count] at hi
  · simp [count] at hi
  · exact span_member layer2 i (by omega) (by simpa [count] using hi)
  · exact span_member layer3 i (by omega) (by simpa [count] using hi)
  · exact span_member layer4 i (by omega) (by simpa [count] using hi)
  · exact span_member layer5 i (by omega) (by simpa [count] using hi)
  · exact span_member layer6 i (by omega) (by simpa [count] using hi)

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem bound : signedLower target raw 7 :=
  Compact.lower table target positive raw essential negative neg startMask 6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) locate switches valid fixed (fun _ _ => false)
    (by intros; rfl) validated

end LeafSeed10

end GraphSignedFrontier

namespace GraphSignedFrontier.LeafAliases

def raw : List W := LeafSeed2.raw

set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem transported (goal representative : W) (floor : ℕ)
    (moves : List Switch) (valid : ∀ s ∈ moves, s.Valid)
    (equal : reindex moves goal = representative)
    (stock : (insert 0 raw.toFinset).image (reindex moves) = insert 0 raw.toFinset)
    (lower : signedLower representative raw floor) : signedLower goal raw floor := by
  intro k s cone sub
  have transfer := cone.reindex moves valid
  rw [equal] at transfer
  have subset := Finset.image_subset_image (f := reindex moves) sub
  rw [stock] at subset
  exact lower transfer subset

def swap0x1 : Switch := ⟨1,0x22222222222222222222222222222222,0x44444444444444444444444444444444⟩
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem swap0x1Valid : swap0x1.Valid := by unfold Switch.Valid; decide +kernel

def swap2x3 : Switch := ⟨4,0xf000f000f000f000f000f000f000f0,0xf000f000f000f000f000f000f000f00⟩
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem swap2x3Valid : swap2x3.Valid := by unfold Switch.Valid; decide +kernel

def swap0x3 : Switch := ⟨7,0xaa00aa00aa00aa00aa00aa00aa00aa,0x55005500550055005500550055005500⟩
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem swap0x3Valid : swap0x3.Valid := by unfold Switch.Valid; decide +kernel

def swap1x4 : Switch := ⟨14,0xcccc0000cccc0000cccc0000cccc,0x33330000333300003333000033330000⟩
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem swap1x4Valid : swap1x4.Valid := by unfold Switch.Valid; decide +kernel

def swap3x4 : Switch := ⟨8,0xff000000ff000000ff000000ff00,0xff000000ff000000ff000000ff0000⟩
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem swap3x4Valid : swap3x4.Valid := by unfold Switch.Valid; decide +kernel

def swap0x4 : Switch := ⟨15,0xaaaa0000aaaa0000aaaa0000aaaa,0x55550000555500005555000055550000⟩
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem swap0x4Valid : swap0x4.Valid := by unfold Switch.Valid; decide +kernel

def swap1x3 : Switch := ⟨6,0xcc00cc00cc00cc00cc00cc00cc00cc,0x33003300330033003300330033003300⟩
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem swap1x3Valid : swap1x3.Valid := by unfold Switch.Valid; decide +kernel

def swap0x2 : Switch := ⟨3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050⟩
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem swap0x2Valid : swap0x2.Valid := by unfold Switch.Valid; decide +kernel

def swap2x4 : Switch := ⟨12,0xf0f00000f0f00000f0f00000f0f0,0xf0f00000f0f00000f0f00000f0f0000⟩
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem swap2x4Valid : swap2x4.Valid := by unfold Switch.Valid; decide +kernel

def swap1x2 : Switch := ⟨2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030⟩
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem swap1x2Valid : swap1x2.Valid := by unfold Switch.Valid; decide +kernel

def wordSeed3 : W := 0xfeeefcc0feeefcc0feeefcc0feeefcc0
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem Seed3 : signedLower wordSeed3 raw 7 := by
  refine transported wordSeed3 LayerSeed0.target 7 [swap0x1, swap2x3] ?_ (by decide +kernel) (by decide +kernel) LayerSeed0.fullBound
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl <;> first | exact swap0x1Valid | exact swap2x3Valid

def wordSeed4 : W := 0xfffffeeafffffeeafffffeeafffffeea
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem Seed4 : signedLower wordSeed4 raw 6 := by
  refine transported wordSeed4 ExampleSix.target 6 [swap0x3, swap1x4, swap3x4] ?_ (by decide +kernel) (by decide +kernel) ExampleSix.bound
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl <;> first | exact swap0x3Valid | exact swap1x4Valid | exact swap3x4Valid

def wordSeed5 : W := 0xfefeeca0fefeeca0fefeeca0fefeeca0
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem Seed5 : signedLower wordSeed5 raw 7 := by
  refine transported wordSeed5 LayerSeed0.target 7 [swap0x4, swap1x3, swap3x4] ?_ (by decide +kernel) (by decide +kernel) LayerSeed0.fullBound
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl <;> first | exact swap0x4Valid | exact swap1x3Valid | exact swap3x4Valid

def wordSeed6 : W := 0xfffeffecfffeffecfffeffecfffeffec
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem Seed6 : signedLower wordSeed6 raw 6 := by
  refine transported wordSeed6 ExampleSix.target 6 [swap0x2, swap2x4, swap3x4] ?_ (by decide +kernel) (by decide +kernel) ExampleSix.bound
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl <;> first | exact swap0x2Valid | exact swap2x4Valid | exact swap3x4Valid

def wordSeed7 : W := 0xffececa0ffececa0ffececa0ffececa0
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem Seed7 : signedLower wordSeed7 raw 6 := by
  refine transported wordSeed7 LeafSeed2.target 6 [swap0x3] ?_ (by decide +kernel) (by decide +kernel) LeafSeed2.bound
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl <;> first | exact swap0x3Valid

def wordSeed11 : W := 0xfffffef8fffffef8fffffef8fffffef8
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem Seed11 : signedLower wordSeed11 raw 6 := by
  refine transported wordSeed11 ExampleSix.target 6 [swap0x3, swap1x2] ?_ (by decide +kernel) (by decide +kernel) ExampleSix.bound
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl <;> first | exact swap0x3Valid | exact swap1x2Valid

def wordSeed12 : W := 0xfefeeac0fefeeac0fefeeac0fefeeac0
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem Seed12 : signedLower wordSeed12 raw 7 := by
  refine transported wordSeed12 LayerSeed0.target 7 [swap0x4, swap1x3] ?_ (by decide +kernel) (by decide +kernel) LayerSeed0.fullBound
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl <;> first | exact swap0x4Valid | exact swap1x3Valid

def wordSeed13 : W := 0xfefefaa0fefefaa0fefefaa0fefefaa0
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem Seed13 : signedLower wordSeed13 raw 7 := by
  refine transported wordSeed13 LeafSeed10.target 7 [swap0x2, swap1x2] ?_ (by decide +kernel) (by decide +kernel) LeafSeed10.bound
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl <;> first | exact swap0x2Valid | exact swap1x2Valid

def wordSeed15 : W := 0xfffefefafffefefafffefefafffefefa
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem Seed15 : signedLower wordSeed15 raw 6 := by
  refine transported wordSeed15 ExampleSix.target 6 [swap0x3, swap1x2, swap2x4, swap3x4] ?_ (by decide +kernel) (by decide +kernel) ExampleSix.bound
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> first | exact swap0x3Valid | exact swap1x2Valid | exact swap2x4Valid | exact swap3x4Valid

def wordSeed16 : W := 0xfefaeca0fefaeca0fefaeca0fefaeca0
set_option maxRecDepth 2500 in
set_option maxHeartbeats 0 in
theorem Seed16 : signedLower wordSeed16 raw 6 := by
  refine transported wordSeed16 LeafSeed2.target 6 [swap0x4, swap1x2, swap2x3] ?_ (by decide +kernel) (by decide +kernel) LeafSeed2.bound
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl <;> first | exact swap0x4Valid | exact swap1x2Valid | exact swap2x3Valid

end GraphSignedFrontier.LeafAliases

namespace GraphSignedFrontier

namespace LeafHint0

def target : W := 0xfffefefeffececa0fffefefeffececa0
def raw : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000]
def negative : List ℕ := [0, 1, 2, 3, 4, 6, 8, 9, 12, 16, 17, 20, 32, 40, 48]

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem positive : target ≠ 0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem unique : raw.Nodup := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem neg : ∀ r ∈ negative, r < 128 ∧ target.getLsbD r = false := by
  intro r hr
  have yes : (negative.all fun j => decide (j < 128 ∧ target.getLsbD j = false)) = true := by decide +kernel
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp yes r hr

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨4,5,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : W) ∨ z.getLsbD 4 = z.getLsbD 5)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨8,10,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xcccccccccccccccccccccccccccccccc : W) ∨ z.getLsbD 8 = z.getLsbD 10)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : W) ∨ z.getLsbD 1 = z.getLsbD 5)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨2,10,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xff00ff00ff00ff00ff00ff00ff00ff00 : W) ∨ z.getLsbD 2 = z.getLsbD 10)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨2,18,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffff0000ffff0000ffff0000ffff0000 : W) ∨ z.getLsbD 2 = z.getLsbD 18)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,33,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffffffff00000000ffffffff00000000 : W) ∨ z.getLsbD 1 = z.getLsbD 33)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd

def dictionary : ℕ → ℕ
  | 0 => 0x5f5f4c4c5f5f00005f5f005f5f5f0000f0f0f0f0a0a0a0a033ff000033ff0000eeeeee00eeeeee00ff000000ff000000ffccffccff00ff0000000000fafafafaeeeeeeeeeeeeeeee00000000aaaaaaaaeeeeeeeecccccccc00000000fcfcfcfc00ffffff00000000ff00ff00ff00ff00cccccccccccccccc5f5f5f5f000000000000ffcc0000ffccffffffffccccccccffff0000ffff0000ff00ffffff00ff00eeeeeeeeaaaaaaaaaeaeaeaeaeaeaeaeffffff00ffffff000f0f0f0f0a0a0a0acccccc00ffffff00aaaaaa00ffffff00ffffffff00000000ffccccccffccccccf0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaa33333300ffffff000000000000000000
  | 1 => 0xffccffcc333333330000000000ff00ff000000000000ffff0000cccc00000000cccccccc00000000f0f0f0f000000000eeeeeeeeffffccccffffccccffccffccffccffccffffffffff00ff00fffffffff0f0f0f0ffffffffaaaaaaaaffeeffeeff00ff000000ffff00000000fffff0f0fffff0f0ffffaaaaffffaaaafff0fff0fff0fff0ffaaffaaffaaffaafcfcfcfcfcfcfcfcffccffccccccccccffaaaaaaffaaaaaafcfcfcfcf0f0f0f0fafafafac8c8c8c8ccccffffcccccccc5f5f00005f5f0000ff000000ffff0000fafafafafafafafaa0a0a0a0a0a0a0a0fafafafaaaaaaaaaececececececececaaaaffee0000ffcca0a0ffeca0a0ffec
  | 2 => 0xccccccccffffffccccccccccffeeffeeccccccccfefefefecc88cc88ffaaffaac8c8c8c8fafafafabbbbbbbbbb00bb00bbbbbbbbb0b0b0b0bbbbbb00bbbbbb00bbb0bbb0bbb0bbb00000ff000000ff0000000000ff00ff00aaa0aaa0fff0fff0aa88aa88ffccffcca8a8a8a8fcfcfcfc33223322ffaaffaa32323232fafafafa0f0fcfcf0000cccc0c0cffff0c0c0c0c00ccffff00cc00cc00000000332233220000000032323232888888888888888822222222222222220f0f0f0f000000000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0000ff000000ffcc333333ff00000000cccccccc00000000aaaaaaaa0000000033333333330033000000ffff0000ff00
  | 3 => 0xcccc0000cccc5555555500000000ffffffffeeeeeeee55555555444444440000ffff0000ffccff00ff00cccccccceeeeeeee00000000ffffffff0c0c0c0cfffafffaff00ff00ffccffccaa88aa88ffaaffaacc88cc88ffaaf0a0ffaaf0a0ffaacc88ffaacc88ff00ff0000000000fefefefefefefefefefefefeccccccccfefefefeaaaaaaaa0e0e0e0e0e0e0e0efafafa00fafafa00fac8fac8fac8fac8f0f0f0f0fcfcfcfcf000f000f000f00033333300333333000f0f0f0f0c0c0c0c5050505050505050eeeeeeeeee00ee00eeeeeeeee0e0e0e00f000f000f000f000000f0f00000f0f0eee0eee0eee0eee0cfcfcfcfcccccccc4444444444444444
  | 4 => 0xcc00cc000000000088888888ffffffccffffffccfffafffafffafffaffeeffeeffeeffee00cc00cc00cc00cccccccccccc00cc00cccccccc88888888cccccc00cccccc00cc88cc88cc88cc88c8c8c8c8c8c8c8c8bbbbbbbbaaaaaaaabbbbbbbb00000000afafafafaaaaaaaaaaaaffffaaaaaaaaaaaaeeeeaaaaeeeeaaaaaaaaeeeeeeee88888888cccccccc0000ffff0000aaaa0000ffaa0000ffaa0000fafa0000fafa0000eeee0000eeee0000cccc0000000000000c0c00000c0c000000ff00000000000000cc000000cc00000000ffffff0000000000ffaaffaa000000000c0c0c0c000000000000ccccffcc0000ffcc000033330000ffff0000
  | 5 => 0x5000500050005000404040404040404f0f0f0f000000000ee00ee00ee00ee00e0e0e0e0e0e0e0e0111111110000000011001100110011001010101010101010888888880000000022222222aaaaaaaacccc0000cccc0000aaaa0000aaaa0000cc00cc00cc00cc00c0c0c0c0c0c0c0c0aaaaaaaa22222222aa00aa00ff00ff00aa00aa00aaaaaaaaaa00aa00aa00aa00a2a2a2a2a2a2a2a2a0a0a0a0aaaaaaaa88888888aaaaaaaa3030303030303030330033003300330000aa00aa00aa00aa0000ff00000000000000aaaa00000000000033330000000000000f0f000000000000cc000000cc0000008888000088880000aaaa0000aaaa00000000ffff0000
  | 6 => 0xaaaaaaaa888888880000000022222222ffff000000000000ffccffcc00000000aa88aa88aa88aa8833330000333300000f0f00000f0f00000f0c0f0c0f0c0f0c003300330000000000330000003300000022002200220022f0f00000f0f00000f0a0f0a0f0a0f0a000500050005000500044004400440044fafafafa00000000fa00fa00fa00fa0032323232323232320505050500000000
  | _ => 0

def packed : ℕ → ℕ → ℕ
  | 4, 0 => 0xe0d0c030a050904030b050904030a0509040208050403070205040302060504030201
  | 5, 0 => 0x5120311022005120311021f05120311021e05121d11020f051211021c0805121102080f051a031b1102051a03110702051a03110206051a031102010d19031102180d0c031102180d12031714160d12031502140d1203110a1312031102100f
  | 5, 1 => 0x50d0412030b050d0412030a050d04120208050d2b122a11050d0c251124050d0c032202050d0c03110a050d12291124050d1203280a05190311022705122603110a05122511240f05122303110f05120315020f05120322020f051203112102
  | 5, 2 => 0x360e0d2e031735340d122d170e0d330317020e0d0c0317020e0d12030a320531302f2e11050d2f2e2d17050d19251124050d19032202050d2c12030a
  | 6, 0 => 0x5120311020f3b05120311020f160512031102453b090d12031102440d1203114302180d1203110242140d1203110241320d120311023e400d120311023e3f0d120311023e390d120311023d3c0d1203110232180d12031102183b0d120311023a39000e0d0c03110200050938370302
  | 6, 1 => 0x50d120311024f050d120311024e050d120311024d050d120311024c050d120311024b0512250311020f0512031711020f0512031143020f0512031102420f0512031102240f05120311024a0f05120311023e0f0512031102490f0512031102480f0512031102470f0512031102460f
  | 6, 2 => 0x50d1203110702050d1203115c02050d1203115b02050d1203115a02050d1203115902050d1203115802050d1203115702050d1203110a32050d1203110a56050d1203110a55050d1203110206050d1203110254050d1203110253050d1203110252050d1203110251050d1203110250
  | 6, 3 => 0x50d1203170269050d1203170268050d1203170214050d120317673b050d1203661102050d1203651102050d12030b1164050d12030b1156050d12030b1163050d12031b1102050d1203621102050d1203610260050d1203280247050d12035f1102050d12035e1102050d12035d1102
  | 6, 4 => 0x50d0c25031102050d0c03171102050d127203110a050d121a030b11050d121a03110a050d127103023b050d1270250302050d126f2d0311050d122d17026e050d1229031102050d126d031102050d126c031102050d126b031702050d12036a0b11050d1203176102050d1203172802
  | 6, 5 => 0x50938370311020538371203020f05300d2f2e0311050d7725031102050d2f2e031711050d3303171102050d3712110208050d1925031102050d7612031102050d2e122d0317050d2e122a1102050d2e12031747050d2e1203173b050d7512031102050d7412031102050d7312031102
  | 6, 6 => 0xe05120311027b0e05120311020f0e0d0c120311020e0d127a0311020e0d12031779020e0d12031702320e0d12031702390e0d12031102400e0d120311023f0e0d12031102390e0d120302473234050d122d031734050d1203174734050d1203173b340d120317114878050d12031702
  | 6, 7 => 0x360e0d1203170236050d2e03171135340d120317117d050d122d03027d050d120302470e34050d1203170e050d2e1203170e050d127103020e050d1203177c0e050d12031767
  | 7, 0 => 0x50d120311023b00050d120311028300050d12031102820005378112031102000537120311020f000512260311023d0005120311430280000512031102567f000d12031143023e000d120311027e48000d120311023e32000d120311023e3b000d120311023d320000050d12030b110000050d1203110a000005120311020f
  | 7, 1 => 0x50d120311024000050d120311023c00050d120311028d00050d120311020f00050d120311028c00050d120311028b00050d120311028a00050d120311028900050d120311028800050d120311028700050d120311028600050d120311028500050d120311023f00050d120311028400050d120311021800050d1203110239
  | 7, 2 => 0x50d120328110200050d120311990200050d120311980200050d120311430200050d120311970200050d120311960200050d120311950200050d120311940200050d120311930200050d120311920200050d1203110a0200050d1203110a4700050d120311910200050d120311900200050d1203118f0200050d120311028e
  | 7, 3 => 0x5380d3712030200050d9c1203110200050d2f2e03110200050d9b1203110200050d371203027f00050d370311029a00050d2e1203171100050d127103110200050d122d03170200050d120317116700050d120317116000050d120317024700050d120317023b00050d12030b114300050d12030b110200050d1203611102
  | 7, 4 => 0x50d120311025516050d120311023a16050d120311023b9f050d120311023b16050d120311023b9e050d120311023b83050d120311023b82007d050d12031102000e050d12031702000e050d12031102000e0d1203114302000e0d1203110232000e0d120311023b0034050d1203171100059d0d120311020005090d37031102
  | 7, 5 => 0x50d12031102563b050d120311025616050d120311027f89050d120311027fa3050d120311027fa2050d120311027f88050d120311027f86050d120311027f55050d120311027f3b050d120311027f16050d120311027f82050d12031102a155050d12031102a13a050d12031102a13b050d12031102a055050d12031102553b
  | 7, 6 => 0x50d12031102463b050d120311023d32050d120311029a32050d120311029a7f050d12031102a832050d12031102a863050d12031102a87f050d1203110232a7050d120311023289050d1203110232a6050d1203110232a5050d1203110232a4050d120311023287050d120311023255050d12031102323b050d120311023216
  | 7, 7 => 0x50d120311024816050d12031102647f050d1203110264a1050d1203110264a0050d12031102643b050d120311026416050d120311024732050d12031102477f050d1203110247a1050d120311024755050d12031102473b050d120311024716050d120311024632050d120311024656050d12031102467f050d120311024655
  | 7, 8 => 0x50d120311024a32050d120311024a56050d120311024a63050d120311024a7f050d120311024a55050d120311024a3a050d120311024a3b050d120311023e3b050d12031102a93b050d12031102a916050d120311024955050d12031102493a050d12031102493b050d12031102487f050d120311024855050d12031102483b
  | 7, 9 => 0x50d12031102ac48050d12031102243e050d1203110224a9050d120311022432050d120311022456050d12031102247f050d120311022455050d12031102243b050d120311028e7e050d12031102ab3e050d120311024a3e050d120311024aa9050d120311024aaa050d120311024a48050d120311024a64050d120311024a47
  | 7, 10 => 0x50d120311024232050d120311024256050d120311024263050d12031102427f050d120311024255050d12031102423a050d12031102423b050d12031102b07e050d12031102af3d050d12031102ae32050d12031102ae63050d12031102ae7f050d12031102aea0050d12031102ae3a050d12031102ae3b050d12031102ad47
  | 7, 11 => 0x50d120311b202ae050d120311b2024a050d12031194023e050d120311930260050d120311920248050d1203110a0247050d120311910232050d12031190027f050d1203118f023b050d12031102b13b050d12031102423e050d1203110242a9050d1203110242aa050d120311024248050d120311024264050d120311024247
  | 7, 12 => 0x50d1203114302b7050d1203114302b6050d120311430232050d120311430256050d12031143027f050d120311430289050d1203114302a1050d120311430255050d12031143023b050d120311430216050d120311b5b302050d120311b30242050d120311b302b4050d120311b30224050d120311b3024a050d120311b20242
  | 7, 13 => 0x50d120317110232050d120317110256050d120317110263050d12031711028a050d12031711027f050d120317110255050d12031711023a050d120317110239050d12031711023b050d12030b114302050d120361110248050d120328110232050d120311430242050d1203114302ae050d120311430224050d12031143024a
  | 7, 14 => 0x50d120317791102050d120317bc1102050d120317bb1102050d120317114302050d12031711b302050d12031711b202050d12031711023e050d1203171102a9050d1203171102aa050d1203171102ba050d1203171102b9050d1203171102b8050d120317110248050d120317110264050d12031711026e050d120317110247
  | 7, 15 => 0x50d12250311023e050d1225031102a9050d1225031102c1050d1225031102c0050d1225031102bf050d1225031102be050d122503110232050d122503110256050d12250311028b050d12250311027f050d122503110255050d122503110218050d12250311023b050d1203bd171102050d12036a171102050d12036a1102b4
  | 7, 16 => 0x50d2e120311023b050d127225031102050d127203171102050d12720311024a050d121a25031102050d121a03171102050d121a03110224050d121a0311024a050d127125031102050d127103171102050d122d03171102050d1225c3031102050d1225c2031102050d122503114302050d12250311b302050d122503119502
  | 7, 17 => 0x50d2e122d031102050d2e1203c71102050d2e1203c61102050d2e1203114302050d2e120311b502050d2e1203119602050d2e120311b202050d2e12031102c5050d2e12031102c4050d2e1203110232050d2e120311028c050d2e1203110263050d2e120311027f050d2e12031102a0050d2e1203110284050d2e120311023a
  | 7, 18 => 0x50d371203110248050d3712031102cc050d3712031102cb050d371203110247050d371203110246050d3712031102ca050d3712031102c9050d3712031102c8050d371203110232050d37120311020f050d37120311027f050d3712031102a1050d3712031102a0050d37120311023f050d37120311023b050d371203110216
  | 7, 19 => 0x50d9b2e12031102050d9b1203171102050d37cf12031102050d378112031102050d371225031102050d371203171102050d371203114302050d37120311b502050d371203110242050d3712031102b4050d3712031102ce050d371203110224050d37120311024a050d37120311023e050d3712031102cd050d371203110249
  | 7, 20 => 0xe050d120311023b0e050d12031102160e050d12031102d134050d371203110234050d122d031102059d090d12031102059d0d371203110205090d122503110205090d120317110205380d371203110205300d2f1203110205300d3712031102050dd03712031102050d9c2e12031102050d9c1225031102050d9b3712031102
  | 7, 21 => 0xe050d37120311020e050d2e120311020e050d12250311020e050d12031711020e050d12031143020e050d12031102d20e050d12031102420e050d12031102ae0e050d12031102240e050d120311024a0e050d120311023c0e050d12031102320e050d12031102560e050d120311027f0e050d12031102a10e050d1203110255
  | 7, 22 => 0x36050d12031711027d0e050d120311027d34050d120311027d050d1203171102
  | 8, 0 => 0x50d37120311020000050d2e120311020000050d12250311020000050d12031711020000050d12031143020000050d12031102420000050d12031102ae0000050d12031102240000050d120311024a0000050d12031102320000050d12031102560000050d120311027f0000050d12031102a10000050d12031102550000050d120311023b0000050d1203110216
  | 8, 1 => 0xe050d12031102
  | 9, 0 => 0x50d12031102
  | _, _ => 0

def count : ℕ → ℕ
  | 4 => 7
  | 5 => 42
  | 6 => 122
  | 7 => 356
  | 8 => 17
  | 9 => 1
  | _ => 0

def table : Compact.PoolData := ⟨64,0x10000000000000001,8,dictionary,packed,count⟩
def startMask : ℕ := 0xfffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0fffefefeffececa0
def poolHintsPage : ℕ → ℕ → ℕ
  | 4, 0 => 0xff294b4025fd578f8103f782f7013f5a15da007e1dd1f00c3b08234810b27aa030195966438033a8186640a7485168000a84b12f0114b1dc7406481dd4640aede1c7c8181bacbb7009addc7c801759cff300a4961ff6010ce75c8c0281a5e8e601028598340604bb230011c96086a01b848537a067
  | 5, 0 => 0x26670ac48e4bb56e854083700f1000fe7f1a1421f929bc4cc3a9ef006d0748c400680e7c3d41441ca295c24638891d0248672cb40928bbb3c62301626f1c1862bd243034857728e0398ae0c681741542310080295f2087dc4df6da11b89a7c480c512f06fc3401f0d0f824c2704b2058840661e16006e9c3c16e0dbc6e865c12ef2d101824ceb211004388344ea0786ec898003e6a311000481a6250
  | 5, 1 => 0x4b5269c0c495d7f2078d2a7f4d07824f5f9615248ace1024090ac0302092025501032310d7e1c741750984a47d39b58804f5ac970801e7b2440b33cb53382aa793579041cf2211513b9c4866a0973890c8038467c8418608cf8b3410219e01b0106335bec4020633c2e0488c63b9d09098bce76022314d8304445d8d5c8490b2e7910821645c1a1322c337cc0e053683504d0a4e04702113dec28256
  | 5, 2 => 0x711b2e8142e2286d0501bed6be06a373f6ae2556e43c5c14edae99b8499b388190c8365d8680c16bcfcd0160d53fcc031da68d810d1347c3220b6670e2b4026cb9456081d918db40292f749461705e6edc8184b8447e03dd6e5dcf0622d8b70e0e25aaa4cc4a2b51279005d67d8f30a3acd5f881f25656d4024ea8288482c94cbd6403ba8f425e27250656200889e8438089d392d2111a268403c156
  | 5, 3 => 0x917e11c3c122ddbb83ca4342c20d2486354e2739079b302291eb699861e3900ff081c6cb51c0308c56b2026d1784130a422b3d7d0b944bb6b610588906dc2eb1072508282204447023c30b3c817685bf50834f0ac37f02920f641b06040ebce825781bddfc18cfed5a006c1fd4d15011bf041481647d68fc8064f5c8d4098de8b8f80723ca9d3222476925704c2ea717084ddc9f2470b3b8e10d2027
  | 5, 4 => 0xb8ccd782c57156c4079ee151920ebdb209641c3b4bd84c0416887d4894ecf671b003d9e40da274b2a88503a7620d7082d6c2fae414a572707c0e7ac699040a950877605c69fd1910f9d3f17ea033a6b1adc40b4ca60201ca933aee1095108dd22659bcab5400536f030870263cd320024b6884e05094c00c42a328fe910842503d5a0ca49baaf027193511bc22524c2f9099e48827313148f6754202
  | 5, 5 => 0xf2f9fd0465e4736186dfc7e6f1138782a3e0276ef4968c06fdc7759040bb5ef7208bf66a6f6214eb172341afd3def483d39ff02e098f28cbe8057e2c7bbc42fc57236819f88f7e70486fd8738191dbb2620523b03a30878b3dc42d0bbe654b681f0caf7c0800193cca585532719fb0e964125900b4c7e6a2852f825aa30382f418e9143de5d69c153bbed5c82af770fb28406ecaf350e85ca6f68264
  | 5, 6 => 0x7f8d02a130fd9e4002e7f75fea0953ec8221099fc248fc135f78fd8c505ec444f86cbd55c77043fa1fa54012
  | 6, 0 => 0xc25f0498e16c9b5888c2cbaa9353857defa4620adcc0452613d65e8140260f5f12104bf9001760952930a2212a18d941c2261e02938432a0c58207b4d108ce0f0c419a9419176a1b902ffd88014055a804c8e0a463e0e1812646910881a59da25003364940e0066a3d8b0c095a8433b810625a5a501973e49c002bb370cd4054725093806f1fc04700d5a6c9840176600400006c29158000ae0e232
  | 6, 1 => 0x1dee0bc82e3accc7939873575b2098e28aae3321c50a1c0ee33b2821c1c6750f90888c693f4600186fc3024c2f911090485b95bd18b8b6f78842116339e8e6e2c297f1d00571f0f26989e0fb6556136841c146258cca1c5c4a6bf2138891586c31311d8490eee21a9b0909c3ea22f1b387ccd107910f6d86480c1e239309c83c3f290cb074081a3960e0c194ec01b98d9029c33b3a53b10648466506
  | 6, 2 => 0x29ff5e0e62536cf314dca65e6a31014b8b8626128790a87265049b19658a046e108913d3e842e726e13d0ac44daba99e409b488c160934277226325f2824ea64b229a0a1894e93e08a125a4b03e724a287824646ea869ac88a94ef21911333941c0223517c7a443ee2b9340879e101c890e58f61252197b8c80a42635915c48461731f990797182e41ee57b4b6a3d84a71a907ab2151290f1c1141e0
  | 6, 3 => 0x3ae8bc8d8e75ae7d154ce970352d39cece042e639c84cc4ee72e29e8414e34fae2021c2a47c3f237dbf3cce46ef2701510dc48032909ae925424434e571c66e67a584911ccf2a8c0691906f480d0314ff4066061e4700440c211c3399981df183112fee870ea05fd7458d4cbf4ea02e3978841e1222e1ff08cce5ab8380f1cb44460328961c8d81242b68c78f2e5644fb0c50abf1062c815238bc257
  | 6, 4 => 0x4764f68ace8d69e589151a5c0f02a233460455445dcd4cee48b2e9b0e490f682206a21e2d624d143be188a02874ade88510cf90e171a1592fc6d742a4fa4f288352818ed10585fd1f120a37c85b241421588e680782d87c4ff41e61a39fa8baa5473f48d185047e35b70d54fc509d0fa1f7404e2d73dd86406ee7b047214c4f5cc9d22b9e8ae0e0a03cf8f3080279080e9bd0f122e00819dba54a371
  | 6, 5 => 0x531f2c4266a409af1a11478db136928ecf543a351001f09aaa13d82099d426408282a835b265845047c3826aa02f3497013f04d916927de09e5a24f1e1a09869c4eef8389380cbe011a6e32be3814d4b354d4699063f0ec53115bd30825d268a1524b5ecec0e496a01e03912c9ab521ba589b543564a7e718a669385fb95dd2693dc281a4cfeb424649246609ac919ad105512067c5033a3c87cc374
  | 6, 6 => 0x61fdd2ce86c2c36f0611844922120b050a0c2756031228c64be742983857aa3e91812f44ac87005e0f7a4de0bad1a49d8d75750c0b92e9c7d60a25c5c3c8e60b831919b896fd202331adeb5241c75b013cc888b50bb485d169392b2ea2ce91d616759af6f090eb2d87a108d6505803722c640c4407587e14c502b0a6b4805d5f7a521302bd17902275697784a86ab4db89ac15594111aba9e1a0c2c5
  | 6, 7 => 0x6dcddcc7a6dae6cf854db3fa8e20836621d81446c529dc50ad8910f16d9afc7de18ab5c02447346b0ed0c584d5e5f9135daa6ffc0aab54dfdc2a26a933509eed2d9d11b41a4ac601a8b427e2a5b7682e12cd2ed015f28b019e604114b33acc0c1e766fd634744cb0f6502119600b2111327591234064c9d48e4ec957d40995921da0351321c9021826427e5c0aec80d3597c98c54f432031730ee217
  | 6, 8 => 0x7a90ba8860f46a5b8b95e54cb42c03c9297000278b83209c6f0d5860485e166423403c2657c4a777c7c9cee0ee18d59acddbff6e2b0bb4d4ce4977674aa4b22ecd6db8ccdd9603a0703b0964c0f274661f09c2e73a83165dcced8307a399db0023372e5a7474ee4eeb191c9c85ed134939061a03c070f03482c0e02afa8a51bf7c5e29837cdd1e1426f775b80c6dec2730e11bb2e5a213370db98395
  | 6, 9 => 0x870a5d86250af49294d215da39170c27bd56630848993036508b01208d61089fd108420cfea43382a8320e6b04c9c3924a08af41089c0f8d0427081e0aa44e70318a004ca0563b039b409f2905e7806c988e26ffd268164dff45632f13fd5b282877f5467822afe8d9c12c9fc2f931333f5a73a1347e251cc520fb089f8545f44d521c83e7cf805e47bf7d38c46f7be0c0a45edaffd241bd55432331
  | 6, 10 => 0x9298b40ea524ba471b12494e4504048ccfe02929149260b432216f406de429f84072c850512382903ddcc469206a89139e3fd19327147d155a2378f88bcc2411d3f64039e3a69c72d1c720bd21318e3627c4a71c1b90958e34c7ae32a467d7fe5558c6534476115345a090e29f2a117044f497e5d089c9b6ca41132ba31e0223d1c72584456d006028853fe43a51021b498ce1f80301b1c3984ee6c0
  | 6, 11 => 0xa2ec16c8e145652c08da8a06861a1d132f6c1939fe58249cb3f1d0986567d47b133a4f3f85a5519dfef3c9013b97e591de75ca172e24e511965359c98444b6937be3c8c5a6e88f10ebcd94c442a798e2494a833186a2001e61712f2f04b9442470397072dcb252d4b16100e5731ec1c3caa2b666a094dc49416529b78e14da5289260a84a4f0963629438330e8526fe93838e4d037930bc9800f6722
  | 6, 12 => 0xad2d0b884559f43f128ab2cfce0f8564683e542ac36b7858f585349835eae7d7008155c20341c1ab3bfa83ef56718c8e5eac82801f05588614350aaf1530dcf554bae0f5ea9db0b2a355057c2020a95cba0ac1527e348ddaa47bc313b5463f9a104a8bb398a8b513952955e9d0e0e19a536213c040a6b5f280654ce328920a96f6af07352c254c702a55f74026147da3b16568c347b029517c7184d2
  | 6, 13 => 0xb84d4c0ba36f453a1402dc86d42725b655bc194b6b0ffc64f6bb3910112d58f04118da44534240b3b60d84c566d25a1bcacc46aa0c3d97cffc3b7b2d4c740e965445a858aca29102b3593b180712b217b24507639ada9592c66f8d2d25891a40310b1228547876229249a9ac2de490b9d8427c2307b021c2096f5f95890592bee8791b9d76ebc65c2ae92810f095c6467988ab786f720156f014c175
  | 6, 14 => 0xc4eb53c28f883f9a13030eafb8103e1ca1805b3c373a64ecf841e999b83074147309e0bd6b05d7c0af85c5e580228c9bdefe5f082105fc9e8e607bf872a4c877efd548f0afb25e13315f3a1700f7be2c02c48f7bda938fc2f6a6b31c2de8e7de380bb7c904aa576c04a1d5eec2c5d2ca5d7d5202c6bacbff8c07754ada8882e79c910b8dce86ce202b9a2204325732655940ae556e11b05c5e558157
  | 6, 15 => 0xd59227c1e1a88ff90b1350a4a13a3ea0794e117d2f7000ca1a55eb30acf493f040d3e92629a062d238084b61a28ce591034414780b8686df4e550cfdaa4c2ad9eb4db95c33c9ada063e71fa305b1cd39e649e5991089824b31bb7117be6343b0137cb3f27ca819646970b8b28f2d80e86517d22180c8cad7c74190bb9b041f20a82f3b9e3cdd02587c65c994cc18c0bcc141317816b15062dd354787
  | 6, 16 => 0xe5fa314389cb08f30043959db2361724dcb0690e3866fc26dc5d71f02df89a2c9013f056db8687e094184e65c0ad3401838148e11a17018c4c565dfa2474a2fbef78e841b7ba4561c1ef69306012de92d7c3c9bcf8360f8f79bcc71596f22512295de313e49a9b8455606477025360a06dd89d4394da8557cc85b378de8fdf6618a83c0ec92448442d8e3a1cd05aec26e07875acac21a96b3d5b2710
  | 6, 17 => 0xf62ff94045ec39ed88c3d826270617ad51562b7f4673689e9e820720693ce798320079bcd3c090f340a4c321e4c24c85dfc8fa2f212f90ad764b3f1dd0944c9df9b089683bd7e13350f74343c094ee4e13006fdc5088169bb7498313a76333e6082ec5bfd8befd715bf0cdbacb48e08b755f63e097e9e8000547d33a6c8407a5b6eb0d0749e244670e86e33452fcfb1ae95d39eb00d313f3a601c657
  | 6, 18 => 0x7f3c572612fe63fcc501fa8dfe18dff5042c1aa7dcf6e8042fb4ded4645f67a8f1093eb3d8b36a7d53dbe087fa8e190a65f4ca0f0753e892f72927ce151a6b7f983bd0509f243538dd7e01a27349fbf8e84197f7c45449e1eea5c80dc3db9e870d17b4d0463d0
  | 7, 0 => 0x4d2e3dd4409a3b155081337ea1f382550a6a110487b7952609002f4b480e6a00a3981b8e40af7036f1394a406a18643880bee403e20170fd872402d247d56c0554f045440a4a4f13181473ae013026e161d6404ac7f9ed8093c667018126143367023cc8cc8c044d0c47dc07a91e50a00ec92453101af995ce602b524b944050e7386a0081e7517600a425d4a600d70f19140131d3a49001701e8d5
  | 7, 1 => 0x9028f44641204e4b7dc233596292044bca84970896d808e410c5e43698204dac8b303fd18aae507ed8723060f8269291c1e87d37d383ce95d3f20793ef644e0eba974f801bec7f749037651c70406ab4525ee0cf92eac1c19c94a4c103347826610649644ae80c2ca5abc81734538d802db2342a305b5a767640adff64a1c158bfa83382acf46df5052873a7a00a3b6a3f08147324b0982882d21d7
  | 7, 2 => 0xe821a17ae1c35dd4d9837bdd34ca06ea1334b30dc6868b081b837c095c3685475e006c1d1eb850d72459ae41adad458c435664f4d38691d601b30cf23019a419a7dd3e003264f92ea061c7724230c2b22c2ea181a83381c30136755a8600a8c5e30bcef48548178547aecc2d52981998592cb01d60b213a942615ca304554291fc6333051cb5ce5409e4cc536812cb7c0a0c25857631a0497a332e7
  | 7, 3 => 0x13a80404a425938f1f844b05b72b0894f2e6a331273cd4b8024c4d61e1447b09380b88ee244e1311ca7297ee2385d5a05846e85f3d208a736e02211188b04202224b951084443d3a1288870eca6410e4bf5bc821918927004282f95818838474b9310590ee2a420950f95104108a50e108009f0b330fec6925241e6ee2a4503c48da89b07854476020ee339a30c1d5af0c6583a4d5d39a07480c4f20
  | 7, 4 => 0x18b064a0e431361d80106152ce3a80c0af7e53717c79013402f623e1fc05db6b31a18b9d20aa611738b987862e4d204b945a9b626f00b512e95a7169ac114622c613d180058b1de4798aeb93742015bb6407282b2c51271054c4a42a08a77b3eda414c541968e294890d88051b0957f20a2f820ba0144bb5634e285eadcd8c50830b82b8a06f6cf5213d6bfe16e278f53ac004ecd379a009d5c6caf5
  | 7, 5 => 0x1dce9cdee03b5353c28074bda82b00e6c87a0d01cd3059222392ed0290872586e6fa0e4a10aca21c5fdf94e438149640c86f44456780ddf876eb11b7277800436ccd3864c6c5b9e5300d816434d71ae7f55bc635ad65d1c86a6e718238d2c6931d41a55ebdd0e3463de05c46826d61338d0449619419f433c3a233ccb38388648e069700c90cf6f10191b27e40031e418805c63be477238c7379c272
  | 7, 6 => 0x24505e69284842c79c808ed7922b291d5f2aeb5237589444246c3fe16848a587211a914a5601f02290d8c664450f3a28d4898f21968910ad98a4021f636e82043814d46948600e89e110a485aef220efe3162841a5720b5c811d135d110089b51621fab68ea2c3ed545c4907d5b1f5120f9bf4f2431f3430c8043e5b744b047c99638b98f65eca6121eb9f645ee3ca0ef88d878ab16a888efd3aced7
  | 7, 7 => 0x2b959b07ee56998a5550ac90d44d91577dc4b962ae4e00f2255bd8bb648a9c66e3681533cf25e12a455fcec053b34b4514a6e6439da14d445615729a4ab550252c0ba0380a4f23eb1b949ccd0ae32925f9c72e520e3590809f2f0164b13aad2313526ffbf47a44d0b351940992c74648931cf2e53426036e85444bc0b749889673590c8929df083b725209166a649ff88a6dc93f3eca2b9254ce7630
  | 7, 8 => 0x30771b8aa05f8c3b1ad8bef6590ca97de8511462f926625a65f0ac9244cbe0e3b94317b0a667822f3f1763465d86fcafd4ba84e8568173f42d1f52e56cb68425c7ad73c54b8a27832096f7d7a6e22de60e09ce5b2060150cb58a0950396a0a12dc62d0be344ee59e02e8080b3954f5731671a6c3952cd6ebe80659a915048cb32e711b396584420c22ca59957025939102d80afd87646b95f90e0821
  | 7, 9 => 0x3520899baa6a1f9196c4d396552539a3d6cc8f0345bdda10467d04a3090cefcdb59399bc078a8233708d25e6665c879498cc837c893196dbc360732d89acb2e6598ae2880ca72216da993aff0de6324bd625e0645a6f4740c890a06f118fec50c4731b6b62288635b411484c5ea4665018b83386c731585ce7e8628c49a894c442a70591887063603310ba8d1826196ab49c0c2f719ae91851f24260
  | 7, 10 => 0x39c569a0a4738861568ce70ede4a11ce09403c139a5698f6872f19ec29ce53f8471b9c6f0ef02238c50f25c6714fd5a9dce25c3461a9c496840a23886a7248270c07cc948e1444d2db9c126327b337f452630a6f94424940de8a121101bc71a2eb7376562e6606dbf7bcb08db7a104e81b6bfa009736c4e90d2c6d58f9c54cd980ab4689b300c2820364338162c6c06613800d7ed684901ad5f48152
  | 7, 11 => 0x3f3775eb0e7e450a45dcfb0e975d81f593b12d53e891e61c87ce69d1088f942f45221f1d0cab843e27b75e2e7c3e79c558f77a259791ec5938ee73d46970b207a76748e08f3f4869a91e78dca3913cc330a94e791e20b0dcf13adf2999e232f08603c38598c067834f75790efa4787291deb1c49973bd5f6ce2877a7c4b898ede6944601d756371403ae8181d6874e271cd58e730454691ce52394c0
  | 7, 12 => 0x45963bcc0c8afe9dbddd15c98911a229c020762451ef00a8c899faa55dd131ec796a2244fc06644440a15fe48875a647110f2ea92c921cc26471343722e55aa8666f34c510ca24d783a18470128442d8c8134885508c2dc909a8470f3a11385856741c8d3502682c7400d8d04f84a278a077168ac540c18a67e680f7e030d901e309b1a1ff6d012d73fbfa89da07f672f4048fe87a23e19fa94a2282
  | 7, 13 => 0x4ab7c71e64950cfa8f112a024432a253b4c24524a4008ea26946f5e538127d799189a4f39293e249d8bb1b6892a17f33c924d68e933a4649fc77648b1d951c291018a481920952b501241146b3004819c2a6c8902e1cbc891f0cc05e823e052903447862a13e08eb65744c51d5f35693a3a5515110471d554f8a8de1e3c6051ae2122c123122dca3046144f58408bab40d80117484581ba2df3826b7
  | 7, 14 => 0x4f26720c649e3bf056013b8ff31b9275fd363004eb0915e249d329583113a54b5989271b1c83a24e2d4718669c5481be11375cd606a26da72d4404d7ed187649aea3546513557dd31ba678164d174cafada282992a0e959931c7ae118a6256e71334c409a836e986d9f204930c12445026007951144b8980878e9709062b492df0a55a125a0486b804b1efd5be6962d7b4acd2c41338da2567278132
  | 7, 15 => 0x562a742106ac28f8c3d156ca22113aac8a347a3557f0f8b0eaafd153ec155dc312b12aa44e046754586bce64a8a2a8c75950539a3f3a9fb45e74253b914a7aea74da7ae8d4dea91778297a32e8c252f10a5da4a574a1a85d4acc07a51294f08ce625273fae520a4c0c0b24d49601a630291e9540b45234e95ea8a436751a45461dfc9e028b9f2a9025125051dc0a1b981b7413eff141b127ceab50f6
  | 7, 16 => 0x5a74d4e7a8b4e5adccc969bb03408ad375052e65a15168644b3b73a3e516734ee2f3acda4d87a05970a215e6b2de079c0d65a5a23ebac9aed0b11593176942ab2620cc51d64a4a0543ac824be69358f3130244b0e9e9490161cac34912c29580987581c34690eb01be54301600c1c453abba3b52f557702edb80aedf791a855d35750db2b9f27cd20570aebcfc4acecba511d59756d889ab158f0262
  | 7, 17 => 0x5ebd80024abcf158549d77e5cd0392ee71854c45dc2e3cf62bb7514130176d9403592ed6d32e105d8eea57a6bad1e70b1d7503b294a2e815223575cf57d6404b9dae7210173a5405f82e6fb40d505cdf36a7ccb8a37b885d7141062192dec64d2305b924e1286b6b67a27096cc93b3692d913ef4d05af6b6032eb5eaae9fc96b8e9d9622d6dea21875ad3918a8eb546df46816a42644a02d3b69f1e0
  | 7, 18 => 0x6431afd0e4c817c8975d8f8a63a3131e6971517636c8ce060c6d0bad4898d27e39f8b1962b8b02630278e548c541a6284189ff2f880b12d980df2622dee63a2c429bfaa0d88031e26830f78f347061ed31e606c3cfb9d5018789cb97a30beda5434614e06482ec1cea408cd82ea8a203b03c4b8bf2606c816444c0144a298d7e5b84011afc426c8b15f4bf91dc8be576d4d1d7b8a625c3af64eae9e7
  | 7, 19 => 0x68e6a86a40d196ee03dda32c74459344e342b626881ea2ac0d0d5fb12c9a15532532b4086911726794760748cefd5db3cd9ca1e70603377256a84669cb4d4eccd320732dd98076b6c3b2cd4c6ad7657f66e284ca94faa99d9506dd5b8329c293164652f130248c9ee6587d193571e12832693315f064acd79584c955fa28dd924e42900b248f680d2647a4c4604c8efd4b88d914b5b9aab21d04c523
  | 7, 20 => 0x6c4404118ed856914dc9b0a9f42693604f089706bed85992ed790018701aebb48423b5d5fda8646b88b4d964d6e82f1111ad5aae88bb5a6e1c4f26b40a25dc4d65686375dab9b39af935716e49c76a58f7c18ed49603801da90d714c83515914b226a0fe456c6d41068b341a7be7217234e4952bb269c6645820d38bd88c5da5e7669b0b4b2e2d412695bf012c4d28f9d090da4a5534a2348bfc6a12
  | 7, 21 => 0x70d98d2828e1afa0d241c35d2c2d93851d7e4f770a2419a00e12f698401c2546c519383466ef117053104ee6e0956d1805c115e0428b7f5be2d826fd34b1246dfa6390109bece403e0b7d99a68f66fab3649e0ded3533e09bd5bff109b7a74be3906f429cc1e4de730d9e9dbc6a9c95ab780c44a856f015985a0ddcdb7840db975d58c9b6b73eaac16d4bd3a3ecda7fb594c1b3caf69c836695cf417
  | 7, 22 => 0x74e032dde6e98cef96d9d30bf1461ba4355e4a273f3bb22a8e7906ecdc1ce813604a39c7706142738798c8e0e701f94411cd777e35ab9ac5aeed373563d046ee60e4bce49cbfcbe32139723dc64772df8e5ee8e5931e2c4dcb0bfd568b958d72552729dbe266ce4bc5d2c81c8eb7c91a38fdc38577717bb446c0e2c9919dc9c58d4250038837fecb071023b8920e1c037c40dc376b8578386d700482
  | 7, 23 => 0x7872acd006f0c7289f81e155049083c16ccd0147818589aa4effdac2441dfb898538bbf49744d777dc799580ef9a6ed115def0bf1c3bbc2f30ba77750090a4eee0ce01101dbace14003b5e2bc29776b200518ced44773b85d9f371112bb26a10be7764316c78aec5a0a50c1d87b72a9bbb05ef87e475d338e504eb84c729d1d6db001903ac93b6184756ab7cc20ea4f9a2455d3d8ea013ba744652a7
  | 7, 24 => 0x7d273ae2c0f902b2a4c9f1a60d2b83e23c466827c416d6666f86cac275df0d909a123e026288907be5268e2ef7c3bb1d49eee3402003dd01567a27b7160dc42f6a395c981ecaafc8013d91bbaf427b173051a8f5cd62355deb871a5a23d41c76ab27a79df0cc4f4c774c909e7d8ae721bcee4490c1799d4c69cef27e295409e476114893c809603f278d48da4aef1644cd0c9e2a2c7090bc47f027d4
  | 7, 25 => 0x81bda3d8cf033c60218605a3ee00040afb60c8280f966e40901ac6b85ca030f36181c03d4654278064aa2c25002bce46c5ffbf3c40abfdd4061767fa04c5784fea8ae9cd9fcb91ea33bf81ffe8437ef6f280a8fda2d9d785fb319b9903f53ddb1327e76c06668fcd352cc89f8fcd0663bf1487d2477dc72ecf6afb887dcbc5f6f90fa3bbecceb65357d89894940fac4bc15c9f4d3017123e96884350
  | 7, 26 => 0x85f11b660b0bae343d9e1742e982142c2d7c2f4857af5eac50ae69e351e150abfa60c29ef7f107852116d3ef0a295bab8614194e08bc270679212849f8be7a5090de4c91610a264a02421303313083ea3491cf072e6eaa020d7bff3b241ab5a867283196285c10620c6555e0b82a4401416ee5d33182b634448f051a8ccb9209efab4a84133d031f482510a87a9047dc14ada07a4778d140eae9a5b5
  | 7, 27 => 0x8acf33c72515336722ce299f8472bc52ee5a8148a2438e3cf13f21a24c227cf766a9c4d0dbc5f789917bea21131deecd5e25ed933c1c4a3256f90890ef65b8511b7c9204222f0022a144498ecaa08879811f6510cd12ca161ff671a7143fd7226e7879682cf0f0eb6c818821ccc89771c38f1e4f64870a73c6610e14d924de1bd26e941c378e231c186847914450cebe3338e194c8b38b4324c49306
  | 7, 28 => 0x8e39cb16651c2686878237d5c545846f84da3e28df03ce58d1b63f0888e366d3568146babb46408d21db83691a404e931e3436c33b8c67aa875078ceb04ceef19c346878a333e8856a4660f7c8308ca6ab5cad19489f16923273138c8c6431a06d48c5e9ee22d18bbe2c8ca3169125cac6186a13b08c22f39ca717583487122e2c9fa8ac58e7cf0a38b05b38f2915efd6a5162ba34a0fbc56afb0b12
  | 7, 29 => 0x93588d0b4d268c9bc3124ce455281498c9a6df092bc8f1ac724f5e3c4d249511f878c9023f878691b1d35921234f04aa9e45bd894b3c88038605090f9d5e58721e58b02c242e5148db484269ee83905a55a605208a2cbd8240bcc89ba480ef9ec629018dd4de71fc591999e3efe5400947d5020db18f56be48ef1e710c06d63be6bf36bc77afb85a28eeab7ebe91d29e323c63968be2c047272c7143
  | 7, 30 => 0x96a75f82ef2d1b96b0d259355f772cb0dc88a739603be27412bbe5a1fce5723d14a34ad750ae4095a2dd46a52b2fd829165616891e04ab58e6f13956462c7c92a6db98c4a5456a1643ca7f430dd194f19153e729b954c402530d6ba00ca4cdaae309470c7182528b8909a125159a14d84a25a3a396943968c4e727f25bc81e4eadfd64ac9cd7b130193974d10e92716ae1c9e4def025e949bbb20130
  | 7, 31 => 0x9b5939a12f36675e1e966c204f351cd676f25639ac0a8d16f356c6f144a6860016d84ce8520a0399be424bc132fdd9c4de65ba7a613ccb1ce066599583b514732acffa45e64399f3e84c7ee8695298e384874f3196db43ce627c8d153cc2e7e00e3981bed54ab2f2bff1c165dd1fe6e0cbb53201a4975cd3d1ad2ea59047925ce0b26cbcb99b3d592970b0f67292de6db2d025b56535f14b55694084
  | 7, 32 => 0x9fb053cc0f3f5c9a044a7e82c67c94fce9ac1629f9a73832d3ee9ed224a7d4efc6994fa90e07639f3cb34e6b3e21a713da7c380b3dbcf6b3c4b439eb29bd0a13c585f4f8e783d13adbcef04493849db0a85f8f3afa953e1e74923d388ce8cbbc0379d1456ca4139819abc527299dd1184e391e67c09c5ed5c485387211289a70e39c9884e0f3acf169c16ec412137d6442ac66f46e65c1cdc03ba870
  | 7, 33 => 0xa331ea4b4b4649009a8a8c04b89105173b828e4a2d999466f4576461d1e89b99a0d85136c97324a259dfdb8744b2fbcc5e8964b28515126a7b203a23182a22343ef3a130a8537e2120506c54cbc3a0c357284d418227274a8281fc34ad04cd9d182a093c00e61410d09a9c281e0af283d02447f123a04556e66b4002458c427fa1ac4a0cfec5374469fd76f8b4f3fadaed0de7f13730e94fdaca6292
  | 7, 34 => 0xa7498c6ac74e66a388929bc86345a5377a8c833a68bb3680f4c7cfe880a98a4e3620530a0a42a5a5ed0f28874bd0feab1e9632fd09352c2944525a56bd96a254ad42d979294f4e1728529a54c487a50f6c68014a105a29d693fafe60b52725f5590a4e47462c3498ba1b8ce9113d0890d1f3b27280a3dd29c4e147990ab98e8ef306618d1dd22b567a3a27d194f4716f91eca8e20ab8cbd1bf24b2b0
  | 7, 35 => 0xab98d167c356f25336deac7e2ba5955844f67c2aaec6156cf559d48b642aad90a5a95530e5a707aa5b90056f54542bd112a872f96a1550d4b2483aa1a52dc4b536b0436cea5d2fd27a54b9dae3a0a971c869ef52af602bdaa51a65a63d4a2dc0b90a94351a2e351c9714852a2381a601543bc3c494a85d89c64750695dc4829f9d04353d3f36312a0a7c9605ba54f820d3a0a9e4a2e38853a81a4de1
  | 7, 36 => 0xb07aea16ef60acf72b1ac12b3bafbd80e8c64b0aff1bd580f5fd1dc53cabf94caa02d7d241a6b1af719ec1415edd1ea5cabda78f681d7ae052fe0af4ea6e5a15e6d14ae52bc70e04b05782818540aee85a5bed5d9e1dc34eba633247a573639e857ae66cec5435c8249c5d2b630c364956a2476082ad05161a615a04959516b3658f8705648de4137ac8bf999cf588472cddaaf6a73683d5dbbe23c2
  | 7, 37 => 0xb45e3f260968a77dbd5ed11555892d9f49b2a66b3e1c8050f66b6cfd4d2ccb76022bd995a22b91b3177596476610b0989ecbbbc238959580b4c00b296dd056565192a359ec9fda811359346c0517b256a1a70564888f04d2c74b8e9d358cf17a775b1921fd8ef631e924e1ec604c5b11589c960442b133f32747625c96d782c4b5a1549588db98604b1107d176f62079aa19ec3fabc3e3d852cac4f3
  | 7, 38 => 0xb8679995217090a61e12e0e0ee6e25c04a2cc72b8088ea4e97010faa382e01c9b561dbf3a5f4b0b7bc47c1256ef2d8508edd9841a825b9e902897b6c67851a76d6218b716dab1378685b1faecc13b613278ecf6c148ecfdad79c976db5ae4eec1a0b5a2cf29a56b04cf3a9ed45391863da7edfb2c5b4d922504f69b184c44ad32aff390da55536fd2b49fe215c968e6bf06cad1b9a306bda30d54b10
  | 7, 39 => 0xbce176d145792e2eb90af140e4a4bde266a6692bc01f4ea8f76f77eb312ed89d2a805d996e32f6bae801d48d7598cea54eeb31513ba5d60318ce2bac02c410f7506872fdae9b5869595d16d227e5b9f669440773e383a68ae7c5de1f05ce469c6c2b9b0f89483734926171ee5c4be9c05ca75171c0b92ef45d017235349d02e3bad13d85c55454ab4b88bcbd72570e92a0d1ee1afde58adc35933397
  | 7, 40 => 0xbfaededcc17f1872b68efe199f6425fc2cbf373bf71345c057ecbb4148afd90752715fa38f4824bf40a026e37e647e124afc3310aa25f85a75080bf057a94a37df346c642fb7afd5a85f5054ea43be91d5a0217d20b710def9647e6525f13546da1be1626e66f7c01c6a98af7ed8a9aa5eeafe2353bdbce3464f7b688c255ef679e32abdec757eae7bd4d5b6baf7a41673046f42f468ebde7413f362
  | 7, 41 => 0xc4b12661e18879b7829f10bac1831e2136c88e2c4224c59af879b53c85f0e0b3064061baf98170c36bc9110f863eb4379f0c0f74882e144753192c211c8df4583963f9f9b06a9599e260ca968677c17974080982e065cd0b0556baa0160a1c68893c0f1b4db658188a9b84b02ed547b9605773eb37c0881646ef81026d46570144f957a600e07f4b7c00ab2a6c180007c081effa9c4742dfe3dd72e1
  | 7, 42 => 0xca5845d56194899f4c9f27dd475b9e4e6a668f7c9bb2b8c87925b9922db248f7e2f36462d3e702c8c0af516b90e04bce8b2192fe75863f6965157c7734e14af8ede8a85cf1d86560e9e39b0953f7c72d1b99a98e408ad7031b790b37be354bfc5e2c66fffdc658cb7c32cc31944e3902e320a011b3c63f921cef8c3aecae1b182d0686962b6d97027c54e3624c98a9a6902df12f01c029625b0368e5
  | 7, 43 => 0xcea7fa61cf9d33d12a8b3a26c035a6725608d93ce3c15d68b9c3ffea5df3838d904066eeef0ab3cdb749656f9b28eb25cf361fd2aa966ae49e903cd5b974f039aaadcd38f3555a22fa6693ec6077cceac9182999c3fe33df336070483e65e89c933ccb2b08b2998fea59c572f4e119a8e5e8f531f1cbc81a9d479742681c072e28b3a20e5a0370a34cb284c21e595ef8c2bc72ba3ad41be56b1c0a86
  | 7, 44 => 0xd3f42a8a6da79af1060b4ed54596069b8b543d0d2fafb162fa54adcc48b4a3e7c3abe940e1e7a6d27be10fa3a4f6e6c35b48e6a18dbe8e0f8f307d1bbd38205a2c0221413448220223e880a78ad6d0f52e2bcfa1a58cc7874340d979be865640790d0676311eba04d61a7533ff70a3fbe7e43c8992cf84cfcc2f9ef1508f5f3db5be5a367a04e6ec0cf3867c78d9dcecd819f3b953e280675cca5550
  | 7, 45 => 0xd85b0c020fafdf3f46875f264e3c06bd49e73b7d764d55201ae8eb83fdf5c9a8f7426b89ffa5a0d6e0e52309ad90d8368b5a74c57106b48fcadd6d67d90230facbbacc9df590535a69eafdfac753d5df4ad5c5ab7cac48df563c1a2d1eabae2ec63d55f6405e1aab8eaa0cb54df729d2ea818cc200d4fe19dd0da9fb8f12df53ae757506a6acc6a21d49ad0aa65a91f8f0d0b51949055be9fefb8480
  | 7, 46 => 0xdc5ac463e7b8967f2d0770f048ae1ededb608c4db93a01fafb725aaa95b6dab8c8316d90632947dabf8c4727b571db16d36a8c816b86d35091115da5702c065b4337eb00f683e575cbecfae72da7d9c9b9a4e5b2dcde9cdf65a296963ec9abe4147d9304f67cfb2434e86c76456168e3ec86d764b3d906c4cc29b1d333194b6369ce5286c67778706d88ba55c4fb114b8811f61eb91868ec3b0c8222
  | 7, 47 => 0xe1a2fb05c5c30578469b85f09b9d0f08d230e90e0d84950efc178d2039f82cd095f9f041f38624dfeaff636bbf9b7c27cb7f03bc83befcf5710b2df569ecce9bded54a8db7b5b15b0bef6118f406dec116e00fbd4675b11379c52c95a6f2f094564ddfd859ac5bbaf75018b76320552a6ec0462f23dd7a8f834fbaf22f9d97757b02acbee6ccbc854dcd25a4a65b97650330b727197551ee4a8febc7
  | 7, 48 => 0xe695da5705cbeadf238f976bebb13f2ece427c6e598858321cafe3034df95d602a9872ba0e3344e54b2e24a9ca8c55868b947f2e3cbf283440fe2e501c7ce67c9d6da87579377f42aa724025a766e4780921efc8b8d33b0f90cf9475b7218ba43b0e40bf663abc7bfd30c1f8e26059baf1b0316f97e355c7102fc66bd1a88f8bbdabae3f160714f50e26f5e1b01c4d5080d0387fa936a070f69ce5d2
  | 7, 49 => 0xeac1e8cbcbd581cf588faab90a209755339e1e4ea8db6eb27d4fd50b9cba88ed43587511823365ea076a21abd3ac95508ba670a5b0874c9ec9060e97ea8cc89d228feb753a31f2e6b0745b1313e4e8b3e8c301d13b09b71fa25da1738744a663102e835278d2fd043ff988ba076ae3787403fa0212e7f046eb09cf9e5ec9139d955b0ea73a7b784c3e71b83884fce35a6b88b9ac564670734e4f4167
  | 7, 50 => 0xee4166e78fdc66e1871fb7b2f3173f6de2785c4edb45822c7db2bb03303b64f775627699a66df1ed22de0501da317e3b9bb42c4b7a3f676bd8253ec93cc9b41d8f0a3d5cbb1d03d9d276377ba5b3ec5491d8a5d89ec75493b0d230a28f5f58bce55ebe6636449d7abfa07cbaf48c462bf5dc7f0dd3eba4358fc7d6c9e68483acc78d759f58d446057eb0fc25d8fd5de5dc3d7ab7d360c975671ce663
  | 7, 51 => 0xf2fd4e0947e591eb210bcab839699f9506a11a4f29e019c2fe51a1dc5c3c9aed0618791f32c8d0f238bbdccfe3df51cfd7c794f0793f8e25e0010f16b51a7e1e2b54a91cfc51fb594bf8939cf581f122808d21e1c3372a5fc18cf588378084f2d24efbeed1d27df5433049fbe7da77da77a4ebcd44eef6b22563ddc3ca8743bb4d93a8a776648a4f5eeb95f982bdd29a297cbba3b86923773b9b0680
  | 7, 52 => 0xf77b7023e5eed409c74fdd63055abfb841ad167f6f3bc5929edde41cb5bdb98606197b7043c602f673450c0bece48bb5dfd9a2d5893fb2d4db2a2f63612dae7ec0525cd43d769476c1facf54c2d2f59d8802e9eaa65319c3d3e2868e97a59ee2fe7f4a349e5c5e93152b44bd1beec65a7a35a8eae0f45de111e5e89413c35fce00de513f9be5d95a0f37844eb85e6d0eb9d0fcd0362473799defa630
  | 7, 53 => 0xfb989c5d85f6e643a85bedb88c6117d586e42a6faadd80e63f531a5970bea4e071797d40584660fa6e130d67f4d3828ed3e90ea7843fd16a28963fa1abb924ff42609c597e8395f3807d05516ad3f9a88c9bcbf307103107e52b975fa7ca3c8ad21f8f85b8be1f1cd9abedfe2db87169fc4f0f51b2f874670ee1f0cd013c07e1643b60bfc2c7655a2f7baa226efef2cd6bbdfde0901940fbbfc8a4d4
  | 7, 54 => 0x3ffecb34f17fe91f4807ff6f814de5fe2ca9995ffc26578c07f7948ebf1febdc04541fd11951e87fa1b19740ff2a0af150fe52450149fc6e6cbd8bf8bb238f87f0848eb53fdb3351b4bfb63d516c3f6a80a462fea5a633a7fd368ce7cbf9daa11a1ff3a5ae74bfe4f5e6916fc82c7e2ebf8a3ea1743ef60f03b0fde627c694
  | 8, 0 => 0x6fa47d81eede85398049a32ddc00bb3519d807364c5880064c87cda82818c4fd003baeb479c0b7568d164144aa9138041d39119a07a26277fc0274ae4d6806a91d65500c11d5d2c001226a5240723e2b1b81c271edf6001ce2630d0111abc45a0572a407d01e45080ae01009f6e6303812160a60f02326dcc06e458418010885062e0300ee92d60470e77a6c12013336f00cc2645770000214c1e087
  | 8, 1 => 0xfe9124812ff6e8548393c05dd40696f828bc036dd8474406388570e818acb47ce0615840744091ae2d13806957a401020aaea44902254f3b2c0a3a749f58129499e5e8142892466063ce5c37a0a79b95c0c18727e8fe814a413b73073c6578e80038679f40180fccce58191f29c2806bbdadd1c0677abc234040ed7f7e0091cad45a02a3843fd00e0
  | 9, 0 => 0xa51256007
  | _, _ => 0

def poolHintsCount : ℕ → ℕ
  | 4 => 24
  | 5 => 201
  | 6 => 597
  | 7 => 1754
  | 8 => 60
  | 9 => 1
  | _ => 0

def poolHints : Compact.CodeBook := ⟨26,13,poolHintsPage, poolHintsCount⟩

def terminalHintsBuckets : ℕ → ℕ
  | 3 => 3
  | 4 => 6
  | 5 => 135
  | 6 => 4143
  | 7 => 696
  | _ => 0

def terminalHintsSlots : ℕ → ℕ
  | 3 => 12
  | 4 => 23
  | 5 => 578
  | 6 => 17648
  | 7 => 2966
  | _ => 0

def terminalHintsShift : ℕ → ℕ → ℕ
  | 3, 0 => 0x200000000
  | 4, 0 => 0x700000001000400000003
  | 5, 0 => 0x70000000300000001000700050003000000000000000700000003000000070006000000070002000d001d0000000000000000000400000005000100000000
  | 5, 1 => 0x100040000000000010005000200000007000200010008000100020001001f0004000000010005000000010001000300000000000000000005000b000c0000
  | 5, 2 => 0x600070007000000050001000400050007000a0000000000000000000c00050001000e00000001000300020000000e00020006000100020004000300000002
  | 5, 3 => 0x180001000000130000001a000a000000010003000600030008000700000001000000000002000300070003001200230014000c000200000000000300000005
  | 5, 4 => 0x180001001100130000000b0000
  | 6, 0 => 0xa0001000100050007000000000001000200020000000000000005001400000000000100020000000000100007000000000001000000160001000900030000
  | 6, 1 => 0x30000000b00000003000600010007000200000005000000010008000200000008000c0000000000000006000200010000000800000014000400000004
  | 6, 2 => 0x90000000700010001000500040000000000010001000200040001000a00000005000200040000000000000016000000010001000500020002000300020001
  | 6, 3 => 0x40004000700000003000000010000000100010006000100000005000000030001000200020000000000010002000100000000000100000003000200000000
  | 6, 4 => 0x1000300000006000000010007000100160005000d000000000000000400070003000000000001000200000005000400000000000100010005000000040000
  | 6, 5 => 0x4000100030003000000020002000200050001000500000000000200000000000700000001000500020003000500050001000100030001000e000000000000
  | 6, 6 => 0x300000003000300070002000000000000000200010003000000000000000100020005000400010000000800070003000400020009000200000004000b0000
  | 6, 7 => 0x40002000000060004000000000002000600000019000300000002000300000000000200000000000400010000000400140000000600000007000400000002
  | 6, 8 => 0x30000000100000001000300010008000a0000000000000000000d000000000001000000000000000000040000000700050007000100000000000100010001
  | 6, 9 => 0x200000004000700080003000200000000000000040000000e0006000200000002000200010000000a00000006000000090004000400000003000100050006
  | 6, 10 => 0x400030000000000050011000400000000001700000003000b0004000b000400010003000100110000000c000300010003000300040012000400020000
  | 6, 11 => 0x3000a00090005000000020000000e000b00150002000c0004000100000000000400000000000100050000000100010000000300040000000c000000030006
  | 6, 12 => 0x130006000600040008000200020001000300000000000000070002000200000003000f00010000000000040003000100130000001100010005000000080004
  | 6, 13 => 0x30000000800000004000100000000000400010000000200000005000300130002000700000005000100040000000000000000000000010000000000010005
  | 6, 14 => 0x100040001000100000003000c00020003000100030001000600000000000b000a0001000200030003000100010005000100020000000500090000
  | 6, 15 => 0x700100000000000050006000200000001000700000001000200000000000000030002000b000200010003000900010003000600000000000000040000
  | 6, 16 => 0x50003000200000004000100030003000400040003000200000001000200010000000300010000000200010000000200000001000000010000000000020000
  | 6, 17 => 0x10000000300050001000200020001000500040000000700040000000000070001000300020000000100000002000c0004000500020000000200010001
  | 6, 18 => 0x1000100000009000200000001000200030000000300000000000600020000001c000d000200010007000200000001000000000003000800070002
  | 6, 19 => 0x30006000200040002000000030004000100090009000300020003000000000004001000020000000800000004000000000001000200010012000000000000
  | 6, 20 => 0xc00030005000200160000000a0008000000000001000a00010000000100000003000300280006000700090002000000060006000000010000000100030006
  | 6, 21 => 0x1000100040000000600020010000100090003000300010000000200000000000100020000000500040001000c00000000000300030005000100000002
  | 6, 22 => 0x10003000400090000000500020001000c0003000100040012000000000003000600010005000f000000010008000000000001000000030006000100010000
  | 6, 23 => 0x20000000200000000001000000008000000100001000200010005001c0001000000060000000600020000000100020000000200000000000000000007
  | 6, 24 => 0x1000010000000000020005000b0001000000000000000000030001000000080000000200020009000200000002000f00090000000100000000000100020000
  | 6, 25 => 0x1000a00000000000200000009000400020001000c0004000d0005000b00080000000000000007000000000000000300010000000100070002000200060002
  | 6, 26 => 0x100140004000100010002000100000005000600070016000a0000000700040003000000010008000000020009000000040002000000070002000000000003
  | 6, 27 => 0x4000b0002000b00080004000000010000001600020009000e00040000000100020001000000190007000b000200060003000300030005000000010001
  | 6, 28 => 0x800000000000000000000000900010008000300030000000400000001000b000000070002000b0013000300000005000500010000000e000a00030006
  | 6, 29 => 0x400000005000000060000000400020000000000030007000100040002000200010003000000040008000000010000000e0000000200090000000600000000
  | 6, 30 => 0x100001000f00060001000800030005000e00000001000000020002000400090002000200020004000100010001000100040001000200010003000000000000
  | 6, 31 => 0x1000000000000000000020009000000030005000a000d00020000000300010000000000060000000700000008000100010000000100020000000000020002
  | 6, 32 => 0x1000200020000000000040003000400070000000500000000000000060006001100010003000d00020012000b0001000000020000000200000009000c0000
  | 6, 33 => 0x1a0001000800000000000100020004000000010001000700090002000a00160000000200020000000a00020000000600020000000000010000000000010003
  | 6, 34 => 0x40000000300030006000500010002000300090001000200000002001000010018000300000004000000000000000000000008000000020006000800010000
  | 6, 35 => 0xa00000001000000010005000e0000000000010004000000030004000300000008000b0000000100030000000000000008000000010004000c000f000f
  | 6, 36 => 0x4000300030002000000000002000000040001000000010000001c000300010000000000000008000100000001000100010002000700000000000300000007
  | 6, 37 => 0xb000c00020000000600030002000000020000000100000003000000030005000f0000000e0002000800000009000000000004000200020000000d
  | 6, 38 => 0x600010000001d00000000000500000004001300000002000b000000010000000b000000040005000b0000000000000006000000000002000100070001
  | 6, 39 => 0x3000000000001000200000005000f00040000000000050003000200000001000b000100040000000300000000000000000002000100000002000600030004
  | 6, 40 => 0x1000000000000000900010004000900080015000100010000000b000500020001000300040005000000090001000400040001000d00010014000100000007
  | 6, 41 => 0xc0002000b0000000000020001001d0001000400070004000600000000000000090000000f000800270002000500030000000100030001000100010002
  | 6, 42 => 0x30006000a00050001000a0008000e000a000400010003000100000001000000000008000500020000000c00000000000d000c000000000000000500000001
  | 6, 43 => 0xc000900230000000a000a0001000200000001000200000000000e00020000000e0003000c00020002000400010000000200010006000500020001
  | 6, 44 => 0x12000a0001000000030001001300060000000a0000000100000007000300080007000000090003000100000001000100120003001200010001000400060020
  | 6, 45 => 0x40008000100000000000d000000030003000500010000000000000002000c0000000100040001000500000000000c00000001000100090004000000070001
  | 6, 46 => 0x30001000100010001000300000002001500060002000000020008000100030004000200060016000900010012000000020004000a0000000000040001
  | 6, 47 => 0x400070009000000000001000500040005000e00000000000f0001002500050000000e00000019000000010000000f000b0001000000020000000200040000
  | 6, 48 => 0x90000000800000005000500070002000c000700050000000200070000000000090001000c000300010000001b00070000000400020000000800060002
  | 6, 49 => 0xe0000000300000005000b000000000000000300010000000000050000000400000006000000000000000000020003000000170000001900010007000a0006
  | 6, 50 => 0x20002000400010006000300030004000e000300030008000000030002000900000000000300070000000000020001000000060010000000070000000a0002
  | 6, 51 => 0x20000000000030003000000010000000000000000000300000002000000040007000700080004000500000000000b00020001000000030000000b0004
  | 6, 52 => 0x50000000b00000006000100010008000e000d000000000002000100010000000000000003000200180001000100050015000300050003000400020000000b
  | 6, 53 => 0x7000700020001000600000000000000020000000d000000020000000a00040000000800000005000400000000000500100000000100030001000000190002
  | 6, 54 => 0x400000001000e000000000001000d000600010000000200030000000000070000000000000003000200030003000200020002000600010002000400030001
  | 6, 55 => 0xf00020002000000020001000000010003000000030015000100050007000100010000001000030001000000010000000d00000002001100000000000e0001
  | 6, 56 => 0x1000c000600000004000000030003000100040000000b0000000400000001000500070001000000100001000f000100010000000300000000000600020030
  | 6, 57 => 0x80000000000000001002d000300120002002400010000000000080006000000120012000000290011001e0002000800010002000100010002000400040000
  | 6, 58 => 0x5000500040000001600010000000b0000000700010000000000000000000200080000000300000000000d000400050001000100010013000600030000
  | 6, 59 => 0x20001001c0000000000130001000400000003000800020000000000020005000b000b0001000800010002000000170002000000100000000d000300050000
  | 6, 60 => 0x50004000000120002000000000000000c00000000000400040000000500010001000a000100010000000e001200080003000300180000000200000005000f
  | 6, 61 => 0x3000500010006000800110002000000040004000c0003000200010003000400040008000200000002000500000000000000010000000000040000000d
  | 6, 62 => 0xe000000090003002900080000000000000001000000080011000e00040002001f0000000d0006000300000001000400010001000100030009000800000000
  | 6, 63 => 0x1700000000000000000000000b00000002000000000004000000030000000f0009000500000007000200000000000300060002000100000000000000000001
  | 6, 64 => 0x700090003000700000004000400020000000b0013000400040000000900000000000300050005000e00010001000100040002000000010021000300010000
  | 6, 65 => 0xa000000000004000000090000000a000100150000000000090003000600000003000a0005000300070003000b00010006000e000f000000000005000c
  | 6, 66 => 0xd00000001001c00000005000300020000000f0001000200040001001000000000000200040001000100000001000000080000003400030000000100030000
  | 6, 67 => 0x11000a00050004000100050002000900030000000000170002000200050000000600030009000900000000000c0006000b0012000c00040014000200090017
  | 6, 68 => 0x4000a000f000200100004000500050001000100040024001c0008000700040000000000020006000200010001000c00010000000800000005001100080000
  | 6, 69 => 0x20014000500060015000c000c00010001000100010000000000000002001f00000000000c0009000100080019001200000001000800020000000000130001
  | 6, 70 => 0x120002000100000007000500000004000000000003000200030006000000040000000100000000000500000001000100000002000500090000000500010000
  | 6, 71 => 0x60002000200060007000b00010000000000160000000700000003000000000002000000000001000200040001000000000007000100000009000600010003
  | 6, 72 => 0x1000100030000000a0002000b00000007000400010000000300190005000a00030001000000000000000000100001000b0000000200060000
  | 6, 73 => 0x300020002000000230000000000010005000e00020001000f0005000d000300140003002e00040000000c000f00000004000500100004000c000e000a0003
  | 6, 74 => 0x200060007001700020010000000000018000100000004000100000010000000010006000300000003000b000100030000000900050007000b000300030010
  | 6, 75 => 0x30000000000020004000100000007000200000000000100000000000000000003000000000007000500000000000400040007000000020001000100000010
  | 6, 76 => 0x10001000100020007000000010002000700000001000000020000000000000009000c00040000000200000000000100000003000000000003000000000001
  | 6, 77 => 0x30001000100010009000000020004000c000100080000001800010010000000030001002700040004000000000005000a0001000000000000000400000003
  | 6, 78 => 0x10012000500020002000b00040004000d00050001000000000004000000000003000a00000006001c00000003000400000002000100020001000100030018
  | 6, 79 => 0x100030000000200030005000000020001000400020002000a000600000014000000040000002e0005000000050004001b001400010004000000010006
  | 6, 80 => 0xe001000000029000e00090001002000030002000000030000000000010000001c000000040009000400090004000100080004000500060000000300010003
  | 6, 81 => 0x100020000000000000005003000040000000500010002000900080002000900050000001400090000000400000001001100020002001700000002000f0001
  | 6, 82 => 0x2c0002000e000c0001000000000004000300180000000000000000000000010000001200010003000100000002001c000100010003000100010002001f
  | 6, 83 => 0xb0000000900060008000f00000004000300010000000f00000000000000050006000000210008001400010001000000050015000700020003000600040000
  | 6, 84 => 0x50000000a00030005000300000004000000020002000a000000020005000900060001000000020005000000010000001f0004000200000014
  | 6, 85 => 0x1000500040009000000000012002700150000000000020000000000010000000a00020000000200000002000400000000000800000000001400040002
  | 6, 86 => 0x30001000e0000000000020000000100100002000200020009000900090001000400020002001e000500140006000400000003000100000010000f0007
  | 6, 87 => 0x300080002000a000100000009001b000000010002000100040008000000010023000600020004000100020003000000000000000100050000
  | 6, 88 => 0x1400020000000000010007000000000006000c0000001d00080009000c00010000000300000001000100060005000200040004000000020000000d0000
  | 6, 89 => 0xa00070011000600000009000f000000000001000400090007000a0006000100020003000100030000000e00090003000100020003001500060000
  | 6, 90 => 0x1a00080001000800010000000000020000000600080000000000020006000000070004000100000001000300020000000000050005000000020027000b0008
  | 6, 91 => 0x27000f00040002000000010009000400010004001700000000000b0019000e00010000000700010000000200090002001e0009000100050001000500020000
  | 6, 92 => 0x11000d0001000200010007000100040001000000000004000200030003001b000e0001002b0009000000050000000000060000000c000c0001000300030000
  | 6, 93 => 0x2000000070005000200100006000200010005000200010000000200000006000100000000000f0019000300020000000f00000002000100050002000c000d
  | 6, 94 => 0x4000f000900010013000000000000000a00030008000f000d00020000000100080000000300090002000200000001000200000006000f0000000200050000
  | 6, 95 => 0x110000000000000022000200060006001800030000000200080005000a0008000d0000000c002b000000000000002e000600030017000d000100010000
  | 6, 96 => 0x3600090000000a0000001100000002000500000011000900000003000300070029000000170000000e000200050007001a000200090002000100000009
  | 6, 97 => 0x2000200000003000300020001000100040004000100000000000b000800000000000200010000000900000006000200000000000000020004000000100013
  | 6, 98 => 0x200010001000000090000000d0001000000010024000f00350000000000010013000400000013000100000003000c000400030002001d0003000200100005
  | 6, 99 => 0x1000110000000400060003000300000006000700060030000d000000060004000c0002000200000003000000010000001400010011000000080018000c0004
  | 6, 100 => 0x600000003000a0011000a0001000200040005000400080020001300030001000000050000000300000000000800080007000c00020000001100120002000d
  | 6, 101 => 0x800000009001200040000001100030000001100020000000500000000000d0008000b0007000c000100000001000a00020000000a00010000000700000000
  | 6, 102 => 0x5000a0008001600160005000e000200000000001f000d000300150001000000020001000100000000002f00140002000600090000000400000000002b0012
  | 6, 103 => 0x1100000011000200040003000f000100050002000b0004000000000003001e0000001a0006000a000500080007000400000007000100000008000200070000
  | 6, 104 => 0x30001000200020002001000030000000b000a00250006000000060000000600090010000b0010000a00040011000000010010001d000b0002000100020004
  | 6, 105 => 0x26000e0004000a00020000000000000005000900000001000a00070000000400090003000000060001000100000000000000020008000a0004000000000000
  | 6, 106 => 0x6000200010000000b0000000000040004000000000003000000080006000000000002000d0003000600030000001000000000001d0005000000010002
  | 6, 107 => 0x4000100000001000d00000001000400050000000100000003000100090001000d0003000e0010001200120004000400000001000600010000000800010000
  | 6, 108 => 0xa00010000000000000003000500010000000c00010006001700070000000100000001000a0002000a000a0001000600070000000200080001000000060015
  | 6, 109 => 0x5000e0019000200040005000e00020020000100060001000100150009000d0000001900070001000c0000000e000000010000000c0003000c00120003000b
  | 6, 110 => 0x130000001f0014000400010001000d00020001000000050004000200080000000600080005000400010000001a0001000f000100000000000000300001
  | 6, 111 => 0x400090000000b0000000200110003000100000001002500000000000200000019000a0006000300010009000800330004000c000300070022000300020002
  | 6, 112 => 0x30012000700010004000000020000000000060006000100150003000300040000000000020007000300070001000100050002000000010004000100000000
  | 6, 113 => 0xa000500000000002f00070004001700020000000a000000010001000d0005000000000000000200000001001c0006000b00010000000f00160003000e0003
  | 6, 114 => 0x13000000000002000b00000001000b000000030000000800030004001600040000000c00070020000100000000000d00030000001300090007000300070000
  | 6, 115 => 0x5000a000300000002002b000d0000000c000000040006000b00190006000700000003000400030003000300020003000f000f00010004000b000200030008
  | 6, 116 => 0x10003000c0000000c001b0004000300070006000100020002000000010001000200060002000a00060021000100000006001600190017000400080002000c
  | 6, 117 => 0x20003001c003b000100010000000c000400030000000700000003000d0000000400000000000a000100000000000500000001000a00050002000500000047
  | 6, 118 => 0x100000000000a000900030005000c000200000005001b0002001800050004001100000006001200000000000b000000010000000000000000
  | 6, 119 => 0x60008000100040002000b00060002000d0002000e001c0001000400030008001c0001000200040011000d00040004000400030002000000040000
  | 6, 120 => 0x20000001200000006000a0021000000000003001100040000000300000001000000250029000100060000002f0005000c000600010000000100000007
  | 6, 121 => 0x110009001800010000000000030001002c000a000a00000002001600000003000400160006000100030020000000000000000000040000000000030000
  | 6, 122 => 0x40003000c0007000200070001000500020005000100010000001d0001002500000000000900090015000b000500010023000a000000000000000d00010004
  | 6, 123 => 0x20000000400050000001c0002000a00010000000100000002000e00110006000000030009000100030000000600010002000800010008000600010000
  | 6, 124 => 0x2e0006000c00270010000c0007000500010008000600060004000b000600090017000e000400000002000800080003000600000006001400010001001d000b
  | 6, 125 => 0x200370000000400070001000100020024000a0004000b001100000006000000000000000a000b0002000b0000000000020001000100010000002e00000001
  | 6, 126 => 0x5000100000000001100010004000100000001000900020001000d0004000200000005000800150008000a0001000c000e0000000500130002000000000009
  | 6, 127 => 0x1000500030008000000020000000400040020005c0015000000030006000c001f0000002d000100060029000800000000002b000000030001000200090006
  | 6, 128 => 0x2000600030002000000200000002b00000002000800010008000f0005000600000004000c0000002e00180004000100010001000000130000000800020002
  | 6, 129 => 0x20005001f0007000b0004000600040008000200020007000a00000000
  | 7, 0 => 0x10003000000040001000400060000000000020003000000000001000b000e000100020003000100010001000000000001000100060000000000000000
  | 7, 1 => 0x60000000000020004000000080002000300000002000000000000000500010006000000000003000a000d000400020004000000000000000b001500000005
  | 7, 2 => 0x10001000200020006000200010003000a0000000100030000000c0009000500010007000c00050000000600040004000100000000000600020000
  | 7, 3 => 0x400050000000000020004000000010002000000020000000c000500050006000200050000000c000200000003000000060003000100010000000000000000
  | 7, 4 => 0x60001000700020001000300060002000300020000001400010007000000040000000100000000000200000001000300070000000000050009000200010007
  | 7, 5 => 0x4000100000007000000010000000a00000004000000040000000300000001000300000015001d00020001000100000007000b000000000008000000080001
  | 7, 6 => 0x3000000000000000000000002000300030002000100000005000300010005000100010001000000000001000000000002000f000100010003000300000002
  | 7, 7 => 0x1000000050003000300010006001c00030000000100020000000300040001001200010003000a000200010004000500010000000200000000000000050000
  | 7, 8 => 0x70010000a0000000000000001000000010001000000000001000000000004000200030001001d0000002a0000000000000004000100000005000000010000
  | 7, 9 => 0x1001400030002000000030004000000010001000100090002000600000009000200030001000400080005000200010000000000010001000000010004
  | 7, 10 => 0x4000900140000000a0007000600030003000000010000001600000007000a0005000000000002000100030004000100020000000100010006000400010000
  | 7, 11 => 0x600010000000100040008000000090019000a0002000000010008000a00000000000f000000010006000f000500030000000d00070001000100000005
  | 7, 12 => 0x800020000000300080001000200010009000200090001000300000003000100130000000e00050001000100000000000b00010006000000090013
  | 7, 13 => 0x1000d00040004000000010003000700000001000700040008001f000100030001003c00010001000a0009000000000000000000090002000a0001000c0000
  | 7, 14 => 0x130002000800050006000000020003001f000000070016001000030001000d00000007000100010001000b000100010002001f001900030002000e000e
  | 7, 15 => 0x17000200060006000c0000000100000018000300000007000200000000000000000008000100000000001b00060002000100030000000800010004
  | 7, 16 => 0x400030001000600050000000c00010004000000050000000b000000010000000e000100010006001b00050006000100040002000100070003000000010003
  | 7, 17 => 0xd0001000600000000000100000004000a000100060013000600070001000000010007000d00020000000d0009000300130000000200000002000600000001
  | 7, 18 => 0xc00000000000100210004000000010005000000060000000b000a000500010000000000000000000000060004000000120001000600020004000100030000
  | 7, 19 => 0x40017000000050005000000080004000100060001000000030005000900080000000000030000000200010000000000070002000900040003000000000007
  | 7, 20 => 0x1000c000c0011000000020019000100000000000200000000000d000000010001000400060001000100190007000100060001000200110000000a00050001
  | 7, 21 => 0x1000e0002000b00010006000000060018002200000006000900030000000100050001000300040000000400030002
  | _, _ => 0

def terminalHintsRules : ℕ → ℕ → ℕ
  | 3, 0 => 0x992992fff22f
  | 4, 0 => 0x2210ffff929214ff020599f
  | 5, 0 => 0x938f6585205ff1f126f1ff20ff305f2ff1f2120fff342214012833f2757021191181f2221086221916812567f424fff59342660157f22464215520908f102f26
  | 5, 1 => 0x86f63fffff06ffff9f0ff9491562212201f8124fff1414f15ffff2f6f252995f2f51f21111162fffff4502ffff374ff2ffffffff05950f1602ff2f2905911699
  | 5, 2 => 0x590206f020200f96f52201f8453618ff00210112f3f262f082ff1510fff113f6f28262f5f0098f096f0611f2f54fff9f6f4fff199ffffff02fff2f7f60f16420
  | 5, 3 => 0x121429f5107f61411f9106469090909512406041f151102222802920295f9f19f2f2f60ffff4f2ff94211ff99221f966151f13f46111180925f6fff151201205
  | 5, 4 => 0xf01fff322ff1144962fff9fff282f226f126f22ffffff68fff2f929ff2ffff5309
  | 6, 0 => 0x34f30f1984525ff0ff2ff00337fff0f5f71f5f5f5030033ffff5f527f0fff42ff3f23002000350770010454f326013256f5ff06311ff225ff0050f1f8ff122f3
  | 6, 1 => 0x60510433005020f04f752f02435f0fff06f06ff3ff701550523620ff57345027f0ff0f3605967842f0ff003f64f001fff530045444ff9f44143f10f0300531f3
  | 6, 2 => 0x438f5ff02220f20f5ffff8f5f33320039fff45f315500122200227750000250f736043123107f0333f0f477ff06542f30fff2020231f500f147020701212022f
  | 6, 3 => 0x22f0209f0f25731012229f0f34f0ff06ff5ff0f3042358302255050383ff7f64800552f51327230060093777ffff8102031f2103511303f350ff2271f0021f2f
  | 6, 4 => 0xf330f003001f52220225121050572fff020271ff2265f475f630f04543f200107260f029f275505339136f0ffff56ff3ff33272f0f23703671810112f227ff24
  | 6, 5 => 0xf030f214f2053207f712573827528f08570260fffffff39f9006fffff1f53ffffff1ff76522f0f5f00f2fff6fff0ff50450331771008ff00f0f0562ff205233
  | 6, 6 => 0x33003f724403221220122ff3f00010300202016f5f7034ff030f0f4220f7f23f0f020005f08fffff00056f5f7f33547032001f5f330224255200001329ff22ff
  | 6, 7 => 0x750fffffff03ff3102ff34400300502400200000017010701f1ffff0f6363550f2ff1fff02860010f23710f5026fff000f21001ff0ffff00ffff042f07500240
  | 6, 8 => 0xf1008340220015633f20313fffff13f7f54040f450700ff320207fff20f7080008583ff4ffff66070ff5012596ff006073105ff51072367f0000ff0f20964210
  | 6, 9 => 0xf2000f00f20f2510f0013f43002f031595f2322ff001125218ff03f223010350ff60fff7004f70f2f70f1ff53f22623f03520708f5f57008ff420f332fff2590
  | 6, 10 => 0xf23ff002f0f0ff05f55330f2f3ff20305ff2ffff3f53550030701f3ff02ff01025ff28ff1f1777f20f3ff4895f10f26f7353ff52275619703032064385f010f2
  | 6, 11 => 0xf6033f06480ff031970ff65f525f1750ff7ffff10f005703011ff702f6ff2055022f0ff0f410f5f011083035000252f003f0260fff135003501f2f0f0370f05
  | 6, 12 => 0xf03f6370f000052531040120824026f2fff0f7f57f221f597ff4193f30462f5720f00f02372990897004775807f0260453243230233317255510f240f50224f3
  | 6, 13 => 0x3156717ff3305fff523f13ff550f9560941f20f5ff3221ffffff555fff70100634f404ff200216f0635ff02ff60f23f5f541210fff102ff230fff400f0223330
  | 6, 14 => 0xf2f2f7f301f2fffff22f30270054f3fffffff4003107448734f26f91ffff57035fff0083032350012057ff0ff52210050321310000007f04037fff0181ff2f14
  | 6, 15 => 0x4310035250100300024721ff1fffff3ffff5f03f02f33f7750f33ff25f2f1f12202f55f0ff701fff3f05fff0027033fffff33f1fffff03ff33f0020f340fffff
  | 6, 16 => 0xfff030fff0730f13f00650f0ffff2f2f3f0545250017ff3f4740305f77f18ff02f0001122502050263630802320250011750f3ff4314424310551f57461f05f0
  | 6, 17 => 0x4f6f25f2f127640f3f03322525f15ff12f00fff7ffff515753515f3f2422fff1f7ff70f21330ffff7f0ff03f05305003ff1520210f5f5f801305ff70f0ff173
  | 6, 18 => 0xf1f1307823045f0fff7f3f067f5f1f3308002f53231577ff1f10000105f503f32f5f0f542ff5ff050f4f2303000200113720026f222fff00745322ffffff0fff
  | 6, 19 => 0xf07031f0f74f6f0227003f3f00534031f6f5f09ffff005f42ff0f0fff5f822ff0f21fff50f0ff0300f128330130f2f141f6f2263002030f7f94907fff364f3ff
  | 6, 20 => 0x3300f2f1f04085f0203f3f1f7f2ffff07f000464ff8f7ff05fff213ff2f0ff52ff05112011f52700fff3ff1f2313f3f025f30ff40040668f03f2ff4f0f0f041
  | 6, 21 => 0x3f0fff527080f2f06f76450242f530024ff05f935f2f225ffff0ff2fff01f10fffffffffff3ff006550000142216225772402029575112031743030f02900131
  | 6, 22 => 0x2f557f60f33552440f8102035ff00f11353fffff26fff3f2f5f30f0f9542320f1f0ffff5f020349ff5fff525000f63f22f27f92020362f5f2f030f3ffff202f0
  | 6, 23 => 0x501f0f22f12202231f40218f01011f2012ff2434f310355f2fff9f71f055f732f1057420f1904003572ff2452231f1fff02f1f01fff7004f03ff236f73302ff0
  | 6, 24 => 0x1fff53ffff05f202f40ffff7f45f50fff526703100f08f334fff5f27f7008053038f2032ff2f7f0280f20ffffff73ffffffff13fffff31215f54ff2ff2ff2100
  | 6, 25 => 0x4fff5f0f075100ff03f552030f3523fffff9f406f00972230575f45f4f31f7ff6f0131203f21703300f52050020f009f12332000ff7610150815020f50f6f0f
  | 6, 26 => 0xff6307202333425f7fff6f8f5f8f3fff053ff20015036ff05f101f593ffff3ff7f51ff60423f56f76f3ff2f2f8f619302705320004f368273040f0ff1f030fff
  | 6, 27 => 0x573f0f013f0901f3300f0fff15105125f3135fff82f51100310f90fff5705fff5f0303322f0310655f00f0f353f6019775233f45035f14012716f50286212f10
  | 6, 28 => 0xf1f27ffff46550020202082f40ff050f0f00217fff001ff2f0ff03fff383000ff7f2f3ff350ff18f2457f0106ff003479515087ff1f7ff6ff4ff11f5ff010236
  | 6, 29 => 0xfff052001250ff164f080ff02f3f325003ff7f131ff464431329f05ff3f04002303702348552930223f071520202021843023205180532f03ff4f30f003151ff
  | 6, 30 => 0xf0f70112200f3302f0010f0f0f21f3f0170f4ffff0f3540ff41f501536ff9ffff2f4300fff0705f2fffffffff2f35f3105013ff5f6051805f0ff04f2f7ff3125
  | 6, 31 => 0x2f152f27134ff27ff10fff0f2931f821ff11fff1f162003ff51ff3f3f3fff1001f4ffff23350f3f60fff4ff05f221315ff601243643040430600170354ff0fff
  | 6, 32 => 0xffff8f2f0ff0f5f0441523101535104791090130452103f009185515500f336440050ff50001f72ffff2f120f1f3ffff07f013350fffff00f04f03f5078350ff
  | 6, 33 => 0x9612200530220514235876755283357730070ff60f25f300f0f452682322f602323726fff151f1733ff6ff373f2f52205503332026f410062107037620203159
  | 6, 34 => 0x3000200181233f6031030001030ff20f1002f131f306f623090424311025ff2f5f0fff3f7f42f5207665ff3043f2ff7ff7181ff25f2510552ff0650f51717003
  | 6, 35 => 0xf25f306f55f5ff15f0f0540f0321f5f3fff133332f23f5f0056ff631fff8f70f05f526f01ffff2ffff10f40f3ff921ffff08ff2081f05030ff2f1f0300425035
  | 6, 36 => 0xfff3f2121f10f13535ff3ff0f2f0360734033000021239234ff5ff1211114633352ff0f030770025ff0f0099771f6200f26393f32320f11112f07f20522f5ff0
  | 6, 37 => 0xf84f2ff015242202f9f140ff2f551ff201f0006663177ff73131002020ff6fff1f245f4f600f0505411f5f3357f25ff53f23f003f11f110f20572f33f2112025
  | 6, 38 => 0x2007800f3f11052f25352050640215522f083003324ff32400f1331ff1004672f25ff2ff30216ff54001130176900ff580f631f45f85fff030002f612fffff05
  | 6, 39 => 0x7fff4302ff90f3200120ff02f555ff351f0ffff3ff0050800422230000520900f12ff132ff30ffff257005330ff752ff5103f311472fff3f3f2f700f6f030205
  | 6, 40 => 0x170f3f5210fffff050ff3820865f0000fff4f00020f503ff5f25fff5f8232f6f5f4ff03f030f03f0f5f0fffff03620041f0f03fff250fff0f310212400f79
  | 6, 41 => 0xfffffff8ff6ff0f3f32f2ff000fff095f61f0fffff4316861ff0fffffff055210f7f3321f027f0004ff405ff015ff722103fff2ff130fffff5f035ff10212101
  | 6, 42 => 0xf107ff0223043325fff5f130f81f0121f1620f301022070f6f2f335f3ff2ff303fff05390015f970040473f370252ff14014506ff10f6ff6009f263ff1002f0
  | 6, 43 => 0x20fff5370ffff232f05f3fff2ffff2f30ff2f0f32f00f2ff5f9f4f6f2f000f13ffff735470f70f3ffff2200f3105303ff08623025740240205f0f25f46787643
  | 6, 44 => 0x277163f032100f30032fff00772362033500330005f052166525280f1752500006111050233035130893630317161721722522507f4503119021f173f010245f
  | 6, 45 => 0xfff9f1f1f0ff22f02ff5fff318005273010f70ffff023046377003302003545501721505f8323f5f6f8323200707522fff1f55f0050f3f3f553fff3f2f1703f0
  | 6, 46 => 0x20211001001ff503549f7f36550f5f307802374f323255f3f7f5f0520533f330ff56206f41f00023022313f01f68f68780255353f8f1f0ff00fff2f1702fff2
  | 6, 47 => 0xf02808ff901ff0f427612021ff02040fff3311801f266534ff1f3525f309703ff20000400425fff79335ff330310f336ff8724ff002f1520113385246354f007
  | 6, 48 => 0x6ff1f02022f09ffff24200500003072335f0035fff007ffffff780520420114fff5f2f5220050000793f47203130f025755f9023100f3ff01402f1f5fffff71f
  | 6, 49 => 0xf5f1fffff30052f225181f0f2567f369f73f008ff7ffff05ff03040f0f81ff0f22520f07fffff1f234250f30712051506f55f7ff5ff04005f5f1f4ffff038f6f
  | 6, 50 => 0xf135026232f3f8f53220ff32f166000f030f03f3f0f5fff00f76f11640603fff0f621f0f0f543504f00f00ff83226101ff013303732f212f371082300fff5f35
  | 6, 51 => 0x2365111705ffff0838177065f010130ff650190515050713450f8732275169f0fff3ff5208f35551ff6ff25f0003f4ffff0f05356ffff13ff0ffff850603ff8f
  | 6, 52 => 0xf2f5f0ff50310000003ff00f1ff23fff20f7403f33330205ff076004000950f2f4f3304020f0ff55f983f0330536fff07f0fff13ffff13075331000055722742
  | 6, 53 => 0x20952251703131001f06f02fff57ff5300f75f005f102020252f30f0f7420ff2f3f0ff300ff5028ff96100f32000007f5fff22f505f215ff556ff0f321632100
  | 6, 54 => 0x5252ffff2ff0ff3ffff500f0f47113707f4505793fff45051f1ff2ffff3f2f02ff0f2ff2f20352200560f10ffff3f0f5ff13fff71f32f0005005700303021170
  | 6, 55 => 0x52435553f0f0f03300fff4f2837f3ff39330f7320313041f03305205000060218f83755052012508055725f35082246f0006f12570020ff2f0fff1fff333f10
  | 6, 56 => 0xff021ffff017ff404010035f03182f55f03f0172fff51001ff2ff124f1f353f20f1fff30f350fff22f10fffffffff0412ffff3fff0f05011f350290011303717
  | 6, 57 => 0x1821ff20601060102303f361f141511fff0ff2ffff2ffff20f3f0ff0f5056007ff3f500374f222006083005ff0074452330ff4ff9f62ff15050155303072ff
  | 6, 58 => 0x2ff3f7f2f4f4f0f2f8f2ff01ff02f25f0ff723f20ff45090160ff1337023456f00300715857048f755701f3f9202f016f23f3203870470ff34ffff4f8fffff15
  | 6, 59 => 0xf5325232610f906f4f47055ff522ff7fff9f10f3f2ff7ff0f1ffffff5f0f04232ff31ff36f10f0502412f520f0f50fff22f582012f0f240ff83f22ff00f7f5ff
  | 6, 60 => 0x2210325ff0571f4f77f5620ff64404503f0230f14f3501f30ff2ff0fffffffffffff3ff8f31100f2f58f560f0f330fff028200ff030582025f402202420fff01
  | 6, 61 => 0xf3657000733327f72023ffff251270f012058012f30ff5f0171406f3f11202f9f0ff5f513fffff5f23ff1203ff307ffffffff29f1ff1fff20f4352f000023351
  | 6, 62 => 0x4f820057ff30230f60208f87f680f43060004035203ff4313032171fff0307002f0533074025ff0f2f3305735f1f65551135ff00f7f24f46304ff31f11ff3f0
  | 6, 63 => 0x6418305fff13226ff0ff76620f0f25fff0f430f40fff3f44f2210ff60f700f15ff134f4f00f05f1f6250f3f5713ff0ff8f4f004ff0f020f010ffff20363414ff
  | 6, 64 => 0xf3f315107453303052f58023275317f001ff01150162ff070f2031013300fff02f260060313f617093292fffff03100f90910354337053525000530f5f0f4040
  | 6, 65 => 0x74f73ffffff0013f20f500f03f2ffff333fff000972f00f518f30071023035f630f832f0f430643273304600f060003fff8f373ff7ff523fff0fff527312021f
  | 6, 66 => 0xf0f2f2ff1fffff3fffff5fff553f0032ff5175f33590f2ff5f3ffff5ff350fff1ff3f15ff01f0920050f5301f06fff6ff70f2f32f3f3f011ff081810fffff205
  | 6, 67 => 0x2ff540f2f0400000f03043f007f0f3007fff055ff555f04882000f214f02f532230020003f10350f5f6320070420f51f654ff24ff6f9546ff6206f76fff1f4f5
  | 6, 68 => 0x20f622f02310040f53f0f06f03f0495f032f127720023f00004f0223495367f1310033f910f0f6f3703433f34437ff3f807f50f0ffff650620170f37f6300725
  | 6, 69 => 0xff24506760f0ff0ff1ff01610f3f0f2f12f31f558753f75f80f3f2f702125414f0ff06f056020f31200057426f92ff05f20f1fff3ff4f3f07ff1335833017f57
  | 6, 70 => 0xf351ff0ffffffff0fff6f210ff01ffff22f2f1f0f5f150ff3fff364ffff6f35375fff155000f06337f0fffff20069525ff3f035000422508873104561812140f
  | 6, 71 => 0x3351fff53000101326f32f6303fff50270f53550326605232120f0052840f415057f432f211006013003235540323762210702721204f10ff1f0fff550ffffff
  | 6, 72 => 0x980ffff2f030052301ff4987354f6333ffffff0f02075ff0f01fffff23017fff61f4ff06f1ff2ffffff125593f06332f0ff2051533f0f7202f45520fff25033
  | 6, 73 => 0x5f27f00f506fffff331f2f302f11ffffff0320204fff23f23f95750022222033062052503f102f0f253f0f0f0fffff4f721f0f371ffff0f1133f5fff5f0ff120
  | 6, 74 => 0x14205415ff300111f35f4f0206f2f0f3f1405451ff229f607560f20000802211776202120261342605200150f0706000023f30ff77055f1f2508ff133f3f0ff3
  | 6, 75 => 0xf05ff0ff0f055ff9fff1fff3fff0504624014273607f043150f5570f360561371208321351144f3f4f3f1f1302727033f677f46ff5f02fff05f572f405f5ff05
  | 6, 76 => 0x802f59f2485232f575f1023ff8ff7ff00f2ff501ff20f4fffffff37ff901f82010f7ff50f1f5153f7013000fff33f30ff5ff7052f1f4ff0f6f452300ffff3217
  | 6, 77 => 0xfff2ff7fff000603550f40ff1162003ff0340f232f92f2121f5620fff30f224735f4f513550150f3870f510ffffff07020080075104f2f000f5f6503f65249f7
  | 6, 78 => 0xff60f367571fff402f0ff04f1f050ff250050f3050ff0604f003ff18913fff8fff5ffff5284f51061ff1011950f4ffffff170730110fff004f6ff04f2331f250
  | 6, 79 => 0xf34f1ffff00400f3f44f13070f03f50f4f240f0f1579030ff005492f7f1ff052147413f0f5f53250030850510050f130ff8ff3052f13f00347145f10011f3546
  | 6, 80 => 0x804ff5f0f235000154ff2ff3f29f51f0fff30302547233077f52f4f4ff032ff7f36f3200200f553f213f3015f094f03573f36335013f3302f06100f123000f55
  | 6, 81 => 0x57771112ff0503750625ff531f1227f3f0ff0f83f30ffff3f70070f7fff1ff4ffffff60f0230f5305855238405f02540ff62f203063503f33f85ff2f06061
  | 6, 82 => 0xf2f3f003f23f6f3031102324fff221622f1fff23153ff39f0216200f0f7207300442720134238050233541051006150005007534730fff280f5f605813f1666f
  | 6, 83 => 0x4f562f3f640f25fff0612712534013205260006f0130f602f50338243565003173130fff8711f0f8ffff0ffff2ff0f3f66030500500155f263f0572f248ff220
  | 6, 84 => 0x701f9ff30503320603032f44fff705f0f0322030071223250000080f02f150ff2201f1fff6870101ff0117f3f80fff1ff0f9ff4009ffff031507ff1139f5f01f
  | 6, 85 => 0xff3f701f0ffff7572500311002021f11ffff254ff2f0202423f35f03f550f5243ff7502f580831190f1156056208110f0f23f5ff12f603000120213057187376
  | 6, 86 => 0x4f2f7ffff520fff231f03105fff8500ff3ff21f01002298017f2035f95132530232515010f2371151f7ffffff2533f39f10f0f454ff313ff0f0971fff5f535f7
  | 6, 87 => 0x30f630f12f003ff0f2fff4fff0f0f532203507f1ffff81280302ff01f310f2f5f0023f3ff0ff0f6035020493ff702f2131370ff1f265185f50003330385536ff
  | 6, 88 => 0x3ff527ffff4525501fff7ff52053fff122f800f50ff061f3010055f122350150502230005485135f500030f2250100f300814f501ffffffff0fffff420fff452
  | 6, 89 => 0xf0f03205347f2ff0f03f9f101ff0258047070f060f287017ff03ff5112255003ff7f2325f0f2f00ff2f011fff2f7f0f02f1fffff155111135130003f2205ff35
  | 6, 90 => 0x31ff0f0fffff7ff5f20533330002022002366214ff709f0ff3f0f3f0ff5f30003f635401244770037f10f00f0f0175024010ff7f2032000500ff00f33f5f0fff
  | 6, 91 => 0x2f07f0ff3003273ffff2f3f372f4fff2332f225f3801ff34320f3001f033225200037300f01fff6ffff320703105525f0f24f653037f77fff09fffffff4f0f0f
  | 6, 92 => 0x20f8912010f6203f301ff100ff0310501ff26fff6f33453fff0100ff203f5ff5f20f010305300020f5f1f1f3f45f190410f1f8f033ff5f0fffff3035532fff0f
  | 6, 93 => 0x352f8ff3510f4045123253712552310ff3f00f5ff2233f356fff0ff5f2f10305f6fff0044510026fff5f006383f11053f05fff221475450500f0031f264630ff
  | 6, 94 => 0x722003032432050f13f55ff025137f0003ff323824492003f1333ff13f052ff0f2f926f0f043fff1210f55000610f470f9231ff22f5f00f2ffff1f60ffff2f63
  | 6, 95 => 0x2707ff0fff6011f52f227f05f70033243f13f21003320057155f233f39fffff3f4f232ff15101002302715202f807f5600502fff04f745f001002f2f35f4533f
  | 6, 96 => 0xfff3f35fff22f0300521333031fff3000f40f1f5f3322701015358302301307244f5f2ff7ffff1070f7130f0f7ff630743021ff4f5f30f0324031107500001f0
  | 6, 97 => 0x70ff455fffff30fffff3f3f1f2f44322402ffffff150fffffff4200f22f10265f160f204241115ff00003fff0f001228001f31ff02f2ff75010f05ff5f052050
  | 6, 98 => 0x80821155f768ff7ff2f05f085332f6fff5ffff5f585ff337f177f0f3503f354f175f210fff91ffff0f2ff0f1550007ff4f0f7040311000555f20ff4532528f75
  | 6, 99 => 0xfff5f0f600f300f202522f5235743050f605300506202f1792030f31004700f351330523605507310278604f100420262622ff0ffff13f4000f26f21512ff470
  | 6, 100 => 0x3583237ff3f2fff3f3520f2f0ff4f0630114f53088f3373f15517ff2f23ff240f09f1f0f7f09ff26754103ff0656207203371263005501ff01f9052ffff5f33
  | 6, 101 => 0x83f3003530fff6016ff5f0f65f21fff143f5f390ff572f0013720254110507103ff370ff1077f04f3131f05f25f5f002f2f532f8ff2ffff2f4047fff12420870
  | 6, 102 => 0xffff0f22370f18682f0405f500f03200727201f3f120170f30f19f0900f03f7500f2f00223ffff010320f0f08ff05fffff3055035f0ffff07210f5ff0f70f709
  | 6, 103 => 0x2f0002508f010500f6000013f7f2051ff0ff2f18071f1f3f50730f401ff335f3f44ff000ff0f55f13ff62ffff21f508ffff030f9f3351f2050005011087f2048
  | 6, 104 => 0xf272003545003005000073ffff06fff4f3f0f009031ff6f06f85003121f0223f3f65700ff2ff82ff0f509ffff001ffff0220f7001f634033f03f0fffffff0ff0
  | 6, 105 => 0x3f00ff0f00403ff023f9ff37f3f2705ff07430050777350f20353901511f753fff1330005205f02905004065029520340ff025563f7f530ffff2f5f0ff82ff19
  | 6, 106 => 0x7232431f253021900348f3f53f615f51f3100f03f4fff579f52202133310610f0872603ff00f00f1ff430822392f3204f00ff304fff02230003ff1f01101001f
  | 6, 107 => 0xf5f3f32001f43f5532f7035300625625522062506f2006ff543ff320202f51407539301f0f47ff057035875100767606351fffff9ff3fff41fff21f2f550f30f
  | 6, 108 => 0xf232220f72030f47ffffff0f0ff0003f108ff05f323ffff521290f2f010ffff030f3f3f0f1ff55f00831025f00f44068030120693f7215583233235600212ff1
  | 6, 109 => 0xff451f77f09223f250653207334610f7130ff51320f1500422355ff20f00230463252718320f5f35f5222323053f050332ff51f21ff33f3fffff23fff703f0f7
  | 6, 110 => 0x351003153304227ff70754113ff05ff09f067321ff5007f0f20f03ffff6007125506f60132ff86f9001f7003ff502ffff30ff2ff450f8fffff0ff7317f105307
  | 6, 111 => 0xf0321f27307222f02f074f0010f23f260501fff0f23fff052ff30313f05f126f0004f23352f02f50ff7ff2f0135073001420ff5145252510026750711103044
  | 6, 112 => 0x3043f401205f63070130ff0300ff307012f215f2015f345f040ffff0f6ff2ff3333f4f0206043544582603801705f0f2f02640ff13100f4200911ffff103f210
  | 6, 113 => 0x3ff003f3531111ff2392f4ff30f233f00ffff7f1f7f3f0f705418100105f14023552f8f2f43fffff0fff0f0fff0ffff0ff0ff507402f401ff3330f35244f720f
  | 6, 114 => 0x36902f62102f0472020f241743f70030f032ffff20003f5f011372f7141102254402883031051700103f1305505125603f23007f9f12f052f2101250005051ff
  | 6, 115 => 0x2f25108f1200f535f0f0335070ff350105232979284f72fff56f3fff15f3ff13f0201f02030f70563401350072230204f0332555162520ff025020330303000
  | 6, 116 => 0x45fffff0ff75f6037f410800f071f3ff53f272ff355100177933194090160074102333024635626062010035251239530370f3f13002020327f04322740f0535
  | 6, 117 => 0x2214f1f4520f5ff2ffffffff000170ff1f21f0ff0f54ff9fffff5052f022970397640550ff20930218070f5f2f0f000f53312fff2f3133f5f5fffffff1f3ff50
  | 6, 118 => 0x7043ff0ff4f5607737033f345802f3f04ff17ff31f7f0fff35f1f22241700437053f520001330f3f300f715850f02423ff1f206311f50f9007114114f1f75f0f
  | 6, 119 => 0xf20f13ffff705032600430f0f5212fff1ff98f2000f0ff4ffffff854030032012205516401ff11245f8012ff9300043137330ff54ff04f6251f8f4f0f2f3f74f
  | 6, 120 => 0xffff203f031331f5f13fff331f141f3ffff0f3ff32205310fffff2fffff350ffff5ff5f025fff50ffff0007f0ffff0fffffff325f1f031585ff550713f22258f
  | 6, 121 => 0x2707ff235202210220f053146372ff2f33fff2f26f077ff082f802fff7f0372f1f42fff15fff5f3230034244723402fff2ff3f701ff0ff7f000023f0341f02ff
  | 6, 122 => 0xf39150f5571f3f0f5f605ff14334402ff6f1241f00ff877fff3fff0ff1202753ffff8f4f3ff3fff7fff35f503fff4511f342f58f2f573585822f0020ff33ff
  | 6, 123 => 0x23405303031030022f0fff17201155f141ff53ff60006204f8505ff023f2f070223f570ff00f21fff0f0ff1f02254317f65301ff5777ff33402f70ff739335f
  | 6, 124 => 0x4ff1ff63ff3fff57f107f2f05550f4fff6f53f2ff4f3f9ff12ff3f70ffff6fff85035302051253f4f574f1ff0ff3f73050733303797255151452666050501060
  | 6, 125 => 0x324ff3ffff2f3f0f580073ff4f52327fffff7f52fff13701920217000001f60331432638302f0435f3232f0232947091f0f0fff03ffff27f057ff00f75300fff
  | 6, 126 => 0x3330f3200f78fff7503f50f315f0385f1f0f67f0008204320f083140000f356fff06f120ff1ff413f0f00f0f0508231230f1f4f306f391fff70ff4ff5f025f
  | 6, 127 => 0x73607ffff5033fff33170f328ff7fff20330fff0ff0425ff3065005050281f00433f5ffff0f2f300ff00150127005f34ff60334030513500500455f1f52333
  | 6, 128 => 0xf9105f3f111115f73f20ffff23f427f53ff7ff303fff7060f0f0ff2f52f0ffff50f75ffff03ffffff007f310053642ff04332103f1ffffff27ff2f4234ffff55
  | 6, 129 => 0x3259569060350558146212122f7ff02fff0000283702332f904042723011010210220177285225505375603f15175300506ff47203ff4370192f3350530ff27
  | 6, 130 => 0xf8260f82849f02ff330235720043600542020100705059022023722f347130217f20000113770f6ff0f2ff503555ff3ff00f1238ff00102143fff2fff50f0307
  | 6, 131 => 0xff20ffffffff00fff22005534030330306f5ff0ff125ff1f40f17024ff0ff39fff631ff2572105362f5f21ffff3ff3ff0033ff5f7f7f83f2f839253695057205
  | 6, 132 => 0x5f3400ff24f3f0f32ff9f06f3f33f132f83711ffff051fff6fff0ff0025503f32f043f3f30f022f8f9023001024f473103f07f02ff215530ff0124ff50f7f0f0
  | 6, 133 => 0x7f377222403f4155055ff20552036300340229050f3436013f3f008f3ff22f0f5ffff35127f2f152052038333f3600023012051ff71520fff1ff27f0f360ff3f
  | 6, 134 => 0xf4f507f0303fff7fffff057278fff1f3ff7341050201239388255200713539560500911f5f3923ff00ff501669f00173563f56fff220f00f4fff07ff290500ff
  | 6, 135 => 0xff02100322f02436002f7556f05f01325630ff402134f600312110f2070ff252f0f02f594f10f5332f32f001f32246f20000400210f5ff06fff20031255ffff1
  | 6, 136 => 0x1f2850f20f5750f50025f2f21545023219f110f5f06f3f07ff46fff2fff0f0f35f12f0112f4344313f5003ff32f526f7f0050f7ff170ff28ffff5273035060f5
  | 6, 137 => 0x611f80ff0fff569ff650110540007ffff57ff2f1ff8f509065f0f205f1f30510241304fff6051209ff2916153224f523325022fff61f00ff
  | 7, 0 => 0xf750ff3007f0f030ff353f53fffffff5f770505700f0f073f53f0553f75705f005f333ffff733f3007050fffff37ff7330003f07370f5f370050ff550f33555f
  | 7, 1 => 0x5ffff33f35755570777730f07f0ff03f00005fffff5f0f7f5ff35530f0350f0070737f530f353f3700ff0755705f70f5f05335ffff7f3fffff7f755fff07f7f5
  | 7, 2 => 0xf7ff3f00055500fff03ff05505070075753035ff33f0f3f70077533355f0ffff0ff575f7575f7053f30030775077f3f0ff5f5f3ffffff07f005ff5537750f50
  | 7, 3 => 0x7f05f3f75f5f3f3ffffff3f03f03f37505f0f7070055ff550530f3505f03ff50f70577055075773555f7505ff33f0f0733fff7357300f57ff377350f7005f0f
  | 7, 4 => 0x3f700307707f0f75ff7f5fffffff5f0f7f0f7f073f7f05005737555335fff35fff0f3f07ff335f35f5f3503ffff70fffff5f005350f330357f507f3ff0ffffff
  | 7, 5 => 0xf0f7f353f3753333537035ffff0ff5f0f5f005055f55ff305f337fff3f7ff330f373f33003ff05ff7305f000f73337f50f057007ff7057f553073f003f577f7
  | 7, 6 => 0x3303ff50007f730070337333f5f05f730050530073030030770057735f503533ff33f50f7ffff3f35f703f35005f055500f53757f35ff7f5377073f73ff00ff5
  | 7, 7 => 0xff05f3330ff300530300303357370f053f00fff53ff33350333533f05ff5f003000f33fff07f55f5f55735335f07f37330070f30f5335f333f5550370505fff
  | 7, 8 => 0x3ff3ffff3757fff353000ffff70330f0f0ff0f7ff0fffff3f50f070553005373f5f707ff0ff77f553f305330753037f3f035f7070057530733f33f0757f3ffff
  | 7, 9 => 0x5f73ff5007fffff500075f530575ff5f3ff035770777f5f07ffff5f3f730303f0753ffff5f7ff73337503730f5f0350ff50fff00fff03707ff700075fff55ff
  | 7, 10 => 0x350f0057773500055370350375375530370377f737f075ff3073053555300777703f7370ffff755557ff73f355373f55ff37033f700050757f37f5f7f50f503f
  | 7, 11 => 0xf07007053ff5ff7ffffff0303f0f35f737ff7005505f7ff5f030055705337505f3373f737f3f707f5f50fff7507353330f7570fff00533f3530f553770573035
  | 7, 12 => 0xf03fff00337f0ff37357035ff5530ff0f55f00333f330ff30733f5f355730f3f05ff530577757f0775f553ff000ff0f0f7fff3ff0f3070f0370f03ff7f0f5ff5
  | 7, 13 => 0xf3003f37ff57ff55ff5fff7f5753505f5ff537503f5530705f00ff755373735ff3f770007073373075550535700305035707505030fffff35fffff7573f30f50
  | 7, 14 => 0xf7f0f00ffff7300305f30000305705505350753f5f05003f0f33f3f7573f370f3505005573fffff553f70557753770330737f3770057f307ff007f30f5ff7570
  | 7, 15 => 0xff0f00037ff50055f0577f05550377f5000ff57ffff733f53303073357030073030f0030003f50577f750ff3fff075370f7733f35373f00f3f3ff3f03030030f
  | 7, 16 => 0x337750535037ff7f0ff7fff030f77ff005f3f0fff0037750f350500f0f7355377f030335003f075050ff57ffff00f7f00f73fff7537070553f05503ff0705f5f
  | 7, 17 => 0x3f555f03033ff3f50fff3f53f735370ff3f00f707fff700fff070f3f30fff35557733333750733577f5ff37f355f33300570f7f050ffff3f733f505053f0f003
  | 7, 18 => 0xff7733f70333555f035f5f07503357050070f30003005773f3733735750077f5703f3f00f3f50f0ff5f503ff0f3f3777fff5ff0ff330fff0ff7f55353f373057
  | 7, 19 => 0xf7035fffff0077f37507555303fff5ff5f5f03555337500357055003f0f0ffffff3f33f535fff5333553373755333007f50737f33f03f0ff7f7ff03050530303
  | 7, 20 => 0x333703f0f0303f703f307003f5700755735ff730f3ff3f3f35ff3f705ff005335300373070f0505fff3f0f7f3f0ff557f3775555337705307f5770003000737f
  | 7, 21 => 0xfff070f0f035fff53f3ffff5f3305f0f0ff3700f5fff303f35f50ff3f0000057f733f000500ff05fff5ff053f530073550f7737530330f53753f705557f35ff5
  | 7, 22 => 0x755570005350350773073f505373f55035f05ff0f3fff7707f0350f07f3f5505f55ff0373fff377ff7f03f03ff0f530fffff707f000f0ff55fff0f77777f7ff7
  | 7, 23 => 0x335ff00350fff30570700f
  | _, _ => 0

def terminalHints : Compact.CutIndex := ⟨terminalHintsBuckets,terminalHintsSlots,terminalHintsShift,terminalHintsRules⟩

def swap0x2 : Switch := ⟨3, 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 0x50505050505050505050505050505050⟩
def swap3x4 : Switch := ⟨8, 0xff000000ff000000ff000000ff00, 0xff000000ff000000ff000000ff0000⟩
def swap0x4 : Switch := ⟨15, 0xaaaa0000aaaa0000aaaa0000aaaa, 0x55550000555500005555000055550000⟩
def swap1x5 : Switch := ⟨30, 0xcccccccc00000000cccccccc, 0x33333333000000003333333300000000⟩
def swap2x3 : Switch := ⟨4, 0xf000f000f000f000f000f000f000f0, 0xf000f000f000f000f000f000f000f00⟩
def swap0x3 : Switch := ⟨7, 0xaa00aa00aa00aa00aa00aa00aa00aa, 0x55005500550055005500550055005500⟩
def swap2x4 : Switch := ⟨12, 0xf0f00000f0f00000f0f00000f0f0, 0xf0f00000f0f00000f0f00000f0f0000⟩

def switchPool : List (List Switch) := [[swap0x2, swap3x4], [swap0x2], [swap0x4, swap1x5, swap2x3], [swap0x3, swap1x5, swap2x4, swap3x4], [swap0x4, swap1x5, swap2x3, swap3x4], [swap0x3, swap1x5, swap2x4], [swap3x4], []]
def switches (i : ℕ) : List Switch := switchPool.getD i []

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem valid (j : ℕ) : ∀ s ∈ switches j, s.Valid := by
  intro s hs
  by_cases inRange : j < switchPool.length
  · have actual : switchPool[j] ∈ switchPool := List.getElem_mem inRange
    have checked : (switchPool.all fun xs => xs.all fun q =>
        @decide q.Valid (by unfold Switch.Valid; infer_instance)) = true := by decide +kernel
    rw [switches, List.getD_eq_getElem _ _ inRange] at hs
    letI : Decidable s.Valid := by unfold Switch.Valid; infer_instance
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked _ actual) s hs)
  · rw [switches, List.getD_eq_default _ _ (by omega)] at hs
    simp at hs

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem fixed (j : ℕ) : reindex (switches j) target = target := by
  by_cases inRange : j < switchPool.length
  · have checked : (switchPool.all fun moves => decide (reindex moves target = target)) = true := by decide +kernel
    rw [switches,List.getD_eq_getElem _ _ inRange]
    exact of_decide_eq_true (List.all_eq_true.mp checked _ (List.getElem_mem inRange))
  · rw [switches, List.getD_eq_default _ _ (by omega)]
    rfl

def salt : ℕ := 0xbf58476d1ce4e5b9

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
def rules : List (SixRules.Rule target) := [
  SixRules.knownRule target 0 false LayerSeed0.target 7
    [0x0, 0x44444444444444444444444444444444, 0x50505050505050505050505050505050, 0x55005500550055005500550055005500, 0x55550000555500005555000055550000, 0x55555555000000005555555500000000]
    [0x0, 0x44444444444444444444444444444444, 0x50505050505050505050505050505050, 0x55005500550055005500550055005500, 0x55550000555500005555000055550000, 0x55555555000000005555555500000000, 0x40404040404040404040404040404040, 0x4040404040404040404040404040404, 0x10101010101010101010101010101010, 0x54545454545454545454545454545454, 0x44004400440044004400440044004400, 0x440044004400440044004400440044, 0x11001100110011001100110011001100, 0x55445544554455445544554455445544, 0x44440000444400004444000044440000, 0x4444000044440000444400004444, 0x11110000111100001111000011110000, 0x55554444555544445555444455554444, 0x44444444000000004444444400000000, 0x444444440000000044444444, 0x11111111000000001111111100000000, 0x55555555444444445555555544444444, 0x50005000500050005000500050005000, 0x500050005000500050005000500050, 0x5000500050005000500050005000500, 0x55505550555055505550555055505550, 0x50500000505000005050000050500000, 0x5050000050500000505000005050, 0x5050000050500000505000005050000, 0x55555050555550505555505055555050, 0x50505050000000005050505000000000, 0x505050500000000050505050, 0x5050505000000000505050500000000, 0x55555555505050505555555550505050, 0x55000000550000005500000055000000, 0x5500000055000000550000005500, 0x550000005500000055000000550000, 0x55555500555555005555550055555500, 0x55005500000000005500550000000000, 0x550055000000000055005500, 0x550055000000000055005500000000, 0x55555555550055005555555555005500, 0x55550000000000005555000000000000, 0x555500000000000055550000, 0x5555000000000000555500000000, 0x55555555555500005555555555550000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LayerSeed0.fullBound,
  SixRules.knownRule target 0 true ExampleSix.target 6
    [0x0, 0x88888888888888888888888888888888, 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00aa00aa00aa00aa00, 0xaaaa0000aaaa0000aaaa0000aaaa0000, 0xaaaaaaaa00000000aaaaaaaa00000000]
    [0x0, 0x88888888888888888888888888888888, 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00aa00aa00aa00aa00, 0xaaaa0000aaaa0000aaaa0000aaaa0000, 0xaaaaaaaa00000000aaaaaaaa00000000, 0x80808080808080808080808080808080, 0x8080808080808080808080808080808, 0x20202020202020202020202020202020, 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, 0x88008800880088008800880088008800, 0x880088008800880088008800880088, 0x22002200220022002200220022002200, 0xaa88aa88aa88aa88aa88aa88aa88aa88, 0x88880000888800008888000088880000, 0x8888000088880000888800008888, 0x22220000222200002222000022220000, 0xaaaa8888aaaa8888aaaa8888aaaa8888, 0x88888888000000008888888800000000, 0x888888880000000088888888, 0x22222222000000002222222200000000, 0xaaaaaaaa88888888aaaaaaaa88888888, 0xa000a000a000a000a000a000a000a000, 0xa000a000a000a000a000a000a000a0, 0xa000a000a000a000a000a000a000a00, 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0, 0xa0a00000a0a00000a0a00000a0a00000, 0xa0a00000a0a00000a0a00000a0a0, 0xa0a00000a0a00000a0a00000a0a0000, 0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0, 0xa0a0a0a000000000a0a0a0a000000000, 0xa0a0a0a000000000a0a0a0a0, 0xa0a0a0a000000000a0a0a0a00000000, 0xaaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0, 0xaa000000aa000000aa000000aa000000, 0xaa000000aa000000aa000000aa00, 0xaa000000aa000000aa000000aa0000, 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, 0xaa00aa0000000000aa00aa0000000000, 0xaa00aa0000000000aa00aa00, 0xaa00aa0000000000aa00aa00000000, 0xaaaaaaaaaa00aa00aaaaaaaaaa00aa00, 0xaaaa000000000000aaaa000000000000, 0xaaaa000000000000aaaa0000, 0xaaaa000000000000aaaa00000000, 0xaaaaaaaaaaaa0000aaaaaaaaaaaa0000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ExampleSix.bound,
  SixRules.knownRule target 1 false LeafSeed2.target 6
    [0x0, 0x22222222222222222222222222222222, 0x30303030303030303030303030303030, 0x33003300330033003300330033003300, 0x33330000333300003333000033330000, 0x33333333000000003333333300000000]
    [0x22222222222222222222222222222222, 0x0, 0x20202020202020202020202020202020, 0x2020202020202020202020202020202, 0x10101010101010101010101010101010, 0x32323232323232323232323232323232, 0x22002200220022002200220022002200, 0x220022002200220022002200220022, 0x11001100110011001100110011001100, 0x33223322332233223322332233223322, 0x22220000222200002222000022220000, 0x2222000022220000222200002222, 0x11110000111100001111000011110000, 0x33332222333322223333222233332222, 0x22222222000000002222222200000000, 0x222222220000000022222222, 0x11111111000000001111111100000000, 0x33333333222222223333333322222222, 0x30303030303030303030303030303030, 0x33003300330033003300330033003300, 0x33330000333300003333000033330000, 0x33333333000000003333333300000000, 0x30003000300030003000300030003000, 0x300030003000300030003000300030, 0x3000300030003000300030003000300, 0x33303330333033303330333033303330, 0x30300000303000003030000030300000, 0x3030000030300000303000003030, 0x3030000030300000303000003030000, 0x33333030333330303333303033333030, 0x30303030000000003030303000000000, 0x303030300000000030303030, 0x3030303000000000303030300000000, 0x33333333303030303333333330303030, 0x33000000330000003300000033000000, 0x3300000033000000330000003300, 0x330000003300000033000000330000, 0x33333300333333003333330033333300, 0x33003300000000003300330000000000, 0x330033000000000033003300, 0x330033000000000033003300000000, 0x33333333330033003333333333003300, 0x33330000000000003333000000000000, 0x333300000000000033330000, 0x3333000000000000333300000000, 0x33333333333300003333333333330000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafSeed2.bound,
  SixRules.knownRule target 2 false LeafAliases.wordSeed3 7
    [0x0, 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 0xf000f000f000f000f000f000f000f00, 0xf0f00000f0f00000f0f00000f0f0000, 0xf0f0f0f000000000f0f0f0f00000000]
    [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 0x0, 0x8080808080808080808080808080808, 0x2020202020202020202020202020202, 0x4040404040404040404040404040404, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e, 0xa000a000a000a000a000a000a000a00, 0xa000a000a000a000a000a000a000a, 0x5000500050005000500050005000500, 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a, 0xa0a00000a0a00000a0a00000a0a0000, 0xa0a00000a0a00000a0a00000a0a, 0x5050000050500000505000005050000, 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a, 0xa0a0a0a000000000a0a0a0a00000000, 0xa0a0a0a000000000a0a0a0a, 0x5050505000000000505050500000000, 0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 0xc000c000c000c000c000c000c000c00, 0xc000c000c000c000c000c000c000c, 0x3000300030003000300030003000300, 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c, 0xc0c00000c0c00000c0c00000c0c0000, 0xc0c00000c0c00000c0c00000c0c, 0x3030000030300000303000003030000, 0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c, 0xc0c0c0c000000000c0c0c0c00000000, 0xc0c0c0c000000000c0c0c0c, 0x3030303000000000303030300000000, 0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c, 0xf000f000f000f000f000f000f000f00, 0xf0f00000f0f00000f0f00000f0f0000, 0xf0f0f0f000000000f0f0f0f00000000, 0xf0000000f0000000f0000000f000000, 0xf0000000f0000000f0000000f00, 0xf0000000f0000000f0000000f0000, 0xf0f0f000f0f0f000f0f0f000f0f0f00, 0xf000f00000000000f000f0000000000, 0xf000f00000000000f000f00, 0xf000f00000000000f000f00000000, 0xf0f0f0f0f000f000f0f0f0f0f000f00, 0xf0f0000000000000f0f000000000000, 0xf0f0000000000000f0f0000, 0xf0f0000000000000f0f00000000, 0xf0f0f0f0f0f00000f0f0f0f0f0f0000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafAliases.Seed3,
  SixRules.knownRule target 2 true LeafAliases.wordSeed4 6
    [0x0, 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0, 0xf000f000f000f000f000f000f000f000, 0xf0f00000f0f00000f0f00000f0f00000, 0xf0f0f0f000000000f0f0f0f000000000]
    [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0, 0x0, 0x80808080808080808080808080808080, 0x20202020202020202020202020202020, 0x40404040404040404040404040404040, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, 0xa000a000a000a000a000a000a000a000, 0xa000a000a000a000a000a000a000a0, 0x50005000500050005000500050005000, 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0, 0xa0a00000a0a00000a0a00000a0a00000, 0xa0a00000a0a00000a0a00000a0a0, 0x50500000505000005050000050500000, 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0, 0xa0a0a0a000000000a0a0a0a000000000, 0xa0a0a0a000000000a0a0a0a0, 0x50505050000000005050505000000000, 0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0, 0xc000c000c000c000c000c000c000c000, 0xc000c000c000c000c000c000c000c0, 0x30003000300030003000300030003000, 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0, 0xc0c00000c0c00000c0c00000c0c00000, 0xc0c00000c0c00000c0c00000c0c0, 0x30300000303000003030000030300000, 0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0, 0xc0c0c0c000000000c0c0c0c000000000, 0xc0c0c0c000000000c0c0c0c0, 0x30303030000000003030303000000000, 0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0, 0xf000f000f000f000f000f000f000f000, 0xf0f00000f0f00000f0f00000f0f00000, 0xf0f0f0f000000000f0f0f0f000000000, 0xf0000000f0000000f0000000f0000000, 0xf0000000f0000000f0000000f000, 0xf0000000f0000000f0000000f00000, 0xf0f0f000f0f0f000f0f0f000f0f0f000, 0xf000f00000000000f000f00000000000, 0xf000f00000000000f000f000, 0xf000f00000000000f000f000000000, 0xf0f0f0f0f000f000f0f0f0f0f000f000, 0xf0f0000000000000f0f0000000000000, 0xf0f0000000000000f0f00000, 0xf0f0000000000000f0f000000000, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafAliases.Seed4,
  SixRules.knownRule target 3 false LeafAliases.wordSeed5 7
    [0x0, 0xaa00aa00aa00aa00aa00aa00aa00aa, 0xcc00cc00cc00cc00cc00cc00cc00cc, 0xf000f000f000f000f000f000f000f0, 0xff000000ff000000ff000000ff0000, 0xff00ff0000000000ff00ff00000000]
    [0xaa00aa00aa00aa00aa00aa00aa00aa, 0x0, 0x880088008800880088008800880088, 0x220022002200220022002200220022, 0x440044004400440044004400440044, 0xee00ee00ee00ee00ee00ee00ee00ee, 0xa000a000a000a000a000a000a000a0, 0xa000a000a000a000a000a000a000a, 0x500050005000500050005000500050, 0xfa00fa00fa00fa00fa00fa00fa00fa, 0xaa000000aa000000aa000000aa0000, 0xaa000000aa000000aa000000aa, 0x550000005500000055000000550000, 0xff00aa00ff00aa00ff00aa00ff00aa, 0xaa00aa0000000000aa00aa00000000, 0xaa00aa0000000000aa00aa, 0x550055000000000055005500000000, 0xff00ff00aa00aa00ff00ff00aa00aa, 0xcc00cc00cc00cc00cc00cc00cc00cc, 0xc000c000c000c000c000c000c000c0, 0xc000c000c000c000c000c000c000c, 0x300030003000300030003000300030, 0xfc00fc00fc00fc00fc00fc00fc00fc, 0xcc000000cc000000cc000000cc0000, 0xcc000000cc000000cc000000cc, 0x330000003300000033000000330000, 0xff00cc00ff00cc00ff00cc00ff00cc, 0xcc00cc0000000000cc00cc00000000, 0xcc00cc0000000000cc00cc, 0x330033000000000033003300000000, 0xff00ff00cc00cc00ff00ff00cc00cc, 0xf000f000f000f000f000f000f000f0, 0xf0000000f0000000f0000000f00000, 0xf0000000f0000000f0000000f0, 0xf0000000f0000000f0000000f0000, 0xff00f000ff00f000ff00f000ff00f0, 0xf000f00000000000f000f000000000, 0xf000f00000000000f000f0, 0xf000f00000000000f000f00000000, 0xff00ff00f000f000ff00ff00f000f0, 0xff000000ff000000ff000000ff0000, 0xff00ff0000000000ff00ff00000000, 0xff00000000000000ff000000000000, 0xff00000000000000ff0000, 0xff00000000000000ff00000000, 0xff00ff00ff000000ff00ff00ff0000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafAliases.Seed5,
  SixRules.knownRule target 3 true LeafAliases.wordSeed6 6
    [0x0, 0xaa00aa00aa00aa00aa00aa00aa00aa00, 0xcc00cc00cc00cc00cc00cc00cc00cc00, 0xf000f000f000f000f000f000f000f000, 0xff000000ff000000ff000000ff000000, 0xff00ff0000000000ff00ff0000000000]
    [0xaa00aa00aa00aa00aa00aa00aa00aa00, 0x0, 0x88008800880088008800880088008800, 0x22002200220022002200220022002200, 0x44004400440044004400440044004400, 0xee00ee00ee00ee00ee00ee00ee00ee00, 0xa000a000a000a000a000a000a000a000, 0xa000a000a000a000a000a000a000a00, 0x50005000500050005000500050005000, 0xfa00fa00fa00fa00fa00fa00fa00fa00, 0xaa000000aa000000aa000000aa000000, 0xaa000000aa000000aa000000aa00, 0x55000000550000005500000055000000, 0xff00aa00ff00aa00ff00aa00ff00aa00, 0xaa00aa0000000000aa00aa0000000000, 0xaa00aa0000000000aa00aa00, 0x55005500000000005500550000000000, 0xff00ff00aa00aa00ff00ff00aa00aa00, 0xcc00cc00cc00cc00cc00cc00cc00cc00, 0xc000c000c000c000c000c000c000c000, 0xc000c000c000c000c000c000c000c00, 0x30003000300030003000300030003000, 0xfc00fc00fc00fc00fc00fc00fc00fc00, 0xcc000000cc000000cc000000cc000000, 0xcc000000cc000000cc000000cc00, 0x33000000330000003300000033000000, 0xff00cc00ff00cc00ff00cc00ff00cc00, 0xcc00cc0000000000cc00cc0000000000, 0xcc00cc0000000000cc00cc00, 0x33003300000000003300330000000000, 0xff00ff00cc00cc00ff00ff00cc00cc00, 0xf000f000f000f000f000f000f000f000, 0xf0000000f0000000f0000000f0000000, 0xf0000000f0000000f0000000f000, 0xf0000000f0000000f0000000f000000, 0xff00f000ff00f000ff00f000ff00f000, 0xf000f00000000000f000f00000000000, 0xf000f00000000000f000f000, 0xf000f00000000000f000f0000000000, 0xff00ff00f000f000ff00ff00f000f000, 0xff000000ff000000ff000000ff000000, 0xff00ff0000000000ff00ff0000000000, 0xff00000000000000ff00000000000000, 0xff00000000000000ff000000, 0xff00000000000000ff0000000000, 0xff00ff00ff000000ff00ff00ff000000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafAliases.Seed6,
  SixRules.knownRule target 4 false LeafAliases.wordSeed5 7
    [0x0, 0xaaaa0000aaaa0000aaaa0000aaaa, 0xcccc0000cccc0000cccc0000cccc, 0xf0f00000f0f00000f0f00000f0f0, 0xff000000ff000000ff000000ff00, 0xffff000000000000ffff00000000]
    [0xaaaa0000aaaa0000aaaa0000aaaa, 0x0, 0x8888000088880000888800008888, 0x2222000022220000222200002222, 0x4444000044440000444400004444, 0xeeee0000eeee0000eeee0000eeee, 0xa0a00000a0a00000a0a00000a0a0, 0xa0a00000a0a00000a0a00000a0a, 0x5050000050500000505000005050, 0xfafa0000fafa0000fafa0000fafa, 0xaa000000aa000000aa000000aa00, 0xaa000000aa000000aa000000aa, 0x5500000055000000550000005500, 0xffaa0000ffaa0000ffaa0000ffaa, 0xaaaa000000000000aaaa00000000, 0xaaaa000000000000aaaa, 0x5555000000000000555500000000, 0xffff0000aaaa0000ffff0000aaaa, 0xcccc0000cccc0000cccc0000cccc, 0xc0c00000c0c00000c0c00000c0c0, 0xc0c00000c0c00000c0c00000c0c, 0x3030000030300000303000003030, 0xfcfc0000fcfc0000fcfc0000fcfc, 0xcc000000cc000000cc000000cc00, 0xcc000000cc000000cc000000cc, 0x3300000033000000330000003300, 0xffcc0000ffcc0000ffcc0000ffcc, 0xcccc000000000000cccc00000000, 0xcccc000000000000cccc, 0x3333000000000000333300000000, 0xffff0000cccc0000ffff0000cccc, 0xf0f00000f0f00000f0f00000f0f0, 0xf0000000f0000000f0000000f000, 0xf0000000f0000000f0000000f0, 0xf0000000f0000000f0000000f00, 0xfff00000fff00000fff00000fff0, 0xf0f0000000000000f0f000000000, 0xf0f0000000000000f0f0, 0xf0f0000000000000f0f00000000, 0xffff0000f0f00000ffff0000f0f0, 0xff000000ff000000ff000000ff00, 0xff00000000000000ff0000000000, 0xff00000000000000ff00, 0xff00000000000000ff00000000, 0xffff0000ff000000ffff0000ff00, 0xffff000000000000ffff00000000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafAliases.Seed5,
  SixRules.knownRule target 4 true LeafAliases.wordSeed6 6
    [0x0, 0xaaaa0000aaaa0000aaaa0000aaaa0000, 0xcccc0000cccc0000cccc0000cccc0000, 0xf0f00000f0f00000f0f00000f0f00000, 0xff000000ff000000ff000000ff000000, 0xffff000000000000ffff000000000000]
    [0xaaaa0000aaaa0000aaaa0000aaaa0000, 0x0, 0x88880000888800008888000088880000, 0x22220000222200002222000022220000, 0x44440000444400004444000044440000, 0xeeee0000eeee0000eeee0000eeee0000, 0xa0a00000a0a00000a0a00000a0a00000, 0xa0a00000a0a00000a0a00000a0a0000, 0x50500000505000005050000050500000, 0xfafa0000fafa0000fafa0000fafa0000, 0xaa000000aa000000aa000000aa000000, 0xaa000000aa000000aa000000aa0000, 0x55000000550000005500000055000000, 0xffaa0000ffaa0000ffaa0000ffaa0000, 0xaaaa000000000000aaaa000000000000, 0xaaaa000000000000aaaa0000, 0x55550000000000005555000000000000, 0xffff0000aaaa0000ffff0000aaaa0000, 0xcccc0000cccc0000cccc0000cccc0000, 0xc0c00000c0c00000c0c00000c0c00000, 0xc0c00000c0c00000c0c00000c0c0000, 0x30300000303000003030000030300000, 0xfcfc0000fcfc0000fcfc0000fcfc0000, 0xcc000000cc000000cc000000cc000000, 0xcc000000cc000000cc000000cc0000, 0x33000000330000003300000033000000, 0xffcc0000ffcc0000ffcc0000ffcc0000, 0xcccc000000000000cccc000000000000, 0xcccc000000000000cccc0000, 0x33330000000000003333000000000000, 0xffff0000cccc0000ffff0000cccc0000, 0xf0f00000f0f00000f0f00000f0f00000, 0xf0000000f0000000f0000000f0000000, 0xf0000000f0000000f0000000f00000, 0xf0000000f0000000f0000000f000000, 0xfff00000fff00000fff00000fff00000, 0xf0f0000000000000f0f0000000000000, 0xf0f0000000000000f0f00000, 0xf0f0000000000000f0f000000000000, 0xffff0000f0f00000ffff0000f0f00000, 0xff000000ff000000ff000000ff000000, 0xff00000000000000ff00000000000000, 0xff00000000000000ff000000, 0xff00000000000000ff000000000000, 0xffff0000ff000000ffff0000ff000000, 0xffff000000000000ffff000000000000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafAliases.Seed6,
  SixRules.knownRule target 5 false LeafAliases.wordSeed7 6
    [0x0, 0xaaaaaaaa00000000aaaaaaaa, 0xcccccccc00000000cccccccc, 0xf0f0f0f000000000f0f0f0f0, 0xff00ff0000000000ff00ff00, 0xffff000000000000ffff0000]
    [0xaaaaaaaa00000000aaaaaaaa, 0x0, 0x888888880000000088888888, 0x222222220000000022222222, 0x444444440000000044444444, 0xeeeeeeee00000000eeeeeeee, 0xa0a0a0a000000000a0a0a0a0, 0xa0a0a0a000000000a0a0a0a, 0x505050500000000050505050, 0xfafafafa00000000fafafafa, 0xaa00aa0000000000aa00aa00, 0xaa00aa0000000000aa00aa, 0x550055000000000055005500, 0xffaaffaa00000000ffaaffaa, 0xaaaa000000000000aaaa0000, 0xaaaa000000000000aaaa, 0x555500000000000055550000, 0xffffaaaa00000000ffffaaaa, 0xcccccccc00000000cccccccc, 0xc0c0c0c000000000c0c0c0c0, 0xc0c0c0c000000000c0c0c0c, 0x303030300000000030303030, 0xfcfcfcfc00000000fcfcfcfc, 0xcc00cc0000000000cc00cc00, 0xcc00cc0000000000cc00cc, 0x330033000000000033003300, 0xffccffcc00000000ffccffcc, 0xcccc000000000000cccc0000, 0xcccc000000000000cccc, 0x333300000000000033330000, 0xffffcccc00000000ffffcccc, 0xf0f0f0f000000000f0f0f0f0, 0xf000f00000000000f000f000, 0xf000f00000000000f000f0, 0xf000f00000000000f000f00, 0xfff0fff000000000fff0fff0, 0xf0f0000000000000f0f00000, 0xf0f0000000000000f0f0, 0xf0f0000000000000f0f0000, 0xfffff0f000000000fffff0f0, 0xff00ff0000000000ff00ff00, 0xff00000000000000ff000000, 0xff00000000000000ff00, 0xff00000000000000ff0000, 0xffffff0000000000ffffff00, 0xffff000000000000ffff0000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafAliases.Seed7
]

def cut : ℕ → List W → Bool := Compact.reject target rules terminalHints salt
def locate : ℕ → List W → ℕ × ℕ := Compact.lookup table poolHints salt
def check : ℕ → ℕ → Bool := Compact.check table target negative startMask locate switches cut

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at0 : span (check 4) 4 0 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at4 : span (check 4) 3 4 = true := by apply block3 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer4 : span (check 4) 7 0 = true := span_join (page4at0) (page4at4)
end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at0 : span (check 5) 4 0 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at4 : span (check 5) 4 4 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at8 : span (check 5) 4 8 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at12 : span (check 5) 4 12 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at16 : span (check 5) 4 16 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at20 : span (check 5) 4 20 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at24 : span (check 5) 4 24 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at28 : span (check 5) 4 28 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at32 : span (check 5) 4 32 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at36 : span (check 5) 4 36 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at40 : span (check 5) 2 40 = true := by apply block2 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer5 : span (check 5) 42 0 = true := span_join (span_join (span_join (span_join (page5at0) (page5at4)) (page5at8)) (span_join (span_join (page5at12) (page5at16)) (page5at20))) (span_join (span_join (span_join (page5at24) (page5at28)) (page5at32)) (span_join (page5at36) (page5at40)))
end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at0 : span (check 6) 4 0 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at4 : span (check 6) 4 4 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at8 : span (check 6) 4 8 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at12 : span (check 6) 4 12 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at16 : span (check 6) 4 16 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at20 : span (check 6) 4 20 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at24 : span (check 6) 4 24 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at28 : span (check 6) 4 28 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at32 : span (check 6) 4 32 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at36 : span (check 6) 4 36 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at40 : span (check 6) 4 40 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at44 : span (check 6) 4 44 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at48 : span (check 6) 4 48 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at52 : span (check 6) 4 52 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at56 : span (check 6) 4 56 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at60 : span (check 6) 4 60 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at64 : span (check 6) 4 64 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at68 : span (check 6) 4 68 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at72 : span (check 6) 4 72 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at76 : span (check 6) 4 76 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at80 : span (check 6) 4 80 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at84 : span (check 6) 4 84 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at88 : span (check 6) 4 88 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at92 : span (check 6) 4 92 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at96 : span (check 6) 4 96 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at100 : span (check 6) 4 100 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at104 : span (check 6) 4 104 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at108 : span (check 6) 4 108 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at112 : span (check 6) 4 112 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at116 : span (check 6) 4 116 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at120 : span (check 6) 2 120 = true := by apply block2 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer6 : span (check 6) 122 0 = true :=
  span_join (f := check 6) (a := 64) (b := 58) (o := 0) (span_join (f := check 6) (a := 32) (b := 32) (o := 0) (span_join (f := check 6) (a := 16) (b := 16) (o := 0) (span_join (f := check 6) (a := 8) (b := 8) (o := 0) (span_join (f := check 6) (a := 4) (b := 4) (o := 0) (page6at0) (page6at4)) (span_join (f := check 6) (a := 4) (b := 4) (o := 8) (page6at8) (page6at12))) (span_join (f := check 6) (a := 8) (b := 8) (o := 16) (span_join (f := check 6) (a := 4) (b := 4) (o := 16) (page6at16) (page6at20)) (span_join (f := check 6) (a := 4) (b := 4) (o := 24) (page6at24) (page6at28)))) (span_join (f := check 6) (a := 16) (b := 16) (o := 32) (span_join (f := check 6) (a := 8) (b := 8) (o := 32) (span_join (f := check 6) (a := 4) (b := 4) (o := 32) (page6at32) (page6at36)) (span_join (f := check 6) (a := 4) (b := 4) (o := 40) (page6at40) (page6at44))) (span_join (f := check 6) (a := 8) (b := 8) (o := 48) (span_join (f := check 6) (a := 4) (b := 4) (o := 48) (page6at48) (page6at52)) (span_join (f := check 6) (a := 4) (b := 4) (o := 56) (page6at56) (page6at60))))) (span_join (f := check 6) (a := 32) (b := 26) (o := 64) (span_join (f := check 6) (a := 16) (b := 16) (o := 64) (span_join (f := check 6) (a := 8) (b := 8) (o := 64) (span_join (f := check 6) (a := 4) (b := 4) (o := 64) (page6at64) (page6at68)) (span_join (f := check 6) (a := 4) (b := 4) (o := 72) (page6at72) (page6at76))) (span_join (f := check 6) (a := 8) (b := 8) (o := 80) (span_join (f := check 6) (a := 4) (b := 4) (o := 80) (page6at80) (page6at84)) (span_join (f := check 6) (a := 4) (b := 4) (o := 88) (page6at88) (page6at92)))) (span_join (f := check 6) (a := 16) (b := 10) (o := 96) (span_join (f := check 6) (a := 8) (b := 8) (o := 96) (span_join (f := check 6) (a := 4) (b := 4) (o := 96) (page6at96) (page6at100)) (span_join (f := check 6) (a := 4) (b := 4) (o := 104) (page6at104) (page6at108))) (span_join (f := check 6) (a := 8) (b := 2) (o := 112) (span_join (f := check 6) (a := 4) (b := 4) (o := 112) (page6at112) (page6at116)) (page6at120))))

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at0 : span (check 7) 4 0 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at4 : span (check 7) 4 4 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at8 : span (check 7) 4 8 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at12 : span (check 7) 4 12 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at16 : span (check 7) 4 16 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at20 : span (check 7) 4 20 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at24 : span (check 7) 4 24 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at28 : span (check 7) 4 28 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at32 : span (check 7) 4 32 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at36 : span (check 7) 4 36 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at40 : span (check 7) 4 40 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at44 : span (check 7) 4 44 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier



namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at48 : span (check 7) 4 48 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at52 : span (check 7) 4 52 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at56 : span (check 7) 4 56 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at60 : span (check 7) 4 60 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at64 : span (check 7) 4 64 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at68 : span (check 7) 4 68 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at72 : span (check 7) 4 72 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at76 : span (check 7) 4 76 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at80 : span (check 7) 4 80 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at84 : span (check 7) 4 84 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at88 : span (check 7) 4 88 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at92 : span (check 7) 4 92 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier



namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at96 : span (check 7) 4 96 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at100 : span (check 7) 4 100 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at104 : span (check 7) 4 104 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at108 : span (check 7) 4 108 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at112 : span (check 7) 4 112 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at116 : span (check 7) 4 116 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at120 : span (check 7) 4 120 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at124 : span (check 7) 4 124 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at128 : span (check 7) 4 128 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at132 : span (check 7) 4 132 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at136 : span (check 7) 4 136 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at140 : span (check 7) 4 140 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier



namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at144 : span (check 7) 4 144 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at148 : span (check 7) 4 148 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at152 : span (check 7) 4 152 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at156 : span (check 7) 4 156 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at160 : span (check 7) 4 160 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at164 : span (check 7) 4 164 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at168 : span (check 7) 4 168 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at172 : span (check 7) 4 172 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at176 : span (check 7) 4 176 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at180 : span (check 7) 4 180 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at184 : span (check 7) 4 184 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at188 : span (check 7) 4 188 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier



namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at192 : span (check 7) 4 192 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at196 : span (check 7) 4 196 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at200 : span (check 7) 4 200 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at204 : span (check 7) 4 204 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at208 : span (check 7) 4 208 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at212 : span (check 7) 4 212 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at216 : span (check 7) 4 216 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at220 : span (check 7) 4 220 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at224 : span (check 7) 4 224 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at228 : span (check 7) 4 228 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at232 : span (check 7) 4 232 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at236 : span (check 7) 4 236 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier



namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at240 : span (check 7) 4 240 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at244 : span (check 7) 4 244 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at248 : span (check 7) 4 248 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at252 : span (check 7) 4 252 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at256 : span (check 7) 4 256 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at260 : span (check 7) 4 260 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at264 : span (check 7) 4 264 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at268 : span (check 7) 4 268 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at272 : span (check 7) 4 272 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at276 : span (check 7) 4 276 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at280 : span (check 7) 4 280 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at284 : span (check 7) 4 284 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier



namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at288 : span (check 7) 4 288 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at292 : span (check 7) 4 292 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at296 : span (check 7) 4 296 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at300 : span (check 7) 4 300 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at304 : span (check 7) 4 304 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at308 : span (check 7) 4 308 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at312 : span (check 7) 4 312 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at316 : span (check 7) 4 316 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at320 : span (check 7) 4 320 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at324 : span (check 7) 4 324 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at328 : span (check 7) 4 328 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at332 : span (check 7) 4 332 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier



namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at336 : span (check 7) 4 336 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at340 : span (check 7) 4 340 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at344 : span (check 7) 4 344 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at348 : span (check 7) 4 348 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at352 : span (check 7) 4 352 = true := by apply block4 <;> decide +kernel

end LeafHint0
end GraphSignedFrontier



namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer7 : span (check 7) 356 0 = true :=
  span_join (f := check 7) (a := 180) (b := 176) (o := 0) (span_join (f := check 7) (a := 92) (b := 88) (o := 0) (span_join (f := check 7) (a := 48) (b := 44) (o := 0) (span_join (f := check 7) (a := 24) (b := 24) (o := 0) (span_join (f := check 7) (a := 12) (b := 12) (o := 0) (span_join (f := check 7) (a := 8) (b := 4) (o := 0) (span_join (f := check 7) (a := 4) (b := 4) (o := 0) (page7at0) (page7at4)) (page7at8)) (span_join (f := check 7) (a := 8) (b := 4) (o := 12) (span_join (f := check 7) (a := 4) (b := 4) (o := 12) (page7at12) (page7at16)) (page7at20))) (span_join (f := check 7) (a := 12) (b := 12) (o := 24) (span_join (f := check 7) (a := 8) (b := 4) (o := 24) (span_join (f := check 7) (a := 4) (b := 4) (o := 24) (page7at24) (page7at28)) (page7at32)) (span_join (f := check 7) (a := 8) (b := 4) (o := 36) (span_join (f := check 7) (a := 4) (b := 4) (o := 36) (page7at36) (page7at40)) (page7at44)))) (span_join (f := check 7) (a := 24) (b := 20) (o := 48) (span_join (f := check 7) (a := 12) (b := 12) (o := 48) (span_join (f := check 7) (a := 8) (b := 4) (o := 48) (span_join (f := check 7) (a := 4) (b := 4) (o := 48) (page7at48) (page7at52)) (page7at56)) (span_join (f := check 7) (a := 8) (b := 4) (o := 60) (span_join (f := check 7) (a := 4) (b := 4) (o := 60) (page7at60) (page7at64)) (page7at68))) (span_join (f := check 7) (a := 12) (b := 8) (o := 72) (span_join (f := check 7) (a := 8) (b := 4) (o := 72) (span_join (f := check 7) (a := 4) (b := 4) (o := 72) (page7at72) (page7at76)) (page7at80)) (span_join (f := check 7) (a := 4) (b := 4) (o := 84) (page7at84) (page7at88))))) (span_join (f := check 7) (a := 44) (b := 44) (o := 92) (span_join (f := check 7) (a := 24) (b := 20) (o := 92) (span_join (f := check 7) (a := 12) (b := 12) (o := 92) (span_join (f := check 7) (a := 8) (b := 4) (o := 92) (span_join (f := check 7) (a := 4) (b := 4) (o := 92) (page7at92) (page7at96)) (page7at100)) (span_join (f := check 7) (a := 8) (b := 4) (o := 104) (span_join (f := check 7) (a := 4) (b := 4) (o := 104) (page7at104) (page7at108)) (page7at112))) (span_join (f := check 7) (a := 12) (b := 8) (o := 116) (span_join (f := check 7) (a := 8) (b := 4) (o := 116) (span_join (f := check 7) (a := 4) (b := 4) (o := 116) (page7at116) (page7at120)) (page7at124)) (span_join (f := check 7) (a := 4) (b := 4) (o := 128) (page7at128) (page7at132)))) (span_join (f := check 7) (a := 24) (b := 20) (o := 136) (span_join (f := check 7) (a := 12) (b := 12) (o := 136) (span_join (f := check 7) (a := 8) (b := 4) (o := 136) (span_join (f := check 7) (a := 4) (b := 4) (o := 136) (page7at136) (page7at140)) (page7at144)) (span_join (f := check 7) (a := 8) (b := 4) (o := 148) (span_join (f := check 7) (a := 4) (b := 4) (o := 148) (page7at148) (page7at152)) (page7at156))) (span_join (f := check 7) (a := 12) (b := 8) (o := 160) (span_join (f := check 7) (a := 8) (b := 4) (o := 160) (span_join (f := check 7) (a := 4) (b := 4) (o := 160) (page7at160) (page7at164)) (page7at168)) (span_join (f := check 7) (a := 4) (b := 4) (o := 172) (page7at172) (page7at176)))))) (span_join (f := check 7) (a := 88) (b := 88) (o := 180) (span_join (f := check 7) (a := 44) (b := 44) (o := 180) (span_join (f := check 7) (a := 24) (b := 20) (o := 180) (span_join (f := check 7) (a := 12) (b := 12) (o := 180) (span_join (f := check 7) (a := 8) (b := 4) (o := 180) (span_join (f := check 7) (a := 4) (b := 4) (o := 180) (page7at180) (page7at184)) (page7at188)) (span_join (f := check 7) (a := 8) (b := 4) (o := 192) (span_join (f := check 7) (a := 4) (b := 4) (o := 192) (page7at192) (page7at196)) (page7at200))) (span_join (f := check 7) (a := 12) (b := 8) (o := 204) (span_join (f := check 7) (a := 8) (b := 4) (o := 204) (span_join (f := check 7) (a := 4) (b := 4) (o := 204) (page7at204) (page7at208)) (page7at212)) (span_join (f := check 7) (a := 4) (b := 4) (o := 216) (page7at216) (page7at220)))) (span_join (f := check 7) (a := 24) (b := 20) (o := 224) (span_join (f := check 7) (a := 12) (b := 12) (o := 224) (span_join (f := check 7) (a := 8) (b := 4) (o := 224) (span_join (f := check 7) (a := 4) (b := 4) (o := 224) (page7at224) (page7at228)) (page7at232)) (span_join (f := check 7) (a := 8) (b := 4) (o := 236) (span_join (f := check 7) (a := 4) (b := 4) (o := 236) (page7at236) (page7at240)) (page7at244))) (span_join (f := check 7) (a := 12) (b := 8) (o := 248) (span_join (f := check 7) (a := 8) (b := 4) (o := 248) (span_join (f := check 7) (a := 4) (b := 4) (o := 248) (page7at248) (page7at252)) (page7at256)) (span_join (f := check 7) (a := 4) (b := 4) (o := 260) (page7at260) (page7at264))))) (span_join (f := check 7) (a := 44) (b := 44) (o := 268) (span_join (f := check 7) (a := 24) (b := 20) (o := 268) (span_join (f := check 7) (a := 12) (b := 12) (o := 268) (span_join (f := check 7) (a := 8) (b := 4) (o := 268) (span_join (f := check 7) (a := 4) (b := 4) (o := 268) (page7at268) (page7at272)) (page7at276)) (span_join (f := check 7) (a := 8) (b := 4) (o := 280) (span_join (f := check 7) (a := 4) (b := 4) (o := 280) (page7at280) (page7at284)) (page7at288))) (span_join (f := check 7) (a := 12) (b := 8) (o := 292) (span_join (f := check 7) (a := 8) (b := 4) (o := 292) (span_join (f := check 7) (a := 4) (b := 4) (o := 292) (page7at292) (page7at296)) (page7at300)) (span_join (f := check 7) (a := 4) (b := 4) (o := 304) (page7at304) (page7at308)))) (span_join (f := check 7) (a := 24) (b := 20) (o := 312) (span_join (f := check 7) (a := 12) (b := 12) (o := 312) (span_join (f := check 7) (a := 8) (b := 4) (o := 312) (span_join (f := check 7) (a := 4) (b := 4) (o := 312) (page7at312) (page7at316)) (page7at320)) (span_join (f := check 7) (a := 8) (b := 4) (o := 324) (span_join (f := check 7) (a := 4) (b := 4) (o := 324) (page7at324) (page7at328)) (page7at332))) (span_join (f := check 7) (a := 12) (b := 8) (o := 336) (span_join (f := check 7) (a := 8) (b := 4) (o := 336) (span_join (f := check 7) (a := 4) (b := 4) (o := 336) (page7at336) (page7at340)) (page7at344)) (span_join (f := check 7) (a := 4) (b := 4) (o := 348) (page7at348) (page7at352))))))

end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page8at0 : span (check 8) 4 0 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page8at4 : span (check 8) 4 4 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page8at8 : span (check 8) 4 8 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page8at12 : span (check 8) 4 12 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page8at16 : span (check 8) 1 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer8 : span (check 8) 17 0 = true := span_join (span_join (span_join (page8at0) (page8at4)) (page8at8)) (span_join (page8at12) (page8at16))
end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page9at0 : span (check 9) 1 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer9 : span (check 9) 1 0 = true := page9at0
end LeafHint0
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint0

set_option maxHeartbeats 0 in
theorem validated (k : ℕ) (hk : k ≤ 9) (i : ℕ) (hi : i < count k) : check k i = true := by
  have e : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
  rcases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [count] at hi
  · simp [count] at hi
  · simp [count] at hi
  · simp [count] at hi
  · exact span_member layer4 i (by omega) (by simpa [count] using hi)
  · exact span_member layer5 i (by omega) (by simpa [count] using hi)
  · exact span_member layer6 i (by omega) (by simpa [count] using hi)
  · exact span_member layer7 i (by omega) (by simpa [count] using hi)
  · exact span_member layer8 i (by omega) (by simpa [count] using hi)
  · exact span_member layer9 i (by omega) (by simpa [count] using hi)

set_option maxHeartbeats 0 in
theorem bound : signedLower target raw 10 :=
  Compact.lower table target positive raw essential negative neg startMask 9
    (by decide +kernel) (by decide +kernel) (by decide +kernel) locate switches valid fixed cut
    (Compact.safe target rules terminalHints salt) validated

end LeafHint0

end GraphSignedFrontier

namespace GraphSignedFrontier

namespace LeafSeed14

def target : W := 0xfffeeca0fffeeca0fffeeca0fffeeca0
def raw : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000]
def negative : List ℕ := [0, 1, 2, 3, 4, 6, 8, 9, 12, 16]

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem positive : target ≠ 0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem unique : raw.Nodup := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem neg : ∀ r ∈ negative, r < 128 ∧ target.getLsbD r = false := by
  intro r hr
  have yes : (negative.all fun j => decide (j < 128 ∧ target.getLsbD j = false)) = true := by decide +kernel
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp yes r hr

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · refine ⟨4,5,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : W) ∨ z.getLsbD 4 = z.getLsbD 5)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨8,10,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xcccccccccccccccccccccccccccccccc : W) ∨ z.getLsbD 8 = z.getLsbD 10)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : W) ∨ z.getLsbD 1 = z.getLsbD 5)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨2,10,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xff00ff00ff00ff00ff00ff00ff00ff00 : W) ∨ z.getLsbD 2 = z.getLsbD 10)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,17,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffff0000ffff0000ffff0000ffff0000 : W) ∨ z.getLsbD 1 = z.getLsbD 17)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd

def dictionary : ℕ → ℕ
  | 0 => 0xccfcccfcaafaaafa0505000000fa00fa5f005f00fcfcfcfceeeeeeeeffa0ffa0fafafafaececececfefecccca0a0a0a0fcfcfcf0eeeeeeaafafaa0a0ccccccccff00cc00eeeeaaaacccccc00afaaafaaffff0000cc00cc00afaeafaef0f0f0f0ccffcc00aaaaaaaa33330000fefeececffffa0a0ff00ff00ccfeccfe00000000
  | 1 => 0x500ff000300ff0000ff00ee00ff00cc00cf00cc33003300cc0ccc0c0f000f0033cc33cc0f0c0f0c003300004c4c4c4c0f00ff000c0cccccf0f0a0a00f005f00b0b0b0b04f004f00a0f0a0f03300ff003030f0f00f0f0000bbff00003fff000033ff000000ffff005f5f000000ff0000fefefefefafaaaaaeeeeececeeeecccc
  | 2 => 0xaeaeaeaeaeaeaaaaaeaaaeaaaafaaaaaaaeeaaaaaaaeaaaeaaaaeeaaaaaaaeaeff00ee00ff00cf00ff005f00ff000000efaaefaaef00ef00dd00dd005500ff00eeaaeeaadf00df00cfcccfcccf00ff00cf00cf00cf00cc00cd00cd00bb00ff0000cc00cc0000ff00af00ff007f007f005f00ff003f00ff000ff00ff00f00cf00
  | 3 => 0xcccc0000aa00aa0055005500aaaa000055550000fffff0f0cceecceeffffaaaaf0f000005050505000f000f0ffff8080ffff00a0fefeaaaafcfcf0f0fcf0fcf05a5a5a5a0000a0a0fafaf0f00a0a0a0a0000f0f0fafa0a0afafa0000a2a2a2a222aa22aaaaaaa0a0eeeeaeae0000cccceceeeceeececcccceaeaaaaaeaaaeaaa
  | 4 => 0xaa88aa88a8a8a8a8a0aaa0aaa0a0aaaaa0a0000088cc88cc88aa88aa8888aaaa8888888888880000808080800fff00000aaa0aaa00ff00aa00ee00ee00cccccc00cc000000aaaaaa00aa00aa00aa000000a000a00088008800220022000f0000000a000a0000fafa0000eeee0000aaaa00008888000000cc000000aa30303030
  | 5 => 0xfffffafaffffeeee0f0f0a0affff8888ffff00ccffff00aa22222222eeee0000eaeaeaeaafafaaaaafaf00000c0c0c0caaffaaaaaaff0000aaeeaaeeaaaafafaaaaaeeeeaaaa8888aaaa0a0aaaaa00aa
  | _ => 0

def packed : ℕ → ℕ → ℕ
  | 2, 0 => 0x30204030201
  | 3, 0 => 0x30208210302082003021f060302101e0302101d0302101c0317101b0b181a190b1817160b0215140b0213120b0211100b0f080e0b080d0c0b080a0908070605
  | 3, 1 => 0x302231003021a1903021716030217100302221003021110
  | 4, 0 => 0xb080633320b311006300b102f062e0b10062d1b0b10062c2b0217101425022208102a020816062502081029060208100628020810062702081006260f08100624081006251b080a0605240003021710
  | 4, 1 => 0xb081006400b081006300b0810063f0b0810063e0b081006260b0810063d0b0810063c0b0810063b0b080d063a0b080d06380b080d06240b083906380b080a06370b080a06360b080a06350b08061b34
  | 4, 2 => 0xb084910060b080710060b08100a0c0b081048060b08100c470b08100c460b081045060b081006440b081006430b0810061b0b0810062e0b081006420b081006370b0810062c0b081006410b08100633
  | 4, 3 => 0xb550810060b54080d060b1710141b0b220810330b08534b100b085210060b081951060b082006500b080e102c0b084f10380b0816061b0b084e10060b084d0a060b084c10060b084b10060b084a1006
  | 4, 4 => 0xb020861100b020860100b020810090b0208105f0b0208105e0b0208105d0b0208105c0b0208105b0b0208105a0b020810590b020810580b020810060b570810060b560810060b0f0819060b0f081006
  | 4, 5 => 0xb0222106c0b0222106b0b026a10060b026910140b020819680b020819670b020821060b020821660b020865100b02080e100b02080e0a0b02080e3a0b02080e640b020863060b020816060b02086206
  | 4, 6 => 0xb022310140b021508060b027208100b021a19140b02710e100b027019060b02704f100b021716140b021710660b021710140b0217106f0b0217106e0b026d20060b022208100b022231100b02221014
  | 4, 7 => 0x78026d10067802102a6c030b02171003021710060302171014030208191003020816060302081006030231100603027710060302100676030210062a0302100675030810061b74020810067302081006
  | 4, 8 => 0x7a78021710780b026d10780b020820780b020879
  | 5, 0 => 0x20810061425020810060524020810062446000302081006000b02171014000b02220810000b02080e10000b02081606000b0208105f000b0f081006000b084b1006000b0810061b000b0810062c000b08100633000b0810063c000208100627
  | 5, 1 => 0xb08107f062c0b08100a063a0b08100a06380b08100a06240b0810067c500b0810067e7d0b081006141b0b0810067d380b0810063a470b0810063a460b08100638750b08100638470b08100638460b08100624470b0810062446020810067c7b
  | 5, 2 => 0xb020810068a0b02081006350b02081006890b02081006880b02081006870b02081006860b02081006850b02081006840b020810066e0b02081006830b02081006820b02081006810b5408100a060b54081006470b54081006460b084b100680
  | 5, 3 => 0xb02081006270b02081006670b02081006940b02081006930b020810063c0b02081006920b02081006240b020810061c0b02081006910b02081006900b02081006470b020810068f0b020810068e0b020810068d0b020810068c0b020810068b
  | 5, 4 => 0xb02081006a20b02081006a10b02081006a00b020810067c0b020810069f0b020810069e0b020810069d0b020810069c0b02081006140b020810069b0b020810069a0b02081006990b02081006980b02081006970b02081006960b0208100695
  | 5, 5 => 0xb02080e10060b0208ac10060b02081610060b02081606140b0208ab10060b020810aa060b020810a9060b0208105f060b0208105fa80b020810a7060b020810a6060b0208101e060b020810a5060b020810a4060b020810a3060b0208100666
  | 5, 6 => 0xb021a0819060b02170810060b02171006140b021710066c0b021710066b0b02220877100b02220810060b02690810060b02081910060b0208190a060b02081906970b020819063a0b02081906ad0b02081906a80b02081906640b02080e107f
  | 5, 7 => 0x780b02081006780b0208107c780b0208107b780b0208106c780b0208108d780b02311006780b021006b178020810067c78020810062a780208100684030b02081006030208100614b00b02081006af0b02081006ae0b020810060b0223081006
  | 5, 8 => 0xb30b020810067a7802081006b20b02081006780b02170810780b02081910
  | 6, 0 => 0x780b02081006000b0217081006000b0208191006000b020810067c000b0208100614000b0208100697000b0208100624000b0208100647000b020810068d000b0208100684
  | 7, 0 => 0xb02081006
  | _, _ => 0

def count : ℕ → ℕ
  | 2 => 2
  | 3 => 22
  | 4 => 132
  | 5 => 133
  | 6 => 10
  | 7 => 1
  | _ => 0

def table : Compact.PoolData := ⟨32,0x1000000010000000100000001,8,dictionary,packed,count⟩
def startMask : ℕ := 0xfffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0fffeeca0
def swap0x3 : Switch := ⟨7, 0xaa00aa00aa00aa00aa00aa00aa00aa, 0x55005500550055005500550055005500⟩
def swap1x2 : Switch := ⟨2, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 0x30303030303030303030303030303030⟩
def swap0x2 : Switch := ⟨3, 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 0x50505050505050505050505050505050⟩
def swap0x1 : Switch := ⟨1, 0x22222222222222222222222222222222, 0x44444444444444444444444444444444⟩
def swap2x3 : Switch := ⟨4, 0xf000f000f000f000f000f000f000f0, 0xf000f000f000f000f000f000f000f00⟩
def swap1x3 : Switch := ⟨6, 0xcc00cc00cc00cc00cc00cc00cc00cc, 0x33003300330033003300330033003300⟩

def switchPool : List (List Switch) := [[swap0x3, swap1x2], [swap0x2], [swap0x1, swap1x2, swap2x3], [swap0x1, swap2x3], [swap0x2, swap1x3], [swap1x3], [swap0x3, swap1x3, swap2x3], []]
def switches (i : ℕ) : List Switch := switchPool.getD i []

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem valid (j : ℕ) : ∀ s ∈ switches j, s.Valid := by
  intro s hs
  by_cases inRange : j < switchPool.length
  · have actual : switchPool[j] ∈ switchPool := List.getElem_mem inRange
    have checked : (switchPool.all fun xs => xs.all fun q =>
        @decide q.Valid (by unfold Switch.Valid; infer_instance)) = true := by decide +kernel
    rw [switches, List.getD_eq_getElem _ _ inRange] at hs
    letI : Decidable s.Valid := by unfold Switch.Valid; infer_instance
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked _ actual) s hs)
  · rw [switches, List.getD_eq_default _ _ (by omega)] at hs
    simp at hs

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem fixed (j : ℕ) : reindex (switches j) target = target := by
  by_cases inRange : j < switchPool.length
  · have checked : (switchPool.all fun moves => decide (reindex moves target = target)) = true := by decide +kernel
    rw [switches,List.getD_eq_getElem _ _ inRange]
    exact of_decide_eq_true (List.all_eq_true.mp checked _ (List.getElem_mem inRange))
  · rw [switches, List.getD_eq_default _ _ (by omega)]
    rfl

def hintPage : ℕ → ℕ → ℕ
  | 2, 0 => 0xed0e8014a1d4b0108f14200049ba70033c55c013305c3007062db017059c1004
  | 3, 0 => 0x496d4020490040404203e0e4402a70e7395f90e238ed103038dcc0e53700d0d52dea002629f560c3282e4083271380f3203910c21fef60371c9c60801beb30c719a0d0f618eba0d0173b510714df60d4105070500fcb10f70f9061330e1221300d0e91120a27102205d81003026ae0c4020a61110113d03400a220930066a0a7
  | 3, 1 => 0x91c1f024908ae0218f4331008d3350d789e260d3867bc0008437b090841c802383e87137821e607781d040f2804551507cfb31577502705474b850337329611771a770a46d6aa0366c1951446b1f40e66747409766bbd0f15d1600255979c14357c3406454be301752b6b0f54ea7a0d24c69a1404ad6a0a34a7f60c149cfd0c0
  | 3, 2 => 0xeb58c0e1e860b0a0e43fb0d6e3082063e241f032de44e070de0f9060d8c19047d79f2094d59930d1d3b0b012d27cc0f4cbc5a027c16de154c10130c5c05db0f0bf3090e0bbd38110b7b1c127b58270c6b2a02004b235e031aff4d147ae2ac087ad028035a9433053a8f09010a8572067a71910e3a169f0b09a17e01192518057
  | 3, 3 => 0xf9d64084f91ab120f894b007f4617134f25b7153ec6210b7
  | 4, 0 => 0xab556e00aa282060a9bc3d70a5214c609dda7a609b2567008b786a707df0380077e25a1077281430630a091062ce6d10576a1f4053dc597050f20b1047ed2c10437c424041e766003e4c057036cb577032f571702dbf10002aff077022c34b50226e8160221e73401ef301701dce5b30119438600dd77070057d360000be253
  | 4, 1 => 0x147270a7146524f413e812731378073112fc74c212d5418412bce0f71210a28711fa227411e580e011dc1590119611f1118c1365117833b61126b57410bc218210aef564104bf350102782c20fade6e30f6dd6c40ee000900d9570d70d0db1850ce0a5b50cc5b5070c5f65450ba5e3d30b7db6470b6c30230b3725c70b2db5b0
  | 4, 2 => 0x21b8759221b823072129167220ea0806204fb6f71fcd02671fae44331f78d3951f01c4971eacb2a41da636121d8711b31d1911c31cf4b1e11c4aa0c71b3c50c41a9426831a5a708319d450c519c977e71915e680190c64311906641318ebf24218dc30801812560217ba33221730a5b61689f0e6167de607166c66a114fbf120
  | 4, 3 => 0x2b9b82e72b74c1642b48d3612b3cd3312b2282b72b10f2e32aa433f72a7e34252a38758629f2474229ed204729a3b050298441e227de70b02766a2042763f430273cf687273aa1a626be6374267f1450264d1137259c34f52530b30224af8761245634e12447620523ef62d423ed33962359d1f021f7e0b721edb75221b8e777
  | 4, 4 => 0x372805b436afc160368064b6359d2563354ec49034f9233734aa31463405a170332e40e433190186329623a1328576333191f542311172a630a8b174309041903087d2d32fdd42912fae33932f8ed1872f50c4072eda40d12e4f75662e1b78212e1263242df204872cfff8372ce006112c89d3e72c8752772c37f2332c2374f6
  | 4, 5 => 0x4498c4a04464c0b644635551441277f24409c15343b51525438bc4104348a813428855754231d5a441f5507041cc55a241bbc7f04197772041595736406e2037404286d73fba61073f20a5313f1d24813ea0a7703e3254f23df4d2a13c6e35173c1485303aa0b5873a0307a339cba344394412e43843f2a2380dc4773761d434
  | 4, 6 => 0x4d0cf1944ca297a44c5f83034bf603a24bd590334bc7b2c74bc0e4154b9758074b4d93764b2466d54b0237604ae744924aa266d04a6167b04a6092114a12452649911024492d242048cf21c748296595482568014805e16247eae0e7478b7484476041d3473ce5b2471723b7470145674639a7a245c1024345a5e18045a28482
  | 4, 7 => 0x593d63e058c7e060584b13065845e59458031822576ec390576d66c05741e4125732a0c056ca038256ae93e35638381055da612755bd03c254d3933454b4b7e153c524f3534956c752d801c4529b4373527c23a55257a0e1512016a4508806345024e3f04f21e5834eec61d04eb7b5a54d5791404d44e3c14d2097474d1a3250
  | 4, 8 => 0x647d86c36455b336644a1491640ab54763d0f177624410b261ee42956188f0976070b5446058b7a1602df327600853945ff893115fc567675f9763815f8c95815ead02075e8ea6a25e8cf6225e56a3775e46c7275d65c4555d1516b45cb0b4a15c9457325c1c91445bbbb6205b0646675a7e14b45a6c753559ab62d159464522
  | 4, 9 => 0x72eef704727820d0722f81417121e562703784476faa50926e2456e46d63c5736d3c63176d3a05e76d1522c46cc7b2346cbf33a36cb523136bfa26176bd581576bac92b26b1f35966aaaf25469fba1a169c47044691ec5236912f0c168ef557067cd445367679202665360846636c46765e957a5656b934364c266f464b525e1
  | 4, 10 => 0x7ebbf4267e3293a07db511b47d8f67407d8c55857d7700b47d3a02b67d2e70f17cce64b17bff72837bf4a7c17bdce3847b99f1c57af3a3d47ae7f79779a901f2792f92a7792f8500791de69078edb2d278c525f0787918307808882777bef263778a22a0762305557604f48075ea72157593b77274c3d0c374b8f37273ce9220
  | 4, 11 => 0x8a6343638a3ff49489dca47489bf51e089a625b1883d15408824c0f087dea4a787c8c524878ce2278743f2a386ad35138646f224860641f785ee87e0852ef510846433208427e4c783e60257839427418215d46081aef1e5817b2435816723018163f4d78152f36480ed57a0808031f5806f48037f8ed3677edd15a77ed785b7
  | 4, 12 => 0x95931650953a83f394e622d794b59703944083b19397949692efd27092efb347925bd57290f2a21090dc07c090ced50490b536d39080f1c1907ee2419024e2648fb691108f3b73d08f01c0208ead45528e88c0718e7cb3b58e7711478e63c1e68e4354518e34a3538d35a2238cac02408c4791b78b64f3878b4916f08add8805
  | 4, 13 => 0xa19c6457a14f1256a1438061a134f362a13152b5a0c46293a0883471a02604c4a00d72449f0221d79ecc84369e7791619e6045039d9462f39d1ce0c69bbb05279ba4a6979b8785369b4ad2979a773416998007b798462296981dc5f197d2b21697d1747697cbb0a097c8e32397b5f6849744618396ae60e39681d5d195957315
  | 4, 14 => 0xadef12c5ad0263c5acf66392ace73514acda2537accae1f6ac6db117abe330f2ab9f8213ab820034aaf31636aaf2c2b0a9dea582a9be1247a85f4304a7daa456a7cc04f0a765d640a65a14b7a64ad811a5bf6330a59a7400a55ee601a49c82f4a47f7520a4163820a3c2d251a3bb2122a30893c3a2d53533a2b0f2c6a1e3b197
  | 4, 15 => 0xb73e3437b6f251f3b67a7780b6289817b5fd8321b5e4b173b5d0c427b5950635b55e23a6b52463b4b51b3802b4b32203b44e0030b3f0e0d4b3ac3486b2d95417b29e7730b21cd557b1d937f7b1cd87d7b0828671b01186b7aff09305af814280af5c1733af0d8470aedae815aeb14787aeac33c4ae7dc534ae4eb5f2ae357212
  | 4, 16 => 0xc45263f4c3d883e4c377f1b0c3127452c2d09414c1999483c19495e0c0863335bf51a4d0bf3fb333bf0ff411befb8757beb836e7be0ff4e0be01e723bdbe55a0bd99d472bce2b637bcd2f4a2bcc9f4c0bc9da565bc8e6230bb318237ba2fa165b97d7312b9718700b96295f7b8d3d4c1b833e2d0b8220150b7d26750b7b1c007
  | 4, 17 => 0xcea8f062ce9ea724ce2ad5d0cd5e07e2cd57a4e2ccf02793ccd49354ccaa9495cc15a314cbd8d193cb71e790cb641370cb4d8584cb3c3010cb0be4c3cadee485cac290b5ca345554c9537461c8b766b0c81b6475c8077422c7cd0560c7181246c6fbb593c6d74600c6bda4d1c5ff5201c5ec25a3c5d71290c4efe4b0c4cbf632
  | 4, 18 => 0xda19c130d9c9b4b2d9496326d947c561d947b576d93df3c0d9393027d8ede454d89226a5d8211217d795e2c0d79521e3d75e95d2d73c7284d72b74e7d70515a6d63dd543d5dd42b4d5b80294d58f2812d4e341e7d41c96d4d3f874b3d36c82b3d2ad1375d28881a7d17be142d0f55580cf5bd1a2cef02546ced7f1c2cecc83b0
  | 4, 19 => 0xe5696532e5586550e500f3b2e4bb6571e47887a7e44b72f7e4143771e3e1e610e3c89521e3812397e37ef553e33f2403e2fd70b3e2ea0072e2ae76a3e2876677e27fa292e24323a7e22832e0e16c4383e04633b3df45d7c2def5b166deb3f214dd8e56d6dd4431a3dc314556db963462db60c4c5dac8a432da5f86a0da5552d6
  | 4, 20 => 0xf09d2371efe7c2b1efccf0d3ef4372d5ef247713edd3e332edb9c200ed6bc1a5ecbc0325ec84f591ec03b357eb9e37c7eb64b473eb60f794eb1590c2ead22181eacc15c0eaa69762ea11c4d2ea00c2a5e992a1c6e9089245e89d80e2e80c8735e7ae3043e77594f7e76803c7e6abc2c3e6427366e63181a0e5af4800e57e9385
  | 4, 21 => 0xf9dce631f97b5657f91ab000f90141a4f8f28627f85db404f84297f1f81b4145f77d1621f77586d2f762a0d5f75fb2f0f726f1c0f6e96493f6927252f665b154f657a4f1f6513541f626b3c6f5f07421f5da6087f4b690e5f3b516b3f3af6710f3a646a6f39750d2f38f8163f3647121f33677d0f23e0067f1f2e804f13f5167
  | 4, 22 => 0xff77c751ff5733a4ff4ef5d7ff046630fdcb51e4fda95714fd5f36f3fd4d3300fd48a040fd2d30d6fcfb9391fcf5f814fca9d1d4fca65737fc5bc5e2fbdd5423fb548260fb4ef310fae50255fa195340f9e6f316
  | 5, 0 => 0xb71f0f70abcc4030aa280260a7283330a521076093dd66608eab32708c5d1a50812a7d107f3d22407c12740079bf2c00794a80405d04650055252970534b17304fdb4960434f541041e70b003e4c00703cd731203ad3662032b46410319e233027d3277023fc1f70231025401a62513019b4197018084f700da732600a66770
  | 5, 1 => 0x1a9cc1561a2234c719d592b419bef7d219a78120196bf5b6193f711718e4230017fe144617f4f8001771d68015c6537615bec82714e166651335f71012fc707212d97152128c93c7120806c111c347a2115c0287115850d3113ae16710aef094109e72530fe5a2670fc4e3c50f4d35850d91c3320ca1d4270c9d54d00bc6f620
  | 5, 2 => 0x2507251124cc051624af67f7244760252420e5e723ff783723ddf3c323bf73f0229955d7223dd3a6222d7644222a53c221a63335219836872163973521294456210892c520fa83a32083e445200f90d0200a33801fcd00471f53c7801f4e33641f4926d11e3c75c71d7793941bc845f31b4ac8011afc23a71afbc5e11ab777e1
  | 5, 3 => 0x2f50c0672f40f3e72f3b64952ef232d22eefa7372e94f0e72e7217172e4f70962e4967312e45b1462e41b3772d0b98122cf171e72cdef6972b5d03842aa4e5572a7a66a22a5787902a04f70329fc179129a3b000296184f628d5c107287bb563285f12b62781d5652766a02426e8a1c026ac53c125cee6f425346572252192b2
  | 5, 4 => 0x3d2413723d2406003c6e30873c4855103c24f4c03c01d3e13b5fc4873a8924113a81012439a503b738dc03a2380524e0372051f336f8955036b0c707364502b335d8d830359d209334f601c73416e6223394f512335501b0333813b4330d15a7326f27163251d65431d766c730f8049130c436e0309040103045f5312f81d303
  | 5, 5 => 0x4bfab6114be181314b6632404b0ff4424a2062024971d5d0483795a24731311347234613471a61354701409746b336104663b7b64616a551461602454506c66744c4a35044b8169244a885d442df814342691653425f35224200f2f040bae4a6405e93c43fc416173f9302613f5126553eb1f6233e8b04213de814d73d62d2b5
  | 5, 6 => 0x5605f23455ac85b4552b70f05493b440548b4580543da6255401f7c253faa601539145905303a41052aa07f25286a3225234b247523461f45205c47751788360513d666150c3421450b4b1a0509c31474ecf81534ece07b24e24f1014dcda6c04d8217f04d4251004d0cf0144d0b85344ce256344c9b31904c5d11d54bfb5250
  | 5, 7 => 0x625001e362228160619ee54360c091a160519457601271a25ff890515f9e64825f8e55f05f7de5e55f0b82445ead00275e8cf0a25dc0a3305d7f14545c8e84a15c5b51805c4de6355bbbb0a05b5c06755b4233105b0640b75a8384f55a76a8075a69561259d602135994e2c157e2954257cb729557ba9357574d05f257108562
  | 5, 8 => 0x6e4986a76dd5a3246d3c60576ced04f46cde24e16cb520536c7213676c58f2006c03b5756b1335676ada820769de851569aa66f769a357f16939e71468fad5b0686ca1b267def42067a832d1679811d16767902265f503c0654ac63664cca13064ca162764c8d20464c59270647cb3b06468e58463c7677263bf157362df8715
  | 5, 9 => 0x788596247856e7717855b3d5782007b577ec952777e962b077e641a377bef0437737e2f2765003e2764d78107622c13275f082f57575e7c77571843574c4017474a5e246749295a073ce903073723452736c135471f32194716756e77121e09270ec34a5703a86146fea01b76faf74176f9011446f6da4a36f5fd0d46ebd2467
  | 5, 10 => 0x81ae37e0817955408100756680a091b68085f6c2806e94418050b797802852d07ed8f2657e3844077e08d2f47d3014d27d16b5817cc773747cc624327bf934b17bc094937bb524347b97b3047b70a3977b5111577b2b23077b2377047b1d26377aedb5f77ab6c5457a8be6437a4964a079ed97c179baa4807906d39078f60331
  | 5, 11 => 0x8d45d7778d35a0338c6164f08bf116648be6b2278bdeb5618b6101d68a6b1447897627b7893d75b788f6776088ba8241889321c4888b1605884de6338848a71287cd0663878ce037875a421086ad30838646f03485718373855561b3852ef080846993a4845637928427e077841326f08384f4008350711482802383826f7321
  | 5, 12 => 0x9b2668409b22f5719aada7e7999e61b4992f83a09835414097b707a796b055b5969d16b095957055958b2170936993a59359c12392e8f63292dbc6409207d1a791bfb2f791bea2f691af2576912346f3908fd370907f8747905ad460902a66579024e044901bb3b3900ea2908fb6a5b18ef2b6d78ec795608eb575c48e534711
  | 5, 13 => 0xa5fe9223a5f74150a5c7a280a59a7060a57661d0a4b5a443a4924762a43d6713a392c481a3260656a2fe97b4a2cc41e0a2a4e4e7a2136586a1e3b017a1ad12b7a167c6a1a0e54806a0bd8825a034f316a02600749ffad1d39f74b4a49f0647a19f0063159ecbc6309ebfa5b29ea941379e0eb1029d8aa5f19bdfc6d09b540337
  | 5, 14 => 0xb1c78257b1370583b0963750af6da436af049151aeda6291aecca626aeb140c7ae12b320ae0c2720adc63371ace73084ace133d0ab1dc645ab1bc260aabf7521aa905203a98b6142a90d6821a8cd0757a8c1e281a811f761a7cd6205a7c00592a7bb0363a7820501a760f455a6f45187a691e642a6904811a648b2a7a617a2e0
  | 5, 15 => 0xbc207544bbcab183bbbff691bb9c8564baf954b0bac2e220ba99a5d3ba681570ba5fd1d7ba1c3387b97d7052b90c2163b8f557c0b8d3d071b85f8134b8145587b7eed700b79867b1b78e53e0b741c437b73384d5b6e500d7b6cc81d2b67a70c0b5d401a6b4b32023b497d4e2b46d0514b446f517b257d532b243e533b240c492
  | 5, 16 => 0xcbb82767cb8b4344cb326127cb0be073c969e1a4c905a193c8941616c8040230c7cd0090c7121500c65e35b3c610c5f6c5ff5021c402b847c3cba820c32dd177c2d621e4c2a5f314c1b42607c1a4a4a7c17e3470c0f9e7d0c0e36723c0073591bff1d5e0be29d494bda231d4bd937164bcc9f070bcc2f4d6bc9da095bc3b8282
  | 5, 17 => 0xd947c091d91372e7d8d07311d83a2606d7f3e5c3d780a450d675a5c0d66e96a0d6329803d5ee9555d5a847a0d5a0c547d4f1d5f4d48102a0d47e5787d4209242d40401b1d3412782d2e9b393d26c5727d26bb670d262d433d1858451d15151b5cee56334cee04431ce9306b2ce4a3651cc9c62f1cc15a054cbe4b556cbd8d013
  | 5, 18 => 0xe5aed6b7e58e84c1e559b444e4de9781e33f2063e33e73a1e316e2d7e2693802e245d621e21d2136e19d40e0e15884a2e1418323e0d262c7df87d603deb355a1de9f66b1de88d502de013574dd88e7b3dd658184dc9c6604dc812453dc4fd430dc361206dbf7c343dbe77805db60c075d9f3c217d9eb3677d9a494d4d986e507
  | 5, 19 => 0xf37d0690f33b43d7f1f2c817f17cb243f08a15f5f07511c3f0327652eff71660efddb3c6ef7a5340ef247535ee92b554edefb553edb9c020edace2f3ed69e497ed2bf546ec49c520ec1e7404ebedf425eaea64c2ead5f4b7ea4996d2e92591f0e870d530e77f5537e755a201e731c7e2e678e602e63ee110e621d671e5d704f1
  | 5, 20 => 0xfbfcb646fbe452b1fb548040fb4ef050fae6f597f9e6f056f99247d7f92ad615f9279582f918d313f8f280a7f8b48155f85db064f7b9e490f7949325f77d10a1f714e4f2f704d375f6f5f415f6f4a647f6bab4b2f6b6f133f68b9536f66e5336f5aa5237f531e577f4fea4d1f4ea7353f3dbf4f3f3b89154f39c64d3f39bf7b0
  | 5, 21 => 0xfe6793d1fe4af145fe278552fe241317fe0083f7fdd47141fdc26724fd94d631fd151347fc6b3730
  | 6, 0 => 0xd2e9b033d26bb070c17e3050bc3b8002ae12b010a8c1e001a5c7a000826f70117b70a0377906d030736c1024716750876dd5a01469a3509167def0405b5c007557ba902752aa00925286a0125205c0574d82109044c4a0203e8b00413c24f06030c4308024af60971d7790341a223067115c00070ca1d04708eab01700da7016
  | 6, 1 => 0xf7949015f4ea7023ebedf045eaea6062e621d071e58e8061e1418013d9eb3077
  | 7, 0 => 0x70378007
  | _, _ => 0

def hintCount : ℕ → ℕ
  | 2 => 8
  | 3 => 102
  | 4 => 725
  | 5 => 682
  | 6 => 40
  | 7 => 1
  | _ => 0

def hints : Compact.CodeBook := ⟨20,12,hintPage,hintCount⟩

def locate : ℕ → List W → ℕ × ℕ := Compact.lookup table hints 0xbf58476d1ce4e5b9
def check : ℕ → ℕ → Bool := Compact.check table target negative startMask locate switches (fun _ _ => false)

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page2at0 : span (check 2) 2 0 = true := by apply block2 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer2 : span (check 2) 2 0 = true := page2at0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at0 : span (check 3) 4 0 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at4 : span (check 3) 4 4 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at8 : span (check 3) 4 8 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at12 : span (check 3) 4 12 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at16 : span (check 3) 4 16 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at20 : span (check 3) 2 20 = true := by apply block2 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer3 : span (check 3) 22 0 = true := span_join (span_join (span_join (page3at0) (page3at4)) (page3at8)) (span_join (span_join (page3at12) (page3at16)) (page3at20))

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at0 : span (check 4) 4 0 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at4 : span (check 4) 4 4 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at8 : span (check 4) 4 8 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at12 : span (check 4) 4 12 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at16 : span (check 4) 4 16 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at20 : span (check 4) 4 20 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at24 : span (check 4) 4 24 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at28 : span (check 4) 4 28 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at32 : span (check 4) 4 32 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at36 : span (check 4) 4 36 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at40 : span (check 4) 4 40 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at44 : span (check 4) 4 44 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at48 : span (check 4) 4 48 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at52 : span (check 4) 4 52 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at56 : span (check 4) 4 56 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at60 : span (check 4) 4 60 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at64 : span (check 4) 4 64 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at68 : span (check 4) 4 68 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at72 : span (check 4) 4 72 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at76 : span (check 4) 4 76 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at80 : span (check 4) 4 80 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at84 : span (check 4) 4 84 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at88 : span (check 4) 4 88 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at92 : span (check 4) 4 92 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at96 : span (check 4) 4 96 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at100 : span (check 4) 4 100 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at104 : span (check 4) 4 104 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at108 : span (check 4) 4 108 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at112 : span (check 4) 4 112 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at116 : span (check 4) 4 116 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at120 : span (check 4) 4 120 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at124 : span (check 4) 4 124 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at128 : span (check 4) 4 128 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer4 : span (check 4) 132 0 = true := span_join (span_join (span_join (span_join (span_join (span_join (page4at0) (page4at4)) (page4at8)) (span_join (page4at12) (page4at16))) (span_join (span_join (page4at20) (page4at24)) (span_join (page4at28) (page4at32)))) (span_join (span_join (span_join (page4at36) (page4at40)) (span_join (page4at44) (page4at48))) (span_join (span_join (page4at52) (page4at56)) (span_join (page4at60) (page4at64))))) (span_join (span_join (span_join (span_join (page4at68) (page4at72)) (span_join (page4at76) (page4at80))) (span_join (span_join (page4at84) (page4at88)) (span_join (page4at92) (page4at96)))) (span_join (span_join (span_join (page4at100) (page4at104)) (span_join (page4at108) (page4at112))) (span_join (span_join (page4at116) (page4at120)) (span_join (page4at124) (page4at128)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at0 : span (check 5) 4 0 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at4 : span (check 5) 4 4 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at8 : span (check 5) 4 8 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at12 : span (check 5) 4 12 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at16 : span (check 5) 4 16 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at20 : span (check 5) 4 20 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at24 : span (check 5) 4 24 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at28 : span (check 5) 4 28 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at32 : span (check 5) 4 32 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at36 : span (check 5) 4 36 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at40 : span (check 5) 4 40 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at44 : span (check 5) 4 44 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at48 : span (check 5) 4 48 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at52 : span (check 5) 4 52 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at56 : span (check 5) 4 56 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at60 : span (check 5) 4 60 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at64 : span (check 5) 4 64 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at68 : span (check 5) 4 68 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at72 : span (check 5) 4 72 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at76 : span (check 5) 4 76 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at80 : span (check 5) 4 80 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at84 : span (check 5) 4 84 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at88 : span (check 5) 4 88 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at92 : span (check 5) 4 92 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at96 : span (check 5) 4 96 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at100 : span (check 5) 4 100 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at104 : span (check 5) 4 104 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at108 : span (check 5) 4 108 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at112 : span (check 5) 4 112 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at116 : span (check 5) 4 116 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at120 : span (check 5) 4 120 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at124 : span (check 5) 4 124 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at128 : span (check 5) 4 128 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at132 : span (check 5) 1 132 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer5 : span (check 5) 133 0 = true := span_join (span_join (span_join (span_join (span_join (span_join (page5at0) (page5at4)) (page5at8)) (span_join (page5at12) (page5at16))) (span_join (span_join (page5at20) (page5at24)) (span_join (page5at28) (page5at32)))) (span_join (span_join (span_join (page5at36) (page5at40)) (span_join (page5at44) (page5at48))) (span_join (span_join (page5at52) (page5at56)) (span_join (page5at60) (page5at64))))) (span_join (span_join (span_join (span_join (span_join (page5at68) (page5at72)) (page5at76)) (span_join (page5at80) (page5at84))) (span_join (span_join (page5at88) (page5at92)) (span_join (page5at96) (page5at100)))) (span_join (span_join (span_join (page5at104) (page5at108)) (span_join (page5at112) (page5at116))) (span_join (span_join (page5at120) (page5at124)) (span_join (page5at128) (page5at132)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at0 : span (check 6) 4 0 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at4 : span (check 6) 4 4 = true := by apply block4 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at8 : span (check 6) 2 8 = true := by apply block2 <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer6 : span (check 6) 10 0 = true := span_join (span_join (page6at0) (page6at4)) (page6at8)

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at0 : span (check 7) 1 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer7 : span (check 7) 1 0 = true := page7at0

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem validated (k : ℕ) (hk : k ≤ 7) (i : ℕ) (hi : i < count k) : check k i = true := by
  have e : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [count] at hi
  · simp [count] at hi
  · exact span_member layer2 i (by omega) (by simpa [count] using hi)
  · exact span_member layer3 i (by omega) (by simpa [count] using hi)
  · exact span_member layer4 i (by omega) (by simpa [count] using hi)
  · exact span_member layer5 i (by omega) (by simpa [count] using hi)
  · exact span_member layer6 i (by omega) (by simpa [count] using hi)
  · exact span_member layer7 i (by omega) (by simpa [count] using hi)

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem bound : signedLower target raw 8 :=
  Compact.lower table target positive raw essential negative neg startMask 7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) locate switches valid fixed (fun _ _ => false)
    (by intros; rfl) validated

end LeafSeed14

end GraphSignedFrontier

namespace GraphSignedFrontier

namespace LeafHint4

def target : W := 0xfffefffefefaeca0fffefffefefaeca0
def raw : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000]
def negative : List ℕ := [0, 1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 32, 48]

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem positive : target ≠ 0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem unique : raw.Nodup := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem neg : ∀ r ∈ negative, r < 128 ∧ target.getLsbD r = false := by
  intro r hr
  have yes : (negative.all fun j => decide (j < 128 ∧ target.getLsbD j = false)) = true := by decide +kernel
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp yes r hr

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨4,5,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : W) ∨ z.getLsbD 4 = z.getLsbD 5)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨8,10,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xcccccccccccccccccccccccccccccccc : W) ∨ z.getLsbD 8 = z.getLsbD 10)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : W) ∨ z.getLsbD 1 = z.getLsbD 5)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨2,10,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xff00ff00ff00ff00ff00ff00ff00ff00 : W) ∨ z.getLsbD 2 = z.getLsbD 10)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,17,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffff0000ffff0000ffff0000ffff0000 : W) ∨ z.getLsbD 1 = z.getLsbD 17)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd
  · refine ⟨1,33,by decide +kernel,?_⟩
    intro v vm hd
    have yes : (raw.all fun z => decide (z = (0xffffffff00000000ffffffff00000000 : W) ∨ z.getLsbD 1 = z.getLsbD 33)) = true := by decide +kernel
    exact (of_decide_eq_true (List.all_eq_true.mp yes v vm)).resolve_left hd

def dictionary : ℕ → ℕ
  | 0 => 0xfafa00fafafa00005a5a5a5a5a5a00000f0f0f0f0a0a0a0a0f0f0f0f00000000f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaa050505050000fafafefefefefefefefefafafafafafafafa00fa00fa00fa00fafffffffffafa0000ffffffffa0a0a0a0fafa0000fafa0000fffafffafffaff00a0a0a0a0a0a0a0a0ffa0ffa0ffa0ffa0fafafafafafa0000fefefefefefeccccfefefefeccccccccececececececececfafaa0a0fafaa0a05f005f005f005f00ffffffff00000000050005000500ff005f5f5f5f00000000fafafafafafaa0a0cccccccccccccccc0505050500000000fffffffffafaa0a0ff00ff00ff00ff00ccfeccfeccfeccfe0000000000000000
  | 1 => 0xaeaeaeaeaeaeaeaecd00cd00cd00cd0005000500ff00ff00afaeafaeafaeafae0504050405040504ffccffccffccffcc0000fafa0000fafaffffffffcc00cc00333333333333000000ff00ff00ff0000ffffffffaaaaaaaaffff0f0fffff0000cceecceecceecceeffffffffaaaa0000fafafafafafaaaaaffffffff0000fafafffffafaffff0000ffff0505ffff0000ffff00ffffff0000ffff0000ffff00000000ffff0000fafa0000fefe0000fefe000000000000fafa55555555555500000f0f0f0f0f0f0000ffffffff0a0a0a0affffa0a0ffffa0a000ff00ff00cc00ccfefecc04fefecc045f5f5f5f00005a5aaaaaaaaaa0a0a0a000000000a0a0a0a0
  | 2 => 0xeeeeeeeeeeeeeeeefafaaaaafafaaaaaaaff00ffaaee00cca0ffa0ffa0eca0ec5050f0f05050f0f0ffff0000fafa0000ffccffccccccccccfefe0404fefe04040a0a0a0a0a0a0a0a00000000f0f0f0f0eeeeeeeeaaaaaaaaeeaaeeaaeeaaeeaaccccfefe0000fafacc00fefacc00fefa5f5f005f5f5f000033ff030f33ff00000505ffff0000fafa0404fefe0404fefe00fffaff0000fafaf0f0f0f0f0f00000aaaaaaaaaaaa0000ff00ff00cc00cc005f5f00005f5f000033003300ff00ff0005050505fafafafa33ff33ff00000000ffccffccffcc00000505050505050000ffffffffffff0000ffccffccaa88aa88cc00cc00cc00cc00fafafafaaaaaaaaa
  | 3 => 0xee00ee00ee00ee005500550055000000ff00ff00ee00eeffeeffeeaaaaaaaaafafafafaaaaaaaaaaaaaaaaffeeffeeaa88aa88ffccffcc0a0a0a0a0f0f0000000000000f0c0f0c0f0f00000f0f000000000000ffff0000ffffffffff00ff00ffffffffccccccccfffffffffafafafac8c8c8c8c8c8c8c80404040404040404fffffffff0f0f0f0ffffeeeeffff000000aa00aa00aa00aafefefefef0f0f0f0ffffffff88888888ffffffff00aa00aafafafafa0000000000000000fafafafafcf0fcf0fcf0fcf022aa22aa22aa22aadd00dd00dd00dd00ffff0505fafa00004c4c4c4c4c4c4c4cfff0fff0fff0fff0ffaaffaaffaaffaafcfcfcfcfcfcfcfc
  | 4 => 0xaaaaaaaafefefefea8a8a8a8fcfcfcfc0a0f0a0f0a0a0a0a0505050504040404000000000e0e0e0eaaaaaaaa00000000aaaa0000aaaa000000cf00cf00cc00cc0000aaaa0000aaaa00000000aaaaaaaacccccccc000000000f0f0f0f0c0c0c0c0f0c0f0c0f0c0f0c00ff00ff00aa00aa00ff00ff0000000000cc00cc00cc00cc00000000cccccccc00000000eeeeeeee00000000fafa00000000ffff0000000000000000ffccffccffffffffffffccccffffffffffffaaaaffeeffeeffeeffeef5f5f5f5f5f5f0f033333333222222223300330033003300eeeeeeeeeeee0000ddddddddddddcccc555555555050505055555555444444440e0e0e0e0e0e0e0e
  | 5 => 0xf000f000f0000ffccffcc00000000cccccccccccc00005555555500000000000000000000cccc000000000000aaaa00000000ff00ff00ffffffffffccffccffffffffeeeeeeeeeeeeeeee00000000ffffffff0f0c0f0cffffffff0e0e0e0effffffccffff0000ffffaaaaffffaaaa4444444444444444888888888888888822222222222222220c0c0c0c0c0c0c0cffff000000000000ffeeffeeccccccccfefefefeaaaaaaaafafffafffafafafafafafafac8c8c8c8fac8fac8fac8fac8aaffaaffaaaaaaaa00000000ffaaffaaeeeeeeeeee00ee00eeeeeeeee0e0e0e0eee0eee0eee0eee0cc88cc88ffaaffaac8c8c8c8fafafafaafafafafaeaeaeae
  | 6 => 0xee00ee00ee00ee00e0e0e0e0e0e0e0e0111111110000000011001100110011001010101010101010cc00cc00ccccccccaa00aa00aa00aa00a0a0a0a0aaaaaaaa88888888cccccccc88888888aaaaaaaa0f000f000f000f000c0c0c0c000000000a0a0a0a0000000000cc00cc0000000000aa00aa00000000cfcfcfcfccccccccccffccffcccccccc0033003300000000000f000f000000003333333300000000f0f0f0f0a0a0a0a0cccccccc88888888c0c0c0c0c0c0c0c000f000f000f000f000000000505050500000000044444444000000000000f0f0cfcfcfcfcfcfccccccffccffccffccccafafafafafafaaaaaaffaaffaaffaaaa0033003300330000
  | 7 => 0xaaaaaaaa8888888800000000330033000000000022222222aa88aa88aa88aa880022002200220022ff00ff0000000000f0f0f0f000000000f000f000f000f000
  | _ => 0

def packed : ℕ → ℕ → ℕ
  | 2, 0 => 0x30201
  | 3, 0 => 0x15020e1115020605150201111402060514020f0c1402130109120e1109100f0c09020e0609020d0b0902060c09020b010906050a090605080206050702060504
  | 3, 1 => 0x3021805030217050302050403020516
  | 4, 0 => 0x902170522090206051109020f0c1109020f052109020f051109020f052009021f05110902130111090205111e090f05110a090f051108020f051a1d020f051107020f05111c020f051104021b051a19
  | 4, 1 => 0x142c1705241402170f05140217052b140217052a140217052914020f051a14020f0511140205282726020f051a0925020d170925021701092517052409120e1b1a09020e0f1109020d13110902231b1a
  | 4, 2 => 0x151b051a08151b051a2438343a1b1a382c1b3c1a382c1b1a3b383a1b1a39381b1a37363534021b333202311b0514300217051409020f05142f021705142e021705142d021705142c020d17142c021701
  | 4, 3 => 0x4314020f05431402054443421b411a150218051115020e1b1a15020d1b1a1502311b0515020f05111502401b0515021b011a15021b053f1502051a1d15020511041502051116151b3e051a151b051a3d
  | 4, 4 => 0x4338451b1a
  | 5, 0 => 0x90f1b051a0809131b3e051a09131b051a3d09131b051a24091b3e051a39091b051a4924091b051a4839091b051a3d39091b051a2439091b411a37362c021b051a47020f1b051a1c020f1b051a04021b051a4639021b051a04290009020f0511
  | 5, 1 => 0x9020f051a5609021f1b051a0902131b011a09021b55053909021b54053909021b011a3909021b53051a09021b05521a09021b051a5109021b051a5009021b051a4f09021b051a4e09021b051a4d09024c054b11090205112827094a1b051a39
  | 5, 2 => 0x95a02051a1d093a1b411a390959021b1a3909020e0f1b1a09020d131b1a09020d1b1a390902581b051a0902170f051109021705112b09021705112a0902170511290902310f1b050902311b054b09020f1b051a09020f051a1109020f051a57
  | 5, 3 => 0x92e021705110964021b051a092d02170511092d021b0c1a092d021b1a63092c6261605f092c421b411a092c020d1711092c02170111092c17051124092c5e1b0524092c1b055d1a092c1b051a5c092c1b413c1a092c1b411a3b092c051a5b24
  | 5, 4 => 0x142d021b051a142c1b051a246b34021b051a6b2d021b051a6a34021b051a3009021705113002691b051a30021b051a68092f0217051109251b051a2409343a1b411a09340267051a0934021b54050934021b331a0934021b056609341b65051a
  | 5, 5 => 0x6f352c02605f6f352c0205166f35021705393834021b051a38021b051a393509020f1b05352f02171b05356e021b5f053534021b5f053534021b056d352c026c5f053502170f1b053502171b052935020f1b051a35021b052827322c1b051a24
  | 5, 6 => 0x4302051a1d76431b051a247574732c611b5f7215021b051a722f021b051a72020f1b051a72021b051a291502181b051a15020f1b051a1502691b051a15021b05711a15021b051a0415021b051a7015021b051a1615021b051a686f352c021805
  | 5, 7 => 0x43350205275743351b051a7d43351b051a24432602051a274309451b411a4309020f0511430902051144437c3a021b054342021b051a43021b5f057b43021b057b2843021b057a1a43021b051a7943021b051a7843021b051a774302051a271d
  | 5, 8 => 0x433502181b05433502601b5f43350217051d4335020f1b05433502871b054335021b5f864335021b5f854335021b84054335021b83054335021b05824335021b05814335021b05804335021b05444335021b05164335021b057f4335021b057e
  | 5, 9 => 0x8a4335021b5f89436f0217054374733a1b1a437202051a1d436f35021705437335021b5f433588021b05
  | 6, 0 => 0x2c021b051a04682c021b051a8c8b004372021b051a00433502171b05004335021b5f05004335021b05280043091b051a240043021b057b1a0043021b051a1d0043021b051a8b0074732c3a1b1a006f352c021705003534021b051a003009021b051a0009020f1b051a00091b051a2475
  | 6, 1 => 0x9021b051a703909021b051a247509021b051a927509021b051a913909021b051a163909021b051a167509021b051a7f7509021b051a903909021b051a396809021b051a398f09021b051a758b09021b051a756809021b051a758e09021b051a688d09021b051a68292c021b051a1d8c
  | 6, 2 => 0x902131b05711a0902131b051a040902131b051a700902131b051a160902131b051a6809021b4c051a4b09021b05951a3909021b05411a3909021b05711a3909021b051a282709021b051a373609021b051a947509021b051a1d7509021b051a937509021b051a807509021b051a0439
  | 6, 3 => 0x92c1b051a5724092c1b051a248c092c1b051a2497092c1b051a2475092c1b051a24960988021b051a75093a021b051a39090218131b051a0902181b051a390902181b051a750902170f1b051a0902171b051a2b0902171b051a2a0902171b051a29090269131b051a0902691b051a39
  | 6, 4 => 0x92c021b059f1a092c021b051a79092c021b051a9e092c021b051a9d092c021b051a9c092c021b051a3b092c021b051a77092c021b051a9b092c02051a1d76092c171b051a24092c1b051a9a24092c1b051a9924092c1b051a1124092c1b051a1c24092c1b051a1c98092c1b051a7624
  | 6, 5 => 0x92c02171b011a092c02171b05a7092c02a91b051a092c02a81b051a092c021b5f057b092c021b5f05a7092c021b5f0592092c021b5f05a6092c021ba5051a092c021ba4051a092c021ba3051a092c021b05a21a092c021b05a11a092c021b05a01a092c021b053c1a092c021b057a1a
  | 6, 6 => 0x92d02171b051a092d021b5f051a092d021b051a11092d021b051ab0092d021b051aaf092d021b051aae092d021b051a57092cad1b051a24092cac61021b1a092c7c3a021b05092c42021b051a092c6102601b5f092c611b5f057f092c020d171b1a092c02ab601b05092c02aa1b051a
  | 6, 7 => 0x352c021b5f058eb5092c021b051ab4092c021b051a300902171b051a09b33a021b051a092f02171b051a096e021b5f051a09b22c1b051a2409343a021b051a0934021b5f051a0934021b05411a0934021b051ab00934021b051ab10934021b051a900934021b051a6d092e02171b051a
  | 6, 8 => 0x35092c0217051d35092c021b5f8635092c021b5f8535092c021b058235092c021b058135092c021b058035092c021b051635092c021b057f35092c1b051a7d35092c1b051a24350902171b05393509021b051a2b352c0217691b05352c02171b0568352c021b5fb605352c021b5f051c
  | 6, 9 => 0x722c021b051a8c722c021b051a686f35092c0217056f352c021b5f056f352c02051a1db7092c61021b05b709021b051a757335092c021b5f73092c61021b5f7309021b051a3973094a1b051a7573091b051a2475732c021b5f1a9135092c88021b0535092c02181b0535092c02601b5f
  | 6, 10 => 0x43021b051a1c9043021b051a1c6d43021b051a1cbb43021b051a1cba43021b051ab98fb809021b051a757473092c3a1b1a74732c021b5f1a74732c1b051a2472092c02051a1d72095a021b051a720902131b051a7209021b051a2b7209021b051a397209021b051a75722c02691b051a
  | 6, 11 => 0x43091b051a9190432c021b057b1a432c021b051a1d432c021b051a8b433abe021b051a433a021b051a1c433a021b051a8b4302171b051a0443021b5f051a1c43021b05bd1a1c43021b05411a1c43021b051a4b1c43021b051ab01c43021b051abc2743021b051ab11c43021b051a1c36
  | 6, 12 => 0x4309021b051a944309021b051a1d4309021b051a934309021b051a804309021b051a444309021b051a244309021b051a924309021b051a164309021b051a7f4309021b051ac04309021b051abf4309021b051a8b4309021b051a684309021b051a8e430902051a275743091b051a3690
  | 6, 13 => 0x4335021b051ac64335021b051ac54335021b051abb43092c1b051a24430988021b051a430945021b051a430961021b5f05430902181b051a430902601b5f1a4309020f1b051a4309021b5f1a854309021b84051a4309021bc4051a4309021bc3051a4309021b05c21a4309021b05c11a
  | 6, 14 => 0x4335021b4c051a4335021bcb051a4335021b05bd1a4335021b05ca1a4335021b05411a4335021b05c91a4335021b051a274335021b051a1d4335021b051aae4335021b051a364335021b051a924335021b051ac84335021b051a904335021b051a564335021b051a8f4335021b051ac7
  | 6, 15 => 0x43722c021b051a437202171b051a436f35021b051a43b735021b051a43b709021b051a437335021b051a4373093a021b1a437309021b5f1a437309021b1a374373094a1b051a4373091b051a2443350902171b05433509021b5f05433509021b052843353a021b051a433502601b051a
  | 6, 16 => 0x8a4335021b051a8a4309021b5f1a8a43021b051a1c89436f021b051a89430902171b058943021b051a1c43b809021b051a437473021b051a437235021b051a437209021b051a
  | 7, 0 => 0x92c021b051a7f00092c021b051ace00092c021b051acd00092c021b051a8b00092c021b051a6800092c021b051a8e00092c1b051a9190000902171b051a39002c021b051abc1c002c021b051acc9100004335021b051a000043021b051a1c00000934021b051a0000092d021b051a0000092c1b051a24000009021b051a39
  | 7, 1 => 0x92c02601b5f1a00092c02691b051a00092c021b5f1a8500092c021bb6051a00092c021bd0051a00092c021bcf051a00092c021b057b1a00092c021b05a71a00092c021b051a9400092c021b051a1d00092c021b051a9300092c021b051a8000092c021b051a0400092c021b051a2400092c021b051a9200092c021b051a16
  | 7, 2 => 0x73092c3a021b1a0073092c021b5f1a0073092c021b1acc0073092c4a1b051a0073092c1b051a2400732c021b051a910035092c02171b050035092c021b5f050035092c021b05bc00352c021b051a1c000934021b051a1c00092d021b051a9100092c88021b051a00092cbe021b051a00092c61021b5f0500092c02181b051a
  | 7, 3 => 0x4309021b051a1c004309021b051aae004309021b051a57004309021b051a36004309021b051a91004309021b051a90004309021b051a6d004309021b051a8f004309021b051a96004309021b051abb004309021b051aba00b8092c021b051a0074732c021b051a0072092c021b051a006f352c021b051a00b7092c021b051a
  | 7, 4 => 0x92c021b051a8f96008a4309021b051a00894309021b051a00437309021b051a00433509021b051a0043093a021b051a00430902171b051a004309021b5f051a004309021b05bd1a004309021b05951a004309021b05411a004309021b051a4b004309021b051a9a004309021b051a11004309021b051ab0004309021b051a27
  | 7, 5 => 0x92c021b051aaeb9092c021b051aae96092c021b051a5791092c021b051a5790092c021b051a578f092c021b051a91d2092c021b051a91d1092c021b051a91ce092c021b051a91cd092c021b051a918f092c021b051a9196092c021b051a9096092c021b051a6d56092c021b051a6d8f092c021b051ab98f092c021b051a5696
  | 7, 6 => 0x92c021b051ab11c092c021b051ab1d5092c021b051acc91092c021b051aaf91092c021b051aafc8092c021b051a1cd4092c021b051a1cd3092c021b051a1c04092c021b051a1c91092c021b051a1c90092c021b051a1c6d092c021b051a1ccd092c021b051a1c8f092c021b051a1c96092c021b051aae91092c021b051aae6d
  | 7, 7 => 0x92c021b051a9a90092c021b051a9a56092c021b051a9a8f092c021b051ad81c092c021b051a1191092c021b051a1190092c021b051a118f092c021b051ad7bc092c021b051ad6cc092c021b051ab01c092c021b051ab0d5092c021b051ab091092c021b051ab0c8092c021b051ab0b9092c021b051ab056092c021b051abc1c
  | 7, 8 => 0x92c021b05951ab9092c021b05951a96092c021b05da1a91092c021b05411a9a092c021b05411a11092c021b05411a1c092c021b05411a57092c021b05411a96092c021b05c91a9a092c021b05c91ad9092c021b057b1a1c092c021b05a71a91092c021b051a9a1c092c021b051a9aae092c021b051a9a91092c021b051a9ac8
  | 7, 9 => 0x92c021b5f051a91092c021b5f051ac8092c021b5f051a7f092c021b5f051ab9092c021b5f051a56092c021b5f051a8e092c021bd0051a1c092c021bcf051a91092c021b05951a9a092c021b05951ad9092c021b05951a11092c021b05951a1c092c021b05951ad5092c021b05951a57092c021b05951a91092c021b05951a6d
  | 7, 10 => 0x92c02171b051a16092c02171b051a90092c02171b051a68092c02171b051a8f092c021be15f051a092c021be1051a9a092c021be05f051a092c021b5fb6051a092c021b5fdf051a092c021b5fde051a092c021b5f051add092c021b5f051adc092c021b5f051adb092c021b5f051a1c092c021b5f051ad5092c021b5f051a80
  | 7, 11 => 0x92c3a021b051ace092c3a021b051ae3092c3a021b051a8b092c3a021b051a96092c6102601b051a092c02e21b5f051a092c02e21b05951a092c0218171b051a092c02181b5f051a092c0217691b051a092c02171b05951a092c02171b05411a092c02171b05711a092c02171b051a04092c02171b051a70092c02171b051a91
  | 7, 12 => 0x35092c021b051ac835092c021b051a9035092c021b051a5635092c021b051a8f35092c021b051ac735092c021b051ac6092c883a021b051a092c88021b5f051a092c3abe021b051a092c3a02171b051a092c3a021b051a9a092c3a021b051ae4092c3a021b051a11092c3a021b051a1c092c3a021b051a93092c3a021b051a57
  | 7, 13 => 0x73092c021b051a9673092c021b051ae673092c021b051ae535092c3a021b051a35092c02601b051a35092c021bcb051a35092c021be1051a35092c021b05ca1a35092c021b05951a35092c021b05411a35092c021b05c91a35092c021b051a1d35092c021b051a1c35092c021b051aae35092c021b051a9235092c021b051a91
  | 7, 14 => 0x73092c61021b051a73092c024a1b051a73092c02e21b051a73092c02171b051a73092c021b051ae773092c021b051a9a73092c021b051ad973092c021b051a1173092c021b051a9473092c021b051a1c73092c021b051ad573092c021b051a5773092c021b051a2473092c021b051a9173092c021b051a6d73092c021b051ab9
  | 7, 15 => 0xb873092c021b051ab8092c3a021b051a7473092c021b051a7235092c021b051a72092c02171b051a6f35092c021b051ab773092c021b051ab735092c021b051ab7092c021b5f051a7335092c021b051a
  | 8, 0 => 0x92c02171b051a0000092c021b5f051a0000092c021b05951a0000092c021b05411a0000092c021b051a9a0000092c021b051a110000092c021b051ab00000092c021b051a1c0000092c021b051aae0000092c021b051a570000092c021b051a910000092c021b051a900000092c021b051a6d0000092c021b051a8f0000092c021b051a960000004309021b051a
  | 8, 1 => 0x73092c021b051a000035092c021b051a0000092c3a021b051a
  | 9, 0 => 0x92c021b051a
  | _, _ => 0

def count : ℕ → ℕ
  | 2 => 1
  | 3 => 20
  | 4 => 65
  | 5 => 151
  | 6 => 266
  | 7 => 250
  | 8 => 19
  | 9 => 1
  | _ => 0

def table : Compact.PoolData := ⟨64,0x10000000000000001,8,dictionary,packed,count⟩
def startMask : ℕ := 0xfffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0fffefffefefaeca0
def poolHintsPage : ℕ → ℕ → ℕ
  | 2, 0 => 0x300ffd9000b8757b6003
  | 3, 0 => 0xf4e97fc027e87551834fcee0f8061f3cc364041e182ec4007be5e7b04c7678e36051e87c400083c988a200c344322180ce610db4021cb129440b194bfb581272893a481ce40ac82081c400fbe02383b767c042e8c68902cd6d095d079ab84268123521d72c266a09af3014537c08f080a1c7d420d13ecb0140e25d172b014ca4e2340508827c9e063100d2c02261fb4e080c4170e1907882a6d180e3
  | 4, 0 => 0x57175fc4269dbcd4070d3367b20c1a3c77320734485fc01e68902f4808d11f426201a0c2c102d33d4ede41a274474885ccc2518112197301c42012ca463c08058d7490accaf319809095623be28029ccfb008648424d098c8165a41a90fb63f03511efe3245263875ac83006e33e90698d516ae303137ad2864623b98888cc46d23e08088283702110d1939c266160b3709c020cb2b0018111d0a1c1
  | 4, 1 => 0x94ef1ac58726b9bc0cce4d51721c848617383938f621287e71e34eb018e2e91291414191ab83e3814b370247021a86820df8742a1d8be6913814379beb745c6f0fa278c4ddf32ff151bbbf2c031175f7a802e0ea06b9014dcb212516838b5d6e28170b8cc80a2e09dfb028dbe9e730a9b715f7c0936c942d06c6d0bb9b8dc191176d1603221baa1a0640f43c602c79f6907c589fbbe1e0ac9b9481e3
  | 4, 2 => 0xe6021b8347c940a78e8f87ab92019f05cd16193df0b390407b827ad094f610469111eab69263c3d39bdb8767a27fab8c8741d8cf1e9e831216081ce8451002796260e840f1f3cd51a863aa0082f3c3097105e37df9388546efa4b21b0ddcd3a0020b2a731850764a4f08446b28429110d3f27143d0a41a21836741d9a3858680528e061ceecb103a19ae1f3c1c734f6cc024661707e059cbbee12273
  | 4, 3 => 0xfcdbd500c3f6e9a9874fe465a8089facd3d4373f46c184283e49e0f8e0fc5f3c31a078ac5442e1eefc8586a7dd4b100d0fb0d70d0f9f3d9e1c163
  | 5, 0 => 0xfc533cfc01f3d81110c3745511a806a911e8b30cbebe854219784d9f4c2f86f117185db3126430bb41bd20016da5608402be5a91b085715765730a2e5882861445e91c4c252e18258848921e3c108d649d186118ef420081f0d512c8036ea2e450069151c1860b6d32860c153eb90718255e3e4100462018a0608a1e503840e3bd548981b85e884201b08a10a202983d180404676942980306f6283
  | 5, 1 => 0x2dc61ad12455b9a71d4cab3a240d09555fe42b12a4d0ccf26540429208ca5c9ad19894820ba32328ac6012864e2ce1a2c091ec042e1920470451021725c8b02422a8e9c00844d5338810721e293020971202c63e4272a58c78334e4998ec72c65331cd4c48aa437b49992c061cae72a88b40bb676114e36712a027a555204c4df6da1d1897837e3c312d4ea43c222b652154042d68f1118855ace8a2
  | 5, 2 => 0x4754c40fe08dbbaa80cd1b0c9d349a2f2ff21b04581d490428af51924410f0a6918021d86fa8e242c0fe12c481c30f90c102090f2b0201d5121f03df039032276e4d29480ec00fe4501d7abb28933a81548e4072ba2ca244e4cf8e3719c5d2da40237e7e2c6866d17909e8cd708d32b89a6026a8e333f3f8408067c59a130cc6cd3421118330e8540302fdc8ac25e2c3c1348bc279c2019719f000a1
  | 5, 3 => 0x5ed04f4ec0bd5c320d097960a04402edee687c35d9f0e10c0b62199984d6b776c1d8ad611f65b35a524b1060b16c68908d5aebfe2682adee425c055880dcb46aad45523414f2b001e8a9d757e1035385b04546a377bba005448c87200a84bbcc7704e57f992c29b8d521a0d359c8f381a6636866534c283686069687ae894d26bc8e47824ccad062148bbc703a29084ff82452065052c1a3cf566563
  | 5, 4 => 0x7ce10d9120f95c4a118defefcb2813da48ac53079428a0fe6f251959dcde418c64793c3f8ac39075a7aecc66eab0ca9401d0e94f301b9aac724b37318bdc840e3bfda0701c5fb9f029b8bca108827172ee4566e01a099785bfab0126135544606736a688b8f80d3ae540d4d9bb21d318b3488348c063abb289c2c3bda60ccd8488f5241b086684960608aa0d146c0a45d1f4580f814038afbb296523
  | 5, 5 => 0x9c35f44e8736704d08026bee073784c67ade293985c1f800730aa2fa1c6610065049ca8c4e6873936c67d24726bef20d8e4a4ead0f9c93d8508e091ecea898123819b804e3eb9fa4a9c7cf5068528eb2c6c9271a57a2884e30a6a52c145ea2b66238b7c6dc263131064820e228559331c3de68a8208634eec6e70ad68b0d4611e981431c22b0c07d27f6ad007a6fc56860305f844352b83ea485e123
  | 5, 6 => 0xb6cbc6c4876d33dd828ed785df441daef98e872b3d7cb4ca367497310cecd0b2a2d05989976063b248018bc7619ba99b86c232e617856daa862f3acb280122358fa1093c6aa09c540055251f0870aa08978b27529aae0986a29691440d3bc9f2580a7757041a74dd4571c8e99a8fd169d2dd5d2780a486b6c5a349037b10029097a9160d14f454273a16b9c11c3423709244a84419b1c9cfa565c153
  | 5, 7 => 0xd2e5fa8283a556c0950f41318b3b167e99aa7e3cdd483d0079aeead904f2fdb312f8e5a56e24a3c91c2309a38fcd451b4f1db86b269e32711e513c3c227c6058171779b0f0216403f16040508313bfc1b792077e10f09ccef8540f2e9deeee92340bdc8f0d0817a77680582f418e92f9de6d7f4043bc996790a176b9170c06e798410e1dcdff9e421b95d3c4481720cf40fcede2de54085bbd11e381
  | 5, 8 => 0xe68573c3c7ccc76902c79917963a072ca220341e520928047c9cf01910393263839871f29d44b2e34a044467c48d3f1d8f862e92379f0b88da352dfd78502e3bf2b65070b7d65512b16fa1f30101df3e158267be2d3fa1076ec9883686dbcc4c1a3dad873cd03b25ed3a10f62b7f8260ec490307b3d81d1849e7af7c2c11cf5b03b9478eacd3f4453d589ee46e3a67acc1acf4bd6dc409697a502081
  | 5, 9 => 0xfd04a1cf07f92f1ca0cfef80bb351fddbb20203fbb65f8383f349768b0fe59b1e0e9fc74390572f85ad7c641efdfe2154fdbbadc3f0fb040fe263f4d80511a7e91dda8a47d12059230fa1fa543b3f403a24227e4bddc1d43c7408c1187870ef20d1ed5ce0c1e7d9e4ad1407b04705271f5fa3368f3eb172342e7d3d7ee86cfa44943078f4734403e3e8b83d4fa1d1482781cf9f1c5f41173b13820b3
  | 5, 10 => 0xfffea49143ff07b6864ffb1df9408ff208ac383
  | 6, 0 => 0xa17f3890413ee92a34427c54d61104e70b43c3092f869ce012523e32402261e02b903da6885d307840642060d82bc378c19a527429831027cef0061d36d9800ab500a40c13d5f18018276d6ccf304af878a44093b533e88121c4f05901fb4b680103a7cee0e4071162b4000de3bf4a8819a8f6541027a4945a604401d9e080826e020900e384e3f301973e4dc003169918c4058af579980a30a2591
  | 6, 1 => 0x1614bf93002bfeaea68455cfc31898a91c5a44114bf6520c0289624a4084bbd3975988f77fe24211d8491386230b22148c43cc47821885ad1e0131077331802207a848ec440783d05887ccd10a800f4161d6021e3467a6883c47263480782fa01910e652640a61c7924bf0c34e6f23a105dc7ea4630ba1df20461734e523802e3ea546985932f28100ad56848621549b593c02a5a1f5a00536cb63e3
  | 6, 2 => 0x26045d91e04b80d0b7c095b33f64992048b6e402388eecc60460ce50fc08af49f138913df467d121a6db466242635919407ea20a3190fa8c66c131f15345b023b9294bb4875d9466e98eb331e6e31bf2918740369860b9486be03b1a18d24ab49101a3e78cfa434281f034c6623457510c80fb2fc018a6f1458630849f1cc860a1d13f18bc4226d4216bfd2dcc22d02a102cc58ce7a4b98b0e03c891
  | 6, 3 => 0x319694d2a662ffe6bec4c5800f29098afff27033124d3d1c661d8c32184c211c354097f1a66e902fd3a80c425f6483c040be786151197bc78a9c12f6a824b605d04a39ac8b8e50446016dd7503a32cffb883a2582313a68caf298a22995b463ca832a896319c053febc25c0a74b051e914c0444b33296df0884250d351038c9f509769093d3e84543276ae5d9824e2dab17889c3de82c09340140f91
  | 6, 4 => 0x3fa7f640e07f45bf0ec8fd48d87001fa468c6a03efa5657a67dd01394ccf9990e2901e9f8364033d2c5395c4771d803d84ec9e7e6981d61de2e623abea84b4475760b108ce970353391cbdb54f40392127cb246e8ee941ccdc48032b89b7cde2b9336e8ef0e466cb7d1910cd863897799b08890ba335ada399e26b2ad20244d21b1526199f2f24e5033d2c24b8666188b348cc9d95d561991c560792
  | 6, 5 => 0x4e0e5ecd849bc6e517c5362d59521a6bda048d04c831f8ae0988adea0012e0224340a5bbd044134a7e7192629409a033c927e3c5791a4e17ee65349bdd046e29349ee158526819248924c2fb8b63496f8281068ec9ed190d1caa1d7c123944e2213471bc458e28e1cad93c91bf040411a1d23047c3439523dd4286da67364d0d39527982172cd64f141e3e6db8681ddd306490390e3300a05532e2f1
  | 6, 6 => 0x5bc5c5c4a6b5b43684c567b6651b1acee9e47f159af6f0c26b22de39a8561d2014c92c3673e0b05857045120af45e4134d5e3884591ab9c798d9056bb7156e4ab809486855594112a9aaa3144e805514935186a9e0962189521979760aa0430edb053c3418a84a76c56c04d4e9af8368a98dd8caf252c91e4260a30ed1204d4461150f0a873038ee05099020ac4a02f349e8d3a76db738a74cfee0c0
  | 6, 7 => 0x683d48c246d0576c9c819f1be03a033d58723816798ab5cc0cf2fa29f819cdef40a1b3431749f36631614386cc35d9b00d9742e96d9b2e2f2aaf06561271660ca2b11b245931f315f9b21203485064069ad3a6c6d6dbb7458c54f448030892444d160c6ffcc24c071a7a2c98068e95803004d8c0805fdff89786be6fd896097c5e12051ae256104c25c3cb8df82b7e0f5350d6fb8d2698adf67e6ad1
  | 6, 8 => 0x748c999066e85afdb94dcf8e1a6283972d3a5637299469c46e4172380cdc8173c480b8de46074371b5b79304e2d3df0849c589d5681b829fd0b537044acc3c6e061bd278dbdaadb689b7898662406e61a40666dbbb0788cdb5115971836981661836cd0274a06d92ccf0f41b1749a131b5cada64706b716c8802d5d4a39145a71a8a3c8b4d6328f636933380946d256301541a2d6b85b9b427e2a642
  | 6, 9 => 0x7fd158d360ff9109294dfd29be0183fa36706d37f3e6c9986fc9a2b1dcdf86d693e83f0b3d67617dfafa5c40fbdd11b18df532cc4c0be7cf809b37bb1a3d024f76153adc5ecb7d85b13d6d7eaad37ac0c8a0e2f5377d880de583ec1f93c929700437904b9d8e4f174c60d4de2108a388bbfe376d0177c7c9d380eede9f1601dccf7a3c0bb7fedc64076f95c1f26ed3533988dd953b53303b0f28cae1
  | 6, 10 => 0x892e15994311fe8ea8ce235a2738844409b4583886a64d623104b58a2021f80302e8c3c4726b43876f575ba50ecc26264e1d2002301c3385c6ae085e5a780070bc8049ece15da392a042b42b871284fc47cce108e61da5060d4bba230c18f70cbb383107b9d2705a93a19ce0aa0c8541411f9cd0918218cedfc7040f100f86072f740c9c0d8ae2d51816807c783028d43200a0512746d1c0364c4a73
  | 6, 11 => 0x9203699b0723345617824616152f1c8a97f6e119149260ce322907fb8ce44fb550b0c88fe1887290e3819d472114a13eca416faa491c7e9272e518fa90a18211f4556938e3e29f2831c7619301538e6323d1411bac353206373b4a7c046d42ae6e18d339a9161194d73380e312fff551c60d0aa1008b9c94dcc715bddd30822b40d7398c54c0deb138a861d8f0714eb78a682281bc7208c4ed50eec3
  | 6, 12 => 0xa0e695cb6540dad0a1ce7d3635619cf7bba67629dfef3cc213bf8fd3fce7705a0501cec4cd04409ca232d26537fb6f120e6db4542d04dabda87229aa063c7e334c4219a8a69326d7d04d1c38e9639a1b180fe1342047b14a628d441d84c447e62e3986864cd633050d02c0a5fed1c0d1cb561fd08195456cd26128eb62074a4ee28f76149a432efd39340de50072676ee10ce4bbfae610c93422edf3
  | 6, 13 => 0xae606e60e15bfbf8afc6b7d76822156e7bb2e10adbb4cc2c75a5417ae82ae4c43148d4e4ce68a3a99df81f075325fe0882a5feff66154b08b5080a85a7d1947502fe6ba829d6c85488d399822f02a728dd19e14d58dc3502990c8c84952f9aa0ce3a571ac15c7496d99a0828ff2cc2c9d1d54fc410a39aa34b43471fd4220a8d914f229517c7186c0a2a691196744b1928a4e8682b07215086b76510
  | 6, 14 => 0xb8614ad1256f98acb7cadc9e532d1db700c4500b65a689be36c5ec12642d77b7d8485ab1e084e0b556e85c2569b1f0100ad2a1f37885a4a29a393b432728383680ab1bb02cfb2fd73959db06c6b0b361269a2165f3ff15cecb834a2d9d92a7b6422b238d007a7644baf11cec7cc4d721d8e9ffa420b14be21641622924a4cec437086f05878d8c763afb0d2d1435f1fb99dc2bb95326b1d76b3e6c51
  | 6, 15 => 0xc535539aa18a6078420f13f6e45996230e81033c3ff8256e1873ab70c8f0e41955e86171e3a611c23250cd25813de1ad82ffcb603f9dfbdf1afb3be51d20e617ca109be8ef8b00b2695efdbbe093bcac0586e7791d33a44ef2237c7a8ddf6008b10bbc3be5c8377585a89ceecba14079dd88f3a073baf269e0a1754ada9342ea31d6099dcf0d6ac73b97dd81b8372a4e0a182e23ff63a9dc3f5b41b1
  | 6, 16 => 0xd0064c16259fbbf1aacf3d86c5440e71fa30641ce076684219bf4059307367b53331e6abf8cbe3cd1675570799bf58284f335f75121e64d3e2721cc8b8159259848889bc72ff294089e51a55aaf1c9f62942e7937e3a98cf25759724064656be560c89181d081903ac3bb432023b91d9e3e4f78190c788ea10e38e39ad888f1b63d9621e345fc6943c665534ec18b74d525cb15c8e0479e2a3d467f2
  | 6, 17 => 0xdacf501ae7b57a4f124f6a650e1c1ecf1647093d9996b45e7b30c5425c765c15a7b8ec88590f73d8ac665e27b00589414f5b73cd7906b35fa42c1d5d1e3c3e3aaa5b83c07536376259ea14942983d40af01145a7cd2f9a0f4f54766a969879e2d02d2d41f4e67a4957a22c7491d5941868edc18132d1d35fdc27a36d5c944f46d035459e8d98e2e31d19ef2c303a2269d874342635e470e8088bac83
  | 6, 18 => 0xe7e3674567cedcb739cf9db3cf5a873a68c6f00e71ba9cb63cdfec80d879bab45408f33aa2e481e649ad89e7c9a8062b4b92342d0f9f2366ec883e43058c7a3c7e4412f838dc6e6348f10b48e5e1e1a8cf59a1c28b19a38b8411e46a9f054aeed32e099c01f43c10b2d2587817d9b4386fe60b86e2df4aff9f85bc627c9b0f755967431ee27276920dbf78980c7b7815bbd0f6e7e85011ed9f81cac0
  | 6, 19 => 0xf1ad87c921e2fcdea983c4408d771f87cf52d41f0df410187e0d88f9d07bf36113c877c26344c0ef81dcde07ded1013ccbbd5456108f775b26eb0eed73b4507dd59d72bcfba9c1a531f722986fb0ee28440f27dc0cedacc7b74983349f6d6d7c713eda8830b21daadff074fb255ad421f610a5aed3ebfb868141d3d00014c7a74b133a874dff10d71e940984fa7d27a154103a40502581f468007082
  | 6, 20 => 0xff32a719a7fd43923d4ffa39cc2f9ff3026e8d2fd97d34483faff318007ebfdf0798fd5cd9a1b3fa9c479127f38ac1bb47e60ef4351fcb9340dd0f96a231323f28d262a4fe01a27538fbe22a26f3f786b2c607eb6e0bb8cbd68a40151fa83630f81f4e3b44963e968063a0fcf5ded20079df90e2d1f3506088a1e5ad6eb14fca8917611f94f420d33f27392c461e48ddfad87c7cfdc56878ee84a6b3
  | 6, 21 => 0xfffe22cd83ffbf7eb1c3ff78314e17fccf6a780
  | 7, 0 => 0xd83a3d3241adad43bc4348eb00a0864c9f26a30c38ee45e21802a317042d52981508592cb01130b213a8e8215ca302808291fc62c983fd18a89307a1f4d6260f27deaf4c1aad14611833e4ba8230649644ce40b6c8d070415bfec5f182b17f4b730559e8dca40a4d0e90001473247c18266fd420104aa14ce4209002f34400e6a00760817dc806b0023cc8cae6044d0c2ecc056a4952000263a6f60
  | 7, 1 => 0x1dce9cd5e63a5ed41500734c163a80db334e1711b4e2f4022360590b74c6b9fd57208d4dce2b631a09b5832633ccb3838c63be475198c6c2f241217c7900f462f623e18805ce2e61808b512e8eb316309e8aa02c58ef24c45315063f90a52242f30144bb554e4285eadb5444f1ea7410094f2e673111ec24d6862394e5218c4323123d9882114a1600fec6919601d20312ac03a086842106e3434652
  | 7, 2 => 0x2cd6ebde4259a91503c4ad33147399577dc484329a4ab4f0252791f3bc8a4e6684481492fce21329071ac5004f9780a40c9d56915111342cd458325e05b9a804a4122b6049141797b191f078a3e123d89786e0476bc919888eaf9575111a571603322879d0e6444c790b04087029a54110c01d0da021478645823f56d1b84c7cdfa76908f9a1862901f2658d4a23ce17b108c7941df0c18efd3aca63
  | 7, 3 => 0x3b88c547667388613b8ce704a01181cd2b4c6c2394fe11446715d508d84e29fab3b91c4b86887238603e5a606dbf7bb400dab1f35009b300c266035fb5a0ec06b57d204ccd1eb663a01a27e6440333bf36d066665c87948ccb6de1789994e442e6231fd8a1186621c18be44c28f920c817decb21722f614ccce05e7e2eaa04ba84e8400172b65ab712de60e0a065b20601804b505094e99671a6c2e2
  | 7, 4 => 0x48c93f8c068f866021051e18a83e023abe6a96346f0f1d4628d7109194517568178822e908ab3145963bcaa68a70081b01133f54741a263d8ed134487b6c9608797549a010ccde6669a143c863a34222d28820827c2513c503b8b4451a060c52f113feda018267f7f512980fcddd77499f91428a423ec3a5d0a07c4f6eaa4cf77a256701ec5938a733d0945c7e079e3728840f36f971e19deb1c4791
  | 7, 5 => 0x57702ed3a0ae15d7994159756d4e8ab153a0951548daa0060a7722931cd4dea91540299f1a637352dffd0722a574a19c894acc077a9a93030293052580691c0a44fb201014373034f027b295a2c34ebfa6c3609d2a5ab34138d8e41382716a388714dd73581a49afda3098133c0b24a9a64a83a5434c4adcd4429860921c412e2602119a58f7eae514ace4f0222950125024d290023728251bd78df0
  | 7, 6 => 0x61e272d9c6c2fb69354d81b205688b0051287515f884d8e40be576d30cd7b27573d8af5ec000f25dc2e3cbe2bb751413c176b6995002ea0764cb35ced738a62b9bed0264172c889179ae2820c2d35b924e11c2b6649d9bcd6c89f76e82d71d3ad035a74d4db06b4dd8198c56699280282cc91040035935da1042b262ed1d0964a4a03c12c824be6f15872554902b0a5601e4d600c1c389abc13a04e1
  | 7, 7 => 0x6baed20a64d71169a501ad5aae4d13573672f006a0fe451a2d41068a44da7be720e1b445d024b368554c8ea4cf28ec09cd9da88a0e8b34b1ca3816601dad346ca58208f8993dccb0a1b266db84d36493909780c923da0345914b5b6c1321d04c6116431afcaa2c83f0a00858f8a637a1b1b42eae606349f8d902c664c88e418c09e3651b156b5a250627fcbd362c45bdca98587b4c7660b0f3ee6e23
  | 7, 8 => 0x7706700546edd67098c1da88ee5383b3e6e21b2764316c604ec17be194dd5aadf2b1ba74464bf374e032ddc2e985f8a505d21aaf2c0b9c7706101738798c5c0e6bbbf1b81cc1c976b83958d72641725e2e9060e475be33c9c376b84083851d7e4f27097b4c140e0d19baa41c115e0290b7d99a67436f8fd5c986deadff8685bce61b2f137736de1216d3fdaca60d9a573ae05b0a9f42c8b604f08780
  | 7, 9 => 0x835effcd870625618e0e0a3519679c0eae9a6a281bda3d1c7033c60150603a9d3230c06b1ae0d0807a8c96e4fea8ae974dfb45b37783f42d384307e69a95980fb887db081f6a8ce029beb12f06717d5b2dc826f882dab5c5f0d9583d0bdf0eec6d37b7160d420f5cd62264de772244b0bccea62df379012c0626f1644cb541e2a2c7050bbf713077177dc798fe0ef9a6eb6c9def0bf101bbd816a463
  | 7, 10 => 0x8c9cc4d523190c681bc23177c5678c61179cdd18bac1a42c717164fb94e2c8867271c58e7cee818b05b38c2715efd6a38a2a66ce480c533f08a4389ebb749471322f7b842263bdd621c4c4eb43b189464ad60711263b1f82219a256514399912eb186f49b99430de388ae86194c8b2e1c3287e435385f11b59850a855fb70214f7bf4d942908b67c3850653816709c19e3406127e2f6c04243792d22
  | 7, 11 => 0x964d57dd652b5d42a8c2565fb03b14a8ad428f394c35ad92129336aa8824fe4b75e1c9db61409193ab7f5267272e9a154a4c64d34f8492a23e9c191b1d35201234f049f8e45bd893b9c8837c6392910070c0c72109a7b7c6411459571c7dfca80238f56be45c71e710c050a3bd7dc32047755bef038e134342471b63f086c635d5da2b8469013a4f38cfc5047a719eaa1b80e33868d0b8465227c643
  | 7, 12 => 0xa24d4f59c344834a8ac688c60a4d0d06c54c8d3a0c12dc9014140fe1bca824f002e8503c15e513a0488fd3c3408aadb5ca7e69ce079cf870165f29ed67891013c585f3cc67782246c9ced8542b239d609c48e73a28ad94827299dd0c04e2f6ae2439beb220fa337a37326466b3b79330cd60546723996e9e916732acff9d4e632db64f8cc56d643e3975cd3ce672e705926ce5c2c3d6b9cb7721e493
  | 7, 13 => 0xac91bc81875731a2b202ac227b359d5770ce1d0aacea45361552c2d120aa9872d2d9550d4b2343a9b5821cc352af60204ea51a656e1d4a2dc0840a94351948351c971340aa1de1e2b953c945c5c0a7498c5da74decad8e869bbd462b0d345d9ac93a6141483854bda1e36c69614a2309529a54c303a4e4be9d4147990ab7868ed0f8009d1c5be46c1a3882ad525457646178e89b64b661d12cefee71
  | 7, 14 => 0xb80726d14170015e0d42df9d2f6d85b7fd48433b6b10c5ce56c7ebb25c6d84c9e2f9daee7d44c1b5c9dd82076a29c8a58ad14efb560da22aaa9e2b3e1c8030566b6cfb90ecac05a438594b6e81e3b256a19b2164888f044ac4cfcc780d8883e8853b103cd4a8560acf71fcebfc6f5439d7f2994f22af69e3d7275e38701dc2bba1694f9d767876e91ae6c73ca455c77720f42b414584b85681256602
  | 7, 15 => 0xc42e9f48a78354acb68f065b7f041e0bcba0293c1438d1223815dcfa00b0220590f9e00e07edb3bfea711be57f5dbda942fe30e5708dfc2cbed60bf471e8cc77e81403142fcc8fc2b8df6f5fa811bebfd704837d41539d86f89aa34e05eeafe22d1bd4d5b5d877a17a3298af2414d241ddbddfa923bacc6751e374a354894ee7234e381dcc6f1e1d2b91a9a4bc170cf331f42e1214c339dc04474d23
  | 7, 16 => 0xd0676312659ffb85188f3de2a10f8e7844da471cee766c0e79d732938cf3ad68a1b1e753fd2b51ce3c15d1079c3ffe9e0f36dd25601e6c3fa4e70cd55688ba59965611a0f2f4e1162065e8f52bb0cba1340b63959044904727dd474c0e46057a902c7619582a18e6c25320b1b790b2d9e35e9fa1d3c65be190038ca271b38b190500558e2ff5b04d0c5f04c07e78adb65ad4f1538d86a1e25b036922
  | 7, 17 => 0xdb93a015e3b6c714110f6c3b7d021ed5fc622e1da6a1213a5b3eb9ca70f6726e66906c9827ac83d915859745b21b5d9687622e95509ec3d722ba0d85b0c0147afdf3f29c75ea4f3631eba3ae0b01d691f953c7acfb2028cb5905356f1eaafb201a3d537dc9e05aa428d8a0b535663388ea4d684e40d465240fa5a7fbee0c034fd0aa299e97d7d8822d1014f1007a1ea5c3bcf4340d9561e865640610
  | 7, 18 => 0xe99c295e41d327b22dc3a076ae2d873ac19a440e71b838507cbeadf2487976beb799f2cc42c0f0e57f1812e7ca965c34cf93adb50a9f26efe8642e478091385c8b8d33b47916a3d159f1eff4c1b3e389815ac7c6ab8e18cb89bd784d070ff526983e1ed39cd41c345f6070382e109140eff57faab2dfc0ef1707bdad8abc8f7b045b599ef396083e0dd5ec09d47b976502483712cfe3f8ee1e090f73
  | 7, 19 => 0xf23e658e61e47177a94fc7bea378978f29e0ab3f15aa54667e24e73ba43c3866e3e9f7df768e01efaa198145dded643003bb8795088775cafc972ee94d14ba3db789e1a4fb6d160508f6916f0181ed0b12d5a7d8ddee9a87b15247551f627b1ce63ec030d4783d7d62f374baf998d68975eafe8140eb31e35d43d5de5da7cbab07a32e1756073cf93eaae428647d54ce785cfa88c116a97503b50e92
  | 7, 20 => 0xfc82c7d4a5f7b07817c3ea634b3487d40584590fa6e130dc7f4d382898fe86aee3b1fd09826a12f9a88c9c85f307102303e531451c9fca3c8a960f8e6cd5623f16dc3888fe1d19c3007bdd510c53f7966b5507ef0480af83ddfe452c97bac60a812f65a9b5941ec6c25b887d76947718facec400d3f553298b47e967b8ab87d28d276787a37dd8943f44a09d747e7006f1c4bcdf2ec758794f00ca03
  | 7, 21 => 0x3ff48fa319ff7948e860fe88ca8bc3fb666a384bf6a80a4a17e9b466f32
  | 8, 0 => 0x93f47f40c1209db9838a32bc74020c33cfa00e07e6672c0e6f94e1403cddafefc019395a8b40636fa47d8206de85398145a32ddc011b3519d80d1643e6d4160c627e8024d75a3ce069aaa44e01234e44668226989dff00852b935a03924759540303e2b1b81c271edf6004ce2630d0189774c240032a407d02205080ae010c9f6e63048116106008021418b80a613336f01c42645770080214c1e0a3
  | 8, 1 => 0x7f48924092df0517806788570e81c2c203a2048d5d4892083a9e7658187449233038e72e1bd059cdcae06121
  | 9, 0 => 0xa51256003
  | _, _ => 0

def poolHintsCount : ℕ → ℕ
  | 2 => 2
  | 3 => 32
  | 4 => 108
  | 5 => 324
  | 6 => 676
  | 7 => 678
  | 8 => 41
  | 9 => 1
  | _ => 0

def poolHints : Compact.CodeBook := ⟨26,13,poolHintsPage, poolHintsCount⟩

def terminalHintsBuckets : ℕ → ℕ
  | 3 => 3
  | 4 => 29
  | 5 => 317
  | 6 => 2356
  | 7 => 839
  | 8 => 7
  | _ => 0

def terminalHintsSlots : ℕ → ℕ
  | 3 => 15
  | 4 => 125
  | 5 => 1350
  | 6 => 10034
  | 7 => 3573
  | 8 => 36
  | _ => 0

def terminalHintsShift : ℕ → ℕ → ℕ
  | 3, 0 => 0x0
  | 4, 0 => 0x50005000500010006000000010000000500040001000400010004000100080000000000010004000100000003000100000002000000000002
  | 5, 0 => 0x700040000000f000200020005000a0006000000030001000900000004000900000001000000000006000a0001000100000000000500000011000100000003
  | 5, 1 => 0x50001000100000006000000010000000100010000000000040000000000000006000000010003000a00000001000100000002000b00000000000100000002
  | 5, 2 => 0x40000000e000000040012000000050000000b000200020001000000020002000200090004000400040001000000000000000100080001000000070001
  | 5, 3 => 0xc000a00000002000300030001001c000000010001000000050004000100000007000000010000001300040003000b0001000d00000001000300010002
  | 5, 4 => 0x20005000900060010000300000000000100000000000400000000001100000001000200010005000000000002000000010008000a00020001000500000007
  | 5, 5 => 0x9000e0000000a000300020004000000010000001400100001000200080003000300180000000000000003000e000300160001000b0009000400000003000c
  | 5, 6 => 0x10002000d0003001000000002000500010002000000020001000400010028000400020000000000000000000100230006000100050002000d00030009
  | 5, 7 => 0x110007000d00050001000e00080000000000000000000300080009000000000004000000000007000000020008000000010000000800050000000200050004
  | 5, 8 => 0x10001e0000000b00270004000d0006000000000002000300060000002a0001000c00000000001400130002000c00000003000000070004000f000b000d
  | 5, 9 => 0x110007000e000a0007000000020001000000030002000b0003001000000019000a00170013000300020002000a0010000b0003000d00010000
  | 6, 0 => 0x1000a000000010002000300010000000000000000000e00060004000100070001000100000007000a0000000d000200000000000000020001000300000003
  | 6, 1 => 0x400000000000100050000000700000004000600010002001700040005000000000001001300020000000800030010000300010005000000000004000f0000
  | 6, 2 => 0x2000e000800070000000400010000000000010000000400010002000000000000000200020000000600030000000700060001000000000003000000000009
  | 6, 3 => 0x130001000000010006000700000001000400000000000000020008000000030001000000080002000e00000001000000050000000000000006000200000005
  | 6, 4 => 0x500020006000a0000001300000001000600030004000d00050007000100010004000300010000000200040002000000020000000300060003000100010009
  | 6, 5 => 0x7000500010007000200030000000600000000000100000000000600090000000900020004000000030004000000040001000800030002000100040009
  | 6, 6 => 0x3000200030000000000010008000000000000000200060006000000020000000600040000000700010007000000000001000c000000050010000000010000
  | 6, 7 => 0x30003000400000000000000020007000200040000000100010000000500020002000000000001000500040001000100010000000100120000000c0000
  | 6, 8 => 0x1000000020000000800030002000300010000000000090000000f000000040001000f000100050001000300000001000100010000000100000001
  | 6, 9 => 0xf00000001000100000001000000020000000000090000000e0000000900070001000000000005000000080001000100010000000300000000000400000000
  | 6, 10 => 0x2000e000f000200050001000200000000000100430014000000010000000100000007000000000003000200070002000900000005000a0000000000000000
  | 6, 11 => 0x20001000400030002000100040012000e0000000000000000000e000000000002000100020005000000020005000100050004000700000001000000040002
  | 6, 12 => 0x9000c000000010000000d000000000000000200020002000200000000000f000100000000000300010000000100060005000100030001000000060001
  | 6, 13 => 0xa000c000000010000000000020000000500050002000b00070000000200060000000700190001000200050002000200000003000300000001000000010004
  | 6, 14 => 0x300020003002000010004000100030001000000020000001c0000000100000000000300020002000100000000000f00000000000000000004000400070002
  | 6, 15 => 0x7000200050001000000000003000a00000001002500020001001100070000001000020004000000010008000000030001000f000100000005000b0002
  | 6, 16 => 0x1200030000000100080001000000000001000600120000000600050000000000010003000200030000000b000e00000001000400030003000000140000
  | 6, 17 => 0x300000004000b000000080001000000010001000000010000000a00020006000400000001000a000000000000000000000002000000000010000400010002
  | 6, 18 => 0x20001000200000003000300000000002400010001000d0006001000000003001000020008000100000015000300020008000200000007000000040004
  | 6, 19 => 0xa00010002000000000001000f0002000000000000000100060001000000040000000100010000000000020003000a0017000000040006000200000003
  | 6, 20 => 0x1000100030003000100030003000600000012000500020002000100010009000100010006000200050002000000010000000000010009000100010002
  | 6, 21 => 0x4000300080000000200020000000200020000000a0000000b000e000100000002000200000006000b00050006000000000000000100030002000200030006
  | 6, 22 => 0x1003300000001000100000001000100000000000500070000000200000005000500110007000500020002000a00090000001000000000000400000001
  | 6, 23 => 0x600000000000100000000000200040002000300080002000000070003000d00010005000000020002000100070000000200040000000e0009
  | 6, 24 => 0x50000000900040000000b001100000000001700030004000e0002000000030000000000000001000100180005000300030008000800020001000100000000
  | 6, 25 => 0x1000000030002000c0000000100000001000000030004000000000001000200000004000200000001000400010000000600000001000d0004000000000006
  | 6, 26 => 0x3000300090019000b0007000000000004000000010000000500030009000a00000002000600100007000a000e000000090007000300020001000000120000
  | 6, 27 => 0x10011000100050001000f000f000f00030000000000000000000d000400000000000100010000000100030001000b00060001000b0000000400000000
  | 6, 28 => 0x1000200010000000000000006001a000900010000000600000000000900020005000100000001000000010003000c000100090000000000000000000c
  | 6, 29 => 0x100000002000400000000000000000006000000020000000700000000000000000000000b00010003000a00000001000c00020000000200000000000f0002
  | 6, 30 => 0xf000000070004000600050000000000030005000000070009001700070001000100000002000200000000000c000100000001000a000a0000000b00020009
  | 6, 31 => 0x70003000300010001000000020002000d0005000600030004000500050002000a00080007000100010000000400020000000000060002000000000000
  | 6, 32 => 0x3000000070000000200140000000e0000000000000005000400050001000c00090002000c000b00000001001100060000000000050001000100000002
  | 6, 33 => 0x70008000300000008000500000004000000040006001000020000000100020001000d00060000000900000001000400000002000400000000000000000003
  | 6, 34 => 0x8000a00030027001100050000000d00000008001000020001000000040001000a0001000000030002000100040002000c00020001000400000008000e0001
  | 6, 35 => 0x40001000800000006000400030008000000030004000000070000001600030017000900000001000100020000000100000001000500020008000100010001
  | 6, 36 => 0x800230000000100000002000d00000000000200090000000200020000000600060000000100000004000000240009000200000003000100060002000b0006
  | 6, 37 => 0x30009001a000100080002000b0001000300000011000f0003000100050001000e000000020003000a00020005001000010003000100030001000000010003
  | 6, 38 => 0x8000a000000020005000100010001000400000007000400040011000400010000000700000002000500020010000000000000000200000003000d000a0012
  | 6, 39 => 0x400100005000100090000000b0001000200000000000000000003000e00070000000200020002000600000000000600040000000200040000000300030000
  | 6, 40 => 0x1f0001000c000c0004000300000007000d00000000000000010000000600030001000000040003000100030000001800000011000100000003
  | 6, 41 => 0x110000000000000003000f000400000007001f00000004000500000002000700000001000900160004000200000005000100000002000200050000
  | 6, 42 => 0x500140003001a000d000200000002000200000006000100010000000b00100000000000040008000000000000000d00120001000d0006000c000000000003
  | 6, 43 => 0x5000200010009000400020002001300050000000100040002000a00000000000300320000000200000013000200000000000a00000002000a000600020007
  | 6, 44 => 0x800030002000700140004000e00150004001700020003000300060000000000130001000c0000001100010001000000080000000000010004000100000003
  | 6, 45 => 0x1000700050006000a0002000000000000000000010024000800000001000e000800020008001e002a000200030000000100010004000a001000010000
  | 6, 46 => 0x1000500000003000200060006000d000200000005000400010000000100060001000000010005000c00050031000400000000000b00020019000000000028
  | 6, 47 => 0xa0001000000000001000b000d000000090001001200010001000100070002000700000001000c000b00010001000a0001000e000400010031000300020000
  | 6, 48 => 0x5000600010001000600010000001d0002002800000000000400020010000000070003000f000200020006000a00080008000100030003000100000007
  | 6, 49 => 0x30001000300020000000c000300000007000000000004000200080008000700020001000000190002000100030010000800000000000c0000000b0002000f
  | 6, 50 => 0x1100020002000a000200040007001300010003000500000000000100010000000000000000000e000000010022000900000005001500000003000000080001
  | 6, 51 => 0x3000000020000000100200006000200020006000100040005000100040000001700000002000b000500020001000000000010000c000a000600040005
  | 6, 52 => 0x2000d000c0003000200090012000600040009000f00020000000c00000002000000150001000000130015000c000c000400020001000400120000
  | 6, 53 => 0xd000000020006000100010006000e00050000000000070006000000000003000900000001000200010003000200000001000b0004001300040000000c0012
  | 6, 54 => 0x20000000000020005000c00080000000a00000002000e000a0000000b0000000d00010006000000000001000a00030004000800010003000200150002
  | 6, 55 => 0x2000a000700000000002300000002002200040001000300000012000000020001000e00020000001300000005000000120004000000010014000000080000
  | 6, 56 => 0x2000c0001000c0013000400000000001300090000000200050005000f00100003001400000026000000090002000b00060009001a00000002000300000007
  | 6, 57 => 0xe000600090007000500020000000c001700070005000e00260008000700000004000900080000000000010010001200050000001300010003001400000000
  | 6, 58 => 0x7000a0005000000010001000300160001000000000000001100000002001f000c000500040000000300090003000000000011001000030002000100000001
  | 6, 59 => 0x100010001000300050000000c000000000003000f0000000200010000000f000f000100090001000100000004000000000000000700020002000800070004
  | 6, 60 => 0x1d000b000a00060000000c0009000300130010000500060005000100050000000900040002000400020002000f0001000100000000000000050000002b0001
  | 6, 61 => 0x10000001000000009001c00080003000100010000000000000005001c000a0002000b000200000001004800010002000000020016000100050000001a0008
  | 6, 62 => 0x200004000300110008000100010003000c002a0011001b000500060004000f000b0005000300000001000300020000000a000300000004000400040004
  | 6, 63 => 0x5000500010001000f000b00060002000600070012000000010004000000000000000300000000000000020000000a00030001002c0002001d0001000e001a
  | 6, 64 => 0x230000000100020005000000010009000000530003000100020001000300030000000300030005000e00000000000d0001000200140001000d000200070000
  | 6, 65 => 0x20000000000020001000b00010007000500030001000b000f000400010008000c000e00000004000000140009000000050001000000040000000d000a001c
  | 6, 66 => 0x17000200000006000b00000000000000020017000f000000030013000000040000001100050003000500030000000700000005000600000004000400020001
  | 6, 67 => 0x200020019000000080002000e000000000011000c00000001000100020013000800000000000700000000000b0006000e0003000100200009000000010007
  | 6, 68 => 0x600020001000100060015000a00020001000b00010003001f00230008001600040005000300060005002700060001000b00060005000300030001001f0003
  | 6, 69 => 0x20000000800000003000200000000000500020000000200000000000b000b001100240003000200050000000200010000001500260002000100040000000c
  | 6, 70 => 0x20000000800040000000400110010000f000400060000003b000a00020005000a00010044001300110001000000010006000a000000120010000000020005
  | 6, 71 => 0x19000000020000000900010009001c0000001b00030000000300030004000500130020000400100000000300090004002c000800030002000b00010001
  | 6, 72 => 0x400080015000e0004000200000013000100030005001b001c00010006000400100001000500020000000d000500200002002200000001000600040003
  | 6, 73 => 0x4001b000000050004003200040001001000070013000a00070001002f00080000000c
  | 7, 0 => 0x40007000000080000000000000001000000040001000100010006000000000002000000050002000000020000000000010001000600030002000a
  | 7, 1 => 0x8000000060005000b000000000005000a0001000100000000000100000000000200010006000500010000000800080001000000000003000000040000
  | 7, 2 => 0xf000600010001000000000000000300000001000200060000000b0002000100010000000000140003000000000001000100010002000a001200030000000c
  | 7, 3 => 0x20000000200060002001c000300010005000300000003000400010000000000030000000100010000000000010002000100010001000200000000000a0002
  | 7, 4 => 0x3000d000500050007000400010000000100050000000000000003000c00130000000000000000000100010005000400030008001700060005000000050000
  | 7, 5 => 0x1300040006000000010002000000060001000100040001000100010004000200000005000c0002000300020001000000020000000000010002000000050000
  | 7, 6 => 0x90010000700000006000a00000003000000030000000300030005000000000011000000020003000000070005000500020001000400020006000000010005
  | 7, 7 => 0x1100010001000400050003000000030002000600030007000700040000000e0015000e00020002000900030000000300000007000100010006000000070001
  | 7, 8 => 0x100000002000300010009000d0000000000050004000f0002000000000000000200030008000300010014000e00040002000200030001000d00060000
  | 7, 9 => 0x11000500000001000100010003001200090005000900010000000200080001000200030000000000030005000300070000000300000011000200000004
  | 7, 10 => 0x10000000000020000000100110001000000000000000a00020001000000000000000200010001000000010002000300000000000000030013000100030003
  | 7, 11 => 0xd00000000000100080001000e00000000000100000000000c0000000c000000020001001500040000000600010000000000020003000300000004000c
  | 7, 12 => 0x2000000020000000500000003000300050000000300000003000a000000080002000c0000000000100002000800000001000000000007000100030008
  | 7, 13 => 0x2000100240003000e0001000200000008000b000100000008000200000002000200100000001d000400130000000000020002000000000000000700020009
  | 7, 14 => 0x500080003000000030009000000000000001700030000000200000002000e000100010001000500090005000a00000006000000030004000400000000
  | 7, 15 => 0x10001000000010007000600150000000500000000000000000000000f000000010000000200000025000f00000001000e000a00000003000200050000
  | 7, 16 => 0x50000000200120000000c0009001000000001002400020001000000120025000b00020004000600000004000000000000000000180001000000090001
  | 7, 17 => 0x2000b000100000001001e0000000500000000000300000002000400050003000100000002000100090002001c000000240007000200030009000300000002
  | 7, 18 => 0x60015000200010000000300110007000300070003000100000000000000030003000000020015000c00000000000100040001000100020025001100000004
  | 7, 19 => 0x100000019001200210001000a000200000000000200010000000b000000020002000200050006000a00000000001000010002000100000000000200000016
  | 7, 20 => 0x70006000600040004000700050005000200040010000100020001000a000e0006001b00010007000100070000000200020006000100030000000100030004
  | 7, 21 => 0x2000200040009000300050000000700000009000a00010003000b00000001000000000001000000020002000000070017000c000200080005
  | 7, 22 => 0x700010024000a0007002000070000000000030000000900000005000b00060001000300050008000e0010000b000600020000001900010000001900030000
  | 7, 23 => 0xe0023000000000000000b001200000007000b000200090001000700010000000100010012000c000000010000000100080002000000040000000c00040009
  | 7, 24 => 0x1000a0003000000120002000100030000000a00050000000000090000000c00000001000600380002000500240008000b000100040023001d00030000
  | 7, 25 => 0x50022000e00080002002d0010000000110014000a0004000900000002000b0008000900000015001e0005000300000005000100030001002300020006
  | 7, 26 => 0x1000090003000a000500050006
  | 8, 0 => 0x100000002000300000002
  | _, _ => 0

def terminalHintsRules : ℕ → ℕ → ℕ
  | 3, 0 => 0xf2f7f72ff77fff7
  | 4, 0 => 0x2f71f272fff27f5276327ff20137121f21001f612ff2fffff7ff77422ff73ff12227f021777f42f17ff2fff7210f117f700f222717220ff2f2f7771152f2f
  | 5, 0 => 0x1420f11120f1241ffff3301ff5f527f133113ffffff1fff241ff00f121ff02fff1117f103010f1418f1705221ff01217f11f11104f132fff40f5048301ff12f0
  | 5, 1 => 0x7f3fff7ff187320f42f086ff437f313848ffff014fffff13ff2fff8f1ff4075638ff32f0f1f2f2815fff001ff2113ff50131841134505118708003760f8ff770
  | 5, 2 => 0x3222201520f2f1ff430ff301ff7f27118210fff002f765f01108f42f302261f1017414074ff4f8f11050f02310202380221200181813f2ff72f04211ffff1011
  | 5, 3 => 0x804f800ffff5fff6f50f0ff00f10fff8302f34f10ff2fff0f1f3f72f280f631301580213108710003733701f31260f802870114267f1131114f1ff145f113f08
  | 5, 4 => 0x20ff4fff11727227f4322f0f80017f82f8fff840140012f06f1ffffff21ffff0f7fffff70f0ff00f18fff030331f407262601806f3f0fff63fff111fff0703ff
  | 5, 5 => 0xf36fff1ff683fffff72032230043ff831fff380f32fff030030477006020038703f01144010418001f16104313016312117315f1881108223661411033410370
  | 5, 6 => 0x566f18520026622032111248240361ff276f11f0ff82ffff7fff1f400173ff17fff131f1ff1232f0f3f1fff78f4412f7023132f00750313510270f38f0ffff02
  | 5, 7 => 0x5f442461240ff01ffff0ffffffff2ff1362005f2f20f35f1311037f2030108f17103f41230ff3fff02000027f20612f1270ff30fff4f43f3806f1f3323f52830
  | 5, 8 => 0xf11f2f78ffff228f31ff5f30ff8021f20ffff4f040f7f083f2023100ff42012f838f227710060f080800320480ff121f3011122f3316ff17681277220150ff03
  | 5, 9 => 0x608fff72761727f02718f5080380101f108f1112100f1f06428fff40f2f2f56f20ff51f3f180363224f31210f24f6ff0008f2ff71008fff147165f368f00030f
  | 5, 10 => 0xff044168f0f28ff21230f375171f4ffffff45f5fff7863057121f1fffff20826f04880
  | 6, 0 => 0x10f033fff300004ff48f01ffff0410352518f0f5ff07132ff028764ffffff018f06f000f40051f8f407fff60ffff01ff08f42f238f061051f62f4f1025fff03
  | 6, 1 => 0x85f100f01406f1f8ff01f1f1f02434021f124f2504104101630830257f507f2f56725100f2f502ff4334f601470033f0104ff0f812140020063f0f11063f01f1
  | 6, 2 => 0x328005150102101120870f0f40f385001432f0153030f5732f113f2343f0ffff260ff65f11103f0f1f02011f1030812f5441ff2ff21f013234f5011030351
  | 6, 3 => 0x600ff14614ff7101f8ffff70065102048818100f102ff0f14ff61ff533f427ff02004ffff02f1f006404f1ff02f623f611ffff3ff7f1830430fff0186f1f0030
  | 6, 4 => 0x8ff3462ff1107010f11ff31028fff84001f080f0230134f0f10f40f00ff5f0f173ff671f03f1153ff06200004631014f40002f210f11f20f030f28443fff200f
  | 6, 5 => 0x1406500ff0f051720f020031100120fff2131120f818301100fff47103030ff431f8400f43ff11f01002040f1fffffff440f4121ff3344f035fff10ff032f4f1
  | 6, 6 => 0xff00136f3f1f1ff53f16ff61fff3ff50803f0ff12f7f41ff1f40331ff4111211045fffff3ffff221ff1fff8221310373043760101751120103061310352011f0
  | 6, 7 => 0xf2f2116161f183f3f4122f3118ff04ffff200ff32fff13fff86fff10fff1005f2f1f66ffff448ff0f8f0f1f5230ffff1ff001f130811f8ff064ff21002f142f
  | 6, 8 => 0x503071f602fffff4231150210ff31180313513f3f60441751030131f0f11484317101010114408020f100604340133ff313385303000064118f00402308ff08
  | 6, 9 => 0x433086024300f0423100f261053f54f1fff1111f3300453081171f1060f0ff1fffff50f01f21f21f01141ffffff1f223f05640f1f0f0fffffff6ff0f346f74f
  | 6, 10 => 0xffff70ffff2ff231fff27fff501547050150f1f3f317fff11f2f3f2f1121831731364ff10433612f4f057065200041016331011111000ff41814033f20350111
  | 6, 11 => 0xf11711304600ff6380858730814017113634121001106201f40ffff1ff6142033f030fff00540ff03f1181f2ffffff03012f2133200f11f1126f1f1411233ff
  | 6, 12 => 0x51f4f410f8f54fff310347ff5ff10f3f2f83f70ff073383301111110f0321101f3f1f14ff11ff035112ff4f7fffff360045510fff1f0ffff5321f3fffffff11
  | 6, 13 => 0x10fff4f6f20208fff3ff1fff37451f3446186240ff4ff21ff3088310432410ff363382f2070ff8ff14011100100250441101ffff33134f0f153634ff0f343fff
  | 6, 14 => 0xf0601005f4f111136831f3f5f3ff603f02fff30f1ff3108111101014001222260f2f334181216704f0f1f0ff4f6332213f35008ffff07ff1ff1410040321f4ff
  | 6, 15 => 0x1ff3f2fffff02fffffff311411f034f1ff05ff6f1ff1f03f23665f2ff4042fff00ffff1fff311fff2f03f0ff40ff10f10ffff1ff8f32840ff71f845f44f34101
  | 6, 16 => 0x14f340132ff20001330f013fffff4f2ffffff2fff14ff0023413818ff0014f1fff523f0ff21ff1ff6f62f600084106f3f1041f07410021ffff4f4ffff31f0fff
  | 6, 17 => 0xf3735f10f606f6001ff5581ffff0262fffff020711036f16120141f084f1f3ff01ff11f233ff1231f20f421f1f031ff310f440f8f73804002015030051010083
  | 6, 18 => 0xfffff141fff1f3f0185f114330113f81f2f8351701030f1f30f00121008011518010313100133010630404520130118614036050f23ffff0f666f76f1f3ff81
  | 6, 19 => 0xf6ff8006184f4013282274f65f1f03284fff21ff1ff731083010f81356101f13f08003ff311110ff71005f141ff11fff1f116603f0112110f630f406110f0113
  | 6, 20 => 0x301fffff3003f34f11ff2ff15f0f101810ff6f0f8f2325f731062f00f51145113430ff0160f805ff01f0ff7320350f30115511174f0008001201000440f6f812
  | 6, 21 => 0xff0fffff0401f1ff200313f230140608010f0f041f45ff1ff4ff01f1f1f031304103200683020080601002305000312400310800008111210003f014f5101411
  | 6, 22 => 0xf02fff1ff2801ff1ffff1143ff3f311204ff5150ff1383100ff5f02ff3f42ff411ff10f23013f3ff1ff6f10ff411ff02404f01322f3f33f3f01f04f812663fff
  | 6, 23 => 0x2ff10001f0113f4100101f38001151012181f031f4f203f04008110070f863ff463ff0212f27f20004f4ff23ff41f2fff4200080f22f43f06f1f1f16ff5323f
  | 6, 24 => 0x4446006681000810f0f5f0fff00f4f620fff1f32f18513f0ff031031f006f1183557f055765111420f1008020ff08f4701000010332130340500f334f13f131
  | 6, 25 => 0x705f360211ff1f8ffffffffffff41f081ffffff37f00060508f810fff300f80001f04351ff1050f6f010f34101434411210f11f7031034013311147301002803
  | 6, 26 => 0x4fff1f30fff2fff43240103063010ff80323033501ff40040030f8f10224604f40010606008884fff010ffff0f310000ff13fffff700344f6007431364040120
  | 6, 27 => 0xffff817f01f0f2310f100ff022ff01415ff1430140f1106036122010306000f8f00203000331f3648180f051f130fffff0203ffff1f42f410013f6f1f1401f60
  | 6, 28 => 0x22834f0304f4ff0081f4336004ff7165320431511360500f2f1ff0ff0fff024013122111fff61123133011f031181010f15011ffff411f1f11fff20033860f7f
  | 6, 29 => 0xf842f7f004f0112f0041511005300338020136f0fff5603103112ff331f13f1f12102f2f80f24f1fff2101200533230f06ffff4ffff1fff0f01ff6ff14f230f3
  | 6, 30 => 0x10540001431111f684f4f0fff1f0f14f61023f00fff0f00ff0f141010f110305ff8f8ff00fffffff0fff0302ff0630f60f11141f1366ff361032150361134112
  | 6, 31 => 0xfff20f34f6f51ff1057f01f0044001f110110131183202566800310263f21f31717073f5600640f1263511f03f18024224013150f3f8ff0f2ff2ff134ffff2
  | 6, 32 => 0x8ff263012fff4f01ff11f10411f0f0100f33123f203478111f31301104f2131061830f10f100f3f001f007ff40fffff412f0f5020f670000006ffff1f8f14870
  | 6, 33 => 0x1f6ff1f0f10113fff1ff30f0ff8f30f120f11f800fff1f7fff5ff117600ff034fff141011480003241033f01600660011f24f0f2024413744f0fff21fff4f5f4
  | 6, 34 => 0xf101451f01f21ff6fff04f5f32030444135427113100f610ff04f4108502f0f32ffff11f0371140300140f01f00f008ff0ffffffff41f71fffff1ffff6f80f10
  | 6, 35 => 0x231333520f2f50ff4f22321f301ff10ff608044320f044f113f10f0820fffff0f2f86f100213021150f6ff04f8f0fff17ff55f2f2f0f2351f683ffff10f01142
  | 6, 36 => 0x4f4401f33f00f1481fff1ff381f10f1214fff4ff3f816ffff0fff286033f003431f2f225f0f18000f180fff0f101ff0026312303ff3fff117f23f430111ff55f
  | 6, 37 => 0x80f512f1ffff6fff6f607f4f060ff304131111ffffff1311260f11f300ff4ff3000ff0010f30f351f3f8f0f8401130f25f0f3537f1f0f04ff06ff0ff0f601622
  | 6, 38 => 0xf37ff36f484f1ff04fff0ff011263163f1fff25f26f33f3f05331100f1f104ff1fff4454012312f341ff1fff601f63f40050073f1ff421012f3fffff02fff01f
  | 6, 39 => 0x160f3111f7131f01304202211810017f1f6ff13f011ffff120fff1f063131357084ff141f0501ff1060428f01f0331f1304112402f70131312f43531338fff52
  | 6, 40 => 0x3f0f1fff2f388f440ff2042512308101651f2063328063f1f3f60001603211413113021440fff1f130110fff1f0f4f182003808fffffff2fff108ff0ff017fff
  | 6, 41 => 0x43f0f0ff00f0ff8f460f400004ff083f088ff00f33fff1fff0f1ff3ffff1f01300ff7fff010f420101fffff1f062ff141560651f0f60f00f6015f03110303002
  | 6, 42 => 0x3066f48211f11f1ff63240114f05f28ff20ff414f61f0340f6ff30f130f0ffff0800000040480f074ff041f442f4f2ffff013ff4f31205f0f52f01f641134510
  | 6, 43 => 0x453fff1161f0241ff1865f1048117f1ffff61f81ff0ff76f3852f3ff03f6ff1f1f001040f338f00632f1f607354621210184f10100088304233701300017532f
  | 6, 44 => 0x623040381113000fff06451f03326121146000100408344ff0f071522f8684ff842123ff010f08f5118f1fff0f4000320f405fff1f02ffff14310ff50fff0f2f
  | 6, 45 => 0xf04f04f0f40ff7ff22f0f11f3102130520f2f1f28614102f641406ff8f7613002233f1ffff0fff1ff5fff00ff183350ffffff6f321ff1f4f7f0f2f4403fffff
  | 6, 46 => 0xfff71f00348301f8204000f1040110302070081100100f081f18414f363103801f23433f02013401f02130f2f3f14500ff2f410f0031330112136f302f0f0540
  | 6, 47 => 0xf55f0f1f002132ff303f0201162300f105014341621865188370f81010ff1fffffffffffff3ff4011f306f11fff10ff00310026001f03f3fff00332264ffff0f
  | 6, 48 => 0x4f0ffffffffff212fff0fff5f1f53f080f1ff04ff8f731f610303f02543ff8f10f0f210ff561321f3f0f110310f4f0f1f066f32ff03fff251111413002162f1f
  | 6, 49 => 0xffff48f0ff2f00f64ffff0f4f713730fff0f46fff10203ff1f411f12331f444f6140f60ff18056304410016143081231ff50ff3f14f3415f6ff001041310210f
  | 6, 50 => 0x501601110603110205300708f81f2631413ffff464321f3f518fff120f6ff1f5f10f206f3100ffff01fff2f210f330f00f43f63f161f56104ff0f000f2f412f
  | 6, 51 => 0x603f311f443ff27ff012324f11f183581f0ffff4ff1f8840101f1331306100f30f0602338160020f6f10120f1128000217307234ff218200ffff1ff1ff18f300
  | 6, 52 => 0xf0200ff1ffff5f3ff10ff327230002ff1fff3ffff110ffff0ff1ffff0f50fff36401042115651102164111181fff044f12f8f02f071306f2ff51fff1fff881f8
  | 6, 53 => 0x1128300100ff33f7ff41ffff071045ff6ff51043618002060f0118663180331182321434433057ffff03ff3fffff1f00664f1ff31f2f2fff133332ff1f114001
  | 6, 54 => 0x51f0f08ff22103fffff6808f31fffff3054003410002f0f0f081ff1f0ff4ff4f257000f070ff04f4f1fff54f21ff400f1fff8ff4fff46f1040186233f1ff602
  | 6, 55 => 0x48248842081fff8f20032f1161f653570f40f1f05f7fff1fff040f03241300f2553f340401f331f58003ff14f1fff6fff4ff012ff11ff47220443ff4f8fff3
  | 6, 56 => 0x310202f20554124ffff4f344ff0fff211115336ff0400ffff410f3ff08ffff1f5f151f004f12244383ffff01f14f13611040765501f04f7f703110050f14fff3
  | 6, 57 => 0x4020624f0120580636170300f3000203806810351110ff014046ff0f0012ff10f053f31f1fff10f3f435f11111100024f101ff1ff308f011281072f141403434
  | 6, 58 => 0x305700671074141826f11f681f31f330f2f04fff1010f3003410105016211184f50f614ffff143ff450fff17f2101103ff4f14f0f2ff4532fffff1ff1f0021f2
  | 6, 59 => 0x1f0ff23f01211144ff810ff1ff4101f1142f1fff012f010132312f33f1ff6f04f21ff0002008064154101873f40f15f281f2f0ff14f202ff101ff4100f18ff1
  | 6, 60 => 0xf407100f014f4ff12004318154101fff3020117144653660f41021342120510403f00510265f8516f1f03ff1414430f1532fffff16f150ff3201001f101440f0
  | 6, 61 => 0x4ffff41112008881512212402128065013500413085f004f5526f313ff1f0ff13ffff4fff0f2f325112010f330fffff071f1264fff18ffffff1f5080f311141f
  | 6, 62 => 0x60410161230f0400f1f5220ff0f2ff3f855f12153f1611f08330400011843f1f05670800f37430030101415f45016fff53f30ffff050230f0ff001f4f2ff210f
  | 6, 63 => 0xf00f6f521ff145330f3f08ffff13f100f01102053106110300130037014356054ffff013332201fff34f311ff1134110f0f1210113010054111ff0100f400414
  | 6, 64 => 0x411fffff34ff600ff00ffffff220512071630181111108141111111034f10fffff12f1800f0042ff030fff030ffff1f7f0742332301030441f22800116308011
  | 6, 65 => 0x75016100ff01f0101f22671ff00602f11330f1ff30f1ff8010518f7fff0331026f4120f033ff11ff141304085106f6f70ff307f3100f0f1ffff3f0f3ff4f87f2
  | 6, 66 => 0xff6ff420f005f0ffffff6fff611fff00f1ff0fff338f0ff3ffffff5fff18f61f2ff48ff02f05fffff03ff00f10f5f08f67110861550011fff83006321ff10000
  | 6, 67 => 0x33f03fff4ff8f3ff56453143ffff0104f800213ff22f167121434780036516660ff110f0800f11f0505f6121655014105134000200ff4f345443f0fff0213ff4
  | 6, 68 => 0x2f10300f200010f57f06ff4ff08f1080220111ff100fff022fffff524fff040070f20fffff121ff0f0004f010ff841f010f13f63ff000f00ff4fff0f3ff6321
  | 6, 69 => 0x11f0416fff1ff05f3fffff0f401100f002ff0f01ffff6f80ff21f3fff6ffff2f1ff2310f0ff22081f1013234f21f31058fff6f0061416533ff1641302f300411
  | 6, 70 => 0x7312247434201008800700f3ff11f1fff10fff25043123f40400f004020f03ffffff2234ff201121ff0337210013f6ff3f365044100552112f1f12ffff3ffff0
  | 6, 71 => 0xffff18312f0ff028124030f21471101108f014110f007f366f6f400111f43f130ff41ff021f7f32f421f301030fff63264f1134f3f1814573048101000810300
  | 6, 72 => 0xf1004ff03f851ff0003133f3f0ffff111100430604f5ff0ff876f0f1ffff8ffff17ff22f05ff0f5000100130ff1ff30342ff100f1f504110311212f4ff0ff137
  | 6, 73 => 0xf612f2480810168023108f48f6ff03103f0f384f35110002104420f4111fff0f14f4f1fff040fff50f2011f3f01f175f1f12233f002f12523343200301ff50f0
  | 6, 74 => 0x16108131f1156ff1f0ff11ffff1f0404580f18864412011f3313011114104008212510764ff00741130410782f30067f100630101203781008030f0301f03123
  | 6, 75 => 0x22513f1f601f156230340100500173446236f06112205070f602010700561763181016fff1ff2fff32f5f027111ff14880140f304f10000f0611400104101500
  | 6, 76 => 0x5fff11f2204616ff2ffff6f1134408f23f06400211012f0100251064203112134f431f0f1f4f14311330f40301025f3f423041160018f4ff7ffff130034f30
  | 6, 77 => 0x825311154fff30f31432f32f18000ff03265f12001f40fff1f433f00702f1ff17306ff1400f160f0ff007040186322040402000441f013113017131001000031
  | 6, 78 => 0xf4fffff3f0ff2ffff5f60070fff06f0403f2f63f001fff21ff
  | 7, 0 => 0x1f603313406f316663f101ff33366630603314f4fff1ff00f616fff660f416661f604661ff0f634f1fff601f6fff14f0f4fff0461ff13663336046640661f060
  | 7, 1 => 0xff033616f01446316646441ff0f4f336f06366416f6444063461ff03f314601ff114106403116130401600601110316666061610110463030ff3f416f66f043f
  | 7, 2 => 0x61343314f433f16f400ffffff6f1ff1fff004fff464f604033fff10ffff0f6f3ffff1ff60114660ff6f03f0f0fff60f6f66031614f00f6f6414ff1606600ff11
  | 7, 3 => 0x4f66616330ffff30f4f616f3ff4336f1ff3fff06f6336f6f311636f00ffff01f1f6f4440031f0f116ff0f4166f06f6ff341f00610ff40166f4ff1f116f303614
  | 7, 4 => 0x6f0ff0fff40f36ff1616f63fff6613f11131600010413603136630364640114016ff01131041033f6f6064f34161306031666161664f6f466341034f63f66411
  | 7, 5 => 0x630f604f3f06f6fff3ff1ff34f1fffffff3ff10611616ffff61f40f0f3ff01fffff4f61f4141f1fff06ff60046f06664310f6f0f14f6f60f3f33f1161f001f0f
  | 7, 6 => 0x160616143f601f1f4f6ff63ff30f6f63330ff4f34f6f40041fffff14f0f1ffff0f136f6ff644634436606f3f1f01f360f3f30ffffff4400f00f6000011f1064f
  | 7, 7 => 0x6ff11ff1ff3161603063306611660606fff0ff6f6300136ff0f66f0010f611f6f641010f106f63f3066f0f4ff14641013f116f3ffff330066116fff31f63166
  | 7, 8 => 0x104110ff1fff116330ff6f6f14416f36ff44ffffff6f1036f61ff03666f661ff4fff43f16660f043ff61136f0f600f6ffffff6ff666ff00ff1000f1ffff31f6f
  | 7, 9 => 0x3466433046300663f016010036ff0ff4f6f3ff0ff034f04f3f436061f433f6f460fff10046ff3f4f0f34fff663f061f1f431f6000f3f0664660603f000f0f600
  | 7, 10 => 0x436140f3134ff30161ff16f4ff3f3f40604f4fffff330ffff6631ff604f0f663161ff34f30043430361130663f64011660f6f3f140060f63f166131ff414ff40
  | 7, 11 => 0xf0416660666f363f6ff40f304fff4f666103301f01ff1f4f0004f6ff3f03161660616614ff063ffff1f66ffff3fff0ff44f314f66ffff6410f603414101660ff
  | 7, 12 => 0xf03f134661fffff1014f3010f66101066063101311160010006143136f406ff6f44ff6ffff46111601f0ff631130660461304413f004663631364016f6046644
  | 7, 13 => 0x6640fff14603f3f4466313ff40f101f00f36001303f64146066f0110130f3f13f16fff161604303ff1fff6633603111611130346f36ffff006f0ff6041161636
  | 7, 14 => 0x616f061ff33363f64403061ff6ff616343106604010fff44601f3fff4ff66146f616f00446f03f6f66106013646f633666f3f610101f406f3f64ff1ffff64f06
  | 7, 15 => 0x1040063116006ff0f130063310f0f011fffff061ff66f6fff10ff13fff6f46f0fff4441316060ff46130634164f16f06ff033f311010f4f066001f160401604f
  | 7, 16 => 0x6430f6664141f016f4f60f36f660300f1404ff3310f0ffffff6003664161646606064166f300130ff1146f00066ff6360ff100646fff66461406111616f130f0
  | 7, 17 => 0x444f3ff6f6fffffff3ffffff3ff1f041031ff0366f6f3464ff6460ff4f66f11f600f3f00464ff4464164f16601430016316101f6600ff4311660f40140334636
  | 7, 18 => 0x336f06644364466f0f11301666fff63ff343ff0f0146344440f3160ffffff4f04fff106401f6f1ff3f630663ff34006f1ffff614f066366fff63666f40f66f01
  | 7, 19 => 0xff61fff6606f13f311630663f3f63666313f1ff066f6ff0fff63ff3f136ffffff316611f6116310631360140406f0104104f3ff3f61041636ff4fffff6106f1f
  | 7, 20 => 0x601f3f130604f1ff34f6004610f6f30144f6040166f41f1660036133f01636631f6ff3f6316f366f03060460f01f0f6f0636f3f6f06f3f6ff0f603f6ffffffff
  | 7, 21 => 0x414f0fff6f60ff043f311f01014fff464f6314106f10ffff44f3f3ffff6ff1ff43ff6f4f16644616660610116334043446f003f6146066640100ff46f36fff1
  | 7, 22 => 0xff6f01366fff6f166311ff13ff430f1163f0ff3131f4446fffff0f4134010f36f13f0ffff301f31316010604446400603400611f14f3416fffff0f346f61f131
  | 7, 23 => 0xf6ffff44600f43f0f3164146116333f63104066ffff143fff61601166466103f1f1f4016ff6460fff66f30ffffffff16ffff64f663040ff0163000161ff31f04
  | 7, 24 => 0x10f1f6043011f34f06066041436160614334ff646fff31411f416f01160100f441046f464f13ff4f3f6636f61f6ff340316613f03f66fff3f60043f663ff6f64
  | 7, 25 => 0xff046f0661f64f3366366036f66313f30f0306f664f31360f4f03061436661f3404f16f31f101443043f1f664fff4ff6f30f64430031fff60ffffffff03f6316
  | 7, 26 => 0xf003f646f000f6ff63f61106fff6640014f0f6116f130ff1fff303034340006361606f00f1ff0f633330ff1ff6646600360066006f36f000601f134636063646
  | 7, 27 => 0x4030403161114164160f4f4ffff6010004f63f6ffffff4166f600f04406634f0416403f61630f0f66f4f1f1f66f6f3f066ffff64f66036f1f3f66
  | 8, 0 => 0x6f6666ffff6666f666fffff6f666ff666f66
  | _, _ => 0

def terminalHints : Compact.CutIndex := ⟨terminalHintsBuckets,terminalHintsSlots,terminalHintsShift,terminalHintsRules⟩

def swap0x2 : Switch := ⟨3, 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 0x50505050505050505050505050505050⟩
def swap1x3 : Switch := ⟨6, 0xcc00cc00cc00cc00cc00cc00cc00cc, 0x33003300330033003300330033003300⟩

def switchPool : List (List Switch) := [[swap0x2], [swap0x2, swap1x3], [swap1x3], []]
def switches (i : ℕ) : List Switch := switchPool.getD i []

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem valid (j : ℕ) : ∀ s ∈ switches j, s.Valid := by
  intro s hs
  by_cases inRange : j < switchPool.length
  · have actual : switchPool[j] ∈ switchPool := List.getElem_mem inRange
    have checked : (switchPool.all fun xs => xs.all fun q =>
        @decide q.Valid (by unfold Switch.Valid; infer_instance)) = true := by decide +kernel
    rw [switches, List.getD_eq_getElem _ _ inRange] at hs
    letI : Decidable s.Valid := by unfold Switch.Valid; infer_instance
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked _ actual) s hs)
  · rw [switches, List.getD_eq_default _ _ (by omega)] at hs
    simp at hs

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem fixed (j : ℕ) : reindex (switches j) target = target := by
  by_cases inRange : j < switchPool.length
  · have checked : (switchPool.all fun moves => decide (reindex moves target = target)) = true := by decide +kernel
    rw [switches,List.getD_eq_getElem _ _ inRange]
    exact of_decide_eq_true (List.all_eq_true.mp checked _ (List.getElem_mem inRange))
  · rw [switches, List.getD_eq_default _ _ (by omega)]
    rfl

def salt : ℕ := 0xbf58476d1ce4e5b9

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
def rules : List (SixRules.Rule target) := [
  SixRules.knownRule target 0 false LeafAliases.wordSeed5 7
    [0x0, 0x44444444444444444444444444444444, 0x50505050505050505050505050505050, 0x55005500550055005500550055005500, 0x55550000555500005555000055550000, 0x55555555000000005555555500000000]
    [0x0, 0x44444444444444444444444444444444, 0x50505050505050505050505050505050, 0x55005500550055005500550055005500, 0x55550000555500005555000055550000, 0x55555555000000005555555500000000, 0x40404040404040404040404040404040, 0x4040404040404040404040404040404, 0x10101010101010101010101010101010, 0x54545454545454545454545454545454, 0x44004400440044004400440044004400, 0x440044004400440044004400440044, 0x11001100110011001100110011001100, 0x55445544554455445544554455445544, 0x44440000444400004444000044440000, 0x4444000044440000444400004444, 0x11110000111100001111000011110000, 0x55554444555544445555444455554444, 0x44444444000000004444444400000000, 0x444444440000000044444444, 0x11111111000000001111111100000000, 0x55555555444444445555555544444444, 0x50005000500050005000500050005000, 0x500050005000500050005000500050, 0x5000500050005000500050005000500, 0x55505550555055505550555055505550, 0x50500000505000005050000050500000, 0x5050000050500000505000005050, 0x5050000050500000505000005050000, 0x55555050555550505555505055555050, 0x50505050000000005050505000000000, 0x505050500000000050505050, 0x5050505000000000505050500000000, 0x55555555505050505555555550505050, 0x55000000550000005500000055000000, 0x5500000055000000550000005500, 0x550000005500000055000000550000, 0x55555500555555005555550055555500, 0x55005500000000005500550000000000, 0x550055000000000055005500, 0x550055000000000055005500000000, 0x55555555550055005555555555005500, 0x55550000000000005555000000000000, 0x555500000000000055550000, 0x5555000000000000555500000000, 0x55555555555500005555555555550000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafAliases.Seed5,
  SixRules.knownRule target 1 false LeafSeed10.target 7
    [0x0, 0x22222222222222222222222222222222, 0x30303030303030303030303030303030, 0x33003300330033003300330033003300, 0x33330000333300003333000033330000, 0x33333333000000003333333300000000]
    [0x22222222222222222222222222222222, 0x0, 0x20202020202020202020202020202020, 0x2020202020202020202020202020202, 0x10101010101010101010101010101010, 0x32323232323232323232323232323232, 0x22002200220022002200220022002200, 0x220022002200220022002200220022, 0x11001100110011001100110011001100, 0x33223322332233223322332233223322, 0x22220000222200002222000022220000, 0x2222000022220000222200002222, 0x11110000111100001111000011110000, 0x33332222333322223333222233332222, 0x22222222000000002222222200000000, 0x222222220000000022222222, 0x11111111000000001111111100000000, 0x33333333222222223333333322222222, 0x30303030303030303030303030303030, 0x33003300330033003300330033003300, 0x33330000333300003333000033330000, 0x33333333000000003333333300000000, 0x30003000300030003000300030003000, 0x300030003000300030003000300030, 0x3000300030003000300030003000300, 0x33303330333033303330333033303330, 0x30300000303000003030000030300000, 0x3030000030300000303000003030, 0x3030000030300000303000003030000, 0x33333030333330303333303033333030, 0x30303030000000003030303000000000, 0x303030300000000030303030, 0x3030303000000000303030300000000, 0x33333333303030303333333330303030, 0x33000000330000003300000033000000, 0x3300000033000000330000003300, 0x330000003300000033000000330000, 0x33333300333333003333330033333300, 0x33003300000000003300330000000000, 0x330033000000000033003300, 0x330033000000000033003300000000, 0x33333333330033003333333333003300, 0x33330000000000003333000000000000, 0x333300000000000033330000, 0x3333000000000000333300000000, 0x33333333333300003333333333330000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafSeed10.bound,
  SixRules.knownRule target 1 true LeafAliases.wordSeed11 6
    [0x0, 0x88888888888888888888888888888888, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00cc00cc00cc00cc00, 0xcccc0000cccc0000cccc0000cccc0000, 0xcccccccc00000000cccccccc00000000]
    [0x88888888888888888888888888888888, 0x0, 0x80808080808080808080808080808080, 0x8080808080808080808080808080808, 0x40404040404040404040404040404040, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, 0x88008800880088008800880088008800, 0x880088008800880088008800880088, 0x44004400440044004400440044004400, 0xcc88cc88cc88cc88cc88cc88cc88cc88, 0x88880000888800008888000088880000, 0x8888000088880000888800008888, 0x44440000444400004444000044440000, 0xcccc8888cccc8888cccc8888cccc8888, 0x88888888000000008888888800000000, 0x888888880000000088888888, 0x44444444000000004444444400000000, 0xcccccccc88888888cccccccc88888888, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00cc00cc00cc00cc00, 0xcccc0000cccc0000cccc0000cccc0000, 0xcccccccc00000000cccccccc00000000, 0xc000c000c000c000c000c000c000c000, 0xc000c000c000c000c000c000c000c0, 0xc000c000c000c000c000c000c000c00, 0xccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0, 0xc0c00000c0c00000c0c00000c0c00000, 0xc0c00000c0c00000c0c00000c0c0, 0xc0c00000c0c00000c0c00000c0c0000, 0xccccc0c0ccccc0c0ccccc0c0ccccc0c0, 0xc0c0c0c000000000c0c0c0c000000000, 0xc0c0c0c000000000c0c0c0c0, 0xc0c0c0c000000000c0c0c0c00000000, 0xccccccccc0c0c0c0ccccccccc0c0c0c0, 0xcc000000cc000000cc000000cc000000, 0xcc000000cc000000cc000000cc00, 0xcc000000cc000000cc000000cc0000, 0xcccccc00cccccc00cccccc00cccccc00, 0xcc00cc0000000000cc00cc0000000000, 0xcc00cc0000000000cc00cc00, 0xcc00cc0000000000cc00cc00000000, 0xcccccccccc00cc00cccccccccc00cc00, 0xcccc000000000000cccc000000000000, 0xcccc000000000000cccc0000, 0xcccc000000000000cccc00000000, 0xcccccccccccc0000cccccccccccc0000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafAliases.Seed11,
  SixRules.knownRule target 2 false LeafAliases.wordSeed12 7
    [0x0, 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 0xf000f000f000f000f000f000f000f00, 0xf0f00000f0f00000f0f00000f0f0000, 0xf0f0f0f000000000f0f0f0f00000000]
    [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 0x0, 0x8080808080808080808080808080808, 0x2020202020202020202020202020202, 0x4040404040404040404040404040404, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e, 0xa000a000a000a000a000a000a000a00, 0xa000a000a000a000a000a000a000a, 0x5000500050005000500050005000500, 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a, 0xa0a00000a0a00000a0a00000a0a0000, 0xa0a00000a0a00000a0a00000a0a, 0x5050000050500000505000005050000, 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a, 0xa0a0a0a000000000a0a0a0a00000000, 0xa0a0a0a000000000a0a0a0a, 0x5050505000000000505050500000000, 0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 0xc000c000c000c000c000c000c000c00, 0xc000c000c000c000c000c000c000c, 0x3000300030003000300030003000300, 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c, 0xc0c00000c0c00000c0c00000c0c0000, 0xc0c00000c0c00000c0c00000c0c, 0x3030000030300000303000003030000, 0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c, 0xc0c0c0c000000000c0c0c0c00000000, 0xc0c0c0c000000000c0c0c0c, 0x3030303000000000303030300000000, 0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c, 0xf000f000f000f000f000f000f000f00, 0xf0f00000f0f00000f0f00000f0f0000, 0xf0f0f0f000000000f0f0f0f00000000, 0xf0000000f0000000f0000000f000000, 0xf0000000f0000000f0000000f00, 0xf0000000f0000000f0000000f0000, 0xf0f0f000f0f0f000f0f0f000f0f0f00, 0xf000f00000000000f000f0000000000, 0xf000f00000000000f000f00, 0xf000f00000000000f000f00000000, 0xf0f0f0f0f000f000f0f0f0f0f000f00, 0xf0f0000000000000f0f000000000000, 0xf0f0000000000000f0f0000, 0xf0f0000000000000f0f00000000, 0xf0f0f0f0f0f00000f0f0f0f0f0f0000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafAliases.Seed12,
  SixRules.knownRule target 3 false LeafAliases.wordSeed13 7
    [0x0, 0xaa00aa00aa00aa00aa00aa00aa00aa, 0xcc00cc00cc00cc00cc00cc00cc00cc, 0xf000f000f000f000f000f000f000f0, 0xff000000ff000000ff000000ff0000, 0xff00ff0000000000ff00ff00000000]
    [0xaa00aa00aa00aa00aa00aa00aa00aa, 0x0, 0x880088008800880088008800880088, 0x220022002200220022002200220022, 0x440044004400440044004400440044, 0xee00ee00ee00ee00ee00ee00ee00ee, 0xa000a000a000a000a000a000a000a0, 0xa000a000a000a000a000a000a000a, 0x500050005000500050005000500050, 0xfa00fa00fa00fa00fa00fa00fa00fa, 0xaa000000aa000000aa000000aa0000, 0xaa000000aa000000aa000000aa, 0x550000005500000055000000550000, 0xff00aa00ff00aa00ff00aa00ff00aa, 0xaa00aa0000000000aa00aa00000000, 0xaa00aa0000000000aa00aa, 0x550055000000000055005500000000, 0xff00ff00aa00aa00ff00ff00aa00aa, 0xcc00cc00cc00cc00cc00cc00cc00cc, 0xc000c000c000c000c000c000c000c0, 0xc000c000c000c000c000c000c000c, 0x300030003000300030003000300030, 0xfc00fc00fc00fc00fc00fc00fc00fc, 0xcc000000cc000000cc000000cc0000, 0xcc000000cc000000cc000000cc, 0x330000003300000033000000330000, 0xff00cc00ff00cc00ff00cc00ff00cc, 0xcc00cc0000000000cc00cc00000000, 0xcc00cc0000000000cc00cc, 0x330033000000000033003300000000, 0xff00ff00cc00cc00ff00ff00cc00cc, 0xf000f000f000f000f000f000f000f0, 0xf0000000f0000000f0000000f00000, 0xf0000000f0000000f0000000f0, 0xf0000000f0000000f0000000f0000, 0xff00f000ff00f000ff00f000ff00f0, 0xf000f00000000000f000f000000000, 0xf000f00000000000f000f0, 0xf000f00000000000f000f00000000, 0xff00ff00f000f000ff00ff00f000f0, 0xff000000ff000000ff000000ff0000, 0xff00ff0000000000ff00ff00000000, 0xff00000000000000ff000000000000, 0xff00000000000000ff0000, 0xff00000000000000ff00000000, 0xff00ff00ff000000ff00ff00ff0000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafAliases.Seed13,
  SixRules.knownRule target 3 true ExampleSix.target 6
    [0x0, 0xaa00aa00aa00aa00aa00aa00aa00aa00, 0xcc00cc00cc00cc00cc00cc00cc00cc00, 0xf000f000f000f000f000f000f000f000, 0xff000000ff000000ff000000ff000000, 0xff00ff0000000000ff00ff0000000000]
    [0xaa00aa00aa00aa00aa00aa00aa00aa00, 0x0, 0x88008800880088008800880088008800, 0x22002200220022002200220022002200, 0x44004400440044004400440044004400, 0xee00ee00ee00ee00ee00ee00ee00ee00, 0xa000a000a000a000a000a000a000a000, 0xa000a000a000a000a000a000a000a00, 0x50005000500050005000500050005000, 0xfa00fa00fa00fa00fa00fa00fa00fa00, 0xaa000000aa000000aa000000aa000000, 0xaa000000aa000000aa000000aa00, 0x55000000550000005500000055000000, 0xff00aa00ff00aa00ff00aa00ff00aa00, 0xaa00aa0000000000aa00aa0000000000, 0xaa00aa0000000000aa00aa00, 0x55005500000000005500550000000000, 0xff00ff00aa00aa00ff00ff00aa00aa00, 0xcc00cc00cc00cc00cc00cc00cc00cc00, 0xc000c000c000c000c000c000c000c000, 0xc000c000c000c000c000c000c000c00, 0x30003000300030003000300030003000, 0xfc00fc00fc00fc00fc00fc00fc00fc00, 0xcc000000cc000000cc000000cc000000, 0xcc000000cc000000cc000000cc00, 0x33000000330000003300000033000000, 0xff00cc00ff00cc00ff00cc00ff00cc00, 0xcc00cc0000000000cc00cc0000000000, 0xcc00cc0000000000cc00cc00, 0x33003300000000003300330000000000, 0xff00ff00cc00cc00ff00ff00cc00cc00, 0xf000f000f000f000f000f000f000f000, 0xf0000000f0000000f0000000f0000000, 0xf0000000f0000000f0000000f000, 0xf0000000f0000000f0000000f000000, 0xff00f000ff00f000ff00f000ff00f000, 0xf000f00000000000f000f00000000000, 0xf000f00000000000f000f000, 0xf000f00000000000f000f0000000000, 0xff00ff00f000f000ff00ff00f000f000, 0xff000000ff000000ff000000ff000000, 0xff00ff0000000000ff00ff0000000000, 0xff00000000000000ff00000000000000, 0xff00000000000000ff000000, 0xff00000000000000ff0000000000, 0xff00ff00ff000000ff00ff00ff000000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ExampleSix.bound,
  SixRules.knownRule target 4 false LeafSeed14.target 8
    [0x0, 0xaaaa0000aaaa0000aaaa0000aaaa, 0xcccc0000cccc0000cccc0000cccc, 0xf0f00000f0f00000f0f00000f0f0, 0xff000000ff000000ff000000ff00, 0xffff000000000000ffff00000000]
    [0xaaaa0000aaaa0000aaaa0000aaaa, 0x0, 0x8888000088880000888800008888, 0x2222000022220000222200002222, 0x4444000044440000444400004444, 0xeeee0000eeee0000eeee0000eeee, 0xa0a00000a0a00000a0a00000a0a0, 0xa0a00000a0a00000a0a00000a0a, 0x5050000050500000505000005050, 0xfafa0000fafa0000fafa0000fafa, 0xaa000000aa000000aa000000aa00, 0xaa000000aa000000aa000000aa, 0x5500000055000000550000005500, 0xffaa0000ffaa0000ffaa0000ffaa, 0xaaaa000000000000aaaa00000000, 0xaaaa000000000000aaaa, 0x5555000000000000555500000000, 0xffff0000aaaa0000ffff0000aaaa, 0xcccc0000cccc0000cccc0000cccc, 0xc0c00000c0c00000c0c00000c0c0, 0xc0c00000c0c00000c0c00000c0c, 0x3030000030300000303000003030, 0xfcfc0000fcfc0000fcfc0000fcfc, 0xcc000000cc000000cc000000cc00, 0xcc000000cc000000cc000000cc, 0x3300000033000000330000003300, 0xffcc0000ffcc0000ffcc0000ffcc, 0xcccc000000000000cccc00000000, 0xcccc000000000000cccc, 0x3333000000000000333300000000, 0xffff0000cccc0000ffff0000cccc, 0xf0f00000f0f00000f0f00000f0f0, 0xf0000000f0000000f0000000f000, 0xf0000000f0000000f0000000f0, 0xf0000000f0000000f0000000f00, 0xfff00000fff00000fff00000fff0, 0xf0f0000000000000f0f000000000, 0xf0f0000000000000f0f0, 0xf0f0000000000000f0f00000000, 0xffff0000f0f00000ffff0000f0f0, 0xff000000ff000000ff000000ff00, 0xff00000000000000ff0000000000, 0xff00000000000000ff00, 0xff00000000000000ff00000000, 0xffff0000ff000000ffff0000ff00, 0xffff000000000000ffff00000000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafSeed14.bound,
  SixRules.knownRule target 4 true LeafAliases.wordSeed15 6
    [0x0, 0xaaaa0000aaaa0000aaaa0000aaaa0000, 0xcccc0000cccc0000cccc0000cccc0000, 0xf0f00000f0f00000f0f00000f0f00000, 0xff000000ff000000ff000000ff000000, 0xffff000000000000ffff000000000000]
    [0xaaaa0000aaaa0000aaaa0000aaaa0000, 0x0, 0x88880000888800008888000088880000, 0x22220000222200002222000022220000, 0x44440000444400004444000044440000, 0xeeee0000eeee0000eeee0000eeee0000, 0xa0a00000a0a00000a0a00000a0a00000, 0xa0a00000a0a00000a0a00000a0a0000, 0x50500000505000005050000050500000, 0xfafa0000fafa0000fafa0000fafa0000, 0xaa000000aa000000aa000000aa000000, 0xaa000000aa000000aa000000aa0000, 0x55000000550000005500000055000000, 0xffaa0000ffaa0000ffaa0000ffaa0000, 0xaaaa000000000000aaaa000000000000, 0xaaaa000000000000aaaa0000, 0x55550000000000005555000000000000, 0xffff0000aaaa0000ffff0000aaaa0000, 0xcccc0000cccc0000cccc0000cccc0000, 0xc0c00000c0c00000c0c00000c0c00000, 0xc0c00000c0c00000c0c00000c0c0000, 0x30300000303000003030000030300000, 0xfcfc0000fcfc0000fcfc0000fcfc0000, 0xcc000000cc000000cc000000cc000000, 0xcc000000cc000000cc000000cc0000, 0x33000000330000003300000033000000, 0xffcc0000ffcc0000ffcc0000ffcc0000, 0xcccc000000000000cccc000000000000, 0xcccc000000000000cccc0000, 0x33330000000000003333000000000000, 0xffff0000cccc0000ffff0000cccc0000, 0xf0f00000f0f00000f0f00000f0f00000, 0xf0000000f0000000f0000000f0000000, 0xf0000000f0000000f0000000f00000, 0xf0000000f0000000f0000000f000000, 0xfff00000fff00000fff00000fff00000, 0xf0f0000000000000f0f0000000000000, 0xf0f0000000000000f0f00000, 0xf0f0000000000000f0f000000000000, 0xffff0000f0f00000ffff0000f0f00000, 0xff000000ff000000ff000000ff000000, 0xff00000000000000ff00000000000000, 0xff00000000000000ff000000, 0xff00000000000000ff000000000000, 0xffff0000ff000000ffff0000ff000000, 0xffff000000000000ffff000000000000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafAliases.Seed15,
  SixRules.knownRule target 5 false LeafAliases.wordSeed16 6
    [0x0, 0xaaaaaaaa00000000aaaaaaaa, 0xcccccccc00000000cccccccc, 0xf0f0f0f000000000f0f0f0f0, 0xff00ff0000000000ff00ff00, 0xffff000000000000ffff0000]
    [0xaaaaaaaa00000000aaaaaaaa, 0x0, 0x888888880000000088888888, 0x222222220000000022222222, 0x444444440000000044444444, 0xeeeeeeee00000000eeeeeeee, 0xa0a0a0a000000000a0a0a0a0, 0xa0a0a0a000000000a0a0a0a, 0x505050500000000050505050, 0xfafafafa00000000fafafafa, 0xaa00aa0000000000aa00aa00, 0xaa00aa0000000000aa00aa, 0x550055000000000055005500, 0xffaaffaa00000000ffaaffaa, 0xaaaa000000000000aaaa0000, 0xaaaa000000000000aaaa, 0x555500000000000055550000, 0xffffaaaa00000000ffffaaaa, 0xcccccccc00000000cccccccc, 0xc0c0c0c000000000c0c0c0c0, 0xc0c0c0c000000000c0c0c0c, 0x303030300000000030303030, 0xfcfcfcfc00000000fcfcfcfc, 0xcc00cc0000000000cc00cc00, 0xcc00cc0000000000cc00cc, 0x330033000000000033003300, 0xffccffcc00000000ffccffcc, 0xcccc000000000000cccc0000, 0xcccc000000000000cccc, 0x333300000000000033330000, 0xffffcccc00000000ffffcccc, 0xf0f0f0f000000000f0f0f0f0, 0xf000f00000000000f000f000, 0xf000f00000000000f000f0, 0xf000f00000000000f000f00, 0xfff0fff000000000fff0fff0, 0xf0f0000000000000f0f00000, 0xf0f0000000000000f0f0, 0xf0f0000000000000f0f0000, 0xfffff0f000000000fffff0f0, 0xff00ff0000000000ff00ff00, 0xff00000000000000ff000000, 0xff00000000000000ff00, 0xff00000000000000ff0000, 0xffffff0000000000ffffff00, 0xffff000000000000ffff0000]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) LeafAliases.Seed16
]

def cut : ℕ → List W → Bool := Compact.reject target rules terminalHints salt
def locate : ℕ → List W → ℕ × ℕ := Compact.lookup table poolHints salt
def check : ℕ → ℕ → Bool := Compact.check table target negative startMask locate switches cut

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page2at0 : span (check 2) 1 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer2 : span (check 2) 1 0 = true := page2at0
end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at0 : span (check 3) 4 0 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at4 : span (check 3) 4 4 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at8 : span (check 3) 4 8 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at12 : span (check 3) 4 12 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page3at16 : span (check 3) 4 16 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer3 : span (check 3) 20 0 = true := span_join (span_join (span_join (page3at0) (page3at4)) (page3at8)) (span_join (page3at12) (page3at16))
end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at0 : span (check 4) 4 0 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at4 : span (check 4) 4 4 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at8 : span (check 4) 4 8 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at12 : span (check 4) 4 12 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at16 : span (check 4) 4 16 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at20 : span (check 4) 4 20 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at24 : span (check 4) 4 24 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at28 : span (check 4) 4 28 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at32 : span (check 4) 4 32 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at36 : span (check 4) 4 36 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at40 : span (check 4) 4 40 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at44 : span (check 4) 4 44 = true := by apply block4 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at48 : span (check 4) 4 48 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at52 : span (check 4) 4 52 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at56 : span (check 4) 4 56 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at60 : span (check 4) 4 60 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page4at64 : span (check 4) 1 64 = true := by decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxRecDepth 5000 in
theorem layer4 : span (check 4) 65 0 = true := span_join (span_join (span_join (span_join (span_join (page4at0) (page4at4)) (page4at8)) (span_join (page4at12) (page4at16))) (span_join (span_join (page4at20) (page4at24)) (span_join (page4at28) (page4at32)))) (span_join (span_join (span_join (page4at36) (page4at40)) (span_join (page4at44) (page4at48))) (span_join (span_join (page4at52) (page4at56)) (span_join (page4at60) (page4at64))))

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at0 : span (check 5) 4 0 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at4 : span (check 5) 4 4 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at8 : span (check 5) 4 8 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at12 : span (check 5) 4 12 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at16 : span (check 5) 4 16 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at20 : span (check 5) 4 20 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at24 : span (check 5) 4 24 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at28 : span (check 5) 4 28 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at32 : span (check 5) 4 32 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at36 : span (check 5) 4 36 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at40 : span (check 5) 4 40 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at44 : span (check 5) 4 44 = true := by apply block4 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at48 : span (check 5) 4 48 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at52 : span (check 5) 4 52 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at56 : span (check 5) 4 56 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at60 : span (check 5) 4 60 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at64 : span (check 5) 4 64 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at68 : span (check 5) 4 68 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at72 : span (check 5) 4 72 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at76 : span (check 5) 4 76 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at80 : span (check 5) 4 80 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at84 : span (check 5) 4 84 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at88 : span (check 5) 4 88 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at92 : span (check 5) 4 92 = true := by apply block4 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at96 : span (check 5) 4 96 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at100 : span (check 5) 4 100 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at104 : span (check 5) 4 104 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at108 : span (check 5) 4 108 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at112 : span (check 5) 4 112 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at116 : span (check 5) 4 116 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at120 : span (check 5) 4 120 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at124 : span (check 5) 4 124 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at128 : span (check 5) 4 128 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at132 : span (check 5) 4 132 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at136 : span (check 5) 4 136 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at140 : span (check 5) 4 140 = true := by apply block4 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at144 : span (check 5) 4 144 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page5at148 : span (check 5) 3 148 = true := by apply block3 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer5 : span (check 5) 151 0 = true :=
  span_join (f := check 5) (a := 76) (b := 75) (o := 0) (span_join (f := check 5) (a := 40) (b := 36) (o := 0) (span_join (f := check 5) (a := 20) (b := 20) (o := 0) (span_join (f := check 5) (a := 12) (b := 8) (o := 0) (span_join (f := check 5) (a := 8) (b := 4) (o := 0) (span_join (f := check 5) (a := 4) (b := 4) (o := 0) (page5at0) (page5at4)) (page5at8)) (span_join (f := check 5) (a := 4) (b := 4) (o := 12) (page5at12) (page5at16))) (span_join (f := check 5) (a := 12) (b := 8) (o := 20) (span_join (f := check 5) (a := 8) (b := 4) (o := 20) (span_join (f := check 5) (a := 4) (b := 4) (o := 20) (page5at20) (page5at24)) (page5at28)) (span_join (f := check 5) (a := 4) (b := 4) (o := 32) (page5at32) (page5at36)))) (span_join (f := check 5) (a := 20) (b := 16) (o := 40) (span_join (f := check 5) (a := 12) (b := 8) (o := 40) (span_join (f := check 5) (a := 8) (b := 4) (o := 40) (span_join (f := check 5) (a := 4) (b := 4) (o := 40) (page5at40) (page5at44)) (page5at48)) (span_join (f := check 5) (a := 4) (b := 4) (o := 52) (page5at52) (page5at56))) (span_join (f := check 5) (a := 8) (b := 8) (o := 60) (span_join (f := check 5) (a := 4) (b := 4) (o := 60) (page5at60) (page5at64)) (span_join (f := check 5) (a := 4) (b := 4) (o := 68) (page5at68) (page5at72))))) (span_join (f := check 5) (a := 40) (b := 35) (o := 76) (span_join (f := check 5) (a := 20) (b := 20) (o := 76) (span_join (f := check 5) (a := 12) (b := 8) (o := 76) (span_join (f := check 5) (a := 8) (b := 4) (o := 76) (span_join (f := check 5) (a := 4) (b := 4) (o := 76) (page5at76) (page5at80)) (page5at84)) (span_join (f := check 5) (a := 4) (b := 4) (o := 88) (page5at88) (page5at92))) (span_join (f := check 5) (a := 12) (b := 8) (o := 96) (span_join (f := check 5) (a := 8) (b := 4) (o := 96) (span_join (f := check 5) (a := 4) (b := 4) (o := 96) (page5at96) (page5at100)) (page5at104)) (span_join (f := check 5) (a := 4) (b := 4) (o := 108) (page5at108) (page5at112)))) (span_join (f := check 5) (a := 20) (b := 15) (o := 116) (span_join (f := check 5) (a := 12) (b := 8) (o := 116) (span_join (f := check 5) (a := 8) (b := 4) (o := 116) (span_join (f := check 5) (a := 4) (b := 4) (o := 116) (page5at116) (page5at120)) (page5at124)) (span_join (f := check 5) (a := 4) (b := 4) (o := 128) (page5at128) (page5at132))) (span_join (f := check 5) (a := 8) (b := 7) (o := 136) (span_join (f := check 5) (a := 4) (b := 4) (o := 136) (page5at136) (page5at140)) (span_join (f := check 5) (a := 4) (b := 3) (o := 144) (page5at144) (page5at148)))))

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at0 : span (check 6) 4 0 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at4 : span (check 6) 4 4 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at8 : span (check 6) 4 8 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at12 : span (check 6) 4 12 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at16 : span (check 6) 4 16 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at20 : span (check 6) 4 20 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at24 : span (check 6) 4 24 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at28 : span (check 6) 4 28 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at32 : span (check 6) 4 32 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at36 : span (check 6) 4 36 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at40 : span (check 6) 4 40 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at44 : span (check 6) 4 44 = true := by apply block4 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at48 : span (check 6) 4 48 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at52 : span (check 6) 4 52 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at56 : span (check 6) 4 56 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at60 : span (check 6) 4 60 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at64 : span (check 6) 4 64 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at68 : span (check 6) 4 68 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at72 : span (check 6) 4 72 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at76 : span (check 6) 4 76 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at80 : span (check 6) 4 80 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at84 : span (check 6) 4 84 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at88 : span (check 6) 4 88 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at92 : span (check 6) 4 92 = true := by apply block4 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at96 : span (check 6) 4 96 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at100 : span (check 6) 4 100 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at104 : span (check 6) 4 104 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at108 : span (check 6) 4 108 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at112 : span (check 6) 4 112 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at116 : span (check 6) 4 116 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at120 : span (check 6) 4 120 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at124 : span (check 6) 4 124 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at128 : span (check 6) 4 128 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at132 : span (check 6) 4 132 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at136 : span (check 6) 4 136 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at140 : span (check 6) 4 140 = true := by apply block4 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at144 : span (check 6) 4 144 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at148 : span (check 6) 4 148 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at152 : span (check 6) 4 152 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at156 : span (check 6) 4 156 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at160 : span (check 6) 4 160 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at164 : span (check 6) 4 164 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at168 : span (check 6) 4 168 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at172 : span (check 6) 4 172 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at176 : span (check 6) 4 176 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at180 : span (check 6) 4 180 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at184 : span (check 6) 4 184 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at188 : span (check 6) 4 188 = true := by apply block4 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at192 : span (check 6) 4 192 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at196 : span (check 6) 4 196 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at200 : span (check 6) 4 200 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at204 : span (check 6) 4 204 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at208 : span (check 6) 4 208 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at212 : span (check 6) 4 212 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at216 : span (check 6) 4 216 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at220 : span (check 6) 4 220 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at224 : span (check 6) 4 224 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at228 : span (check 6) 4 228 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at232 : span (check 6) 4 232 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at236 : span (check 6) 4 236 = true := by apply block4 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at240 : span (check 6) 4 240 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at244 : span (check 6) 4 244 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at248 : span (check 6) 4 248 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at252 : span (check 6) 4 252 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at256 : span (check 6) 4 256 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at260 : span (check 6) 4 260 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page6at264 : span (check 6) 2 264 = true := by apply block2 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer6 : span (check 6) 266 0 = true :=
  span_join (f := check 6) (a := 136) (b := 130) (o := 0) (span_join (f := check 6) (a := 68) (b := 68) (o := 0) (span_join (f := check 6) (a := 36) (b := 32) (o := 0) (span_join (f := check 6) (a := 20) (b := 16) (o := 0) (span_join (f := check 6) (a := 12) (b := 8) (o := 0) (span_join (f := check 6) (a := 8) (b := 4) (o := 0) (span_join (f := check 6) (a := 4) (b := 4) (o := 0) (page6at0) (page6at4)) (page6at8)) (span_join (f := check 6) (a := 4) (b := 4) (o := 12) (page6at12) (page6at16))) (span_join (f := check 6) (a := 8) (b := 8) (o := 20) (span_join (f := check 6) (a := 4) (b := 4) (o := 20) (page6at20) (page6at24)) (span_join (f := check 6) (a := 4) (b := 4) (o := 28) (page6at28) (page6at32)))) (span_join (f := check 6) (a := 16) (b := 16) (o := 36) (span_join (f := check 6) (a := 8) (b := 8) (o := 36) (span_join (f := check 6) (a := 4) (b := 4) (o := 36) (page6at36) (page6at40)) (span_join (f := check 6) (a := 4) (b := 4) (o := 44) (page6at44) (page6at48))) (span_join (f := check 6) (a := 8) (b := 8) (o := 52) (span_join (f := check 6) (a := 4) (b := 4) (o := 52) (page6at52) (page6at56)) (span_join (f := check 6) (a := 4) (b := 4) (o := 60) (page6at60) (page6at64))))) (span_join (f := check 6) (a := 36) (b := 32) (o := 68) (span_join (f := check 6) (a := 20) (b := 16) (o := 68) (span_join (f := check 6) (a := 12) (b := 8) (o := 68) (span_join (f := check 6) (a := 8) (b := 4) (o := 68) (span_join (f := check 6) (a := 4) (b := 4) (o := 68) (page6at68) (page6at72)) (page6at76)) (span_join (f := check 6) (a := 4) (b := 4) (o := 80) (page6at80) (page6at84))) (span_join (f := check 6) (a := 8) (b := 8) (o := 88) (span_join (f := check 6) (a := 4) (b := 4) (o := 88) (page6at88) (page6at92)) (span_join (f := check 6) (a := 4) (b := 4) (o := 96) (page6at96) (page6at100)))) (span_join (f := check 6) (a := 16) (b := 16) (o := 104) (span_join (f := check 6) (a := 8) (b := 8) (o := 104) (span_join (f := check 6) (a := 4) (b := 4) (o := 104) (page6at104) (page6at108)) (span_join (f := check 6) (a := 4) (b := 4) (o := 112) (page6at112) (page6at116))) (span_join (f := check 6) (a := 8) (b := 8) (o := 120) (span_join (f := check 6) (a := 4) (b := 4) (o := 120) (page6at120) (page6at124)) (span_join (f := check 6) (a := 4) (b := 4) (o := 128) (page6at128) (page6at132)))))) (span_join (f := check 6) (a := 68) (b := 62) (o := 136) (span_join (f := check 6) (a := 36) (b := 32) (o := 136) (span_join (f := check 6) (a := 20) (b := 16) (o := 136) (span_join (f := check 6) (a := 12) (b := 8) (o := 136) (span_join (f := check 6) (a := 8) (b := 4) (o := 136) (span_join (f := check 6) (a := 4) (b := 4) (o := 136) (page6at136) (page6at140)) (page6at144)) (span_join (f := check 6) (a := 4) (b := 4) (o := 148) (page6at148) (page6at152))) (span_join (f := check 6) (a := 8) (b := 8) (o := 156) (span_join (f := check 6) (a := 4) (b := 4) (o := 156) (page6at156) (page6at160)) (span_join (f := check 6) (a := 4) (b := 4) (o := 164) (page6at164) (page6at168)))) (span_join (f := check 6) (a := 16) (b := 16) (o := 172) (span_join (f := check 6) (a := 8) (b := 8) (o := 172) (span_join (f := check 6) (a := 4) (b := 4) (o := 172) (page6at172) (page6at176)) (span_join (f := check 6) (a := 4) (b := 4) (o := 180) (page6at180) (page6at184))) (span_join (f := check 6) (a := 8) (b := 8) (o := 188) (span_join (f := check 6) (a := 4) (b := 4) (o := 188) (page6at188) (page6at192)) (span_join (f := check 6) (a := 4) (b := 4) (o := 196) (page6at196) (page6at200))))) (span_join (f := check 6) (a := 32) (b := 30) (o := 204) (span_join (f := check 6) (a := 16) (b := 16) (o := 204) (span_join (f := check 6) (a := 8) (b := 8) (o := 204) (span_join (f := check 6) (a := 4) (b := 4) (o := 204) (page6at204) (page6at208)) (span_join (f := check 6) (a := 4) (b := 4) (o := 212) (page6at212) (page6at216))) (span_join (f := check 6) (a := 8) (b := 8) (o := 220) (span_join (f := check 6) (a := 4) (b := 4) (o := 220) (page6at220) (page6at224)) (span_join (f := check 6) (a := 4) (b := 4) (o := 228) (page6at228) (page6at232)))) (span_join (f := check 6) (a := 16) (b := 14) (o := 236) (span_join (f := check 6) (a := 8) (b := 8) (o := 236) (span_join (f := check 6) (a := 4) (b := 4) (o := 236) (page6at236) (page6at240)) (span_join (f := check 6) (a := 4) (b := 4) (o := 244) (page6at244) (page6at248))) (span_join (f := check 6) (a := 8) (b := 6) (o := 252) (span_join (f := check 6) (a := 4) (b := 4) (o := 252) (page6at252) (page6at256)) (span_join (f := check 6) (a := 4) (b := 2) (o := 260) (page6at260) (page6at264))))))

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at0 : span (check 7) 4 0 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at4 : span (check 7) 4 4 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at8 : span (check 7) 4 8 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at12 : span (check 7) 4 12 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at16 : span (check 7) 4 16 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at20 : span (check 7) 4 20 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at24 : span (check 7) 4 24 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at28 : span (check 7) 4 28 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at32 : span (check 7) 4 32 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at36 : span (check 7) 4 36 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at40 : span (check 7) 4 40 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at44 : span (check 7) 4 44 = true := by apply block4 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at48 : span (check 7) 4 48 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at52 : span (check 7) 4 52 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at56 : span (check 7) 4 56 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at60 : span (check 7) 4 60 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at64 : span (check 7) 4 64 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at68 : span (check 7) 4 68 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at72 : span (check 7) 4 72 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at76 : span (check 7) 4 76 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at80 : span (check 7) 4 80 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at84 : span (check 7) 4 84 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at88 : span (check 7) 4 88 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at92 : span (check 7) 4 92 = true := by apply block4 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at96 : span (check 7) 4 96 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at100 : span (check 7) 4 100 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at104 : span (check 7) 4 104 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at108 : span (check 7) 4 108 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at112 : span (check 7) 4 112 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at116 : span (check 7) 4 116 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at120 : span (check 7) 4 120 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at124 : span (check 7) 4 124 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at128 : span (check 7) 4 128 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at132 : span (check 7) 4 132 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at136 : span (check 7) 4 136 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at140 : span (check 7) 4 140 = true := by apply block4 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at144 : span (check 7) 4 144 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at148 : span (check 7) 4 148 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at152 : span (check 7) 4 152 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at156 : span (check 7) 4 156 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at160 : span (check 7) 4 160 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at164 : span (check 7) 4 164 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at168 : span (check 7) 4 168 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at172 : span (check 7) 4 172 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at176 : span (check 7) 4 176 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at180 : span (check 7) 4 180 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at184 : span (check 7) 4 184 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at188 : span (check 7) 4 188 = true := by apply block4 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at192 : span (check 7) 4 192 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at196 : span (check 7) 4 196 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at200 : span (check 7) 4 200 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at204 : span (check 7) 4 204 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at208 : span (check 7) 4 208 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at212 : span (check 7) 4 212 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at216 : span (check 7) 4 216 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at220 : span (check 7) 4 220 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at224 : span (check 7) 4 224 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at228 : span (check 7) 4 228 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at232 : span (check 7) 4 232 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at236 : span (check 7) 4 236 = true := by apply block4 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at240 : span (check 7) 4 240 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at244 : span (check 7) 4 244 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page7at248 : span (check 7) 2 248 = true := by apply block2 <;> decide +kernel

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer7 : span (check 7) 250 0 = true :=
  span_join (f := check 7) (a := 128) (b := 122) (o := 0) (span_join (f := check 7) (a := 64) (b := 64) (o := 0) (span_join (f := check 7) (a := 32) (b := 32) (o := 0) (span_join (f := check 7) (a := 16) (b := 16) (o := 0) (span_join (f := check 7) (a := 8) (b := 8) (o := 0) (span_join (f := check 7) (a := 4) (b := 4) (o := 0) (page7at0) (page7at4)) (span_join (f := check 7) (a := 4) (b := 4) (o := 8) (page7at8) (page7at12))) (span_join (f := check 7) (a := 8) (b := 8) (o := 16) (span_join (f := check 7) (a := 4) (b := 4) (o := 16) (page7at16) (page7at20)) (span_join (f := check 7) (a := 4) (b := 4) (o := 24) (page7at24) (page7at28)))) (span_join (f := check 7) (a := 16) (b := 16) (o := 32) (span_join (f := check 7) (a := 8) (b := 8) (o := 32) (span_join (f := check 7) (a := 4) (b := 4) (o := 32) (page7at32) (page7at36)) (span_join (f := check 7) (a := 4) (b := 4) (o := 40) (page7at40) (page7at44))) (span_join (f := check 7) (a := 8) (b := 8) (o := 48) (span_join (f := check 7) (a := 4) (b := 4) (o := 48) (page7at48) (page7at52)) (span_join (f := check 7) (a := 4) (b := 4) (o := 56) (page7at56) (page7at60))))) (span_join (f := check 7) (a := 32) (b := 32) (o := 64) (span_join (f := check 7) (a := 16) (b := 16) (o := 64) (span_join (f := check 7) (a := 8) (b := 8) (o := 64) (span_join (f := check 7) (a := 4) (b := 4) (o := 64) (page7at64) (page7at68)) (span_join (f := check 7) (a := 4) (b := 4) (o := 72) (page7at72) (page7at76))) (span_join (f := check 7) (a := 8) (b := 8) (o := 80) (span_join (f := check 7) (a := 4) (b := 4) (o := 80) (page7at80) (page7at84)) (span_join (f := check 7) (a := 4) (b := 4) (o := 88) (page7at88) (page7at92)))) (span_join (f := check 7) (a := 16) (b := 16) (o := 96) (span_join (f := check 7) (a := 8) (b := 8) (o := 96) (span_join (f := check 7) (a := 4) (b := 4) (o := 96) (page7at96) (page7at100)) (span_join (f := check 7) (a := 4) (b := 4) (o := 104) (page7at104) (page7at108))) (span_join (f := check 7) (a := 8) (b := 8) (o := 112) (span_join (f := check 7) (a := 4) (b := 4) (o := 112) (page7at112) (page7at116)) (span_join (f := check 7) (a := 4) (b := 4) (o := 120) (page7at120) (page7at124)))))) (span_join (f := check 7) (a := 64) (b := 58) (o := 128) (span_join (f := check 7) (a := 32) (b := 32) (o := 128) (span_join (f := check 7) (a := 16) (b := 16) (o := 128) (span_join (f := check 7) (a := 8) (b := 8) (o := 128) (span_join (f := check 7) (a := 4) (b := 4) (o := 128) (page7at128) (page7at132)) (span_join (f := check 7) (a := 4) (b := 4) (o := 136) (page7at136) (page7at140))) (span_join (f := check 7) (a := 8) (b := 8) (o := 144) (span_join (f := check 7) (a := 4) (b := 4) (o := 144) (page7at144) (page7at148)) (span_join (f := check 7) (a := 4) (b := 4) (o := 152) (page7at152) (page7at156)))) (span_join (f := check 7) (a := 16) (b := 16) (o := 160) (span_join (f := check 7) (a := 8) (b := 8) (o := 160) (span_join (f := check 7) (a := 4) (b := 4) (o := 160) (page7at160) (page7at164)) (span_join (f := check 7) (a := 4) (b := 4) (o := 168) (page7at168) (page7at172))) (span_join (f := check 7) (a := 8) (b := 8) (o := 176) (span_join (f := check 7) (a := 4) (b := 4) (o := 176) (page7at176) (page7at180)) (span_join (f := check 7) (a := 4) (b := 4) (o := 184) (page7at184) (page7at188))))) (span_join (f := check 7) (a := 32) (b := 26) (o := 192) (span_join (f := check 7) (a := 16) (b := 16) (o := 192) (span_join (f := check 7) (a := 8) (b := 8) (o := 192) (span_join (f := check 7) (a := 4) (b := 4) (o := 192) (page7at192) (page7at196)) (span_join (f := check 7) (a := 4) (b := 4) (o := 200) (page7at200) (page7at204))) (span_join (f := check 7) (a := 8) (b := 8) (o := 208) (span_join (f := check 7) (a := 4) (b := 4) (o := 208) (page7at208) (page7at212)) (span_join (f := check 7) (a := 4) (b := 4) (o := 216) (page7at216) (page7at220)))) (span_join (f := check 7) (a := 16) (b := 10) (o := 224) (span_join (f := check 7) (a := 8) (b := 8) (o := 224) (span_join (f := check 7) (a := 4) (b := 4) (o := 224) (page7at224) (page7at228)) (span_join (f := check 7) (a := 4) (b := 4) (o := 232) (page7at232) (page7at236))) (span_join (f := check 7) (a := 8) (b := 2) (o := 240) (span_join (f := check 7) (a := 4) (b := 4) (o := 240) (page7at240) (page7at244)) (page7at248)))))

end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page8at0 : span (check 8) 4 0 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page8at4 : span (check 8) 4 4 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page8at8 : span (check 8) 4 8 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page8at12 : span (check 8) 4 12 = true := by apply block4 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page8at16 : span (check 8) 3 16 = true := by apply block3 <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer8 : span (check 8) 19 0 = true :=
  span_join (f := check 8) (a := 12) (b := 7) (o := 0) (span_join (f := check 8) (a := 8) (b := 4) (o := 0) (span_join (f := check 8) (a := 4) (b := 4) (o := 0) (page8at0) (page8at4)) (page8at8)) (span_join (f := check 8) (a := 4) (b := 3) (o := 12) (page8at12) (page8at16))
end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem page9at0 : span (check 9) 1 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem layer9 : span (check 9) 1 0 = true := page9at0
end LeafHint4
end GraphSignedFrontier

namespace GraphSignedFrontier
namespace LeafHint4

set_option maxHeartbeats 0 in
theorem validated (k : ℕ) (hk : k ≤ 9) (i : ℕ) (hi : i < count k) : check k i = true := by
  have e : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
  rcases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [count] at hi
  · simp [count] at hi
  · exact span_member layer2 i (by omega) (by simpa [count] using hi)
  · exact span_member layer3 i (by omega) (by simpa [count] using hi)
  · exact span_member layer4 i (by omega) (by simpa [count] using hi)
  · exact span_member layer5 i (by omega) (by simpa [count] using hi)
  · exact span_member layer6 i (by omega) (by simpa [count] using hi)
  · exact span_member layer7 i (by omega) (by simpa [count] using hi)
  · exact span_member layer8 i (by omega) (by simpa [count] using hi)
  · exact span_member layer9 i (by omega) (by simpa [count] using hi)

set_option maxHeartbeats 0 in
theorem bound : signedLower target raw 10 :=
  Compact.lower table target positive raw essential negative neg startMask 9
    (by decide +kernel) (by decide +kernel) (by decide +kernel) locate switches valid fixed cut
    (Compact.safe target rules terminalHints salt) validated

end LeafHint4

end GraphSignedFrontier

end PEqualNP.Outside.L_meta_30959_aux

theorem PEqualNP.Outside.L_meta_30959 :
  ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_30959_aux.GraphSignedFrontier.DeskCases.deskStatement
    PEqualNP.Outside.L_meta_30959_aux.GraphSignedFrontier.LeafHint0.bound
    PEqualNP.Outside.L_meta_30959_aux.GraphSignedFrontier.LeafHint4.bound
