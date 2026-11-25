import TightBinaryCircuit
import PEqualNP.Defs.TopForm

namespace BatchWireRewrite
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open TightBinaryCircuit

def value (g : Gate) (s : Pins) := g.op.eval (g.inputs.map s)
def up (a b : Bool) := a=true → b=true
def directed (out : Bool) (a b : Bool) := if out then up a b else up b a

theorem reflDir (dir a : Bool) : directed dir a a := by cases dir <;> exact id

theorem transDir {dir a b c : Bool} (h : directed dir a b) (k : directed dir b c) :
    directed dir a c := by cases dir <;> first | exact k ∘ h | exact h ∘ k

theorem monotoneValue (g : Gate) (kind : g.op=.and ∨ g.op=.or) (x y : Pins)
    (pointwise : ∀ i ∈ g.inputs, up (x i) (y i)) : up (value g x) (value g y) := by
  intro on
  rcases kind with h|h
  · simp [value,h,GateOp.eval] at on ⊢
    exact fun i hi => pointwise i hi (on i hi)
  · simp [value,h,GateOp.eval] at on ⊢
    obtain ⟨i,hi,v⟩ := on
    exact ⟨i,hi,pointwise i hi v⟩

theorem monotoneDir (dir : Bool) (g : Gate) (kind : g.op=.and ∨ g.op=.or) (x y : Pins)
    (pointwise : ∀ i ∈ g.inputs, directed dir (x i) (y i)) :
    directed dir (value g x) (value g y) := by
  cases dir <;> exact monotoneValue _ kind _ _ pointwise

theorem past (gs : List Gate) (base : ℕ) (x : Pins) (w : ℕ) (lt : w < base) :
    run base x gs w = x w := by
  induction gs generalizing base x with
  | nil => rfl
  | cons g gs ih =>
    change run (base+1) (step base g x) gs w = _
    rw [ih _ _ (by omega)]
    simp [step,Function.update_of_ne (show w ≠ base by omega)]

theorem earlierValue (g : Gate) (gs : List Gate) (base : ℕ) (x : Pins)
    (early : ∀ i ∈ g.inputs, i < base) : value g (run base x gs) = value g x := by
  unfold value
  congr 1
  exact List.map_congr_left (fun i hi => past gs base x i (early i hi))

-- Each edited gate is tested only on the original circuit's final tape.
-- Earlier-wire checks make these comparisons valid at the moment it runs.
def checks (dir : Bool) (tape : Pins) (base : ℕ) (old new : List Gate) :=
  ∀ j (ho : j<old.length) (hn : j<new.length),
    (∀ i ∈ old[j].inputs, i<base+j) ∧ (∀ i ∈ new[j].inputs, i<base+j) ∧
    (new[j].op=.and ∨ new[j].op=.or) ∧ directed dir (value old[j] tape) (value new[j] tape)

theorem simulateBatch (dir : Bool) (base : ℕ) (x y : Pins) (old new : List Gate)
    (len : old.length=new.length) (before : ∀ i, directed dir (x i) (y i))
    (edit : checks dir (run base x old) base old new) :
    ∀ i, directed dir (run base x old i) (run base y new i) := by
  induction old generalizing base x y new with
  | nil => cases new <;> simp_all [run]
  | cons g gs ih =>
    cases new with
    | nil => simp at len
    | cons h hs =>
      have equal : gs.length = hs.length := by simpa using len
      obtain ⟨go,ho,kind,localGate⟩ := edit 0 (by simp) (by simp)
      change directed dir (value g (run base x (g::gs))) (value h (run base x (g::gs))) at localGate
      rw [earlierValue g _ base x (by simpa using go),earlierValue h _ base x (by simpa using ho)] at localGate
      have after : ∀ i, directed dir (step base g x i) (step base h y i) := by
        intro i
        by_cases eq : i=base
        · subst i; simp only [step,Function.update_self]
          exact transDir localGate (monotoneDir dir h kind x y (fun j _ => before j))
        · simpa [step,Function.update_of_ne eq] using before i
      apply ih (base+1) _ _ hs equal after
      intro j jo jn
      have shift : base+1+j=base+(j+1) := by omega
      rw [shift]
      exact edit (j+1) (by simpa using jo) (by simpa using jn)

def inputs {n} (x : Fin n → Bool) : Pins := fun i => (List.ofFn x).getD i false
def tape {n} (C : Circuit) (x : Fin n → Bool) := run n (inputs x) C.gates

theorem realTape {n} (C : Circuit) (x : Fin n → Bool) (i : ℕ) :
    tape C x i = (C.wires (List.ofFn x)).getD i false := by
  change run n (fun j => (List.ofFn x).getD j false) C.gates i = _
  simpa only [List.length_ofFn,Circuit.wires,actual] using
    (congrFun (simulate C.gates (List.ofFn x)) i).symm

theorem tapeOutput {n} (C : Circuit) (x : Fin n → Bool) :
    tape C x C.output = circuitFun n C x := realTape C x C.output

theorem batchRow {n} (C D : Circuit) (sameOutput : C.output=D.output)
    (len : C.gates.length=D.gates.length) (x : Fin n → Bool)
    (edit : checks (circuitFun n C x) (tape C x) n C.gates D.gates) :
    circuitFun n D x = circuitFun n C x := by
  have h := simulateBatch (circuitFun n C x) n (inputs x) (inputs x) C.gates D.gates len
    (fun _ => reflDir _ _) edit C.output
  change directed _ (tape C x C.output) (tape D x C.output) at h
  rw [tapeOutput,sameOutput,tapeOutput] at h
  cases a : circuitFun n C x <;> cases b : circuitFun n D x <;> simp_all [directed,up]

theorem batchCorrect {n} (C D : Circuit) (sameOutput : C.output=D.output)
    (len : C.gates.length=D.gates.length)
    (edit : ∀ x : Fin n → Bool, checks (circuitFun n C x) (tape C x) n C.gates D.gates) :
    circuitFun n D = circuitFun n C := funext (fun x => batchRow C D sameOutput len x (edit x))

abbrev Menu := Gate × List Gate
def options (m : Menu) := m.1::m.2
def allowed (menus : List Menu) (gs : List Gate) := List.Forall₂ (fun m g => g ∈ options m) menus gs

def extreme (high : Bool) (m : Menu) (x : Pins) :=
  if high then (options m).any (fun g => value g x) else (options m).all (fun g => value g x)

def envelope (high : Bool) (base : ℕ) (x : Pins) : List Menu → Pins
  | [] => x
  | m::ms => envelope high (base+1) (Function.update x base (extreme high m x)) ms

theorem choiceBound (high : Bool) (g : Gate) (m : Menu) (h : g ∈ options m) (x : Pins) :
    directed high (value g x) (extreme high m x) := by
  cases high
  · change (options m).all _ = true → _
    exact fun a => (List.all_eq_true.mp a) g h
  · change _ → (options m).any _ = true
    exact fun a => List.any_eq_true.mpr ⟨g,h,a⟩

theorem envelopeBound (high : Bool) (base : ℕ) (x y : Pins) (menus : List Menu) (gs : List Gate)
    (sel : allowed menus gs) (mono : ∀ m ∈ menus, ∀ g ∈ options m, g.op=.and ∨ g.op=.or)
    (prior : ∀ i, directed high (x i) (y i)) :
    ∀ i, directed high (run base x gs i) (envelope high base y menus i) := by
  induction sel generalizing base x y with
  | nil => exact prior
  | @cons m g ms rest mem tail ih =>
    apply ih (base+1) (step base g x) (Function.update y base (extreme high m y))
      (fun k hk => mono k (List.mem_cons_of_mem _ hk))
    intro i
    by_cases eq : i=base
    · subst i; simp only [step,Function.update_self]
      exact transDir (monotoneDir high g (mono m List.mem_cons_self g mem) x y (fun j _ => prior j))
        (choiceBound high g m mem y)
    · simpa [step,Function.update_of_ne eq] using prior i

theorem attained (high : Bool) (m : Menu) (x : Pins) :
    ∃ g ∈ options m, value g x = extreme high m x := by
  cases high
  · change ∃ g ∈ options m, value g x = (options m).all _
    cases eq : (options m).all (fun g => value g x) with
    | true => exact ⟨m.1,List.mem_cons_self,(List.all_eq_true.mp eq) _ List.mem_cons_self⟩
    | false =>
      by_contra! bad
      have all := List.all_eq_true.mpr (fun g hg => Bool.eq_true_of_ne_false (bad g hg))
      exact Bool.noConfusion (eq.symm.trans all)
  · change ∃ g ∈ options m, value g x = (options m).any _
    cases eq : (options m).any (fun g => value g x) with
    | true => exact List.any_eq_true.mp eq
    | false =>
      refine ⟨m.1,List.mem_cons_self,?_⟩
      cases v : value m.1 x with
      | false => rfl
      | true => exact Bool.noConfusion (eq.symm.trans (List.any_eq_true.mpr ⟨_,List.mem_cons_self,v⟩))

-- The witness may depend on the input. For a fixed input it realizes every
-- extremal register simultaneously, including registers reused downstream.
theorem attainableTape (high : Bool) (base : ℕ) (x : Pins) (menus : List Menu) :
    ∃ gs, allowed menus gs ∧ run base x gs = envelope high base x menus := by
  induction menus generalizing base x with
  | nil => exact ⟨[],.nil,rfl⟩
  | cons m ms ih =>
    obtain ⟨g,hg,v⟩ := attained high m x
    obtain ⟨gs,hgates,eq⟩ := ih (base+1) (Function.update x base (extreme high m x))
    refine ⟨g::gs,.cons hg hgates,?_⟩
    change run (base+1) (Function.update x base (value g x)) gs = _
    rw [v,eq]; rfl

theorem realRun {n} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) :
    run n (inputs x) gs w = circuitFun n ⟨gs,w⟩ x := tapeOutput ⟨gs,w⟩ x

theorem allChoicesOnRow {n} (menus : List Menu) (w : ℕ) (x : Fin n → Bool) (target : Bool)
    (mono : ∀ m ∈ menus, ∀ g ∈ options m, g.op=.and ∨ g.op=.or) :
    (∀ gs, allowed menus gs → circuitFun n ⟨gs,w⟩ x = target) ↔
      envelope (!target) n (inputs x) menus w = target := by
  constructor
  · intro correct
    obtain ⟨gs,allowed,eq⟩ := attainableTape (!target) n (inputs x) menus
    rw [←eq,realRun]; exact correct gs allowed
  · intro extremum gs chosen
    have cap := envelopeBound (!target) n (inputs x) (inputs x) menus gs chosen mono
      (fun _ => reflDir _ _) w
    rw [realRun,extremum] at cap
    cases target <;> cases h : circuitFun n ⟨gs,w⟩ x <;> simp_all [directed,up]

theorem allChoices {n} (menus : List Menu) (w : ℕ) (f : (Fin n → Bool) → Bool)
    (mono : ∀ m ∈ menus, ∀ g ∈ options m, g.op=.and ∨ g.op=.or) :
    (∀ gs, allowed menus gs → circuitFun n ⟨gs,w⟩ = f) ↔
      ∀ x, envelope (!(f x)) n (inputs x) menus w = f x := by
  constructor
  · intro correct x
    exact (allChoicesOnRow menus w x (f x) mono).mp (fun gs hg => congrFun (correct gs hg) x)
  · intro bound gs hg; funext x
    exact (allChoicesOnRow menus w x (f x) mono).mpr (bound x) gs hg

def changePort (g : Gate) (b w : ℕ) : Gate := ⟨g.op,g.inputs.set b w⟩
def replacePort (C : Circuit) (g b w : ℕ) : Circuit :=
  ⟨C.gates.set g (changePort (gateAt C g) b w),C.output⟩

theorem gateReal (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt,List.getD_eq_getElem?_getD,hj]

theorem oldGate {n} (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 n C) (j : ℕ) (hj : j<C.gates.length) :
    (C.gates[j].op=.and ∨ C.gates[j].op=.or) ∧
    (∀ i ∈ C.gates[j].inputs, i<n+j) ∧ C.gates[j].inputs.length=2 := by
  refine ⟨ao.1 _ (List.getElem_mem hj),?_,ao.2.2 _ (List.getElem_mem hj)⟩
  simpa only [gateReal C j hj] using ao.2.1 j hj

theorem replacementSyntax {n} (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 n C)
    (g b w : ℕ) (early : w<n+g) : PEqualNP.TopForm.IsAO2 n (replacePort C g b w) := by
  let D := replacePort C g b w
  have flags (j) (hj : j < D.gates.length) : (D.gates[j].op=.and ∨ D.gates[j].op=.or) ∧
      (∀ i ∈ D.gates[j].inputs, i<n+j) ∧ D.gates[j].inputs.length=2 := by
    have orig : j<C.gates.length := by simpa [D,replacePort] using hj
    obtain ⟨op,back,len⟩ := oldGate C ao j orig
    by_cases e : g=j
    · subst j
      simp only [D,replacePort,List.getElem_set_self,changePort,gateReal C g orig,List.length_set]
      refine ⟨op,?_,len⟩
      intro i hi
      rcases List.mem_or_eq_of_mem_set hi with old | rfl
      · exact back i old
      · exact early
    · simpa only [D,replacePort,List.getElem_set_ne e] using And.intro op (And.intro back len)
  have all (k : Gate) (hk : k ∈ D.gates) :
      (k.op=.and ∨ k.op=.or) ∧ k.inputs.length=2 := by
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hk
    exact ⟨(flags j hj).1,(flags j hj).2.2⟩
  exact ⟨fun k hk => (all k hk).1,fun j hj => by
    rw [gateReal D j hj]; exact (flags j hj).2.1,fun k hk => (all k hk).2⟩

theorem twoArgs (dir : Bool) (op : GateOp) (kind : op=.and ∨ op=.or) (a b c d : Bool)
    (ac : directed dir a c) (bd : directed dir b d) :
    directed dir (op.eval [a,b]) (op.eval [c,d]) := by
  rcases kind with rfl | rfl <;> cases dir <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [directed,up,GateOp.eval]

theorem portDirection (dir : Bool) (k : Gate) (kind : k.op=.and ∨ k.op=.or)
    (size : k.inputs.length=2) (b old new : ℕ) (hb : b<2) (read : k.inputs.getD b 0=old)
    (s : Pins) (order : directed dir (s old) (s new)) :
    directed dir (value k s) (value (changePort k b new) s) := by
  obtain ⟨a,c,h⟩ := List.length_eq_two.mp size
  interval_cases b
  · have e : a=old := by simpa [h] using read
    simpa [value,changePort,h] using twoArgs dir k.op kind (s a) (s c) (s new) (s c) (e.symm ▸ order) (reflDir _ _)
  · have e : c=old := by simpa [h] using read
    simpa [value,changePort,h] using twoArgs dir k.op kind (s a) (s c) (s a) (s new) (reflDir _ _) (e.symm ▸ order)

theorem replaceOnRows {n} (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 n C)
    (g b w w' : ℕ) (hg : g<C.gates.length) (hb : b<2) (read : (gateAt C g).inputs.getD b 0=w)
    (early : w'<n+g)
    (order : ∀ x : Fin n → Bool, directed (circuitFun n C x) (tape C x w) (tape C x w')) :
    circuitFun n (replacePort C g b w') = circuitFun n C := by
  let D := replacePort C g b w'
  have edited := replacementSyntax C ao g b w' early
  apply batchCorrect C D rfl (by simp [D,replacePort])
  intro x j jo jn
  obtain ⟨kind,go,len⟩ := oldGate C ao j jo
  obtain ⟨newKind,gn,_⟩ := oldGate D edited j jn
  refine ⟨go,gn,newKind,?_⟩
  have get : D.gates[j] = if g=j then changePort (gateAt C g) b w' else C.gates[j] :=
    List.getElem_set (l:=C.gates) (i:=g) (a:=changePort (gateAt C g) b w') (j:=j) (by simpa using jo)
  rw [get]
  by_cases e : g=j
  · subst j; simp only [ite_true,gateReal C g hg]
    exact portDirection _ _ kind len b w w' hb (by simpa only [gateReal C g hg] using read) _ (order x)
  · rw [ite_eq_right e]; exact reflDir _ _

theorem wireValue {n} (C : Circuit) (x : Fin n → Bool) (i : ℕ) :
    tape C x i = Circuit.eval ⟨C.gates,i⟩ (List.ofFn x) := realTape C x i

theorem noCounterexample :
    ¬ ∃ (n : ℕ) (C : Circuit) (g b w w' : ℕ),
      PEqualNP.TopForm.IsAO2 n C ∧ ReadsBack n C ∧ g<C.gates.length ∧ b<2 ∧
      (gateAt C g).inputs.getD b 0=w ∧ w'<n+g ∧
      (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates,w⟩ (List.ofFn x)=true →
        Circuit.eval ⟨C.gates,w'⟩ (List.ofFn x)=true) ∧
      (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates,w'⟩ (List.ofFn x)=true → circuitFun n C x=true) ∧
      ¬ (PEqualNP.TopForm.IsAO2 n (replacePort C g b w') ∧
        circuitFun n (replacePort C g b w')=circuitFun n C ∧ (replacePort C g b w').size=C.size) := by
  rintro ⟨n,C,g,b,w,w',ao,_,hg,hb,read,early,lower,upper,bad⟩
  apply bad
  refine ⟨replacementSyntax C ao g b w' early,replaceOnRows C ao g b w w' hg hb read early ?_,?_⟩
  · intro x
    rw [wireValue,wireValue]
    cases h : circuitFun n C x with
    | true => exact lower x
    | false => exact fun hi => False.elim (Bool.noConfusion (h.symm.trans (upper x hi)))
  · simp [replacePort,Circuit.size]

theorem runMono (gs : List Gate) (base : ℕ) (x y : Pins)
    (kinds : ∀ g ∈ gs, g.op=.and ∨ g.op=.or) (le : ∀ i, up (x i) (y i)) :
    ∀ i, up (run base x gs i) (run base y gs i) := by
  induction gs generalizing base x y with
  | nil => exact le
  | cons g gs ih =>
    apply ih (base+1) _ _ (fun k hk => kinds k (List.mem_cons_of_mem _ hk))
    intro i
    by_cases eq : i=base
    · subst i; simp only [step,Function.update_self]
      exact monotoneValue g (kinds g List.mem_cons_self) x y (fun j _ => le j)
    · simpa [step,Function.update_of_ne eq] using le i

theorem selectedKinds (menus : List Menu) (gs : List Gate) (choices : allowed menus gs)
    (mono : ∀ m ∈ menus, ∀ g ∈ options m, g.op=.and ∨ g.op=.or) :
    ∀ g ∈ gs, g.op=.and ∨ g.op=.or := by
  induction choices with
  | nil => simp
  | @cons m g ms gs hg _ ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | h
    · exact mono m List.mem_cons_self _ hg
    · exact ih (fun v hv => mono v (List.mem_cons_of_mem _ hv)) k h

theorem inputMono {n} (x y : Fin n → Bool) (le : ∀ i, up (x i) (y i)) :
    ∀ i, up (inputs x i) (inputs y i) := by
  intro i; by_cases lt : i<n
  · simpa [inputs,List.getD_eq_getElem?_getD,lt] using le ⟨i,lt⟩
  · simp [inputs,List.getD_eq_getElem?_getD,lt,up]

theorem frontiers {n} (menus : List Menu) (w : ℕ) (f : (Fin n → Bool) → Bool)
    (mono : ∀ m ∈ menus, ∀ g ∈ options m, g.op=.and ∨ g.op=.or)
    (pos neg : Set (Fin n → Bool)) (yes : ∀ p ∈ pos, f p=true) (no : ∀ q ∈ neg, f q=false)
    (below : ∀ x, f x=true → ∃ p ∈ pos, ∀ i, up (p i) (x i))
    (above : ∀ x, f x=false → ∃ q ∈ neg, ∀ i, up (x i) (q i)) :
    (∀ gs, allowed menus gs → circuitFun n ⟨gs,w⟩ = f) ↔
    (∀ p ∈ pos, envelope false n (inputs p) menus w=true) ∧
    (∀ q ∈ neg, envelope true n (inputs q) menus w=false) := by
  constructor
  · intro good; have h := (allChoices menus w f mono).mp good
    exact ⟨fun p hp => by simpa [yes p hp] using h p,fun q hq => by simpa [no q hq] using h q⟩
  · rintro ⟨lo,hi⟩ gs hg
    have step (x y : Fin n → Bool) (xy : ∀ i, up (x i) (y i)) :
        up (circuitFun n ⟨gs,w⟩ x) (circuitFun n ⟨gs,w⟩ y) := by
      rw [←realRun,←realRun]
      exact runMono gs n _ _ (selectedKinds menus gs hg mono) (inputMono x y xy) w
    funext x
    cases eq : f x with
    | true =>
      obtain ⟨p,hp,le⟩ := below x eq
      exact step p x le ((allChoicesOnRow menus w p true mono).mpr (lo p hp) gs hg)
    | false =>
      obtain ⟨q,hq,le⟩ := above x eq
      have top := (allChoicesOnRow menus w q false mono).mpr (hi q hq) gs hg
      cases hx : circuitFun n ⟨gs,w⟩ x with
      | false => rfl
      | true => exact False.elim (Bool.noConfusion (top.symm.trans (step x q le hx)))

def twoEdits (left right : Bool) : Circuit :=
  ⟨[⟨.or,[0,1]⟩,⟨.and,[if left then 2 else 0,if right then 2 else 0]⟩],3⟩

theorem interacting : (∀ x : Fin 2 → Bool, circuitFun 2 (twoEdits true false) x = x 0 ∧
    circuitFun 2 (twoEdits false true) x = x 0 ∧ circuitFun 2 (twoEdits false false) x = x 0) ∧
    circuitFun 2 (twoEdits true true) ![false,true] = true := by decide +kernel

end BatchWireRewrite
