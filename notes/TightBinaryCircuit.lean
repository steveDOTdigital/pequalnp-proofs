import Mathlib.Tactic
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.MetaComplexityLgpMono

namespace TightBinaryCircuit
open PEqualNP.CircuitLowerBounds

abbrev Pins := ℕ → Bool

def step (base : ℕ) (g : Gate) (x : Pins) : Pins :=
  Function.update x base (g.op.eval (g.inputs.map x))

def run (base : ℕ) (x : Pins) : List Gate → Pins
  | [] => x
  | g::gs => run (base+1) (step base g x) gs

def pull (base : ℕ) (g : Gate) (S : Finset ℕ) : Finset ℕ :=
  if base ∈ S then S.erase base ∪ g.inputs.toFinset else S

def back (base : ℕ) : List Gate → Finset ℕ → Finset ℕ
  | [],S => S
  | g::gs,S => pull base g (back (base+1) gs S)

theorem stepAgree (w : ℕ) (g : Gate) (S : Finset ℕ) (x y : Pins)
    (same : ∀ i ∈ pull w g S, x i = y i) : ∀ i ∈ S, step w g x i = step w g y i := by
  intro i hi
  by_cases eq : i=w
  · subst i
    simp only [step,Function.update_self]
    congr 1
    apply List.map_congr_left
    intro j hj
    exact same j (by simp [pull,hi,hj])
  · simp only [step,Function.update_of_ne eq]
    apply same i
    by_cases h : w ∈ S <;> simp [pull,h,hi,eq]

theorem backAgree (gs : List Gate) (base : ℕ) (S : Finset ℕ) (x y : Pins)
    (same : ∀ i ∈ back base gs S, x i = y i) : ∀ i ∈ S, run base x gs i = run base y gs i := by
  induction gs generalizing base x y with
  | nil => exact same
  | cons g gs ih => exact ih (base+1) _ _ (stepAgree _ _ _ _ _ same)

theorem snoc (xs : List Bool) (a : Bool) :
    (fun i => (xs++[a]).getD i false) = Function.update (fun i => xs.getD i false) xs.length a := by
  funext i
  by_cases eq : i=xs.length
  · subst i; simp [List.getD_eq_getElem?_getD]
  · rw [Function.update_of_ne eq]
    by_cases lt : i<xs.length
    · exact List.getD_append _ _ _ _ lt
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

def actual (gs : List Gate) (xs : List Bool) :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) xs

theorem simulate (gs : List Gate) (xs : List Bool) :
    (fun i => (actual gs xs).getD i false) = run xs.length (fun i => xs.getD i false) gs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (fun i => (actual gs (xs++[_])).getD i false) = _
    rw [ih,snoc]; simp [run,step]

theorem pullBound (base : ℕ) (g : Gate) (S : Finset ℕ) (width : g.inputs.length ≤ 2) :
    (pull base g S).card ≤ S.card+1 := by
  by_cases live : base ∈ S
  · simp only [pull,ite_eq_left live]
    have h := Finset.card_union_le (S.erase base) g.inputs.toFinset
    have size := Finset.card_erase_of_mem live
    have two := List.toFinset_card_le g.inputs
    have nz := Finset.card_pos.mpr ⟨base,live⟩
    omega
  · simp [pull,live]

theorem backBound (gs : List Gate) (base : ℕ) (S : Finset ℕ)
    (width : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (back base gs S).card ≤ S.card+gs.length := by
  induction gs generalizing base with
  | nil => simp [back]
  | cons g gs ih =>
    have h := ih (base+1) (fun k hk => width k (List.mem_cons_of_mem _ hk))
    have h' := pullBound base g (back (base+1) gs S) (width g List.mem_cons_self)
    simpa only [back,List.length_cons] using (show (pull _ _ _).card ≤ S.card+(gs.length+1) by omega)

def essential (n : ℕ) (C : Circuit) := ∀ i : Fin n, ∃ x y : Fin n → Bool,
  (∀ j, j ≠ i → x j = y j) ∧ C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)

theorem sourceCover (n : ℕ) (C : Circuit) (essentialInput : essential n C) :
    Finset.range n ⊆ back n C.gates {C.output} := by
  intro i hi
  have lt := Finset.mem_range.mp hi
  by_contra absent
  let k : Fin n := ⟨i,lt⟩
  obtain ⟨x,y,other,ne⟩ := essentialInput k
  apply ne
  have same (j : ℕ) (hj : j ∈ back n C.gates {C.output}) :
      (List.ofFn x).getD j false = (List.ofFn y).getD j false := by
    by_cases h : j<n
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,h,Option.getD_some,dite_eq_left]
      apply other; intro eq; exact absent ((Fin.mk.inj eq) ▸ hj)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
  have out := backAgree C.gates n {C.output} _ _ same C.output (Finset.mem_singleton_self _)
  have sem (z : Fin n → Bool) : C.eval (List.ofFn z) =
      run n (fun j => (List.ofFn z).getD j false) C.gates C.output := by
    simpa [Circuit.eval,Circuit.wires,actual] using congrFun (simulate C.gates (List.ofFn z)) C.output
  rw [sem,sem]; exact out

theorem gateLower (n : ℕ) (C : Circuit) (ess : essential n C)
    (width : ∀ g ∈ C.gates, g.inputs.length ≤ 2) : n ≤ C.size+1 := by
  have h := Finset.card_le_card (sourceCover n C ess)
  have b := backBound C.gates n {C.output} width
  simp only [Finset.card_range] at h
  simp only [Finset.card_singleton] at b
  unfold Circuit.size; omega

-- Traverse the output cone backwards. At the essential-input lower bound
-- every gate must replace one live wire by two fresh wires.
theorem freshPair (w : ℕ) (g : Gate) (S : Finset ℕ) (h : g.inputs.length ≤ 2)
    (tight : (pull w g S).card = S.card+1) :
    w ∈ S ∧ ∃ a b, g.inputs=[a,b] ∧ a ≠ b ∧ a ∉ S.erase w ∧ b ∉ S.erase w := by
  have live : w ∈ S := by
    by_contra absent; simp [pull,absent] at tight
  refine ⟨live,?_⟩
  let Z := S.erase w
  have base : Z.card+1=S.card := by
    have := Finset.card_erase_of_mem live; have := Finset.card_pos.mpr ⟨w,live⟩
    dsimp [Z]; omega
  have size : (Z ∪ g.inputs.toFinset).card = Z.card+2 := by
    rw [show Z ∪ g.inputs.toFinset = pull w g S by simp [pull,Z,live],tight,←base]
  have two : 2 ≤ g.inputs.toFinset.card := by
    have := Finset.card_union_le Z g.inputs.toFinset; omega
  rcases he : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩
  · simp [he] at two
  · simp [he] at two
  · have count : (insert a (insert b Z)).card = Z.card+2 := by simpa [he] using size
    have aNew : a ∉ insert b Z := by
      intro old; rw [Finset.insert_eq_of_mem old] at count
      have := Finset.card_insert_le b Z; omega
    have bNew : b ∉ Z := by
      intro old; rw [Finset.insert_eq_of_mem old] at count
      have := Finset.card_insert_le a Z; omega
    exact ⟨a,b,rfl,fun e => aNew (e ▸ Finset.mem_insert_self _ _),
      fun mem => aNew (Finset.mem_insert_of_mem mem),bNew⟩
  · simp [he] at h

inductive Expr where
  | raw (i : ℕ)
  | node (op : GateOp) (a b : Expr)

def Expr.val : Expr → Pins → Bool
  | .raw i,x => x i
  | .node op a b,x => op.eval [a.val x,b.val x]

def Expr.labels : Expr → List ℕ
  | .raw i => [i]
  | .node _ a b => a.labels ++ b.labels

def Expr.ops : Expr → List GateOp
  | .raw _ => []
  | .node op a b => op :: (a.ops ++ b.ops)

def Expr.splice (w : ℕ) (g : GateOp) (a b : ℕ) : Expr → Expr
  | .raw i => if i=w then .node g (.raw a) (.raw b) else .raw i
  | .node op l r => .node op (l.splice w g a b) (r.splice w g a b)

theorem spliceValue (T : Expr) (w : ℕ) (g : Gate) (a b : ℕ) (pair : g.inputs=[a,b]) (x : Pins) :
    (T.splice w g.op a b).val x = T.val (step w g x) := by
  induction T with
  | raw i => by_cases eq : i=w <;> simp [Expr.splice,Expr.val,step,eq,pair]
  | node op l r hl hr => simp [Expr.splice,Expr.val,hl,hr]

theorem spliceMember (T : Expr) (w : ℕ) (g : GateOp) (a b i : ℕ) :
    i ∈ (T.splice w g a b).labels ↔
    (i ∈ T.labels ∧ i ≠ w) ∨ (w ∈ T.labels ∧ (i=a ∨ i=b)) := by
  induction T with
  | raw j => by_cases eq : j=w <;> simp [Expr.labels,Expr.splice,eq]; grind only
  | node op l r hl hr => simp only [Expr.labels,Expr.splice,List.mem_append,hl,hr]; grind only

theorem spliceSize (T : Expr) (w : ℕ) (g : GateOp) (a b : ℕ) :
    (T.splice w g a b).labels.length = T.labels.length + T.labels.count w := by
  induction T with
  | raw i => by_cases eq : i=w <;> simp [Expr.splice,Expr.labels,eq]
  | node op l r hl hr => simp [Expr.labels,Expr.splice,hl,hr]; omega

theorem spliceOps (T : Expr) (w : ℕ) (op : GateOp) (a b : ℕ) :
    ∀ k ∈ (T.splice w op a b).ops, k = op ∨ k ∈ T.ops := by
  induction T with
  | raw i => by_cases eq : i=w <;> simp [Expr.splice,Expr.ops,eq]
  | node cmd l r hl hr =>
    intro k h
    simp only [Expr.splice,Expr.ops,List.mem_cons,List.mem_append] at h ⊢
    rcases h with h | h | h
    · tauto
    · have := hl k h; tauto
    · have := hr k h; tauto

theorem reconstruct (gs : List Gate) (base : ℕ) (T : Expr) (nodup : T.labels.Nodup)
    (width : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (tight : (back base gs T.labels.toFinset).card = T.labels.toFinset.card+gs.length) :
    ∃ Q : Expr, Q.labels.toFinset = back base gs T.labels.toFinset ∧ Q.labels.Nodup ∧
      (∀ k ∈ Q.ops, k ∈ T.ops ∨ ∃ g ∈ gs, g.op=k) ∧
      ∀ x, Q.val x = T.val (run base x gs) := by
  induction gs generalizing base with
  | nil => exact ⟨T,rfl,nodup,fun k hk => Or.inl hk,fun _ => rfl⟩
  | cons g gs ih =>
    let S := back (base+1) gs T.labels.toFinset
    have wg := width g List.mem_cons_self
    have ws : ∀ a ∈ gs, a.inputs.length ≤ 2 := fun a ha => width a (List.mem_cons_of_mem _ ha)
    have suf := backBound gs (base+1) T.labels.toFinset ws
    have add := pullBound base g S wg
    change (pull base g S).card = T.labels.toFinset.card+(gs.length+1) at tight
    change S.card ≤ _ at suf
    have gain : (pull base g S).card = S.card+1 := by omega
    obtain ⟨R,labels,nr,ops,evalR⟩ := ih (base+1) ws (show S.card = _ by omega)
    change R.labels.toFinset = S at labels
    obtain ⟨live,a,b,pair,_,_,_⟩ := freshPair base g S wg gain
    let Q := R.splice base g.op a b
    have labelSet : Q.labels.toFinset = pull base g S := by
      ext i
      have mem (j : ℕ) : j ∈ R.labels ↔ j ∈ S := by rw [←labels]; simp
      simp [Q,spliceMember,mem,pull,live,pair]
      tauto
    have once := List.nodup_iff_count_eq_one.mp nr base (show base ∈ R.labels by
      rw [←List.mem_toFinset,labels]; exact live)
    have distinct : Q.labels.Nodup := by
      apply List.dedup_eq_self.mp
      apply (List.dedup_sublist _).eq_of_length
      change Q.labels.toFinset.card = Q.labels.length
      rw [labelSet,gain,←labels,List.toFinset_card_of_nodup nr]
      simp [Q,spliceSize,once]
    refine ⟨Q,labelSet,distinct,?_,?_⟩
    · intro k hk
      rcases spliceOps R base g.op a b k hk with eq | old
      · exact Or.inr ⟨g,List.mem_cons_self,eq.symm⟩
      · rcases ops k old with ht | ⟨j,hj,e⟩
        · exact Or.inl ht
        · exact Or.inr ⟨j,List.mem_cons_of_mem _ hj,e⟩
    · intro x
      change (R.splice base g.op a b).val x = _
      rw [spliceValue R base g a b pair,evalR]; rfl

theorem tightCircuit (n : ℕ) (C : Circuit) (ess : essential n C)
    (width : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (budget : C.size+1=n) :
    ∃ T : Expr, T.labels.toFinset = Finset.range n ∧ T.labels.Nodup ∧
      (∀ k ∈ T.ops, ∃ g ∈ C.gates, g.op=k) ∧
      ∀ x : Fin n → Bool, T.val (fun i => (List.ofFn x).getD i false) = C.eval (List.ofFn x) := by
  have incl := sourceCover n C ess
  have bound := backBound C.gates n {C.output} width
  have size : (back n C.gates {C.output}).card ≤ n := by
    simp only [Finset.card_singleton] at bound
    unfold Circuit.size at budget; omega
  have eq := Finset.eq_of_subset_of_card_le incl (by simpa using size)
  have tight : (back n C.gates {C.output}).card = 1+C.gates.length := by
    rw [←eq,Finset.card_range,←budget]; simp [Circuit.size,Nat.add_comm]
  obtain ⟨T,set,nd,ops,e⟩ := reconstruct C.gates n (.raw C.output) (by simp [Expr.labels]) width
    (by simpa [Expr.labels] using tight)
  refine ⟨T,by simpa [Expr.labels,←eq] using set,nd,?_,?_⟩
  · intro k hk; simpa [Expr.ops] using ops k hk
  · intro x
    have sem := congrFun (simulate C.gates (List.ofFn x)) C.output
    rw [e]
    change run n _ C.gates C.output = (actual C.gates (List.ofFn x)).getD C.output false
    simpa only [List.length_ofFn] using sem.symm

def unaryChange (T : Expr) (x y : Pins) (i : ℕ) : Prop :=
  T.val (Function.update x i false) = false ∧ T.val (Function.update y i true) = true

theorem sameValues (T : Expr) (x y : Pins) (h : ∀ i ∈ T.labels, x i = y i) :
    T.val x = T.val y := by
  induction T with
  | raw i => exact h i (by simp [Expr.labels])
  | node op l r hl hr =>
    simp only [Expr.val]
    rw [hl (fun i hi => h i (by simp [Expr.labels,hi])),hr (fun i hi => h i (by simp [Expr.labels,hi]))]

theorem irrelevant (T : Expr) (x : Pins) (i : ℕ) (b : Bool) (absent : i ∉ T.labels) :
    T.val (Function.update x i b) = T.val x := by
  apply sameValues
  intro j hj
  have diff : j ≠ i := fun eq => absent (eq ▸ hj)
  exact Function.update_of_ne diff _ _

-- A true and a false assignment to a read-once monotone formula have at
-- most one coordinate individually pivotal on both sides.
theorem leftChange (op : GateOp) (l r : Expr) (x y : Pins)
    (kind : op = .and ∨ op = .or) (apart : l.labels.Disjoint r.labels)
    (lx : l.val x = true) (ly : l.val y = false)
    (on : (Expr.node op l r).val x = true) (off : (Expr.node op l r).val y = false)
    (i : ℕ) (piv : unaryChange (.node op l r) x y i) : unaryChange l x y i := by
  obtain ⟨zero,one⟩ := piv
  have use : i ∈ l.labels := by
    by_contra miss
    have xu := irrelevant l x i false miss
    have yu := irrelevant l y i true miss
    rcases kind with rfl | rfl <;> simp [Expr.val,GateOp.eval,xu,yu,lx,ly] at zero one
  have miss := apart use
  have xu := irrelevant r x i false miss
  have yu := irrelevant r y i true miss
  rcases kind with rfl | rfl <;> simp [Expr.val,GateOp.eval,lx,ly,xu,yu] at on off zero one <;>
    simp_all [unaryChange]

theorem swapValue (op : GateOp) (kind : op = .and ∨ op = .or) (l r : Expr) (x : Pins) :
    (Expr.node op r l).val x = (Expr.node op l r).val x := by
  rcases kind with rfl | rfl <;> simp [Expr.val,GateOp.eval,Bool.or_comm,Bool.and_comm]

theorem oneCommonPivot (T : Expr) (nd : T.labels.Nodup)
    (mono : ∀ op ∈ T.ops, op = .and ∨ op = .or) (x y : Pins)
    (on : T.val x = true) (off : T.val y = false)
    (i j : ℕ) (ci : unaryChange T x y i) (cj : unaryChange T x y j) : i=j := by
  induction T with
  | raw w =>
    change x w = true at on
    obtain ⟨hi,_⟩ := ci
    obtain ⟨hj,_⟩ := cj
    change Function.update x i false w = false at hi
    change Function.update x j false w = false at hj
    by_contra ne
    by_cases eq : w=i
    · have diff : w ≠ j := eq ▸ ne
      simp [Function.update_of_ne diff,on] at hj
    · simp [Function.update_of_ne eq,on] at hi
  | node op l r hl hr =>
    have ok := List.nodup_append.mp nd
    have apart : l.labels.Disjoint r.labels := fun _ hl hr => ok.2.2 _ hl _ hr rfl
    have kind := mono op (by simp [Expr.ops])
    have ml (k) (hk : k ∈ l.ops) := mono k (by simp [Expr.ops,hk])
    have mr (k) (hk : k ∈ r.ops) := mono k (by simp [Expr.ops,hk])
    have valid : (l.val x=true ∧ l.val y=false) ∨ (r.val x=true ∧ r.val y=false) := by
      rcases kind with rfl | rfl <;>
        cases xl : l.val x <;> cases xr : r.val x <;> cases yl : l.val y <;> cases yr : r.val y <;>
        simp_all [Expr.val,GateOp.eval]
    rcases valid with ⟨lx,ly⟩ | ⟨rx,ry⟩
    · exact hl ok.1 ml lx ly (leftChange op l r x y kind apart lx ly on off i ci)
        (leftChange op l r x y kind apart lx ly on off j cj)
    · have change (k) (ck : unaryChange (.node op l r) x y k) : unaryChange r x y k := by
        apply leftChange op r l x y kind apart.symm rx ry
        · simpa only [swapValue op kind l r] using on
        · simpa only [swapValue op kind l r] using off
        · simpa only [unaryChange,swapValue op kind l r] using ck
      exact hr ok.2.1 mr rx ry (change i ci) (change j cj)

def evalOn {n : ℕ} (C : Circuit) (x : Fin n → Bool) := C.eval (List.ofFn x)

theorem extendUpdate {n} (x : Fin n → Bool) (i : Fin n) (b : Bool) :
    (fun j => (List.ofFn (Function.update x i b)).getD j false) =
    Function.update (fun j => (List.ofFn x).getD j false) i.val b := by
  funext j
  by_cases eq : j=i.val
  · subst j; simp [List.getD_eq_getElem?_getD,i.isLt]
  · by_cases lt : j<n
    · have diff : (⟨j,lt⟩ : Fin n) ≠ i := fun h => eq (congrArg Fin.val h)
      simp [Function.update_of_ne eq,Function.update_of_ne diff,List.getD_eq_getElem?_getD,lt]
    · simp [Function.update_of_ne eq,List.getD_eq_getElem?_getD,lt]

theorem twoPivotLower {n : ℕ} (C : Circuit) (ess : essential n C)
    (mono : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (on : evalOn C x = true) (off : evalOn C y = false)
    (i j : Fin n) (different : i ≠ j)
    (changes : ∀ k ∈ [i,j], evalOn C (Function.update x k false) = false ∧
      evalOn C (Function.update y k true) = true) : n ≤ C.size := by
  by_contra! short
  have w := fun g hg => (mono g hg).2
  have base := gateLower n C ess w
  obtain ⟨T,_,nd,ops,compute⟩ := tightCircuit n C ess w (by omega)
  let ext (z : Fin n → Bool) := fun j => (List.ofFn z).getD j false
  have evaluates (z) : T.val (ext z) = evalOn C z := compute z
  have crit (k : Fin n) (hk : k ∈ [i,j]) : unaryChange T (ext x) (ext y) k.val := by
    obtain ⟨lo,hi⟩ := changes k hk
    constructor
    · rw [←extendUpdate x k false]; exact (evaluates _).trans lo
    · rw [←extendUpdate y k true]; exact (evaluates _).trans hi
  apply different
  apply Fin.ext
  apply oneCommonPivot T nd (fun k hk => by
    obtain ⟨g,hg,rfl⟩ := ops k hk; exact (mono g hg).1) (ext x) (ext y)
    ((evaluates x).trans on) ((evaluates y).trans off) i j (crit i (by simp)) (crit j (by simp))

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def bits {n} (S : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ S)

theorem graphOn {n} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (x : Fin n → Bool) :
    graphFun K ∅ x = true ↔ ∃ a b, K.Adj a b ∧ x a=true ∧ x b=true := by simp [graphFun]

theorem pairEdge {n} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (a b : Fin n) :
    graphFun K ∅ (bits {a,b}) = true ↔ K.Adj a b := by
  rw [graphOn]
  constructor
  · rintro ⟨u,v,edge,hu,hv⟩
    simp [bits] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with eq | eq <;> subst_vars <;>
      first | exact edge | exact edge.symm | exact (K.loopless.irrefl _ edge).elim
  · exact fun edge => ⟨a,b,edge,by simp [bits],by simp [bits]⟩

theorem noSingleton {n} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (a : Fin n) :
    graphFun K ∅ (bits {a}) = false := by
  have h := (pairEdge K a a).not
  simpa using h.mpr (K.loopless.irrefl a)

theorem graphEssential {n} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (noIsolates : ∀ i, ∃ j, K.Adj i j) (C : Circuit)
    (correct : ∀ x : Fin n → Bool, evalOn C x = graphFun K ∅ x) : essential n C := by
  intro i
  obtain ⟨j,edge⟩ := noIsolates i
  refine ⟨bits {j},bits {i,j},fun k hk => by simp [bits,hk],?_⟩
  change evalOn C _ ≠ evalOn C _
  rw [correct,correct,noSingleton,(pairEdge _ _ _).mpr edge]; decide

theorem clearEndpoint {n} (b c : Fin n) (ne : b≠c) :
    Function.update (bits {b,c}) b false = bits {c} := by
  funext j; by_cases eq : j=b <;> simp [eq,bits,ne,Function.update_of_ne]

theorem graphPathLower {n} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (noIsolates : ∀ i, ∃ j, K.Adj i j) (C : Circuit) (hm : Monotone2 C)
    (correct : ∀ x : Fin n → Bool, evalOn C x = graphFun K ∅ x)
    (a b c d : Fin n) (ab : K.Adj a b) (bc : K.Adj b c) (cd : K.Adj c d)
    (outer : ¬ K.Adj a d) : n ≤ C.size := by
  let x := bits {b,c}
  let y := bits {a,d}
  have on : evalOn C x = true := (correct _).trans ((pairEdge K b c).mpr bc)
  have off : evalOn C y = false := by
    rw [correct]
    cases h : graphFun K ∅ y with
    | false => rfl
    | true => exact (outer ((pairEdge K a d).mp h)).elim
  apply twoPivotLower C (graphEssential K noIsolates C correct) (fun g hg =>
    ⟨by simpa using (hm g hg).1,(hm g hg).2⟩) x y on off b c bc.ne
  intro k hk
  rcases List.mem_cons.mp hk with eq | hk
  · subst k
    constructor
    · rw [correct]; change graphFun K ∅ (Function.update (bits {b,c}) b false) = false
      rw [clearEndpoint b c bc.ne]; exact noSingleton K c
    · rw [correct,graphOn]
      exact ⟨a,b,ab,by simp [y,bits,Function.update_of_ne ab.ne],by simp⟩
  · have e := List.mem_singleton.mp hk
    subst k
    constructor
    · rw [correct]; change graphFun K ∅ (Function.update (bits {b,c}) c false) = false
      rw [Finset.pair_comm,clearEndpoint c b bc.ne.symm]; exact noSingleton K b
    · rw [correct,graphOn]
      exact ⟨c,d,cd,by simp,by simp [y,bits,Function.update_of_ne cd.ne.symm]⟩

def target (z : Fin 5 → Bool) :=
  (z 0 && z 2) || (z 0 && z 3) || (z 0 && z 4) || (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4)

def four : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.or,[2,3]⟩,⟨.or,[6,4]⟩,⟨.and,[5,7]⟩],8⟩

theorem fourLegal : Monotone2 four ∧ ReadsBack 5 four := by
  constructor
  · intro g hg
    simp [four] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · intro j hj i hi
    change j < 4 at hj
    interval_cases j <;> simp [gateAt,four] at hi <;> omega

theorem fourComputes : ∀ x : Fin 5 → Bool, evalOn four x = target x := by decide +kernel

theorem targetEssential (C : Circuit) (correct : ∀ x : Fin 5 → Bool, evalOn C x = target x) :
    essential 5 C := by
  have sensitivity : ∀ i : Fin 5, ∃ x y : Fin 5 → Bool,
      (∀ j, j≠i → x j = y j) ∧ target x ≠ target y := by decide +kernel
  intro i
  obtain ⟨x,y,agree,diff⟩ := sensitivity i
  exact ⟨x,y,agree,by change evalOn C x ≠ evalOn C y; rwa [correct,correct]⟩

theorem noThree : ¬ ∃ C : Circuit, Monotone2 C ∧ ReadsBack 5 C ∧ C.size ≤ 3 ∧
    ∀ x : Fin 5 → Bool, evalOn C x = target x := by
  rintro ⟨C,hm,_,cap,correct⟩
  have := gateLower 5 C (targetEssential C correct) (fun g hg => (hm g hg).2)
  omega

theorem fourSharp : four.size=4 ∧ Monotone2 four ∧ ReadsBack 5 four ∧
    ∀ x : Fin 5 → Bool, evalOn four x = target x :=
  ⟨rfl,fourLegal.1,fourLegal.2,fourComputes⟩

theorem tightThreeEdges {n} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (noIsolates : ∀ i, ∃ j, K.Adj i j) (C : Circuit) (hm : Monotone2 C)
    (correct : ∀ x : Fin n → Bool, evalOn C x = graphFun K ∅ x) (size : C.size+1=n)
    (a b c d : Fin n) (ab : K.Adj a b) (bc : K.Adj b c) (cd : K.Adj c d) : K.Adj a d := by
  by_contra missing
  have := graphPathLower K noIsolates C hm correct a b c d ab bc cd missing
  omega

theorem tightNeighborhoods {n} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (noIsolates : ∀ i, ∃ j, K.Adj i j) (C : Circuit) (hm : Monotone2 C)
    (correct : ∀ x : Fin n → Bool, evalOn C x = graphFun K ∅ x) (size : C.size+1=n)
    {a b c : Fin n} (ab : K.Adj a b) (bc : K.Adj b c) : K.neighborSet a = K.neighborSet c := by
  ext d; change K.Adj a d ↔ K.Adj c d
  exact ⟨tightThreeEdges K noIsolates C hm correct size c b a d bc.symm ab.symm,
    tightThreeEdges K noIsolates C hm correct size a b c d ab bc⟩

-- Each unit of missing growth is visible in the backwards frontier. This
-- also works for invalid reads, repeated operands, dead and constant gates.
def losses (base : ℕ) : List Gate → Finset ℕ → List ℕ
  | [],_ => []
  | g::gs,S =>
    let R := back (base+1) gs S
    (R.card+1-(pull base g R).card) :: losses (base+1) gs S

theorem frontierIdentity (gs : List Gate) (base : ℕ) (S : Finset ℕ)
    (width : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (back base gs S).card + (losses base gs S).sum = S.card + gs.length := by
  induction gs generalizing base with
  | nil => simp [back,losses]
  | cons g gs ih =>
    have sum := ih (base+1) (fun k hk => width k (List.mem_cons_of_mem _ hk))
    have step := pullBound base g (back (base+1) gs S) (width g List.mem_cons_self)
    simp only [back,losses,List.sum_cons,List.length_cons]; omega

theorem exactExcess (n : ℕ) (C : Circuit) (ess : essential n C)
    (width : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    n + (back n C.gates {C.output} \ Finset.range n).card +
      (losses n C.gates {C.output}).sum = C.size + 1 := by
  have count := frontierIdentity C.gates n {C.output} width
  have sub := sourceCover n C ess
  have eq := Finset.card_sdiff_add_card_eq_card sub
  simp only [Finset.card_singleton] at count
  simp only [Finset.card_range] at eq
  unfold Circuit.size; omega

-- A subcircuit whose private inputs leave it through a single bit can
-- communicate at most two distinct residual functions to the other inputs.
def binaryCut {n} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (S : Finset (Fin n)) :=
  ∃ tag : Finset (Fin n) → Bool, ∀ A ⊆ S, ∀ B ⊆ S, tag A=tag B →
    ∀ W : Finset (Fin n), Disjoint W S →
      graphFun K ∅ (bits (A ∪ W)) = graphFun K ∅ (bits (B ∪ W))

theorem binaryCutTwins {n} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (noIsolates : ∀ i, ∃ j, K.Adj i j) (S : Finset (Fin n)) (cut : binaryCut K S)
    {p l : Fin n} (pin : p ∈ S) (out : l ∉ S) (edge : K.Adj p l) :
    (∀ a ∈ S, ∀ b ∈ S, ¬ K.Adj a b) ∧
      ∀ a ∈ S, ∀ b ∈ S, K.neighborSet a = K.neighborSet b := by
  obtain ⟨tag,same⟩ := cut
  have empty : graphFun K ∅ (bits ∅) = false := by simp [graphFun,bits]
  have different (a b : Fin n) (inside : a ∈ S) (outside : b ∉ S) (cross : K.Adj a b) :
      tag {a} ≠ tag ∅ := by
    intro eq
    have h := same {a} (by simpa using inside) ∅ (by simp) eq {b} (by simpa using outside)
    have v := (pairEdge K a b).mpr cross
    simp [noSingleton,v] at h
  have two := different p l pin out edge
  have separate (a b : Fin n) (ha : a ∈ S) (hb : b ∈ S) : ¬ K.Adj a b := by
    intro ab
    have v := (pairEdge K a b).mpr ab
    have hp : tag {a,b} = tag ∅ ∨ tag {a,b} = tag {p} := by
      cases tag {a,b} <;> cases h : tag ∅ <;> cases h' : tag {p} <;> simp_all
    rcases hp with eq | eq
    · have h := same {a,b} (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro ha hb) ∅ (by simp) eq ∅ (by simp)
      simp [v,empty] at h
    · have h := same {a,b} (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro ha hb) {p} (by simpa using pin) eq ∅ (by simp)
      simp [v,noSingleton] at h
  refine ⟨fun a ha b hb => separate a b ha hb,?_⟩
  have nz (a : Fin n) (ha : a ∈ S) : tag {a} ≠ tag ∅ := by
    obtain ⟨b,ab⟩ := noIsolates a
    exact different a b ha (fun hb => separate a b ha hb ab) ab
  intro a ha b hb
  have eq : tag {a} = tag {b} := by
    have x := nz a ha; have y := nz b hb
    cases h : tag {a} <;> cases h' : tag {b} <;> cases t : tag ∅ <;> simp_all
  ext d; change K.Adj a d ↔ K.Adj b d
  by_cases inside : d ∈ S
  · simp [separate a d ha inside,separate b d hb inside]
  · have h := same {a} (by simpa using ha) {b} (by simpa using hb) eq {d} (by simpa using inside)
    rw [←pairEdge,←pairEdge K b d]
    have hh : graphFun K ∅ (bits {a,d}) = graphFun K ∅ (bits {b,d}) := by simpa using h
    rw [hh]

end TightBinaryCircuit
