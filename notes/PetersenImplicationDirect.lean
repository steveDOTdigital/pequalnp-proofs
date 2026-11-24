import PEqualNP.Outside.L_meta_517
import PEqualNP.Outside.L_meta_2012

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Live514
namespace Implication3180

abbrev Bits := Fin 9 → Bool
def graph (x : Bits) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
def theta (y : Fin 7 → Bool) : Bool :=
  (y 0 && y 2) || (y 2 && y 1) || (y 0 && y 3) || (y 3 && y 4) ||
  (y 4 && y 1) || (y 0 && y 5) || (y 5 && y 6) || (y 6 && y 1)
def deletion (y : Fin 8 → Bool) : Bool := theta (fun i => y i.castSucc) || (y 7 && y 2)

theorem rawKnown : ¬HasCircuitSize 9 graph 14 := by
  have eq : graph = (fun x : Bits => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10))) := by
    funext x
    simp only [List.any_cons,List.any_nil,Bool.or_false,graph,Bool.or_assoc]; rfl
  rw [eq]
  exact PEqualNP.Outside.L_meta_2012

theorem deletionKnown : ¬HasCircuitSize 8 deletion 11 := by
  intro small
  have sensitive : ∃ y : Fin 8 → Bool, deletion (Function.update y (Fin.last 7) (!y (Fin.last 7))) ≠ deletion y := by
    exact ⟨fun i => decide (i=2),by decide⟩
  have nonconst : ∃ y y' : Fin 7 → Bool, deletion (Fin.snoc y false) ≠ deletion (Fin.snoc y' false) := by
    exact ⟨fun _ => false,fun _ => true,by decide⟩
  have restricted := gate_elim 7 deletion false 10 sensitive nonconst small
  have eq : (fun y : Fin 7 → Bool => deletion (Fin.snoc y false)) = theta := by
    funext y
    have last : (Fin.snoc y false : Fin 8 → Bool) (Fin.last 7) = false := Fin.snoc_last _ _
    unfold deletion
    rw [show (7 : Fin 8) = Fin.last 7 from rfl,last]
    simp
  rw [eq] at restricted
  have := PEqualNP.Outside.L_meta_517 10 restricted
  omega

def marked (g : Gate) : Bool := g.inputs.any (fun i => decide (i=0 ∨ i=9 ∨ i=10))
def axis (g : Gate) : Prop := 0 ∈ g.inputs ∨ 9 ∈ g.inputs
def sliceStats : List Stat :=
  [.const false,.wire 3,.wire 0,.wire 2,.wire 7,.wire 6,.wire 4,.wire 5,.wire 1,.const true,.const true]
def inject (y : Fin 8 → Bool) : Bits := ![false,y 3,y 0,y 2,y 7,y 6,y 4,y 5,y 1]
def pins (j : Fin 9) (x : Bits) := List.ofFn x ++ [!x 0, !x 0 || x j]
def readStats (s : List Stat) (w : List Bool) := s.map (Stat.val w)

theorem baseInv {n : ℕ} (s : List Stat) (pre : List Gate) (y : List Bool)
    (valid : ∀ a ∈ s, a.Valid (n+pre.length)) :
    Inv n y (readStats s (wiresFrom pre y)) (s,pre) := by
  constructor
  · simp [readStats]
  intro i
  change (s.getD i (.const false)).Valid (n+pre.length) ∧ (s.getD i (.const false)).val (wiresFrom pre y) = (readStats s (wiresFrom pre y)).getD i false
  by_cases hi : i<s.length
  · rw [List.getD_eq_getElem _ _ hi]
    refine ⟨valid _ (List.getElem_mem _),?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa [readStats] using hi)]
    exact (List.getElem_map ..).symm
  · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp [readStats];omega)]
    exact ⟨trivial,rfl⟩

theorem extract {n budget : ℕ} (f : (Fin n → Bool) → Bool) (s : List Stat) (pre gs : List Gate) (o : ℕ)
    (ok : ∀ g ∈ gs, Ok g) (first : ∀ g ∈ pre, Ok g) (valid : ∀ a ∈ s, a.Valid (n+pre.length))
    (nonconst : ∃ x y, f x ≠ f y)
    (size : (elim n gs (s,pre)).2.length ≤ budget)
    (value : ∀ x : Fin n → Bool,
      (wiresFrom gs (readStats s (wiresFrom pre (List.ofFn x)))).getD o false = f x) :
    HasCircuitSize n f budget := by
  let done := elim n gs (s,pre)
  have value' (x : Fin n → Bool) :
      (done.1.getD o (.const false)).val (wiresFrom done.2 (List.ofFn x)) = f x :=
    ((inv_elim n _ (by simp) gs _ _ ok (baseInv s pre (List.ofFn x) valid)).2 o).2.trans (value x)
  cases e : done.1.getD o (.const false) with
  | const b =>
    obtain ⟨x,y,ne⟩ := nonconst
    apply False.elim; apply ne
    rw [← value' x,← value' y,e]; rfl
  | wire i =>
    refine ⟨⟨done.2,i⟩,elim_ok n gs _ first,size,?_⟩
    intro y
    have h := value' y
    rw [e] at h
    exact h

theorem markedCost (gs : List Gate) (ok : ∀ g ∈ gs, NOk g)
    (acc : List Stat × List Gate)
    (base : ∀ i : ℕ, i=0 ∨ i=9 ∨ i=10 → i<acc.1.length ∧ ∃ b, acc.1.getD i (.const false) = .const b) :
    (elim 8 gs acc).2.length + (gs.filter marked).length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    let next := elimStep 8 acc g
    have keep : ∀ i : ℕ, i=0 ∨ i=9 ∨ i=10 → i<next.1.length ∧ ∃ b, next.1.getD i (.const false) = .const b := by
      intro i h
      obtain ⟨small,b,e⟩ := base i h
      refine ⟨by simp [next,elimStep];omega,b,?_⟩
      change (acc.1++[_]).getD i (.const false) = _
      rw [List.getD_append _ _ _ _ small,e]
    have tail := ih (fun k hk => ok k (List.mem_cons_of_mem _ hk)) next keep
    change (elim 8 gs next).2.length + ((g::gs).filter marked).length ≤ _
    by_cases h : marked g = true
    · obtain ⟨i,hi,hm⟩ := List.any_eq_true.mp h
      have prop : i=0 ∨ i=9 ∨ i=10 := of_decide_eq_true hm
      obtain ⟨_,b,e⟩ := base i prop
      have same := elimStep_none 8 acc g (ok _ List.mem_cons_self) i hi b e
      change next.2.length = acc.2.length at same
      simp [List.filter_cons,h];omega
    · have inc : next.2.length ≤ acc.2.length+1 := by
        simp only [next,elimStep,List.length_append]
        have := toList_length_le ((simplify g.op (8 + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (.const false))).1)
        omega
      simp [List.filter_cons,h];omega

theorem sliceRow (j : Fin 9) (y : Fin 8 → Bool) :
    readStats sliceStats (wiresFrom [] (List.ofFn y)) = pins j (inject y) := by
  change _ = List.ofFn (inject y) ++ [!inject y 0,!inject y 0 || inject y j]
  rw [show List.ofFn (inject y) = [false,y 3,y 0,y 2,y 7,y 6,y 4,y 5,y 1] from rfl]
  simp [readStats,sliceStats,wiresFrom,Stat.val,inject,List.getD_eq_getElem]

theorem sliceGraph (y : Fin 8 → Bool) : graph (inject y) = deletion y := by
  change ((false && y 3) || (y 3 && y 0) || (y 0 && y 2) || (y 2 && y 7) || (y 7 && false) || (false && y 6) ||
    (y 3 && y 4) || (y 0 && y 5) || (y 2 && y 1) || (y 6 && y 5) || (y 4 && y 1) || (y 1 && y 6)) = _
  simp only [deletion,theta,Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or]
  change _ = ((y 0 && y 2) || (y 2 && y 1) || (y 0 && y 3) || (y 3 && y 4) || (y 4 && y 1) || (y 0 && y 5) || (y 5 && y 6) || (y 6 && y 1) || (y 7 && y 2))
  ac_rfl

theorem fewReaders (j : Fin 9) (gs : List Gate) (o : ℕ) (ok : ∀ g ∈ gs, NOk g) (len : gs.length≤13)
    (hit : ∀ x, (wiresFrom gs (pins j x)).getD o false = graph x) : (gs.filter marked).length ≤ 1 := by
  by_contra! many
  apply deletionKnown
  apply extract deletion sliceStats [] gs o (fun g hg => (ok g hg).1) (by simp)
  · intro a ha
    simp only [sliceStats,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with h|h|h|h|h|h|h|h|h|h|h <;> subst a <;> simp [Stat.Valid]
  · exact ⟨fun _ => false,fun _ => true,by decide⟩
  · have counted := markedCost gs ok (sliceStats,[]) (by
      intro i hi; rcases hi with rfl | rfl | rfl <;> exact ⟨by decide,_,rfl⟩)
    simp only [List.length_nil,Nat.zero_add] at counted
    omega
  · intro y; rw [sliceRow j,hit,sliceGraph]


theorem outside (a b t : List Bool) (i : ℕ) (hlen : a.length=b.length)
    (atBase : a.getD i false = b.getD i false) :
    (a++t).getD i false = (b++t).getD i false := by
  by_cases h : i<a.length
  · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (by omega)]; exact atBase
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),hlen]

-- The old input slots may differ. Each computed slot has the same value.
theorem sameSuffix (gs : List Gate) (a b : List Bool)
    (step : ∀ g ∈ gs, ∀ t : List Bool,
      g.op.eval (g.inputs.map fun i => (a++t).getD i false) =
      g.op.eval (g.inputs.map fun i => (b++t).getD i false)) (pre : List Bool) :
    ∃ t, wiresFrom gs (a++pre) = a++t ∧ wiresFrom gs (b++pre) = b++t := by
  induction gs generalizing pre with
  | nil => exact ⟨pre,rfl,rfl⟩
  | cons g gs ih =>
    let z := g.op.eval (g.inputs.map fun i => (a++pre).getD i false)
    have e := step g List.mem_cons_self pre
    obtain ⟨t,ha,hb⟩ := ih (fun k hk => step k (List.mem_cons_of_mem _ hk)) (pre++[z])
    refine ⟨t,?_,?_⟩
    · simpa only [wiresFrom,List.foldl_cons,List.append_assoc,z] using ha
    · change wiresFrom gs ((b++pre)++[_]) = b++t
      rw [← e,List.append_assoc]; exact hb

theorem sameOutput (gs : List Gate) (a b : List Bool) (o : ℕ) (len : a.length=b.length) (hi : a.length≤o)
    (step : ∀ g ∈ gs, ∀ t : List Bool, g.op.eval (g.inputs.map fun i => (a++t).getD i false) =
      g.op.eval (g.inputs.map fun i => (b++t).getD i false)) :
    (wiresFrom gs a).getD o false = (wiresFrom gs b).getD o false := by
  obtain ⟨t,ha,hb⟩ := sameSuffix gs a b step []
  simp only [List.append_nil] at ha hb
  rw [ha,hb,List.getD_append_right _ _ _ _ hi,List.getD_append_right _ _ _ _ (by omega),len]

def bits (r : Fin 512) : Bits := fun i => r.val.testBit i.val
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem pinMismatch : ∀ j : Fin 9, ∀ i : Fin 11, ∃ r : Fin 512,
    (pins j (bits r)).getD i.val false ≠ graph (bits r) := by decide +kernel

theorem beyond (j : Fin 9) (gs : List Gate) (o : ℕ)
    (hit : ∀ x, (wiresFrom gs (pins j x)).getD o false = graph x) : 11≤o := by
  by_contra! low
  obtain ⟨r,h⟩ := pinMismatch j ⟨o,low⟩
  have e := hit (bits r)
  rw [getD_wiresFrom gs _ o (by simpa [pins] using low)] at e
  exact h e

def witness (j : Fin 9) : ℕ := (![0,2,20,10,16,32,80,130,258] : Fin 9 → ℕ) j
def wrow (j : Fin 9) (b : Bool) : Bits := Function.update (fun i => (witness j).testBit i.val) 0 b

set_option maxRecDepth 8000 in
theorem sensitivity : ∀ j : Fin 9, j ≠ 0 → graph (wrow j false) ≠ graph (wrow j true) ∧
    ∀ i : Fin 11, i.val ≠ 0 → i.val ≠ 9 →
      (pins j (wrow j false)).getD i.val false = (pins j (wrow j true)).getD i.val false := by decide +kernel

theorem readsAxis (j : Fin 9) (nz : j≠0) (gs : List Gate) (o : ℕ) (hi : 11≤o)
    (hit : ∀ x, (wiresFrom gs (pins j x)).getD o false = graph x) : ∃ g ∈ gs, axis g := by
  by_contra! noAxis
  obtain ⟨diff,agree⟩ := sensitivity j nz
  apply diff
  rw [← hit,← hit]
  apply sameOutput gs _ _ o (by simp [pins]) (by simpa [pins] using hi)
  intro g mem t
  congr 1
  apply List.map_congr_left
  intro i loc
  apply outside _ _ _ _ (by simp [pins])
  by_cases lo : i<11
  · exact agree ⟨i,lo⟩ (fun e => noAxis g mem (Or.inl (e ▸ loc))) (fun e => noAxis g mem (Or.inr (e ▸ loc)))
  · rw [List.getD_eq_default _ _ (by simp [pins];omega),List.getD_eq_default _ _ (by simp [pins];omega)]

theorem uniqueMarked {gs : List Gate} {a g : Gate} (cap : (gs.filter marked).length ≤ 1)
    (ha : a ∈ gs) (ma : marked a = true) (hg : g ∈ gs) (mg : marked g = true) : g=a := by
  have p := List.mem_filter.mpr (And.intro ha ma)
  have q := List.mem_filter.mpr (And.intro hg mg)
  generalize e : gs.filter marked = l at p q cap
  cases l with
  | nil => simp at p
  | cons k l =>
    have en : l=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at cap;omega)
    subst l; simp only [List.mem_singleton] at p q; exact q.trans p.symm

def alternate (j : Fin 9) (b : Bool) (x : Bits) :=
  List.ofFn x ++ [!x 0,if b then x j else !x 0]

theorem still (j : Fin 9) (b : Bool) (x : Bits) (t : List Bool) (i : ℕ) (ne : i≠10) :
    (pins j x++t).getD i false = (alternate j b x++t).getD i false := by
  apply outside _ _ _ _ (by simp [pins,alternate])
  change ((List.ofFn x++[!x 0])++[_]).getD i false = ((List.ofFn x++[!x 0])++[_]).getD i false
  let base := List.ofFn x++[!x 0]
  have h : i≠base.length := by simpa [base] using ne
  exact (getD_snoc_ne base _ false i h).trans (getD_snoc_ne base _ false i h).symm

theorem withoutExtra (g : Gate) (ng : 10 ∉ g.inputs) (j : Fin 9) (b : Bool) (x : Bits) (t : List Bool) :
    g.op.eval (g.inputs.map fun i => (pins j x++t).getD i false) =
    g.op.eval (g.inputs.map fun i => (alternate j b x++t).getD i false) := by
  congr 1
  apply List.map_congr_left
  intro i hi
  exact still _ _ _ _ _ (fun e => ng (e ▸ hi))

theorem pairForm (l : List ℕ) (i : ℕ) (ne : i≠10) (hlen : l.length≤2) (mem : i∈l) (ten : 10∈l) :
    l=[i,10] ∨ l=[10,i] := by
  cases l with
  | nil => simp at mem
  | cons a r =>
    cases r with
    | nil => simp at mem ten; omega
    | cons b r =>
      have e : r=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen;omega)
      subst r
      simp only [List.mem_cons,List.mem_singleton] at mem ten
      rcases mem with h | h <;> rcases ten with h' | h' <;> simp_all

theorem pinsAt (j : Fin 9) (b : Bool) (x : Bits) (t : List Bool) :
    (pins j x++t).getD 0 false = x 0 ∧ (pins j x++t).getD 9 false = !x 0 ∧
    (pins j x++t).getD 10 false = (!x 0 || x j) ∧
    (alternate j b x++t).getD 0 false = x 0 ∧ (alternate j b x++t).getD 9 false = !x 0 ∧
    (alternate j b x++t).getD 10 false = (if b then x j else !x 0) := by
  repeat' apply And.intro
  all_goals rw [List.getD_append _ _ _ _ (by simp [pins,alternate])]; rfl

-- The single original-pin reader can take xⱼ or NOT x₀ wherever it used the extra OR.
theorem choice (j : Fin 9) (a : Gate) (ok : NOk a) (uses : axis a) : ∃ b : Bool, ∀ x t,
    a.op.eval (a.inputs.map fun i => (pins j x++t).getD i false) =
    a.op.eval (a.inputs.map fun i => (alternate j b x++t).getD i false) := by
  by_cases ten : 10 ∈ a.inputs
  · have shape : a.inputs=[0,10] ∨ a.inputs=[10,0] ∨ a.inputs=[9,10] ∨ a.inputs=[10,9] := by
      rcases uses with m | m
      · rcases pairForm _ 0 (by decide) ok.1.2 m ten with e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (pairForm _ 9 (by decide) ok.1.2 m ten))
    have allowed : a.op=.and ∨ a.op=.or := by
      rcases ok.1.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · have lim := ok.2 h
        rcases shape with e | e | e | e <;> simp [e] at lim
    rcases allowed with op | op <;> rcases shape with e | e | e | e
    all_goals first | (refine ⟨true,?_⟩; intro x t; obtain ⟨aa,bb,dd,aa',bb',dd'⟩ := pinsAt j true x t;
                        simp only [op,e,List.map_cons,List.map_nil,aa,bb,dd,aa',bb',dd',GateOp.eval,List.all_cons,List.all_nil,List.any_cons,List.any_nil, id_eq,ite_true,Bool.and_true,Bool.or_false];
                        cases x 0 <;> cases x j <;> rfl) |
                      (refine ⟨false,?_⟩; intro x t; obtain ⟨aa,bb,dd,aa',bb',dd'⟩ := pinsAt j false x t;
                        simp only [op,e,List.map_cons,List.map_nil,aa,bb,dd,aa',bb',dd',GateOp.eval,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.false_eq_true,ite_false,Bool.and_true,Bool.or_false];
                        cases x 0 <;> cases x j <;> rfl)
  · exact ⟨true,withoutExtra a ten j true⟩


def preNot : List Gate := [⟨.not,[0]⟩]
def aliasStats (j : Fin 9) (b : Bool) : List Stat :=
  [.wire 0,.wire 1,.wire 2,.wire 3,.wire 4,.wire 5,.wire 6,.wire 7,.wire 8,.wire 9,
   .wire (if b then j.val else 9)]

theorem aliasRow (j : Fin 9) (b : Bool) (x : Bits) :
    readStats (aliasStats j b) (wiresFrom preNot (List.ofFn x)) = alternate j b x := by
  fin_cases j <;> cases b <;> rfl

theorem impossible (j : Fin 9) (nz : j≠0) (gs : List Gate) (o : ℕ) (ok : ∀ g ∈ gs, NOk g)
    (len : gs.length≤13) (hit : ∀ x, (wiresFrom gs (pins j x)).getD o false = graph x) : False := by
  have hi := beyond j gs o hit
  have cap := fewReaders j gs o ok len hit
  obtain ⟨a,ha,ax⟩ := readsAxis j nz gs o hi hit
  have ma : marked a = true := by
    apply List.any_eq_true.mpr
    rcases ax with h | h
    · exact ⟨0,h,by decide⟩
    · exact ⟨9,h,by decide⟩
  obtain ⟨b,chosen⟩ := choice j a (ok a ha) ax
  have same (x : Bits) : (wiresFrom gs (pins j x)).getD o false =
      (wiresFrom gs (alternate j b x)).getD o false := by
    apply sameOutput gs _ _ o (by simp [pins,alternate]) (by simpa [pins] using hi)
    intro g hg t
    by_cases d : 10∈g.inputs
    · have mg : marked g = true := List.any_eq_true.mpr ⟨10,d,by decide⟩
      rw [uniqueMarked cap ha ma hg mg]; exact chosen x t
    · exact withoutExtra g d j b x t
  apply rawKnown
  apply extract graph (aliasStats j b) preNot gs o (fun g hg => (ok g hg).1)
  · intro g h; have e : g = ⟨.not,[0]⟩ := by simpa [preNot] using h
    subst g; exact ⟨Or.inr (Or.inr rfl),by decide⟩
  · intro a h
    simp only [aliasStats,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with e|e|e|e|e|e|e|e|e|e|e <;> subst a
    all_goals simp only [Stat.Valid,preNot,List.length_cons,List.length_nil] <;> first | decide | (cases b <;> simp <;> omega)
  · exact ⟨fun _ => false,fun _ => true,by decide⟩
  · have bound := elim_len 9 gs (aliasStats j b,preNot)
    change (elim 9 gs (aliasStats j b,preNot)).2.length ≤ 1+gs.length at bound
    omega
  · intro x; rw [aliasRow,← same,hit]

theorem selector (l : List ℕ) (len : l.length = 2) (range : ∀ k ∈ l, k < 10)
      (nontrivial : ¬∀ k ∈ l, k = 0 ∨ k = 9) (holds : 9 ∈ l) :
      ∃ j : Fin 9, j ≠ 0 ∧ ∀ x : Fin 9 → Bool,
      GateOp.or.eval (l.map fun k => (List.ofFn x ++ [!x 0]).getD k false) = (!x 0 || x j) := by
    obtain ⟨a,b,rfl⟩ : ∃ a b, l = [a,b] := by
      cases l with
      | nil => simp at len
      | cons a tail =>
        cases tail with
        | nil => simp at len
        | cons b rest =>
          have h : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
          exact ⟨a,b,by rw [h]⟩
    have read (x : Fin 9 → Bool) (j : Fin 9) : (List.ofFn x ++ [!x 0]).getD j.val false = x j := by
      rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact j.isLt)]
      rw [List.getD_eq_getElem _ _ (by simpa using j.isLt),List.getElem_ofFn]
    have neg (x : Fin 9 → Bool) : (List.ofFn x ++ [!x 0]).getD 9 false = !x 0 := rfl
    simp only [List.mem_cons,List.not_mem_nil,or_false] at holds
    rcases holds with h | h
    · subst a
      have small : b < 10 := range b (by simp)
      have other : b ≠ 0 ∧ b ≠ 9 := by
        constructor <;> intro e <;> subst b <;> apply nontrivial <;> simp
      let j : Fin 9 := ⟨b,by omega⟩
      refine ⟨j,fun e => other.1 (congrArg Fin.val e),?_⟩
      intro x
      have rb : (List.ofFn x ++ [!x 0]).getD b false = x j := read x j
      change ([(List.ofFn x ++ [!x 0]).getD 9 false,(List.ofFn x ++ [!x 0]).getD b false] : List Bool).any id = _
      rw [neg,rb]
      simp
    · subst b
      have small : a < 10 := range a (by simp)
      have other : a ≠ 0 ∧ a ≠ 9 := by
        constructor <;> intro e <;> subst a <;> apply nontrivial <;> simp
      let j : Fin 9 := ⟨a,by omega⟩
      refine ⟨j,fun e => other.1 (congrArg Fin.val e),?_⟩
      intro x
      have ra : (List.ofFn x ++ [!x 0]).getD a false = x j := read x j
      change ([(List.ofFn x ++ [!x 0]).getD a false,(List.ofFn x ++ [!x 0]).getD 9 false] : List Bool).any id = _
      rw [neg,ra]
      simp [Bool.or_comm]

end Implication3180

open Implication3180 in
theorem PEqualNP.Outside.L_meta_3180 : ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 < (10 : ℕ)) →       (0 : ℕ) ∈ x1 ∨ (9 : ℕ) ∈ x1 →         (¬∀ x5 ∈ x1, x5 = (0 : ℕ) ∨ x5 = (9 : ℕ)) ∧ (9 : ℕ) ∈ x1 →           ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.FanInTwo x6 →               x6.size ≤ (13 : ℕ) →                 ∃ (x9 : Fin (9 : ℕ) → Bool),                   have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];                   x6.eval (x10 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x1)]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro l size limits _ h C hc small
  obtain ⟨j,nz,signal⟩ := selector l size limits h.1 h.2
  by_contra! correct
  apply impossible j nz (C.gates.map normGate) C.output
  · intro g hg
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok k (hc k hk)
  · simpa [Circuit.size] using small
  · intro x
    rw [wiresFrom_norm]
    change C.eval (pins j x) = graph x
    have h := correct x
    dsimp only at h
    rw [signal] at h
    simpa only [pins,List.append_assoc,List.singleton_append,graph,not_not] using h
