import PEqualNP.Defs.CircuitMoves
import PEqualNP.Defs.MetaComplexityLgpMono

namespace OrderFourErasure18057

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

private theorem runLength (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

private theorem readAppend (w : List Bool) (v : Bool) (i : Nat) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h, ite_eq_right (by omega)]
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt h)]
    by_cases eq : i = w.length
    · subst i
      rw [ite_eq_left rfl, Nat.sub_self]
      rfl
    · rw [ite_eq_right eq]
      have i1 : 1 ≤ i - w.length := by omega
      have i2 : w.length ≤ i := by omega
      have singleton : [v].length ≤ i - w.length := by simpa using i1
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none singleton,
        List.getElem?_eq_none i2]

private theorem runOld (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem redirectEnd (n m p i limit : Nat) (before : p < n + m)
    (room : n + m ≤ limit) :
    eraseRedirect n m p i = limit ↔ i = limit + 1 := by
  unfold eraseRedirect
  split <;> (first | omega | split <;> omega)

private theorem afterEraseRun (n m p : Nat) (gs : List Gate) (old new : List Bool)
    (before : p < n + m) (room : n + m ≤ new.length)
    (width : old.length = new.length + 1)
    (allAgree : ∀ i, (i ≠ n+m ∨ old.getD (n+m) false = new.getD p false) →
      old.getD i false = new.getD (eraseRedirect n m p i) false)
    (safe : (old.getD (n+m) false = new.getD p false) ∨
      ∀ g ∈ gs, n+m ∉ g.inputs) :
    ∀ i, (i ≠ n+m ∨ old.getD (n+m) false = new.getD p false) →
      (run gs old).getD i false =
      (run (gs.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) new).getD
        (eraseRedirect n m p i) false := by
  induction gs generalizing old new with
  | nil => exact allAgree
  | cons g gs ih =>
    have h : ∀ i ∈ g.inputs, old.getD i false =
        new.getD (eraseRedirect n m p i) false := by
      intro i mem
      apply allAgree
      rcases safe with equal | unread
      · exact Or.inr equal
      · exact Or.inl (fun e => unread g (by simp) (e ▸ mem))
    let v := g.op.eval (g.inputs.map fun i => old.getD i false)
    have mapped : step new ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ = new ++ [v] := by
      unfold step v
      rw [List.map_map]
      have e : (g.inputs.map fun i => new.getD (eraseRedirect n m p i) false) =
          (g.inputs.map fun i => old.getD i false) :=
        List.map_congr_left (fun i mem => (h i mem).symm)
      change new ++ [g.op.eval (g.inputs.map fun i => new.getD (eraseRedirect n m p i) false)] = _
      rw [e]
    have eqAt : (old ++ [v]).getD (n+m) false = old.getD (n+m) false := by
      rw [readAppend, ite_eq_right (by omega)]
    have eqNew : (new ++ [v]).getD p false = new.getD p false := by
      rw [readAppend, ite_eq_right (by omega)]
    have advance : ∀ i,
        (i ≠ n+m ∨ (old ++ [v]).getD (n+m) false = (new ++ [v]).getD p false) →
        (old ++ [v]).getD i false =
          (new ++ [v]).getD (eraseRedirect n m p i) false := by
      intro i hi
      rw [eqAt,eqNew] at hi
      simp only [readAppend,width,redirectEnd _ _ _ _ _ before room]
      split
      · rfl
      · exact allAgree i hi
    intro i hi
    change (run gs (step old g)).getD i false =
      (run (gs.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩)
        (step new ⟨g.op,g.inputs.map (eraseRedirect n m p)⟩)).getD
          (eraseRedirect n m p i) false
    rw [mapped]
    change (run gs (old ++ [v])).getD i false = _
    apply ih
    · simp only [List.length_append,List.length_cons,List.length_nil]
      omega
    · simp only [List.length_append,List.length_cons,List.length_nil]
      omega
    · exact advance
    · simpa only [eqAt,eqNew] using safe.imp_right
        (fun no g mem => no g (List.mem_cons_of_mem _ mem))
    · simpa only [eqAt,eqNew] using hi

private theorem runAppend (L R : List Gate) (x : List Bool) :
    run (L ++ R) x = run R (run L x) := by
  unfold run
  exact List.foldl_append

private theorem tapeStart (n m p : Nat) (w : List Bool) (v : Bool) (len : w.length = n+m)
    : ∀ i, (i ≠ n+m ∨ v = w.getD p false) →
      (w ++ [v]).getD i false = w.getD (eraseRedirect n m p i) false := by
  intro i allowed
  unfold eraseRedirect
  by_cases eq : i = n+m
  · simp only [eq,len,readAppend]
    exact allowed.resolve_left (fun bad => bad eq)
  · rw [ite_eq_right eq]
    by_cases gt : n+m < i
    · rw [ite_eq_left gt,readAppend,ite_eq_right (by omega)]
      have out : w.length ≤ i := by omega
      have out' : w.length ≤ i-1 := by omega
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none out,List.getElem?_eq_none out']
    · rw [ite_eq_right gt,readAppend,ite_eq_right (by omega)]

theorem eraseEval (n : Nat) (C : Circuit) (m p : Nat) (x : List Bool)
    (len : x.length = n) (bound : m < C.size) (before : p < n+m)
    (safe : (C.wires x).getD (n+m) false = (C.wires x).getD p false ∨
       (C.output ≠ n+m ∧ ∀ g ∈ C.gates.drop (m+1), n+m ∉ g.inputs)) :
    (eraseGate n C m p).eval x = C.eval x := by
  have idx : m < C.gates.length := bound
  let L := C.gates.take m
  let R := C.gates.drop (m+1)
  let g := C.gates[m]
  have allGates : C.gates = L ++ g :: R := by
    conv_lhs => rw [← List.take_append_drop m C.gates]
    exact congrArg (L ++ ·) (List.drop_eq_getElem_cons idx)
  let tape := run L x
  let v := g.op.eval (g.inputs.map fun i => tape.getD i false)
  have width : tape.length = n+m := by
    change (run L x).length = _
    rw [runLength,len]
    simp [L,Nat.min_eq_left (Nat.le_of_lt idx)]
  have old : C.wires x = run R (tape ++ [v]) := by
    change run C.gates x = _
    rw [allGates,runAppend]
    rfl
  have atMark : (tape ++ [v]).getD (n+m) false = v := by simp [width]
  have atDest : (tape ++ [v]).getD p false = tape.getD p false := by
    rw [readAppend,width,ite_eq_right (by omega)]
  have extended : (tape ++ [v]).length = tape.length+1 := by simp
  have sourceValue : (C.wires x).getD (n+m) false = v := by
    rw [old,runOld _ _ _ (by omega),atMark]
  have destValue : (C.wires x).getD p false = tape.getD p false := by
    rw [old,runOld _ _ _ (by omega),atDest]
  have safe' : v = tape.getD p false ∨
      (C.output ≠ n+m ∧ ∀ g ∈ R, n+m ∉ g.inputs) := by
    simpa only [sourceValue,destValue] using safe
  let G := R.map (fun gate : Gate => (⟨gate.op, gate.inputs.map (eraseRedirect n m p)⟩ : Gate))
  have shortened : (eraseGate n C m p).wires x = run G tape := by
    change run (eraseGate n C m p).gates x = _
    simp only [eraseGate,ite_eq_left idx]
    exact runAppend L G x
  have out : (eraseGate n C m p).output = eraseRedirect n m p C.output := by
    simp [eraseGate,idx]
  have h := afterEraseRun n m p R (tape ++ [v]) tape before (by omega) extended
  have h' := h (by
      intro i premise
      simp only [atMark] at premise
      exact tapeStart _ _ _ _ _ width i premise)
    (by
      rcases safe' with values | garbage
      · exact Or.inl (by simpa only [atMark] using values)
      · exact Or.inr garbage.2)
    C.output
    (by
      rcases safe' with values | garbage
      · exact Or.inr (by simpa only [atMark] using values)
      · exact Or.inl garbage.1)
  change ((eraseGate n C m p).wires x).getD (eraseGate n C m p).output false =
    (C.wires x).getD C.output false
  rw [shortened,out,old]
  exact h'.symm

theorem eraseSize (n : Nat) (C : Circuit) (m p : Nat) (bound : m < C.size) :
    (eraseGate n C m p).size = C.size-1 := by
  have idx : m < C.gates.length := bound
  simp only [Circuit.size,eraseGate,ite_eq_left idx,List.length_append,List.length_map,
    List.length_take,Nat.min_eq_left (Nat.le_of_lt idx),List.length_drop]
  omega

theorem eraseMono (n : Nat) (C : Circuit) (m p : Nat) (legal : Monotone2 C) :
    Monotone2 (eraseGate n C m p) := by
  unfold eraseGate
  split
  · intro g memb
    change g ∈ C.gates.take m ++
      (C.gates.drop (m+1)).map (fun h => ⟨h.op,h.inputs.map (eraseRedirect n m p)⟩) at memb
    rcases List.mem_append.mp memb with left | right
    · exact legal g (List.mem_of_mem_take left)
    · obtain ⟨h,mem,rfl⟩ := List.mem_map.mp right
      simpa using legal h (List.mem_of_mem_drop mem)
  · exact legal

#print axioms eraseEval
#print axioms eraseSize
#print axioms eraseMono

private theorem orPairCopy (q r width : Nat) (hq : q < width) :
    ∃ p < width, ∀ w : List Bool, w.length = width → w.getD q false = false →
      (w.getD q false || w.getD r false) = w.getD p false := by
  by_cases inside : r < width
  · refine ⟨r,inside,?_⟩
    intro w _ zero
    rw [zero]
    rfl
  · refine ⟨q,hq,?_⟩
    intro w len zero
    have out : w.length ≤ r := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none out]

private theorem readerCopy (g : Gate) (q width : Nat) (hq : q < width)
    (mono : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (mem : q ∈ g.inputs) :
    ∃ p < width, ∀ (w : List Bool), w.length = width → w.getD q false = false →
      g.op.eval (g.inputs.map fun i => w.getD i false) = w.getD p false := by
  have modes : g.op = .and ∨ g.op = .or := by simpa using mono.1
  rcases modes with andOp | orOp
  · refine ⟨q,hq,?_⟩
    intro w _ zero
    rw [andOp, GateOp.eval, zero]
    cases h : (g.inputs.map fun i => w.getD i false).all id
    · rfl
    · have present : false ∈ g.inputs.map (fun i => w.getD i false) :=
        List.mem_map.mpr ⟨q,mem,zero⟩
      have bad := List.all_eq_true.mp h false present
      contradiction
  · rw [orOp]
    rcases args : g.inputs with _ | ⟨a,tail⟩
    · simp [args] at mem
    · rcases tail with _ | ⟨b,tail⟩
      · have aq : q=a := by simpa [args] using mem
        subst a
        refine ⟨q,hq,?_⟩
        intro w _ _
        simp [GateOp.eval]
      · have cap := mono.2
        simp only [args,List.length_cons] at cap
        cases tail with
        | cons c rest => simp at cap
        | nil =>
          have pair : q=a ∨ q=b := by simpa [args] using mem
          rcases pair with qa | qb
          · subst a
            obtain ⟨p,bound,proof⟩ := orPairCopy q b width hq
            exact ⟨p,bound,fun w len zero => by simpa [GateOp.eval] using proof w len zero⟩
          · subst b
            obtain ⟨p,bound,proof⟩ := orPairCopy q a width hq
            exact ⟨p,bound,fun w len zero => by
              simpa [GateOp.eval,Bool.or_comm] using proof w len zero⟩

theorem pinReader (n : Nat) (C : Circuit) (m q : Nat) (mono : Monotone2 C)
    (bound : m < C.gates.length) (raw : q < n) (reads : q ∈ C.gates[m].inputs) :
    ∃ p < n+m, ∀ x : List Bool, x.length = n → x.getD q false = false →
      (eraseGate n C m p).eval x = C.eval x := by
  let L := C.gates.take m
  let R := C.gates.drop (m+1)
  let g := C.gates[m]
  have allGates : C.gates = L ++ g :: R := by
    conv_lhs => rw [← List.take_append_drop m C.gates]
    exact congrArg (L ++ ·) (List.drop_eq_getElem_cons bound)
  have hg := mono g (List.getElem_mem _)
  obtain ⟨p,hp,copy⟩ := readerCopy g q (n+m) (by omega) hg reads
  refine ⟨p,hp,?_⟩
  intro x len zero
  let tape := run L x
  have width : tape.length = n+m := by
    change (run L x).length = _
    rw [runLength,len]
    simp [L,Nat.min_eq_left (Nat.le_of_lt bound)]
  have qval : tape.getD q false = false := by
    change (run L x).getD q false = _
    rw [runOld _ _ _ (by omega),zero]
  let v := g.op.eval (g.inputs.map fun i => tape.getD i false)
  have old : C.wires x = run R (tape ++ [v]) := by
    change run C.gates x = _
    rw [allGates,runAppend]
    rfl
  have extended : (tape ++ [v]).length = tape.length+1 := by simp
  apply eraseEval n C m p x len bound hp
  left
  rw [old,runOld _ _ _ (by omega),runOld _ _ _ (by omega),readAppend,
    readAppend,width,ite_eq_left rfl,ite_eq_right (by omega)]
  exact copy tape width qval

#print axioms pinReader

private theorem readExcept (q : Nat) (gs : List Gate) (x y : List Bool)
    (len : x.length = y.length)
    (quiet : ∀ g ∈ gs, q ∉ g.inputs)
    (same : ∀ i, i ≠ q → x.getD i false = y.getD i false) :
    ∀ i, i ≠ q → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs generalizing x y with
  | nil => exact same
  | cons g gs ih =>
    have args : (g.inputs.map fun i => x.getD i false) =
        (g.inputs.map fun i => y.getD i false) := by
      apply List.map_congr_left
      intro i mem
      apply same i
      intro e
      exact quiet g (by simp) (e ▸ mem)
    let v := g.op.eval (g.inputs.map fun i => x.getD i false)
    have hx : step x g = x ++ [v] := rfl
    have hy : step y g = y ++ [v] := by
      unfold step v
      rw [args]
    intro i keep
    change (run gs (step x g)).getD i false = (run gs (step y g)).getD i false
    rw [hx,hy]
    apply ih
    · simp [len]
    · intro a mem
      exact quiet a (by simp [mem])
    · intro j neq
      rw [readAppend,readAppend,len,same j neq]
    · exact keep

theorem changedInputHasReader (C : Circuit) (q : Nat) (x y : List Bool)
    (len : x.length = y.length) (output : C.output ≠ q)
    (same : ∀ i, i ≠ q → x.getD i false = y.getD i false)
    (changes : C.eval x ≠ C.eval y) :
    ∃ m, ∃ hm : m < C.gates.length, q ∈ C.gates[m].inputs := by
  by_contra absent
  have quiet : ∀ g ∈ C.gates, q ∉ g.inputs := by
    intro g mem hit
    obtain ⟨j,bound,identify⟩ := List.getElem_of_mem mem
    exact absent ⟨j,bound,by rwa [identify]⟩
  exact changes (readExcept q C.gates x y len quiet same C.output output)

#print axioms changedInputHasReader

def eraseSteps (n : Nat) (C : Circuit) (ops : List (Nat × Nat)) : Circuit :=
  ops.foldl (fun D op => eraseGate n D op.1 op.2) C

def validSteps (n : Nat) : Circuit → List (Nat × Nat) → Prop
  | _, [] => True
  | C, (m,p) :: ops => m < C.size ∧ p < n+m ∧ validSteps n (eraseGate n C m p) ops

def pinnedRead (n : Nat) (C : Circuit) (pins : Finset Nat) (m : Nat) : Prop :=
  ∃ g, C.gates[m]? = some g ∧ ∃ q ∈ pins, q < n ∧ q ∈ g.inputs

private theorem earlierGate (n : Nat) (C : Circuit) (m p j : Nat)
    (hm : m < C.gates.length) (hj : j < m) :
    (eraseGate n C m p).gates[j]? = C.gates[j]? := by
  simp only [eraseGate,ite_eq_left hm]
  have len : (C.gates.take m).length = m := by
    simp [Nat.min_eq_left (Nat.le_of_lt hm)]
  rw [List.getElem?_append_left (by simpa only [len] using hj)]
  simp [hj]

theorem eraseMarkedBatch (n : Nat) (C : Circuit) (pins marks : Finset Nat)
    (mono : Monotone2 C) (cert : ∀ m ∈ marks, pinnedRead n C pins m) :
    ∃ ops : List (Nat × Nat), ops.length = marks.card ∧ validSteps n C ops ∧
      (eraseSteps n C ops).size = C.size - marks.card ∧ Monotone2 (eraseSteps n C ops) ∧
      ∀ x : List Bool, x.length = n → (∀ q ∈ pins, x.getD q false = false) →
        (eraseSteps n C ops).eval x = C.eval x := by
  suffices claim : ∀ k (D : Circuit) (S : Finset Nat), S.card = k → Monotone2 D →
      (∀ m ∈ S, pinnedRead n D pins m) →
      ∃ ops : List (Nat × Nat), ops.length = S.card ∧ validSteps n D ops ∧
        (eraseSteps n D ops).size = D.size - S.card ∧ Monotone2 (eraseSteps n D ops) ∧
        ∀ x : List Bool, x.length = n → (∀ q ∈ pins, x.getD q false = false) →
          (eraseSteps n D ops).eval x = D.eval x from
    claim _ C marks rfl mono cert
  intro k
  induction k with
  | zero =>
    intro D S card good _
    exact ⟨[],card.symm,trivial,by simp [eraseSteps,card],good,fun _ _ _ => rfl⟩
  | succ k ih =>
    intro D S card well known
    have nonempty : S.Nonempty := Finset.card_pos.mp (by omega)
    let m := S.max' nonempty
    have member : m ∈ S := S.max'_mem nonempty
    obtain ⟨g,here,q,qpin,qraw,qread⟩ := known m member
    have bound : m < D.gates.length := by
      by_contra out
      simp [List.getElem?_eq_none (Nat.le_of_not_gt out)] at here
    have thisGate : D.gates[m] = g :=
      Option.some.inj ((List.getElem?_eq_getElem bound).symm.trans here)
    have hasRead : q ∈ D.gates[m].inputs := by simpa only [thisGate] using qread
    obtain ⟨p,redirect,keep⟩ := pinReader n D m q well bound qraw hasRead
    let E := eraseGate n D m p
    have rest : ∀ j ∈ S.erase m, pinnedRead n E pins j := by
      intro j jm
      have less : j < m := lt_of_le_of_ne
        (S.le_max' _ (Finset.mem_of_mem_erase jm)) (Finset.mem_erase.mp jm).1
      obtain ⟨h,atj,v,vpin,vraw,vread⟩ := known j (Finset.mem_of_mem_erase jm)
      refine ⟨h,?_,v,vpin,vraw,vread⟩
      exact (earlierGate n D m p j bound less).trans atj
    have count : (S.erase m).card = k := by
      rw [Finset.card_erase_of_mem member,card]
      omega
    obtain ⟨ops,len,valid,size,usable,eq⟩ :=
      ih E (S.erase m) count (eraseMono n D m p well) rest
    let full := (m,p) :: ops
    have shift : E.size = D.size - 1 := eraseSize n D m p bound
    refine ⟨full,?_,⟨bound,redirect,valid⟩,?_,usable,?_⟩
    · simp only [full,List.length_cons,len,count,card]
    · change (eraseSteps n E ops).size = D.size - S.card
      rw [size,shift,count,card]
      omega
    · intro x length zeros
      exact (eq x length zeros).trans (keep x length (zeros q qpin))

#print axioms eraseMarkedBatch

theorem validStepIndex (n : Nat) (C : Circuit) (ops : List (Nat × Nat))
    (valid : validSteps n C ops) (j : Fin ops.length) :
    (ops[j.val]).1 < C.size - j.val := by
  induction ops generalizing C with
  | nil => exact Fin.elim0 j
  | cons op tail ih =>
    have first : op.1 < C.size := valid.1
    have rest : validSteps n (eraseGate n C op.1 op.2) tail := valid.2.2
    cases j using Fin.cases with
    | zero => simpa using first
    | succ q =>
      have index := ih (eraseGate n C op.1 op.2) rest q
      rw [eraseSize n C op.1 op.2 first] at index
      simpa [Nat.sub_sub,Nat.add_comm] using index

theorem markedFinTrace (n : Nat) (C : Circuit) (pins marks : Finset Nat)
    (mono : Monotone2 C) (cert : ∀ m ∈ marks, pinnedRead n C pins m) :
    ∃ (g : (j : Fin marks.card) → Fin (C.size-j.val)) (r : Fin marks.card → Nat),
      ∀ x : List Bool, x.length = n → (∀ q ∈ pins, x.getD q false = false) →
        ((List.finRange marks.card).foldl (fun D j => eraseGate n D (g j).val (r j)) C).eval x
          = C.eval x := by
  obtain ⟨ops,len,valid,_,_,agree⟩ := eraseMarkedBatch n C pins marks mono cert
  let entry (j : Fin marks.card) : Nat × Nat := ops[j.cast len.symm]
  let first (j : Fin marks.card) : Fin (C.size-j.val) :=
    ⟨(entry j).1, validStepIndex n C ops valid (j.cast len.symm)⟩
  let second (j : Fin marks.card) : Nat := (entry j).2
  refine ⟨first,second,?_⟩
  have listing : (List.finRange marks.card).map entry = ops := by
    apply List.ext_getElem
    · simpa using len.symm
    · intro i hi h'
      simp [entry]
  intro x width pinned
  have folded :
      (List.finRange marks.card).foldl (fun D j => eraseGate n D (first j).val (second j)) C =
        eraseSteps n C ops := by
    unfold eraseSteps
    rw [← listing,List.foldl_map]
  rw [folded]
  exact agree x width pinned

#print axioms markedFinTrace

end OrderFourErasure18057
