import PetersenFirstSignedCut

open PetersenSignedSlice PetersenFirstSignedCut
namespace PetersenRawFirstErase

def graph (x : Bits) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
def isPin (v : Fin 9) (i : ℕ) := i=2+v.val ∨ i=11+v.val
instance (v : Fin 9) (i : ℕ) : Decidable (isPin v i) := inferInstanceAs (Decidable (i=2+v.val ∨ i=11+v.val))
def lit (v : Fin 9) (s : Bool) : S Bits := if s then inv (raw v) else raw v
def fixed (v : Fin 9) (b : Bool) (x : Bits) := Function.update x v b
def slice (v : Fin 9) : List (S Bits) := pool.map (fun u x => u (fixed v false x))

theorem pos (v : Fin 9) : pool.getD (2+v.val) zero = raw v := by fin_cases v <;> rfl
theorem neg (v : Fin 9) : pool.getD (11+v.val) zero = inv (raw v) := by fin_cases v <;> rfl

theorem read (i : ℕ) : (pool.getD i zero = zero ∨ pool.getD i zero = inv zero) ∨
    ∃ (v : Fin 9) (s : Bool), isPin v i ∧ pool.getD i zero = lit v s := by
  by_cases lo : i < 2
  · interval_cases i <;> first | exact Or.inl (Or.inl rfl) | exact Or.inl (Or.inr rfl)
  by_cases hi : i < 11
  · let v : Fin 9 := ⟨i-2,by omega⟩
    have e : i=2+v.val := by dsimp [v]; omega
    exact Or.inr ⟨v,false,Or.inl e,e ▸ pos v⟩
  by_cases inRange : i < 20
  · let v : Fin 9 := ⟨i-11,by omega⟩
    have e : i=11+v.val := by dsimp [v]; omega
    exact Or.inr ⟨v,true,Or.inr e,e ▸ neg v⟩
  · left; left; rw [List.getD_eq_default _ _ (by change 20 ≤ i; omega)]

theorem poolIsLive : Live (fun _ => True) pool pool := by
  intro i _
  rcases read i with (e | e) | ⟨v,s,_,e⟩ <;> rw [e]
  · exact poolZero
  · exact biNeg poolZero
  · cases s <;> first | exact poolRaw v | exact biNeg (poolRaw v)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 6000000 in
theorem bypass : ∀ v w : Fin 9, v ≠ w → ∀ b : Bool, ∃ r : Fin 512,
    let x : Bits := fun i => r.val.testBit i.val
    x w = b ∧ graph (fixed v false x) ≠ graph (fixed v true x) := by decide +kernel

theorem sliceAt (v : Fin 9) (i : ℕ) (x : Bits) :
    (slice v).getD i zero x = pool.getD i zero (fixed v false x) := by
  rw [getAt,getAt]
  simp [slice,List.map_map,Function.comp_def]

theorem initSlice (v : Fin 9) : Live (fun _ => True) pool (slice v) := by
  intro i _
  rcases read i with (e | e) | ⟨w,s,_,e⟩
  · have z : (slice v).getD i zero = zero := by funext x; rw [sliceAt,e]; rfl
    exact z.symm ▸ poolZero
  · have z : (slice v).getD i zero = inv zero := by funext x; rw [sliceAt,e]; rfl
    exact z.symm ▸ biNeg poolZero
  · have z : (slice v).getD i zero = fun x => lit w s (fixed v false x) := by funext x; rw [sliceAt,e]
    rw [z]
    by_cases same : w=v
    · subst w; cases s <;> simp only [lit,Bool.false_eq_true,ite_false,ite_true,raw,inv,fixed,Function.update_self,Bool.not_false]
      · exact poolZero
      · exact biNeg poolZero
    · cases s <;> simp only [lit,Bool.false_eq_true,ite_false,ite_true,raw,inv,fixed,Function.update_of_ne same]
      · exact poolRaw w
      · exact biNeg (poolRaw w)

theorem markedConstant (v : Fin 9) (pre : List (S Bits)) (i : ℕ) (h : isPin v i) :
    ((slice v++pre).getD i zero = zero) ∨ ((slice v++pre).getD i zero = inv zero) := by
  rcases h with rfl | rfl
  · left
    rw [List.getD_append _ _ _ _ (by change 2+v.val < 20; omega)]
    funext x; rw [sliceAt,pos]; simp [raw,fixed,zero]
  · right
    rw [List.getD_append _ _ _ _ (by change 11+v.val < 20; omega)]
    funext x; rw [sliceAt,neg]; simp [raw,fixed,zero,inv]

theorem samePin (v : Fin 9) (s t : Bool) : Bi pool (meet (lit v s) (lit v t)) := by
  have eq : meet (lit v s) (lit v t) = ite (s=t) (lit v s) zero := by
    funext x; cases s <;> cases t <;> cases e : x v <;> simp [lit,meet,raw,inv,zero,e]
  rw [eq]
  by_cases h : s=t
  · rw [ite_eq_left h]; cases s <;> first | exact poolRaw v | exact biNeg (poolRaw v)
  · rw [ite_eq_right h]; exact poolZero

theorem firstGate (g : Gate) : Bi pool (val pool g) ∨
    ∃ (v : Fin 9) (x : Bits), touches (isPin v) g ∧
    graph (fixed v false x) ≠ graph (fixed v true x) ∧
    val pool g (fixed v false x) = val pool g (fixed v true x) := by
  have ha := poolIsLive g.1 trivial
  have hb := poolIsLive g.2 trivial
  rcases read g.1 with (e | e) | ⟨v,s,pv,ev⟩
  · left; unfold val; rw [e]; exact poolZero
  · left; unfold val; rw [e]; exact hb
  rcases read g.2 with (e | e) | ⟨w,t,pw,ew⟩
  · left
    have eq : val pool g = zero := by unfold val; rw [e]; funext x; simp [meet,zero]
    rw [eq]; exact poolZero
  · left
    have eq : val pool g = pool.getD g.1 zero := by unfold val; rw [e]; funext x; simp [inv,meet,zero]
    rw [eq]; exact ha
  by_cases eq : v=w
  · subst w; left; unfold val; rw [ev,ew]; exact samePin _ _ _
  right
  obtain ⟨r,bit,diff⟩ := bypass v w eq t
  let x : Bits := fun i => r.val.testBit i.val
  have off (b : Bool) : lit w t (fixed v b x) = false := by
    have h : x w = t := bit
    cases t <;> simp [lit,inv,raw,fixed,Ne.symm eq,h]
  exact ⟨v,x,Or.inl pv,diff,by unfold val; rw [ew]; simp only [meet,off,Bool.and_false]⟩

theorem poolAgreement (v : Fin 9) (x : Bits) : ∀ i, ¬isPin v i →
    pool.getD i zero (fixed v false x) = pool.getD i zero (fixed v true x) := by
  intro i unmarked
  rcases read i with (e | e) | ⟨w,t,pin,e⟩ <;> rw [e]
  · rfl
  · rfl
  · have ne : w ≠ v := fun h => unmarked (h ▸ pin)
    cases t <;> simp [lit,raw,inv,fixed,ne]

theorem noInput (i : ℕ) : pool.getD i zero ≠ graph := by
  by_cases hi : i<20
  · have test : ∀ ii : Fin 20, ∃ r : Fin 512,
        let x : Bits := fun j => r.val.testBit j.val
        pool.getD ii.val zero x ≠ graph x := by decide +kernel
    obtain ⟨r,bad⟩ := test ⟨i,hi⟩
    exact fun h => bad (congrFun h _)
  · rw [List.getD_eq_default _ _ (by change 20 ≤ i; omega)]
    intro eq
    have impossible := congrFun eq (fun _ => true)
    change false = true at impossible
    contradiction

theorem rebuild (w : List (S Bits)) (init : Live (fun _ => True) pool w) (p : Program) (o : ℕ) :
    Can pool p.length ((p.foldl st w).getD o zero) := by
  have rule : ∀ g ∈ p, ∀ (pre t : List (S Bits)), Bi t zero → Live (fun _ => True) t (w++pre) →
      ∃ d u, Run t d u ∧ d ≤ (1 : ℕ) ∧ Bi u (val (w++pre) g) := by
    intro g _ pre t _ live
    obtain ⟨u,r,ok⟩ := biGate (live g.1 trivial) (live g.2 trivial)
    exact ⟨1,u,r,le_rfl,ok⟩
  obtain ⟨k,t,r,le,good⟩ := build w p (fun _ => True) (fun _ => 1) rule [] pool poolZero (by simpa using init)
  exact canOfRun r (by simpa using le) (by simpa using (good o trivial).1)
theorem sliceRun {v : Fin 9} {p : Program} :
    ∃ k t, Run pool k t ∧ k ≤ (p.map fun g => ite (touches (isPin v) g) 0 1).sum ∧
      Live (fun _ => True) t (p.foldl st (slice v)) := by
  apply build (slice v) p (fun _ => True) (fun g => ite (touches (isPin v) g) 0 1) _ [] pool poolZero (initSlice v)
  intro g _ pre t base old
  by_cases h : touches (isPin v) g
  · refine ⟨0,t,Run.nil,by simp [h],?_⟩
    have ha := old g.1 trivial
    have hb := old g.2 trivial
    change Bi t (meet _ _)
    rcases h with left | right
    · rcases markedConstant v pre _ left with e | e
      · simpa only [e] using (show Bi t (meet zero ((slice v++pre).getD g.2 zero)) from base)
      · rw [e]
        change Bi t (fun x => true && _)
        simpa only [Bool.true_and] using hb
    · rcases markedConstant v pre _ right with e | e
      · rw [e]
        have z : meet ((slice v++pre).getD g.1 zero) zero = zero := by funext x; simp [meet,zero]
        rw [z]; exact base
      · rw [e]
        have z : meet ((slice v++pre).getD g.1 zero) (inv zero) = (slice v++pre).getD g.1 zero := by funext x; simp [meet,zero,inv]
        rw [z]; exact ha
  · obtain ⟨u,r,fresh⟩ := biGate (old g.1 trivial) (old g.2 trivial)
    exact ⟨1,u,r,by simp [h],fresh⟩

theorem losesOne (v : Fin 9) (p : Program) (k : Gate) (hk : k∈p) (touch : touches (isPin v) k) :
    (p.map (fun g => ite (touches (isPin v) g) 0 1)).sum < p.length := by
  have cap (l : Program) : (l.map (fun g => ite (touches (isPin v) g) 0 1)).sum ≤ l.length := by
    induction l with
    | nil => simp
    | cons g l ih => by_cases h : touches (isPin v) g <;> simp [h] <;> omega
  obtain ⟨l,r,e⟩ := List.mem_iff_append.mp hk
  rw [e]
  simp [touch]
  have := cap l
  have := cap r
  omega


/-- On a raw program for the graph some zero restriction removes at least two gates. -/
theorem restriction (n : ℕ) (can : Can pool n graph) :
    ∃ v : Fin 9, Can pool (n-2) (fun x => graph (fixed v false x)) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    obtain ⟨p,o,len,hit⟩ := can
    have outEq : (p.foldl st pool).getD o zero = graph := by
      funext x; rw [getAt,values]; exact hit x
    cases p with
    | nil => exact False.elim (noInput o outEq)
    | cons g tail =>
      rcases firstGate g with cheap | ⟨v,x,mark,diff,same⟩
      · have init : Live (fun _ => True) pool (st pool g) := extend poolZero poolIsLive cheap
        have next := rebuild (st pool g) init tail o
        change (tail.foldl st (st pool g)).getD o zero = graph at outEq
        rw [outEq] at next
        simp only [List.length_cons] at len
        obtain ⟨v,p,k,sz,yes⟩ := ih tail.length (by omega) next
        exact ⟨v,p,k,by omega,yes⟩
      · have outNotPin : ¬ isPin v o := by
          intro pin
          have low : o < pool.length := by change o < 20; rcases pin with e | e <;> omega
          rw [original (g::tail) pool o low] at outEq
          exact noInput _ outEq
        have agrees : ∀ i, ¬isPin v i → (st pool g).getD i zero (fixed v false x) =
            (st pool g).getD i zero (fixed v true x) := by
          intro i good
          by_cases small : i < pool.length
          · rw [st,List.getD_append _ _ _ _ small]
            exact poolAgreement v x i good
          · rw [st,List.getD_append_right _ _ _ _ (by omega)]
            cases e : i-pool.length with
            | zero => exact same
            | succ j =>
              cases j with
              | zero => exact congrArg Bool.not same
              | succ j => rfl
        have reader : ∃ k ∈ tail, touches (isPin v) k := by
          by_contra! avoids
          have agree := equalOff tail (st pool g) _ _ (isPin v) agrees avoids o outNotPin
          change (tail.foldl st (st pool g)).getD o zero = graph at outEq
          rw [outEq] at agree
          exact diff agree
        obtain ⟨k,hk,touched⟩ := reader
        have loss := losesOne v tail k hk touched
        obtain ⟨cost,t,run,bound,live⟩ := sliceRun (v:=v) (p:=g::tail)
        simp only [List.map_cons,List.sum_cons,ite_eq_left mark,Nat.zero_add] at bound
        have valEq : ((g::tail).foldl st (slice v)).getD o zero = fun y => graph (fixed v false y) := by
          funext y
          rw [getAt,values]
          have poolEq : (slice v).map (fun u => u y) = pool.map (fun u => u (fixed v false y)) := by
            simp only [slice,List.map_map,Function.comp_def]
          rw [poolEq]
          exact hit _
        simp only [List.length_cons] at len
        exact ⟨v,canOfRun run (by omega) (valEq ▸ (live o trivial).1)⟩

theorem rawLower (bounds : ∀ v : Fin 9, ¬Can pool 11 (fun x => graph (fixed v false x))) :
    ¬Can pool 13 graph := by
  intro can
  obtain ⟨v,h⟩ := restriction 13 can
  exact bounds v h


/-- Pinning an essential variable of a nonliteral function saves one paid gate. -/
theorem pinOnce (v : Fin 9) (f : S Bits) (n : ℕ)
    (nonlit : ∀ i, pool.getD i zero ≠ f)
    (sensitive : ∃ x : Bits, f (fixed v false x) ≠ f (fixed v true x))
    (can : Can pool n f) : Can pool (n-1) (fun x => f (fixed v false x)) := by
  obtain ⟨p,o,len,hit⟩ := can
  have output : (p.foldl st pool).getD o zero = f := by
    funext x; rw [getAt,values]; exact hit _
  have nonpin : ¬isPin v o := by
    intro wrong
    have small : o < pool.length := by change o < 20; rcases wrong with h | h <;> omega
    rw [original _ _ _ small] at output
    exact nonlit _ output
  obtain ⟨x,diff⟩ := sensitive
  have reader : ∃ g ∈ p, touches (isPin v) g := by
    by_contra! avoids
    have e := equalOff p pool _ _ (isPin v) (poolAgreement v x) avoids o nonpin
    rw [output] at e
    exact diff e
  obtain ⟨g,hg,hm⟩ := reader
  have loss := losesOne v p g hg hm
  obtain ⟨k,t,r,bound,live⟩ := sliceRun (v:=v) (p:=p)
  have eq : (p.foldl st (slice v)).getD o zero = fun y => f (fixed v false y) := by
    funext y; rw [getAt,values]
    have table : (slice v).map (fun u => u y) = pool.map (fun u => u (fixed v false y)) := by
      simp only [slice,List.map_map,Function.comp_def]
    rw [table]; exact hit _
  exact canOfRun r (by omega) (eq ▸ (live o trivial).1)

def mate (v : Fin 9) : Fin 9 := (![4,6,7,4,0,7,1,5,6] : Fin 9 → Fin 9) v
def relabel (v : Fin 9) : Fin 9 → Fin 9 :=
  (![
    ![0,1,2,3,4,5,6,7,8], ![1,0,5,8,6,2,4,7,3], ![2,1,0,5,7,3,6,4,8],
    ![3,2,1,0,4,8,7,6,5], ![0,1,2,3,4,5,6,7,8], ![1,2,3,8,6,0,7,4,5],
    ![1,0,5,8,6,2,4,7,3], ![1,2,3,8,6,0,7,4,5], ![2,3,8,5,7,1,4,6,0]
  ] : Fin 9 → Fin 9 → Fin 9) v
def deletion (v : Fin 9) (x : Bits) := graph (fixed v false x)
def theta (x : Bits) := deletion 0 (fixed 4 false x)
def bits (r : Fin 512) : Bits := fun i => r.val.testBit i.val

theorem enumerate (x : Bits) : ∃ r, bits r = x := by
  let b := BitVec.ofBoolListLE (List.ofFn x)
  let r : Fin 512 := ⟨b.toNat,by have h := b.isLt; simpa [b] using h⟩
  refine ⟨r,?_⟩
  funext i
  change b.getLsbD i.val = x i
  simp only [b,BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt),List.getElem_ofFn]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 6000000 in
theorem pinWitness : ∀ v : Fin 9, ∃ r : Fin 512,
    deletion v (fixed (mate v) false (bits r)) ≠ deletion v (fixed (mate v) true (bits r)) := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 6000000 in
theorem deletionNonlit (v : Fin 9) (i : ℕ) : pool.getD i zero ≠ deletion v := by
  have tested : ∀ v : Fin 9, ∀ j : Fin 20, ∃ r : Fin 512,
      pool.getD j.val zero (bits r) ≠ deletion v (bits r) := by decide +kernel
  by_cases hi : i<20
  · obtain ⟨r,h⟩ := tested v ⟨i,hi⟩
    exact fun e => h (congrFun e _)
  · rw [List.getD_eq_default _ _ (by change 20 ≤ i; omega)]
    obtain ⟨r,h⟩ := tested v 0
    exact fun e => h (congrFun e _)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem renameRows : ∀ v : Fin 9, ∀ r : Fin 512,
    deletion v (fixed (mate v) false (bits r ∘ relabel v)) = theta (bits r) := by decide +kernel

/-- Raw signed programs may substitute a raw input for each input without paying a gate. -/
theorem substitute (f : S Bits) (ρ : Fin 9 → Fin 9) (n : ℕ) (can : Can pool n f) :
    Can pool n (fun x => f (x ∘ ρ)) := by
  let w := pool.map (fun u x => u (x ∘ ρ))
  have atWire (i : ℕ) (x : Bits) : w.getD i zero x = pool.getD i zero (x ∘ ρ) := by
    rw [getAt,getAt]; simp only [w,List.map_map,Function.comp_def]
  have init : Live (fun _ => True) pool w := by
    intro i _
    rcases read i with (e | e) | ⟨v,s,_,e⟩
    · have z : w.getD i zero = zero := by funext x; rw [atWire,e]; rfl
      exact z.symm ▸ poolZero
    · have z : w.getD i zero = inv zero := by funext x; rw [atWire,e]; rfl
      exact z.symm ▸ biNeg poolZero
    · have z : w.getD i zero = lit (ρ v) s := by funext x; rw [atWire,e]; cases s <;> rfl
      rw [z]; cases s <;> first | exact poolRaw _ | exact biNeg (poolRaw _)
  obtain ⟨p,o,le,hit⟩ := can
  have eq : (p.foldl st w).getD o zero = fun x => f (x ∘ ρ) := by
    funext x; rw [getAt,values]
    have rows : w.map (fun u => u x) = pool.map (fun u => u (x ∘ ρ)) := by
      simp only [w,List.map_map,Function.comp_def]
    rw [rows]; exact hit _
  obtain ⟨q,k,sz,run⟩ := eq ▸ rebuild w init p o
  exact ⟨q,k,sz.trans le,run⟩

theorem thetaOfDeletion (v : Fin 9) (h : Can pool 11 (deletion v)) : Can pool 10 theta := by
  obtain ⟨r,diff⟩ := pinWitness v
  have smaller := pinOnce (mate v) (deletion v) 11 (deletionNonlit v) ⟨bits r,diff⟩ h
  have renamed := substitute _ (relabel v) 10 smaller
  have eq : (fun x : Bits => deletion v (fixed (mate v) false (x ∘ relabel v))) = theta := by
    funext x; obtain ⟨r,rfl⟩ := enumerate x; exact renameRows v r
  exact eq ▸ renamed

/-- The same seven-vertex numerical statement proves both graph bounds in the reduction. -/
theorem bothBounds (h : ¬Can pool 10 theta) :
    (¬Can pool 13 graph) ∧ (¬Can pool 11 (deletion 0)) := by
  have all : ∀ v : Fin 9, ¬Can pool 11 (deletion v) := fun v c => h (thetaOfDeletion v c)
  exact ⟨rawLower all,all 0⟩


theorem submittedRaw (thetaBound : ¬Can pool 10 theta) : ∀ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ 13 → ∃ x : Fin 9 → Bool,
      (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
        w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false ≠
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2) := by
  intro p o small
  by_contra! hit
  apply (bothBounds thetaBound).1
  exact ⟨p,o,small,fun x => by rw [poolAt]; exact hit x⟩

theorem submittedDeletion (thetaBound : ¬Can pool 10 theta) : ∀ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ 11 → ∃ x : Fin 9 → Bool,
      (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
        w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false ≠
      ([(1,2),(2,3),(3,4),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2) := by
  intro p o small
  by_contra! hit
  apply (bothBounds thetaBound).2
  refine ⟨p,o,small,?_⟩
  intro x
  rw [poolAt]
  apply (hit x).trans
  simp [deletion,graph,fixed,Function.update]

end PetersenRawFirstErase
