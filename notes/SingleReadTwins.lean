import PEqualNP.Defs

namespace SingleReadTwins

open PEqualNP.CircuitLowerBounds

-- Original inputs occupy [0,n). The new twin is n and its OR wire is n+1.
def wire (n u i : ℕ) : ℕ := if i < n then (if i=u then n+1 else i) else i+2
def rewriteGate (n u : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (wire n u)⟩
def duplicate (C : Circuit) (n u : ℕ) : Circuit :=
  ⟨⟨.or,[u,n]⟩ :: C.gates.map (rewriteGate n u), wire n u C.output⟩

theorem size (C : Circuit) (n u) : (duplicate C n u).size = C.size+1 := by
  simp [duplicate,Circuit.size]

def step {α : Type} (d : α) (op : GateOp → List α → α) (s : List α) (g : Gate) :=
  s ++ [op g.op (g.inputs.map fun i => s.getD i d)]

def merge {α : Type} {n : ℕ} (u : Fin n) (Y : Fin (n+1) → α) (h : α) (i : Fin n) :=
  if i=u then h else Y i.castSucc

theorem getFn {α : Type} {n : ℕ} (f : Fin n → α) (d : α) (i : ℕ) (hi : i<n) :
    (List.ofFn f).getD i d = f ⟨i,hi⟩ := by
  have len : i < (List.ofFn f).length := by simpa
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem len,Option.getD_some,List.getElem_ofFn]

theorem lookup {α : Type} {n : ℕ} (u : Fin n) (Y : Fin (n+1) → α) (h d : α)
    (T : List α) (i : ℕ) :
    ((List.ofFn Y ++ [h]) ++ T).getD (wire n u i) d =
      (List.ofFn (merge u Y h) ++ T).getD i d := by
  by_cases small : i<n
  · let j : Fin n := ⟨i,small⟩
    have old : i < (List.ofFn (merge u Y h)).length := by simpa
    rw [List.getD_append _ _ _ _ old]
    by_cases e : i=u.val
    · subst i
      have bound : n+1 < (List.ofFn Y ++ [h]).length := by simp
      rw [show wire n u u.val = n+1 by simp [wire,u.isLt],List.getD_append _ _ _ _ bound,
          List.getD_append_right _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD,merge]
    · have bound : i < (List.ofFn Y ++ [h]).length := by simp; omega
      have nd : i < (List.ofFn Y).length := by simp; omega
      rw [show wire n u i = i by simp [wire,small,e],List.getD_append _ _ _ _ bound,
          List.getD_append _ _ _ _ nd]
      rw [getFn _ d i (by omega),getFn _ d i small]
      simp [merge,Fin.ext_iff,e]
  · rw [show wire n u i = i+2 by simp [wire,small]]
    rw [List.getD_append_right _ _ _ _ (by simp;omega),List.getD_append_right _ _ _ _ (by simp;omega)]
    simp

theorem foldTail {α : Type} {n : ℕ} (u : Fin n) (Y : Fin (n+1) → α) (h d : α)
    (op : GateOp → List α → α) (gs : List Gate) (t : List α) :
    ∃ T, gs.foldl (step d op) (List.ofFn (merge u Y h) ++ t) = List.ofFn (merge u Y h) ++ T ∧
      (gs.map (rewriteGate n u)).foldl (step d op) ((List.ofFn Y ++ [h]) ++ t) =
        (List.ofFn Y ++ [h]) ++ T := by
  induction gs generalizing t with
  | nil => exact ⟨t,rfl,rfl⟩
  | cons g gs ih =>
    let v := op g.op (g.inputs.map fun i => (List.ofFn (merge u Y h) ++ t).getD i d)
    obtain ⟨T,lt,rt⟩ := ih (t++[v])
    refine ⟨T,?_,?_⟩
    · simpa only [List.foldl_cons,step,List.append_assoc,v] using lt
    · simp only [List.map_cons,List.foldl_cons,rewriteGate,step,List.map_map,Function.comp_def]
      simp_rw [lookup]
      simpa only [List.append_assoc,v] using rt

theorem transform {α : Type} {n : ℕ} (u : Fin n) (Y : Fin (n+1) → α) (d : α)
    (op : GateOp → List α → α) (C : Circuit) :
    let h := op .or [Y u.castSucc,Y (Fin.last n)]
    ((duplicate C n u).gates.foldl (step d op) (List.ofFn Y)).getD (duplicate C n u).output d =
      (C.gates.foldl (step d op) (List.ofFn (merge u Y h))).getD C.output d := by
  dsimp only
  let h := op .or [Y u.castSucc,Y (Fin.last n)]
  obtain ⟨T,old,new⟩ := foldTail u Y h d op C.gates []
  simp only [List.append_nil] at old new
  have seed : step d op (List.ofFn Y) ⟨GateOp.or,[u.val,n]⟩ = List.ofFn Y ++ [h] := by
    simp only [step,h,List.map_cons,List.map_nil]
    rw [getFn _ d u.val (by omega),getFn _ d n (by omega)]
    rfl
  change (((C.gates.map (rewriteGate n u)).foldl (step d op)
    (step d op (List.ofFn Y) ⟨GateOp.or,[u.val,n]⟩))).getD (wire n u C.output) d = _
  rw [seed,new,old,lookup]

theorem eval (C : Circuit) {n : ℕ} (u : Fin n) (Y : Fin (n+1) → Bool) :
    (duplicate C n u).eval (List.ofFn Y) =
      C.eval (List.ofFn (merge u Y (Y u.castSucc || Y (Fin.last n)))) := by
  have h := transform u Y false GateOp.eval C
  change ((duplicate C n u).gates.foldl (step false GateOp.eval) (List.ofFn Y)).getD (duplicate C n u).output false = (C.gates.foldl (step false GateOp.eval) (List.ofFn (merge u Y _))).getD C.output false
  simpa only [GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false] using h

def parts (op : GateOp) (ins : List (Bool×Bool)) :=
  match op with
  | .or => (ins.any (·.1),ins.any (·.2))
  | .and => ins.foldl (fun (a b : Bool×Bool) => (a.1 && b.1,(a.1 && b.2) || (a.2 && b.1))) (true,false)
  | _ => (false,false)

def seed (side : ℕ → Bool) (x : Bool) (i : ℕ) : Bool×Bool :=
  if side i then (false,x) else (x,false)

theorem linear {n : ℕ} (C : Circuit) (s : ℕ → Bool) (X : Fin n → Bool) :
    PEqualNP.ReadK.linearParts C s (List.ofFn X) =
      C.gates.foldl (step (false,false) parts) (List.ofFn fun i : Fin n => seed s (X i) i.val) := by
  unfold PEqualNP.ReadK.linearParts
  change C.gates.foldl (step (false,false) parts) _ = _
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [seed]

theorem linearOutput (C : Circuit) {n : ℕ} (u : Fin n) (s : ℕ → Bool)
    (same : s n = s u) (Y : Fin (n+1) → Bool) :
    ((PEqualNP.ReadK.linearParts (duplicate C n u) s (List.ofFn Y)).getD (duplicate C n u).output (false,false)) =
    ((PEqualNP.ReadK.linearParts C s
      (List.ofFn (merge u Y (Y u.castSucc || Y (Fin.last n))))).getD C.output (false,false)) := by
  rw [linear,linear]
  rw [transform]
  congr 3
  funext i
  by_cases eq : i=u
  · subst i
    cases h : s u.val <;> simp [merge,seed,parts,same,h]
  · simp [merge,seed,eq]


open PEqualNP.ReadK

def project (n u i : ℕ) := if i=n then u else i
def active (p l i : ℕ) : Bool := i == p || i == l

theorem rangeFlags (n p l : ℕ) :
    (List.range n).map (active p l) = List.ofFn (fun i : Fin n => active p l i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem mergeFlags {n : ℕ} (u : Fin n) (p l : ℕ) :
    merge u (fun i : Fin (n+1) => active p l i.val) (active p l u.val || active p l n) =
      (fun i : Fin n => active (project n u p) (project n u l) i.val) := by
  funext i
  have hu := u.isLt
  have hi := i.isLt
  apply Bool.eq_iff_iff.mpr
  by_cases a : i=u <;> by_cases b : p=n <;> by_cases c : l=n <;>
    simp [merge,active,project,a,b,c] <;> simp_all [Fin.ext_iff] <;> omega

theorem flag (C : Circuit) {n : ℕ} (u : Fin n) (s : ℕ → Bool)
    (same : s n = s u) (p l : ℕ) :
    lineSingle (duplicate C n u) (n+1) s p l =
      lineSingle C n s (project n u p) (project n u l) := by
  unfold lineSingle
  change ((linearParts _ _ ((List.range _).map (active _ _))).getD _ _).2 =
    ((linearParts _ _ ((List.range _).map (active _ _))).getD _ _).2
  rw [rangeFlags,rangeFlags,linearOutput C u s same]
  exact congrArg (fun X => ((linearParts C s (List.ofFn X)).getD C.output (false,false)).2)
    (mergeFlags u p l)

theorem singleRead (C : Circuit) {n : ℕ} (u : Fin n) (s : ℕ → Bool)
    (same : s n = s u) (oldEdges newEdges : List (ℕ × ℕ))
    (edges : ∀ e ∈ newEdges, (project n u e.1,project n u e.2) ∈ oldEdges)
    (old : doubleReread C n s oldEdges = []) :
    doubleReread (duplicate C n u) (n+1) s newEdges = [] := by
  unfold doubleReread at old ⊢
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro e h
  obtain ⟨mem,bad⟩ := List.mem_filter.mp h
  rw [flag C u s same,flag C u (fun i => !s i) (congrArg Bool.not same)] at bad
  have contra : (project n u e.1,project n u e.2) ∈ oldEdges.filter (fun z =>
      !(lineSingle C n s z.1 z.2) && !(lineSingle C n (fun i => !s i) z.1 z.2)) :=
    List.mem_filter.mpr ⟨edges e mem,bad⟩
  rw [old] at contra
  exact List.not_mem_nil contra


open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

theorem legal (C : Circuit) {n : ℕ} (u : Fin n) (old : IsAO2 n C) :
    IsAO2 (n+1) (duplicate C n u) := by
  rcases old with ⟨ops,back,arity⟩
  refine ⟨?_,?_,?_⟩
  · intro g mem
    rcases List.mem_cons.mp mem with eq | tail
    · subst g; exact Or.inr rfl
    · obtain ⟨g,hm,rfl⟩ := List.mem_map.mp tail
      exact ops g hm
  · intro j hj i hi
    cases j with
    | zero =>
      simp [gateAt,duplicate,List.getD_eq_getElem?_getD] at hi
      rcases hi with rfl | rfl <;> omega
    | succ j =>
      have jb : j<C.gates.length := by simpa [duplicate] using hj
      have atj : gateAt (duplicate C n u) (j+1) = rewriteGate n u (gateAt C j) := by
        simp [gateAt,duplicate,List.getD_eq_getElem?_getD,jb]
      rw [atj] at hi
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hi
      have lt := back j jb b hb
      simp only [wire]; split_ifs <;> omega
  · intro g mem
    rcases List.mem_cons.mp mem with eq | tail
    · subst g; rfl
    · obtain ⟨g,hm,rfl⟩ := List.mem_map.mp tail
      simpa [rewriteGate] using arity g hm

end SingleReadTwins
