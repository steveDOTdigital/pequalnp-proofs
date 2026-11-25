import FlagStarCircuit
import TightBinaryCircuit

namespace ForkStarRepair
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm FlagStarCircuit

-- The first coordinate is an endpoint adjacent to the common anchor.
theorem uniqueCenter {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (no4 : NoFourCycle G)
    {s u t t' : Fin n} (different : s ≠ u)
    (st : G.Adj s t) (ut : G.Adj u t) (st' : G.Adj s t') (ut' : G.Adj u t') : t=t' := by
  let A := Finset.univ.filter (fun w => G.Adj s w ∧ G.Adj u w)
  have small : A.card ≤ 1 := no4 s u different
  exact Finset.card_le_one.mp small t (by simp [A,st,ut]) t' (by simp [A,st',ut'])

theorem repairPrice {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (no4 : NoFourCycle G)
    (col : Fin n → Bool) (bip : ∀ a b, G.Adj a b → col a ≠ col b) (s : Fin n)
    (E : Finset (Fin n × Fin n))
    (guard : ∀ e ∈ E, G.Adj s e.1 ∧ G.Adj e.1 e.2 ∧ s ≠ e.2) :
    E.card+(E.image Prod.fst).card = (E.image Prod.fst ∪ E.image Prod.snd).card := by
  have inject : Set.InjOn Prod.snd (E : Set (Fin n × Fin n)) := by
    intro a ha b hb eq
    obtain ⟨sa,ab,ne⟩ := guard a ha
    obtain ⟨sb,bb,_⟩ := guard b hb
    apply Prod.ext _ eq
    exact uniqueCenter G no4 ne sa ab.symm sb (eq ▸ bb.symm)
  have dis : Disjoint (E.image Prod.fst) (E.image Prod.snd) := by
    apply Finset.disjoint_left.mpr
    intro v hv ht
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨f,hf,eq⟩ := Finset.mem_image.mp ht
    have se := bip _ _ (guard e he).1
    have sf := bip _ _ (guard f hf).1
    have ff := bip _ _ (guard f hf).2.1
    rw [eq] at ff
    cases hs : col s <;> cases he' : col e.1 <;> cases hf' : col f.1 <;> simp_all
  rw [Finset.card_union_of_disjoint dis,Finset.card_image_iff.mpr inject,Nat.add_comm]

abbrev Star (m : ℕ) := Fin m × Fin m × List (Fin m)

def star {m} (b : Star m) : Expr m := .gate false (.raw b.1)
  (foldOr (.raw b.2.1) (b.2.2.map Expr.raw))

def restore {m} (residual : Fin m) (groups : List (Star m)) : Expr m :=
  foldOr (.raw residual) (groups.map star)

theorem starPrice {m} (b : Star m) : (star b).cost = b.2.2.length+1 := by
  simp [star,Expr.cost,foldCost,List.map_map,Function.comp_def]

theorem restorePrice {m} (r : Fin m) (groups : List (Star m)) :
    (restore r groups).cost = (groups.map (fun b => b.2.2.length+2)).sum := by
  simp [restore,foldCost,Expr.cost,List.map_map,Function.comp_def,starPrice,Nat.add_assoc]

theorem starVal {m} (b : Star m) (x : Fin m → Bool) : (star b).val GateOp.eval x = true ↔
    x b.1=true ∧ ∃ v ∈ b.2.1 :: b.2.2, x v=true := by
  simp [star,Expr.val,op,GateOp.eval,foldBool]

theorem restoreVal {m} (r : Fin m) (groups : List (Star m)) (x : Fin m → Bool) :
    (restore r groups).val GateOp.eval x = true ↔ x r=true ∨
      ∃ b ∈ groups, x b.1=true ∧ ∃ v ∈ b.2.1 :: b.2.2, x v=true := by
  simp [restore,foldBool,Expr.val,starVal]

theorem legalFrom (base : ℕ) (gs : List Gate)
    (valid : ∀ j (hj : j < gs.length), (gs[j].op=.and ∨ gs[j].op=.or) ∧
      gs[j].inputs.length=2 ∧ ∀ w ∈ gs[j].inputs, w<base+j) : legal base gs := by
  induction gs generalizing base with
  | nil => trivial
  | cons g gs ih =>
    obtain ⟨op,len,reads⟩ := valid 0 (by simp)
    refine ⟨op,len,by simpa using reads,ih (base+1) ?_⟩
    intro j hj
    rw [show base+1+j = base+(j+1) by omega]
    exact valid (j+1) (by simpa using hj)

theorem listLegal {n} (C : Circuit) (ok : IsAO2 n C) : legal n C.gates := by
  apply legalFrom
  intro j hj
  refine ⟨ok.1 _ (List.getElem_mem hj),ok.2.2 _ (List.getElem_mem hj),?_⟩
  simpa [gateAt,List.getD_eq_getElem?_getD,hj] using ok.2.1 j hj

theorem realLegal {n} (C : Circuit) (valid : legal n C.gates) : IsAO2 n C := by
  have props (j) (hj : j<C.gates.length) := legalAt valid j hj (⟨GateOp.or,[]⟩ : Gate)
  have all (g : Gate) (hg : g ∈ C.gates) : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 := by
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
    have h := props j hj
    simp [List.getD_eq_getElem?_getD,hj] at h
    exact ⟨h.1,h.2.1⟩
  exact ⟨fun g hg => (all g hg).1,fun j hj => (props j hj).2.2,fun g hg => (all g hg).2⟩

def appendExpr {n} (C : Circuit) (t : Expr (n+C.size)) : Circuit :=
  ⟨C.gates ++ t.emit (n+C.size),t.wire (n+C.size)⟩

theorem appendSize {n} (C : Circuit) (t : Expr (n+C.size)) :
    (appendExpr (n:=n) C t).size = C.size+t.cost := by
  change (C.gates ++ t.emit (n+C.size)).length = C.gates.length+t.cost
  rw [List.length_append,emitLen]

theorem appendLegal {n} (C : Circuit) (ok : IsAO2 n C) (t : Expr (n+C.size)) :
    IsAO2 n (appendExpr (n:=n) C t) := by
  apply realLegal
  exact legalAppend (listLegal C ok) (emitLegal t _ (le_refl _))

theorem appendVal {n} (C : Circuit) (t : Expr (n+C.size)) (x : Fin n → Bool) :
    circuitFun n (appendExpr (n:=n) C t) x =
    t.val GateOp.eval (fun w => (C.wires (List.ofFn x)).getD w.val false) := by
  let xs := C.wires (List.ofFn x)
  obtain ⟨tail,eq,len⟩ := runPrefix false GateOp.eval C.gates (List.ofFn x)
  have length : xs.length = n+C.size := by
    change (run false GateOp.eval C.gates (List.ofFn x)).length = _
    rw [eq,List.length_append,len,List.length_ofFn]; rfl
  have h := runRead false GateOp.eval t xs (fun i => xs.getD i.val false) (by omega) (fun _ => rfl)
  rw [length] at h
  simpa only [circuitFun,appendExpr,Circuit.eval,Circuit.wires,List.foldl_append,run,xs] using h

theorem repaired {n} (C : Circuit) (ok : IsAO2 n C) (r : Fin (n+C.size))
    (groups : List (Star (n+C.size))) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size+(groups.map (fun b => b.2.2.length+2)).sum ∧
      ∀ x : Fin n → Bool,
        let V := fun w : Fin (n+C.size) => (C.wires (List.ofFn x)).getD w.val false
        circuitFun n D x=true ↔ V r=true ∨
                             ∃ b ∈ groups, V b.1=true ∧ ∃ v ∈ b.2.1 :: b.2.2, V v=true := by
  refine ⟨appendExpr (n:=n) C (restore r groups),appendLegal C ok _,?_,?_⟩
  · rw [appendSize,restorePrice]
  · intro x; rw [appendVal]; exact restoreVal _ _ _


-- Group an arbitrary oriented edge set by first coordinate. A wire map lets
-- the same construction append stars to a circuit with an existing prefix.
theorem groupEdges {n m} (E : Finset (Fin n × Fin n)) (wire : Fin n → Fin m) :
    ∃ gs : List (Star m),
      (gs.map (fun b => b.2.2.length+2)).sum = E.card+(E.image Prod.fst).card ∧
      ∀ x : Fin m → Bool,
        (∃ b ∈ gs, x b.1=true ∧ ∃ v ∈ b.2.1 :: b.2.2, x v=true) ↔
        ∃ e ∈ E, x (wire e.1)=true ∧ x (wire e.2)=true := by
  classical
  let fiber (c : Fin n) := E.filter (fun e => e.1=c)
  have group (S : Finset (Fin n)) (active : S ⊆ E.image Prod.fst) :
      ∃ gs : List (Star m),
        (gs.map (fun b => b.2.2.length+2)).sum = (∑ c ∈ S, (fiber c).card)+S.card ∧
        ∀ x : Fin m → Bool,
          (∃ b ∈ gs, x b.1=true ∧ ∃ v ∈ b.2.1 :: b.2.2, x v=true) ↔
          ∃ e ∈ E, e.1 ∈ S ∧ x (wire e.1)=true ∧ x (wire e.2)=true := by
    induction S using Finset.induction_on with
    | empty => exact ⟨[],by simp,by simp⟩
    | @insert c S fresh ih =>
      obtain ⟨gs,price,val⟩ := ih (fun z hz => active (Finset.mem_insert_of_mem hz))
      let leaves := (fiber c).toList.map (fun e => wire e.2)
      have mem (v) : v ∈ leaves ↔ ∃ e ∈ E, e.1=c ∧ wire e.2=v := by
        simp [leaves,fiber,List.mem_map]
      obtain ⟨e,he,hc⟩ := Finset.mem_image.mp (active (Finset.mem_insert_self c S))
      have live := (mem (wire e.2)).mpr ⟨e,he,hc,rfl⟩
      cases eq : leaves with
      | nil => simp [eq] at live
      | cons v vs =>
        let b : Star m := (wire c,v,vs)
        refine ⟨b :: gs,?_,?_⟩
        · have size := congrArg List.length eq
          simp [leaves] at size
          simp [b,price,Finset.sum_insert,fresh,Finset.card_insert_of_notMem]
          omega
        · intro x
          have hv := val x
          have localVal : (∃ z ∈ v :: vs, x z=true) ↔
              ∃ e ∈ E, e.1=c ∧ x (wire e.2)=true := by
            rw [←eq]; constructor
            · rintro ⟨z,hz,hx⟩
              obtain ⟨a,ha,ca,rfl⟩ := (mem z).mp hz
              exact ⟨a,ha,ca,hx⟩
            · rintro ⟨a,ha,ca,hx⟩
              exact ⟨_,(mem _).mpr ⟨a,ha,ca,rfl⟩,hx⟩
          rw [show (∃ t ∈ b :: gs, x t.1=true ∧ ∃ z ∈ t.2.1 :: t.2.2, x z=true) ↔
              (x (wire c)=true ∧ (∃ z ∈ v::vs, x z=true) ∨
               ∃ t ∈ gs, x t.1=true ∧ ∃ z ∈ t.2.1 :: t.2.2, x z=true) by
                constructor
                · rintro ⟨t,ht,hx⟩
                  rcases List.mem_cons.mp ht with rfl | h
                  · exact Or.inl hx
                  · exact Or.inr ⟨t,h,hx⟩
                · rintro (h | ⟨t,ht,hx⟩)
                  · exact ⟨b,List.mem_cons_self,h⟩
                  · exact ⟨t,List.mem_cons_of_mem _ ht,hx⟩]
          rw [localVal,hv]
          simp only [Finset.mem_insert]
          grind
  obtain ⟨gs,hc,hv⟩ := group _ (Finset.Subset.refl (E.image Prod.fst))
  refine ⟨gs,?_,?_⟩
  · rw [hc,Finset.card_eq_sum_card_image Prod.fst E]
  · intro x
    rw [hv]
    exact ⟨fun ⟨e,he,_,hx⟩ => ⟨e,he,hx⟩,
      fun ⟨e,he,hx⟩ => ⟨e,he,Finset.mem_image_of_mem _ he,hx⟩⟩


theorem appendLostEdges {n} (C : Circuit) (ok : IsAO2 n C) (out : C.output<n+C.size)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (no4 : NoFourCycle G)
    (col : Fin n → Bool) (bip : ∀ a b, G.Adj a b → col a ≠ col b) (s : Fin n)
    (E : Finset (Fin n × Fin n)) (guard : ∀ e ∈ E, G.Adj s e.1 ∧ G.Adj e.1 e.2 ∧ s ≠ e.2) :
    ∃ D : Circuit, IsAO2 n D ∧
      D.size = C.size+(E.image Prod.fst ∪ E.image Prod.snd).card ∧
      ∀ x : Fin n → Bool, circuitFun n D x=true ↔ circuitFun n C x=true ∨
        ∃ e ∈ E, x e.1=true ∧ x e.2=true := by
  let wire (i : Fin n) : Fin (n+C.size) := ⟨i.val,by have := i.isLt; omega⟩
  obtain ⟨gs,cost,groups⟩ := groupEdges E wire
  obtain ⟨D,legalD,price,val⟩ := repaired C ok ⟨C.output,out⟩ gs
  refine ⟨D,legalD,?_,?_⟩
  · rw [price,cost,repairPrice G no4 col bip s E guard]
  · intro x
    let V (w : Fin (n+C.size)) := (C.wires (List.ofFn x)).getD w.val false
    have raw (i : Fin n) : V (wire i) = x i := by
      obtain ⟨tail,eq,_⟩ := runPrefix false GateOp.eval C.gates (List.ofFn x)
      change (run false GateOp.eval C.gates (List.ofFn x)).getD i.val false = x i
      rw [eq,List.getD_append _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD,i.isLt]
    have hd : circuitFun n D x=true ↔ circuitFun n C x=true ∨
        ∃ b ∈ gs, V b.1=true ∧ ∃ v ∈ b.2.1 :: b.2.2, V v=true := val x
    rw [hd,groups V]
    simp only [raw]

end ForkStarRepair
