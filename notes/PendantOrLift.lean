import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import PEqualNP.Defs.MetaComplexityLgpMono

namespace Independent.PendantOrLift
open PEqualNP.CircuitLowerBounds

def Hits {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ u ∈ S, ∃ v ∈ S, G.Adj u v

def Exposes {V : Type*} [DecidableEq V] (G : SimpleGraph V) (p : V) : Prop :=
  ∀ S : Finset V, p ∉ S → ¬ Hits G S → ∃ T : Finset V,
    S ⊆ T ∧ p ∉ T ∧ ¬ Hits G T ∧ Hits G (insert p T)

theorem leafExposes {V : Type*} [DecidableEq V] (G : SimpleGraph V) (p z : V)
    (edge : G.Adj z p) (leaf : ∀ t, G.Adj z t → t=p) : Exposes G p := by
  intro S hp free
  refine ⟨insert z S,Finset.subset_insert _ _,?_,?_,?_⟩
  · simpa [edge.ne.symm] using hp
  · rintro ⟨u,hu,v,hv,uv⟩
    rcases Finset.mem_insert.mp hu with eq | hu
    · have bad : v=p := leaf v (eq ▸ uv)
      have abs : p ∉ insert z S := by simpa [edge.ne.symm] using hp
      exact abs (bad ▸ hv)
    · rcases Finset.mem_insert.mp hv with eq | hv
      · have bad : u=p := leaf u (eq ▸ uv.symm)
        exact hp (bad ▸ hu)
      · exact free ⟨u,hu,v,hv,uv⟩
  · exact ⟨p,by simp,z,by simp,edge.symm⟩

-- When p is used only through p OR h, saturating h masks every toggle of p.
theorem masked {V : Type*} [DecidableEq V] (G : SimpleGraph V) (p : V)
    (h : Finset V → Bool) (context : Finset V → Bool → Bool)
    (correct : ∀ S, p ∉ S → ∀ b : Bool,
      context S (b || h S) = true ↔ Hits G (if b then insert p S else S)) :
    ∀ S, p ∉ S → h S = true → (Hits G S ↔ Hits G (insert p S)) := by
  intro S absent on
  have a := correct S absent false
  have b := correct S absent true
  simp [on] at a b
  exact a.symm.trans b

theorem safeSibling {V : Type*} [DecidableEq V] (G : SimpleGraph V) (p : V)
    (expose : Exposes G p) (h : Finset V → Bool)
    (rising : ∀ S T, S ⊆ T → h S = true → h T = true)
    (mask : ∀ T, p ∉ T → h T = true → (Hits G T ↔ Hits G (insert p T))) :
    ∀ S, p ∉ S → h S = true → Hits G S := by
  intro S hp on
  by_contra no
  obtain ⟨T,sub,absent,free,hit⟩ := expose S hp no
  exact free ((mask T absent (rising S T sub on)).mpr hit)

def advance (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
def run (gs : List Gate) (w : List Bool) := gs.foldl advance w
def dropWire (j p i : ℕ) := if i<j then i else if i=j then p else i-1
def rename (j p : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (dropWire j p)⟩

theorem extendsTape (gs : List Gate) (w : List Bool) : ∃ t, run gs w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [run]⟩
  | cons g gs ih =>
    obtain ⟨t,ht⟩ := ih (advance w g)
    exact ⟨_,by simpa [run,advance,List.append_assoc] using ht⟩

theorem runLength (gs : List Gate) (w : List Bool) : (run gs w).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (advance w g)).length = _
    rw [ih];simp [advance];omega

theorem drop_lookup (head tail : List Bool) (p i : ℕ) (hp : p<head.length) :
    (head++tail).getD (dropWire head.length p i) false =
    ((head++[head.getD p false])++tail).getD i false := by
  by_cases small : i<head.length
  · have lt : i < (head++[head.getD p false]).length := by simp;omega
    simp only [dropWire,small,ite_true,List.getD_append _ _ _ _ lt,List.getD_append _ _ _ _ small]
  · by_cases eq : i=head.length
    · subst i
      simp only [dropWire,lt_irrefl,ite_false,ite_true]
      rw [List.getD_append _ _ _ _ hp,List.getD_append _ _ _ _ (by simp),
          List.getD_append_right _ _ _ _ (by omega)]
      simp
    · have d : head.length ≤ i-1 := by omega
      have e : (head++[head.getD p false]).length ≤ i := by simp;omega
      simp only [dropWire,small,eq,ite_false,List.getD_append_right _ _ _ _ d,
        List.getD_append_right _ _ _ _ e,List.length_append,List.length_singleton]
      congr 1
      omega

theorem align (gs : List Gate) (head tail : List Bool) (p : ℕ) (hp : p<head.length) :
    ∃ r, run (gs.map (rename head.length p)) (head++tail) = head++(tail++r) ∧
      run gs ((head++[head.getD p false])++tail) = (head++[head.getD p false])++(tail++r) := by
  induction gs generalizing tail with
  | nil => exact ⟨[],by simp [run]⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map (fun i => ((head++[head.getD p false])++tail).getD i false))
    obtain ⟨r,a,b⟩ := ih (tail++[v])
    refine ⟨[v]++r,?_,?_⟩
    · simp only [List.map_cons,run,List.foldl_cons,advance,rename,List.map_map,Function.comp_def]
      simp_rw [drop_lookup head tail p _ hp]
      simpa only [run,v,List.append_assoc] using a
    · simpa only [run,List.foldl_cons,advance,v,List.append_assoc] using b

def before (pre post : List Gate) (p h out : ℕ) : Circuit :=
  ⟨pre++[⟨.or,[p,h]⟩]++post,out⟩

def moved (n : ℕ) (pre post : List Gate) (p h out : ℕ) : Circuit :=
  let j := n+pre.length
  ⟨(pre++post.map (rename j p))++[⟨.or,[dropWire j p out,h]⟩], j+post.length⟩

theorem sameSize (n pre post p h out) :
    (moved n pre post p h out).size = (before pre post p h out).size := by
  simp [moved,before,Circuit.size]

theorem monotoneMoved (n pre post p h out)
    (basis : PEqualNP.MetaComplexity.Monotone2 (before pre post p h out)) :
    PEqualNP.MetaComplexity.Monotone2 (moved n pre post p h out) := by
  intro g hg
  simp only [moved,List.mem_append,List.mem_map,List.mem_singleton] at hg
  rcases hg with (early | ⟨old,hold,rfl⟩) | rfl
  · exact basis g (by simp [before,early])
  · obtain ⟨op,arity⟩ := basis old (by simp [before,hold])
    exact ⟨op,by simpa [rename] using arity⟩
  · simp

/-- Strictly sequential wire references in the suffix remain earlier wires. -/
theorem dropEarlier {j p i t : ℕ} (hp : p<j) (hi : i<j+1+t) :
    dropWire j p i < j+t := by
  unfold dropWire
  split <;> first | omega | (split <;> omega)

def Earlier (bound : ℕ) : List Gate → Prop
  | [] => True
  | g::gs => (∀ i ∈ g.inputs, i<bound) ∧ Earlier (bound+1) gs

theorem earlierRename (gs : List Gate) {j p t : ℕ} (hp : p<j)
    (valid : Earlier (j+1+t) gs) : Earlier (j+t) (gs.map (rename j p)) := by
  induction gs generalizing t with
  | nil => trivial
  | cons g gs ih =>
    obtain ⟨head,tail⟩ := valid
    constructor
    · intro i hi
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
      exact dropEarlier hp (head k hk)
    · exact ih (t:=t+1) tail

theorem liftedEval (pre post : List Gate) (p h out : ℕ) (x : List Bool)
    (hp : p<x.length+pre.length) (hh : h<x.length+pre.length) :
    (moved x.length pre post p h out).eval x =
      ((before pre post p h out).eval x || (run pre x).getD h false) := by
  let head := run pre x
  have len : head.length=x.length+pre.length := runLength _ _
  have hp' : p<head.length := by omega
  have hh' : h<head.length := by omega
  let newTape := run (post.map (rename head.length p)) head
  have preserved : newTape.getD h false = head.getD h false := by
    obtain ⟨t,ht⟩ := extendsTape (post.map (rename head.length p)) head
    change (run _ _).getD h false = _
    rw [ht,List.getD_append _ _ _ _ hh']
  have newSize : newTape.length=x.length+pre.length+post.length := by
    simp [newTape,runLength,len]
  have final : (moved x.length pre post p h out).eval x =
      (newTape.getD (dropWire head.length p out) false || head.getD h false) := by
    change (((pre++post.map (rename _ p))++[_]).foldl advance x).getD _ false = _
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [←len]
    change (newTape ++ [GateOp.or.eval ([dropWire head.length p out,h].map
      (fun i => newTape.getD i false))]).getD _ false = _
    change (newTape ++ [_]).getD (x.length+pre.length+post.length) false = _
    rw [←newSize,List.getD_append_right _ _ _ _ (by omega)]
    simp only [Nat.sub_self,List.getD_cons_zero,GateOp.eval,List.map_cons,List.map_nil,
      List.any_cons,List.any_nil,id_eq,Bool.or_false,preserved]
  rw [final]
  cases hot : head.getD h false with
  | true => simp
  | false =>
    simp only [Bool.or_false]
    obtain ⟨r,a,b⟩ := align post head [] p hp'
    simp only [List.append_nil,List.nil_append] at a b
    have orig : (before pre post p h out).wires x =
        run post (head++[head.getD p false]) := by
      change (((pre++[_])++post).foldl advance x) = _
      simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
      change run post (head++[GateOp.or.eval ([p,h].map (fun i => head.getD i false))]) = _
      simp only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,hot,Bool.or_false]
    change (run _ head).getD _ _ = ((before pre post p h out).wires x).getD out false
    rw [a,orig,b,drop_lookup head r p out hp']

end Independent.PendantOrLift
