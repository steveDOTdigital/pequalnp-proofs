import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_2012

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PetersenTerminalTriples

abbrev Bits := Fin 9 → Bool
def graph (x : Bits) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
  x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10))
def first : Gate := ⟨.or,[0,3]⟩
def start (x : Bits) := List.ofFn x ++ [x 0 || x 3]
def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
def wires (p : List Gate) (x : Bits) := p.foldl step (start x)
def read (p : List Gate) (i : ℕ) (x : Bits) := (wires p x).getD i false
def legal (g : Gate) := g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
def inversions (p : List Gate) := p.countP fun g => g.op.eval [false]
def tri (t a b c : Bool) := a || (if t then b && c else b || c)
def code (a b c : Bool) := a.toNat + 2*b.toNat + 4*c.toNat
def witness (p : List Gate) (a b c n : ℕ) := ∃ x, code (read p a x) (read p b x) (read p c x) = n
def footprint (p : List Gate) (a b c : ℕ) (t : Bool) : Prop :=
  (∀ n ∈ (if t then [2,4,6] else [0,1,2,4] : List ℕ), witness p a b c n) ∧
  (t=true → ∃ n ∈ ([1,3,5] : List ℕ), witness p a b c n)

theorem foldLen (p : List Gate) (w : List Bool) : (p.foldl step w).length = w.length+p.length := by
  induction p generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons,ih]; simp [step]; omega

theorem startAt (x : Bits) : step (List.ofFn x) first = start x := by
  simp [step,first,start,GateOp.eval,List.getD_eq_getElem?_getD]

theorem lastAt (w : List Bool) (v : Bool) (i : ℕ) :
    (w++[v]).getD i false = if i=w.length then v else w.getD i false := by
  by_cases h : i<w.length
  · rw [List.getD_append _ _ _ _ h]; simp only [Nat.ne_of_lt h,ite_false]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases e : i=w.length
    · simp [e]
    · have z : [v].length ≤ i-w.length := by simp; omega
      rw [List.getD_eq_default _ _ z,List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
      simp [e]

def gateVal (p : List Gate) (g : Gate) (x : Bits) := g.op.eval (g.inputs.map (fun i => read p i x))

theorem shorter (low : ¬ HasCircuitSize 9 graph 14) (p : List Gate) (len : p.length=12)
    (ok : ∀ g ∈ p, legal g) (g : Gate) (hg : legal g) :
    ¬ ∀ x, gateVal p g x = graph x := by
  intro all
  let C : Circuit := ⟨first :: (p++[g]),22⟩
  apply low
  refine ⟨C,?_,?_,?_⟩
  · intro k hk
    change k ∈ first :: (p++[g]) at hk
    rcases List.mem_cons.mp hk with rfl | hk
    · simp [first]
    rcases List.mem_append.mp hk with hp | hg'
    · exact ok _ hp
    · obtain rfl := List.mem_singleton.mp hg'
      exact hg
  · simp [C,Circuit.size,len]
  · intro x
    change (((first :: (p++[g])).foldl step (List.ofFn x)).getD 22 false) = graph x
    rw [List.foldl_cons,startAt,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change ((wires p x)++[gateVal p g x]).getD 22 false = graph x
    have hlen : (wires p x).length=22 := by simp [wires,foldLen,start,len]
    rw [lastAt,hlen]; simp only [ite_true]
    exact all x

def atom (k : Fin 6) (a b : ℕ) : Gate :=
  ![⟨.or,[]⟩,⟨.and,[]⟩,⟨.or,[a]⟩,⟨.not,[a]⟩,⟨.and,[a,b]⟩,⟨.or,[a,b]⟩] k
def val (k : Fin 6) (a b : Bool) := (![false,true,a,!a,a && b,a || b] : Fin 6 → Bool) k
theorem atomLegal (k : Fin 6) (a b) : legal (atom k a b) := by fin_cases k <;> simp [legal,atom]
theorem atomVal (k : Fin 6) (p) (a b : ℕ) (x) :
    gateVal p (atom k a b) x = val k (read p a x) (read p b x) := by
  fin_cases k <;> simp [gateVal,atom,val,GateOp.eval]

-- A subset of the eight possible input triples is represented by its eight-bit mask.
-- Every smaller final gate must disagree on at least one triple realized by the prefix.
def separates (D : Fin 256) (t : Bool) : Bool :=
  (((List.finRange 6).flatMap fun k => (List.finRange 3).flatMap fun i => (List.finRange 3).map fun j => (k,i,j))).all fun ⟨k,i,j⟩ =>
    (List.range 8).any fun r => D.val.testBit r &&
      (val k (r.testBit i.val) (r.testBit j.val) != tri t (r.testBit 0) (r.testBit 1) (r.testBit 2))
theorem signatures : ∀ (t : Bool) (D : Fin 256), separates D t = true ↔
    ((if t then [2,4,6] else [0,1,2,4] : List ℕ).all D.val.testBit = true ∧
     (t=true → ([1,3,5] : List ℕ).any D.val.testBit = true)) := by decide +kernel


def need (t : Bool) (s : Fin 4) : List ℕ :=
  if t then (![ [2],[4],[6],[1,3,5] ] : Fin 4 → List ℕ) s
  else (![ [0],[1],[2],[4] ] : Fin 4 → List ℕ) s
def rival (t : Bool) (s : Fin 4) : Fin 6 × Fin 3 × Fin 3 :=
  if t then (![(5,0,1),(5,0,2),(2,0,0),(4,1,2)] : Fin 4 → Fin 6 × Fin 3 × Fin 3) s
  else (![(1,0,0),(5,1,2),(5,0,2),(5,0,1)] : Fin 4 → Fin 6 × Fin 3 × Fin 3) s

theorem rivalRow : ∀ t s (z : Fin 3 → Bool),
    let r := rival t s
    val r.1 (z r.2.1) (z r.2.2) ≠ tri t (z 0) (z 1) (z 2) →
    code (z 0) (z 1) (z 2) ∈ need t s := by decide

theorem profile (low : ¬ HasCircuitSize 9 graph 14) (p : List Gate) (len : p.length=12)
    (ok : ∀ g ∈ p, legal g) (a b c : ℕ) (t : Bool)
    (hit : ∀ x, tri t (read p a x) (read p b x) (read p c x) = graph x) : footprint p a b c t := by
  classical
  let w : Fin 3 → ℕ := ![a,b,c]
  have someRow (s : Fin 4) : ∃ n ∈ need t s, witness p a b c n := by
    let r := rival t s
    have bad := shorter low p len ok _ (atomLegal r.1 (w r.2.1) (w r.2.2))
    push Not at bad
    obtain ⟨x,hx⟩ := bad
    rw [atomVal,←hit x] at hx
    have h := rivalRow t s (fun i => read p (w i) x) hx
    exact ⟨_,h,x,rfl⟩
  have h0 := someRow 0
  have h1 := someRow 1
  have h2 := someRow 2
  have h3 := someRow 3
  cases t <;> simp [need,footprint] at h0 h1 h2 h3 ⊢ <;> tauto

theorem asAtom (g : Gate) (hg : legal g) : ∃ (k : Fin 6) (i j : ℕ), (k=3 → g.op=.not) ∧ ∀ (p : List Gate) (x : Bits),
    gateVal p g x = val k (read p i x) (read p j x) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hop,hlen⟩ := hg
  change op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) at hop
  change ins.length ≤ 2 at hlen
  rcases hop with h | h | h <;> subst op
  · cases ins with
    | nil => exact ⟨1,0,0,by rintro ⟨⟩,fun _ _ => rfl⟩
    | cons a l => cases l with
      | nil => exact ⟨2,a,0,by rintro ⟨⟩,fun p x => by simp [gateVal,val,GateOp.eval]⟩
      | cons b l =>
        cases l with
        | nil => exact ⟨4,a,b,by rintro ⟨⟩,fun p x => by simp [gateVal,val,GateOp.eval]⟩
        | cons z l => simp at hlen
  · cases ins with
    | nil => exact ⟨0,0,0,by rintro ⟨⟩,fun _ _ => rfl⟩
    | cons a l => cases l with
      | nil => exact ⟨2,a,0,by rintro ⟨⟩,fun p x => by simp [gateVal,val,GateOp.eval]⟩
      | cons b l =>
        cases l with
        | nil => exact ⟨5,a,b,by rintro ⟨⟩,fun p x => by simp [gateVal,val,GateOp.eval]⟩
        | cons z l => simp at hlen
  · cases ins with
    | nil => exact ⟨1,0,0,by rintro ⟨⟩,fun _ _ => rfl⟩
    | cons a l => exact ⟨3,a,0,fun _ => rfl,fun _ _ => rfl⟩


namespace Order
def WireLE (a b : List Bool) := ∀ i, a.getD i false = true → b.getD i false = true
def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def fold (gs : List Gate) (w : List Bool) := gs.foldl step w
def mono (gs : List Gate) := ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or

theorem gate_mono (g : Gate) (a b : List Bool) (h : WireLE a b) (kind : g.op = GateOp.and ∨ g.op = GateOp.or) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
    g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases kind with hk|hk
  · simp only [hk,GateOp.eval,List.all_eq_true,List.mem_map,id_eq,forall_exists_index,and_imp]
    intro ha v i hi e
    subst v
    exact h i (ha _ i hi rfl)
  · simp only [hk,GateOp.eval,List.any_eq_true,List.mem_map,id_eq]
    rintro ⟨v,⟨i,hi,rfl⟩,ok⟩
    exact ⟨_,⟨i,hi,rfl⟩,h i ok⟩

theorem append_mono (a b : List Bool) (hlen : a.length=b.length) (h : WireLE a b)
    (x y : Bool) (hxy : x=true → y=true) : WireLE (a++[x]) (b++[y]) := by
  intro i hi
  by_cases inA : i<a.length
  · rw [List.getD_append _ _ _ _ inA] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi ⊢
    rw [← hlen]
    by_cases atEnd : i=a.length
    · simpa [atEnd] using hxy (by simpa [atEnd] using hi)
    · have hbound : [x].length ≤ i-a.length := by simp; omega
      rw [List.getD_eq_default _ _ hbound] at hi
      contradiction

theorem fold_mono (gs : List Gate) (a b : List Bool) (m : mono gs)
    (hl : a.length=b.length) (h : WireLE a b) : WireLE (fold gs a) (fold gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    change WireLE (fold gs (step a g)) (fold gs (step b g))
    apply ih _ _ (fun z hz => m z (List.mem_cons_of_mem _ hz))
    · simp [step,hl]
    · exact append_mono a b hl h _ _ (gate_mono g a b h (m g (by simp)))


end Order

theorem monotoneFromZero (p : List Gate) (ok : ∀ g ∈ p, legal g) (none : inversions p=0)
    (x : Bits) (i : ℕ) : read p i (fun _ => false)=true → read p i x=true := by
  have ord : Order.mono p := by
    intro g hg
    rcases (ok g hg).1 with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · have z : p.countP (fun k : Gate => k.op.eval [false]) = 0 := none
      have h := List.countP_eq_zero.mp z g hg
      change g.op = .not at hn
      simp [hn,GateOp.eval] at h
  have seed : Order.WireLE (start (fun _ => false)) (start x) := by
    intro i hi
    by_cases h : i<9
    · rw [show start (fun _ => false) = List.ofFn (fun _ : Fin 9 => false) ++ [false] from rfl,
        List.getD_append _ _ _ _ (by simpa using h),
        List.getD_eq_getElem _ _ (by simpa using h),List.getElem_ofFn] at hi
      contradiction
    · rw [show start (fun _ => false) = List.ofFn (fun _ : Fin 9 => false) ++ [false] from rfl,lastAt] at hi
      simp only [List.length_ofFn] at hi
      split at hi
      · contradiction
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        contradiction
  exact Order.fold_mono p _ _ ord (by simp [start]) seed i

theorem endGate (low : ¬ HasCircuitSize 9 graph 14) (p : List Gate) (len : p.length=12)
    (ok : ∀ g ∈ p, legal g) (g : Gate) (hg : legal g) (one : inversions (p++[g])≤1) (a : ℕ)
    (hit : ∀ x, (read p a x || gateVal p g x) = graph x) :
    ∃ b c t, footprint p a b c t ∧ ∀ x, tri t (read p a x) (read p b x) (read p c x) = graph x := by
  obtain ⟨k,b,c,tag,eq⟩ := asAtom g hg
  have form (x) := (hit x)
  simp_rw [eq] at form
  have no (kind : Fin 6) (i j : ℕ) : ¬∀ x, val kind (read p i x) (read p j x) = graph x := by
    intro h
    apply shorter low p len ok _ (atomLegal kind i j)
    simpa only [atomVal] using h
  have bin (t : Bool) (h : ∀ x, tri t (read p a x) (read p b x) (read p c x) = graph x) :
      ∃ b c t, footprint p a b c t ∧ ∀ x, tri t (read p a x) (read p b x) (read p c x) = graph x :=
    ⟨b,c,t,profile low p len ok a b c t h,h⟩
  fin_cases k
  · exfalso; apply no 2 a a; simpa [val] using form
  · exfalso; apply no 1 a a; simpa [val] using form
  · exfalso; apply no 5 a b; simpa [val] using form
  · have op : g.op = .not := tag rfl
    have z : inversions p = 0 := by
      simp [inversions,List.countP_append,op,GateOp.eval] at one ⊢
      omega
    have empty := form (fun _ => false)
    have high : read p b (fun _ => false) = true := by
      cases h : read p b (fun _ => false) <;> simp [h,val,graph] at empty ⊢
    have fixed (x) := monotoneFromZero p ok z x b high
    exfalso; apply no 2 a a
    simpa [val,fixed] using form
  · apply bin true; simpa [tri,val] using form
  · apply bin false; simpa [tri,val] using form

def touches (v : ℕ) (g : Gate) := (g.op.eval [false] && g.inputs.head? == some v || !g.op.eval [false] && g.inputs.contains v)
def caps (p : List Gate) := ∀ v ∈ ([0,3] : List ℕ), p.countP (touches v) ≤ 2

theorem formOfHit (low : ¬ HasCircuitSize 9 graph 14) (gs : List Gate) (len : gs.length=13)
    (ok : ∀ g ∈ gs, legal g) (lim : inversions gs≤1) (cap : caps gs) (i j : ℕ)
    (hit : ∀ x, (read gs i x || read gs j x) = graph x) :
    ∃ (p : List Gate) (a b c : ℕ) (t : Bool), p.length=12 ∧ (∀ g ∈ p, legal g) ∧
      inversions p≤1 ∧ caps p ∧ footprint p a b c t ∧ ∀ x, tri t (read p a x) (read p b x) (read p c x) = graph x := by
  obtain ⟨p,g,rfl⟩ : ∃ p g, gs=p++[g] := by
    induction gs using List.reverseRecOn with
    | nil => simp at len
    | append_singleton l g _ => exact ⟨l,g,rfl⟩
  have plen : p.length=12 := by simp at len; omega
  have pok (v) (h : v ∈ p) := ok v (List.mem_append_left _ h)
  have gok := ok g (by simp)
  have olim : inversions p≤1 := by
    simp only [inversions,List.countP_append] at lim ⊢
    omega
  have pcap : caps p := by
    intro v hv
    have z := cap v hv
    simp only [List.countP_append] at z
    omega
  have wire (u : ℕ) (x : Bits) : read (p++[g]) u x = if u=22 then gateVal p g x else read p u x := by
    change (((p++[g]).foldl step (start x)).getD u false) = _
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
    change ((wires p x)++[gateVal p g x]).getD u false = _
    rw [lastAt,show (wires p x).length=22 by simp [wires,foldLen,start,plen]]
    rfl
  have close (a) (good : ∀ x, (read p a x || gateVal p g x) = graph x) := endGate low p plen pok g gok lim a good
  by_cases hi : i=22 <;> by_cases hj : j=22
  · exfalso; apply shorter low p plen pok g gok
    simpa [wire,hi,hj] using hit
  · obtain ⟨b,c,t,shape,law⟩ := close j (by simpa [wire,hi,hj,Bool.or_comm] using hit)
    exact ⟨p,j,b,c,t,plen,pok,olim,pcap,shape,law⟩
  · obtain ⟨b,c,t,shape,law⟩ := close i (by simpa [wire,hi,hj] using hit)
    exact ⟨p,i,b,c,t,plen,pok,olim,pcap,shape,law⟩
  · exfalso; apply shorter low p plen pok _ (atomLegal 5 i j)
    simpa [wire,hi,hj,atomVal,val] using hit


theorem lastUsed (low : ¬HasCircuitSize 9 graph 14) (p : List Gate) (len : p.length=12)
    (ok : ∀ g ∈ p, legal g) (a b c : ℕ) (t : Bool)
    (hit : ∀ x, tri t (read p a x) (read p b x) (read p c x) = graph x) : 21 ∈ [a,b,c] := by
  by_contra absent
  have na : a≠21 := fun h => absent (by simp [h])
  have nb : b≠21 := fun h => absent (by simp [h])
  have nc : c≠21 := fun h => absent (by simp [h])
  obtain ⟨q,g,rfl⟩ : ∃ q g, p=q++[g] := by
    induction p using List.reverseRecOn with
    | nil => simp at len
    | append_singleton l g _ => exact ⟨l,g,rfl⟩
  have lq : q.length=11 := by simp at len; omega
  have wire (u : ℕ) (ne : u≠21) (x : Bits) (h : Gate) : read (q++[h]) u x=read q u x := by
    change (((q++[h]).foldl step (start x)).getD u false) = _
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
    change ((wires q x)++[gateVal q h x]).getD u false = _
    rw [lastAt,show (wires q x).length=21 by simp [wires,foldLen,start,lq]]
    simp only [ne,ite_false]; rfl
  let h := atom (if t then 4 else 5) b c
  have hh : legal h := atomLegal _ _ _
  have len' : (q++[h]).length=12 := by simp [lq]
  have ok' (k) (hk : k ∈ q++[h]) : legal k := by
    rcases List.mem_append.mp hk with mem | mem
    · exact ok _ (List.mem_append_left _ mem)
    · obtain rfl := List.mem_singleton.mp mem
      exact hh
  apply shorter low (q++[h]) len' ok' _ (atomLegal 5 a 21)
  intro x
  have last : read (q++[h]) 21 x = gateVal q h x := by
    change (((q++[h]).foldl step (start x)).getD 21 false) = _
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
    change ((wires q x)++[gateVal q h x]).getD 21 false = _
    rw [lastAt, show (wires q x).length=21 by simp [wires,foldLen,start,lq]]
    simp
  rw [atomVal,wire a na x h,last]
  have eq := hit x
  rw [wire a na x g,wire b nb x g,wire c nc x g] at eq
  cases t <;> simpa [h,atomVal,val,tri] using eq

theorem keep (p : List Gate) (w : List Bool) (i) (hi : i<w.length) :
    (p.foldl step w).getD i false = w.getD i false := by
  induction p generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih _ (by simp [step]; omega)]
    apply List.getD_append _ _ _ _ hi

theorem smallWire : ∀ i : Fin 10, ∃ j : Fin 9,
    let x : Bits := fun k => decide (k=j)
    (start x).getD i.val false = true ∧ graph x = false := by decide

theorem outputInternal (p : List Gate) (a b c : ℕ) (t : Bool)
    (hit : ∀ x, tri t (read p a x) (read p b x) (read p c x) = graph x) :
    10 ≤ a ∧ (t=false → 10 ≤ b ∧ 10 ≤ c) := by
  have safe (i) (always : ∀ x, read p i x=true → graph x=true) : 10 ≤ i := by
    by_contra! lt
    obtain ⟨j,h,miss⟩ := smallWire ⟨i,lt⟩
    let x : Bits := fun k => decide (k=j)
    have eq : read p i x = (start x).getD i false := keep _ _ _ (by simp [start]; omega)
    exact Bool.noConfusion ((always x (eq.trans h)).symm.trans miss)
  constructor
  · apply safe
    intro x h
    rw [←hit x]; simp [tri,h]
  · rintro rfl
    constructor
    · apply safe; intro x h; rw [←hit x]; simp [tri,h]
    · apply safe; intro x h; rw [←hit x]; simp [tri,h]



-- A pair of primary wires can feed the final product only on an edge, or
-- when vertex four meets its complete neighborhood supplied by the first OR.
def pairOK (b c : Fin 10) := ([1,4,5,12,16,23,27,34,38,49,57,58,68] : List ℕ).contains (10*b.val+c.val)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem primaryProduct : ∀ b c : Fin 10, b<c →
    ((∀ x : Bits, ((start x).getD b.val false && (start x).getD c.val false) = true → graph x = true) ↔
      pairOK b c=true) := by decide +kernel

def choices (t : Bool) : List (Fin 22 × Fin 22 × Fin 22) := do
  let a ← List.finRange 22
  let b ← List.finRange 22
  let c ← List.finRange 22
  guard (10 ≤ a.val && b < c && (a=21 || c=21))
  if t then
    guard (a≠b && a≠c)
    guard (if hb : b.val<10 then (if hc : c.val<10 then pairOK ⟨b.val,hb⟩ ⟨c.val,hc⟩ else true) else true)
  else
    guard (a<b)
  pure (a,b,c)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem choiceCounts : (choices false).length=55 ∧ (choices true).length=398 := by decide +kernel


-- The project already proved this lower bound for the same twelve-edge graph.
theorem lower : ¬ HasCircuitSize 9 graph 14 := PEqualNP.Outside.L_meta_2012

theorem pins (p : List Gate) (len : p.length=12) (a b c : ℕ) (t : Bool)
    (f : footprint p a b c t) : a<22 ∧ b<22 ∧ c<22 ∧ a≠b ∧ a≠c ∧ b≠c := by
  have row2 := f.1 2 (by cases t <;> simp)
  have row4 := f.1 4 (by cases t <;> simp)
  obtain ⟨x,hx⟩ := row2
  obtain ⟨y,hy⟩ := row4
  have two : ∀ i j k : Bool, code i j k=2 → i=false ∧ j=true ∧ k=false := by decide
  have four : ∀ i j k : Bool, code i j k=4 → i=false ∧ j=false ∧ k=true := by decide
  obtain ⟨ax,bx,cx⟩ := two _ _ _ hx
  obtain ⟨ay,by',cy⟩ := four _ _ _ hy
  have arow : ∃ z, read p a z = true := by
    cases t with
    | false =>
      obtain ⟨z,hz⟩ := f.1 1 (by simp)
      exact ⟨z,(by decide : ∀ i j k : Bool, code i j k=1 → i=true) _ _ _ hz⟩
    | true =>
      obtain ⟨n,hn,z,hz⟩ := f.2 rfl
      exact ⟨z,(by decide : ∀ i j k : Bool, code i j k ∈ ([1,3,5] : List ℕ) → i=true) _ _ _ (hz.symm ▸ hn)⟩
  have cap (i) (z) (h : read p i z = true) : i<22 := by
    by_contra! outside
    change (wires p z).getD i false=true at h
    rw [List.getD_eq_default _ _ (by simp [wires,foldLen,start,len]; omega)] at h
    contradiction
  obtain ⟨z,az⟩ := arow
  refine ⟨cap _ _ az,cap _ _ bx,cap _ _ cy,?_,?_,?_⟩
  · rintro rfl; simp [ax] at bx
  · rintro rfl; simp [ay] at cy
  · rintro rfl; simp [cx] at bx

theorem rawProductOfHit (p : List Gate) (a : ℕ) (b c : Fin 10) (hbc : b<c)
    (hit : ∀ x, tri true (read p a x) (read p b.val x) (read p c.val x) = graph x) : pairOK b c=true := by
  apply (primaryProduct b c hbc).mp
  intro x both
  obtain ⟨hb,hc⟩ := Bool.and_eq_true_iff.mp both
  rw [←hit x]
  have rd (i : Fin 10) : read p i.val x = (start x).getD i.val false :=
    keep p _ _ (by simp [start])
  change (read p a x || (read p b.val x && read p c.val x)) = true
  rw [rd b,rd c,both,Bool.or_true]


theorem ordered (p : List Gate) (a b c : ℕ) (t : Bool) (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (law : ∀ x, tri t (read p a x) (read p b x) (read p c x)=graph x) :
    ∃ A B C : ℕ, B<C ∧ (t=false → A<B) ∧
      ∀ x, tri t (read p A x) (read p B x) (read p C x)=graph x := by
  cases t with
  | true =>
    rcases lt_or_gt_of_ne bc with h | h
    · exact ⟨a,b,c,h,by simp,law⟩
    · exact ⟨a,c,b,h,by simp,by simpa [tri,Bool.and_comm] using law⟩
  | false =>
    by_cases h : a<b <;> by_cases k : b<c <;> by_cases l : a<c
    all_goals first
      | exact ⟨a,b,c,by omega,fun _ => by omega,law⟩
      | exact ⟨a,c,b,by omega,fun _ => by omega,by simpa [tri,Bool.or_comm,Bool.or_left_comm,Bool.or_assoc] using law⟩
      | exact ⟨b,a,c,by omega,fun _ => by omega,by simpa [tri,Bool.or_comm,Bool.or_left_comm,Bool.or_assoc] using law⟩
      | exact ⟨b,c,a,by omega,fun _ => by omega,by simpa [tri,Bool.or_comm,Bool.or_left_comm,Bool.or_assoc] using law⟩
      | exact ⟨c,a,b,by omega,fun _ => by omega,by simpa [tri,Bool.or_comm,Bool.or_left_comm,Bool.or_assoc] using law⟩
      | exact ⟨c,b,a,by omega,fun _ => by omega,by simpa [tri,Bool.or_comm,Bool.or_left_comm,Bool.or_assoc] using law⟩

theorem rawRule (p : List Gate) (a b c : ℕ) (t : Bool)
    (hit : ∀ x, tri t (read p a x) (read p b x) (read p c x) = graph x) :
    b<c → c<10 → 10*b+c ∈ ([1,4,5,12,16,23,27,34,38,49,57,58,68] : List ℕ) := by
  intro lt hc
  cases t with
  | false =>
    have h := ((outputInternal p a b c false hit).2 rfl).2
    omega
  | true =>
    have z := rawProductOfHit p a ⟨b,by omega⟩ ⟨c,hc⟩ lt hit
    exact List.contains_iff_mem.mp z

theorem peelChecked : let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10)))
    let R := fun (p : List Gate) (i : ℕ) (x : Fin 9 → Bool) => ((Circuit.mk p 0).wires (List.ofFn x ++ [x 0 || x 3])).getD i false
    let good := fun p : List Gate => FanInTwo (Circuit.mk p 0) ∧ (p.countP fun g => g.op.eval [false]) ≤ 1 ∧ (∀ v ∈ ([0,3] : List ℕ), (p.countP fun g => (g.op.eval [false] && g.inputs.head? == some v || !g.op.eval [false] && g.inputs.contains v)) ≤ 2)
    ∀ gs i j, List.length gs=13 → good gs → (∀ x, (R gs i x || R gs j x) = F x) →
      ∃ (p : List Gate) (a b c : ℕ) (t : Bool), List.length p=12 ∧ good p ∧ b<c ∧ (t=false → a<b) ∧ ∀ x, (R p a x || (if t then R p b x && R p c x else R p b x || R p c x)) = F x := by
  dsimp only
  intro gs i j len good eq
  obtain ⟨p,a,b,c,t,sz,ok,one,cap,fp,hit⟩ := formOfHit lower gs len good.1 good.2.1 good.2.2 i j eq
  obtain ⟨_,_,_,ab,ac,bc⟩ := pins p sz a b c t fp
  obtain ⟨A,B,C,lt,sorted,eq'⟩ := ordered p a b c t ab ac bc hit
  exact ⟨p,A,B,C,t,sz,⟨ok,one,cap⟩,lt,sorted,eq'⟩

theorem signatureChecked : let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10)))
    let R := fun (p : List Gate) (i : ℕ) (x : Fin 9 → Bool) => ((Circuit.mk p 0).wires (List.ofFn x ++ [x 0 || x 3])).getD i false
    ∀ (p : List Gate) (a b c : ℕ) (t : Bool), p.length=12 → (FanInTwo (Circuit.mk p 0) ∧ (p.countP fun g => g.op.eval [false]) ≤ 1) → (∀ x, (R p a x || (if t then R p b x && R p c x else R p b x || R p c x)) = F x) →
      ((b<c → c<10 → 10*b+c ∈ ([1,4,5,12,16,23,27,34,38,49,57,58,68] : List ℕ)) ∧ 21 ∈ [a,b,c] ∧ 10 ≤ a ∧ (t=false → 10 ≤ b ∧ 10 ≤ c) ∧ ∀ ns ∈ (if t then [[2],[4],[6],[1,3,5]] else [[0],[1],[2],[4]] : List (List ℕ)), ∃ x, (R p a x).toNat + 2*(R p b x).toNat + 4*(R p c x).toNat ∈ ns) := by
  dsimp only
  intro p a b c t len good eq
  have shape := profile lower p len good.1 a b c t eq
  obtain ⟨aMin,bcMin⟩ := outputInternal p a b c t eq
  refine ⟨rawRule p a b c t eq,lastUsed lower p len good.1 a b c t eq,aMin,bcMin,?_⟩
  have groups : ∀ ns ∈ (if t then [[2],[4],[6],[1,3,5]] else [[0],[1],[2],[4]] : List (List ℕ)), ∃ n ∈ ns, witness p a b c n := by
    cases t <;> simp [footprint] at shape ⊢ <;> tauto
  intro ns member
  obtain ⟨n,hn,x,hx⟩ := groups ns member
  refine ⟨x,?_⟩
  change code (read p a x) (read p b x) (read p c x) ∈ ns
  rwa [hx]


theorem inChoices (t : Bool) (a b c : Fin 22) (ha : 10 ≤ a.val) (hbc : b<c)
    (used : a=21 ∨ c=21) (hab : a≠b) (hac : a≠c) (order : t=false → a<b)
    (raw : ∀ hb : b.val<10, ∀ hc : c.val<10, pairOK ⟨b.val,hb⟩ ⟨c.val,hc⟩=true) :
    (a,b,c) ∈ choices t := by
  apply List.mem_flatMap.mpr
  refine ⟨a,List.mem_finRange _,List.mem_flatMap.mpr ⟨b,List.mem_finRange _,List.mem_flatMap.mpr ⟨c,List.mem_finRange _,?_⟩⟩⟩
  have hw : (a=21 || c=21) = true := by simpa using used
  cases t
  · simp [ha,hbc,hw,order rfl,guard]
  · by_cases hb : b.val<10 <;> by_cases hc : c.val<10 <;> simp [ha,hbc,hw,hab,hac,hb,hc,raw,guard]

/-- Every successful twelve-gate prefix has a terminal triple in the enumerated
list. The list contains 55 triples for a union and 398 for a product. -/
theorem canonical (p : List Gate) (len : p.length=12) (ok : ∀ g ∈ p, legal g)
    (a b c : ℕ) (t : Bool) (hit : ∀ x, tri t (read p a x) (read p b x) (read p c x) = graph x) :
    ∃ v ∈ choices t, ∀ x, tri t (read p v.1.val x) (read p v.2.1.val x) (read p v.2.2.val x)=graph x := by
  obtain ⟨_,_,_,n1,n2,n3⟩ := pins p len a b c t (profile lower p len ok a b c t hit)
  obtain ⟨A,B,C,bc,sort,eq⟩ := ordered p a b c t n1 n2 n3 hit
  obtain ⟨ra,rb,rc,ab,ac,_⟩ := pins p len A B C t (profile lower p len ok A B C t eq)
  obtain ⟨amin, _⟩ := outputInternal p A B C t eq
  have use := lastUsed lower p len ok A B C t eq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at use
  let a' : Fin 22 := ⟨A,ra⟩
  let b' : Fin 22 := ⟨B,rb⟩
  let c' : Fin 22 := ⟨C,rc⟩
  refine ⟨(a',b',c'),inChoices t a' b' c' amin bc ?_ ?_ ?_ sort ?_,eq⟩
  · have h : A=21 ∨ C=21 := by omega
    exact h.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
  · exact fun h => ab (congrArg Fin.val h)
  · exact fun h => ac (congrArg Fin.val h)
  · intro hb hc
    exact List.contains_iff_mem.mpr (rawRule p A B C t eq bc hc)

end PetersenTerminalTriples
