import PEqualNP.Defs

namespace Independent.QuadrangleFreeOr
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def addOr (n : ℕ) (s : List ℕ) (c : Circuit) : Circuit :=
  ⟨⟨.or, s.filter (fun i => i < n)⟩ :: c.gates, c.output⟩

def withOr (s : List ℕ) (x : List Bool) := x ++ [s.any (fun i => x.getD i false)]

theorem addOr_size (n s c) : (addOr n s c).size = c.size + 1 := by
  simp [addOr,Circuit.size]

theorem addOr_mono (n s c) (size : s.length ≤ 2) (hc : Monotone2 c) :
    Monotone2 (addOr n s c) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact ⟨by simp, le_trans (List.length_filter_le ..) size⟩
  · exact hc _ hg

theorem addOr_eval (s : List ℕ) (c : Circuit) (x : List Bool) :
    (addOr x.length s c).eval x = c.eval (withOr s x) := by
  have same : ((s.filter (fun i => decide (i < x.length))).map (fun i => x.getD i false)).any id =
      s.any (fun i => x.getD i false) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq, id_eq]
    constructor
    · rintro ⟨v,⟨i,⟨hi,_⟩,rfl⟩,hit⟩
      exact ⟨i,hi,hit⟩
    · rintro ⟨i,hi,hit⟩
      have valid : i < x.length := by
        by_contra! bad
        rw [List.getD_eq_default _ _ bad] at hit
        contradiction
      exact ⟨_,⟨i,⟨hi,valid⟩,rfl⟩,hit⟩
  simp only [addOr,Circuit.eval,Circuit.wires,List.foldl_cons,GateOp.eval,withOr,same]

theorem addOr_legal {n s c} (hc : ∀ j : Fin c.gates.length, ∀ w ∈ (c.gates.get j).inputs,
    w < n + 1 + j.val) : ∀ i : Fin (addOr n s c).gates.length,
      ∀ w ∈ ((addOr n s c).gates.get i).inputs, w < n + i.val := by
  rintro ⟨i,hi⟩ w hw
  cases i with
  | zero =>
    change w ∈ s.filter (fun j => decide (j < n)) at hw
    simpa using (List.mem_filter.mp hw).2
  | succ i =>
    have lt : i < c.gates.length := by simpa [addOr] using hi
    have h := hc ⟨i,lt⟩ w hw
    change w < n + 1 + i at h
    change w < n + (i+1)
    omega

-- Symbolic monotone evaluation. A polynomial is the disjunction of its terms.
abbrev Poly := List (Finset ℕ)
def accepts (x : ℕ → Bool) (t : Poly) : Bool :=
  t.any (fun m => decide (∀ i ∈ m, x i = true))
def prod (a b : Poly) : Poly := a.flatMap (fun m => b.map (fun n => m ∪ n))
def atom (i : ℕ) : Poly := [{i}]

theorem accepts_append (x a b) : accepts x (a++b) = (accepts x a || accepts x b) := by
  simp [accepts]
theorem accepts_prod (x a b) : accepts x (prod a b) = (accepts x a && accepts x b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [accepts,prod,List.any_eq_true,List.mem_flatMap,List.mem_map,decide_eq_true_eq,
    Bool.and_eq_true]
  aesop
theorem accepts_atom (x i) : accepts x (atom i) = x i := by simp [accepts,atom]

def symbolic (ws : List Poly) (g : Gate) : List Poly :=
  let values := g.inputs.map (fun i => ws.getD i [])
  ws ++ [match g.op, values with
    | .or, [a,b] => a++b
    | .and, [a,b] => prod a b
    | _, _ => []]
def binary (g : Gate) := g.inputs.length = 2 ∧ (g.op = .and ∨ g.op = .or)

theorem sim (x : ℕ → Bool) (gs : List Gate) (ws : List Poly) (ok : ∀ g ∈ gs, binary g) :
    (gs.foldl symbolic ws).map (accepts x) =
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (ws.map (accepts x)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih _ (fun q h => ok q (List.mem_cons_of_mem _ h))]
    obtain ⟨len,op⟩ := ok g (by simp)
    obtain ⟨a,b,eq⟩ := List.length_eq_two.mp len
    have lookup (i : ℕ) : (ws.map (accepts x)).getD i false = accepts x (ws.getD i []) := by
      change (ws.map (accepts x)).getD i (accepts x []) = _
      rw [List.getD_map]
    rcases op with op | op <;> simp only [symbolic,eq,op,List.map_cons,List.map_nil,List.map_append,lookup,
      accepts_prod,accepts_append,GateOp.eval,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,
      Bool.and_true,Bool.or_false]

def edgeTerms : Finset (Finset ℕ) :=
  (((Finset.range 13).product (Finset.range 13)).filter (fun z =>
    (z.1+13-z.2)%13 ∈ ([0,1,3,9] : List ℕ))).image (fun z => {z.1,13+z.2})

def initial (s : List ℕ) : List Poly := (List.range 26).map atom ++ [s.flatMap atom]
def actual (s : List ℕ) (x : ℕ → Bool) : List Bool := (initial s).map (accepts x)

theorem actual_eq (s : List ℕ) (x : ℕ → Bool) :
    actual s x = (List.range 26).map x ++ [s.any x] := by
  simp [actual,initial,List.map_map,Function.comp_def,accepts,
    List.any_flatMap,atom]

def project (c : Circuit) (s : List ℕ) :=
  (c.gates.foldl symbolic (initial s)).getD c.output []

theorem correct (s : List ℕ) (c : Circuit) (ok : ∀ g ∈ c.gates, binary g)
    (test : (project c s).toFinset = edgeTerms) (x : ℕ → Bool) :
    c.eval (actual s x) = true ↔ ∃ t ∈ edgeTerms, ∀ i ∈ t, x i = true := by
  have simulates := sim x c.gates (initial s) ok
  change _ = c.wires (actual s x) at simulates
  rw [Circuit.eval,←simulates]
  change ((c.gates.foldl symbolic (initial s)).map (accepts x)).getD _ (accepts x []) = true ↔ _
  rw [List.getD_map]
  change accepts x (project c s) = true ↔ _
  rw [←test]
  simp [accepts]

def compact (g : Bool × ℕ × ℕ) : Gate := ⟨if g.1 then .or else .and,[g.2.1,g.2.2]⟩
theorem compact_ok (g : Bool × ℕ × ℕ) : binary (compact g) := by
  cases g with
  | mk k v => cases k <;> simp [binary,compact]

def freePoints : Circuit := ⟨([
    (true,26,3),(true,27,9),(false,13,28),(true,1,2),(true,30,4),
    (true,31,10),(false,14,32),(true,2,3),(true,34,5),(true,35,11),
    (false,15,36),(true,3,4),(true,38,6),(true,39,12),(false,16,40),
    (true,0,4),(true,42,5),(true,43,7),(false,17,44),(true,1,5),
    (true,46,6),(true,47,8),(false,18,48),(true,2,6),(true,50,7),
    (true,51,9),(false,19,52),(true,3,7),(true,54,8),(true,55,10),
    (false,20,56),(true,4,8),(true,58,9),(true,59,11),(false,21,60),
    (true,5,9),(true,62,10),(true,63,12),(false,22,64),(true,0,6),
    (true,66,10),(true,67,11),(false,23,68),(true,1,7),(true,70,11),
    (true,71,12),(false,24,72),(true,0,2),(true,74,8),(true,75,12),
    (false,25,76),(true,29,33),(true,78,37),(true,79,41),(true,80,45),
    (true,81,49),(true,82,53),(true,83,57),(true,84,61),(true,85,65),
    (true,86,69),(true,87,73),(true,88,77)] : List (Bool × ℕ × ℕ)).map compact,89⟩

set_option maxRecDepth 24000 in
theorem freePoints_data : freePoints.size = 63 ∧ (project freePoints [0,1]).toFinset = edgeTerms ∧
    (∀ i : Fin freePoints.gates.length, ∀ w ∈ (freePoints.gates.get i).inputs, w < 27+i.val) := by
  decide +kernel

theorem freePoints_correct (x : ℕ → Bool) :
    freePoints.eval (actual [0,1] x) = true ↔ ∃ t ∈ edgeTerms, ∀ i ∈ t, x i = true := by
  apply correct _ _ _ freePoints_data.2.1
  intro g hg
  obtain ⟨h,_,rfl⟩ := List.mem_map.mp hg
  exact compact_ok h

def freeLines : Circuit := ⟨([
    (true,13,17),(true,27,23),(true,28,25),(false,0,29),(true,26,18),
    (true,31,24),(false,1,32),(true,14,15),(true,34,19),(true,35,25),
    (false,2,36),(true,13,15),(true,38,16),(true,39,20),(false,3,40),
    (true,14,16),(true,42,17),(true,43,21),(false,4,44),(true,15,17),
    (true,46,18),(true,47,22),(false,5,48),(true,16,18),(true,50,19),
    (true,51,23),(false,6,52),(true,17,19),(true,54,20),(true,55,24),
    (false,7,56),(true,18,20),(true,58,21),(true,59,25),(false,8,60),
    (true,13,19),(true,62,21),(true,63,22),(false,9,64),(true,14,20),
    (true,66,22),(true,67,23),(false,10,68),(true,15,21),(true,70,23),
    (true,71,24),(false,11,72),(true,16,22),(true,74,24),(true,75,25),
    (false,12,76),(true,30,33),(true,78,37),(true,79,41),(true,80,45),
    (true,81,49),(true,82,53),(true,83,57),(true,84,61),(true,85,65),
    (true,86,69),(true,87,73),(true,88,77)] : List (Bool × ℕ × ℕ)).map compact,89⟩

set_option maxRecDepth 24000 in
theorem freeLines_data : freeLines.size = 63 ∧ (project freeLines [13,14]).toFinset = edgeTerms ∧
    (∀ i : Fin freeLines.gates.length, ∀ w ∈ (freeLines.gates.get i).inputs, w < 27+i.val) := by
  decide +kernel

theorem freeLines_correct (x : ℕ → Bool) :
    freeLines.eval (actual [13,14] x) = true ↔ ∃ t ∈ edgeTerms, ∀ i ∈ t, x i = true := by
  apply correct _ _ _ freeLines_data.2.1
  intro g hg
  obtain ⟨h,_,rfl⟩ := List.mem_map.mp hg
  exact compact_ok h

def ordinary : Circuit := ⟨([
    (true,0,1),(true,27,3),(true,28,9),(false,13,29),(true,1,2),
    (true,31,4),(true,32,10),(false,14,33),(true,2,3),(true,35,5),
    (true,36,11),(false,15,37),(true,3,4),(true,39,6),(true,40,12),
    (false,16,41),(true,0,4),(true,43,5),(true,44,7),(false,17,45),
    (true,1,5),(true,47,6),(true,48,8),(false,18,49),(true,2,6),
    (true,51,7),(true,52,9),(false,19,53),(true,3,7),(true,55,8),
    (true,56,10),(false,20,57),(true,4,8),(true,59,9),(true,60,11),
    (false,21,61),(true,5,9),(true,63,10),(true,64,12),(false,22,65),
    (true,0,6),(true,67,10),(true,68,11),(false,23,69),(true,1,7),
    (true,71,11),(true,72,12),(false,24,73),(true,0,2),(true,75,8),
    (true,76,12),(false,25,77),(true,30,34),(true,79,38),(true,80,42),
    (true,81,46),(true,82,50),(true,83,54),(true,84,58),(true,85,62),
    (true,86,66),(true,87,70),(true,88,74),(true,89,78)] : List (Bool × ℕ × ℕ)).map compact,90⟩

set_option maxRecDepth 24000 in
theorem ordinary_data : ordinary.size = 64 ∧ (project ordinary []).toFinset = edgeTerms ∧
    (∀ i : Fin ordinary.gates.length, ∀ w ∈ (ordinary.gates.get i).inputs, w < 27+i.val) := by
  decide +kernel

theorem ordinary_correct (x : ℕ → Bool) :
    ordinary.eval (actual [] x) = true ↔ ∃ t ∈ edgeTerms, ∀ i ∈ t, x i = true := by
  apply correct _ _ _ ordinary_data.2.1
  intro g hg
  obtain ⟨h,_,rfl⟩ := List.mem_map.mp hg
  exact compact_ok h

def offsets : Finset (Fin 13) := {0,1,3,9}

theorem relation : ∀ p l : Fin 13,
    (p.val+13-l.val)%13 ∈ ([0,1,3,9] : List ℕ) ↔ p-l ∈ offsets := by decide +kernel

theorem terms_edges (x : ℕ → Bool) :
    (∃ t ∈ edgeTerms, ∀ i ∈ t, x i = true) ↔
      ∃ p l : Fin 13, p-l ∈ offsets ∧ x p.val = true ∧ x (13+l.val) = true := by
  constructor
  · rintro ⟨t,ht,hx⟩
    obtain ⟨⟨p,l⟩,mem,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨inRange,hit⟩ := Finset.mem_filter.mp mem
    obtain ⟨hp,hl⟩ := Finset.mem_product.mp inRange
    let a : Fin 13 := ⟨p, Finset.mem_range.mp hp⟩
    let b : Fin 13 := ⟨l, Finset.mem_range.mp hl⟩
    exact ⟨a,b,(relation a b).mp hit,hx p (by simp),hx (13+l) (by simp)⟩
  · rintro ⟨p,l,hit,hp,hl⟩
    refine ⟨{p.val,13+l.val},Finset.mem_image.mpr ⟨(p.val,l.val),?_,rfl⟩,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr p.isLt,
        Finset.mem_range.mpr l.isLt⟩,(relation p l).mpr hit⟩
    · intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> assumption

def bits (p l : Fin 13 → Bool) (i : ℕ) : Bool :=
  if h : i < 13 then p ⟨i,h⟩ else if k : i-13 < 13 then l ⟨i-13,k⟩ else false

theorem join_ends (p l : Fin 13 → Bool) (a b : Fin 13) :
    bits p l a.val = p a ∧ bits p l (13 + b.val) = l b := by
  simp [bits,a.isLt,Nat.not_lt_of_ge (Nat.le_add_right 13 b.val),b.isLt]

theorem positive (a b : Fin 13) (hit : a-b ∈ offsets) :
    let x := bits (fun r => decide (r=a)) (fun s => decide (s=b))
    ∃ t ∈ edgeTerms, ∀ i ∈ t, x i = true := by
  dsimp only
  apply (terms_edges _).mpr
  obtain ⟨hp,hl⟩ := join_ends (fun r => decide (r=a)) (fun s => decide (s=b)) a b
  exact ⟨a,b,hit,by simpa using hp,by simpa using hl⟩

theorem independent (Q : Finset (Fin 13)) :
    let x := bits (fun p => decide (p∈Q)) (fun l => decide (∀ p ∈ Q, p-l ∉ offsets))
    ¬∃ t ∈ edgeTerms, ∀ i ∈ t, x i = true := by
  dsimp only
  intro hasEdge
  obtain ⟨a,b,ab,ha,hb⟩ := (terms_edges _).mp hasEdge
  obtain ⟨hp,hl⟩ := join_ends (fun p => decide (p∈Q)) (fun l => decide (∀ p ∈ Q, p-l ∉ offsets)) a b
  rw [hp] at ha
  rw [hl] at hb
  exact of_decide_eq_true hb a (of_decide_eq_true ha) ab

set_option maxRecDepth 24000 in
theorem ordinaryMarker : (project ordinary [26]).toFinset = edgeTerms := by decide +kernel

theorem ordinary_all (s : List ℕ) (x : ℕ → Bool) :
    ordinary.eval (actual s x) = true ↔ ∃ p l : Fin 13,
      p-l ∈ offsets ∧ x p.val = true ∧ x (13+l.val) = true := by
  let y := Function.update x 26 (s.any x)
  have same (i : ℕ) (hi : i < 26) : y i = x i := Function.update_of_ne (by omega) _ _
  have start : actual [26] y = actual s x := by
    rw [actual_eq,actual_eq]
    have raw : (List.range 26).map y = (List.range 26).map x :=
      List.map_congr_left (fun i h => same i (List.mem_range.mp h))
    simp [raw,y]
  rw [←start,correct [26] ordinary (by
    intro g hg
    obtain ⟨h,_,rfl⟩ := List.mem_map.mp hg
    exact compact_ok h) ordinaryMarker,terms_edges]
  have points (p : Fin 13) : y p.val = x p.val := same _ (by have := p.isLt; omega)
  have lines (l : Fin 13) : y (13+l.val) = x (13+l.val) := same _ (by have := l.isLt; omega)
  simp [points,lines]

end Independent.QuadrangleFreeOr
