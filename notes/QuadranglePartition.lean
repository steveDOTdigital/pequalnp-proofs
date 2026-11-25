import PEqualNP.Defs

namespace QuadranglePartition

-- Four bits stand for the local flag rows at one vertex.
def pop (n : ℕ) : ℕ := ((List.range 4).filter fun i => n.testBit i).length
def submask (a b : ℕ) : Bool := a &&& b == a
def maskUnion (F : List ℕ) : ℕ := F.foldl (· ||| ·) 0

-- Rectangles enabled at a column must have pairwise disjoint row sets.
def pack : List ℕ → List ℕ
  | [] => [0]
  | a :: tail =>
    let prev := pack tail
    prev ++ ((prev.filter fun r => r &&& a == 0).map fun r => r ||| a)

def dominates (F : List ℕ) (i j : ℕ) : Bool :=
  F.all fun r => !(r.testBit j) || r.testBit i

def domCount (F : List ℕ) : ℕ :=
  let U := maskUnion F
  ((List.range 4).filter fun i => U.testBit i && (List.range 4).any fun j =>
    decide (j≠i) && U.testBit j && dominates F i j).length

def localCost (right : Bool) (F : List ℕ) : ℕ :=
  let U := maskUnion F
  let choices := pack F
  ((List.range 16).map fun t =>
    let freq := if pop t=1 then (if right then 18 else 27)
      else if pop t=2 then (if right then 18 else 9) else 0
    let needed := t &&& U
    let best := ((choices.filter (submask needed)).map pop).foldl min 1000
    freq * best).sum

def possible (F : List ℕ) : Bool :=
  let U := maskUnion F
  let choices := pack F
  (List.range 16).all fun t =>
    decide (pop t>2) || choices.any (submask (t &&& U))

def localOK (F : List ℕ) : Bool :=
  !possible F || [false,true].all fun right =>
    let lhs := 432*F.length + 216*domCount F + localCost right F
    let rhs := (if right then 504 else 486) * pop (maskUnion F)
    decide (rhs≤lhs) && (decide (rhs≠lhs) || decide (pop (maskUnion F)≠4) ||
      decide (F=[15]) || decide (F=[1,2,4,8]))

-- Enumerate each increasing family once. With at least one rectangle per row
-- the bound already follows by counting forced reports at the other endpoint.
def shortFamilies : List (List ℕ) :=
  let rows := (List.range 15).map (·+1)
  [[]] ++ rows.flatMap fun a =>
    [[a]] ++ (rows.filter (a < ·)).flatMap fun b =>
      [[a,b]] ++ ((rows.filter (b < ·)).map fun c => [a,b,c])

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem number_of_families : shortFamilies.length=576 := by decide +kernel

set_option maxRecDepth 100000 in
theorem short_certificate : shortFamilies.all localOK=true := by decide +kernel

theorem each_short {F : List ℕ} (h : F ∈ shortFamilies) : localOK F=true :=
  List.all_eq_true.mp short_certificate F h


theorem certified_price {F : List ℕ} (h : F ∈ shortFamilies)
    (ok : possible F=true) (right : Bool) :
    (if right then 504 else 486)*pop (maskUnion F) ≤
      432*F.length+216*domCount F+localCost right F := by
  have law := each_short h
  simp only [localOK,ok,Bool.not_true,Bool.false_or] at law
  have hx := List.all_eq_true.mp law right (by cases right <;> simp)
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp hx).1

-- The global double count after summing the local inequalities. The m flags
-- contribute one point and one line slot, 234 reports and at most m dominated slots.
theorem aggregate (m leaves dom reports : ℕ) (hdom : dom≤m) (hrep : reports=234*m)
    (locals : 486*m+504*m ≤ 432*leaves+216*dom+reports) : 5*m≤4*leaves := by omega

theorem full_bound (leaves dom reports : ℕ) (hdom : dom≤52) (hrep : reports=234*52)
    (locals : 486*52+504*52 ≤ 432*leaves+216*dom+reports) : 65≤leaves := by
  have := aggregate 52 leaves dom reports hdom hrep locals
  omega

-- For each selected rectangle set, disjoint union realizes an element of pack.
theorem mem_pack_cons_left {r a : ℕ} {F : List ℕ} (h : r ∈ pack F) :
    r ∈ pack (a::F) := List.mem_append_left _ h

theorem mem_pack_cons_right {r a : ℕ} {F : List ℕ} (h : r ∈ pack F) (dis : r &&& a=0) :
    r ||| a ∈ pack (a::F) := by
  simp only [pack,List.mem_append,List.mem_map,List.mem_filter]
  exact Or.inr ⟨r,⟨h,by simp [dis]⟩,rfl⟩


def incidence (p l : ℕ) : Bool := [0,1,3,9].contains ((p+13-l)%13)
def neighbor (v i : ℕ) : ℕ :=
  let a := [0,1,3,9].getD i 0
  if v<13 then 13+(v+13-a)%13 else (v-13+a)%13

def columns : List ℕ := [3211303, 7340103, 6357127, 5310471, 5275731, 4751635, 5769235, 1609747, 2688035, 1640483, 3674147, 6324419, 3182659, 4292995, 2196611, 623875, 4786435, 2659331, 21233693, 23068749, 6553741, 19137549, 22020181, 18088469, 5507093, 19923045, 17891877, 18940965, 2425989, 4524165, 17106437, 1378821, 21496089, 17564697, 4982809, 18890857, 17318185, 19399721, 2641961, 6308041, 20988233, 4475017, 2379913, 4737289, 2888713, 808969, 21004625, 17859153, 17335569, 17073681, 1348113, 824337, 1841169, 17842785, 3166305, 16859937, 17368353, 608545, 1133089, 1595425, 4243905, 2150593, 16827201, 1102401, 115585, 4278657, 362113, 346753, 316033, 2397313, 16877313, 1333761, 6422606, 14680206, 12714254, 10620942, 10551462, 9503270, 11538470, 5376070, 3280966, 12648838, 8585990, 4393222, 1247750, 9572870, 42467386, 46137498, 13107482, 38275098, 44040362, 36176938, 11014186, 39846090, 35783754, 37881930, 4851978, 9048330, 34212874, 2757642, 42992178, 35129394, 9965618, 37781714, 34636370, 38799442, 12616082, 41976466, 8950034, 9474578, 42009250, 35718306, 34671138, 34147362, 35685570, 33719874, 34736706, 1217090, 2266178, 8487810, 33654402, 231170, 8557314, 724226, 693506, 33754626, 12845212, 29360412, 25428508, 21102924, 19006540, 10752140, 25297676, 17171980, 8786444, 2495500, 17834100, 25174324, 26214964, 9449524, 20980052, 5253204, 12591508, 4466836, 8663188, 9703956, 1325076, 18883684, 3158116, 8462756, 2172068, 10498212, 25232164, 16852260, 16917828, 4335940, 2241604, 1194052, 4270468, 339076, 2372740, 16975620, 208132, 462340, 1448452, 408580, 25690424, 58720824, 50857016, 42205848, 38013080, 50595352, 34343960, 35668200, 50348648, 52429928, 41960104, 10506408, 25183016, 8933672, 37767368, 16925512, 4344136, 50464328, 33704520, 33835656, 8671880, 8540936, 678152, 33951240, 416264, 924680, 51380848, 50340976, 34613360, 17311024, 8925488, 34090032, 1587248, 4235728, 33596624, 37759184, 16819536, 50366032, 8434064, 33851024, 8688272, 33827984, 308368, 570640, 801808, 35661024, 33581280, 2126048, 34622048, 1079392, 8471456, 92576, 8417696, 33639072, 33631392, 601376, 555296, 4221376, 61888, 2143424, 16942912, 185152, 177472, 162112, 1202752, 8442752, 33885824, 670976]
def lineCount (word l : ℕ) : ℕ :=
  ((List.range 13).filter fun p => word.testBit p && incidence p l).length

def validColumn (word : ℕ) : Bool :=
  decide (((List.range 13).filter word.testBit).length=4) &&
  (List.range 13).all fun l => decide (lineCount word l≤2) &&
    (word.testBit (13+l) == decide (lineCount word l=0))

theorem geometry : columns.length=234 ∧ columns.Nodup ∧ columns.all validColumn=true := by
  decide +kernel

theorem nonedge_extension : ∀ p l : Fin 13, incidence p l=false →
    columns.any (fun t => t.testBit p.val && t.testBit (13+l.val))=true := by decide +kernel

theorem cross_nonedge : ∀ p l a b : Fin 13, incidence p l=true → incidence a l=true →
    incidence p b=true → a≠p → b≠l → incidence a b=false := by decide +kernel

def forcedRows (v word : ℕ) : ℕ :=
  ((List.range 4).map fun i => if word.testBit (neighbor v i) then 2^i else 0).sum

def histOK (v : ℕ) : Bool :=
  let rows := (columns.filter (fun t => !(t.testBit v))).map (forcedRows v)
  (List.range 16).all fun t => rows.count t ==
    (if pop t=1 then (if v<13 then 27 else 18)
     else if pop t=2 then (if v<13 then 9 else 18) else 0)

theorem actual_histograms : (List.range 26).all histOK=true := by decide +kernel

-- A default of false uses OR, a default of true uses AND. The first
-- signal differing from its default determines the label on the promise.
def restore : List (Bool × Bool × Bool) → Bool → Bool
  | [], last => last
  | (d,_,r)::rest, last => if d then r && restore rest last else r || restore rest last

theorem priority (wires : List (Bool × Bool × Bool)) (last want : Bool)
    (good : ∀ x ∈ wires, x.2.1 ≠ x.1 → x.2.1=want)
    (agrees : ∀ pre x post, wires=pre++x::post → (∀ y ∈ pre, y.2.1=y.1) → x.2.2=x.2.1)
    (finish : (∀ x ∈ wires, x.2.1=x.1) → last=want) : restore wires last=want := by
  induction wires with
  | nil => exact finish (by simp)
  | cons x xs ih =>
    obtain ⟨d,a,r⟩ := x
    have eq : r=a := agrees [] (d,a,r) xs rfl (by simp)
    subst r
    by_cases hit : a=d
    · have tail := ih (fun y hy => good y (by simp [hy]))
        (fun pre x post h hh => agrees ((d,a,a)::pre) x post (by simp [h])
          (fun y hy => by rcases List.mem_cons.mp hy with rfl|hy; exact hit; exact hh y hy))
        (fun all => finish (fun y hy => by
          rcases List.mem_cons.mp hy with rfl|hy; exact hit; exact all y hy))
      cases d <;> simp_all [restore]
    · have isGoal := good (d,a,a) (by simp) hit
      cases d <;> cases a <;> simp_all [restore]

theorem unsharing_count (s shared readers joins residual : ℕ)
    (uses : 2*shared≤2*readers) (joins_le : joins≤shared)
    (removed : residual+readers≤s) : residual+joins≤s := by omega

inductive Tree where
  | raw (v : Fin 26)
  | gate (isOr : Bool) (a b : Tree)

def Tree.val : Tree → (Fin 26 → Bool) → Bool
  | .raw v,x => x v
  | .gate op a b,x => if op then a.val x || b.val x else a.val x && b.val x

def Tree.leaves : Tree → ℕ
  | .raw _ => 1
  | .gate _ a b => a.leaves+b.leaves

structure Protocol (X Y : Type) where
  size : ℕ
  label : Fin size → Fin 26
  start : X → Y → Fin size
  row : Fin size → X → Bool
  col : Fin size → Y → Bool
  block : ∀ x y b, start x y=b ↔ row b x=true ∧ col b y=true

-- Row and column tests are independent. This construction permits two
-- disjoint occurrences of the same raw variable to carry different blocks.
theorem tree_protocol {Pos Neg : Type} (T : Tree) (px : Pos → Fin 26 → Bool) (ny : Neg → Fin 26 → Bool) :
    ∃ P : Protocol (Pos) (Neg), P.size=T.leaves ∧
      ∀ e t, T.val (px e)=true → T.val (ny t)=false →
        px e (P.label (P.start e t))=true ∧ ny t (P.label (P.start e t))=false := by
  induction T with
  | raw v =>
    exact ⟨⟨1,fun _ => v,fun _ _ => 0,fun _ _ => true,fun _ _ => true,
      fun e t b => by fin_cases b; simp⟩,rfl,fun _ _ h q => ⟨h,q⟩⟩
  | gate op a b ia ib =>
    obtain ⟨A,sa,ha⟩ := ia
    obtain ⟨B,sb,hb⟩ := ib
    let E := finSumFinEquiv (m:=A.size) (n:=B.size)
    let onA := fun e t => if op then a.val (px e) else !(a.val (ny t))
    let start := fun e t => E (if onA e t then Sum.inl (A.start e t) else Sum.inr (B.start e t))
    let lab := fun i => Sum.elim A.label B.label (E.symm i)
    let row := fun i e => Sum.elim (fun j => A.row j e && (!op || a.val (px e)))
      (fun j => B.row j e && (!op || !(a.val (px e)))) (E.symm i)
    let col := fun i t => Sum.elim (fun j => A.col j t && (op || !(a.val (ny t))))
      (fun j => B.col j t && (op || a.val (ny t))) (E.symm i)
    have rect : ∀ e t i, start e t=i ↔ row i e=true ∧ col i t=true := by
      intro e t i
      obtain ⟨u,rfl⟩ := E.surjective i
      cases u with
      | inl j =>
        cases op <;> cases x : a.val (px e) <;> cases y : a.val (ny t) <;>
          simp [start,onA,row,col,x,y,A.block]
      | inr j =>
        cases op <;> cases x : a.val (px e) <;> cases y : a.val (ny t) <;>
          simp [start,onA,row,col,x,y,B.block]
    refine ⟨⟨A.size+B.size,lab,start,row,col,rect⟩,by simp [Tree.leaves,sa,sb],?_⟩
    intro e t on off
    change px e (lab (start e t))=true ∧ ny t (lab (start e t))=false
    cases op <;> cases x : a.val (px e) <;> cases y : a.val (ny t) <;>
      simp_all [Tree.val,lab,start,onA]



-- Vertex degree sums are m on each shore. Each selected cell contributes
-- one report, independently of how its formula routed the witness.
theorem vertex_sum {V : Type} [Fintype V] (k d h base : V → ℕ) (m : ℕ)
    (one : ∀ v, base v ≤ 432*k v+216*d v+h v)
    (degree : ∑ v, base v=486*m+504*m) (disjoint : ∑ v, d v≤m)
    (partition : ∑ v, h v=234*m) : 5*m≤4*∑ v, k v := by
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => one v)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at total
  rw [degree] at total
  exact aggregate m _ _ _ disjoint partition total

end QuadranglePartition
