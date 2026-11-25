import PEqualNP.Defs

namespace PlaneSelectedRoot
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate

abbrev Row := Fin 26 → Bool

def incident (p l : Fin 13) := p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9

def containsFlag (x : Row) := ∃ p l : Fin 13, incident p l ∧
  x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true

def linePoints (l : Fin 13) := [l,l+1,l+3,l+9]
def others : List (Fin 13) := [1,2,3,4,5,6,7,8,9,10,11,12]
def either (a b : Bool) := GateOp.or.eval [a,b]
def both (a b : Bool) := GateOp.and.eval [a,b]

def merge : List Bool → Bool
  | [] => false
  | [a] => a
  | a :: b :: t => either a (merge (b::t))

def touched (x : Row) (l : Fin 13) :=
  merge ((linePoints l).map fun p => x (Fin.castAdd 13 p))
def alarm (x : Row) (l : Fin 13) := both (x (Fin.natAdd 13 l)) (touched x l)
def remainder (x : Row) := merge (others.map (alarm x))

theorem mergeYes (bs : List Bool) : merge bs = true ↔ true ∈ bs := by
  induction bs with
  | nil => decide
  | cons a bs ih =>
    cases bs with
    | nil => simp [merge,eq_comm]
    | cons b bs => simp only [merge,either,GateOp.eval,List.any_cons,List.any_nil,id_eq,
        Bool.or_false,Bool.or_eq_true,ih,List.mem_cons]; tauto

theorem linePointsSpec (p l : Fin 13) : p ∈ linePoints l ↔ incident p l := by
  simp [linePoints,incident]

theorem touchedYes (x : Row) (l : Fin 13) :
    touched x l = true ↔ ∃ p, incident p l ∧ x (Fin.castAdd 13 p) = true := by
  simp [touched,mergeYes,List.mem_map,linePointsSpec]

theorem alarmYes (x : Row) (l : Fin 13) :
    alarm x l = true ↔ x (Fin.natAdd 13 l) = true ∧
      ∃ p, incident p l ∧ x (Fin.castAdd 13 p) = true := by
  simp [alarm,both,GateOp.eval,touchedYes]

theorem otherMem : ∀ l : Fin 13, l ∈ others ↔ l ≠ 0 := by decide +kernel

theorem remainderYes (x : Row) :
    remainder x = true ↔ ∃ l : Fin 13, l ≠ 0 ∧ x (Fin.natAdd 13 l) = true ∧
      ∃ p, incident p l ∧ x (Fin.castAdd 13 p) = true := by
  simp only [remainder,mergeYes,List.mem_map,otherMem,alarmYes]

theorem flagSplit (x : Row) : containsFlag x ↔ remainder x = true ∨
    (touched x 0 = true ∧ x 13 = true) := by
  rw [remainderYes,touchedYes]
  constructor
  · rintro ⟨p,l,inc,hp,hl⟩
    by_cases zero : l = 0
    · subst l; exact Or.inr ⟨⟨p,inc,hp⟩,hl⟩
    · exact Or.inl ⟨l,zero,hl,p,inc,hp⟩
  · rintro (⟨l,_,hl,p,inc,hp⟩ | ⟨⟨p,inc,hp⟩,hl⟩)
    · exact ⟨p,l,inc,hp,hl⟩
    · exact ⟨p,0,inc,hp,hl⟩

def circuit : Circuit := ⟨[
    ⟨.or,[4,10]⟩,⟨.or,[2,26]⟩,⟨.or,[1,27]⟩,⟨.and,[14,28]⟩,
    ⟨.or,[5,11]⟩,⟨.or,[3,30]⟩,⟨.or,[2,31]⟩,⟨.and,[15,32]⟩,
    ⟨.or,[6,12]⟩,⟨.or,[4,34]⟩,⟨.or,[3,35]⟩,⟨.and,[16,36]⟩,
    ⟨.or,[7,0]⟩,⟨.or,[5,38]⟩,⟨.or,[4,39]⟩,⟨.and,[17,40]⟩,
    ⟨.or,[8,1]⟩,⟨.or,[6,42]⟩,⟨.or,[5,43]⟩,⟨.and,[18,44]⟩,
    ⟨.or,[9,2]⟩,⟨.or,[7,46]⟩,⟨.or,[6,47]⟩,⟨.and,[19,48]⟩,
    ⟨.or,[10,3]⟩,⟨.or,[8,50]⟩,⟨.or,[7,51]⟩,⟨.and,[20,52]⟩,
    ⟨.or,[11,4]⟩,⟨.or,[9,54]⟩,⟨.or,[8,55]⟩,⟨.and,[21,56]⟩,
    ⟨.or,[12,5]⟩,⟨.or,[10,58]⟩,⟨.or,[9,59]⟩,⟨.and,[22,60]⟩,
    ⟨.or,[0,6]⟩,⟨.or,[11,62]⟩,⟨.or,[10,63]⟩,⟨.and,[23,64]⟩,
    ⟨.or,[1,7]⟩,⟨.or,[12,66]⟩,⟨.or,[11,67]⟩,⟨.and,[24,68]⟩,
    ⟨.or,[2,8]⟩,⟨.or,[0,70]⟩,⟨.or,[12,71]⟩,⟨.and,[25,72]⟩,
    ⟨.or,[69,73]⟩,⟨.or,[65,74]⟩,⟨.or,[61,75]⟩,⟨.or,[57,76]⟩,
    ⟨.or,[53,77]⟩,⟨.or,[49,78]⟩,⟨.or,[45,79]⟩,⟨.or,[41,80]⟩,
    ⟨.or,[37,81]⟩,⟨.or,[33,82]⟩,⟨.or,[29,83]⟩,⟨.or,[3,9]⟩,
    ⟨.or,[1,85]⟩,⟨.or,[0,86]⟩,⟨.or,[84,87]⟩,⟨.or,[84,13]⟩,
    ⟨.and,[88,89]⟩],90⟩

theorem valid : circuit.size = 65 ∧ IsAO2 26 circuit ∧
    (∀ g ∈ circuit.gates, g.inputs.Nodup) ∧ circuit.output = 26+64 ∧
    circuit.gates[64]? = some ⟨.and,[88,89]⟩ := by
  refine ⟨rfl,by decide +kernel,?_,rfl,rfl⟩
  exact List.all_eq_true.mp (show circuit.gates.all (fun g => decide g.inputs.Nodup) = true by decide +kernel) |> fun h g hg => of_decide_eq_true (h g hg)

private def advance (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem simulate (gs : List Gate) (w : List Bool) (v : ℕ → Bool)
    (start : ∀ i < w.length, w.getD i false = v i)
    (steps : ∀ j : Fin gs.length, let g := gs[j.val]
      (∀ i ∈ g.inputs, i < w.length+j.val) ∧ g.op.eval (g.inputs.map v) = v (w.length+j.val)) :
    ∀ i < w.length + gs.length, (gs.foldl advance w).getD i false = v i := by
  induction gs generalizing w with
  | nil => simpa using start
  | cons g gs ih =>
    have now := steps ⟨0,by simp⟩
    simp only [List.getElem_cons_zero,Nat.add_zero] at now
    have eqv : g.op.eval (g.inputs.map fun i => w.getD i false) = v w.length := by
      rw [← now.2]
      congr 1
      apply List.map_congr_left
      exact fun i mem => start i (now.1 i mem)
    have len : (advance w g).length = w.length+1 := by simp [advance]
    have next : ∀ i < (advance w g).length, (advance w g).getD i false = v i := by
      intro i hi
      by_cases lt : i < w.length
      · rw [advance,List.getD_append _ _ _ _ lt,start i lt]
      · have e : i=w.length := by omega
        subst i
        rw [advance,List.getD_append_right _ _ _ _ (Nat.le_refl _),Nat.sub_self]
        exact eqv
    have tail (j : Fin gs.length) := steps ⟨j.val+1,by simp⟩
    intro i hi
    apply ih (advance w g) next _ i (by simp only [len]; simp only [List.length_cons] at hi; omega)
    intro j
    simpa only [List.getElem_cons_succ,len,Nat.add_right_comm,Nat.add_assoc,Nat.add_comm 1] using tail j

private def values (x : Row) : List Bool :=
  let w26 := either (x 4) (x 10)
  let w27 := either (x 2) w26
  let w28 := either (x 1) w27
  let w29 := both (x 14) w28
  let w30 := either (x 5) (x 11)
  let w31 := either (x 3) w30
  let w32 := either (x 2) w31
  let w33 := both (x 15) w32
  let w34 := either (x 6) (x 12)
  let w35 := either (x 4) w34
  let w36 := either (x 3) w35
  let w37 := both (x 16) w36
  let w38 := either (x 7) (x 0)
  let w39 := either (x 5) w38
  let w40 := either (x 4) w39
  let w41 := both (x 17) w40
  let w42 := either (x 8) (x 1)
  let w43 := either (x 6) w42
  let w44 := either (x 5) w43
  let w45 := both (x 18) w44
  let w46 := either (x 9) (x 2)
  let w47 := either (x 7) w46
  let w48 := either (x 6) w47
  let w49 := both (x 19) w48
  let w50 := either (x 10) (x 3)
  let w51 := either (x 8) w50
  let w52 := either (x 7) w51
  let w53 := both (x 20) w52
  let w54 := either (x 11) (x 4)
  let w55 := either (x 9) w54
  let w56 := either (x 8) w55
  let w57 := both (x 21) w56
  let w58 := either (x 12) (x 5)
  let w59 := either (x 10) w58
  let w60 := either (x 9) w59
  let w61 := both (x 22) w60
  let w62 := either (x 0) (x 6)
  let w63 := either (x 11) w62
  let w64 := either (x 10) w63
  let w65 := both (x 23) w64
  let w66 := either (x 1) (x 7)
  let w67 := either (x 12) w66
  let w68 := either (x 11) w67
  let w69 := both (x 24) w68
  let w70 := either (x 2) (x 8)
  let w71 := either (x 0) w70
  let w72 := either (x 12) w71
  let w73 := both (x 25) w72
  let w74 := either w69 w73
  let w75 := either w65 w74
  let w76 := either w61 w75
  let w77 := either w57 w76
  let w78 := either w53 w77
  let w79 := either w49 w78
  let w80 := either w45 w79
  let w81 := either w41 w80
  let w82 := either w37 w81
  let w83 := either w33 w82
  let w84 := either w29 w83
  let w85 := either (x 3) (x 9)
  let w86 := either (x 1) w85
  let w87 := either (x 0) w86
  let w88 := either w84 w87
  let w89 := either w84 (x 13)
  let w90 := both w88 w89
  [w26,w27,w28,w29,w30,w31,w32,w33,w34,w35,w36,w37,w38,w39,w40,w41,w42,w43,w44,w45,w46,w47,w48,w49,w50,w51,w52,w53,w54,w55,w56,w57,w58,w59,w60,w61,w62,w63,w64,w65,w66,w67,w68,w69,w70,w71,w72,w73,w74,w75,w76,w77,w78,w79,w80,w81,w82,w83,w84,w85,w86,w87,w88,w89,w90]

private def reference (x : Row) (i : ℕ) : Bool :=
  if h : i < 26 then x ⟨i,h⟩ else (values x).getD (i-26) false

private theorem circuitSteps (x : Row) (j : Fin 65) :
    let g := circuit.gates[j.val]'(by exact j.isLt)
    (∀ i ∈ g.inputs, i < 26+j.val) ∧
      g.op.eval (g.inputs.map (reference x)) = reference x (26+j.val) := by
  fin_cases j <;> constructor
  all_goals first | decide +kernel | rfl

theorem operands (x : Row) :
    wireValue circuit 26 x 88 = either (remainder x) (touched x 0) ∧
    wireValue circuit 26 x 89 = either (remainder x) (x 13) := by
  have ss := simulate circuit.gates (List.ofFn x) (reference x)
    (by
      intro i hi
      have ok : i < 26 := by simpa only [List.length_ofFn] using hi
      rw [List.getD_eq_getElem _ _ hi,List.getElem_ofFn]
      simp [reference,ok])
    (by intro j; simp only [List.length_ofFn]; exact circuitSteps x ⟨j.val,j.isLt⟩)
  exact ⟨(ss 88 (by rw [List.length_ofFn]; decide +kernel)).trans rfl,(ss 89 (by rw [List.length_ofFn]; decide +kernel)).trans rfl⟩

theorem nearWitness :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (65 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (26 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Fin (26 : ℕ) → Bool), Maximal (fun (x8 : Fin (26 : ℕ) → Bool) => ¬x2 x8) x7 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x7 (if x7 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by
  refine ⟨circuit,64,88,89,by decide +kernel,valid.2.1,valid.2.2.1,rfl,rfl,?_,?_⟩
  · intro p l inc
    let row : Row := fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
    have yes : containsFlag row := ⟨p,l,inc,by simp [row],by simp [row]⟩
    have h := (flagSplit row).mp yes
    change wireValue circuit 26 row 88 = true ∧ wireValue circuit 26 row 89 = true
    rw [(operands row).1,(operands row).2]
    rcases h with h | ⟨hp,hl⟩ <;> simp_all [either,GateOp.eval]
  · intro x mx
    have no : ¬containsFlag x := mx.1
    have h := mt (flagSplit x).mpr no
    by_cases sel : x 13 = true
    · rw [ite_eq_left sel,(operands x).1]
      cases e : remainder x <;> cases f : touched x 0 <;> simp_all [either,GateOp.eval]
    · rw [ite_eq_right sel,(operands x).2]
      cases e : remainder x <;> cases f : x 13 <;> simp_all [either,GateOp.eval]


def mark (x : Row) (j : Fin 26) : Row := fun i => if i = j then true else x i

private theorem leMark (x : Row) (j : Fin 26) : x ≤ mark x j := by
  intro i
  by_cases h : i=j <;> simp [mark,h]

private theorem keepTrue {x y : Row} (le : x ≤ y) (i : Fin 26) (yes : x i = true) :
    y i = true := by
  cases e : y i with
  | true => rfl
  | false => have h := le i; rw [yes,e] at h; exact False.elim ((by decide : ¬ true ≤ false) h)

private theorem disjointPins : ∀ (p l : Fin 13), Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by decide +kernel
private theorem pin13 : ∀ l : Fin 13, Fin.natAdd 13 l = (13 : Fin 26) ↔ l=0 := by decide +kernel

def blocked (x : Row) := ∀ p : Fin 13, incident p 0 →
  ∃ l : Fin 13, incident p l ∧ x (Fin.natAdd 13 l) = true

private theorem markLine {x : Row} (no : ¬containsFlag x) (clear : touched x 0 = false) :
    ¬containsFlag (mark x 13) := by
  rintro ⟨p,l,inc,hp,hl⟩
  have oldp : x (Fin.castAdd 13 p) = true := by
    simpa [mark,show Fin.castAdd 13 p ≠ (13 : Fin 26) from disjointPins p 0] using hp
  by_cases hit : Fin.natAdd 13 l = (13 : Fin 26)
  · have z := (pin13 l).mp hit
    subst l
    have t := (touchedYes x 0).mpr ⟨p,inc,oldp⟩
    simp [clear] at t
  · exact no ⟨p,l,inc,oldp,by simpa only [mark,ite_eq_right hit] using hl⟩

theorem highExtension (x : Row) (no : ¬containsFlag x) :
    (∃ y : Row, x ≤ y ∧ Maximal (fun w => ¬containsFlag w) y ∧ y 13 = true) ↔
      touched x 0 = false := by
  constructor
  · rintro ⟨y,le,mx,high⟩
    cases t : touched x 0 with
    | false => rfl
    | true =>
      obtain ⟨p,inc,hp⟩ := (touchedYes x 0).mp t
      exact False.elim (mx.1 ⟨p,0,inc,keepTrue le _ hp,high⟩)
  · intro t
    obtain ⟨y,le,mx⟩ := Finite.exists_le_maximal (p := fun w : Row => ¬containsFlag w) (markLine no t)
    exact ⟨y,(leMark x 13).trans le,mx,keepTrue le 13 (by simp [mark])⟩

theorem lowExtension (x : Row) (no : ¬containsFlag x) :
    (∃ y : Row, x ≤ y ∧ Maximal (fun w => ¬containsFlag w) y ∧ y 13 = false) ↔
      x 13 = false ∧ ¬blocked x := by
  constructor
  · rintro ⟨y,le,mx,low⟩
    have lowx : x 13 = false := by
      cases e : x 13 with
      | false => rfl
      | true => have h := keepTrue le 13 e; simp [low] at h
    refine ⟨lowx,?_⟩
    intro occupied
    have somePoint : touched y 0 = true := by
      cases t : touched y 0 with
      | true => rfl
      | false =>
        have back := mx.2 (markLine mx.1 t) (leMark y 13)
        have h := keepTrue back 13 (by simp [mark])
        simp [low] at h
    obtain ⟨p,inc,hp⟩ := (touchedYes y 0).mp somePoint
    obtain ⟨l,il,hl⟩ := occupied p inc
    exact mx.1 ⟨p,l,il,hp,keepTrue le _ hl⟩
  · rintro ⟨_,free⟩
    unfold blocked at free
    push Not at free
    obtain ⟨p,on,clear⟩ := free
    let x' := mark x (Fin.castAdd 13 p)
    have no' : ¬containsFlag x' := by
      rintro ⟨q,l,inc,hq,hl⟩
      have oldl : x (Fin.natAdd 13 l) = true := by
        simpa only [x',mark,ite_eq_right (Ne.symm (disjointPins p l))] using hl
      by_cases same : q = p
      · subst q
        exact clear l inc oldl
      · have diff : Fin.castAdd 13 q ≠ Fin.castAdd 13 p := by
          intro e; apply same; exact Fin.ext (congrArg (fun i : Fin 26 => i.val) e)
        exact no ⟨q,l,inc,by simpa [x',mark,diff] using hq,oldl⟩
    obtain ⟨y,le,mx⟩ := Finite.exists_le_maximal (p := fun w : Row => ¬containsFlag w) no'
    have hp : y (Fin.castAdd 13 p) = true := keepTrue le _ (by simp [x',mark])
    refine ⟨y,(leMark _ _).trans le,mx,?_⟩
    cases e : y 13 with
    | false => rfl
    | true => exact False.elim (mx.1 ⟨p,0,on,hp,e⟩)


/-- A route on a column forcing three rows to the same raw vertex selects
exactly one occurrence of that vertex for each of the three rows. -/
def hits (mask test : ℕ) : Bool :=
  let v := mask &&& test
  v == 1 || v == 2 || v == 4

def triple (a b c : ℕ) : Bool := (List.range 8).any fun t => hits a t && hits b t && hits c t
def contained (a b : ℕ) : Bool := a &&& b == a

def dominated (masks : List ℕ) : ℕ :=
  (List.range masks.length).countP fun i => (List.range masks.length).any fun j =>
    j != i && contained (masks.getD j 0) (masks.getD i 0)

def fourTests (a b c d : ℕ) : Bool :=
  triple a b c && triple a b d && triple a c d && triple b c d

set_option maxHeartbeats 1000000 in
theorem fourThree : ∀ a b c d : Fin 8, a ≤ b → b ≤ c → c ≤ d →
    fourTests a b c d = true → 2 ≤ dominated [a,b,c,d] := by decide +kernel

theorem fourTwo : ∀ a b c d : Fin 4, a ≤ b → b ≤ c → c ≤ d →
    fourTests a b c d = true → 3 ≤ dominated [a,b,c,d] := by decide +kernel

theorem threeTwo : ∀ a b c : Fin 4, a ≤ b → b ≤ c →
    triple a b c = true → 2 ≤ dominated [a,b,c] := by decide +kernel


def rejectsSelected (a b : Row → Bool) : Prop :=
  ∀ y : Row, Maximal (fun x => ¬containsFlag x) y →
    (if y 13 then a y else b y) = false

theorem operandsUpper (a b : Row → Bool) (ma : Monotone a) (mb : Monotone b) :
    rejectsSelected a b ↔
      (∀ x, ¬containsFlag x → touched x 0 = false → a x = false) ∧
      (∀ x, ¬containsFlag x → x 13 = false → ¬blocked x → b x = false) := by
  constructor
  · intro ok
    constructor
    · intro x no empty
      obtain ⟨y,le,mx,ey⟩ := (highExtension x no).mpr empty
      have hy := ok y mx
      simp only [ey,ite_true] at hy
      cases hx : a x with
      | false => rfl
      | true => have h := ma le; rw [hx,hy] at h; exact False.elim ((by decide : ¬ true ≤ false) h)
    · intro x no low free
      obtain ⟨y,le,mx,ey⟩ := (lowExtension x no).mpr ⟨low,free⟩
      have hy := ok y mx
      simp only [ey,Bool.false_eq_true,ite_false] at hy
      cases hx : b x with
      | false => rfl
      | true => have h := mb le; rw [hx,hy] at h; exact False.elim ((by decide : ¬ true ≤ false) h)
  · rintro ⟨ha,hb⟩ y mx
    cases hy : y 13 with
    | true =>
      have t := (highExtension y mx.1).mp ⟨y,le_rfl,mx,hy⟩
      exact ha y mx.1 t
    | false =>
      have t := (lowExtension y mx.1).mp ⟨y,le_rfl,mx,hy⟩
      exact hb y mx.1 t.1 t.2

end PlaneSelectedRoot
