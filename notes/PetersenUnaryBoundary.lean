import PetersenUnaryInput
import PetersenFinalNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PetersenFreeOr PetersenSignedSlice PetersenUnaryInput

namespace PetersenUnaryBoundary

def unpack (r : ℕ) (i : Fin 10) := r.testBit i.val

def rows : List ℕ := [6,12,24,66,132,160,264,288,320,528,576,640,3,13,17,33,133,265,321,577,641,50,104,116,138,200,208,276,402,548,554,770,772,69,201,385,521,773]

def sample (j : Fin 38) := unpack (rows.getD j.val 0)

def below (x y : Input) := x 0 = y 0 ∧ ∀ i, x i = true → y i = true

instance (x y : Input) : Decidable (below x y) :=
  inferInstanceAs (Decidable (x 0 = y 0 ∧ ∀ i, x i = true → y i = true))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem geometry : ∀ r : Fin 1024,
    let x := unpack r.val
    (graph x = true → ∃ j : Fin 38, j.val < 21 ∧ below (sample j) x) ∧
    (graph x = false → ∃ j : Fin 38, 21 ≤ j.val ∧ below x (sample j)) := by decide +kernel

theorem rowLabels : ∀ j : Fin 38, graph (sample j) = decide (j.val < 21) := by decide +kernel

theorem represent (x : Input) : ∃ r : Fin 1024, unpack r.val = x := by
  let b := BitVec.ofBoolListLE (List.ofFn x)
  let r : Fin 1024 := ⟨b.toNat,by have h := b.isLt; simpa [b] using h⟩
  refine ⟨r,?_⟩
  funext i
  change b.getLsbD i.val = x i
  simp only [b,BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]

theorem sliceComplete (F : Input → Bool)
    (mono : ∀ x y, below x y → F x = true → F y = true) :
    (∀ j : Fin 38, F (sample j) = decide (j.val < 21)) ↔ F = graph := by
  constructor
  · intro pass
    funext x
    obtain ⟨r,eq⟩ := represent x
    have h := geometry r
    dsimp only at h
    rw [eq] at h
    cases hx : graph x with
    | true =>
      obtain ⟨j,hj,le⟩ := h.1 hx
      exact mono _ _ le (by simp [pass,hj])
    | false =>
      obtain ⟨j,hj,le⟩ := h.2 hx
      cases hf : F x with
      | false => rfl
      | true =>
        have impossible := mono _ _ le hf
        simp [pass,Nat.not_lt.mpr hj] at impossible
  · rintro rfl
    exact rowLabels

theorem physicalComplete (C : Circuit) (m : Monotone2 C) :
    (∀ j : Fin 38, C.eval (canonical (sample j)) = decide (j.val < 21)) ↔
      (fun x => C.eval (canonical x)) = graph := by
  apply sliceComplete (fun x => C.eval (canonical x))
  intro x y le yes
  have order : FinalNotWires.WireLE (canonical x) (canonical y) := by
    intro i hi
    by_cases inside : i < 10
    · rw [canonical,List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using inside),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using inside),
          List.getElem_ofFn] at hi ⊢
      exact le.2 ⟨i,inside⟩ hi
    · have hx : (List.ofFn x).length ≤ i := by simpa only [List.length_ofFn] using Nat.le_of_not_gt inside
      have hy : (List.ofFn y).length ≤ i := by simpa only [List.length_ofFn] using Nat.le_of_not_gt inside
      rw [canonical,List.getD_append_right _ _ _ _ hx,List.length_ofFn] at hi
      rw [canonical,List.getD_append_right _ _ _ _ hy,List.length_ofFn]
      simpa only [le.1] using hi
  exact FinalNotWires.fold_mono C.gates _ _ (fun g mem => (m g mem).1)
    (by simp [canonical]) order C.output yes

def pack {k : ℕ} (bits : Fin k → Bool) : ℕ := (BitVec.ofBoolListLE (List.ofFn bits)).toNat

theorem bitPack {k : ℕ} (bits : Fin k → Bool) (j : Fin k) :
    (pack bits).testBit j.val = bits j := by
  change (BitVec.ofBoolListLE (List.ofFn bits)).getLsbD j.val = bits j
  simp only [BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]

theorem bitOfRead (w : List ℕ) (i j : ℕ) :
    (w.getD i 0).testBit j = (w.map fun a => a.testBit j).getD i false := by
  simp only [List.getD,List.getElem?_map]
  cases w[i]? <;> simp

def signedWord (ones : ℕ) (w : List ℕ) (g : ℕ × ℕ) :=
  let a := w.getD g.1 0 &&& w.getD g.2 0
  w ++ [a, a ^^^ ones]

theorem signedFold (p : List (ℕ × ℕ)) (w : List ℕ) (o j ones : ℕ)
    (oneBit : ones.testBit j = true) :
    ((p.foldl (signedWord ones) w).getD o 0).testBit j =
      (p.foldl addPair (w.map fun a => a.testBit j)).getD o false := by
  rw [bitOfRead]
  suffices h : (p.foldl (signedWord ones) w).map (fun a => a.testBit j) =
      p.foldl addPair (w.map fun a => a.testBit j) by rw [h]
  induction p generalizing w with
  | nil => rfl
  | cons g tail ih =>
    simp only [List.foldl_cons,ih]
    congr 1
    simp only [signedWord,addPair,List.map_append,List.map_cons,List.map_nil,
      Nat.testBit_xor,Nat.testBit_and,bitOfRead,oneBit,Bool.xor_true]

def signedStart : List ℕ :=
  List.ofFn fun i : Fin 22 => pack fun j : Fin 1024 => (initial (unpack j.val)).getD i.val false

theorem startBits (r : Fin 1024) :
    signedStart.map (fun a => a.testBit r.val) = initial (unpack r.val) := by
  apply List.ext_getElem
  · simp [signedStart,initial]
  · intro i l h
    have hi : i < 22 := by simpa only [signedStart,List.length_map,List.length_ofFn] using l
    simp only [signedStart,List.getElem_map,List.getElem_ofFn,bitPack]
    rw [List.getD_eq_getElem _ _ h]

def signedOnes := pack fun _ : Fin 1024 => true
def signedTarget := pack fun r : Fin 1024 => graph (unpack r.val)

theorem signedFromWords
    (exclude : ∀ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ 17 →
      (p.foldl (signedWord signedOnes) signedStart).getD o 0 ≠ signedTarget)
    (p : List (ℕ × ℕ)) (o : ℕ) (small : p.length ≤ 17) :
    ∃ x : Input, (p.foldl addPair (initial x)).getD o false ≠ graph x := by
  by_contra! yes
  apply exclude p o small
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 1024
  · let r : Fin 1024 := ⟨i,hi⟩
    rw [signedFold p signedStart o i signedOnes (bitPack _ r)]
    change (p.foldl addPair (signedStart.map (fun a => a.testBit r.val))).getD o false =
      signedTarget.testBit r.val
    rw [startBits,signedTarget,bitPack,yes]
  · have allOff : ∀ a ∈ signedStart, a.testBit i = false := by
      intro a mem
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp mem
      change (BitVec.ofBoolListLE _).getLsbD _ = _
      rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]
    have off (bits : Fin 1024 → Bool) : (pack bits).testBit i = false := by
      change (BitVec.ofBoolListLE _).getLsbD _ = _
      rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]
    have finalOff (xs : List (ℕ × ℕ)) (w : List ℕ)
        (ok : ∀ a ∈ w, a.testBit i = false) :
        ∀ a ∈ xs.foldl (signedWord signedOnes) w, a.testBit i = false := by
      induction xs generalizing w with
      | nil => exact ok
      | cons g rest ih =>
        apply ih
        intro a mem
        rcases List.mem_append.mp mem with h | h
        · exact ok a h
        · have zero (k : ℕ) : (w.getD k 0).testBit i = false := by
            by_cases l : k < w.length
            · rw [List.getD_eq_getElem _ _ l]
              exact ok _ (List.getElem_mem l)
            · rw [List.getD_eq_default _ _ (by omega)]
              simp
          simp only [List.mem_cons,List.not_mem_nil,or_false] at h
          rcases h with rfl | rfl <;> simp only [Nat.testBit_and,Nat.testBit_xor,zero,signedOnes,off] <;> rfl
    rw [show signedTarget.testBit i = false from off _]
    by_cases l : o < (p.foldl (signedWord signedOnes) signedStart).length
    · rw [List.getD_eq_getElem _ _ l]
      exact finalOff p signedStart allOff _ (List.getElem_mem l)
    · rw [List.getD_eq_default _ _ (by omega)]
      simp


abbrev MonoOp := Bool × Option ℕ × Option ℕ

def monoOnes := pack fun _ : Fin 38 => true

def pin (w : List ℕ) (unit : ℕ) (o : Option ℕ) : ℕ :=
  match o with
  | none => unit
  | some i => w.getD i 0

def monoWord (w : List ℕ) (g : MonoOp) : List ℕ :=
  let a := pin w (if g.1 then 0 else monoOnes) g.2.1
  let b := pin w (if g.1 then 0 else monoOnes) g.2.2
  w ++ [if g.1 then a ||| b else a &&& b]

def monoCode (g : Gate) : MonoOp :=
  (g.op.eval [true,false], g.inputs[0]?, g.inputs[1]?)

theorem monoGate (w : List ℕ) (g : Gate) (j : Fin 38)
    (kind : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2) :
    (monoWord w (monoCode g)).map (fun a => a.testBit j.val) =
      FinalNotWires.step (w.map fun a => a.testBit j.val) g := by
  have one : monoOnes.testBit j.val = true := bitPack _ j
  have shapes : g.inputs = [] ∨ (∃ a, g.inputs = [a]) ∨ ∃ a b, g.inputs = [a,b] := by
    cases h : g.inputs with
    | nil => exact Or.inl rfl
    | cons a l =>
      cases l with
      | nil => exact Or.inr (Or.inl ⟨a,rfl⟩)
      | cons b t =>
        have sz := h ▸ arity
        have ht : t = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at sz; omega)
        exact Or.inr (Or.inr ⟨a,b,by rw [ht]⟩)
  rcases shapes with inputs | ⟨a,inputs⟩ | ⟨a,b,inputs⟩ <;>
    rcases kind with op | op <;>
    simp only [monoWord,monoCode,FinalNotWires.step,op,inputs,GateOp.eval,List.map_append,
      List.map_cons,List.map_nil,List.all_cons,List.all_nil,List.any_cons,List.any_nil,
      id_eq,Bool.and_true,Bool.or_false,Bool.and_false,
      List.getElem?_cons_zero,List.getElem?_nil,List.getElem?_cons_succ,pin,
      Bool.false_eq_true,ite_false,ite_true,Nat.testBit_and,Nat.testBit_or,one,
      Nat.zero_testBit,bitOfRead]

theorem monoFold (gs : List Gate)
    (m : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (w : List ℕ) (j : Fin 38) :
    ((gs.map monoCode).foldl monoWord w).map (fun a => a.testBit j.val) =
      gs.foldl FinalNotWires.step (w.map fun a => a.testBit j.val) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [ih (fun k hk => m k (List.mem_cons_of_mem _ hk))]
    rw [monoGate w g j (m g (by simp)).1 (m g (by simp)).2]

def monoStart : List ℕ :=
  List.ofFn fun i : Fin 13 => pack fun r : Fin 38 => (canonical (sample r)).getD i.val false

theorem monoStartBits (r : Fin 38) :
    monoStart.map (fun a => a.testBit r.val) = canonical (sample r) := by
  apply List.ext_getElem
  · simp [monoStart,canonical]
  · intro i l h
    simp only [monoStart,List.getElem_map,List.getElem_ofFn,bitPack]
    rw [List.getD_eq_getElem _ _ h]

def monoTarget := pack fun j : Fin 38 => decide (j.val < 21)

theorem printedMonoData :
    monoStart = [266290065408,3508539401,151003406355,87027753030,480264708,1625325728,
      25883837704,51926599728,178644189632,214213070336,8587841535,0,274877906943] ∧
    monoTarget = 2097151 := by decide +kernel

theorem positiveFromWords
    (exclude : ∀ (p : List MonoOp) (o : ℕ), p.length ≤ 18 →
      pack (fun r : Fin 38 => ((p.foldl monoWord monoStart).getD o 0).testBit r.val) ≠ monoTarget)
    (C : Circuit) (m : Monotone2 C) (small : C.size ≤ 18) :
    ∃ x : Input, C.eval (canonical x) ≠ graph x := by
  by_contra! all
  have pass := (physicalComplete C m).mpr (funext all)
  apply exclude (C.gates.map monoCode) C.output (by simpa [Circuit.size] using small)
  apply congrArg pack
  funext r
  rw [bitOfRead,monoFold C.gates m,monoStartBits]
  exact pass r


/-- Every invalid read returns zero, so one sentinel suffices for all large indices. -/
def clamp (cap i : ℕ) : Fin (cap + 1) := ⟨min cap i, by omega⟩

theorem readClamp (w : List ℕ) (cap i : ℕ) (short : w.length ≤ cap) :
    w.getD (clamp cap i).val 0 = w.getD i 0 := by
  by_cases ok : i ≤ cap
  · simp [clamp,Nat.min_eq_right ok]
  · rw [List.getD_eq_default _ _ (show w.length ≤ (clamp cap i).val by
          change w.length ≤ min cap i; omega),
        List.getD_eq_default _ _ (by omega)]

abbrev SignedInstruction := Fin 57 × Fin 57
abbrev PositiveInstruction := Bool × Option (Fin 32) × Option (Fin 32)

def limitS (g : ℕ × ℕ) : SignedInstruction := (clamp 56 g.1,clamp 56 g.2)
def widenS (g : SignedInstruction) : ℕ × ℕ := (g.1.val,g.2.val)
def limitM (g : MonoOp) : PositiveInstruction :=
  (g.1,g.2.1.map (clamp 31),g.2.2.map (clamp 31))
def widenM (g : PositiveInstruction) : MonoOp :=
  (g.1,g.2.1.map Fin.val,g.2.2.map Fin.val)

private theorem limitSigned (p : List (ℕ × ℕ)) (w : List ℕ)
    (short : w.length + 2*p.length ≤ 56) :
    (p.map limitS).foldl (fun v g => signedWord signedOnes v (widenS g)) w =
      p.foldl (signedWord signedOnes) w := by
  induction p generalizing w with
  | nil => rfl
  | cons g t ih =>
    simp only [List.length_cons] at short
    simp only [List.map_cons,List.foldl_cons]
    have same : signedWord signedOnes w (widenS (limitS g)) = signedWord signedOnes w g := by
      simp only [signedWord,widenS,limitS,readClamp _ _ _ (by omega : w.length ≤ 56)]
    rw [same]
    apply ih
    simp only [signedWord,List.length_append,List.length_cons,List.length_nil]
    omega

private theorem limitPositive (p : List MonoOp) (w : List ℕ)
    (short : w.length + p.length ≤ 31) :
    (p.map limitM).foldl (fun v g => monoWord v (widenM g)) w =
      p.foldl monoWord w := by
  induction p generalizing w with
  | nil => rfl
  | cons g t ih =>
    simp only [List.length_cons] at short
    simp only [List.map_cons,List.foldl_cons]
    have eqPin (o : Option ℕ) (u : ℕ) :
        pin w u ((o.map (clamp 31)).map Fin.val) = pin w u o := by
      cases o with
      | none => rfl
      | some i => exact readClamp _ _ _ (by omega)
    have same : monoWord w (widenM (limitM g)) = monoWord w g := by
      simp only [monoWord,widenM,limitM,eqPin]
      rfl
    rw [same]
    apply ih
    simp only [monoWord,List.length_append,List.length_cons,List.length_nil]
    omega

/-- The two obligations quantify only over finite types, including gate counts and outputs. -/
def SignedExclusion := ∀ (n : Fin 18) (p : Fin n.val → SignedInstruction) (o : Fin 57),
    ((List.ofFn p).foldl (fun w g => signedWord signedOnes w (widenS g)) signedStart).getD
      o.val 0 ≠ signedTarget

def PositiveExclusion := ∀ (n : Fin 19) (p : Fin n.val → PositiveInstruction) (o : Fin 32),
    pack (fun r : Fin 38 => (((List.ofFn p).foldl (fun w g => monoWord w (widenM g))
      monoStart).getD o.val 0).testBit r.val) ≠ monoTarget

theorem liftSigned (h : SignedExclusion) (p : List (ℕ × ℕ)) (o : ℕ) (small : p.length ≤ 17) :
    (p.foldl (signedWord signedOnes) signedStart).getD o 0 ≠ signedTarget := by
  have lim := h ⟨p.length,by omega⟩ (fun i => limitS (p.get i)) (clamp 56 o)
  have tab : List.ofFn (fun i : Fin p.length => limitS (p.get i)) = p.map limitS := by
    change List.ofFn (limitS ∘ p.get) = _
    rw [← List.map_ofFn,List.ofFn_get]
  rw [tab,limitSigned p signedStart (by simp only [signedStart,List.length_ofFn]; omega)] at lim
  have len (q : List (ℕ × ℕ)) (w : List ℕ) :
      (q.foldl (signedWord signedOnes) w).length = w.length + 2*q.length := by
    induction q generalizing w with
    | nil => simp
    | cons g tail ih => simp [ih,signedWord]; omega
  rw [readClamp _ _ _ (by rw [len]; simp only [signedStart,List.length_ofFn]; omega)] at lim
  exact lim

theorem liftPositive (h : PositiveExclusion) (p : List MonoOp) (o : ℕ) (small : p.length ≤ 18) :
    pack (fun r : Fin 38 => ((p.foldl monoWord monoStart).getD o 0).testBit r.val) ≠ monoTarget := by
  have lim := h ⟨p.length,by omega⟩ (fun i => limitM (p.get i)) (clamp 31 o)
  have tab : List.ofFn (fun i : Fin p.length => limitM (p.get i)) = p.map limitM := by
    change List.ofFn (limitM ∘ p.get) = _
    rw [← List.map_ofFn,List.ofFn_get]
  rw [tab,limitPositive p monoStart (by simp only [monoStart,List.length_ofFn]; omega)] at lim
  have len (q : List MonoOp) (w : List ℕ) : (q.foldl monoWord w).length = w.length + q.length := by
    induction q generalizing w with
    | nil => simp
    | cons g tail ih => simp [ih,monoWord]; omega
  rw [readClamp _ _ _ (by rw [len]; simp only [monoStart,List.length_ofFn]; omega)] at lim
  exact lim

theorem resultFromFiniteChecks (s : SignedExclusion) (m : PositiveExclusion)
    (C : Circuit) (w : Fin 10 → Fin 10) (f : Bool → Bool) (legal : FanInTwo C) (small : C.size ≤ 18) :
    ∃ x : Input, C.eval (List.ofFn (x ∘ w) ++ [f (x 0)]) ≠ graph x :=
  deskFromSearches (signedFromWords (liftSigned s)) (positiveFromWords (liftPositive m))
    C w f legal small

end PetersenUnaryBoundary
