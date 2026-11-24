import PetersenSignedSlice

open PetersenSignedSlice
namespace PetersenFirstSignedCut

abbrev Gate := ℕ × ℕ
abbrev Program := List Gate
abbrev S (α : Type) := α → Bool
def zero {α : Type} : S α := fun _ => false
def val {α : Type} (w : List (S α)) (g : Gate) : S α :=
  meet (w.getD g.1 zero) (w.getD g.2 zero)
def st {α : Type} (w : List (S α)) (g : Gate) := w ++ [val w g,inv (val w g)]
def Bi {α : Type} (t : List (S α)) (f : S α) := f ∈ t ∧ inv f ∈ t
def Can {α : Type} (initial : List (S α)) (n : ℕ) (f : S α) : Prop :=
  ∃ (p : Program) (o : ℕ), p.length ≤ n ∧ ∀ x : α,
    (p.foldl addPair (initial.map fun u => u x)).getD o false = f x

theorem biNeg {α} {t : List (S α)} {f} (h : Bi t f) : Bi t (inv f) := by
  refine ⟨h.2,?_⟩
  have eq : inv (inv f) = f := by funext x; simp [inv]
  rw [eq]
  exact h.1

theorem biKeep {α} {s t : List (S α)} {k} (r : Run s k t) {f} (h : Bi s f) :
    Bi t f := ⟨r.keep _ h.1,r.keep _ h.2⟩

theorem biGate {α} {t : List (S α)} {a b} (ha : Bi t a) (hb : Bi t b) :
    ∃ u, Run t 1 u ∧ Bi u (meet a b) := by
  refine ⟨_,Run.gate Run.nil ha.1 hb.1,?_⟩
  exact ⟨List.mem_append_right _ (by simp),List.mem_append_right _ (by simp)⟩

theorem canOfRun {α} {s t : List (S α)} {k n f} (r : Run s k t) (le : k≤n) (mem : f ∈ t) : Can s n f := by
  obtain ⟨p,len,sim⟩ := r.program
  obtain ⟨o,ho,eo⟩ := List.getElem_of_mem mem
  refine ⟨p,o,len ▸ le,?_⟩
  intro x
  rw [sim,List.getD_eq_getElem _ _ (by simpa using ho),List.getElem_map,eo]

theorem getAt {α} (w : List (S α)) (i : ℕ) (x : α) :
    w.getD i zero x = (w.map fun u => u x).getD i false := by
  simp only [List.getD,List.getElem?_map]
  cases w[i]? <;> rfl

theorem values {α} (p : Program) (w : List (S α)) (x : α) :
    (p.foldl st w).map (fun u => u x) = p.foldl addPair (w.map fun u => u x) := by
  induction p generalizing w with
  | nil => rfl
  | cons g p ih =>
    simp only [List.foldl_cons,ih]
    congr 1
    simp only [st,addPair,val,List.map_append,List.map_cons,List.map_nil,meet,inv,getAt]

def Live {α : Type} (ok : ℕ → Prop) (t w : List (S α)) := ∀ i, ok i → Bi t (w.getD i zero)

theorem extend {α} {ok : ℕ → Prop} {t w : List (S α)} {f} (base : Bi t zero)
    (old : Live ok t w) (fresh : Bi t f) : Live ok t (w ++ [f,inv f]) := by
  intro i hi
  by_cases small : i < w.length
  · rw [List.getD_append _ _ _ _ small]
    exact old _ hi
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    cases h : i-w.length with
    | zero => exact fresh
    | succ j =>
      cases j with
      | zero => exact biNeg fresh
      | succ j => exact base

theorem build {α} (w₀ : List (S α)) (p : Program) (ok : ℕ → Prop) (price : Gate → ℕ)
    (rule : ∀ g ∈ p, ∀ (pre t : List (S α)), Bi t zero → Live ok t (w₀++pre) →
      ∃ d u, Run t d u ∧ d ≤ price g ∧ Bi u (val (w₀++pre) g))
    (pre t : List (S α)) (base : Bi t zero) (old : Live ok t (w₀++pre)) :
    ∃ k u, Run t k u ∧ k ≤ (p.map price).sum ∧ Live ok u (p.foldl st (w₀++pre)) := by
  induction p generalizing pre t with
  | nil => exact ⟨0,t,Run.nil,by simp,old⟩
  | cons g p ih =>
    obtain ⟨d,v,r,cap,hg⟩ := rule g (by simp) pre t base old
    let f := val (w₀++pre) g
    have keep : Live ok v (w₀++pre) := fun i hi => biKeep r (old i hi)
    have stepGood := extend (biKeep r base) keep hg
    obtain ⟨k,u,tail,sz,live⟩ := ih (fun z hz => rule z (List.mem_cons_of_mem g hz))
      (pre++[f,inv f]) v (biKeep r base) (by simpa only [List.append_assoc] using stepGood)
    refine ⟨d+k,u,r.comp tail,by simpa using Nat.add_le_add cap sz,?_⟩
    simpa only [List.foldl_cons,st,List.append_assoc] using live

abbrev Bits := Fin 9 → Bool
def raw (i : Fin 9) : S Bits := fun x => x i
def seed (j : Fin 9) : S Bits := meet (raw 0) (inv (raw j))
def pool : List (S Bits) := [zero,inv zero] ++ List.ofFn raw ++ (List.ofFn raw).map inv
def start (j : Fin 9) : List (S Bits) := pool ++ [seed j,inv (seed j)]
def off (x : Bits) : Bits := Function.update x 0 false

theorem poolAt (x : Bits) : pool.map (fun u => u x) =
    [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not := by
  simp only [pool,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
  rfl

theorem startAt (j : Fin 9) (x : Bits) : (start j).map (fun u => u x) =
    ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not) ++ [x 0 && !(x j),!(x 0 && !(x j))] := by
  simp only [start,List.map_append,List.map_cons,List.map_nil,poolAt]
  rfl

theorem poolZero : Bi pool zero :=
  ⟨by simp [pool],by simp [pool]⟩

theorem poolRaw (i : Fin 9) : Bi pool (raw i) := by
  have pos : raw i ∈ List.ofFn raw := List.mem_ofFn.mpr ⟨i,rfl⟩
  exact ⟨List.mem_append_left _ (List.mem_append_right _ pos),List.mem_append_right _ (List.mem_map_of_mem pos)⟩

def extra (i : ℕ) := i=20 ∨ i=21
def axis (i : ℕ) := i=2 ∨ i=11
def marked (i : ℕ) := extra i ∨ axis i
instance (i : ℕ) : Decidable (extra i) := inferInstanceAs (Decidable (i=20 ∨ i=21))
instance (i : ℕ) : Decidable (axis i) := inferInstanceAs (Decidable (i=2 ∨ i=11))
instance (i : ℕ) : Decidable (marked i) := inferInstanceAs (Decidable (extra i ∨ axis i))
def touches (s : ℕ → Prop) (g : Gate) := s g.1 ∨ s g.2
instance (s : ℕ → Prop) [DecidablePred s] (g : Gate) : Decidable (touches s g) :=
  inferInstanceAs (Decidable (s g.1 ∨ s g.2))

theorem rawStart (j : Fin 9) : Live (fun i => ¬ extra i) pool (start j) := by
  intro i hi
  by_cases small : i < 22
  · interval_cases i <;> first | exact poolZero | exact biNeg poolZero | exact poolRaw _ | exact biNeg (poolRaw _) | exact False.elim (hi (by decide))
  · rw [List.getD_eq_default _ _ (by change 22 ≤ i; omega)]
    exact poolZero

def sliced (j : Fin 9) : List (S Bits) := (start j).map (fun u x => u (off x))

theorem slicedStart (j : Fin 9) : Live (fun _ => True) pool (sliced j) := by
  intro i _
  by_cases small : i < 22
  · interval_cases i <;> first | exact poolZero | exact biNeg poolZero | exact poolRaw _ | exact biNeg (poolRaw _)
  · rw [List.getD_eq_default _ _ (by change 22 ≤ i; omega)]
    exact poolZero

theorem sliceConst (j : Fin 9) (pre : List (S Bits)) (i : ℕ) (h : marked i) :
    ((sliced j++pre).getD i zero = zero) ∨ ((sliced j++pre).getD i zero = inv zero) := by
  rcases h with (rfl | rfl) | (rfl | rfl) <;>
    rw [List.getD_append _ _ _ _ (by change _ < 22; decide)] <;>
    first | left; rfl | right; rfl | (left; funext x; simp [sliced,start,seed,off,raw,meet,inv,Function.update,zero,List.getD]) |
      (right; funext x; simp [sliced,start,seed,off,raw,meet,inv,Function.update,zero,List.getD])

theorem slicedRun {j : Fin 9} {p : Program} :
    ∃ k t, Run pool k t ∧ k ≤ (p.map fun g => ite (touches marked g) 0 1).sum ∧
      Live (fun _ => True) t (p.foldl st (sliced j)) := by
  apply build (sliced j) p (fun _ => True) (fun g => ite (touches marked g) 0 1) _ [] pool poolZero (slicedStart j)
  intro g _ pre t base old
  by_cases h : touches marked g
  · refine ⟨0,t,Run.nil,by simp [h],?_⟩
    have ha := old g.1 trivial
    have hb := old g.2 trivial
    change Bi t (meet _ _)
    rcases h with left | right
    · rcases sliceConst j pre _ left with e | e
      · simpa only [e] using (show Bi t (meet zero ((sliced j++pre).getD g.2 zero)) from base)
      · rw [e]
        change Bi t (fun x => true && _)
        simpa only [Bool.true_and] using hb
    · rcases sliceConst j pre _ right with e | e
      · rw [e]
        have z : meet ((sliced j++pre).getD g.1 zero) zero = zero := by funext x; simp [meet,zero]
        rw [z]; exact base
      · rw [e]
        have z : meet ((sliced j++pre).getD g.1 zero) (inv zero) = (sliced j++pre).getD g.1 zero := by funext x; simp [meet,zero,inv]
        rw [z]; exact ha
  · obtain ⟨u,r,fresh⟩ := biGate (old g.1 trivial) (old g.2 trivial)
    exact ⟨1,u,r,by simp [h],fresh⟩

theorem jointValue (j : Fin 9) (pre : List (S Bits)) (g : Gate) (he : touches extra g) (ha : touches axis g) :
    val (start j++pre) g = zero ∨ val (start j++pre) g = inv (raw 0) ∨
    val (start j++pre) g = meet (raw 0) (raw j) ∨ val (start j++pre) g = seed j := by
  obtain ⟨a,b⟩ := g
  simp only [touches,extra,axis] at he ha
  have e2 : (start j++pre).getD 2 zero = raw 0 := by rw [List.getD_append _ _ _ _ (by change 2<22; decide)]; rfl
  have e11 : (start j++pre).getD 11 zero = inv (raw 0) := by rw [List.getD_append _ _ _ _ (by change 11<22; decide)]; rfl
  have e20 : (start j++pre).getD 20 zero = seed j := by rw [List.getD_append _ _ _ _ (by change 20<22; decide)]; rfl
  have e21 : (start j++pre).getD 21 zero = inv (seed j) := by rw [List.getD_append _ _ _ _ (by change 21<22; decide)]; rfl
  have positions : (a=2 ∧ b=20) ∨ (a=2 ∧ b=21) ∨ (a=11 ∧ b=20) ∨ (a=11 ∧ b=21) ∨ (a=20 ∧ b=2) ∨ (a=21 ∧ b=2) ∨ (a=20 ∧ b=11) ∨ (a=21 ∧ b=11) := by omega
  rcases positions with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · right; right; right
    funext x
    simp only [val,e2,e11,e20,e21,seed,raw,inv,meet,zero]
    cases x 0 <;> cases x j <;> rfl
  · right; right; left
    funext x
    simp only [val,e2,e11,e20,e21,seed,raw,inv,meet,zero]
    cases x 0 <;> cases x j <;> rfl
  · left
    funext x
    simp only [val,e2,e11,e20,e21,seed,raw,inv,meet,zero]
    cases x 0 <;> cases x j <;> rfl
  · right; left
    funext x
    simp only [val,e2,e11,e20,e21,seed,raw,inv,meet,zero]
    cases x 0 <;> cases x j <;> rfl
  · right; right; right
    funext x
    simp only [val,e2,e11,e20,e21,seed,raw,inv,meet,zero]
    cases x 0 <;> cases x j <;> rfl
  · right; right; left
    funext x
    simp only [val,e2,e11,e20,e21,seed,raw,inv,meet,zero]
    cases x 0 <;> cases x j <;> rfl
  · left
    funext x
    simp only [val,e2,e11,e20,e21,seed,raw,inv,meet,zero]
    cases x 0 <;> cases x j <;> rfl
  · right; left
    funext x
    simp only [val,e2,e11,e20,e21,seed,raw,inv,meet,zero]
    cases x 0 <;> cases x j <;> rfl

theorem rawRun {j : Fin 9} {p : Program} (joint : ∀ g ∈ p, touches extra g → touches axis g) :
    ∃ k t, Run pool k t ∧ k ≤ p.length ∧ Live (fun i => ¬extra i) t (p.foldl st (start j)) := by
  have make : ∀ g ∈ p, ∀ (pre t : List (S Bits)), Bi t zero → Live (fun i => ¬extra i) t (start j++pre) →
      ∃ d u, Run t d u ∧ d ≤ (1 : ℕ) ∧ Bi u (val (start j++pre) g) := by
    intro g hg pre t base old
    by_cases he : touches extra g
    · have rawGood (i : Fin 9) : Bi t (raw i) := by
        have good := old (2+i.val) (by dsimp [extra]; omega)
        rw [List.getD_append _ _ _ _ (by change 2+i.val < 22; omega)] at good
        fin_cases i <;> exact good
      rcases jointValue j pre g he (joint g hg he) with e | e | e | e
      · exact ⟨0,t,Run.nil,by decide,e.symm ▸ base⟩
      · exact ⟨0,t,Run.nil,by decide,e.symm ▸ biNeg (rawGood 0)⟩
      · obtain ⟨u,r,ok⟩ := biGate (rawGood 0) (rawGood j)
        exact ⟨1,u,r,le_rfl,e.symm ▸ ok⟩
      · obtain ⟨u,r,ok⟩ := biGate (rawGood 0) (biNeg (rawGood j))
        rw [e]
        exact ⟨1,u,r,le_rfl,ok⟩
    · obtain ⟨u,r,ok⟩ := biGate (old g.1 (fun h => he (Or.inl h))) (old g.2 (fun h => he (Or.inr h)))
      exact ⟨1,u,r,le_rfl,ok⟩
  obtain ⟨k,t,r,le,good⟩ := build (start j) p (fun i => ¬extra i) (fun _ => 1) make [] pool poolZero (rawStart j)
  exact ⟨k,t,r,by simpa using le,good⟩

theorem retainsInputs {α} (p : Program) (w : List (S α)) : ∃ tail, p.foldl st w = w++tail := by
  induction p generalizing w with
  | nil => exact ⟨[],by simp⟩
  | cons g p ih =>
    obtain ⟨t,eq⟩ := ih (st w g)
    exact ⟨[val w g,inv (val w g)]++t,by simpa only [List.foldl_cons,st,List.append_assoc] using eq⟩

theorem original {α} (p : Program) (w : List (S α)) (i : ℕ) (hi : i<w.length) :
    (p.foldl st w).getD i zero = w.getD i zero := by
  obtain ⟨tail,e⟩ := retainsInputs p w
  rw [e,List.getD_append _ _ _ _ hi]

theorem equalOff {α} (p : Program) (w : List (S α)) (a b : α) (m : ℕ → Prop)
    (init : ∀ i, ¬m i → w.getD i zero a = w.getD i zero b)
    (avoids : ∀ g ∈ p, ¬touches m g) :
    ∀ i, ¬m i → (p.foldl st w).getD i zero a = (p.foldl st w).getD i zero b := by
  induction p generalizing w with
  | nil => exact init
  | cons g p ih =>
    apply ih (st w g) _ (fun k hk => avoids k (List.mem_cons_of_mem _ hk))
    intro i good
    have gateEq : val w g a = val w g b := by
      simp only [val,meet,init g.1 (fun h => avoids _ (by simp) (Or.inl h)),init g.2 (fun h => avoids _ (by simp) (Or.inr h))]
    by_cases small : i<w.length
    · rw [st,List.getD_append _ _ _ _ small]
      exact init i good
    · rw [st,List.getD_append_right _ _ _ _ (by omega)]
      cases eq : i-w.length with
      | zero => exact gateEq
      | succ k =>
        cases k with
        | zero => exact congrArg Bool.not gateEq
        | succ k => rfl

theorem startEqual (j : Fin 9) (x : Bits) (nz : j ≠ 0) (bit : x j = true) :
    ∀ i, ¬axis i → (start j).getD i zero (off x) =
      (start j).getD i zero (Function.update x 0 true) := by
  intro i h
  by_cases small : i<22
  · interval_cases i <;> first | exact False.elim (h (by decide)) | rfl |
      simp [start,seed,pool,raw,zero,meet,inv,off,Function.update,nz,bit,List.getD]
  · rw [List.getD_eq_default _ _ (by change 22 ≤ i; omega)]
    rfl

theorem saved (p : Program) (g k : Gate) (hg : g ∈ p) (hk : k ∈ p) (distinct : g ≠ k)
    (gm : touches marked g) (km : touches marked k) :
    (p.map fun h => ite (touches marked h) 0 1).sum ≤ p.length-2 := by
  let drop := fun z : Gate => decide (touches marked z)
  have count (l : Program) : (l.map fun h => ite (touches marked h) 0 1).sum + (l.filter drop).length = l.length := by
    induction l with
    | nil => rfl
    | cons z l ih =>
      by_cases h : touches marked z <;> simp [List.filter_cons,drop,h] at * <;> omega
  have gm' : g ∈ p.filter drop := List.mem_filter.mpr ⟨hg,by simpa [drop] using gm⟩
  have km' : k ∈ p.filter drop := List.mem_filter.mpr ⟨hk,by simpa [drop] using km⟩
  have two : 2 ≤ (p.filter drop).length := by
    generalize eq : p.filter drop = l at gm' km' ⊢
    cases l with
    | nil => simp at gm'
    | cons h t =>
      cases t with
      | nil => simp only [List.mem_singleton] at gm' km'; exact False.elim (distinct (gm'.trans km'.symm))
      | cons z t => simp
  have total := count p
  omega

theorem split : ∀ (j : Fin 9) (f : (Fin 9 → Bool) → Bool) (m : ℕ),
      let raw := fun x : Fin 9 → Bool => [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not
      let can := fun (s : (Fin 9 → Bool) → List Bool) (n : ℕ) (h : (Fin 9 → Bool) → Bool) =>
        ∃ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ n ∧ ∀ x : Fin 9 → Bool,
          (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
            w ++ [z,!z]) (s x)).getD o false = h x
      (∃ x : Fin 9 → Bool, j ≠ 0 ∧ x j = true ∧ f (Function.update x 0 false) ≠ f (Function.update x 0 true)) →
      can (fun x => raw x ++ [x 0 && !(x j),!(x 0 && !(x j))]) m f →
      can raw m f ∨ can raw (m-2) (fun x => f (Function.update x 0 false)) := by
  intro j f m
  dsimp only
  rintro ⟨x,nz,bit,diff⟩ ⟨p,o,len,hit⟩
  have output (y : Bits) : (p.foldl st (start j)).getD o zero y = f y := by
    rw [getAt,values,startAt]
    exact hit y
  have makeRaw (ok : Can pool m f) : ∃ (q : Program) (k : ℕ), q.length ≤ m ∧ ∀ y : Bits,
      (q.foldl addPair ([false,true] ++ List.ofFn y ++ (List.ofFn y).map Bool.not)).getD k false = f y := by
    obtain ⟨q,k,small,sim⟩ := ok
    exact ⟨q,k,small,fun y => (poolAt y) ▸ sim y⟩
  by_cases solo : axis o
  · left
    apply makeRaw
    have member : Bi pool ((p.foldl st (start j)).getD o zero) := by
      rcases solo with rfl | rfl <;> rw [original _ _ _ (by change _<22; decide)] <;>
        first | exact poolRaw 0 | exact biNeg (poolRaw 0)
    have eq : (p.foldl st (start j)).getD o zero = f := funext output
    exact canOfRun Run.nil (Nat.zero_le _) (eq ▸ member.1)
  have firstUse : ∃ k ∈ p, touches axis k := by
    by_contra! avoided
    exact diff ((output _).symm.trans ((equalOff p (start j) (off x) (Function.update x 0 true) axis (startEqual j x nz bit) avoided o solo).trans (output _)))
  have outOK : ¬extra o := by
    intro forbidden
    have eq : (p.foldl st (start j)).getD o zero = (start j).getD o zero := by
      apply original
      rcases forbidden with rfl | rfl <;> change _<22 <;> decide
    exact diff ((output _).symm.trans (by rw [eq]; exact (startEqual j x nz bit o solo).trans (by rw [← eq]; exact output _)))
  by_cases joint : ∀ g ∈ p, touches extra g → touches axis g
  · left; apply makeRaw
    obtain ⟨k,t,r,small,ok⟩ := rawRun (j:=j) joint
    have eq : (p.foldl st (start j)).getD o zero = f := funext output
    exact canOfRun r (small.trans len) (eq ▸ (ok o outOK).1)
  · right
    push_neg at joint
    obtain ⟨g,hg,ge,ga⟩ := joint
    obtain ⟨k,hk,ka⟩ := firstUse
    have gm : touches marked g := ge.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inl h))
    have km : touches marked k := ka.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h))
    have save := saved p g k hg hk (fun e => ga (by subst k; exact ka)) gm km
    obtain ⟨n,t,r,cost,ok⟩ := slicedRun (j:=j) (p:=p)
    have valEq : (p.foldl st (sliced j)).getD o zero = fun y => f (off y) := by
      funext y
      rw [getAt,values]
      have poolEq : (sliced j).map (fun u => u y) = (start j).map (fun u => u (off y)) := by
        simp only [sliced,List.map_map,Function.comp_def]
      rw [poolEq,startAt]
      exact hit (off y)
    obtain ⟨q,i,lb,h⟩ := canOfRun r (n:=(m-2)) (by omega) (valEq ▸ (ok o trivial).1)
    exact ⟨q,i,lb,fun y => (poolAt y) ▸ h y⟩

end PetersenFirstSignedCut
