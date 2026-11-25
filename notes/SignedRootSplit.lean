import PrismSignedFrontier

namespace PrismSignedFrontier.RootSplit

def Agrees (s : Finset W) (i j : Fin 64) : Prop :=
  ∀ w ∈ s, w.getLsbD i.val = w.getLsbD j.val

def Depends (s : Finset W) (w : W) : Prop :=
  ∀ i j, Agrees s i j → w.getLsbD i.val = w.getLsbD j.val

def root (g : W) (s : Finset W) : Prop :=
  ∃ A B : Finset W, A ∪ B = s ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
    ∃ x y, Depends A x ∧ Depends B y ∧ g ∈ choices x y

private def expand (set : Finset W) (w a b : W) : Finset W :=
  if w ∈ set then insert a (insert b (set.erase w)) else set

private theorem depend_expand {S : Finset W} {z a b w : W} (dep : Depends S z)
    (form : w ∈ choices a b) : Depends (expand S w a b) z := by
  intro i j agree
  apply dep i j
  intro u hu
  by_cases used : w ∈ S
  · rw [expand,ite_eq_left used] at agree
    by_cases eq : u = w
    · subst u
      exact same_choice a b w form i j i.isLt j.isLt (agree _ (by simp)) (agree _ (by simp))
    · exact agree u (by simp [hu,eq])
  · exact agree u (by simp [expand,used,hu])

-- At the leaf bound, inserting the two operands increases the live set by
-- exactly one. Neither operand was already needed elsewhere in the suffix.
theorem factor {g : W} {k : Nat} {s : Finset W} (run : Cone g k s)
    (tight : s.card = k+1) : s = {g} ∨ root g s := by
  induction run with
  | done => exact Or.inl rfl
  | @step k needed a b w rest wanted a0 b0 ab aw bw form ih =>
    have erase := Finset.card_erase_of_mem wanted
    have pos := Finset.card_pos.mpr ⟨w,wanted⟩
    have eb := Finset.card_insert_le b (needed.erase w)
    have ea := Finset.card_insert_le a (insert b (needed.erase w))
    have size := rest.size
    have deep : needed.card = k+1 := by omega
    have freshA : a ∉ needed := by
      intro mem
      have inS : a ∈ insert b (needed.erase w) := by simp [aw,mem]
      rw [Finset.insert_eq_of_mem inS] at tight
      omega
    have freshB : b ∉ needed := by
      intro mem
      have keep : insert b (needed.erase w) = needed.erase w :=
        Finset.insert_eq_of_mem (by simp [bw,mem])
      rw [keep] at tight ea
      omega
    right
    rcases ih deep with single | ⟨A,B,parts,dis,aLive,bLive,x,y,ax,by',hit⟩
    · have wg : w = g := by simpa [single] using wanted
      subst w
      refine ⟨{a},{b},by simp [single],by simp [ab],by simp,by simp,a,b,
        fun i j h => h a (by simp),fun i j h => h b (by simp),form⟩
    · have inAB : w ∈ A ∨ w ∈ B := Finset.mem_union.mp (parts.symm ▸ wanted)
      have leftFresh : a ∉ A ∧ b ∉ A := by
        constructor <;> intro h
        · exact freshA (parts ▸ Finset.mem_union_left B h)
        · exact freshB (parts ▸ Finset.mem_union_left B h)
      have rightFresh : a ∉ B ∧ b ∉ B := by
        constructor <;> intro h
        · exact freshA (parts ▸ Finset.mem_union_right A h)
        · exact freshB (parts ▸ Finset.mem_union_right A h)
      refine ⟨expand A w a b,expand B w a b,?_,?_,?_,?_,
        x,y,depend_expand ax form,depend_expand by' form,hit⟩
      · rcases inAB with ha | hb
        · have hb : w ∉ B := Finset.disjoint_left.mp dis ha
          simp only [expand,ha,hb,ite_true,ite_false,←parts,Finset.erase_union_distrib,
            Finset.erase_eq_of_notMem hb,Finset.insert_union]
        · have ha : w ∉ A := fun h => Finset.disjoint_left.mp dis h hb
          simp only [expand,ha,hb,ite_true,ite_false,←parts,Finset.erase_union_distrib,
            Finset.erase_eq_of_notMem ha,Finset.union_insert]
      · rcases inAB with ha | hb
        · have hb : w ∉ B := Finset.disjoint_left.mp dis ha
          simp only [expand,ha,hb,ite_true,ite_false,Finset.disjoint_insert_left]
          exact ⟨rightFresh.1,rightFresh.2,dis.mono_left (Finset.erase_subset ..)⟩
        · have ha : w ∉ A := fun h => Finset.disjoint_left.mp dis h hb
          simp only [expand,ha,hb,ite_true,ite_false,Finset.disjoint_insert_right]
          exact ⟨leftFresh.1,leftFresh.2,dis.mono_right (Finset.erase_subset ..)⟩
      · by_cases mem : w ∈ A <;> simp [expand,mem,aLive]
      · by_cases mem : w ∈ B <;> simp [expand,mem,bLive]

-- A negative row defeats an AND root when each part of that row also occurs
-- on some positive row. The same test with polarities reversed defeats OR.
def obstruction (g : W) (A B : Finset W) (polarity : Bool) : Prop :=
  ∃ r i j : Fin 64, g.getLsbD r.val = polarity ∧ g.getLsbD i.val = !polarity ∧
    g.getLsbD j.val = !polarity ∧ Agrees A r i ∧ Agrees B r j

theorem root_test {g : W} {A B : Finset W} {x y : W}
    (left : Depends A x) (right : Depends B y) (hit : g ∈ choices x y) :
    ¬obstruction g A B false ∨ ¬obstruction g A B true := by
  simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl
  · left
    rintro ⟨r,i,j,hr,hi,hj,a,b⟩
    have hx := left r i a
    have hy := right r j b
    simp only [BitVec.getLsbD_and,Bool.not_false,Bool.and_eq_true] at hr hi hj
    rw [hx,hy,hi.1,hj.2] at hr
    contradiction
  · left
    rintro ⟨r,i,j,hr,hi,hj,a,b⟩
    have hx := left r i a
    have hy := right r j b
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,r.isLt,i.isLt,j.isLt,
      decide_true,Bool.true_and,Bool.not_false,Bool.and_eq_true] at hr hi hj
    rw [hx,hy,hi.1,hj.2] at hr
    contradiction
  · left
    rintro ⟨r,i,j,hr,hi,hj,a,b⟩
    have hx := left r i a
    have hy := right r j b
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,r.isLt,i.isLt,j.isLt,
      decide_true,Bool.true_and,Bool.not_false,Bool.and_eq_true] at hr hi hj
    rw [hx,hy,hi.1,hj.2] at hr
    contradiction
  · right
    rintro ⟨r,i,j,hr,hi,hj,a,b⟩
    have hx := left r i a
    have hy := right r j b
    simp only [BitVec.getLsbD_or,Bool.not_true,Bool.or_eq_false_iff] at hr hi hj
    rw [hx,hy,hi.1,hj.2] at hr
    contradiction


def possible (g : W) (s : Finset W) : Prop :=
  ∃ A ⊆ s, A.Nonempty ∧ (s \ A).Nonempty ∧
    (¬obstruction g A (s \ A) false ∨ ¬obstruction g A (s \ A) true)

theorem necessary {g : W} {k : Nat} {s : Finset W} (run : Cone g k s)
    (tight : s.card = k+1) (many : 1 < s.card) : possible g s := by
  rcases factor run tight with eq | ⟨A,B,partition,dis,ha,hb,x,y,dx,dy,form⟩
  · simp [eq] at many
  · have remainder : s \ A = B := by
      ext w
      rw [← partition]
      simp only [Finset.mem_sdiff,Finset.mem_union]
      constructor
      · intro h
        exact h.1.resolve_left h.2
      · exact fun h => ⟨Or.inr h,fun bad => Finset.disjoint_left.mp dis bad h⟩
    refine ⟨A,fun w hw => partition ▸ Finset.mem_union_left B hw,ha,?_,?_⟩
    · rwa [remainder]
    · rw [remainder]
      exact root_test dx dy form

end PrismSignedFrontier.RootSplit
