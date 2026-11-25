import SignedPinProjection

namespace PrismSignedFrontier.UniversalSix

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def five : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def four : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0xfffffffefefaeca0
def friend : W := 0xfffef888fffef888
def pendant : W := 0xfffee8e8fffee8e8
def clique : W := 0xfee8fee8fee8fee8
def negative : List Nat := [0, 1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 32]

theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨4,5,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨8,10,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨2,10,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,17,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,33,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def row0 : Fin 64 → Fin 64 := ![0, 4, 16, 20, 2, 6, 18, 22, 8, 12, 24, 28, 10, 14, 26, 30, 32, 36, 48, 52, 34, 38, 50, 54, 40, 44, 56, 60, 42, 46, 58, 62, 0, 4, 16, 20, 2, 6, 18, 22, 8, 12, 24, 28, 10, 14, 26, 30, 32, 36, 48, 52, 34, 38, 50, 54, 40, 44, 56, 60, 42, 46, 58, 62]
def row1 : Fin 64 → Fin 64 := ![0, 1, 4, 5, 16, 17, 20, 21, 8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 40, 41, 44, 45, 56, 57, 60, 61, 0, 1, 4, 5, 16, 17, 20, 21, 8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 40, 41, 44, 45, 56, 57, 60, 61]
def row2 : Fin 64 → Fin 64 := ![0, 1, 16, 17, 2, 3, 18, 19, 8, 9, 24, 25, 10, 11, 26, 27, 32, 33, 48, 49, 34, 35, 50, 51, 40, 41, 56, 57, 42, 43, 58, 59, 0, 1, 16, 17, 2, 3, 18, 19, 8, 9, 24, 25, 10, 11, 26, 27, 32, 33, 48, 49, 34, 35, 50, 51, 40, 41, 56, 57, 42, 43, 58, 59]
def row3 : Fin 64 → Fin 64 := ![0, 1, 4, 5, 16, 17, 20, 21, 2, 3, 6, 7, 18, 19, 22, 23, 32, 33, 36, 37, 48, 49, 52, 53, 34, 35, 38, 39, 50, 51, 54, 55, 0, 1, 4, 5, 16, 17, 20, 21, 2, 3, 6, 7, 18, 19, 22, 23, 32, 33, 36, 37, 48, 49, 52, 53, 34, 35, 38, 39, 50, 51, 54, 55]
def row4 : Fin 64 → Fin 64 := ![0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15, 32, 33, 36, 37, 34, 35, 38, 39, 40, 41, 44, 45, 42, 43, 46, 47, 0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15, 32, 33, 36, 37, 34, 35, 38, 39, 40, 41, 44, 45, 42, 43, 46, 47]
def source (i : Fin 5) : Fin 64 → Fin 64 := ![row0,row1,row2,row3,row4] i
def pin (i : Fin 5) := rowMap (source i)
def prune : Fin 64 → Fin 64 := ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23]
def typeGoal (i : Fin 5) : W := if i = 0 ∨ i = 2 ∨ i = 4 then friend else pendant

theorem goalPin : ∀ i, pin i target = typeGoal i := by decide +kernel
theorem fiveOn (i : Fin 5) : pin i target ≠ 0 := by fin_cases i <;> decide +kernel
theorem cliqueOn : rowMap prune pendant = clique := by decide +kernel

-- Each pinned peripheral vertex leaves one of two five-input graphs.
def smallLower (g : W) (xs : List W) (n : Nat) := ∀ {k : Nat} {s : Finset W},
  Cone g k s → s ⊆ insert 0 xs.toFinset → n ≤ k

theorem pendantEssential : Essential pendant five := by
  intro w hw
  simp only [five,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · refine ⟨2,3,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [five,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,3,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [five,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [five,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨16,24,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [five,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,17,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [five,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

theorem pendantLower (hc : smallLower clique four 7) : smallLower pendant five 8 := by
  intro k s run sub
  have start := run.initial (by decide +kernel : pendant ≠ 0) five pendantEssential sub
  rw [start] at run
  have nz : rowMap prune pendant ≠ 0 := by rw [cliqueOn]; decide +kernel
  obtain ⟨j,t,le,proj,inside,equal⟩ := run.project (rowMap prune) (rowMap_form prune) nz
  have access : five.toFinset.image (rowMap prune) ⊆ insert 0 four.toFinset := by decide +kernel
  have zero : 0 ∈ five.toFinset.image (rowMap prune) := by decide +kernel
  have strict : j ≠ k := fun eq => proj.noZero nz (equal eq zero)
  rw [cliqueOn] at proj
  have lower := hc proj (inside.trans access)
  omega

def excluded (i : Fin 5) (s : List W) : Bool :=
  let xs := s.map (pin i)
  xs.contains 0 && xs.all (fun w => w == 0 || five.contains w)

def permit (s : List W) : Bool :=
  covered target negative s && !((List.finRange 5).any fun i => excluded i s)

theorem survives (hf : smallLower friend five 8) (hc : smallLower clique four 7)
    {k : Nat} (s : List W) (short : k ≤ 8) (run : Cone target k s.toFinset) :
    permit s = true := by
  have hp : smallLower pendant five 8 := @pendantLower hc
  have clean (i : Fin 5) : excluded i s = false := by
    by_contra! hit
    have both := Bool.and_eq_true_iff.mp (show excluded i s = true by simpa using hit)
    let f := pin i
    have stock : (s.map f).toFinset = s.toFinset.image f := by
      ext z
      simp only [List.mem_toFinset,List.mem_map,Finset.mem_image]
    have zero : 0 ∈ s.toFinset.image f := by rw [←stock]; simpa using both.1
    have subset : s.toFinset.image f ⊆ insert 0 five.toFinset := by
      intro w hw
      rw [←stock] at hw
      have ok := List.all_eq_true.mp both.2 w (List.mem_toFinset.mp hw)
      simpa [List.contains_eq_mem] using ok
    obtain ⟨j,t,le,p,inside,full⟩ := run.project f (rowMap_form (source i)) (fiveOn i)
    have strict : j ≠ k := fun eq => p.noZero (fiveOn i) (full eq zero)
    change Cone (pin i target) j t at p
    rw [goalPin,typeGoal] at p
    have bound : 8 ≤ j := by
      split at p
      · exact hf p (inside.trans subset)
      · exact hp p (inside.trans subset)
    omega
  simpa [permit,run.covered negative neg] using clean

def first (a : W) := raw.any fun b => decide (a.toNat < b.toNat) && onePair raw permit a b

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem first0 : first 0xaaaaaaaaaaaaaaaa = false := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem first1 : first 0xcccccccccccccccc = false := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem first2 : first 0xf0f0f0f0f0f0f0f0 = false := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem first3 : first 0xff00ff00ff00ff00 = false := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem first4 : first 0xffff0000ffff0000 = false := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem first5 : first 0xffffffff00000000 = false := by decide +kernel

theorem avoid : moves raw permit = false := by
  change raw.any first = false
  simp only [raw,List.any_cons,List.any_nil,first0,first1,first2,first3,first4,first5,Bool.false_or]

theorem lower (hf : smallLower friend five 8) (hc : smallLower clique four 7) :
    smallLower target raw 10 := by
  intro k s run sub
  have eq := run.initial nonzero raw essential sub
  rw [eq] at run
  by_contra! short
  cases k with
  | zero =>
    have bound := run.size
    have card : raw.toFinset.card = 6 := by decide +kernel
    omega
  | succ k =>
    have ok := moves_complete raw permit nonzero (by decide +kernel) run rfl
      (fun t _ ht => survives hf hc t (by omega) ht)
    simp [avoid] at ok

end PrismSignedFrontier.UniversalSix
