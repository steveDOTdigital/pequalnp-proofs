import Mathlib

namespace PEqualNP.Outside.OrientationRanges904

-- Bit j points from the first endpoint of edge j to its second when true.
def absorbs {n : Nat} (edges : List (Nat × Nat)) (o : BitVec n) (s : List Nat) (v : Nat) : Bool :=
  edges.zipIdx.any fun ((a,b),j) =>
    (a == v && s.contains b && o.getLsbD j) || (b == v && s.contains a && !o.getLsbD j)

-- Every edge has at most one endpoint in s. An edge entirely outside s
-- has at least one endpoint with an outgoing arc into s.
def valid {n : Nat} (edges : List (Nat × Nat)) (o : BitVec n) (s : List Nat) : Bool :=
  edges.all fun (a,b) =>
    !(s.contains a && s.contains b) &&
    (s.contains a || s.contains b || absorbs edges o s a || absorbs edges o s b)

def edges0 : List (Nat × Nat) :=
  [(2, 3), (1, 4), (0, 5), (4, 6), (5, 6),
   (3, 7), (5, 7), (6, 7), (2, 8), (4, 8),
   (6, 8), (1, 9), (3, 9), (7, 9), (0, 10),
   (2, 10), (8, 10), (0, 11), (1, 11), (9, 11),
   (10, 11)]

def candidates0 : List (List Nat) :=
  [[7, 8, 11], [0, 1, 7, 8], [0, 2, 6, 9], [1, 3, 6, 10],
   [2, 4, 5, 9], [2, 4, 7, 11], [3, 4, 5, 10], [3, 4, 5, 11],
   [3, 5, 8, 11], [4, 5, 9, 10]]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem graph0 (o : BitVec 21) :
    ∃ s ∈ candidates0, (s.Nodup ∧ s.length ≤ 4 ∧ ∀ v ∈ s, v < 12) ∧ valid edges0 o s = true := by
  have cover : (candidates0.any fun s => valid edges0 o s) = true := by
    simp only [candidates0, valid, absorbs, edges0, List.zipIdx, Nat.reduceBEq, Nat.reduceAdd,
      List.any_cons, List.any_nil, List.all_cons, List.all_nil, List.contains_cons,
      List.contains_nil, Bool.or_false, Bool.false_or, Bool.true_or, Bool.or_true,
      Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.not_false]
    grind (splits := 40) only
  obtain ⟨s, hs, ok⟩ := List.any_eq_true.mp cover
  refine ⟨s, hs, ?_, ok⟩
  have small : ∀ t ∈ candidates0, t.Nodup ∧ t.length ≤ 4 ∧ ∀ v ∈ t, v < 12 := by decide
  exact small s hs

def edges1 : List (Nat × Nat) :=
  [(3, 5), (4, 5), (2, 6), (4, 6), (1, 7),
   (3, 7), (6, 7), (1, 8), (2, 8), (5, 8),
   (0, 9), (2, 9), (3, 9), (0, 10), (1, 10),
   (4, 10), (0, 11), (6, 11), (7, 11), (0, 12),
   (5, 12), (8, 12), (11, 12)]

def candidates1 : List (List Nat) :=
  [[1, 5, 9, 11], [1, 6, 9, 12], [2, 3, 4, 11], [2, 3, 4, 12],
   [2, 4, 7, 12], [2, 5, 10, 11], [2, 7, 10, 12], [3, 4, 8, 11],
   [3, 6, 10, 12], [3, 8, 10, 11], [4, 7, 8, 9], [4, 7, 9, 12],
   [4, 8, 9, 11], [5, 6, 9, 10], [5, 7, 9, 10], [5, 9, 10, 11],
   [6, 8, 9, 10], [6, 9, 10, 12], [7, 8, 9, 10], [7, 9, 10, 12],
   [8, 9, 10, 11]]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem graph1 (o : BitVec 23) :
    ∃ s ∈ candidates1, (s.Nodup ∧ s.length ≤ 4 ∧ ∀ v ∈ s, v < 13) ∧ valid edges1 o s = true := by
  have cover : (candidates1.any fun s => valid edges1 o s) = true := by
    simp only [candidates1, valid, absorbs, edges1, List.zipIdx, Nat.reduceBEq, Nat.reduceAdd,
      List.any_cons, List.any_nil, List.all_cons, List.all_nil, List.contains_cons,
      List.contains_nil, Bool.or_false, Bool.false_or, Bool.true_or, Bool.or_true,
      Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.not_false]
    grind (splits := 40) only
  obtain ⟨s, hs, ok⟩ := List.any_eq_true.mp cover
  refine ⟨s, hs, ?_, ok⟩
  have small : ∀ t ∈ candidates1, t.Nodup ∧ t.length ≤ 4 ∧ ∀ v ∈ t, v < 13 := by decide
  exact small s hs

def edges2 : List (Nat × Nat) :=
  [(2, 4), (3, 4), (1, 5), (3, 5), (1, 6),
   (2, 6), (0, 7), (3, 7), (6, 7), (0, 8),
   (2, 8), (5, 8), (0, 9), (1, 9), (4, 9),
   (6, 10), (7, 10), (5, 11), (8, 11), (10, 11),
   (4, 12), (9, 12), (10, 12), (11, 12)]

def candidates2 : List (List Nat) :=
  [[0, 4, 5, 6], [0, 4, 6, 11], [0, 5, 6, 12], [1, 4, 7, 8],
   [1, 4, 7, 11], [1, 7, 8, 12], [2, 3, 9, 11], [2, 5, 7, 9],
   [2, 5, 7, 12], [2, 5, 9, 10], [2, 7, 9, 11], [3, 6, 8, 9],
   [3, 6, 8, 12], [3, 6, 9, 11], [3, 8, 9, 10]]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem graph2 (o : BitVec 24) :
    ∃ s ∈ candidates2, (s.Nodup ∧ s.length ≤ 4 ∧ ∀ v ∈ s, v < 13) ∧ valid edges2 o s = true := by
  have cover : (candidates2.any fun s => valid edges2 o s) = true := by
    simp only [candidates2, valid, absorbs, edges2, List.zipIdx, Nat.reduceBEq, Nat.reduceAdd,
      List.any_cons, List.any_nil, List.all_cons, List.all_nil, List.contains_cons,
      List.contains_nil, Bool.or_false, Bool.false_or, Bool.true_or, Bool.or_true,
      Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.not_false]
    grind (splits := 40) only
  obtain ⟨s, hs, ok⟩ := List.any_eq_true.mp cover
  refine ⟨s, hs, ?_, ok⟩
  have small : ∀ t ∈ candidates2, t.Nodup ∧ t.length ≤ 4 ∧ ∀ v ∈ t, v < 13 := by decide
  exact small s hs

end PEqualNP.Outside.OrientationRanges904
