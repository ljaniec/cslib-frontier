/-
Copyright (c) 2026 Samuel Schlesinger, ljaniec. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, ljaniec
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.MengerSet

/-!
# `A`–`B` Menger tests

Kernel-checked instances (no `native_decide`) of the finite `A`–`B` vertex forms in
`CslibFrontier.Algorithms.Lean.MaxFlow.MengerSet`:

1. A 5-vertex digraph with two strict `A`–`B` paths and a cut of size `2`, pinning the
   matching-cut size. Three paths are refuted.
2. An `A ∩ B` vertex is forced into every cut, and the singleton path is an `A`–`B` path.
3. The same packing on the underlying simple graph, identified with `SimpleGraph.IsSeparator`.
4. On a 3-vertex path, `IsVertexSeparator` is the singleton separator that avoids both
   terminals; a separator that contains a terminal is not an `IsVertexSeparator`.
-/

public section

namespace CslibFrontierTests.MengerSet

open Cslib.Algorithms.Lean.MaxFlow SimpleGraph

/-! ### 1. Two disjoint `A`–`B` paths -/

/-- Arcs `0 → 2 → 3` and `1 → 4`. -/
def dg : Digraph (Fin 5) where
  Adj i j := (i, j) ∈ ([(0, 2), (2, 3), (1, 4)] : List (Fin 5 × Fin 5))

instance : DecidableRel dg.Adj := fun i j =>
  inferInstanceAs (Decidable ((i, j) ∈ ([(0, 2), (2, 3), (1, 4)] : List (Fin 5 × Fin 5))))

def dgA : Finset (Fin 5) := {0, 1}

def dgB : Finset (Fin 5) := {3, 4}

/-- The paths `[0, 2, 3]` and `[1, 4]`. -/
def dgP : Fin 2 → List (Fin 5)
  | 0 => [0, 2, 3]
  | 1 => [1, 4]

theorem dgP_isABDipath : ∀ i, IsABDipath dg dgA dgB (dgP i) := by decide

theorem dgP_vertexDisjoint : VertexDisjoint dgP := by decide

theorem dg_cut : IsABVertexCut dg dgA dgB {2, 4} :=
  isABVertexCut_of_closed (S := {0, 1}) (by decide) (by decide) (by decide)

example : ({2, 4} : Finset (Fin 5)).card = 2 := by decide

/-- Every `A`–`B` vertex cut has at least two vertices. -/
example : ∀ T : Finset (Fin 5), IsABVertexCut dg dgA dgB T → 2 ≤ T.card :=
  (exists_vertexDisjoint_iff_forall_isABVertexCut dg dgA dgB 2).mp
    ⟨dgP, dgP_isABDipath, dgP_vertexDisjoint⟩

example : ¬ ∃ P : Fin 3 → List (Fin 5), (∀ i, IsABDipath dg dgA dgB (P i)) ∧
    VertexDisjoint P := by
  rw [exists_vertexDisjoint_iff_forall_isABVertexCut]
  intro h
  have := h _ dg_cut
  simp at this

/-- The matching-cut form, pinned at `m = 2` by weak duality. -/
example : ∃ (m : ℕ) (P : Fin m → List (Fin 5)), m = 2 ∧ (∀ i, IsABDipath dg dgA dgB (P i)) ∧
    VertexDisjoint P ∧ ∃ T : Finset (Fin 5), IsABVertexCut dg dgA dgB T ∧ T.card = m := by
  obtain ⟨m, P, hP, hdisj, T, hT, hTm⟩ := exists_vertexDisjoint_eq_isABVertexCut dg dgA dgB
  refine ⟨m, P, ?_, hP, hdisj, T, hT, hTm⟩
  have h1 := card_le_card_of_vertexDisjoint_of_isABVertexCut hP hdisj dg_cut
  have h2 := card_le_card_of_vertexDisjoint_of_isABVertexCut dgP_isABDipath dgP_vertexDisjoint hT
  have h3 : ({2, 4} : Finset (Fin 5)).card = 2 := by decide
  omega

/-! ### 2. The intersection is forced into the cut -/

def interG : Digraph (Fin 3) where
  Adj _ _ := False

instance : DecidableRel interG.Adj := fun _ _ => inferInstanceAs (Decidable False)

theorem inter_singleton : IsABDipath interG {0, 1} {1, 2} [1] := by decide

theorem inter_cut : IsABVertexCut interG {0, 1} {1, 2} {1} :=
  isABVertexCut_of_closed (S := {0}) (by decide) (by decide) (by decide)

example : ∀ T : Finset (Fin 3), IsABVertexCut interG {0, 1} {1, 2} T → (1 : Fin 3) ∈ T :=
  fun _ hT => mem_of_mem_inter_of_isABVertexCut (by decide) hT

example : ¬ IsABVertexCut interG {0, 1} {1, 2} (∅ : Finset (Fin 3)) := by
  intro h
  have := mem_of_mem_inter_of_isABVertexCut (A := {0, 1}) (B := {1, 2}) (v := 1) (by decide) h
  simp at this

/-! ### 3. The same packing, undirected -/

/-- Edges `0 — 2 — 3` and `1 — 4`. -/
def ug : SimpleGraph (Fin 5) where
  Adj i j := s(i, j) ∈ ({s(0, 2), s(2, 3), s(1, 4)} : Finset (Sym2 (Fin 5)))
  symm := ⟨fun _ _ h => by simpa [Sym2.eq_swap] using h⟩
  loopless := ⟨fun i h => by revert i; decide⟩

instance : DecidableRel ug.Adj := fun i j =>
  inferInstanceAs (Decidable (s(i, j) ∈
    ({s(0, 2), s(2, 3), s(1, 4)} : Finset (Sym2 (Fin 5)))))

def ugP : Fin 2 → List (Fin 5)
  | 0 => [0, 2, 3]
  | 1 => [1, 4]

theorem ugP_isABDipath : ∀ i, IsABDipath (toDigraph ug) dgA dgB (ugP i) := by decide

theorem ugP_vertexDisjoint : VertexDisjoint ugP := by decide

theorem ug_cut : IsABVertexCut (toDigraph ug) dgA dgB {2, 4} :=
  isABVertexCut_of_closed (S := {0, 1}) (by decide) (by decide) (by decide)

theorem ug_sep : ug.IsSeparator (dgA : Set (Fin 5)) dgB ({2, 4} : Set (Fin 5)) :=
  isABVertexCut_iff_isSeparator.mp ug_cut

example : ∀ T : Finset (Fin 5), ug.IsSeparator (dgA : Set _) dgB (T : Set _) → 2 ≤ T.card :=
  (exists_vertexDisjoint_iff_forall_isSeparator ug dgA dgB 2).mp
    ⟨ugP, ugP_isABDipath, ugP_vertexDisjoint⟩

example : ∃ (m : ℕ) (P : Fin m → List (Fin 5)), m = 2 ∧
    (∀ i, IsABDipath (toDigraph ug) dgA dgB (P i)) ∧ VertexDisjoint P ∧
    ∃ T : Finset (Fin 5), ug.IsSeparator (dgA : Set _) dgB (T : Set _) ∧ T.card = m := by
  obtain ⟨m, P, hP, hdisj, T, hT, hTm⟩ := exists_vertexDisjoint_eq_isSeparator ug dgA dgB
  refine ⟨m, P, ?_, hP, hdisj, T, hT, hTm⟩
  have h1 := card_le_card_of_vertexDisjoint_of_isSeparator hP hdisj ug_sep
  have h2 := card_le_card_of_vertexDisjoint_of_isSeparator ugP_isABDipath ugP_vertexDisjoint hT
  have h3 : ({2, 4} : Finset (Fin 5)).card = 2 := by decide
  omega

/-! ### 4. Single-terminal bridge -/

/-- The path `0 — 1 — 2`. -/
def path3 : SimpleGraph (Fin 3) where
  Adj i j := s(i, j) ∈ ({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3)))
  symm := ⟨fun _ _ h => by simpa [Sym2.eq_swap] using h⟩
  loopless := ⟨fun i h => by revert i; decide⟩

instance : DecidableRel path3.Adj := fun i j =>
  inferInstanceAs (Decidable (s(i, j) ∈ ({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3)))))

theorem path3_sep : IsVertexSeparator path3 0 2 {1} :=
  isVertexSeparator_of_forall_adj (S := {0}) (by decide) (by decide) (by decide) (by decide)
    (by decide)

example : path3.IsSeparator ({0} : Set (Fin 3)) {2} ({1} : Set _) ∧
    (0 : Fin 3) ∉ ({1} : Finset (Fin 3)) ∧ (2 : Fin 3) ∉ ({1} : Finset (Fin 3)) :=
  isVertexSeparator_iff_isSeparator.mp path3_sep

/-- A separator may contain a terminal; `IsVertexSeparator` may not. -/
example : path3.IsSeparator ({0} : Set (Fin 3)) {2} ({0, 1} : Set _) :=
  isSeparator_of_subset_left (by decide)

example : ¬ IsVertexSeparator path3 0 2 {0, 1} := by
  intro h
  have := (isVertexSeparator_iff_isSeparator.mp h).2.1
  simp at this

end CslibFrontierTests.MengerSet
