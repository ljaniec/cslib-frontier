/-
Copyright (c) 2026 Samuel Schlesinger, ljaniec. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, ljaniec
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.Menger
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Separator

/-!
# Menger's theorem for `A`–`B` paths

The finite vertex form of Menger's theorem for a pair of vertex sets, derived from the
two-terminal theorem `exists_internallyDisjoint_eq_isVertexCut`.

## Model and source mapping

* **Directed graphs.** Mathlib `Digraph V` on a finite vertex type, so there are no parallel arcs.
  A strict `A`–`B` path (`IsABDipath`) is a duplicate-free vertex list that starts in `A`, ends in
  `B`, and meets `A ∪ B` only at its ends. A singleton is an `A`–`B` path exactly when its vertex
  lies in `A ∩ B`. An `A`–`B` vertex cut (`IsABVertexCut`) meets every such path; it may meet `A`
  and `B`, and it must contain `A ∩ B`.
* **Source.** This is [Schrijver2017], §4.1, Theorem 4.1, for simple digraphs. The proof is the
  reduction of that theorem to Corollary 4.1a used there: add a super-source with arcs into `A`
  and a super-sink with arcs out of `B`, apply the two-terminal theorem, and shortcut each
  super-source–super-sink path to a strict `A`–`B` path (last vertex in `A`, then first later
  vertex in `B`). Strict and non-strict `A`–`B` paths agree for both the packing and the cut,
  because the shortcut is a subpath.
* **Undirected graphs.** Apply the directed theorem to `toDigraph G`. The resulting cut is
  `SimpleGraph.IsSeparator` ([Diestel2025], Theorem 3.3.1, finite simple graphs). For single
  terminals, `IsVertexSeparator G u v T` is that separator together with `u, v ∉ T`
  ([Diestel2025], §1.4).

## Scope

Finite vertex sets and simple digraphs only. Not covered: the directed-multigraph and capacity
forms, the arc and edge `A`–`B` forms, the global `k`-connectivity form ([Diestel2025],
Theorem 3.3.6), infinite graphs, and any running-time bound. This is a milestone of the remaining
work in [Menger1927]'s formalization, not that whole objective.

## Main definitions

* `Cslib.Algorithms.Lean.MaxFlow.IsABDipath`, `VertexDisjoint`, `IsABVertexCut`: strict directed
  `A`–`B` paths, vertex-disjointness and cuts.

## Main results

* `Cslib.Algorithms.Lean.MaxFlow.exists_vertexDisjoint_eq_isABVertexCut` and
  `exists_vertexDisjoint_iff_forall_isABVertexCut`: directed `A`–`B` vertex form.
* `Cslib.Algorithms.Lean.MaxFlow.exists_vertexDisjoint_eq_isSeparator`,
  `exists_vertexDisjoint_iff_forall_isSeparator` and `isABVertexCut_iff_isSeparator`:
  undirected `A`–`B` vertex form, identified with `SimpleGraph.IsSeparator`.
* `Cslib.Algorithms.Lean.MaxFlow.isVertexSeparator_iff_isSeparator`: the single-terminal bridge.
* Weak duality `card_le_card_of_vertexDisjoint_of_isABVertexCut` and the closed-set certificate
  `isABVertexCut_of_closed`.

## References

* [K. Menger, *Zur allgemeinen Kurventheorie*][Menger1927]
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017]
* [R. Diestel, *Graph Theory*][Diestel2025]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

variable {V : Type*}

/-- `p` is a strict directed `A`–`B` path in `G`: a duplicate-free vertex list that starts in `A`,
ends in `B`, meets `A ∪ B` only at its ends, and whose consecutive pairs are arcs. A singleton is
an `A`–`B` path exactly when its vertex lies in `A ∩ B`. -/
def IsABDipath (G : Digraph V) (A B : Finset V) (p : List V) : Prop :=
  p.Nodup ∧
    (∃ a ∈ A, p.head? = some a) ∧
      (∃ b ∈ B, p.getLast? = some b) ∧
        (∀ v ∈ p, p.head? ≠ some v → p.getLast? ≠ some v → v ∉ A ∧ v ∉ B) ∧
          ∀ e ∈ pathArcs p, G.Adj e.1 e.2

instance instDecidableIsABDipath [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (A B : Finset V) (p : List V) : Decidable (IsABDipath G A B p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The vertex lists `P i` are pairwise vertex-disjoint. -/
def VertexDisjoint {ι : Type*} (P : ι → List V) : Prop :=
  Pairwise fun i j => (P i).Disjoint (P j)

instance instDecidableVertexDisjoint [DecidableEq V] {ι : Type*} [Fintype ι] (P : ι → List V) :
    Decidable (VertexDisjoint P) :=
  inferInstanceAs (Decidable (Pairwise fun i j => (P i).Disjoint (P j)))

/-- `T` is an `A`–`B` vertex cut of `G`: every strict directed `A`–`B` path visits `T`. `T` may
meet `A` and `B`, and must contain `A ∩ B`. -/
def IsABVertexCut (G : Digraph V) (A B : Finset V) (T : Finset V) : Prop :=
  ∀ p, IsABDipath G A B p → ∃ v ∈ p, v ∈ T

/-- A vertex of `A ∩ B` lies on the singleton `A`–`B` path, so every `A`–`B` vertex cut contains
it. -/
theorem mem_of_mem_inter_of_isABVertexCut {G : Digraph V} {A B : Finset V} {v : V}
    (hv : v ∈ A ∩ B) {T : Finset V} (hT : IsABVertexCut G A B T) : v ∈ T := by
  have hvA : v ∈ A := (Finset.mem_inter.mp hv).1
  have hvB : v ∈ B := (Finset.mem_inter.mp hv).2
  have hp : IsABDipath G A B [v] := by
    refine ⟨List.nodup_singleton v, ⟨v, hvA, rfl⟩, ⟨v, hvB, rfl⟩, ?_, by simp⟩
    intro w hw hne _
    have hw' : w = v := List.mem_singleton.mp hw
    exact hne (by simp only [hw', List.head?_cons])
  obtain ⟨w, hw, hwT⟩ := hT _ hp
  simp only [List.mem_singleton] at hw
  exact hw ▸ hwT

/-- **Weak duality for `A`–`B` paths**: `k` pairwise vertex-disjoint strict `A`–`B` paths need at
least `k` vertices in every `A`–`B` vertex cut. -/
theorem card_le_card_of_vertexDisjoint_of_isABVertexCut {G : Digraph V} {A B : Finset V} {k : ℕ}
    {P : Fin k → List V} (hP : ∀ i, IsABDipath G A B (P i)) (hdisj : VertexDisjoint P)
    {T : Finset V} (hT : IsABVertexCut G A B T) : k ≤ T.card := by
  classical
  choose v hv hvT using fun i => hT (P i) (hP i)
  have hinj : Function.Injective fun i => (⟨v i, hvT i⟩ : T) := by
    intro i j hij
    by_contra hne
    have heq : v i = v j := congrArg Subtype.val hij
    exact (hdisj hne) (v i) (hv i) (heq ▸ hv j)
  simpa using Fintype.card_le_of_injective _ hinj

private theorem getLast_cons_cons {α : Type*} (a b : α) (l : List α) :
    (a :: b :: l).getLast (List.cons_ne_nil _ _) =
      (b :: l).getLast (List.cons_ne_nil _ _) := rfl

/-- While a chain stays in `S`, it must enter `T` or end outside `S`. -/
private theorem exists_mem_T_of_closed {G : Digraph V} {S T : Finset V} {p : List V}
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S ∨ v ∈ T)
    (hadj : ∀ e ∈ pathArcs p, G.Adj e.1 e.2) (hne : p ≠ []) (hhead : p.head hne ∈ S)
    (hend : p.getLast hne ∈ T ∨ p.getLast hne ∉ S) : ∃ v ∈ p, v ∈ T := by
  induction p generalizing hadj hne hhead hend with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    have hu : u ∈ S := by simpa using hhead
    by_cases huT : u ∈ T
    · exact ⟨u, List.mem_cons_self, huT⟩
    cases rest with
    | nil =>
      rcases by simpa using hend with h | h
      · exact ⟨u, List.mem_cons_self, h⟩
      · exact absurd hu h
    | cons v rest =>
      have hadjuv : G.Adj u v := hadj (u, v) (by simp [pathArcs_cons_cons])
      rcases hclosed u hu v hadjuv with hvS | hvT
      · have htail : ∀ e ∈ pathArcs (v :: rest), G.Adj e.1 e.2 :=
          fun e he => hadj e (by simp [pathArcs_cons_cons, he])
        have hne' : v :: rest ≠ [] := List.cons_ne_nil _ _
        obtain ⟨w, hw, hwT⟩ := ih htail hne' (by simp [hvS])
          (by simpa [getLast_cons_cons] using hend)
        exact ⟨w, List.mem_cons_of_mem _ hw, hwT⟩
      · exact ⟨v, List.mem_cons_of_mem _ List.mem_cons_self, hvT⟩

/-- Closed-set certificate for an `A`–`B` vertex cut. `S` holds vertices reached from `A \ T`
without entering `T`: every vertex of `A` lies in `S` or `T`, every arc out of `S` lands in `S` or
`T`, and no vertex of `B \ T` lies in `S`. -/
theorem isABVertexCut_of_closed {G : Digraph V} {A B S T : Finset V}
    (hA : ∀ a ∈ A, a ∈ T ∨ a ∈ S) (hB : ∀ b ∈ B, b ∈ T ∨ b ∉ S)
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S ∨ v ∈ T) : IsABVertexCut G A B T := by
  intro p hp
  obtain ⟨-, ⟨a, ha, hhead⟩, ⟨b, hb, hlast⟩, -, hadj⟩ := hp
  have hne : p ≠ [] := by
    intro hempty
    simp [hempty] at hhead
  have haHead : p.head hne = a := by
    rw [List.head?_eq_some_head hne] at hhead
    exact Option.some.inj hhead
  have hbLast : p.getLast hne = b := by
    rw [List.getLast?_eq_some_getLast hne] at hlast
    exact Option.some.inj hlast
  rcases hA a ha with hTa | hSa
  · exact ⟨a, haHead ▸ List.head_mem hne, hTa⟩
  · exact exists_mem_T_of_closed hclosed hadj hne (haHead ▸ hSa) (hbLast.symm ▸ hB b hb)

private theorem getLast_cons_of_ne_nil {α : Type*} (a : α) (l : List α) (hl : l ≠ []) :
    (a :: l).getLast (List.cons_ne_nil _ _) = l.getLast hl := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b rest => rw [getLast_cons_cons]

private theorem getLast_append_singleton {α : Type*} (l : List α) (x : α) :
    (l ++ [x]).getLast (by simp) = x := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      rw [List.cons_append, List.cons_append, getLast_cons_cons]
      exact ih

private theorem eq_dropLast_append_getLast {α : Type*} (l : List α) (hl : l ≠ []) :
    l = l.dropLast ++ [l.getLast hl] := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      have ih' := ih (List.cons_ne_nil _ _)
      calc
        a :: b :: rest
          = a :: ((b :: rest).dropLast ++ [(b :: rest).getLast (List.cons_ne_nil _ _)]) :=
            congrArg (a :: ·) ih'
        _ = (a :: (b :: rest).dropLast) ++ [(b :: rest).getLast (List.cons_ne_nil _ _)] := by
            rw [List.cons_append]
        _ = (a :: b :: rest).dropLast ++
            [(a :: b :: rest).getLast (List.cons_ne_nil _ _)] := by
            rw [getLast_cons_cons]

private theorem nodup_of_prefix {α : Type*} {q p : List α} (h : q <+: p) (hp : p.Nodup) :
    q.Nodup := by
  obtain ⟨t, rfl⟩ := h
  exact (List.nodup_append.mp hp).1

private theorem nodup_of_suffix {α : Type*} {q p : List α} (h : q <:+ p) (hp : p.Nodup) :
    q.Nodup := by
  obtain ⟨t, rfl⟩ := h
  exact (List.nodup_append.mp hp).2.1

private theorem mem_pathArcs_of_suffix {l₁ l₂ : List V} (h : l₁ <:+ l₂) {e : V × V}
    (he : e ∈ pathArcs l₁) : e ∈ pathArcs l₂ := by
  obtain ⟨t, rfl⟩ := h
  induction t generalizing e with
  | nil => exact he
  | cons a t ih =>
    have hmem : e ∈ pathArcs (t ++ l₁) := ih he
    rw [List.cons_append]
    cases ht : t ++ l₁ with
    | nil => simp [ht] at hmem
    | cons b rest =>
      rw [ht, pathArcs_cons_cons]
      exact List.mem_cons_of_mem _ (ht ▸ hmem)

private theorem mem_pathArcs_of_prefix {l₁ l₂ : List V} (h : l₁ <+: l₂) {e : V × V}
    (he : e ∈ pathArcs l₁) : e ∈ pathArcs l₂ := by
  obtain ⟨t, rfl⟩ := h
  induction l₁ generalizing e with
  | nil => simp at he
  | cons a rest ih =>
    cases rest with
    | nil => simp at he
    | cons b rest =>
      rw [pathArcs_cons_cons] at he
      rw [show (a :: b :: rest) ++ t = a :: b :: (rest ++ t) from rfl, pathArcs_cons_cons]
      rcases he with rfl | he
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih he)

/-! ### Strict shortcuts -/

section Shortcut

variable [DecidableEq V]

/-- Suffix of `p` starting at its last vertex in `S`, or `[]` if `p` misses `S`. -/
private def dropUntilLastMem (S : Finset V) : List V → List V
  | [] => []
  | v :: vs =>
    if dropUntilLastMem S vs = [] then
      if v ∈ S then v :: vs else []
    else
      dropUntilLastMem S vs

/-- Prefix of `p` through its first vertex in `S`, or all of `p` if `p` misses `S`. -/
private def takeToFirstMem (S : Finset V) : List V → List V
  | [] => []
  | v :: vs => if v ∈ S then [v] else v :: takeToFirstMem S vs

/-- From the last vertex in `A`, stop at the first later vertex in `B`. -/
private def abShortcut (A B : Finset V) (p : List V) : List V :=
  takeToFirstMem B (dropUntilLastMem A p)

private theorem dropUntilLastMem_eq_nil_iff (S : Finset V) :
    ∀ p, dropUntilLastMem S p = [] ↔ ∀ v ∈ p, v ∉ S
  | [] => by simp [dropUntilLastMem]
  | v :: vs => by
    unfold dropUntilLastMem
    split_ifs with htail hv
    · simp only [List.cons_ne_nil, false_iff]
      exact fun h => h v List.mem_cons_self hv
    · simp only [true_iff]
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hv
      · exact ((dropUntilLastMem_eq_nil_iff S vs).mp htail) w hw
    · refine ⟨fun h => absurd h htail, fun h => ?_⟩
      exact htail ((dropUntilLastMem_eq_nil_iff S vs).mpr
        fun w hw => h w (List.mem_cons_of_mem _ hw))

private theorem dropUntilLastMem_suffix (S : Finset V) :
    ∀ p, dropUntilLastMem S p <:+ p
  | [] => ⟨[], rfl⟩
  | v :: vs => by
    unfold dropUntilLastMem
    split_ifs with htail hv
    · exact ⟨[], rfl⟩
    · exact ⟨v :: vs, by simp⟩
    · obtain ⟨t, ht⟩ := dropUntilLastMem_suffix S vs
      exact ⟨v :: t, by rw [ht]⟩

private theorem head_mem_dropUntilLastMem (S : Finset V) (p : List V) {v : V}
    (hv : (dropUntilLastMem S p).head? = some v) : v ∈ S := by
  induction p with
  | nil => exact Option.noConfusion (by simpa [dropUntilLastMem, List.head?_nil] using hv)
  | cons u us ih =>
    unfold dropUntilLastMem at hv
    split_ifs at hv with htail hu
    · simp only [List.head?_cons, Option.some.injEq] at hv
      exact hv ▸ hu
    · exact Option.noConfusion (by simpa [List.head?_nil] using hv)
    · exact ih hv

private theorem getLast?_dropUntilLastMem (S : Finset V) (p : List V)
    (hne : dropUntilLastMem S p ≠ []) : (dropUntilLastMem S p).getLast? = p.getLast? := by
  induction p with
  | nil => exact absurd rfl (by simpa [dropUntilLastMem] using hne)
  | cons u us ih =>
    unfold dropUntilLastMem at hne ⊢
    split_ifs with htail hu
    · rfl
    · exact absurd rfl hne
    · rw [ih htail]
      cases us with
      | nil => simp [dropUntilLastMem] at htail
      | cons w ws => rfl

private theorem not_mem_tail_dropUntilLastMem (S : Finset V) (p : List V) {v : V}
    (hv : v ∈ (dropUntilLastMem S p).tail) : v ∉ S := by
  induction p with
  | nil => exact absurd hv (by simp [dropUntilLastMem])
  | cons u us ih =>
    unfold dropUntilLastMem at hv
    split_ifs at hv with htail hu
    · exact ((dropUntilLastMem_eq_nil_iff S us).mp htail) v hv
    · simp at hv
    · exact ih hv

private theorem takeToFirstMem_prefix (S : Finset V) :
    ∀ p, takeToFirstMem S p <+: p
  | [] => ⟨[], rfl⟩
  | v :: vs => by
    unfold takeToFirstMem
    split_ifs with hv
    · exact ⟨vs, rfl⟩
    · obtain ⟨t, ht⟩ := takeToFirstMem_prefix S vs
      exact ⟨t, by simp [ht]⟩

private theorem head?_takeToFirstMem (S : Finset V) {p : List V} (hp : p ≠ []) :
    (takeToFirstMem S p).head? = p.head? := by
  cases p with
  | nil => exact absurd rfl hp
  | cons v vs =>
    unfold takeToFirstMem
    split_ifs <;> rfl

private theorem takeToFirstMem_of_exists_mem (S : Finset V) :
    ∀ p, (∃ v ∈ p, v ∈ S) → ∃ v ∈ S, (takeToFirstMem S p).getLast? = some v
  | [], h => by simp at h
  | v :: vs, h => by
    unfold takeToFirstMem
    split_ifs with hv
    · exact ⟨v, hv, rfl⟩
    · have hvs : ∃ w ∈ vs, w ∈ S := by
        obtain ⟨w, hw, hwS⟩ := h
        rcases List.mem_cons.mp hw with rfl | hw
        · exact absurd hwS hv
        · exact ⟨w, hw, hwS⟩
      obtain ⟨w, hwS, hw⟩ := takeToFirstMem_of_exists_mem S vs hvs
      have hne : takeToFirstMem S vs ≠ [] := by
        intro hempty
        simp [hempty] at hw
      cases htake : takeToFirstMem S vs with
      | nil => exact absurd htake hne
      | cons x xs =>
        rw [htake, List.getLast?_cons_cons]
        exact ⟨w, hwS, by simpa [htake] using hw⟩

private theorem not_mem_of_mem_takeToFirstMem_of_ne_getLast (S : Finset V) :
    ∀ p {v : V}, v ∈ takeToFirstMem S p → (takeToFirstMem S p).getLast? ≠ some v → v ∉ S
  | [], _, h, _ => by exact absurd h (by simp [takeToFirstMem])
  | u :: us, v, hv, hne => by
    unfold takeToFirstMem at hv hne
    split_ifs at hv hne with hu
    · have hv' : v = u := List.mem_singleton.mp hv
      exact hne (by simp only [hv', List.getLast?_singleton])
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact hu
      · apply not_mem_of_mem_takeToFirstMem_of_ne_getLast S us hv
        intro hlast
        apply hne
        cases htake : takeToFirstMem S us with
        | nil => simp [htake] at hlast
        | cons w ws => simp [htake, hlast]

private theorem mem_tail_of_mem_prefix_of_ne_head {q s : List V} (h : q <+: s) {v : V}
    (hv : v ∈ q) (hne : s.head? ≠ some v) : v ∈ s.tail := by
  obtain ⟨t, rfl⟩ := h
  cases q with
  | nil => simp at hv
  | cons u us =>
    simp only [List.head?_cons, Option.some.injEq] at hne
    rcases List.mem_cons.mp hv with rfl | hv
    · exact absurd rfl hne
    · exact List.mem_append_left _ hv

/-- The last-`A` then first-`B` shortcut of a duplicate-free `A`-to-`B` walk is a strict
`A`–`B` path, and its vertices are vertices of the walk. -/
private theorem isABDipath_abShortcut {G : Digraph V} {A B : Finset V} {p : List V}
    (hnd : p.Nodup) (ha : ∃ a ∈ A, p.head? = some a) (hb : ∃ b ∈ B, p.getLast? = some b)
    (hadj : ∀ e ∈ pathArcs p, G.Adj e.1 e.2) :
    IsABDipath G A B (abShortcut A B p) ∧ ∀ v ∈ abShortcut A B p, v ∈ p := by
  obtain ⟨a, haA, hhead⟩ := ha
  obtain ⟨b, hbB, hlast⟩ := hb
  have hpne : p ≠ [] := by
    intro h
    simp [h] at hhead
  have hA : ∃ v ∈ p, v ∈ A := by
    refine ⟨a, ?_, haA⟩
    rw [List.head?_eq_some_head hpne] at hhead
    exact hhead ▸ List.head_mem hpne
  have hsne : dropUntilLastMem A p ≠ [] := by
    intro h
    obtain ⟨v, hv, hvA⟩ := hA
    exact ((dropUntilLastMem_eq_nil_iff A p).mp h) v hv hvA
  have hsuf := dropUntilLastMem_suffix A p
  have hheadS : ∃ a ∈ A, (dropUntilLastMem A p).head? = some a := by
    have hsome := List.head?_eq_some_head hsne
    exact ⟨_, head_mem_dropUntilLastMem A p hsome, hsome⟩
  have hlastS : (dropUntilLastMem A p).getLast? = some b := by
    rw [getLast?_dropUntilLastMem A p hsne, hlast]
  have hB : ∃ v ∈ dropUntilLastMem A p, v ∈ B := by
    have hsne' : dropUntilLastMem A p ≠ [] := hsne
    rw [List.getLast?_eq_some_getLast hsne'] at hlastS
    exact ⟨_, List.getLast_mem hsne', hlastS ▸ hbB⟩
  obtain ⟨b', hb'B, hlastQ⟩ := takeToFirstMem_of_exists_mem B _ hB
  have hpref := takeToFirstMem_prefix B (dropUntilLastMem A p)
  have hqne : takeToFirstMem B (dropUntilLastMem A p) ≠ [] := by
    intro h
    simp [h] at hlastQ
  have hheadQ : (abShortcut A B p).head? = (dropUntilLastMem A p).head? :=
    head?_takeToFirstMem B hsne
  obtain ⟨a', ha'A, hheadS'⟩ := hheadS
  refine ⟨⟨nodup_of_prefix hpref (nodup_of_suffix hsuf hnd), ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact ⟨a', ha'A, hheadQ.trans hheadS'⟩
  · exact ⟨b', hb'B, hlastQ⟩
  · intro v hv hneHead hneLast
    refine ⟨?_, not_mem_of_mem_takeToFirstMem_of_ne_getLast B _ hv hneLast⟩
    have hvTail : v ∈ (dropUntilLastMem A p).tail :=
      mem_tail_of_mem_prefix_of_ne_head hpref hv (by
        rw [← hheadQ]
        exact hneHead)
    exact not_mem_tail_dropUntilLastMem A p hvTail
  · intro e he
    exact hadj e (mem_pathArcs_of_suffix hsuf (mem_pathArcs_of_prefix hpref he))
  · intro v hv
    have hvS : v ∈ dropUntilLastMem A p := by
      obtain ⟨t, rfl⟩ := hpref
      exact List.mem_append_left _ hv
    obtain ⟨t, rfl⟩ := hsuf
    exact List.mem_append_right _ hvS

end Shortcut

/-! ### Super-source reduction -/

private abbrev abSource {V : Type*} : V ⊕ Fin 2 := Sum.inr 0

private abbrev abSink {V : Type*} : V ⊕ Fin 2 := Sum.inr 1

private theorem abSource_ne_abSink : (abSource : V ⊕ Fin 2) ≠ abSink := by
  intro h
  exact Fin.zero_ne_one (Sum.inr_injective h)

/-- `G` with a super-source into `A` and a super-sink out of `B`. -/
private def abDigraph (G : Digraph V) (A B : Finset V) : Digraph (V ⊕ Fin 2) where
  Adj
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inr i, Sum.inl v => i = 0 ∧ v ∈ A
    | Sum.inl v, Sum.inr i => i = 1 ∧ v ∈ B
    | _, _ => False

private theorem not_adj_abSource_abSink (G : Digraph V) (A B : Finset V) :
    ¬ (abDigraph G A B).Adj abSource abSink := by
  simp [abDigraph, abSource, abSink]

private theorem inr_eq_abSource_or_abSink (i : Fin 2) :
    Sum.inr i = (abSource : V ⊕ Fin 2) ∨ Sum.inr i = abSink := by
  match h : i.val with
  | 0 => exact Or.inl (congrArg Sum.inr (Fin.ext h))
  | 1 => exact Or.inr (congrArg Sum.inr (Fin.ext h))
  | n + 2 =>
    have := i.isLt
    rw [h] at this
    exact absurd this (Nat.not_lt.mpr (Nat.le_add_left 2 n))

private def ofInlList : List (V ⊕ Fin 2) → List V
  | [] => []
  | Sum.inl v :: xs => v :: ofInlList xs
  | Sum.inr _ :: xs => ofInlList xs

private theorem map_ofInlList_of_forall_inl {l : List (V ⊕ Fin 2)}
    (h : ∀ x ∈ l, ∃ v, x = Sum.inl v) : l = (ofInlList l).map Sum.inl := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨v, rfl⟩ := h x List.mem_cons_self
    simp [ofInlList, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

private theorem mem_ofInlList {l : List (V ⊕ Fin 2)} {v : V}
    (h : ∀ x ∈ l, ∃ w, x = Sum.inl w) : v ∈ ofInlList l ↔ Sum.inl v ∈ l := by
  induction l with
  | nil => simp [ofInlList]
  | cons x xs ih =>
    obtain ⟨w, rfl⟩ := h x List.mem_cons_self
    simp [ofInlList, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

private theorem nodup_ofInlList {l : List (V ⊕ Fin 2)} (hl : l.Nodup)
    (h : ∀ x ∈ l, ∃ v, x = Sum.inl v) : (ofInlList l).Nodup := by
  induction l with
  | nil => simp [ofInlList]
  | cons x xs ih =>
    obtain ⟨v, rfl⟩ := h x List.mem_cons_self
    rw [ofInlList, List.nodup_cons] at hl ⊢
    refine ⟨?_, ih hl.2 (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩
    intro hv
    exact hl.1 ((mem_ofInlList fun y hy => h y (List.mem_cons_of_mem _ hy)).mp hv)

private theorem map_inl_ne_nil {p : List V} (hp : p ≠ []) : p.map Sum.inl ≠ [] := by
  cases p <;> simp_all

private theorem head_map_inl {p : List V} (hp : p ≠ []) :
    (p.map Sum.inl).head (map_inl_ne_nil hp) = Sum.inl (p.head hp) := by
  cases p with
  | nil => exact absurd rfl hp
  | cons a rest => rfl

private theorem getLast_map_inl {p : List V} (hp : p ≠ []) :
    (p.map Sum.inl).getLast (map_inl_ne_nil hp) = Sum.inl (p.getLast hp) := by
  induction p with
  | nil => exact absurd rfl hp
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      simp only [List.map_cons]
      rw [getLast_cons_cons]
      exact ih (List.cons_ne_nil _ _)

private theorem pathArcs_map_inl (p : List V) :
    pathArcs (p.map Sum.inl) =
      (pathArcs p).map fun e => (Sum.inl e.1, Sum.inl e.2) := by
  induction p with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      simp [List.map_cons, pathArcs_cons_cons, ih]

/-- An `s`–`t` path in the augmented digraph is a super-source, an original walk from `A` to
`B`, and the super-sink. -/
private theorem exists_r_of_isDipath {G : Digraph V} {A B : Finset V}
    {q : List (V ⊕ Fin 2)} (hp : IsDipath (abDigraph G A B) abSource abSink q) :
    ∃ r : List V, q = abSource :: (r.map Sum.inl ++ [abSink]) ∧ r.Nodup ∧
      (∃ a ∈ A, r.head? = some a) ∧ (∃ b ∈ B, r.getLast? = some b) ∧
      ∀ e ∈ pathArcs r, G.Adj e.1 e.2 := by
  obtain ⟨hnd, hhead, hlast, hadj⟩ := hp
  have hqne : q ≠ [] := by
    intro h
    simp [h] at hhead
  have hhead' : q.head hqne = abSource := by
    rw [List.head?_eq_some_head hqne] at hhead
    exact Option.some.inj hhead
  have hlast' : q.getLast hqne = abSink := by
    rw [List.getLast?_eq_some_getLast hqne] at hlast
    exact Option.some.inj hlast
  cases q with
  | nil => exact absurd rfl hqne
  | cons x rest =>
    have hx : x = abSource := by simpa using hhead'
    subst hx
    have hrest : rest ≠ [] := by
      intro h
      simp [h] at hlast'
    have hlastRest : rest.getLast hrest = abSink := by
      simpa [getLast_cons_of_ne_nil] using hlast'
    have hrestEq := eq_dropLast_append_getLast rest hrest
    set mid := rest.dropLast
    have hsrcMid : abSource ∉ mid := by
      have hsrcRest : abSource ∉ rest := (List.nodup_cons.mp hnd).1
      intro h
      exact hsrcRest (by
        rw [hrestEq]
        exact List.mem_append_left _ h)
    have hsnkMid : abSink ∉ mid := by
      have hndRest : rest.Nodup := (List.nodup_cons.mp hnd).2
      rw [hrestEq] at hndRest
      intro h
      exact (List.nodup_append.mp hndRest).2.2 h (by simp [hlastRest])
    have hmidNe : mid ≠ [] := by
      intro hmid
      have hadjST : (abDigraph G A B).Adj abSource abSink := by
        have he : (abSource, abSink) ∈ pathArcs (abSource :: rest) := by
          have : rest = [abSink] := by
            rw [hrestEq, hmid, hlastRest]
            simp
          simp [this, pathArcs_cons_cons]
        exact hadj _ he
      exact not_adj_abSource_abSink G A B hadjST
    have hall : ∀ x ∈ mid, ∃ v, x = Sum.inl v := by
      intro y hy
      cases y with
      | inl v => exact ⟨v, rfl⟩
      | inr i =>
        rcases inr_eq_abSource_or_abSink i with h | h
        · exact absurd (h ▸ hy) hsrcMid
        · exact absurd (h ▸ hy) hsnkMid
    refine ⟨ofInlList mid, ?_, nodup_ofInlList ?_ hall, ?_, ?_, ?_⟩
    · rw [← map_ofInlList_of_forall_inl hall, ← hrestEq, hlastRest]
    · rw [← map_ofInlList_of_forall_inl hall]
      have hndRest : rest.Nodup := (List.nodup_cons.mp hnd).2
      rw [hrestEq] at hndRest
      exact (List.nodup_append.mp hndRest).1
    · have hfst : (abSource, mid.head hmidNe) ∈ pathArcs (abSource :: rest) := by
        have hform : rest = mid.head hmidNe :: (mid.tail ++ [abSink]) := by
          have hcons := List.cons_head_tail hmidNe
          rw [hrestEq, ← hcons, hlastRest, List.cons_append]
        rw [hform, pathArcs_cons_cons]
        exact List.mem_cons_self
      have hadjFst := hadj _ hfst
      cases hheadMid : mid.head hmidNe with
      | inr i =>
        have hy : Sum.inr i ∈ mid := by
          rw [← hheadMid]
          exact List.head_mem hmidNe
        rcases inr_eq_abSource_or_abSink i with h | h
        · exact absurd (h ▸ hy) hsrcMid
        · exact absurd (h ▸ hy) hsnkMid
      | inl a =>
        have ha : a ∈ A := by
          simpa [abDigraph, abSource, hheadMid] using hadjFst
        refine ⟨a, ha, ?_⟩
        have hcons : mid = Sum.inl a :: mid.tail := by
          rw [← List.cons_head_tail hmidNe, hheadMid]
        simp [hcons, ofInlList]
    · have hgl : (mid.getLast hmidNe, abSink) ∈ pathArcs (abSource :: rest) := by
        have hneCons : abSource :: mid ≠ [] := List.cons_ne_nil _ _
        have happ : abSource :: rest = (abSource :: mid) ++ [abSink] := by
          simp [hrestEq, hlastRest]
        have hget : ((abSource :: mid) ++ [abSink]).getLast (by simp) = abSink :=
          getLast_append_singleton _ _
        have hmem := pathArcs_append_singleton (p := abSource :: mid)
          (x := (abSource :: mid).getLast hneCons) (y := abSink) hneCons
          (by rw [List.getLast?_eq_some_getLast hneCons])
        rw [happ]
        rw [hmem]
        have hlastMid : (abSource :: mid).getLast hneCons = mid.getLast hmidNe :=
          getLast_cons_of_ne_nil _ _ hmidNe
        rw [hlastMid]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have hadjLast := hadj _ hgl
      cases hlastMid : mid.getLast hmidNe with
      | inr i =>
        have hy : Sum.inr i ∈ mid := by
          rw [← hlastMid]
          exact List.getLast_mem hmidNe
        rcases inr_eq_abSource_or_abSink i with h | h
        · exact absurd (h ▸ hy) hsrcMid
        · exact absurd (h ▸ hy) hsnkMid
      | inl b =>
        have hb : b ∈ B := by
          simpa [abDigraph, abSink, hlastMid] using hadjLast
        refine ⟨b, hb, ?_⟩
        have hmap : mid = (ofInlList mid).map Sum.inl := map_ofInlList_of_forall_inl hall
        have hrne : ofInlList mid ≠ [] := by
          intro h
          apply hmidNe
          simpa [h] using hmap.symm
        have hget : mid.getLast hmidNe = Sum.inl ((ofInlList mid).getLast hrne) := by
          rw [hmap, getLast_map_inl hrne]
        rw [hlastMid] at hget
        have hbEq : b = (ofInlList mid).getLast hrne := Sum.inl_injective hget
        rw [List.getLast?_eq_some_getLast hrne, hbEq]
    · intro e he
      have hmap : mid = (ofInlList mid).map Sum.inl := map_ofInlList_of_forall_inl hall
      have heMid : (Sum.inl e.1, Sum.inl e.2) ∈ pathArcs mid := by
        rw [hmap, pathArcs_map_inl]
        exact List.mem_map_of_mem _ he
      have happend := pathArcs_append_singleton (p := mid) (x := mid.getLast hmidNe)
        (y := abSink) hmidNe (by rw [List.getLast?_eq_some_getLast hmidNe])
      have heAppend : (Sum.inl e.1, Sum.inl e.2) ∈ pathArcs (mid ++ [abSink]) := by
        rw [happend]
        exact List.mem_append_left _ heMid
      have hform : rest = mid ++ [abSink] := by rw [hrestEq, hlastRest]
      have hsub : (Sum.inl e.1, Sum.inl e.2) ∈ pathArcs (abSource :: rest) := by
        rw [← hform] at heAppend
        cases hrestCons : rest with
        | nil => exact absurd hrestCons hrest
        | cons y ys =>
          rw [hrestCons, pathArcs_cons_cons]
          exact List.mem_cons_of_mem _ (by simpa [hrestCons] using heAppend)
      simpa [abDigraph] using hadj _ hsub

private theorem exists_isABDipath_of_isDipath [DecidableEq V] {G : Digraph V} {A B : Finset V}
    {q : List (V ⊕ Fin 2)} (hp : IsDipath (abDigraph G A B) abSource abSink q) :
    ∃ p, IsABDipath G A B p ∧ ∀ v ∈ p, Sum.inl v ∈ q := by
  obtain ⟨r, hq, hnd, ha, hb, hadj⟩ := exists_r_of_isDipath hp
  obtain ⟨hp, hsub⟩ := isABDipath_abShortcut hnd ha hb hadj
  refine ⟨abShortcut A B r, hp, fun v hv => ?_⟩
  have hvq : Sum.inl v ∈ r.map Sum.inl := List.mem_map_of_mem _ (hsub hv)
  simp [hq, hvq]

private theorem isDipath_extend {G : Digraph V} {A B : Finset V} {p : List V}
    (hp : IsABDipath G A B p) :
    IsDipath (abDigraph G A B) abSource abSink
      (abSource :: (p.map Sum.inl ++ [abSink])) := by
  obtain ⟨hnd, ⟨a, ha, hhead⟩, ⟨b, hb, hlast⟩, -, hadj⟩ := hp
  have hpne : p ≠ [] := by
    intro h
    simp [h] at hhead
  have hhead' : p.head hpne = a := by
    rw [List.head?_eq_some_head hpne] at hhead
    exact Option.some.inj hhead
  have hlast' : p.getLast hpne = b := by
    rw [List.getLast?_eq_some_getLast hpne] at hlast
    exact Option.some.inj hlast
  have hmapnd : (p.map Sum.inl).Nodup := List.Nodup.map Sum.inl_injective hnd
  have hsrc : abSource ∉ p.map Sum.inl := by
    intro h
    obtain ⟨_, -, hx⟩ := List.mem_map.mp h
    exact Sum.noConfusion (by simpa [abSource] using hx)
  have hsnk : abSink ∉ p.map Sum.inl := by
    intro h
    obtain ⟨_, -, hx⟩ := List.mem_map.mp h
    exact Sum.noConfusion (by simpa [abSink] using hx)
  have happ : (p.map Sum.inl ++ [abSink]).Nodup := by
    rw [List.nodup_append, List.nodup_singleton]
    refine ⟨hmapnd, trivial, ?_⟩
    intro x hx hx'
    simp only [List.mem_singleton] at hx'
    exact hsnk (hx' ▸ hx)
  refine ⟨?_, rfl, ?_, ?_⟩
  · rw [List.nodup_cons]
    refine ⟨?_, happ⟩
    intro h
    rcases List.mem_append.mp h with h | h
    · exact hsrc h
    · simp [abSource, abSink] at h
  · rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), ← List.cons_append,
      getLast_append_singleton]
  · intro e he
    have hmne := map_inl_ne_nil hpne
    have happend := pathArcs_append_singleton (p := p.map Sum.inl)
      (x := Sum.inl (p.getLast hpne)) (y := abSink) hmne
      (by rw [List.getLast?_eq_some_getLast hmne, getLast_map_inl])
    have hsplit : p.map Sum.inl ++ [abSink] =
        (p.map Sum.inl).head hmne :: ((p.map Sum.inl).tail ++ [abSink]) := by
      conv_lhs => rw [← List.cons_head_tail hmne]
      simp
    have hform : pathArcs (abSource :: (p.map Sum.inl ++ [abSink])) =
        (abSource, Sum.inl (p.head hpne)) ::
          (pathArcs (p.map Sum.inl) ++ [(Sum.inl (p.getLast hpne), abSink)]) := by
      have hlist : abSource :: (p.map Sum.inl ++ [abSink]) =
          abSource :: (p.map Sum.inl).head hmne :: ((p.map Sum.inl).tail ++ [abSink]) := by
        rw [hsplit]
      rw [hlist, pathArcs_cons_cons, ← hsplit, happend, head_map_inl]
    rw [hform] at he
    rcases List.mem_cons.mp he with rfl | he
    · simp [abDigraph, abSource, hhead', ha]
    · rcases List.mem_append.mp he with he | he
      · rw [pathArcs_map_inl] at he
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        have := hadj e' he'
        simp [abDigraph, this]
      · simp only [List.mem_singleton] at he
        rw [he]
        simp [abDigraph, abSink, hlast', hb]

/-- **Menger's theorem, directed `A`–`B` vertex form, with a matching cut** ([Menger1927];
[Schrijver2017], §4.1, Theorem 4.1, reduced there to Corollary 4.1a). For finite `V` there are
`m` pairwise vertex-disjoint strict directed `A`–`B` paths and an `A`–`B` vertex cut with `m`
vertices. -/
theorem exists_vertexDisjoint_eq_isABVertexCut [Finite V] (G : Digraph V) (A B : Finset V) :
    ∃ (m : ℕ) (P : Fin m → List V), (∀ i, IsABDipath G A B (P i)) ∧ VertexDisjoint P ∧
      ∃ T : Finset V, IsABVertexCut G A B T ∧ T.card = m := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨m, Q, hQ, hdisj, T, hT, hTm⟩ := exists_internallyDisjoint_eq_isVertexCut
    (abDigraph G A B) abSource_ne_abSink (not_adj_abSource_abSink G A B)
  have hex : ∀ i, ∃ p, IsABDipath G A B p ∧ ∀ v ∈ p, Sum.inl v ∈ Q i :=
    fun i => exists_isABDipath_of_isDipath (hQ i)
  choose p hp hsub using hex
  have hdisj' : VertexDisjoint p := by
    intro i j hij v hv hvj
    rcases hdisj hij (Sum.inl v) (hsub i v hv) (hsub j v hvj) with h | h
    · simp [abSource] at h
    · simp [abSink] at h
  let T' : Finset V := Finset.univ.filter fun v => Sum.inl v ∈ T
  have hT' : IsABVertexCut G A B T' := by
    intro r hr
    have hdip := isDipath_extend hr
    obtain ⟨x, hx, hxT⟩ := hT.2.2 _ hdip
    have hx' : x ∈ r.map Sum.inl := by
      simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hx
      rcases hx with rfl | hx | rfl
      · exact absurd hxT hT.1
      · exact hx
      · exact absurd hxT hT.2.1
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx'
    exact ⟨v, hv, by simp [T', hxT]⟩
  have hcard : T'.card = T.card := by
    refine Finset.card_congr (fun v _ => Sum.inl v) ?_ ?_ ?_
    · intro v hv
      simp only [T', Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact hv
    · intro v _ w _ h
      exact Sum.inl_injective h
    · intro x hx
      cases x with
      | inl v =>
        refine ⟨v, ?_, rfl⟩
        simp [T', hx]
      | inr i =>
        rcases inr_eq_abSource_or_abSink i with h | h
        · exact absurd (h ▸ hx) hT.1
        · exact absurd (h ▸ hx) hT.2.1
  exact ⟨m, p, hp, hdisj', T', hT', hcard.trans hTm⟩

/-- **Menger's theorem, directed `A`–`B` vertex form** ([Menger1927]; [Schrijver2017], §4.1,
Theorem 4.1): `k` pairwise vertex-disjoint strict directed `A`–`B` paths exist if and only if
every `A`–`B` vertex cut has at least `k` vertices. -/
theorem exists_vertexDisjoint_iff_forall_isABVertexCut [Finite V] (G : Digraph V)
    (A B : Finset V) (k : ℕ) :
    (∃ P : Fin k → List V, (∀ i, IsABDipath G A B (P i)) ∧ VertexDisjoint P) ↔
      ∀ T : Finset V, IsABVertexCut G A B T → k ≤ T.card := by
  classical
  constructor
  · rintro ⟨P, hP, hdisj⟩ T hT
    exact card_le_card_of_vertexDisjoint_of_isABVertexCut hP hdisj hT
  · intro h
    obtain ⟨m, P, hP, hdisj, T, hT, hTm⟩ := exists_vertexDisjoint_eq_isABVertexCut G A B
    have hk : k ≤ m := hTm ▸ h T hT
    refine ⟨fun i => P (Fin.castLE hk i), fun i => hP _, fun i j hij => ?_⟩
    exact hdisj fun h' => hij (Fin.castLE_injective hk h')

/-- An `A`–`B` vertex cut of the symmetric digraph is a separator of the underlying simple
graph, and conversely. -/
theorem isABVertexCut_iff_isSeparator {G : SimpleGraph V} {A B T : Finset V} :
    IsABVertexCut (toDigraph G) A B T ↔
      G.IsSeparator (A : Set V) (B : Set V) (T : Set V) := by
  classical
  rw [SimpleGraph.isSeparator_iff_forall_isPath]
  constructor
  · intro hCut a ha b hb w hw
    have hdip := isDipath_support hw
    obtain ⟨hnd, hhead, hlast, hadj⟩ := hdip
    obtain ⟨hp, hsub⟩ := isABDipath_abShortcut (G := toDigraph G) hnd
      ⟨a, Finset.mem_coe.mp ha, hhead⟩ ⟨b, Finset.mem_coe.mp hb, hlast⟩ hadj
    obtain ⟨v, hv, hvT⟩ := hCut _ hp
    exact ⟨v, hsub hv, hvT⟩
  · intro hSep p hp
    obtain ⟨hnd, ⟨a, ha, hhead⟩, ⟨b, hb, hlast⟩, -, hadj⟩ := hp
    have hdip : IsDipath (toDigraph G) a b p := ⟨hnd, hhead, hlast, hadj⟩
    obtain ⟨w, hw, rfl⟩ := exists_walk_of_isDipath hdip
    exact hSep (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) w hw

/-- A single-terminal separator is an `A`–`B` separator of the singletons that avoids both
terminals ([Diestel2025], §1.4). -/
theorem isVertexSeparator_iff_isSeparator {G : SimpleGraph V} {u v : V} {T : Finset V} :
    IsVertexSeparator G u v T ↔
      G.IsSeparator ({u} : Set V) {v} (T : Set V) ∧ u ∉ T ∧ v ∉ T := by
  constructor
  · rintro ⟨hu, hv, h⟩
    refine ⟨?_, hu, hv⟩
    rw [SimpleGraph.isSeparator_iff_forall_isPath]
    intro a ha b hb w hw
    have ha' : a = u := by simpa using ha
    have hb' : b = v := by simpa using hb
    subst ha'
    subst hb'
    exact h w hw
  · rintro ⟨hsep, hu, hv⟩
    refine ⟨hu, hv, fun w hw => ?_⟩
    rw [SimpleGraph.isSeparator_iff_forall_isPath] at hsep
    exact hsep (by simp) (by simp) w hw

/-- **Menger's theorem, undirected `A`–`B` vertex form, with a matching cut** ([Menger1927];
[Diestel2025], Theorem 3.3.1, finite simple graphs). -/
theorem exists_vertexDisjoint_eq_isSeparator [Finite V] (G : SimpleGraph V) (A B : Finset V) :
    ∃ (m : ℕ) (P : Fin m → List V),
      (∀ i, IsABDipath (toDigraph G) A B (P i)) ∧ VertexDisjoint P ∧
        ∃ T : Finset V, G.IsSeparator (A : Set V) (B : Set V) (T : Set V) ∧ T.card = m := by
  obtain ⟨m, P, hP, hdisj, T, hT, hcard⟩ :=
    exists_vertexDisjoint_eq_isABVertexCut (toDigraph G) A B
  exact ⟨m, P, hP, hdisj, T, (isABVertexCut_iff_isSeparator).mp hT, hcard⟩

/-- **Menger's theorem, undirected `A`–`B` vertex form** ([Diestel2025], Theorem 3.3.1, finite
simple graphs): `k` pairwise vertex-disjoint strict `A`–`B` paths exist if and only if every
`A`–`B` separator has at least `k` vertices. -/
theorem exists_vertexDisjoint_iff_forall_isSeparator [Finite V] (G : SimpleGraph V)
    (A B : Finset V) (k : ℕ) :
    (∃ P : Fin k → List V, (∀ i, IsABDipath (toDigraph G) A B (P i)) ∧ VertexDisjoint P) ↔
      ∀ T : Finset V, G.IsSeparator (A : Set V) (B : Set V) (T : Set V) → k ≤ T.card := by
  rw [exists_vertexDisjoint_iff_forall_isABVertexCut]
  constructor
  · intro h T hT
    exact h T (isABVertexCut_iff_isSeparator.mpr hT)
  · intro h T hT
    exact h T (isABVertexCut_iff_isSeparator.mp hT)

/-- **Weak duality, undirected `A`–`B` form.** -/
theorem card_le_card_of_vertexDisjoint_of_isSeparator {G : SimpleGraph V} {A B : Finset V}
    {k : ℕ} {P : Fin k → List V} (hP : ∀ i, IsABDipath (toDigraph G) A B (P i))
    (hdisj : VertexDisjoint P) {T : Finset V}
    (hT : G.IsSeparator (A : Set V) (B : Set V) (T : Set V)) : k ≤ T.card :=
  card_le_card_of_vertexDisjoint_of_isABVertexCut hP hdisj
    (isABVertexCut_iff_isSeparator.mpr hT)

end Cslib.Algorithms.Lean.MaxFlow
