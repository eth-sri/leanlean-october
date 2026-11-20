/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import InfinitaryLogic.Descriptive.KleeneBrouwer

@[expose] public section

namespace KleeneBrouwer

open Descriptive MeasureTheory Filter Topology Set

variable {X : Type*}

/-- The first coordinates of a list of `Nat.pair` codes. -/
private def fstList (l : List ℕ) : List ℕ := l.map fun n ↦ n.unpair.1

/-- The second coordinates of `l` form an initial segment of `y`. -/
private def SndAgrees (l : List ℕ) (y : ℕ → ℕ) : Prop :=
  ∀ i (h : i < l.length), l[i].unpair.2 = y i

/-- Pair a list with the initial segment of `y` of the same length. -/
private def pairList (s : List ℕ) (y : ℕ → ℕ) : List ℕ := s.mapIdx fun i a ↦ Nat.pair a (y i)

private theorem fstList_pairList (s : List ℕ) (y : ℕ → ℕ) : fstList (pairList s y) = s :=
  List.ext_getElem (by simp [fstList, pairList]) fun i _ _ ↦ by simp [fstList, pairList]

private theorem sndAgrees_pairList (s : List ℕ) (y : ℕ → ℕ) : SndAgrees (pairList s y) y :=
  fun i _ ↦ by simp [pairList]

/-- Pairing with a fixed sequence preserves proper prefixes. -/
private theorem properPrefix_pairList {s t : List ℕ} (y : ℕ → ℕ) (h : ProperPrefix s t) :
    ProperPrefix (pairList s y) (pairList t y) := by
  obtain ⟨⟨r, rfl⟩, hne⟩ := h
  refine ⟨by simp only [pairList, List.mapIdx_append]; exact List.prefix_append _ _,
    fun heq ↦ hne ?_⟩
  have hlen := congrArg List.length heq
  simp only [pairList, List.length_mapIdx, List.length_append] at hlen
  aesop

/-- The nodes of the witness tree: codes of pairs `(s, u)` such that some `y` extending `u` has
`s ∈ T (f y)`. -/
private def witnessNodes (f : (ℕ → ℕ) → X) (T : X → tree ℕ) : Set (List ℕ) :=
  {l | ∃ y, SndAgrees l y ∧ fstList l ∈ T (f y)}

private theorem witnessNodes_prefix {f : (ℕ → ℕ) → X} {T : X → tree ℕ} ⦃l : List ℕ⦄ ⦃a : ℕ⦄
    (h : l ++ [a] ∈ witnessNodes f T) : l ∈ witnessNodes f T := by
  obtain ⟨y, hy, hmem⟩ := h
  refine ⟨y, fun i hi ↦ ?_, Tree.mem_of_prefix ?_ hmem⟩
  · have := hy i (by simp; omega)
    simp_all
  · simp [fstList]

/-- The witness tree ("tree of attempts") of `T` along `f`. -/
private def witnessTree (f : (ℕ → ℕ) → X) (T : X → tree ℕ) : tree ℕ :=
  ⟨witnessNodes f T, fun _ _ h ↦ witnessNodes_prefix h⟩

private theorem mem_witnessTree {f : (ℕ → ℕ) → X} {T : X → tree ℕ} {l : List ℕ} :
    l ∈ witnessTree f T ↔ ∃ y, SndAgrees l y ∧ fstList l ∈ T (f y) := Iff.rfl

/-- **The witness tree is well-founded**: a branch would converge, through closed node sets, to an
infinite branch of a tree of the family. -/
private theorem wellFounded_witnessTree [TopologicalSpace X] {f : (ℕ → ℕ) → X}
    (hf : Continuous f) (T : X → tree ℕ) (hT : ∀ s : List ℕ, IsClosed {x | s ∈ T x})
    (hwf : ∀ x ∈ range f, WellFounded (extBelow (T x))) :
    WellFounded (extBelow (witnessTree f T)) := by
  rw [wellFounded_extBelow_iff_not_hasInfiniteBranch, hasInfiniteBranch_iff_exists_seq]
  rintro ⟨z, hz⟩
  -- the branch splits into first coordinates `x` and second coordinates `y`
  set x : ℕ → ℕ := fun i ↦ (z i).unpair.1 with hx
  set y : ℕ → ℕ := fun i ↦ (z i).unpair.2
  -- a witness `w n` at every stage `n`
  choose w hw hmem using fun n ↦ mem_witnessTree.mp (hz n)
  have hfst : ∀ n, fstList (List.ofFn fun i : Fin n ↦ z i) = List.ofFn fun i : Fin n ↦ x i :=
    fun n ↦ by simp [fstList, hx, List.map_ofFn, Function.comp_def]
  have hagree : ∀ n i, i < n → w n i = y i := fun n i hi ↦ by
    have := hw n i (by simpa using hi)
    grind
  -- the witnesses converge to `y` in Baire space
  have htend : Tendsto w atTop (𝓝 y) :=
    tendsto_pi_nhds.mpr fun i ↦ tendsto_atTop_of_eventually_const (i₀ := i + 1)
      fun n hn ↦ hagree n i (by omega)
  -- the limit step: fix `k`; every stage `n ≥ k` puts `w n` in one closed set
  have hbranch : ∀ k, (List.ofFn fun i : Fin k ↦ x i) ∈ T (f y) := by
    intro k
    have hclosed : IsClosed {v : ℕ → ℕ | (List.ofFn fun i : Fin k ↦ x i) ∈ T (f v)} :=
      (hT _).preimage hf
    refine hclosed.mem_of_tendsto htend (eventually_atTop.mpr ⟨k, fun n hn ↦ ?_⟩)
    have hn : (List.ofFn fun i : Fin n ↦ x i) ∈ T (f (w n)) := hfst n ▸ hmem n
    have htake : (List.ofFn fun i : Fin n ↦ x i).take k = List.ofFn fun i : Fin k ↦ x i :=
      List.ext_getElem (by simp; omega) fun i _ _ ↦ by simp
    exact htake ▸ Tree.mem_of_prefix (List.take_prefix _ _) hn
  exact (wellFounded_extBelow_iff_not_hasInfiniteBranch _).mp (hwf (f y) (mem_range_self y))
    ((hasInfiniteBranch_iff_exists_seq _).mpr ⟨x, hbranch⟩)

/-- The tree of the parameter `f y` maps into the witness tree, pairing each node with the
matching initial segment of `y`. -/
private def witnessHom (f : (ℕ → ℕ) → X) (T : X → tree ℕ) (y : ℕ → ℕ) :
    extBelow (T (f y)) →r extBelow (witnessTree f T) where
  toFun s := ⟨pairList s y, mem_witnessTree.mpr
    ⟨y, sndAgrees_pairList _ y, by rw [fstList_pairList]; exact s.2⟩⟩
  map_rel' h := properPrefix_pairList y h

/-- **Boundedness for analytic families of well-founded trees.**  If `A` is analytic, every node
set `{x | s ∈ T x}` is closed, and `T x` is well-founded for `x ∈ A`, then one countable ordinal
strictly bounds the heights of all the trees `T x` with `x ∈ A`. -/
theorem analytic_tree_rank_bounded [TopologicalSpace X] {A : Set X} (hA : AnalyticSet A)
    (T : X → tree ℕ) (hT : ∀ s : List ℕ, IsClosed {x | s ∈ T x})
    (hwf : ∀ x ∈ A, WellFounded (extBelow (T x))) :
    ∃ β : Ordinal.{0}, β < Ordinal.omega 1 ∧
      ∀ x (hx : x ∈ A), @treeHeight (T x) (hwf x hx) < β := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨f, hf, rfl⟩
  · exact ⟨0, Ordinal.omega_pos 1, fun _ hx ↦ hx.elim⟩
  have : WellFounded (extBelow (witnessTree f T)) := wellFounded_witnessTree hf T hT hwf
  refine ⟨treeHeight (witnessTree f T) + 1, ?_, ?_⟩
  · rw [← Order.succ_eq_add_one]
    exact (Cardinal.isSuccLimit_omega 1).succ_lt (treeHeight_lt_omega1 _)
  · rintro _ ⟨y, rfl⟩
    have := hwf (f y) (mem_range_self y)
    exact (treeHeight_le_of_relHom (witnessHom f T y)).trans_lt (lt_add_one _)

end KleeneBrouwer
