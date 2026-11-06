
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.OrdinaryProperPredecessor

/-! # The ordinary global predecessor, stopping below the final gate

Complete every proper scope first, then add full-scope grades through N-1.
Retained private grade-N owners are never subjected to a grade-(N-1) bound.
This module treats N = n+4, using the initialized recursive seed.
-/

namespace VaughtConjecture.Knight.OrdinaryGlobalPredecessor
open AmalgamationPlan    CoatomBoundaryExtension
open SourcePrefixRows OrbitPrefixSupport OrdinaryProperPredecessor
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι}
variable {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)
variable (n : ℕ) {G : Finset ExtOrd} {θ : ExtOrd}
variable (X : Completed I (n + 4) G θ) (hcard : A.card = n + 5)

include hcard in
omit [DecidableEq ι] in
variable {n} in
theorem height : n + 3 ≤ A.card := by omega
local notation "height₀" => height hcard

abbrev carrier := CanonicalRecursiveContract.carrier X.state.rows n (height₀)
abbrev rows := CanonicalRecursiveSemantics.rows X.state.rows (proper) n (height₀)
abbrev old := CanonicalRecursiveInventory.boundary X.state.rows (n + 3) (height₀)
local notation "carrier₀" => carrier I n X hcard

local notation "old₀" => old I n X hcard

def original : Cell I.boundary ↪o Cell (carrier₀) :=
  X.state.original.trans (old₀)

local notation "original₀" => original I n X hcard



local notation "rows₀" => rows I n X hcard



theorem plan : (carrier₀).plan = R :=
  (CanonicalRecursiveBoundaryTransport.plan_eq _ _ _).trans X.state.plan

theorem consistent : (rows₀).IsConsistent :=
  CanonicalRecursiveSemantics.consistent _ (proper) X.state.consistent

theorem coded : (rows₀).IsCoded :=
  CanonicalRecursiveCoding.coded _ (proper) X.state.coded

/-- The full scope is stopped below N. Proper grade-N cells are retained. -/
theorem coverage d :
    (∃ c, old₀ c = d) ∨
      (carrier₀).scope d = A ∧ (carrier₀).grade d ≤ n + 3 := by
  rcases RecursiveSourceCarrier.classify X.state.carrier
    (CanonicalRecursiveInventory.Profile X.state.rows) (n + 3) (height₀) d with
    ⟨c, rfl⟩ | ⟨j, _, hj, he⟩
  · exact Or.inl ⟨c, rfl⟩
  · simp_all

theorem grade_bound d : (carrier₀).grade d ≤ n + 4 := by
  rcases coverage I n X hcard d with ⟨c, rfl⟩ | ⟨_, hg⟩
  · change ((carrier₀).cell (old₀ c)).2 ≤ _
    rw [CanonicalRecursiveInventory.boundary_cell]
    have hs := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨X.state.carrier.scope_subset c, proper c⟩)
    have hg := X.state.carrier.grade_le_card_scope c
    change X.state.carrier.grade c ≤ _
    omega
  · omega

theorem complete {J} (hJ : J ∈ Plan.gradedPlan R)
    (hscope : J.1 ≠ A ∨ J.2 ≤ n + 3) : ∃ d, (carrier₀).cell d = J := by
  rcases hscope with hJA | hj
  · obtain ⟨d, hd⟩ := OrdinaryProperPredecessor.complete I X hJ hJA
    exact ⟨old₀ d, (CanonicalRecursiveInventory.boundary_cell _ _ _ _).trans hd⟩
  · exact CanonicalRecursiveCoverage.complete_through X.state.rows (n + 3)
      (height₀) (ready I X).complete J
      (by rwa [CanonicalRecursiveBoundaryTransport.plan_eq, X.state.plan]) hj

theorem proper_lift {CI BJ} (hCI : CI ∈ Plan.gradedPlan R)
    (hBJ : BJ ∈ Plan.gradedPlan R) (hJA : BJ.1 ≠ A) (h : GradedLe CI BJ) :
    CappedLift (rows₀) h := by
  apply CanonicalRecursiveBoundaryTransport.proper_lift _ proper n (height₀) h
    (fun hs => hJA (Finset.Subset.antisymm
      (I.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hBJ).1) hs))
  exact lifts I X CI BJ (by rwa [X.state.plan]) (by rwa [X.state.plan]) hJA h

/-- The binary facets are derived from this completed raw plan. The small
donor is not incorrectly used as the second tall facet. -/
theorem lower_lift {CI BJ} (hCI : CI ∈ Plan.gradedPlan R)
    (hBJ : BJ ∈ Plan.gradedPlan R) (h : GradedLe CI BJ) (hj : BJ.2 ≤ n + 3) :
    CappedLift (rows₀) h := by
  obtain ⟨s, hs⟩ := AmalgamatedBoundaryPlan.exists_step X.state.carrier.isPlan
    (by omega)
  have hL := OrdinaryPlanScopeStep.left_height s  hcard
  have hR := OrdinaryPlanScopeStep.right_height s  hcard
  exact CanonicalRecursiveInitialized.lift X.state.rows proper X.state.consistent
    (lifts I X) (OrdinaryRawScope.left_mem s hs.symm) (OrdinaryRawScope.right_mem s hs.symm)
    (OrdinaryPlanScopeStep.left_proper s) (OrdinaryPlanScopeStep.right_proper s)
    (OrdinaryRawScope.overlap_mem s hs.symm) (OrdinaryRawScope.coverage s hs.symm)
    n (height₀) (by omega) (by omega)
    (fun S hS hSA j hj hjS _ => (ready I X).complete (S, j)
      (Plan.mem_gradedPlan.mpr ⟨hS, hj, hjS⟩) hSA)
    (by rwa [X.state.plan]) (by rwa [X.state.plan]) h hj

def leftFace (hBA : B ≠ A) : ExactSemanticFace I.leftRows (rows₀) :=
  CanonicalRecursiveFace.face (OrdinaryProperPredecessor.leftFace I X)
    (fun h => hBA (Finset.Subset.antisymm
      (I.isPlan.subset_of_mem (WholeDonorOrdinaryLift.left_mem I)) h))
    (proper) n (height₀)

def rightFace (hCA : C ≠ A) : ExactSemanticFace I.rightRows (rows₀) :=
  CanonicalRecursiveFace.face (OrdinaryProperPredecessor.rightFace I X)
    (fun h => hCA (Finset.Subset.antisymm
      (I.isPlan.subset_of_mem (WholeDonorOrdinaryLift.right_mem I)) h))
    (proper) n (height₀)

theorem left_order (hBA : B ≠ A) : StrictMono (leftFace I n X hcard hBA).map :=
  (old₀).strictMono.comp (OrdinaryProperPredecessor.left_order I X)

theorem right_order (hCA : C ≠ A) : StrictMono (rightFace I n X hcard hCA).map :=
  (old₀).strictMono.comp (OrdinaryProperPredecessor.right_order I X)

theorem below_old c
    (d : (carrier₀).below ((carrier₀).cell (old₀ c))) :
    ∃ e : X.state.carrier.belowCell c, old₀ e.1 = d.1 := by
  rcases coverage I n X hcard d.1 with ⟨e, he⟩ | ⟨hs, _⟩
  · refine ⟨⟨e, ?_⟩, he⟩
    have hd := d.2
    rw [← he, CanonicalRecursiveInventory.boundary_cell,
      CanonicalRecursiveInventory.boundary_cell] at hd
    exact hd
  · have hd := d.2.1
    change (carrier₀).scope d.1 ⊆
      ((carrier₀).cell (old₀ c)).1 at hd
    rw [hs, CanonicalRecursiveInventory.boundary_cell] at hd
    exact (proper c (Finset.Subset.antisymm
      (X.state.carrier.scope_subset c) hd)).elim

/-- The decoder classification survives the final recursion as well as every
proper-scope installation. No shortness is imposed on inherited original rows. -/
theorem classification : OrderedScopeRelocation.OwnerClassification
    (rows I n X hcard) (original I n X hcard) := by
  intro z
  rcases coverage I n X hcard z with ⟨c, rfl⟩ | ⟨hs, _⟩
  · rcases X.state.classification c with hshort | horig
    · left
      intro d
      obtain ⟨e, he⟩ := below_old I n X hcard c d
      have hd : d = ⟨old I n X hcard e.1, by
          grind⟩ := Subtype.ext he.symm
      rw [hd, CanonicalRecursiveLiteralRows.row]
      change SharpWitnessComposition.Short
        ((carrier I n X hcard).cell (old I n X hcard c)).2 _
      rw [CanonicalRecursiveInventory.boundary_cell]
      exact hshort e
    · right
      intro d
      obtain ⟨e, he⟩ := below_old I n X hcard c d
      obtain ⟨x, hx⟩ := horig e
      exact ⟨x, (congrArg (old I n X hcard) hx).trans he⟩
  · exact Or.inl ((CanonicalRecursiveSemantics.state X.state.rows
      (proper) n (height hcard)).full_short z hs)

theorem nonprivate_mute (hB : B.card = n + 4) (hC : C.card < n + 4)
    d (hg : (carrier₀).grade d = n + 4)
    (hd : (carrier₀).scope d ≠ B) :
    (rows₀).E d ⟨d, GradedLe.refl _⟩ = ⊥ := by
  rcases coverage I n X hcard d with ⟨c, rfl⟩ | ⟨_, hb⟩
  · have hc : X.state.carrier.grade c = n + 4 := by
      simpa only [CellScheme.grade, CanonicalRecursiveInventory.boundary_cell] using hg
    have hscope  := by
      simpa only [CellScheme.scope, CanonicalRecursiveInventory.boundary_cell] using hd
    exact (CanonicalRecursiveLiteralRows.row X.state.rows proper n (height₀)
      c ⟨c, GradedLe.refl _⟩).trans
      (OrdinaryProperPredecessor.nonprivate_mute I X hcard hB hC c hc hscope)
  · omega

variable (hG : VisibleOn (n + 4) G) (hθ : SelfVis (n + 4) θ)
variable (htθ : θ ≠ ⊤) (hθG : θ ∈ G)
variable {p : CellLabels I.boundary} (hp : RespectsSemantics I.rows p) (hb : BoundedBy p θ)

local notation "state₀" => CanonicalRecursiveSemantics.state X.state.rows (proper) n (height hcard)

def render : CellLabels (carrier₀) :=
  (state₀).sectionOf
    (height₀) ((X.state.lawful hp hb).toBelow (A, A.card))
    (fun d => ne_top_of_le_ne_top htθ (X.state.bound hp hb d)) G θ

local notation "render₀" => render I n X hcard htθ hp hb

local notation "selfVis_mono₀" => selfVis_mono hθ (by omega)

include hG hθ in
theorem readback d :
    render₀ (original₀ d) = p d :=
  ((state₀).section_boundary
    (height₀) _ _ (fun z hz => selfVis_mono (hG z hz) (by omega))
    (selfVis_mono₀) (X.state.original d)).trans (X.state.readback hp hb d)

include hG hθ in
theorem lawful : RespectsSemantics (rows₀) (render₀) := by
  apply ((state₀).section_lawful
    (height₀) _ _ (fun z hz => selfVis_mono (hG z hz) (by omega))
    (selfVis_mono₀)).toRespects
  intro d
  exact ⟨(carrier₀).scope_subset d,
    (grade_bound I n X hcard d).trans (by omega)⟩

include hθ in
theorem bound d : render₀ d ≤ θ :=
  (state₀).section_bound
    (height₀) _ _ (selfVis_mono₀) (X.state.bound hp hb) d

include hG hθG in
theorem supported d :
    Supported (n + 4) (G : Set ExtOrd) p (render₀ d) :=
  ((state₀).section_supported
    (height₀) _ _ (by omega) hθG d).substitute hG (X.state.support hp hb)

include hG hθ in
theorem agreement {q} (hq : RespectsSemantics I.rows q)
    (hqb : BoundedBy q θ) {γ} (hγ : γ ∈ G) (hγθ : γ ≤ θ) (he : Agree p q γ) :
    Agree (render₀) (render I n X hcard htθ hq hqb) γ :=
  (state₀).section_agreement
    (height₀) _ _ _ _ (fun z hz => selfVis_mono (hG z hz) (by omega))
    (selfVis_mono₀) hγ hγθ (X.state.agreement hp hb hq hqb hγ hγθ he)

