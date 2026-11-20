/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryProperPredecessor

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryGlobalPredecessor

open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension

open SourcePrefixRows OrbitPrefixSupport OrdinaryProperPredecessor

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}

variable {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)

/-- One completed proper boundary, together with its common rendering grid. -/
structure Frame (n : ℕ) (G : Finset ExtOrd) (θ : ExtOrd) where
  completed : Completed I (n + 4) G θ
  card : A.card = n + 5
  left_card : B.card = n + 4
  right_lt : C.card < n + 4
  visible : ∀ z ∈ G, SelfVis (n + 4) z
  ceiling_visible : SelfVis (n + 4) θ
  ceiling_proper : θ ≠ ⊤
  ceiling_mem : θ ∈ G

namespace Frame

variable {I} {n : ℕ} {G : Finset ExtOrd} {θ : ExtOrd} (F : Frame I n G θ)

local notation "X" => Frame.completed F

abbrev height : n + 3 ≤ A.card := Nat.le_of_succ_le (Nat.le_of_succ_le F.card.ge)

abbrev carrier := CanonicalRecursiveContract.carrier (X).state.rows n F.height

abbrev stage := CanonicalRecursiveSemantics.state (X).state.rows (proper I X) n F.height

abbrev rows := F.stage.rows

abbrev old := CanonicalRecursiveInventory.boundary (X).state.rows (n + 3) F.height

abbrev patch := CanonicalRecursiveInventory.patch (X).state.rows (proper I X) (n + 3) F.height

def original : Cell I.boundary ↪o Cell F.carrier :=
  (X).state.original.trans F.old

theorem plan : F.carrier.plan = R :=
  (CanonicalRecursiveBoundaryTransport.plan_eq _ _ _).trans (X).state.plan

theorem consistent : F.rows.IsConsistent :=
  F.stage.consistent (X).state.consistent

theorem coded : F.rows.IsCoded :=
  CanonicalRecursiveCoding.coded _ (proper I X) (X).state.coded n F.height

/-- The full scope is stopped below N. Proper grade-N cells are retained. -/
theorem coverage (d : Cell F.carrier) :
    (∃ c, old F c = d) ∨
      F.carrier.scope d = A ∧ F.carrier.grade d ≤ n + 3 := by
  rcases RecursiveSourceCarrier.classify (X).state.carrier
    (CanonicalRecursiveInventory.Profile (X).state.rows) (n + 3) F.height d with
    ⟨c, rfl⟩ | ⟨j, _, hj, he⟩
  all_goals simp_all

theorem grade_bound (d : Cell F.carrier) : F.carrier.grade d ≤ n + 4 := by
  rcases coverage F d with ⟨c, rfl⟩ | ⟨_, hg⟩
  · exact (congrArg Prod.snd (F.patch.index c)).trans_le
      (OrdinaryRawScope.boundary_grade (X).state.rows (ready I X) F.card.le c)
  · omega

theorem full_below (d : Cell F.carrier) (hd : F.carrier.scope d = A) : F.carrier.grade d < n + 4 :=
  Nat.lt_succ_of_le (RecursiveSourceCarrier.full_grade _ _ (proper I X) (n + 3) F.height d hd)

theorem complete {J : Finset ι × ℕ} (hJ : J ∈ Plan.gradedPlan R)
    (hscope : J.1 ≠ A ∨ J.2 ≤ n + 3) : ∃ d, F.carrier.cell d = J := by
  rcases hscope with hJA | hj
  · obtain ⟨d, hd⟩ := OrdinaryProperPredecessor.complete I X hJ hJA
    exact ⟨old F d, (CanonicalRecursiveInventory.boundary_cell _ _ _ _).trans hd⟩
  · exact CanonicalRecursiveCoverage.complete_through (X).state.rows (n + 3)
      F.height (ready I X).complete J
      (by rwa [CanonicalRecursiveBoundaryTransport.plan_eq, (X).state.plan]) hj

theorem proper_lift {CI BJ : Finset ι × ℕ} (hCI : CI ∈ Plan.gradedPlan R)
    (hBJ : BJ ∈ Plan.gradedPlan R) (hJA : BJ.1 ≠ A) (h : GradedLe CI BJ) :
    CappedLift F.rows h := by
  apply CanonicalRecursiveBoundaryTransport.proper_lift _ (proper I X) n F.height h
    (fun hs => hJA (Finset.Subset.antisymm
      (I.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hBJ).1) hs))
  exact lifts I X CI BJ (by rwa [(X).state.plan]) (by rwa [(X).state.plan]) hJA h

/-- The binary facets are derived from this completed raw plan. The small
donor is not incorrectly used as the second tall facet. -/
theorem lower_lift {CI BJ : Finset ι × ℕ} (hCI : CI ∈ Plan.gradedPlan R)
    (hBJ : BJ ∈ Plan.gradedPlan R) (h : GradedLe CI BJ) (hj : BJ.2 ≤ n + 3) :
    CappedLift F.rows h := by
  obtain ⟨s, hs⟩ := AmalgamatedBoundaryPlan.exists_step (X).state.carrier.isPlan
    ((by omega : 2 ≤ n + 3).trans F.height)
  have hL := OrdinaryPlanScopeStep.left_height s (k := n + 4) F.card
  have hR := OrdinaryPlanScopeStep.right_height s (k := n + 4) F.card
  exact CanonicalRecursiveInitialized.lift (X).state.rows (proper I X)
    (lifts I X) (OrdinaryRawScope.left_mem s hs.symm) (OrdinaryRawScope.right_mem s hs.symm)
    (OrdinaryPlanScopeStep.left_proper s) (OrdinaryPlanScopeStep.right_proper s)
    (OrdinaryRawScope.overlap_mem s hs.symm) (OrdinaryRawScope.coverage s hs.symm)
    n F.height (by omega) (by omega)
    (fun S hS hSA j hj hjS _ => (ready I X).complete (S, j)
      (Plan.mem_gradedPlan.mpr ⟨hS, hj, hjS⟩) hSA)
    (by rwa [(X).state.plan]) (by rwa [(X).state.plan]) h hj

include F in
theorem left_ne : B ≠ A := by
  intro h
  have := F.left_card
  rw [h, F.card] at this
  omega

include F in
theorem right_ne : C ≠ A := by
  intro h
  have := F.right_lt
  rw [h, F.card] at this
  omega

def leftFace : ExactSemanticFace I.leftRows F.rows :=
  CanonicalRecursiveFace.face (OrdinaryProperPredecessor.leftFace I X)
    (fun h => F.left_ne (Finset.Subset.antisymm
      (I.isPlan.subset_of_mem (WholeDonorOrdinaryLift.left_mem I)) h))
    (proper I X) n F.height

def rightFace : ExactSemanticFace I.rightRows F.rows :=
  CanonicalRecursiveFace.face (OrdinaryProperPredecessor.rightFace I X)
    (fun h => F.right_ne (Finset.Subset.antisymm
      (I.isPlan.subset_of_mem (WholeDonorOrdinaryLift.right_mem I)) h))
    (proper I X) n F.height

theorem left_order : StrictMono F.leftFace.map :=
  F.old.strictMono.comp (OrdinaryProperPredecessor.left_order I X)

theorem right_order : StrictMono F.rightFace.map :=
  F.old.strictMono.comp (OrdinaryProperPredecessor.right_order I X)

/-- The decoder classification is preserved by the literal patch of old rows. -/
theorem classification : OrderedScopeRelocation.OwnerClassification F.rows F.original := by
  apply OrderedScopeRelocation.OwnerClassification.extend (X).state.rows (X).state.classification F.patch F.stage.row
  intro z
  exact (coverage F z).imp id (fun h => F.stage.full_short z h.1)

theorem mute
    (d : Cell F.carrier) (hg : F.carrier.grade d = n + 4)
    (hd : F.carrier.scope d ≠ B) :
    F.rows.E d ⟨d, GradedLe.refl _⟩ = ⊥ := by
  rcases coverage F d with ⟨c, rfl⟩ | ⟨_, hb⟩
  · have hc : (X).state.carrier.grade c = n + 4 := by
      simpa only [CellScheme.grade, CanonicalRecursiveInventory.boundary_cell] using hg
    have hscope : (X).state.carrier.scope c ≠ B := by
      simpa only [CellScheme.scope, CanonicalRecursiveInventory.boundary_cell] using hd
    exact (F.stage.row c ⟨c, GradedLe.refl _⟩).trans
      (OrdinaryProperPredecessor.nonprivate_mute I X F.card F.left_card F.right_lt c hc hscope)
  omega

variable {p : Cell I.boundary → ExtOrd} (hp : RespectsSemantics I.rows p) (hb : ∀ d, p d ≤ θ)

def render : Cell F.carrier → ExtOrd :=
  F.stage.sectionOf
    F.height (((X).state.lawful hp hb).toBelow (A, A.card))
    (fun d => ne_top_of_le_ne_top F.ceiling_proper ((X).state.bound hp hb d)) G θ

theorem readback (d : Cell I.boundary) :
    render F hp hb (original F d) = p d :=
  (F.stage.section_boundary
    F.height _ _ (fun z hz => selfVis_mono (F.visible z hz) (by omega))
    (selfVis_mono F.ceiling_visible (by omega)) ((X).state.original d)).trans ((X).state.readback hp hb d)

theorem lawful : RespectsSemantics F.rows (render F hp hb) := by
  apply (F.stage.section_lawful
    F.height _ _ (fun z hz => selfVis_mono (F.visible z hz) (by omega))
    (selfVis_mono F.ceiling_visible (by omega))).toRespects
  intro d
  exact ⟨F.carrier.scope_subset d,
    (F.grade_bound d).trans (Nat.le_of_succ_le F.card.ge)⟩

theorem bound (d : Cell F.carrier) : render F hp hb d ≤ θ :=
  F.stage.section_bound
    F.height _ _ (selfVis_mono F.ceiling_visible (by omega)) ((X).state.bound hp hb) d

theorem support (d : Cell F.carrier) :
    Supported (n + 4) (G : Set ExtOrd) p (render F hp hb d) :=
  (F.stage.section_supported
    F.height _ _ (by omega) F.ceiling_mem d).substitute F.visible ((X).state.support hp hb)

theorem agreement {q : Cell I.boundary → ExtOrd} (hq : RespectsSemantics I.rows q)
    (hqb : ∀ d, q d ≤ θ) {γ : ExtOrd} (hγ : γ ∈ G) (hγθ : γ ≤ θ) (he : Agree p q γ) :
    Agree (render F hp hb) (render F hq hqb) γ :=
  F.stage.section_agreement
    F.height _ _ _ _ (fun z hz => selfVis_mono (F.visible z hz) (by omega))
    (selfVis_mono F.ceiling_visible (by omega)) hγ hγθ ((X).state.agreement hp hb hq hqb hγ hγθ he)

end Frame

end

end VaughtConjecture.Knight.OrdinaryGlobalPredecessor
