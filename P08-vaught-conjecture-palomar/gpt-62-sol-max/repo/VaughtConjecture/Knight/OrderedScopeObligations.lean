/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrderedScopeSections

@[expose] public section

namespace VaughtConjecture.Knight.OrderedScopeRelocation

open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}

variable {D : CellScheme A} (sem : Semantics D) (hB : B ∈ D.plan) {k : ℕ}

variable (S : OrdinaryScopeOperator.Core (ScopeBoundary.rows D B hB sem) k)

variable (hsep : Separated (D := D) (B := B))

local notation "K" => carrier sem hB S

local notation "l" => old sem hB S

local notation "r" => localCell sem hB S

/-- All earlier targets not containing this new scope are literally unchanged. -/
theorem old_lower_exhaustive {J : Finset ι × ℕ} (hJ : ¬ B ⊆ J.1)
    (z : Cell K) (hz : GradedLe ((K).cell z) J) : ∃ d, l d = z := by
  rcases classify sem hB S z with hl | he
  · exact hl
  · exact (hJ (he ▸ hz.1)).elim

theorem old_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : ¬ B ⊆ J.1)
    (hb : CappedLift sem h) : CappedLift (rows sem hB S hsep) h :=
  (oldPatch sem hB S hsep).lift (row_old sem hB S hsep) h (old_lower_exhaustive sem hB S hJ) hb

theorem local_lift {I J : Finset ι × ℕ} (h : GradedLe I J)
    (hI : I ∈ Plan.gradedPlan D.plan) (hJ : J ∈ Plan.gradedPlan D.plan) (hJB : J.1 ⊆ B) :
    CappedLift (rows sem hB S hsep) h := by
  have memLocal (T : Finset ι × ℕ) (hT : T ∈ Plan.gradedPlan D.plan) (hTB : T.1 ⊆ B) :
      T ∈ Plan.gradedPlan S.carrier.plan := by
    obtain ⟨hp, hg, hc⟩ := Plan.mem_gradedPlan.mp hT
    rw [S.plan]
    exact Plan.mem_gradedPlan.mpr
      ⟨Finset.mem_inter.mpr ⟨hp, Finset.mem_powerset.mpr hTB⟩, hg, hc⟩
  exact (localFace sem hB S hsep).lift hJB (memLocal I hI (h.1.trans hJB))
    (memLocal J hJ hJB) h S.bountiful

/-- The selected-display decoder needs this alternative, not global shortness. -/
def OwnerClassification {X : Type*} (original : X → Cell D) : Prop :=
  ∀ c : Cell D, (∀ d, SharpWitnessComposition.Short (D.grade c) (sem.E c d)) ∨
    ∀ d : D.below (D.cell c), ∃ x, original x = d.1

theorem short_at {Out : CellScheme B} {out : Semantics Out}
    (P : SemanticPatch D Out) (hrows : P.Preserves sem out) (c : Cell D)
    (hshort : ∀ d, SharpWitnessComposition.Short (D.grade c) (sem.E c d))
    (d : Out.below (Out.cell (P.map c))) : SharpWitnessComposition.Short (Out.grade (P.map c)) (out.E (P.map c) d) := by
  obtain ⟨e, rfl⟩ := (P.ownerEquiv c).surjective d
  have he : out.E (P.map c) (P.ownerEquiv c e) = sem.E c e := hrows c e
  rw [he, CellScheme.grade, P.index]
  exact hshort e

theorem OwnerClassification.extend {Out : CellScheme B} {out : Semantics Out} {X : Type*}
    {original : X → Cell D} (hc : OwnerClassification sem original)
    (P : SemanticPatch D Out) (hrows : P.Preserves sem out)
    (cover : ∀ z, (∃ c, P.map c = z) ∨ ∀ d, SharpWitnessComposition.Short (Out.grade z) (out.E z d)) :
    OwnerClassification out (P.map ∘ original) := by
  intro z
  rcases cover z with ⟨c, rfl⟩ | hs
  · rcases hc c with hs | ho
    · exact Or.inl (short_at sem P hrows c hs)
    · right
      intro d
      obtain ⟨e, rfl⟩ := (P.ownerEquiv c).surjective d
      obtain ⟨x, hx⟩ := ho e
      exact ⟨x, congrArg P.map hx⟩
  · exact Or.inl hs

theorem ownerClassification {X : Type*} (original : X → Cell D)
    (hc : OwnerClassification sem original) :
    OwnerClassification (rows sem hB S hsep) (l ∘ original) := by
  apply OwnerClassification.extend sem hc (oldPatch sem hB S hsep) (row_old sem hB S hsep)
  intro z
  rcases classify sem hB S z with hl | hz
  · exact Or.inl hl
  · obtain ⟨c, rfl⟩ := local_exhaustive sem hB S z (subset_of_eq hz)
    have hs : S.carrier.scope c = B := by simpa only [CellScheme.scope, local_index] using hz
    exact Or.inr (short_at S.rows (localPatch sem hB S) (row_local sem hB S hsep) c (S.short c hs))

/-- The initial inventory is itself the original-field inventory, regardless
of the lengths of any of its rows. -/
theorem ownerClassification_initial : OwnerClassification sem (id : Cell D → Cell D) :=
  by tauto

end

end VaughtConjecture.Knight.OrderedScopeRelocation
