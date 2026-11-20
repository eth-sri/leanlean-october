/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FinalGateLayer
public import VaughtConjecture.Knight.FinalGateDecoding
public import VaughtConjecture.Knight.CanonicalCodingSupport
public import VaughtConjecture.Knight.OrdinaryFinalCatalogue

@[expose] public section

namespace VaughtConjecture.Knight.FinalGateLayer.Input

open Transform Value ExtOrd AmalgamationPlan

noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype Q]

variable {A : Finset ι} {D : CellScheme A} {N : ℕ} (F : Input D N X Q)

theorem node_row (a : Q) (marked : Bool)
    (d : F.carrier.below (F.carrier.cell (F.added a marked))) :
    F.rows.E (F.added a marked) d = min (F.source a d.1) (F.nodeWeight (a, marked)) := by
  exact (WeightedSourcePrefixLayer.row_new F.data F.weight F.weight_visible
    (F.controller (a, marked)) d).trans (by
      simp [F.master_eq_source, weight, member_controller])

theorem grade_bound (hD : ∀ d : Cell D, D.grade d ≤ N) :
    ∀ d : Cell F.carrier, F.carrier.grade d ≤ N := by
  intro d
  obtain ⟨x, rfl⟩ := (SourceLayerCarrier.enumeration D (Node (Q := Q)) N
    F.pos F.height).surjective d
  change (F.carrier.cell (SourceLayerCarrier.toCell D (Node (Q := Q)) N
    F.pos F.height x)).2 ≤ N
  rw [SourceLayerCarrier.cell_toCell]
  aesop

theorem coded (hc : F.sem.IsCoded)
    (hfields : ∀ a f, IsCodedLabel N (F.fields a f))
    (hgrid : ∀ z ∈ F.grid, IsCodedLabel N z)
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d)) :
    F.rows.IsCoded := by
  apply CanonicalCodingSupport.layer D (Node (Q := Q)) N F.pos F.height F.separated
    F.sem F.rows hc F.inherited_row
  rintro ⟨a, marked⟩ d
  change F.carrier.below (F.carrier.cell (F.added a marked)) at d
  change IsCodedLabel N (F.rows.E (F.added a marked) d)
  rw [F.node_row]
  have hs : IsCodedLabel N (F.source a d.1) := CanonicalCodingSupport.supported
    hgrid (hfields a) (F.source_supported hsupport a d.1 (by
      simpa only [CellScheme.grade, F.added_index] using d.2.2))
  have hw : IsCodedLabel N (F.nodeWeight (a, marked)) := by
    unfold nodeWeight
    split
    · exact hfields a F.gate
    · exact hgrid _ F.ceiling_mem
  grind

/-- Fill the unique missing full active index by an actual ceiling leaf. -/
theorem complete_through (seed : Q)
    (hc : ∀ J ∈ Plan.gradedPlan D.plan, J.2 ≤ N → J ≠ (A, N) → ∃ d, D.cell d = J) :
    ∀ J ∈ Plan.gradedPlan F.carrier.plan, J.2 ≤ N → ∃ d, F.carrier.cell d = J := by
  intro J hJ hJN
  by_cases he : J = (A, N)
  · exact ⟨F.added seed false, (F.added_index seed false).trans he.symm⟩
  · obtain ⟨d, hd⟩ := hc J hJ hJN he
    exact ⟨F.old d, (F.old_index d).trans hd⟩

end

end VaughtConjecture.Knight.FinalGateLayer.Input

namespace VaughtConjecture.Knight.OrdinaryFinalCatalogue

open Transform Value ExtOrd CappedDonor CappedDonor.Ref PairedSlotComparison

noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}

variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)

theorem member_coded (a : Member R) (f : Field P C) : IsCodedLabel N (a.val f) := by
  rcases mem_codedAlphabet_iff.mp
    (CanonicalPairedProfiles.inventory_coded (Field P C) N a.property.1 f)
    with hb | ⟨b, i, _, hi, he⟩
  all_goals tauto

end

end VaughtConjecture.Knight.OrdinaryFinalCatalogue
