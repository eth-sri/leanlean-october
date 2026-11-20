/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthReplicatedLegal
public import VaughtConjecture.Knight.WholeDonorAttachment

@[expose] public section

namespace VaughtConjecture.Knight.GrowthAttachedCarrier

open AmalgamationPlan Transform Value ExtOrd Growth

open CellScheme.restrictFace

noncomputable section

variable {n J : ℕ}
  (C : SemScheme J) (P : SemScheme (n + 1)) (Q : SemScheme n)
  (e : Fin n ↪ Fin J)
  (hvC : Finset.univ.image e ∈ C.scheme.plan)
  (hvP : Finset.univ.image Fin.castSuccEmb ∈ P.scheme.plan)
  (hC : C.restrictFace e hvC = Q)
  (hP : P.restrictFace Fin.castSuccEmb hvP = Q)

/-- The same constructed attachment plan, in the growth family's orientation. -/
def boundary : WholeDonorBoundary.Input Finset.univ
    (WholeDonorAttachment.donorScope e) WholeDonorAttachment.privateScope
    (WholeDonorAttachment.plan e C P Q hvC hvP hC hP) n (n + 1) J :=
  (WholeDonorAttachment.input e C P Q hvC hvP hC hP).swap

variable (X : RelativeData C.scheme C.rows P.scheme P.rows)
  (T : RootAttachment Q Fin.castSuccEmb hvP hP e hvC hC X)
  (hsmall : n + 1 < X.req.N)

theorem threshold_le_arity : X.req.N ≤ J := by
  have hg := C.scheme.grade_le_card_scope X.req.C
  have hc := Finset.card_le_card (Finset.subset_univ (C.scheme.scope X.req.C))
  rw [X.grade_C] at hg
  (simp_all <;> omega)

include hsmall in
theorem donor_arity_lt : n + 1 < J :=
  hsmall.trans_le (threshold_le_arity C P X)

include hsmall in
theorem height : 2 ≤ (Finset.univ : Finset (Fin (J + 1))).card := by
  have := donor_arity_lt C P X hsmall
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

include hsmall in
theorem donor_proper : WholeDonorAttachment.donorScope e ⊂ Finset.univ :=
  Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,
    WholeDonorAttachment.donor_proper e (donor_arity_lt C P X hsmall)⟩

theorem private_proper : WholeDonorAttachment.privateScope (N := J) ⊂ Finset.univ :=
  Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, WholeDonorAttachment.private_proper⟩

local notation "I" => boundary C P Q e hvC hvP hC hP

local notation "hA" => height C P X hsmall

local notation "hB" => donor_proper C P e X hsmall

local notation "hD" => private_proper (J := J)

/-- No supplied plan, occurrence alignment, coverage or carrier lift is needed. -/
abbrev semScheme : SemScheme (J + 1) :=
  GrowthReplicatedLegal.semScheme I X T hA hB hD hsmall

abbrev donorFace := GrowthReplicatedLegal.donor I X T hA hB hD hsmall

abbrev privateFace := GrowthReplicatedLegal.privateFace I X T hA hB hD hsmall

abbrev donor_receipt := GrowthReplicatedLegal.donor_receipt I X T hA hB hD hsmall

abbrev private_receipt := GrowthReplicatedLegal.private_receipt I X T hA hB hD hsmall

end

end VaughtConjecture.Knight.GrowthAttachedCarrier
