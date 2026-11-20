module

public import QPBT.Observables.LineMeasurement.LinePointOverlap

/-!
# Placement calculus on the expanded state

This module records the algebra of the four register placements used by the
combining argument: a placement is a unital `*`-homomorphism, placements on
opposite register pairs commute, and the crosswise exchange of the two EPR
pairs of the expanded state carries the placement `AA'` to `AB''` and `BA''`
to `BB'` while fixing the expanded state.  The last fact transfers every
state-dependent distance between the two bipartition schemes of
`def:symmetric-equivalents` without assuming a symmetric strategy.

## References

The placements are those of `def:symmetric-equivalents`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.  The
placement module proves EPR-exchange invariance for the involution
`(A' B'')(A'' B')`, which fixes `A` and `B`, in
`ProjectiveSetting.reindexState_eprCrossSwap_psiHat`; its use for
`lem:qld-4-10` is analyzed in
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## Placements as reindexed tensor factors -/

/-- Reindexing an operator commutes with the conjugate transpose. -/
theorem reindexOp_conjTranspose {ι κ : Type*} (e : ι ≃ κ) (M : Op κ) :
    reindexOp e Mᴴ = (reindexOp e M)ᴴ := by
  ext i j
  rfl

/-! ## The placement is a unital `*`-homomorphism -/

section

variable (S : ProjectiveSetting P ε)
include S

set_option synthInstance.maxSize 400 in
/-- A placement is multiplicative. -/
theorem place_mul :
    ∀ (p : Placement) (A B : Op (S.ExpandedLocalSpace p.side)),
      S.place p (A * B) = S.place p A * S.place p B := by
  intro p A B
  rw [place_eq_reindex, place_eq_reindex, place_eq_reindex, ← reindexOp_mul,
    heteroKron_mul, mul_one]

/-- A placement is additive over finite sums of local operators.
Compatibility name for `place_finset_sum`, retained for the combining-point
proofs that use this spelling. -/
theorem place_finsetSum (p : Placement) {γ : Type*}
    (s : Finset γ) (O : γ → Op (S.ExpandedLocalSpace p.side)) :
    S.place p (∑ x ∈ s, O x) = ∑ x ∈ s, S.place p (O x) :=
  S.place_finset_sum p s O

/-- A placement commutes with the conjugate transpose. -/
theorem place_conjTranspose :
    ∀ (p : Placement) (A : Op (S.ExpandedLocalSpace p.side)),
      S.place p Aᴴ = (S.place p A)ᴴ := by
  intro p A
  rw [place_eq_reindex, place_eq_reindex, ← reindexOp_conjTranspose,
    heteroKron_conjTranspose, Matrix.conjTranspose_one]

/-- The placement of a local operator bounded by the identity is bounded by
the identity. -/
theorem place_le_one (p : Placement)
    {A : Op (S.ExpandedLocalSpace p.side)} (hA : A ≤ 1) :
    S.place p A ≤ 1 := by
  have h : 0 ≤ S.place p (1 - A) := S.place_nonneg p (sub_nonneg.mpr hA)
  rw [place_sub, place_one] at h
  exact sub_nonneg.mp h

/-- The placement of a projector is a contraction. -/
theorem place_conjTranspose_mul_self_le_one
    (p : Placement) {E : Op (S.ExpandedLocalSpace p.side)} (hE : IsProj E) :
    (S.place p E)ᴴ * S.place p E ≤ 1 := by
  rw [← place_conjTranspose, ← place_mul, hE.isSelfAdjoint.isHermitian.eq,
    hE.isIdempotentElem.eq]
  exact S.place_le_one p (sub_nonneg.mp hE.one_sub.nonneg)

set_option synthInstance.maxSize 400 in
/-- Operators placed on opposite register pairs commute. -/
theorem place_comm :
    ∀ (p₁ p₂ : Placement), p₁.IsOpposite p₂ →
      ∀ (A : Op (S.ExpandedLocalSpace p₁.side))
        (B : Op (S.ExpandedLocalSpace p₂.side)),
        S.place p₁ A * S.place p₂ B = S.place p₂ B * S.place p₁ A := by
  intro p q h A B
  obtain rfl := Placement.eq_overlapPartner h
  rw [place_eq_reindex S p, ← S.reindexOp_placeSplit_partner p B, ← reindexOp_mul, ← reindexOp_mul]
  rw [heteroKron_mul, heteroKron_mul, mul_one, one_mul, mul_one, one_mul]

/-- A placed projective measurement is projective. -/
theorem placedMeasurement_isProjective
    (p : Placement) {α : Type*} [Fintype α]
    (M : Measurement α (S.ExpandedLocalSpace p.side))
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective (S.placedMeasurement p M) :=
  Measurement.mapEffects_isProjective M hM (S.placeLinear p).toAddMonoidHom (S.place_one p)
    (fun {_} h => S.place_nonneg p h) (fun _ => S.place_mul p _ _)

end

end ProjectiveSetting

end

end MIPStarRE.QPBT
