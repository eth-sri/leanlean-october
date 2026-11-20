module

public import QPBT.Games.DistanceTheorems.Support
public import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.InnerProduct

/-!
# Replacing one factor of a measurement-weighted overlap

The scalar estimates used to combine the two Pauli bases compare averaged
overlaps whose left factor is one complete measurement and whose right factors
are operator families at small state-dependent distance.  This module records
the corresponding Cauchy--Schwarz estimate.  The right-hand families are
arbitrary, so the estimate covers an ordered product of point effects, which
is not itself a measurement.

## References

The estimate is `lem:overlap-gap-distance` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; it is the Cauchy--Schwarz
step at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1147-1166`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

/-! ## The Cauchy--Schwarz inequality weighted by a positive operator -/

/-- For a positive operator `A`, the sesquilinear form `⟨u, A v⟩` satisfies the
Cauchy--Schwarz inequality with the two diagonal values `⟨u, A u⟩` and
`⟨v, A v⟩`.  This is the inequality behind the Cauchy--Schwarz steps of the
proofs of `lem:claim-17-2` and `lem:claim-17-3`, in which both factors carry
the square root of the line effect, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1209`. -/
theorem norm_inner_applyOperatorToState_le_sqrt_mul_sqrt {ι : Type*}
    [Fintype ι] [DecidableEq ι] {A : Op ι} (hA : 0 ≤ A)
    (u v : EuclideanSpace ℂ ι) :
    ‖inner ℂ u (applyOperatorToState A v)‖ ≤
      Real.sqrt (inner ℂ u (applyOperatorToState A u)).re *
        Real.sqrt (inner ℂ v (applyOperatorToState A v)).re := by
  let R := CFC.sqrt A
  have hR : Rᴴ = R :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hgram : Rᴴ * R = A := by rw [hR, CFC.sqrt_mul_sqrt_self A hA]
  have hsplit (w z : EuclideanSpace ℂ ι) : inner ℂ w (applyOperatorToState A z) =
      inner ℂ (applyOperatorToState R w) (applyOperatorToState R z) := by
    rw [← hgram, applyOperatorToState_mul, inner_applyOperatorToState_adjoint]
  have hd (w : EuclideanSpace ℂ ι) :
      (inner ℂ w w).re = ‖w‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) w
  simpa only [hsplit, hd, Real.sqrt_sq (norm_nonneg _)] using
    norm_inner_le_norm (𝕜 := ℂ) (applyOperatorToState R u) (applyOperatorToState R v)

/-- The averaged form of the preceding estimate: the average over a
distribution of the outcome sums of `Re ⟨u, A v⟩` is bounded by the product of
the square roots of the two averaged diagonal sums. -/
theorem abs_avgOver_sum_re_inner_le_sqrt_mul_sqrt {X α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (μ : Distribution X) (A : X → α → Op ι)
    (hA : ∀ x a, 0 ≤ A x a) (u v : X → α → EuclideanSpace ℂ ι) :
    |avgOver μ (fun x =>
        ∑ a, (inner ℂ (u x a) (applyOperatorToState (A x a) (v x a))).re)| ≤
      Real.sqrt (avgOver μ (fun x =>
          ∑ a, (inner ℂ (u x a) (applyOperatorToState (A x a) (u x a))).re)) *
        Real.sqrt (avgOver μ (fun x =>
          ∑ a, (inner ℂ (v x a) (applyOperatorToState (A x a) (v x a))).re)) := by
  exact MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz μ _ _ _
    (fun x a => (Complex.abs_re_le_norm _).trans
      (norm_inner_applyOperatorToState_le_sqrt_mul_sqrt (hA x a) _ _))
    (fun x a => stateQForm_nonneg _ (hA x a)) (fun x a => stateQForm_nonneg _ (hA x a))

/-! ## Quadratic forms against projections -/

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
include ι

section

variable (ψ : EuclideanSpace ℂ ι)
include ψ

/-- For a projection `B` commuting with `A`, the quadratic form of `A` in
`B ψ` is the quadratic form of `A B` in `ψ`. -/
theorem stateQForm_applyOperatorToState_eq_of_isProj {A B : Op ι} (hB : IsProj B)
    (hAB : Commute A B) :
    stateQForm (applyOperatorToState B ψ) A = stateQForm ψ (A * B) := by
  rw [← stateQForm_conjTranspose_mul_mul, hB.isSelfAdjoint.isHermitian.eq,
    ← hAB.eq, mul_assoc, hB.isIdempotentElem.eq]

end

/-- The quadratic form of an operator bounded by the identity is bounded by
the squared norm of the vector. -/
theorem stateQForm_le_norm_sq_of_le_one
    (v : EuclideanSpace ℂ ι) {A : Op ι} (hA : A ≤ 1) :
    stateQForm v A ≤ ‖v‖ ^ 2 := by
  rw [← stateQForm_one]
  exact quadratic_form_mono hA v

end

/-- The effects of a complete measurement have total quadratic form one on a
unit vector. -/
theorem sum_stateQForm_effect_eq_one {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι] (A : Measurement α ι) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) :
    (∑ a : α, stateQForm ψ (A.effect a)) = 1 := by
  rw [← stateQForm_finset_sum, A.sum_eq_one, stateQForm_one, hψ, one_pow]

/-- Weighting a complete measurement by commuting projections cannot exceed
the total mass one. -/
theorem avgOver_sum_stateQForm_mul_le_one {X α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (μ : Distribution X) (A : X → Measurement α ι)
    (C : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability)
    (hψ : ‖ψ‖ = 1) (hC : ∀ x a, IsProj (C x a))
    (hAC : ∀ x a, Commute ((A x).effect a) (C x a)) :
    avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a)) ≤ 1 := by
  rw [← avgOver_const_of_isProbability μ hμ 1]
  refine avgOver_mono _ _ _ fun x => (Finset.sum_le_sum fun a _ => ?_).trans_eq
    (sum_stateQForm_effect_eq_one (A x) ψ hψ)
  have h := stateQForm_nonneg (applyOperatorToState (1 - C x a) ψ) ((A x).pos a)
  rw [stateQForm_applyOperatorToState_eq_of_isProj ψ (hC x a).one_sub
    ((Commute.one_right _).sub_right (hAC x a)), mul_sub, mul_one, stateQForm_sub] at h
  exact sub_nonneg.mp h

/-! ## Replacing a factor under the weight of a measurement -/

section

variable {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] (μ : Distribution X)
    (A : X → Measurement α ι)
include X α ι μ A

section

variable (B C : X → α → Op ι) (ψ : EuclideanSpace ℂ ι)
include B C ψ

/-- Cauchy--Schwarz with the measurement as weight: for projections `B`
commuting with the effects of `A`, the averaged overlap of `A` against the
product `B C` is bounded by the square roots of the averaged overlap of `A`
against `B` and of the averaged quadratic form of `A` in `C ψ`.  This is the
Cauchy--Schwarz step of the proofs of `lem:claim-17-2` and `lem:claim-17-3`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1209`. -/
theorem abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt
    (hB : ∀ x a, IsProj (B x a))
    (hAB : ∀ x a, Commute ((A x).effect a) (B x a)) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (B x a * C x a)))| ≤
      Real.sqrt (avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a))) *
        Real.sqrt (avgOver μ (fun x => ∑ a,
          stateQForm (applyOperatorToState (C x a) ψ) ((A x).effect a))) := by
  have hrw : ∀ x a, stateQForm ψ ((A x).effect a * (B x a * C x a)) =
      (inner ℂ (applyOperatorToState (B x a) ψ)
        (applyOperatorToState ((A x).effect a)
          (applyOperatorToState (C x a) ψ))).re := by
    intro x a
    rw [← mul_assoc, (hAB x a).eq, mul_assoc, stateQForm_mul_eq_inner,
      (hB x a).isSelfAdjoint.isHermitian.eq, applyOperatorToState_mul]
  have hdiag (u : EuclideanSpace ℂ ι) (M : Op ι) :
      (inner ℂ u (applyOperatorToState M u)).re = stateQForm u M := rfl
  simpa only [← hrw, hdiag, stateQForm_applyOperatorToState_eq_of_isProj ψ (hB _ _) (hAB _ _)] using
    abs_avgOver_sum_re_inner_le_sqrt_mul_sqrt μ (fun x a => (A x).effect a)
      (fun x a => (A x).pos a) (fun x a => applyOperatorToState (B x a) ψ)
      (fun x a => applyOperatorToState (C x a) ψ)

/-- Deficit form of the Cauchy--Schwarz estimate: for projections `B` and `C`
commuting with the effects of `A`, replacing the factor `C B` by `C` inside an
overlap weighted by the complete measurement `A` changes the average by at
most the square root of the deficit `1 - E Σ_a ⟨A_a B_a⟩`.  This is the
estimate used in the proof of `lem:claim-17-2` and, with `C = Id`, in the proof
of `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1209`. -/
theorem abs_overlap_gap_le_sqrt_one_sub_of_isProj (hμ : μ.IsProbability)
    (hψ : ‖ψ‖ = 1) (hB : ∀ x a, IsProj (B x a)) (hC : ∀ x a, IsProj (C x a))
    (hAB : ∀ x a, Commute ((A x).effect a) (B x a))
    (hAC : ∀ x a, Commute ((A x).effect a) (C x a)) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (C x a * B x a))) -
        avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a))| ≤
      Real.sqrt (1 - avgOver μ (fun x =>
        ∑ a, stateQForm ψ ((A x).effect a * B x a))) := by
  rw [abs_sub_comm]
  have hcs := abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt μ A C
    (fun x a => 1 - B x a) ψ hC hAC
  have h (x : X) (a : α) := stateQForm_applyOperatorToState_eq_of_isProj ψ
    (hB x a).one_sub ((Commute.one_right _).sub_right (hAB x a))
  simp only [h, mul_sub, mul_one, stateQForm_sub, Finset.sum_sub_distrib,
    sum_stateQForm_effect_eq_one _ _ hψ, avgOver_sub, avgOver_const_of_isProbability _ hμ] at hcs
  refine hcs.trans ?_
  simpa only [Real.sqrt_one, one_mul] using mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (avgOver_sum_stateQForm_mul_le_one μ A C ψ hμ hψ hC hAC))
    (Real.sqrt_nonneg _)

end

/-- Inserting an arbitrary operator family `W` after a projection family `R`
commuting with the effects of `A` costs at most the square root of the
averaged squared norms of `W ψ`. -/
theorem abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj (R W : X → α → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) (hR : ∀ x a, IsProj (R x a))
    (hAR : ∀ x a, Commute ((A x).effect a) (R x a)) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (R x a * W x a)))| ≤
      Real.sqrt (avgOver μ (fun x =>
        ∑ a, ‖applyOperatorToState (W x a) ψ‖ ^ 2)) := by
  have hcs := abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt μ A R W ψ hR hAR
  refine hcs.trans ?_
  simpa only [Real.sqrt_one, one_mul] using
    mul_le_mul (Real.sqrt_le_sqrt (avgOver_sum_stateQForm_mul_le_one μ A R ψ hμ hψ hR hAR))
      (Real.sqrt_le_sqrt (avgOver_mono μ _ _ fun x => Finset.sum_le_sum fun a _ =>
        stateQForm_le_norm_sq_of_le_one _ (measurement_effect_le_one (A x) a)))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end

end MIPStarRE.QPBT
