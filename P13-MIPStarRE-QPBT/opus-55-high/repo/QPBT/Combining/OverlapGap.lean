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

variable {X α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι] (μ : Distribution X) (A : X → Measurement α ι)

/-- Replacing one operator family inside an overlap weighted on the left by a
complete measurement changes the average by at most the square root of the
state-dependent squared distance between the two families. -/
theorem abs_overlap_gap_le_sqrt_of_opFamilyDistSq (B C : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (ζ : ℝ) (hBC : opFamilyDistSq μ B C ψ ≤ ζ) :
    |avgOver μ (fun x => ∑ a : α, stateQForm ψ ((A x).effect a * B x a)) -
        avgOver μ (fun x => ∑ a : α, stateQForm ψ ((A x).effect a * C x a))| ≤
      Real.sqrt ζ := by
  rw [← avgOver_sub]
  refine (MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise μ _
    (fun x => ∑ a, ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2) (fun x => ?_)
    (fun x => Finset.sum_nonneg fun a _ => sq_nonneg _) (by rw [hμ.weight_sum_eq_one])).trans
    (Real.sqrt_le_sqrt hBC)
  have h := quadratic_form_mono (measurement_sum_adjoint_mul_le_one (A x)) ψ
  change stateQForm ψ _ ≤ stateQForm ψ 1 at h
  rw [stateQForm_one, hψ, stateQForm_finset_sum] at h
  simp_rw [← norm_applyOperatorToState_sq_eq_stateQForm] at h
  simp_rw [← Finset.sum_sub_distrib, ← stateQForm_sub, ← mul_sub, stateQForm_mul_eq_inner,
    measurement_effect_hermitian]
  refine (Finset.abs_sum_le_sum_abs _ _).trans <| (Finset.sum_le_sum fun a _ =>
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)).trans <|
    (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr (by simpa using h))

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
  set R : Op ι := CFC.sqrt A with hR
  have hRnonneg : 0 ≤ R := CFC.sqrt_nonneg A
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A hA
  have hRherm : Rᴴ = R :=
    (Matrix.nonneg_iff_posSemidef.mp hRnonneg).isHermitian.eq
  have hadjoint : (Matrix.toEuclideanLin R).adjoint = Matrix.toEuclideanLin R := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hRherm]
  have hsplit : ∀ w z : EuclideanSpace ℂ ι,
      inner ℂ w (applyOperatorToState A z) =
        inner ℂ (applyOperatorToState R w) (applyOperatorToState R z) := by
    intro w z
    have h := LinearMap.adjoint_inner_right (Matrix.toEuclideanLin R) w
      (Matrix.toEuclideanLin R z)
    rw [hadjoint] at h
    rw [← hRR, applyOperatorToState_mul]
    exact h
  have hnorm : ∀ w : EuclideanSpace ℂ ι,
      ‖applyOperatorToState R w‖ =
        Real.sqrt (inner ℂ w (applyOperatorToState A w)).re := by
    intro w
    have h2 : ‖applyOperatorToState R w‖ ^ 2 =
        (inner ℂ (applyOperatorToState R w) (applyOperatorToState R w)).re := by
      rw [@norm_sq_eq_re_inner ℂ]
      rfl
    rw [hsplit, ← h2, Real.sqrt_sq (norm_nonneg _)]
  grind [norm_inner_le_norm]

/-- The average over a
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
          ∑ a, (inner ℂ (v x a) (applyOperatorToState (A x a) (v x a))).re)) :=
  LDT.Preliminaries.weightedFinsetCauchySchwarz μ _ _ _ (fun x a => (Complex.abs_re_le_norm _).trans
    (norm_inner_applyOperatorToState_le_sqrt_mul_sqrt (hA x a) _ _))
    (fun x a => stateQForm_nonneg _ (hA x a)) (fun x a => stateQForm_nonneg _ (hA x a))

/-! ## Quadratic forms against projections -/

/-- For a projection `B` commuting with `A`, the quadratic form of `A` in
`B ψ` is the quadratic form of `A B` in `ψ`. -/
theorem stateQForm_applyOperatorToState_eq_of_isProj {ι : Type*} [Fintype ι]
    [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) {A B : Op ι} (hB : IsProj B)
    (hAB : Commute A B) :
    stateQForm (applyOperatorToState B ψ) A = stateQForm ψ (A * B) := by
  rw [← stateQForm_conjTranspose_mul_mul, hB.isSelfAdjoint.isHermitian.eq,
    ← hAB.eq, mul_assoc, hB.isIdempotentElem.eq]

/-- The quadratic form of an operator bounded by the identity is bounded by
the squared norm of the vector. -/
theorem stateQForm_le_norm_sq_of_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) {A : Op ι} (hA : A ≤ 1) :
    stateQForm v A ≤ ‖v‖ ^ 2 := by
  rw [← stateQForm_one]
  exact quadratic_form_mono hA v

/-- The effects of a complete measurement have total quadratic form one on a
unit vector. -/
theorem sum_stateQForm_effect_eq_one {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι] (A : Measurement α ι) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) :
    (∑ a : α, stateQForm ψ (A.effect a)) = 1 := by
  rw [← stateQForm_finset_sum, A.sum_eq_one, stateQForm_one, hψ, one_pow]

/-- Weighting a complete measurement by commuting projections cannot exceed
the total mass one. -/
theorem avgOver_sum_stateQForm_mul_le_one (C : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability)
    (hψ : ‖ψ‖ = 1) (hC : ∀ x a, IsProj (C x a))
    (hAC : ∀ x a, Commute ((A x).effect a) (C x a)) :
    avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a)) ≤ 1 := by
  refine hμ.avgOver_le_of_forall_le_on_support _ _ fun x _ => ?_
  rw [← sum_stateQForm_effect_eq_one (A x) ψ hψ]
  refine Finset.sum_le_sum fun a _ => ?_
  have h := stateQForm_nonneg (applyOperatorToState (1 - C x a) ψ) ((A x).pos a)
  rw [stateQForm_applyOperatorToState_eq_of_isProj ψ (hC x a).one_sub
    ((Commute.one_right _).sub_right (hAC x a)), mul_sub, mul_one, stateQForm_sub] at h
  linarith

/-! ## Replacing a factor under the weight of a measurement -/

/-- Cauchy--Schwarz with the measurement as weight: for projections `B`
commuting with the effects of `A`, the averaged overlap of `A` against the
product `B C` is bounded by the square roots of the averaged overlap of `A`
against `B` and of the averaged quadratic form of `A` in `C ψ`.  This is the
Cauchy--Schwarz step of the proofs of `lem:claim-17-2` and `lem:claim-17-3`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1209`. -/
theorem abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt (B C : X → α → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hB : ∀ x a, IsProj (B x a))
    (hAB : ∀ x a, Commute ((A x).effect a) (B x a)) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (B x a * C x a)))| ≤
      Real.sqrt (avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a))) *
        Real.sqrt (avgOver μ (fun x => ∑ a,
          stateQForm (applyOperatorToState (C x a) ψ) ((A x).effect a))) := by
  have h := abs_avgOver_sum_re_inner_le_sqrt_mul_sqrt μ (fun x a => (A x).effect a)
    (fun x a => (A x).pos a) (fun x a => applyOperatorToState (B x a) ψ)
    (fun x a => applyOperatorToState (C x a) ψ)
  simp only [← stateQForm_applyOperatorToState_eq_of_isProj ψ (hB _ _) (hAB _ _)]
  convert h using 6
  · rw [← mul_assoc, (hAB _ _).eq, mul_assoc, stateQForm_mul_eq_inner,
      (hB _ _).isSelfAdjoint.isHermitian.eq, applyOperatorToState_mul]
  all_goals rfl

/-- Deficit form of the Cauchy--Schwarz estimate: for projections `B` and `C`
commuting with the effects of `A`, replacing the factor `C B` by `C` inside an
overlap weighted by the complete measurement `A` changes the average by at
most the square root of the deficit `1 - E Σ_a ⟨A_a B_a⟩`.  This is the
estimate used in the proof of `lem:claim-17-2` and, with `C = Id`, in the proof
of `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1209`. -/
theorem abs_overlap_gap_le_sqrt_one_sub_of_isProj (B C : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability)
    (hψ : ‖ψ‖ = 1) (hB : ∀ x a, IsProj (B x a)) (hC : ∀ x a, IsProj (C x a))
    (hAB : ∀ x a, Commute ((A x).effect a) (B x a))
    (hAC : ∀ x a, Commute ((A x).effect a) (C x a)) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (C x a * B x a))) -
        avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a))| ≤
      Real.sqrt (1 - avgOver μ (fun x =>
        ∑ a, stateQForm ψ ((A x).effect a * B x a))) := by
  have hpt : ∀ x, (∑ a, stateQForm ψ ((A x).effect a * C x a)) -
      (∑ a, stateQForm ψ ((A x).effect a * (C x a * B x a))) =
        ∑ a, stateQForm ψ ((A x).effect a * (C x a * (1 - B x a))) := by
    intro x
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [stateQForm, applyOperatorToState, mul_sub]
  rw [abs_sub_comm, ← avgOver_sub, avgOver_congr μ _ _ hpt]
  have h1B : ∀ x a, IsProj (1 - B x a) := fun x a => (hB x a).one_sub
  have hA1B : ∀ x a, Commute ((A x).effect a) (1 - B x a) := fun x a =>
    (Commute.one_right _).sub_right (hAB x a)
  have hcs := abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt μ A C
    (fun x a => 1 - B x a) ψ hC hAC
  have hsecond : avgOver μ (fun x => ∑ a,
      stateQForm (applyOperatorToState (1 - B x a) ψ) ((A x).effect a)) =
      1 - avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a)) := by
    have hx : ∀ x, (∑ a,
        stateQForm (applyOperatorToState (1 - B x a) ψ) ((A x).effect a)) =
        1 - ∑ a, stateQForm ψ ((A x).effect a * B x a) := by
      intro x
      rw [← sum_stateQForm_effect_eq_one (A x) ψ hψ, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [stateQForm_applyOperatorToState_eq_of_isProj ψ (h1B x a) (hA1B x a)]
      simp [stateQForm, applyOperatorToState, mul_sub]
    rw [avgOver_congr μ _ _ hx, avgOver_sub, avgOver_const_of_isProbability μ hμ]
  rw [hsecond] at hcs
  exact hcs.trans (mul_le_of_le_one_left (Real.sqrt_nonneg _)
    (Real.sqrt_le_one.mpr (avgOver_sum_stateQForm_mul_le_one μ A C ψ hμ hψ hC hAC)))

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
  exact hcs.trans ((mul_le_of_le_one_left (Real.sqrt_nonneg _)
    (Real.sqrt_le_one.mpr (avgOver_sum_stateQForm_mul_le_one μ A R ψ hμ hψ hR hAR))).trans
    (Real.sqrt_le_sqrt (avgOver_mono μ _ _ fun x => Finset.sum_le_sum fun a _ =>
      stateQForm_le_norm_sq_of_le_one _ (measurement_effect_le_one (A x) a))))

/-- The mirror image of the preceding estimate: an operator family `W`
commuting with the effects of `A`, inserted before a commuting projection
family `R`, costs at most the square root of the averaged squared norms of
`Wᴴ ψ`. -/
theorem abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj' (W R : X → α → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) (hR : ∀ x a, IsProj (R x a))
    (hAR : ∀ x a, Commute ((A x).effect a) (R x a))
    (hAW : ∀ x a, Commute ((A x).effect a) (W x a)) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (W x a * R x a)))| ≤
      Real.sqrt (avgOver μ (fun x =>
        ∑ a, ‖applyOperatorToState (W x a)ᴴ ψ‖ ^ 2)) := by
  have hrw : ∀ x a, stateQForm ψ ((A x).effect a * (W x a * R x a)) =
      stateQForm ψ ((A x).effect a * (R x a * (W x a)ᴴ)) := by
    intro x a
    have hAWH : Commute ((A x).effect a) (W x a)ᴴ := by
      have h := congrArg Matrix.conjTranspose (hAW x a).eq
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        measurement_effect_hermitian] at h
      exact h.symm
    rw [← stateQForm_conjTranspose ψ ((A x).effect a * (W x a * R x a)),
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      measurement_effect_hermitian, (hR x a).isSelfAdjoint.isHermitian.eq]
    congr 1
    exact ((hAR x a).mul_right hAWH).eq.symm
  simp_all [abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj]

end MIPStarRE.QPBT
