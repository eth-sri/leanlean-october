module

public import QPBT.Combining.Points.Sandwich

/-!
# Self-consistency of the sandwich POVM

The sandwich POVM `R^{x,z}_{a,b} = M^Z_b M^X_a M^Z_b` of
`MIPStarRE/QPBT/Combining/Points/Sandwich.lean` is approximately self-consistent
between opposite register placements.  The source establishes this by a
Cauchy--Schwarz chain (displays `eq:qld-rw-self-cons-1` to
`eq:qld-rw-self-cons-4`); here an exact identity is used instead.  Writing
`P_1, P_2` for the two placements of an operator `P`,
`W_b = (M^Z_b)_1 (M^Z_b)_2`, and `D^W_c = (M^W_c)_1 - (M^W_c)_2`, the
consistency defect of the two placed sandwiches equals
`(1/2) ∑_b ‖D^Z_b ψ‖^2 + (1/2) ∑_{a,b} ‖D^X_a W_b ψ‖^2`,
by two applications of the identity
`∑_c ⟨w, P_c Q_c w⟩ = ‖w‖^2 - (1/2) ∑_c ‖(P_c - Q_c) w‖^2` for projective
measurements.  The second sum is then bounded by the self-consistency of `M^X`
and the commutators on the two placements, since
`D^X_a W_b = W_b D^X_a + (M^Z_b)_2 K^1_{a,b} - (M^Z_b)_1 K^2_{a,b}`, where
`K^i_{a,b}` is the placed commutator of `M^X_a` and `M^Z_b`.

## Main results

* `sandwich_overlap_identity`: the exact expression of the overlap of two
  placed sandwiches.
* `sandwich_defect_pointwise_le`: the pointwise bound on the consistency
  defect of the sandwich for a fixed point pair.
* `ProjectiveSetting.sandwichDefectBound`,
  `ProjectiveSetting.sandwich_offDiagonal_le_sandwichDefectBound`, and
  `ProjectiveSetting.avg_sandwichDefectBound_le`: the bound as a function of
  the point pair, the pointwise estimate, and the average.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:743-790`,
blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex:851-880`
(`lem:qld-4-10`, first step); the identity route is explained in
`docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## Quadratic-form identities -/

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

/-- For two projective measurements, the diagonal overlap in a vector `w` is
the squared norm of `w` minus half the summed squared distances.  This is the
identity behind `fact:agreement` for projective families, blueprint
`blueprint/src/chapter/ch12_qpbt_games.tex:260-272`. -/
theorem sum_stateQForm_mul_eq_of_projective (A B : Measurement α ι) (w : EuclideanSpace ℂ ι)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B) :
    ∑ a, stateQForm w (A.effect a * B.effect a) =
      ‖w‖ ^ 2 -
        (1 / 2) * ∑ a, ‖applyOperatorToState (A.effect a - B.effect a) w‖ ^ 2 := by
  classical
  simp_all [point_distance_eq_two_defect_of_projective, point_defect_eq]

/-- An effect of a projective measurement is a contraction. -/
theorem norm_applyOperatorToState_proj_effect_le (M : Measurement α ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (a : α)
    (v : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (M.effect a) v‖ ≤ ‖v‖ := by
  refine MagicSquareRigidity.norm_applyOperatorToState_le ?_ v
  rw [(hM a).isSelfAdjoint.isHermitian.eq, (hM a).isIdempotentElem.eq]
  exact measurement_effect_le_one M a

/-! ## The overlap of two placed sandwiches -/

section Abstract

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]

/-- Formalization-only auxiliary for `lem:qld-4-10`: the product of the two
placed sandwiches is `W_bᴴ (X_1 X_2) W_b` with `W_b = Z_1 Z_2`, whenever the
operators of the two placements commute. -/
theorem sandwich_mul_sandwich_eq (X₁ X₂ : Measurement α ι) (Z₁ Z₂ : Measurement β ι)
    (hXZ : ∀ a b, X₁.effect a * Z₂.effect b = Z₂.effect b * X₁.effect a)
    (hZX : ∀ a b, Z₁.effect b * X₂.effect a = X₂.effect a * Z₁.effect b)
    (hZZ : ∀ b, Z₁.effect b * Z₂.effect b = Z₂.effect b * Z₁.effect b)
    (a : α) (b : β) :
    (Z₁.effect b * X₁.effect a * Z₁.effect b) *
        (Z₂.effect b * X₂.effect a * Z₂.effect b) =
      (Z₁.effect b * Z₂.effect b)ᴴ * (X₁.effect a * X₂.effect a) *
        (Z₁.effect b * Z₂.effect b) := by
  rw [Matrix.conjTranspose_mul, measurement_effect_hermitian,
    measurement_effect_hermitian]
  grind

omit [DecidableEq ι] in
/-- Formalization-only auxiliary for `lem:qld-4-10`: the decomposition of
`(X_1 - X_2) Z_1 Z_2` into `Z_1 Z_2 (X_1 - X_2)` and the two commutator
terms. -/
theorem sub_mul_mul_eq_add_commutators (X₁ X₂ Z₁ Z₂ : Op ι)
    (hXZ : X₁ * Z₂ = Z₂ * X₁) (hZX : Z₁ * X₂ = X₂ * Z₁)
    (hZZ : Z₁ * Z₂ = Z₂ * Z₁) :
    (X₁ - X₂) * (Z₁ * Z₂) =
      Z₁ * Z₂ * (X₁ - X₂) + Z₂ * (X₁ * Z₁ - Z₁ * X₁) -
        Z₁ * (X₂ * Z₂ - Z₂ * X₂) := by
  simp only [sub_mul, mul_sub, Matrix.mul_assoc]
  rw [(show Commute Z₂ X₁ from hXZ.symm).left_comm Z₁, ← hZZ,
    (show Commute Z₂ Z₁ from hZZ.symm).left_comm X₁,
    (show Commute Z₁ X₂ from hZX).left_comm Z₂]
  abel

variable (ψ : EuclideanSpace ℂ ι) (X₁ X₂ : Measurement α ι) (Z₁ Z₂ : Measurement β ι)

/-- The overlap of the two placed sandwiches, exactly: with
`W_b = Z_1(b) Z_2(b)`,
`∑_{a,b} ⟨ψ, R_1(a,b) R_2(a,b) ψ⟩ = ‖ψ‖^2 - (1/2) ∑_b ‖(Z_1(b) - Z_2(b)) ψ‖^2
  - (1/2) ∑_{a,b} ‖(X_1(a) - X_2(a)) W_b ψ‖^2`.
This replaces the Cauchy--Schwarz chain of displays
`eq:qld-rw-self-cons-1` to `eq:qld-rw-self-cons-4`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:743-790`. -/
theorem sandwich_overlap_identity (hX₁ : MIPStarRE.QPBT.Measurement.IsProjective X₁)
    (hX₂ : MIPStarRE.QPBT.Measurement.IsProjective X₂)
    (hZ₁ : MIPStarRE.QPBT.Measurement.IsProjective Z₁)
    (hZ₂ : MIPStarRE.QPBT.Measurement.IsProjective Z₂)
    (hXZ : ∀ a b, X₁.effect a * Z₂.effect b = Z₂.effect b * X₁.effect a)
    (hZX : ∀ a b, Z₁.effect b * X₂.effect a = X₂.effect a * Z₁.effect b)
    (hZZ : ∀ b, Z₁.effect b * Z₂.effect b = Z₂.effect b * Z₁.effect b) :
    ∑ ab : α × β, stateQForm ψ
        ((Z₁.effect ab.2 * X₁.effect ab.1 * Z₁.effect ab.2) *
          (Z₂.effect ab.2 * X₂.effect ab.1 * Z₂.effect ab.2)) =
      ‖ψ‖ ^ 2 -
        (1 / 2) * ∑ b, ‖applyOperatorToState (Z₁.effect b - Z₂.effect b) ψ‖ ^ 2 -
        (1 / 2) * ∑ ab : α × β, ‖applyOperatorToState (X₁.effect ab.1 - X₂.effect ab.1)
          (applyOperatorToState (Z₁.effect ab.2 * Z₂.effect ab.2) ψ)‖ ^ 2 := by
  have hW : ∀ b, ‖applyOperatorToState (Z₁.effect b * Z₂.effect b) ψ‖ ^ 2 =
      stateQForm ψ (Z₁.effect b * Z₂.effect b) := by
    intro b
    rw [norm_applyOperatorToState_sq_eq_stateQForm, Matrix.conjTranspose_mul,
      measurement_effect_hermitian, measurement_effect_hermitian]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Z₁.effect b) (Z₁.effect b),
      (hZ₁ b).isIdempotentElem.eq, hZZ b, ← Matrix.mul_assoc,
      (hZ₂ b).isIdempotentElem.eq]
  simp only [sandwich_mul_sandwich_eq X₁ X₂ Z₁ Z₂ hXZ hZX hZZ, stateQForm_conjTranspose_mul_mul,
    Fintype.sum_prod_type_right, sum_stateQForm_mul_eq_of_projective X₁ X₂ _ hX₁ hX₂, hW,
    Finset.sum_sub_distrib, ← Finset.mul_sum, sum_stateQForm_mul_eq_of_projective Z₁ Z₂ ψ hZ₁ hZ₂]

/-- The pointwise bound on the consistency defect of the placed sandwiches:
in terms of the distances `D^Z`, `D^X` of the two placements and the placed
commutators `K^1`, `K^2`,
`‖ψ‖^2 - ∑_{a,b} ⟨ψ, R_1 R_2 ψ⟩ ≤ (1/2) D^Z + (3/2) (D^X + K^1 + K^2)`. -/
theorem sandwich_defect_pointwise_le (hX₁ : MIPStarRE.QPBT.Measurement.IsProjective X₁)
    (hX₂ : MIPStarRE.QPBT.Measurement.IsProjective X₂)
    (hZ₁ : MIPStarRE.QPBT.Measurement.IsProjective Z₁)
    (hZ₂ : MIPStarRE.QPBT.Measurement.IsProjective Z₂)
    (hXZ : ∀ a b, X₁.effect a * Z₂.effect b = Z₂.effect b * X₁.effect a)
    (hZX : ∀ a b, Z₁.effect b * X₂.effect a = X₂.effect a * Z₁.effect b)
    (hZZ : ∀ b, Z₁.effect b * Z₂.effect b = Z₂.effect b * Z₁.effect b) :
    ‖ψ‖ ^ 2 - ∑ ab : α × β, stateQForm ψ
        ((Z₁.effect ab.2 * X₁.effect ab.1 * Z₁.effect ab.2) *
          (Z₂.effect ab.2 * X₂.effect ab.1 * Z₂.effect ab.2)) ≤
      (1 / 2) * ∑ b, ‖applyOperatorToState (Z₁.effect b - Z₂.effect b) ψ‖ ^ 2 +
        (3 / 2) * ((∑ a, ‖applyOperatorToState (X₁.effect a - X₂.effect a) ψ‖ ^ 2) +
          (∑ ab : α × β, ‖applyOperatorToState
            (X₁.effect ab.1 * Z₁.effect ab.2 -
              Z₁.effect ab.2 * X₁.effect ab.1) ψ‖ ^ 2) +
          ∑ ab : α × β, ‖applyOperatorToState
            (X₂.effect ab.1 * Z₂.effect ab.2 -
              Z₂.effect ab.2 * X₂.effect ab.1) ψ‖ ^ 2) := by
  rw [sandwich_overlap_identity ψ X₁ X₂ Z₁ Z₂ hX₁ hX₂ hZ₁ hZ₂ hXZ hZX hZZ]
  -- the pointwise decomposition of `(X_1 - X_2) W_b ψ`
  have hpt : ∀ ab : α × β,
      ‖applyOperatorToState (X₁.effect ab.1 - X₂.effect ab.1)
          (applyOperatorToState (Z₁.effect ab.2 * Z₂.effect ab.2) ψ)‖ ^ 2 ≤
        3 * (‖applyOperatorToState (Z₂.effect ab.2 *
              (X₁.effect ab.1 - X₂.effect ab.1)) ψ‖ ^ 2 +
          ‖applyOperatorToState
            (X₁.effect ab.1 * Z₁.effect ab.2 -
              Z₁.effect ab.2 * X₁.effect ab.1) ψ‖ ^ 2 +
          ‖applyOperatorToState
            (X₂.effect ab.1 * Z₂.effect ab.2 -
              Z₂.effect ab.2 * X₂.effect ab.1) ψ‖ ^ 2) := by
    rintro ⟨a, b⟩
    have h (Z : Measurement β ι) (hZ : MIPStarRE.QPBT.Measurement.IsProjective Z) (M : Op ι) :
        ‖applyOperatorToState (Z.effect b * M) ψ‖ ≤ ‖applyOperatorToState M ψ‖ := by
      rw [applyOperatorToState_mul]; exact norm_applyOperatorToState_proj_effect_le Z hZ b _
    have key (t x y z : ℝ) (h0 : 0 ≤ t) (h : t ≤ x + y + z) : t ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
    rw [← applyOperatorToState_mul, sub_mul_mul_eq_add_commutators _ _ _ _ (hXZ a b) (hZX a b)
      (hZZ b), Matrix.mul_assoc, MagicSquareRigidity.applyOperatorToState_sub_op,
      MagicSquareRigidity.applyOperatorToState_add_op]
    exact key _ _ _ _ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (h Z₁ hZ₁ _) (h Z₂ hZ₂ _))) (h Z₁ hZ₁ _)))
  -- the contraction sum over `b`
  have hcontr : ∑ ab : α × β, ‖applyOperatorToState (Z₂.effect ab.2 *
      (X₁.effect ab.1 - X₂.effect ab.1)) ψ‖ ^ 2 ≤
      ∑ a, ‖applyOperatorToState (X₁.effect a - X₂.effect a) ψ‖ ^ 2 := by
    simp only [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun a _ => sum_norm_mul_apply_le Z₂.effect _ ψ
      (measurement_sum_adjoint_mul_le_one Z₂)
  have hsum := Finset.sum_le_sum fun ab (_ : ab ∈ Finset.univ) => hpt ab
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  linarith

end Abstract

/-! ## The bound for the placed sandwiches -/

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- The pointwise bound on the consistency defect of the sandwich POVM between
two placements, as a function of the point pair: one half of the
`Z`-distance plus three halves of the `X`-distance and of the two placed
commutator sums. -/
def sandwichDefectBound (S : ProjectiveSetting P ε) (p₁ p₂ : Placement)
    (xz : PointPair P) : ℝ :=
  (1 / 2) * ∑ b : PauliScalar P, ‖applyOperatorToState
      (S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect b) -
        S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect b)) S.psiHat‖ ^ 2 +
    (3 / 2) * ((∑ a : PauliScalar P, ‖applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .X xz.1).effect a) -
          S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect a)) S.psiHat‖ ^ 2) +
      (∑ ab : PauliScalar P × PauliScalar P, ‖applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p₁.side .Z xz.2).effect ab.2) -
          S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p₁.side .X xz.1).effect ab.1)) S.psiHat‖ ^ 2) +
      ∑ ab : PauliScalar P × PauliScalar P, ‖applyOperatorToState
        (S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p₂.side .Z xz.2).effect ab.2) -
          S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p₂.side .X xz.1).effect ab.1)) S.psiHat‖ ^ 2)

variable (S : ProjectiveSetting P ε) (p₁ p₂ : Placement)

/-- The pointwise bound is nonnegative. -/
theorem sandwichDefectBound_nonneg (xz : PointPair P) : 0 ≤ S.sandwichDefectBound p₁ p₂ xz := by
  unfold sandwichDefectBound
  positivity

/-- For a fixed point pair, the off-diagonal mass of the two placed sandwiches
is at most the pointwise bound.  This is the consistency of the sandwich POVM
between opposite placements, display `eq:rw-sc` of the proof of
`lem:qld-4-10`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:743-790`, in
exact form. -/
theorem sandwich_offDiagonal_le_sandwichDefectBound (hopp : p₁.IsOpposite p₂) (xz : PointPair P) :
    (∑ ab : PauliScalar P × PauliScalar P, ∑ ab' : PauliScalar P × PauliScalar P,
      if ab = ab' then 0 else stateQForm S.psiHat
        (S.place p₁ ((S.sandwichPoint p₁.side xz.1 xz.2).effect ab) *
          S.place p₂ ((S.sandwichPoint p₂.side xz.1 xz.2).effect ab'))) ≤
      S.sandwichDefectBound p₁ p₂ xz := by
  have hdefect := point_defect_eq
    (S.placedMeasurement p₁ (S.sandwichPoint p₁.side xz.1 xz.2))
    (S.placedMeasurement p₂ (S.sandwichPoint p₂.side xz.1 xz.2)) S.psiHat
  simp at hdefect
  have hkey := sandwich_defect_pointwise_le S.psiHat
    (S.placedMeasurement p₁ (S.pointMeasExp p₁.side .X xz.1))
    (S.placedMeasurement p₂ (S.pointMeasExp p₂.side .X xz.1))
    (S.placedMeasurement p₁ (S.pointMeasExp p₁.side .Z xz.2))
    (S.placedMeasurement p₂ (S.pointMeasExp p₂.side .Z xz.2))
    (S.placedMeasurement_isProjective p₁ _ (S.pointMeasExp_isProjective _ _ _))
    (S.placedMeasurement_isProjective p₂ _ (S.pointMeasExp_isProjective _ _ _))
    (S.placedMeasurement_isProjective p₁ _ (S.pointMeasExp_isProjective _ _ _))
    (S.placedMeasurement_isProjective p₂ _ (S.pointMeasExp_isProjective _ _ _))
    (fun a b => S.place_comm p₁ p₂ hopp _ _)
    (fun a b => S.place_comm p₁ p₂ hopp _ _)
    (fun b => S.place_comm p₁ p₂ hopp _ _)
  simp_all [placedMeasurement_effect, psiHat_norm, sandwichDefectBound, sandwichPoint_effect, place_mul]

/-- The average over the point pair of the pointwise bound is polynomially
small: at most a universal constant times `ε + √ε`.  The `X`- and
`Z`-distances are the self-consistency of item 1 of `lem:qld-comm-cons`, and
the two commutator sums are the field-valued commutation estimate. -/
theorem avg_sandwich_defect_bound_le_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
      (p₁ p₂ : Placement), p₁.IsOpposite p₂ →
      avgOver (uniformDistribution (PointPair P)) (S.sandwichDefectBound p₁ p₂) ≤
        (344 + 3 * pauliBaselineTwistedConstant) * (ε + Real.sqrt ε) := by
  intro P ε S p₁ p₂ hopp
  have hT : (1 : ℝ) ≤ pauliBaselineTwistedConstant := by
    simp only [pauliBaselineTwistedConstant, pauliBaselineCommutatorConstant]
    linarith [Real.sqrt_nonneg (344 : ℝ)]
  have hε : (0 : ℝ) ≤ ε := by linarith [S.toStrategy.value_le_one, S.win]
  have hZ := (avgOver_uniform_snd (α := Fin P.m → PauliScalar P) _).trans_le
    (exp_point_self_cons_explicit P ε S p₁ p₂ hopp .Z)
  have hX := (avgOver_uniform_fst (β := Fin P.m → PauliScalar P) _).trans_le
    (exp_point_self_cons_explicit P ε S p₁ p₂ hopp .X)
  have hK₁ := exp_point_comm_explicit P ε S p₁
  have hK₂ := exp_point_comm_explicit P ε S p₂
  unfold opFamilyDistSq at hK₁ hK₂
  unfold sandwichDefectBound
  rw [avgOver_add, avgOver_const_mul, avgOver_const_mul, avgOver_add, avgOver_add]
  nlinarith [Real.sqrt_nonneg ε]

end ProjectiveSetting

end

end MIPStarRE.QPBT
