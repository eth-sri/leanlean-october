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

variable {X α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι] (μ : Distribution X)
  (A : X → Measurement α ι) (v : EuclideanSpace ℂ ι) (B C R W CB : X → α → Op ι)
  (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) (hB : ∀ x a, IsProj (B x a))
  (hC : ∀ x a, IsProj (C x a)) (hAB : ∀ x a, Commute ((A x).effect a) (B x a))
  (hAC : ∀ x a, Commute ((A x).effect a) (C x a)) (hR : ∀ x a, IsProj (R x a))
  (hAR : ∀ x a, Commute ((A x).effect a) (R x a))

/-! ## The Cauchy--Schwarz inequality weighted by a positive operator -/

/-- For a positive operator `A`, the sesquilinear form `⟨u, A v⟩` satisfies the
Cauchy--Schwarz inequality with the two diagonal values `⟨u, A u⟩` and
`⟨v, A v⟩`.  This is the inequality behind the Cauchy--Schwarz steps of the
proofs of `lem:claim-17-2` and `lem:claim-17-3`, in which both factors carry
the square root of the line effect, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1209`. -/
theorem norm_inner_applyOperatorToState_le_sqrt_mul_sqrt {A : Op ι} (hA : 0 ≤ A)
    (u v : EuclideanSpace ℂ ι) :
    ‖inner ℂ u (applyOperatorToState A v)‖ ≤
      Real.sqrt (inner ℂ u (applyOperatorToState A u)).re *
        Real.sqrt (inner ℂ v (applyOperatorToState A v)).re := by
  set R : Op ι := CFC.sqrt A with hR
  have hRherm :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hsplit : ∀ w z : EuclideanSpace ℂ ι,
      inner ℂ w (applyOperatorToState A z) =
        inner ℂ (applyOperatorToState R w) (applyOperatorToState R z) := by
    intro w z
    have h := LinearMap.adjoint_inner_right (Matrix.toEuclideanLin R) w
      (Matrix.toEuclideanLin R z)
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hRherm] at h
    rw [← (CFC.sqrt_mul_sqrt_self A hA), applyOperatorToState_mul]
    exact h
  have hnorm : ∀ w : EuclideanSpace ℂ ι,
      ‖applyOperatorToState R w‖ =
        Real.sqrt (inner ℂ w (applyOperatorToState A w)).re := by
    intro w
    have h2 : ‖applyOperatorToState R w‖ ^ 2 =
        (inner ℂ (applyOperatorToState R w) (applyOperatorToState R w)).re := by
      simp [@norm_sq_eq_re_inner ℂ]
    rw [hsplit, ← h2, Real.sqrt_sq (norm_nonneg _)]
  rw [hsplit, ← hnorm, ← hnorm]
  apply norm_inner_le_norm

/-- The sum over outcomes of the real parts of `⟨u a, A a (v a)⟩`, for
positive weights `A a`, is bounded by the product of the square roots of the
two diagonal sums. -/
theorem abs_sum_re_inner_le_sqrt_mul_sqrt {A : α → Op ι} (hA : ∀ a, 0 ≤ A a)
    (u v : α → EuclideanSpace ℂ ι) :
    |∑ a, (inner ℂ (u a) (applyOperatorToState (A a) (v a))).re| ≤
      Real.sqrt (∑ a, (inner ℂ (u a) (applyOperatorToState (A a) (u a))).re) *
        Real.sqrt (∑ a, (inner ℂ (v a) (applyOperatorToState (A a) (v a))).re) := by
  have hu : ∀ a, 0 ≤ (inner ℂ (u a) _).re :=
    fun a => stateQForm_nonneg (u a) (hA a)
  have hv : ∀ a, 0 ≤ (inner ℂ (v a) _).re :=
    fun a => stateQForm_nonneg (v a) (hA a)
  calc
    _
        ≤ _ :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, Real.sqrt (inner ℂ (u a) (applyOperatorToState (A a) (u a))).re *
          Real.sqrt (inner ℂ (v a) (applyOperatorToState (A a) (v a))).re := by
      refine Finset.sum_le_sum fun a _ => ?_
      exact (Complex.abs_re_le_norm _).trans
        (norm_inner_applyOperatorToState_le_sqrt_mul_sqrt (hA a) (u a) (v a))
    _ ≤ _ :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      simp_all

/-- The averaged form of the preceding estimate: the average over a
distribution of the outcome sums of `Re ⟨u, A v⟩` is bounded by the product of
the square roots of the two averaged diagonal sums. -/
theorem abs_avgOver_sum_re_inner_le_sqrt_mul_sqrt (A : X → α → Op ι)
    (hA : ∀ x a, 0 ≤ A x a) (u v : X → α → EuclideanSpace ℂ ι) :
    |avgOver μ (fun x =>
        ∑ a, (inner ℂ (u x a) (applyOperatorToState (A x a) (v x a))).re)| ≤
      Real.sqrt (avgOver μ (fun x =>
          ∑ a, (inner ℂ (u x a) (applyOperatorToState (A x a) (u x a))).re)) *
        Real.sqrt (avgOver μ (fun x =>
          ∑ a, (inner ℂ (v x a) (applyOperatorToState (A x a) (v x a))).re)) := by
  set f : X → ℝ := fun x =>
    ∑ a, (inner ℂ (u x a) (applyOperatorToState (A x a) (v x a))).re with hf
  set g : X → ℝ := fun x =>
    ∑ a, (inner ℂ (u x a) (applyOperatorToState (A x a) (u x a))).re with hg
  set h : X → ℝ := fun x =>
    ∑ a, (inner ℂ (v x a) (applyOperatorToState (A x a) (v x a))).re with hh
  have hg0 : ∀ x, 0 ≤ g x := fun x =>
    Finset.sum_nonneg fun a _ => stateQForm_nonneg _ (hA x a)
  have hh0 : ∀ x, 0 ≤ h x := fun x =>
    Finset.sum_nonneg fun a _ => stateQForm_nonneg _ (hA x a)
  unfold avgOver
  calc
    _
        ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x ∈ μ.support, μ.weight x * |f x| := by
      congr 1 with x
      simp [abs_of_nonneg (μ.nonnegative x)]
    _ ≤ _ :=
      Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left ((fun x =>
          abs_sum_re_inner_le_sqrt_mul_sqrt (hA x) (u x) (v x)) x) (μ.nonnegative x)
    _ = ∑ x ∈ μ.support,
          Real.sqrt (μ.weight x * g x) * Real.sqrt (μ.weight x * h x) := by
      congr 1 with x
      rw [Real.sqrt_mul (μ.nonnegative x), Real.sqrt_mul (μ.nonnegative x),
        show Real.sqrt (μ.weight x) * Real.sqrt (g x) *
            (Real.sqrt (μ.weight x) * Real.sqrt (h x)) =
          Real.sqrt (μ.weight x) * Real.sqrt (μ.weight x) *
            (Real.sqrt (g x) * Real.sqrt (h x)) by ring,
        Real.mul_self_sqrt (μ.nonnegative x)]
    _ ≤ _ :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      rw [Finset.sum_congr rfl fun x _ =>
          Real.sq_sqrt (mul_nonneg (μ.nonnegative x) (hg0 x)),
        Finset.sum_congr rfl fun x _ =>
          Real.sq_sqrt (mul_nonneg (μ.nonnegative x) (hh0 x))]

/-! ## Quadratic forms against projections -/

/-- The real quadratic form is invariant under the conjugate transpose. -/
theorem stateQForm_conjTranspose (M : Op ι) :
    stateQForm ψ Mᴴ = stateQForm ψ M := by
  change (inner ℂ ψ (Matrix.toEuclideanLin Mᴴ ψ)).re =
    (inner ℂ ψ (Matrix.toEuclideanLin M ψ)).re
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right,
    ← inner_conj_symm, Complex.conj_re]

/-- For a projection `B` commuting with `A`, the quadratic form of `A` in
`B ψ` is the quadratic form of `A B` in `ψ`. -/
theorem stateQForm_applyOperatorToState_eq_of_isProj {A B : Op ι} (hB : IsProj B)
    (hAB : Commute A B) :
    stateQForm (applyOperatorToState B ψ) A = stateQForm ψ (A * B) := by
  rw [← stateQForm_conjTranspose_mul_mul, hB.isSelfAdjoint.isHermitian.eq,
    ← hAB.eq, mul_assoc, hB.isIdempotentElem.eq]

/-- The effects of a complete measurement have total quadratic form one on a
unit vector. -/
theorem sum_stateQForm_effect_eq_one (A : Measurement α ι) {ψ : EuclideanSpace ℂ ι}
    (hψ : ‖ψ‖ = 1) :
    (∑ a : α, stateQForm ψ (A.effect a)) = 1 := by
  calc
    _ =
        stateQForm ψ (∑ a : α, A.effect a) := by
      simp [stateQForm, applyOperatorToState]
    _ = stateQForm ψ 1 := by rw [A.sum_eq_one]
    _ = 1 := by simp [stateQForm_one, hψ]

include hAC hC hψ hμ in
/-- Weighting a complete measurement by commuting projections cannot exceed
the total mass one. -/
theorem avgOver_sum_stateQForm_mul_le_one :
    avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a)) ≤ 1 := by
  have hpt : ∀ x, (∑ a, stateQForm ψ ((A x).effect a * C x a)) ≤ 1 := by
    intro x
    calc
      _ ≤
          ∑ a, stateQForm ψ ((A x).effect a) := by
        gcongr
        have h1 : stateQForm ψ ((A x).effect a * (1 - C x a)) =
            stateQForm ψ ((A x).effect a) -
              stateQForm ψ ((A x).effect a * C x a) := by
          simp [stateQForm, applyOperatorToState]
        have h2 : 0 ≤ stateQForm ψ ((A x).effect a * (1 - C x a)) := by
          rw [← stateQForm_applyOperatorToState_eq_of_isProj ψ (hC x a).one_sub
            ((Commute.one_right _).sub_right (hAC x a))]
          exact stateQForm_nonneg _ ((A x).pos a)
        linarith
      _ = 1 := sum_stateQForm_effect_eq_one (A x) hψ
  rw [← avgOver_const_of_isProbability μ hμ 1]
  solve_by_elim [avgOver_mono]

/-! ## Replacing a factor under the weight of a measurement -/

include hAB hB in
/-- Cauchy--Schwarz with the measurement as weight: for projections `B`
commuting with the effects of `A`, the averaged overlap of `A` against the
product `B C` is bounded by the square roots of the averaged overlap of `A`
against `B` and of the averaged quadratic form of `A` in `C ψ`.  This is the
Cauchy--Schwarz step of the proofs of `lem:claim-17-2` and `lem:claim-17-3`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1209`. -/
theorem abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (B x a * C x a)))| ≤
      Real.sqrt (avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a))) *
        Real.sqrt (avgOver μ (fun x => ∑ a,
          stateQForm (applyOperatorToState (C x a) ψ) ((A x).effect a))) := by
  have hrw : ∀ x a, stateQForm ψ ((A x).effect a * (B x a * C x a)) =
      (inner ℂ (applyOperatorToState (B x a) ψ)
        (applyOperatorToState ((A x).effect a)
          (applyOperatorToState (C x a) ψ))).re := by
    intro x a
    unfold stateQForm
    rw [← mul_assoc, (hAB x a).eq, mul_assoc, applyOperatorToState_mul,
      applyOperatorToState_mul]
    congr 1
    have h := LinearMap.adjoint_inner_right (Matrix.toEuclideanLin (B x a)) ψ
      (applyOperatorToState ((A x).effect a) (applyOperatorToState (C x a) ψ))
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
        (hB x a).isSelfAdjoint.isHermitian.eq] at h
    exact h
  rw [(funext fun x => Finset.sum_congr rfl fun a _ => hrw x a), (funext fun x => Finset.sum_congr rfl fun a _ =>
      (stateQForm_applyOperatorToState_eq_of_isProj ψ (hB x a) (hAB x a)).symm)]
  exact abs_avgOver_sum_re_inner_le_sqrt_mul_sqrt μ _
    (fun x => (A x).pos) _
    _

include hAC hAB hC hB hψ hμ in
/-- Deficit form of the Cauchy--Schwarz estimate: for projections `B` and `C`
commuting with the effects of `A`, replacing the factor `C B` by `C` inside an
overlap weighted by the complete measurement `A` changes the average by at
most the square root of the deficit `1 - E Σ_a ⟨A_a B_a⟩`.  This is the
estimate used in the proof of `lem:claim-17-2` and, with `C = Id`, in the proof
of `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1209`. -/
theorem abs_overlap_gap_le_sqrt_one_sub_of_isProj :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (C x a * B x a))) -
        avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a))| ≤
      Real.sqrt (1 - avgOver μ (fun x =>
        ∑ a, stateQForm ψ ((A x).effect a * B x a))) := by
  have hpt : ∀ x, (∑ a, stateQForm ψ ((A x).effect a * C x a)) -
      (∑ a, stateQForm ψ ((A x).effect a * (C x a * B x a))) =
        ∑ a, stateQForm ψ ((A x).effect a * (C x a * (1 - B x a))) := by
    simp [stateQForm, applyOperatorToState]
  rw [abs_sub_comm, ← avgOver_sub, avgOver_congr μ _ _ hpt]
  have hcs := abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt μ A C
    (fun x a => 1 - B x a) ψ hC hAC
  have hsecond : avgOver μ (fun x => ∑ a,
      stateQForm (applyOperatorToState (1 - B x a) ψ) ((A x).effect a)) =
      1 - avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a)) := by
    have hx : ∀ x, (∑ a,
        stateQForm (applyOperatorToState (1 - B x a) ψ) ((A x).effect a)) =
        1 - ∑ a, stateQForm ψ ((A x).effect a * B x a) := by
      intro x
      rw [← sum_stateQForm_effect_eq_one (A x) hψ, ← Finset.sum_sub_distrib]
      congr 1 with a
      rw [stateQForm_applyOperatorToState_eq_of_isProj ψ ((fun x a => (hB x a).one_sub) x a) ((fun x a =>
        (Commute.one_right _).sub_right (hAB x a)) x a)]
      simp [stateQForm, applyOperatorToState]
    rw [avgOver_congr μ _ _ hx, avgOver_sub, avgOver_const_of_isProbability μ hμ]
  have hfirst : Real.sqrt (avgOver μ (fun x =>
      ∑ a, stateQForm ψ ((A x).effect a * C x a))) ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt
      (avgOver_sum_stateQForm_mul_le_one μ A C ψ hμ hψ hC hAC)
  rw [hsecond] at hcs
  calc
    _ ≤ _ := hcs
    _ ≤ _ :=
      mul_le_mul_of_nonneg_right hfirst (Real.sqrt_nonneg _)
    _ = _ := one_mul _

variable {A B C} in
include hAC hAB hC hB hψ hμ in
/-- The deficit form of the Cauchy--Schwarz estimate with the product family
`C B` supplied as one family `CB`, which is convenient when the product is
formed on a local space before being placed. -/
theorem abs_overlap_gap_le_sqrt_one_sub_of_isProj'
    (hCB : ∀ x a, CB x a = C x a * B x a) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * CB x a)) -
        avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a))| ≤
      Real.sqrt (1 - avgOver μ (fun x =>
        ∑ a, stateQForm ψ ((A x).effect a * B x a))) := by
  simp_all
  apply abs_overlap_gap_le_sqrt_one_sub_of_isProj <;> assumption

include hAR hR hψ hμ in
/-- Inserting an arbitrary operator family `W` after a projection family `R`
commuting with the effects of `A` costs at most the square root of the
averaged squared norms of `W ψ`. -/
theorem abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (R x a * W x a)))| ≤
      Real.sqrt (avgOver μ (fun x =>
        ∑ a, ‖applyOperatorToState (W x a) ψ‖ ^ 2)) := by
  calc
    _ ≤ _ := (abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt μ A R W ψ hR hAR)
    _ ≤ _ :=
      mul_le_mul (by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt
          (avgOver_sum_stateQForm_mul_le_one μ A R ψ hμ hψ hR hAR)) (Real.sqrt_le_sqrt (avgOver_mono μ _ _ fun x => Finset.sum_le_sum fun a _ =>
          (by
            rw [← stateQForm_one]
            exact quadratic_form_mono (measurement_effect_le_one (A x) a) _))) (Real.sqrt_nonneg _)
        zero_le_one
    _ = _ := one_mul _

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
    rw [← stateQForm_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      measurement_effect_hermitian, (hR x a).isSelfAdjoint.isHermitian.eq]
    congr 1
    refine ((hAR x a).mul_right ?_).eq.symm
    have h := congrArg Matrix.conjTranspose (hAW x a).eq
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      measurement_effect_hermitian] at h
    exact h.symm
  simp [*]
  solve_by_elim [abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj]

end MIPStarRE.QPBT
