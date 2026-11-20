module

public import QPBT.Games.Consistency
public import MIPStarRE.LDT.MakingMeasurementsProjective.Defs
public import MIPStarRE.LDT.Preliminaries.CauchySchwarz
public import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.RankReduction.Sigma
public import MIPStarRE.Quantum.FiniteHilbert

/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open MIPStarRE.LDT MIPStarRE.Quantum
open MIPStarRE.LDT.MakingMeasurementsProjective

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The squared norm of `M ψ` is the quadratic form of `Mᴴ M`. -/
theorem norm_applyOperatorToState_sq_eq
    (M : Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState M ψ‖ ^ 2 =
      (inner ℂ ψ (applyOperatorToState (Mᴴ * M) ψ)).re := by
  rw [@norm_sq_eq_re_inner ℂ]
  unfold applyOperatorToState
  rw [Matrix.toEuclideanLin_conjTranspose_mul_self]
  simp [LinearMap.adjoint_inner_right]

/-- Formalization-only auxiliary lemma for Fact 4.20: evaluation in a fixed
vector preserves operator order. -/
theorem quadratic_form_mono
    {S T : Op ι} (hST : S ≤ T) (v : EuclideanSpace ℂ ι) :
    (inner ℂ v (applyOperatorToState S v)).re ≤
      (inner ℂ v (applyOperatorToState T v)).re := by
  have hnonneg := (Matrix.le_iff.mp hST).dotProduct_mulVec_nonneg v
  rw [show T = S + (T - S) by abel]
  simp only [applyOperatorToState, map_add, LinearMap.add_apply, inner_add_right,
    Complex.add_re]
  apply le_add_of_nonneg_right
  simp only [applyOperatorToState, Matrix.toEuclideanLin,
    Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm]
  exact (Complex.nonneg_iff.mp hnonneg).1

theorem applyOperatorToState_sub_op (M N : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (M - N) v = applyOperatorToState M v - applyOperatorToState N v := by
  simp [applyOperatorToState]

/-- Formalization-only auxiliary lemma: applying a product of operators agrees
with successive application. It supports the ground-slice transfer of the Magic
Square rigidity bounds in `thm:ms-rigidity`; see blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:268-290` and paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
theorem applyOperatorToState_mul
    (M N : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (M * N) v =
      applyOperatorToState M (applyOperatorToState N v) := by
  unfold applyOperatorToState
  simp

end

/-- Finite-subset form of contraction by square-summable left multipliers. -/
private theorem finset_sum_norm_mul_apply_le {γ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (s : Finset γ) (C : γ → Op ι) (D : Op ι) (v : EuclideanSpace ℂ ι)
    (hC : ∑ c ∈ s, (C c)ᴴ * C c ≤ 1) :
    ∑ c ∈ s, ‖applyOperatorToState (C c * D) v‖ ^ 2 ≤
      ‖applyOperatorToState D v‖ ^ 2 := by
  calc
    _ =
        ∑ c ∈ s,
          (inner ℂ (applyOperatorToState D v)
            (applyOperatorToState ((C c)ᴴ * C c)
              (applyOperatorToState D v))).re := by
          congr 1 with c
          rw [applyOperatorToState_mul]
          apply norm_applyOperatorToState_sq_eq
    _ = (inner ℂ (applyOperatorToState D v)
          (applyOperatorToState (∑ c ∈ s, (C c)ᴴ * C c)
            (applyOperatorToState D v))).re := by
          simp [applyOperatorToState]
    _ ≤ _ :=
      quadratic_form_mono hC _
    _ = _ := by
      simpa [applyOperatorToState] using
        (norm_applyOperatorToState_sq_eq 1 (applyOperatorToState D v)).symm

/-- Formalization-only auxiliary lemma for Fact 4.20: a square-summable family
of left multipliers contracts total squared norm. -/
theorem sum_norm_mul_apply_le {γ ι : Type*}
    [Fintype γ] [Fintype ι] [DecidableEq ι]
    (C : γ → Op ι) (D : Op ι) (v : EuclideanSpace ℂ ι)
    (hC : ∑ c : γ, (C c)ᴴ * C c ≤ 1) :
    ∑ c : γ, ‖applyOperatorToState (C c * D) v‖ ^ 2 ≤
      ‖applyOperatorToState D v‖ ^ 2 := by
  solve_by_elim [finset_sum_norm_mul_apply_le]

/-- The squared distance between two square-summable operator families is at
most four on a unit vector. Formalization-only auxiliary bounding the
state-dependent distance of `def:povm-distance` trivially. -/
theorem sum_norm_sub_apply_sq_le_four {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] {A B : α → Op ι} {ψ : EuclideanSpace ℂ ι}
    (hψ : ‖ψ‖ = 1) (hA : ∑ a : α, (A a)ᴴ * A a ≤ 1)
    (hB : ∑ a : α, (B a)ᴴ * B a ≤ 1) :
    ∑ a : α, ‖applyOperatorToState (A a - B a) ψ‖ ^ 2 ≤ 4 := by
  have hAsum : ∑ a : α, ‖applyOperatorToState (A a) ψ‖ ^ 2 ≤ 1 := by
    have h := sum_norm_mul_apply_le A 1 ψ hA
    simpa [applyOperatorToState, hψ] using h
  have hBsum : ∑ a : α, ‖applyOperatorToState (B a) ψ‖ ^ 2 ≤ 1 := by
    have h := sum_norm_mul_apply_le B 1 ψ hB
    simpa [applyOperatorToState, hψ] using h
  have hpoint (a : α) :
      ‖applyOperatorToState (A a - B a) ψ‖ ^ 2 ≤
        2 * ‖applyOperatorToState (A a) ψ‖ ^ 2 +
          2 * ‖applyOperatorToState (B a) ψ‖ ^ 2 := by
    have hdecomp : applyOperatorToState (A a - B a) ψ =
        applyOperatorToState (A a) ψ - applyOperatorToState (B a) ψ := by
      simp [applyOperatorToState]
    rw [hdecomp]
    have hpar := parallelogram_law_with_norm ℂ
      (applyOperatorToState (A a) ψ) (applyOperatorToState (B a) ψ)
    nlinarith [sq_nonneg ‖applyOperatorToState (A a) ψ +
      applyOperatorToState (B a) ψ‖]
  calc
    _ ≤
        _ :=
      Finset.sum_le_sum fun a _ => hpoint a
    _ = 2 * ∑ a : α, ‖applyOperatorToState (A a) ψ‖ ^ 2 +
        2 * ∑ a : α, ‖applyOperatorToState (B a) ψ‖ ^ 2 := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 4 := by linarith

/-- Formalization-only auxiliary lemma for the function-indexed multiplication
estimate at paper lines 347--361: fiber-indexed left multiplication contracts
the associated squared-norm sum. -/
theorem sum_norm_mul_funIndexed_apply_le {α Γ ι : Type*}
    [Fintype α] [Fintype Γ] [Fintype ι] [DecidableEq ι]
    (eval : Γ → α) (S : Γ → Op ι) (D : α → Op ι)
    (v : EuclideanSpace ℂ ι) (hS : ∑ g : Γ, (S g)ᴴ * S g ≤ 1) :
    ∑ g : Γ, ‖applyOperatorToState (S g * D (eval g)) v‖ ^ 2 ≤
      ∑ a : α, ‖applyOperatorToState (D a) v‖ ^ 2 := by
  classical
  rw [← Finset.sum_readout eval (fun g a => ‖applyOperatorToState (S g * D a) v‖ ^ 2)]
  apply Finset.sum_le_sum
  intro a _
  apply finset_sum_norm_mul_apply_le
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
  (Finset.filter_subset _ _)
  (fun g _ _ => star_mul_self_nonneg (S g))) ?_
  exact hS

section

variable {α ι : Type*}

/-- Formalization-only auxiliary lemma for the projective-sum estimate at paper
lines 364--380: distinct effects of a projective measurement are orthogonal. -/
theorem projective_effect_mul_effect_eq_zero
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    {a b : α} (hab : a ≠ b) :
    M.effect a * M.effect b = 0 :=
  projectorFamily_mul_eq_zero_of_ne_of_sum_le_one _ hM M.sum_le_one hab

/-- Gram expansion for a finite sum with mutually orthogonal left projectors. -/
private theorem gram_finset_sum_projector_mul
    [Fintype ι]
    (P D : α → Op ι) (hproj : ∀ a, IsProj (P a))
    (horth : ∀ {a b}, a ≠ b → P a * P b = 0) (s : Finset α) :
    (∑ a ∈ s, P a * D a)ᴴ * (∑ a ∈ s, P a * D a) =
      ∑ a ∈ s, (D a)ᴴ * P a * D a := by
  classical
  let T : α → Op ι := fun a => P a * D a
  have hstar (a : α) : (P a)ᴴ = P a := IsSelfAdjoint.star_eq (hproj a).isSelfAdjoint
  calc
    _ = (∑ a ∈ s, (T a)ᴴ) * (∑ b ∈ s, T b) := by
      simp [T, Matrix.conjTranspose_sum]
    _ = ∑ a ∈ s, ∑ b ∈ s, (T a)ᴴ * T b := by
      rw [Matrix.sum_mul]
      simp [Matrix.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_eq_single]
      · simp [T, Matrix.conjTranspose_mul, hstar]
        rw [mul_assoc,
          ← mul_assoc (P a) (P a) (D a), (hproj a).isIdempotentElem.eq]
        exact (mul_assoc (D a)ᴴ (P a) (D a)).symm
      · intro b _ hba
        calc
          _ = (D a)ᴴ * (P a * P b) * D b := by
            simp [T, Matrix.conjTranspose_mul, hstar, mul_assoc]
          _ = 0 := by simp [horth (Ne.symm hba)]
      · grind

/-- Formalization-only auxiliary lemma for the projective-sum estimate at paper
lines 364--380: an orthogonal projective left sum is bounded by the full input
norm sum. -/
theorem norm_finset_sum_projector_mul_sq_le
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (P D : α → Op ι) (hproj : ∀ a, IsProj (P a))
    (horth : ∀ {a b}, a ≠ b → P a * P b = 0)
    (s : Finset α) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (∑ a ∈ s, P a * D a) ψ‖ ^ 2 ≤
      ∑ a : α, ‖applyOperatorToState (D a) ψ‖ ^ 2 := by
  classical
  rw [norm_applyOperatorToState_sq_eq]
  calc
    _ ≤
        (inner ℂ ψ (applyOperatorToState (∑ a : α, (D a)ᴴ * D a) ψ)).re :=
      quadratic_form_mono (by
        rw [gram_finset_sum_projector_mul P D hproj horth s]
        calc
          _ ≤
              ∑ a ∈ s, (D a)ᴴ * D a := by
            apply Finset.sum_le_sum
            intro a _
            simpa [Matrix.star_eq_conjTranspose] using
              (star_left_conjugate_le_conjugate (hproj a).le_one (D a))
          _ ≤ _ :=
            Finset.sum_le_sum_of_subset_of_nonneg (by simp)
              (fun a _ _ => (Matrix.posSemidef_conjTranspose_mul_self (D a)).nonneg)) ψ
    _ = ∑ a : α,
          (inner ℂ ψ (applyOperatorToState ((D a)ᴴ * D a) ψ)).re := by
      simp [applyOperatorToState]
    _ = _ := by
      congr 1 with a
      exact (norm_applyOperatorToState_sq_eq (D a) ψ).symm

end

/-- Formalization-only definition for the agreement facts (Facts 4.13 and 4.14):
the real quadratic form of an operator evaluated in a state vector. -/
noncomputable def stateQForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : Op ι) : ℝ :=
  (inner ℂ ψ (applyOperatorToState M ψ)).re

section

variable {β ιA ιB : Type*} (s : Finset β)

/-- Tensor placement is additive over finite sums in the left factor. This is
the formalization-only identity `lem:distance-tensor-sum-left`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem heteroKron_finset_sum_left
    (A : β → Op ιA) (C : Op ιB) :
    heteroKron (∑ b ∈ s, A b) C = ∑ b ∈ s, heteroKron (A b) C := by
  ext p q
  simp [heteroKron, Matrix.sum_apply, Finset.sum_mul]

/-- Tensor placement is additive over finite sums in the right factor. This is
the formalization-only identity `lem:distance-tensor-sum-right`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem heteroKron_finset_sum_right
    (A : Op ιA) (C : β → Op ιB) :
    heteroKron A (∑ b ∈ s, C b) = ∑ b ∈ s, heteroKron A (C b) := by
  ext p q
  simp [heteroKron, Matrix.sum_apply, Finset.mul_sum]

end

/-- The state quadratic form is additive over finite sums of operators. This is
the formalization-only identity `lem:distance-qform-finset-sum`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → Op ι) :
    stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, stateQForm ψ (M b) := by
  simp [stateQForm, applyOperatorToState]

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι)

/-- A positive semidefinite operator has nonnegative state quadratic form. This
is the formalization-only order fact `lem:distance-qform-nonnegative`, used for
the nonnegative overlap terms in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_nonneg {M : Op ι} (hM : 0 ≤ M) :
    0 ≤ stateQForm ψ M := by
  calc
    0 = stateQForm ψ 0 := by simp [stateQForm, applyOperatorToState]
    _ ≤ _ := quadratic_form_mono hM ψ

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): the state quadratic form is additive in its operator. -/
theorem stateQForm_add (M N : Op ι) :
    stateQForm ψ (M + N) = stateQForm ψ M + stateQForm ψ N := by
  simp [stateQForm, applyOperatorToState]

/-- The state quadratic form preserves operator subtraction. -/
theorem stateQForm_sub (M N : Op ι) :
    stateQForm ψ (M - N) = stateQForm ψ M - stateQForm ψ N := by
  simp [stateQForm, applyOperatorToState]

end

/-- The state quadratic form commutes with a finite sum. -/
private theorem stateQForm_sum {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : α → Op ι) :
    stateQForm ψ (∑ a, M a) = ∑ a, stateQForm ψ (M a) := by
  simp [stateQForm, applyOperatorToState]

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι)

/-- The quadratic form of the identity is the squared vector norm. -/
theorem stateQForm_one :
    stateQForm ψ (1 : Op ι) = ‖ψ‖ ^ 2 := by
  rw [stateQForm, applyOperatorToState]
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) ψ)

/-- The quadratic form of `Wᴴ M W` in `ψ` is the quadratic form of `M` in
`W ψ`.  This is the conjugation identity behind the placed-sandwich
rewritings: conjugating transfers the outer operator to the state vector.
It is formalization-only auxiliary content, shared by the overlap-gap estimate
and the sandwich self-consistency argument. -/
theorem stateQForm_conjTranspose_mul_mul (W M : Op ι) :
    stateQForm ψ (Wᴴ * M * W) = stateQForm (applyOperatorToState W ψ) M := by
  unfold stateQForm
  simp [applyOperatorToState_mul]
  congr 1
  change inner ℂ ψ (Matrix.toEuclideanLin Wᴴ _) =
    inner ℂ (Matrix.toEuclideanLin W ψ) _
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

end

section

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): every effect of a complete measurement is bounded by the identity. -/
theorem measurement_effect_le_one
    (M : MIPStarRE.Quantum.Measurement α ι) (a : α) :
    M.effect a ≤ 1 := by
  rw [← M.sum_eq_one]
  exact Finset.single_le_sum (fun b _ => M.pos b) (Finset.mem_univ a)

/-- Expand the squared state-dependent distance between two measurement effects. -/
private theorem norm_effect_sub_effect_sq_expand
    (A B : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (a : α) :
    ‖applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2 =
      stateQForm ψ (A.effect a * A.effect a) +
      stateQForm ψ (B.effect a * B.effect a) -
      2 * stateQForm ψ (A.effect a * B.effect a) := by
  rw [norm_applyOperatorToState_sq_eq]
  change stateQForm ψ _ = _
  rw [show (A.effect a - B.effect a)ᴴ * (A.effect a - B.effect a) =
      A.effect a * A.effect a - B.effect a * A.effect a -
        (A.effect a * B.effect a - B.effect a * B.effect a) by
    simp [Matrix.conjTranspose_sub, measurement_effect_hermitian]
    noncomm_ring]
  simp [stateQForm_sub]
  have hcross : stateQForm ψ (B.effect a * A.effect a) =
      stateQForm ψ (A.effect a * B.effect a) := by
    unfold stateQForm applyOperatorToState
    rw [show B.effect a * A.effect a = (A.effect a * B.effect a)ᴴ by
      simp [Matrix.conjTranspose_mul, measurement_effect_hermitian]]
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.adjoint_inner_right]
    exact (inner_re_symm (𝕜 := ℂ)
      ((Matrix.toEuclideanLin (A.effect a * B.effect a)) ψ) ψ)
  rw [hcross]
  ring

end

section

variable {α ι : Type*} [Fintype α]

/-- The quadratic forms of all effects sum to the squared vector norm. -/
private theorem stateQForm_effect_sum
    [Fintype ι] [DecidableEq ι]
    (A : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) :
    (∑ a : α, stateQForm ψ (A.effect a)) = ‖ψ‖ ^ 2 := by
  rw [← stateQForm_sum, A.sum_eq_one, stateQForm_one]

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): pointwise inconsistency is total mass minus diagonal overlap. -/
theorem point_defect_eq [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (A B : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) :
    (∑ a : α, ∑ b : α,
      if a = b then 0 else stateQForm ψ (A.effect a * B.effect b)) =
      ‖ψ‖ ^ 2 - ∑ a : α, stateQForm ψ (A.effect a * B.effect a) := by
  calc
    _ = ∑ a : α, ((∑ b : α, stateQForm ψ (A.effect a * B.effect b)) -
          stateQForm ψ (A.effect a * B.effect a)) := by
      apply Finset.sum_congr rfl
      intro a _
      have herase := Finset.sum_erase_add (Finset.univ : Finset _) (fun b => stateQForm ψ (A.effect a * B.effect b))
        (Finset.mem_univ a)
      calc
        _ =
            ∑ b ∈ (Finset.univ : Finset _).filter (fun b => b ≠ a), (fun b => stateQForm ψ (A.effect a * B.effect b)) b := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro b _
          by_cases h : a = b <;> simp [h, Ne.symm]
        _ = ∑ b ∈ (Finset.univ : Finset _).erase a, (fun b => stateQForm ψ (A.effect a * B.effect b)) b := by
          rw [Finset.filter_ne']
        _ = _ := by linarith
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← stateQForm_sum, ← Finset.mul_sum, B.sum_eq_one, mul_one]
    _ = (∑ a : α, stateQForm ψ (A.effect a)) -
          ∑ a : α, stateQForm ψ (A.effect a * B.effect a) := by
      simp
    _ = _ := by rw [stateQForm_effect_sum]

end

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): the matrix-vector term in `consistencyDefect` is the state quadratic
form. -/
theorem consistency_term_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : Op ι) :
    (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm (M.mulVec ψ))).re =
      stateQForm ψ M := rfl

section

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  (A B : MIPStarRE.Quantum.Measurement α ι) (ψ : EuclideanSpace ℂ ι)

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 1: pointwise measurement distance is at most twice the
inconsistency defect. -/
theorem point_distance_le_two_defect :
    (∑ a : α, ‖applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2) ≤
      2 * (∑ a : α, ∑ b : α,
        if a = b then 0 else stateQForm ψ (A.effect a * B.effect b)) := by
  have hterm (a : α) :
      ‖applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2 ≤
        stateQForm ψ (A.effect a) + stateQForm ψ (B.effect a) -
          2 * stateQForm ψ (A.effect a * B.effect a) := by
    rw [norm_effect_sub_effect_sq_expand]
    exact sub_le_sub_right (add_le_add (quadratic_form_mono
      (MIPStarRE.Quantum.sq_le_self (A.pos a) (measurement_effect_le_one A a)) ψ) (quadratic_form_mono
      (MIPStarRE.Quantum.sq_le_self (B.pos a) (measurement_effect_le_one B a)) ψ)) _
  calc
    _ ≤ _ :=
      Finset.sum_le_sum fun a _ => hterm a
    _ = (∑ a : α, stateQForm ψ (A.effect a)) +
          (∑ a : α, stateQForm ψ (B.effect a)) -
          2 * (∑ a : α, stateQForm ψ (A.effect a * B.effect a)) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 2 * (‖ψ‖ ^ 2 -
          ∑ a : α, stateQForm ψ (A.effect a * B.effect a)) := by
      simp [stateQForm_effect_sum]
      ring
    _ = _ := by rw [point_defect_eq]

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 2: projective measurements make distance exactly twice the
pointwise defect. -/
theorem point_distance_eq_two_defect_of_projective
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B) :
    (∑ a : α, ‖applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2) =
      2 * (∑ a : α, ∑ b : α,
        if a = b then 0 else stateQForm ψ (A.effect a * B.effect b)) := by
  calc
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      exact norm_effect_sub_effect_sq_expand A B ψ a
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [(hA a).isIdempotentElem.eq, (hB a).isIdempotentElem.eq]
    _ = (∑ a : α, stateQForm ψ (A.effect a)) +
          (∑ a : α, stateQForm ψ (B.effect a)) -
          2 * (∑ a : α, stateQForm ψ (A.effect a * B.effect a)) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 2 * (‖ψ‖ ^ 2 -
          ∑ a : α, stateQForm ψ (A.effect a * B.effect a)) := by
      simp [stateQForm_effect_sum]
      ring
    _ = _ := by rw [point_defect_eq]

end

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 2: state-dependent squared distance between operator families is
nonnegative. -/
theorem opFamilyDistSq_nonneg {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (M N : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    0 ≤ opFamilyDistSq μ M N ψ := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonnegative x)
    (Finset.sum_nonneg fun a _ => sq_nonneg _)

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- View the coordinate function of an LDT pure state as a Euclidean vector.

The theorem `pureState_stateQForm_eq_ev` below identifies the
quadratic form of that vector with evaluation in the associated density state.
Both constructions and that identity are stated here for an arbitrary finite
index type, and are used both by the distance calculus and by the low-degree
consistency transport; the two formulations of consistency they relate are
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395` and
`references/ldt-paper/preliminaries.tex:649-666`. -/
noncomputable def pureStateEuclideanVector
    (ψ : PureState ι) : EuclideanSpace ℂ ι :=
  (EuclideanSpace.equiv ι ℂ).symm ψ.vector

/-- The Euclidean vector associated with an LDT pure state has norm one. -/
theorem pureStateEuclideanVector_norm
    (ψ : PureState ι) : ‖pureStateEuclideanVector ψ‖ = 1 := by
  have hsquareComplex :
      ((‖pureStateEuclideanVector ψ‖ ^ 2 : ℝ) : ℂ) = 1 := by
    calc
      _ =
          (‖pureStateEuclideanVector ψ‖ : ℂ) ^ 2 := by norm_cast
      _ = _ :=
        (inner_self_eq_norm_sq_to_K (pureStateEuclideanVector ψ)).symm
      _ = _ :=
        EuclideanSpace.inner_eq_star_dotProduct _ _
      _ = _ := dotProduct_comm _ _
      _ = 1 := ψ.unit
  have hsquare : ‖pureStateEuclideanVector ψ‖ ^ 2 = 1 := by
    exact_mod_cast hsquareComplex
  nlinarith [norm_nonneg (pureStateEuclideanVector ψ)]

/-- Evaluation in a pure LDT density state is the quadratic form of its
Euclidean vector.  This identity relates the density formulation of consistency
to the vector formulation; see
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`. -/
theorem pureState_stateQForm_eq_ev
    (ψ : PureState ι) (T : Op ι) :
    stateQForm (pureStateEuclideanVector ψ) T = ev (ψ : QuantumState ι) T := by
  rw [PureState.ev_eq_re_inner]
  unfold stateQForm applyOperatorToState
  simp [dotProduct_comm]
  rfl

end

variable {X α ι : Type*}

/-- Formalization-only auxiliary lemma for Proposition 4.29: on a unit state and
probability distribution, defect is one minus diagonal overlap. -/
theorem consistencyDefect_eq_one_sub_overlap
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    {μ : Distribution X} (A B : X → MIPStarRE.Quantum.Measurement α ι)
    {ψ : EuclideanSpace ℂ ι} (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) :
    consistencyDefect μ (fun x a => (A x).effect a)
        (fun x a => (B x).effect a) ψ =
      1 - avgOver μ (fun x => ∑ a,
        stateQForm ψ ((A x).effect a * (B x).effect a)) := by
  calc
    _ =
      _ := by
      apply avgOver_congr
      intro x
      apply point_defect_eq
    _ = _ :=
      avgOver_sub μ _ _
    _ = _ := by
      simp [hψ, avgOver_const_of_isProbability μ hμ]

/-- Formalization-only auxiliary lemma for Proposition 4.29: state-dependent
operator-family distance is symmetric. -/
theorem opFamilyDistSq_symm
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq μ A B ψ = opFamilyDistSq μ B A ψ := by
  apply avgOver_congr
  intro x
  congr 1 with a
  simp [applyOperatorToState]
  rw [norm_sub_rev]

end MIPStarRE.QPBT.DistanceCalculus

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

variable {X α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

/-- The squared effects of a POVM sum to at most the identity. This is the
formalization-only estimate `lem:sandwich-povm-square-sum` used in the
contractions underlying `lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem measurement_sum_adjoint_mul_le_one
    (M : Measurement α ι) :
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ 1 := by
  rw [← M.sum_eq_one]
  apply Finset.sum_le_sum
  intro a _
  rw [measurement_effect_hermitian]
  exact MIPStarRE.Quantum.sq_le_self (M.pos a) (measurement_effect_le_one M a)

theorem norm_image_sq (ψ : EuclideanSpace ℂ ι) (W : Op ι) :
    ‖applyOperatorToState W ψ‖ ^ 2 = stateQForm ψ (Wᴴ * W) := norm_applyOperatorToState_sq_eq W ψ

theorem effect_sandwich_nonneg (M : Measurement α ι) (a : α) {V : Op ι} (h : 0 ≤ V) :
    0 ≤ M.effect a * V * M.effect a := Matrix.nonneg_iff_posSemidef.mpr (by
  simpa only [measurement_effect_hermitian] using
    (Matrix.nonneg_iff_posSemidef.mp h).conjTranspose_mul_mul_same (M.effect a))

theorem measurement_mass_le (ψ : EuclideanSpace ℂ ι) (M : Measurement α ι) :
    ∑ a, ‖applyOperatorToState (M.effect a) ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
  simpa [applyOperatorToState] using
    sum_norm_mul_apply_le M.effect 1 ψ (measurement_sum_adjoint_mul_le_one M)

theorem stateQForm_mul_inner (ψ : EuclideanSpace ℂ ι) (U V : Op ι) :
    stateQForm ψ (U * V) = (inner ℂ (applyOperatorToState Uᴴ ψ) (applyOperatorToState V ψ)).re := by
  simp [stateQForm, applyOperatorToState, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_left]

theorem projective_mass (M : Measurement α ι) (hM : Measurement.IsProjective M)
    (ψ : EuclideanSpace ℂ ι) : ∑ a, ‖applyOperatorToState (M.effect a) ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  simp_rw [norm_applyOperatorToState_sq_eq, measurement_effect_hermitian, fun a => (hM a).isIdempotentElem.eq]
  exact (stateQForm_finset_sum ψ _ _).symm.trans (by rw [M.sum_eq_one, stateQForm_one])

theorem abs_sum_inner_re_le (u v : α → EuclideanSpace ℂ ι) :
    |∑ a, (inner ℂ (u a) (v a)).re| ≤
      Real.sqrt (∑ a, ‖u a‖ ^ 2) * Real.sqrt (∑ a, ‖v a‖ ^ 2) := by
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ‖u a‖ * ‖v a‖ := Finset.sum_le_sum fun a _ =>
      (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- Cauchy–Schwarz weighted by a complete measurement. -/
theorem abs_sum_effect_mul_le {ψ : EuclideanSpace ℂ ι} (M : Measurement α ι)
    (V : α → Op ι) (hψ : ‖ψ‖ = 1) :
    |∑ a, stateQForm ψ (M.effect a * V a)| ≤
      Real.sqrt (∑ a, ‖applyOperatorToState (V a) ψ‖ ^ 2) := by
  simp only [stateQForm_mul_inner, measurement_effect_hermitian]
  refine (abs_sum_inner_re_le _ _).trans ?_
  have h := Real.sqrt_le_sqrt (measurement_mass_le ψ M)
  simp only [hψ, one_pow, Real.sqrt_one] at h
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) h

/-- Distance controls the change in overlap with a fixed measurement. -/
theorem abs_overlap_gap_le_sqrt_of_opFamilyDistSq (μ : Distribution X) (A : X → Measurement α ι)
    (B C : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    {ζ : ℝ} (hBC : opFamilyDistSq μ B C ψ ≤ ζ) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a)) -
      avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a))| ≤ Real.sqrt ζ := by
  have h := Preliminaries.avgOver_abs_le_sqrt_of_pointwise μ _ _
    (fun x => abs_sum_effect_mul_le (A x) (fun a => B x a - C x a) hψ)
    (fun x => Finset.sum_nonneg fun a _ => sq_nonneg _) hμ.weight_sum_eq_one.le
  simp only [mul_sub, stateQForm_sub, Finset.sum_sub_distrib, avgOver_sub] at h
  exact h.trans (Real.sqrt_le_sqrt hBC)

end MIPStarRE.QPBT
