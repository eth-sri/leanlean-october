module

public import QPBT.Games.Consistency
public import MIPStarRE.LDT.Basic.DistributionAvg
public import MIPStarRE.LDT.MakingMeasurementsProjective.Defs
public import MIPStarRE.LDT.Preliminaries.CauchySchwarz
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

section OperatorAction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Moving a matrix action between the arguments of the inner product takes its adjoint. -/
theorem inner_applyOperatorToState_adjoint (M : Op ι) (u v : EuclideanSpace ℂ ι) :
    inner ℂ u (applyOperatorToState Mᴴ v) = inner ℂ (applyOperatorToState M u) v := by
  simp [applyOperatorToState, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]

/-- The mixed inner product obtained by splitting a product inside an expectation. -/
theorem stateQForm_mul_eq_inner (ψ : EuclideanSpace ℂ ι) (M N : Op ι) :
    stateQForm ψ (M * N) =
      (inner ℂ (applyOperatorToState Mᴴ ψ) (applyOperatorToState N ψ)).re := by
  simp [stateQForm, applyOperatorToState, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_left]

/-- The squared norm of `M ψ` is the quadratic form of `Mᴴ M`. -/
theorem norm_applyOperatorToState_sq (M : Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState M ψ‖ ^ 2 = stateQForm ψ (Mᴴ * M) := by
  rw [stateQForm_mul_eq_inner, Matrix.conjTranspose_conjTranspose]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm

/-- Polarization of the squared distance between two operator images. -/
theorem norm_applyOperatorToState_sub_sq (M N : Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (M - N) ψ‖ ^ 2 =
      ‖applyOperatorToState M ψ‖ ^ 2 + ‖applyOperatorToState N ψ‖ ^ 2 -
        2 * stateQForm ψ (Mᴴ * N) := by
  rw [stateQForm_mul_eq_inner, Matrix.conjTranspose_conjTranspose]
  simp only [applyOperatorToState, map_sub, LinearMap.sub_apply, norm_sub_sq (𝕜 := ℂ),
    RCLike.re_to_complex]
  ring

end OperatorAction

section

variable {ι : Type*}
    [Fintype ι] [DecidableEq ι]
include ι

/-- Formalization-only auxiliary lemma for Fact 4.20: evaluation in a fixed
vector preserves operator order. -/
theorem quadratic_form_mono
    {S T : Op ι} (hST : S ≤ T) (v : EuclideanSpace ℂ ι) :
    (inner ℂ v (applyOperatorToState S v)).re ≤
      (inner ℂ v (applyOperatorToState T v)).re := by
  have hpsd : (T - S).PosSemidef := Matrix.le_iff.mp hST
  have hnonneg := hpsd.dotProduct_mulVec_nonneg v
  have hdiff : 0 ≤ (inner ℂ v (applyOperatorToState (T - S) v)).re := by
    simp only [applyOperatorToState, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    rw [dotProduct_comm]
    exact (Complex.nonneg_iff.mp hnonneg).1
  rw [show T = S + (T - S) by abel]
  simp only [applyOperatorToState, map_add, LinearMap.add_apply, inner_add_right,
    Complex.add_re]
  exact le_add_of_nonneg_right hdiff

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
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]

/-- A positive semidefinite operator has nonnegative state quadratic form. This
is the formalization-only order fact `lem:distance-qform-nonnegative`, used for
the nonnegative overlap terms in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_nonneg
    (ψ : EuclideanSpace ℂ ι) {M : Op ι} (hM : 0 ≤ M) :
    0 ≤ stateQForm ψ M := by
  calc
    0 = stateQForm ψ 0 := by simp [stateQForm, applyOperatorToState]
    _ ≤ stateQForm ψ M := quadratic_form_mono hM ψ

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): the state quadratic form is additive in its operator. -/
theorem stateQForm_add
    (ψ : EuclideanSpace ℂ ι) (M N : Op ι) :
    stateQForm ψ (M + N) = stateQForm ψ M + stateQForm ψ N := by
  simp [stateQForm, applyOperatorToState]

/-- The state quadratic form preserves operator subtraction. -/
theorem stateQForm_sub
    (ψ : EuclideanSpace ℂ ι) (M N : Op ι) :
    stateQForm ψ (M - N) = stateQForm ψ M - stateQForm ψ N := by
  simp [stateQForm, applyOperatorToState]

end

/-- The state quadratic form commutes with a finite sum. -/
private theorem stateQForm_sum {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : α → Op ι) :
    stateQForm ψ (∑ a, M a) = ∑ a, stateQForm ψ (M a) := by
  simp [stateQForm, applyOperatorToState]

/-- The quadratic form of the identity is the squared vector norm. -/
theorem stateQForm_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) :
    stateQForm ψ (1 : Op ι) = ‖ψ‖ ^ 2 := by
  simpa [stateQForm, applyOperatorToState] using inner_self_eq_norm_sq (𝕜 := ℂ) ψ

/-- The total squared norm is the expectation of the sum of the Gram operators. -/
theorem sum_norm_applyOperatorToState_sq {γ ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset γ) (C : γ → Op ι) :
    ∑ c ∈ s, ‖applyOperatorToState (C c) ψ‖ ^ 2 = stateQForm ψ (∑ c ∈ s, (C c)ᴴ * C c) := by
  simp only [norm_applyOperatorToState_sq, stateQForm_finset_sum]

/-- Evaluation at a fixed vector preserves the positive semidefinite order. -/
theorem stateQForm_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) {M N : Op ι} (h : M ≤ N) : stateQForm ψ M ≤ stateQForm ψ N :=
  quadratic_form_mono h ψ

/-- Finite-subset form of contraction by square-summable left multipliers. -/
private theorem finset_sum_norm_mul_apply_le {γ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (s : Finset γ) (C : γ → Op ι) (D : Op ι) (v : EuclideanSpace ℂ ι)
    (hC : ∑ c ∈ s, (C c)ᴴ * C c ≤ 1) :
    ∑ c ∈ s, ‖applyOperatorToState (C c * D) v‖ ^ 2 ≤
      ‖applyOperatorToState D v‖ ^ 2 := by
  simp_rw [applyOperatorToState_mul]
  rw [sum_norm_applyOperatorToState_sq, ← stateQForm_one]
  exact stateQForm_mono _ hC

/-- Formalization-only auxiliary lemma for Fact 4.20: a square-summable family
of left multipliers contracts total squared norm. -/
theorem sum_norm_mul_apply_le {γ ι : Type*}
    [Fintype γ] [Fintype ι] [DecidableEq ι]
    (C : γ → Op ι) (D : Op ι) (v : EuclideanSpace ℂ ι)
    (hC : ∑ c : γ, (C c)ᴴ * C c ≤ 1) :
    ∑ c : γ, ‖applyOperatorToState (C c * D) v‖ ^ 2 ≤
      ‖applyOperatorToState D v‖ ^ 2 := by
  simpa using finset_sum_norm_mul_apply_le Finset.univ C D v (by simpa using hC)

/-- The squared norm of a two-term sum. -/
theorem norm_add_sq_le_two {E : Type*} [NormedAddCommGroup E] (u v : E) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  nlinarith only [pow_le_pow_left₀ (norm_nonneg _) (norm_add_le u v) 2, sq_nonneg (‖u‖ - ‖v‖)]

/-- A nonnegative quantity bounded by three terms satisfies the corresponding squared bound. -/
theorem sq_le_three_sq_of_le {t a b c : ℝ} (ht : 0 ≤ t) (h : t ≤ a + b + c) :
    t ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have := (sq_le_sq₀ ht (ht.trans h)).2 h
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- The squared distance between two square-summable operator families is at
most four on a unit vector. Formalization-only auxiliary bounding the
state-dependent distance of `def:povm-distance` trivially. -/
theorem sum_norm_sub_apply_sq_le_four {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (A B : α → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (hA : ∑ a : α, (A a)ᴴ * A a ≤ 1)
    (hB : ∑ a : α, (B a)ᴴ * B a ≤ 1) :
    ∑ a : α, ‖applyOperatorToState (A a - B a) ψ‖ ^ 2 ≤ 4 := by
  have hm (C : α → Op ι) (hC : ∑ a, (C a)ᴴ * C a ≤ 1) :
      ∑ a, ‖applyOperatorToState (C a) ψ‖ ^ 2 ≤ 1 := by
    simpa only [mul_one, applyOperatorToState_one, hψ, one_pow] using sum_norm_mul_apply_le C 1 ψ hC
  have h := Finset.sum_le_sum (s := Finset.univ) fun a _ => by
    simpa only [← sub_eq_add_neg, applyOperatorToState, map_sub, LinearMap.sub_apply,
      norm_neg] using norm_add_sq_le_two (applyOperatorToState (A a) ψ)
        (-applyOperatorToState (B a) ψ)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  simp only [applyOperatorToState, map_sub, LinearMap.sub_apply] at hm ⊢
  linarith only [h, hm A hA, hm B hB]

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
  rw [← Finset.sum_fiberwise_apply Finset.univ eval
    (fun g a => ‖applyOperatorToState (S g * D a) v‖ ^ 2)]
  apply Finset.sum_le_sum
  intro a _
  apply finset_sum_norm_mul_apply_le
  calc
    ∑ g ∈ Finset.univ.filter (fun g => eval g = a), (S g)ᴴ * S g ≤
        ∑ g : Γ, (S g)ᴴ * S g := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun g _ _ => star_mul_self_nonneg (S g))
    _ ≤ 1 := hS

/-- Formalization-only auxiliary lemma for the projective-sum estimate at paper
lines 364--380: distinct effects of a projective measurement are orthogonal. -/
theorem projective_effect_mul_effect_eq_zero {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    {a b : α} (hab : a ≠ b) :
    M.effect a * M.effect b = 0 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      letI := hι
      exact Subsingleton.elim _ _
  | inr hι =>
      letI := hι
      let H : FiniteHilbertSpace :=
        { carrier := ι
          instFintype := inferInstance
          instDecidableEq := inferInstance
          instNonempty := inferInstance }
      let P : ProjMeas α ι :=
        { toMeasurement := MatrixMeasurement.toMeasurement (H := H) M
          proj := fun a => (hM a).isIdempotentElem.eq }
      simpa [P, H] using P.outcome_orthogonal a b hab

/-- Gram expansion for a finite sum with mutually orthogonal left projectors. -/
theorem gram_finset_sum_projector_mul {α ι : Type*}
    [Fintype ι] (P D : α → Op ι) (hproj : ∀ a, IsProj (P a)) (s : Finset α)
    (horth : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → P a * P b = 0) :
    (∑ a ∈ s, P a * D a)ᴴ * (∑ a ∈ s, P a * D a) =
      ∑ a ∈ s, (D a)ᴴ * P a * D a := by
  classical
  have hterm (a b : α) : (P a * D a)ᴴ * (P b * D b) = (D a)ᴴ * (P a * P b) * D b := by
    have hstar : (P a)ᴴ = P a := (hproj a).isSelfAdjoint.star_eq
    simp only [Matrix.conjTranspose_mul, hstar, mul_assoc]
  rw [Matrix.conjTranspose_sum, Finset.sum_mul]
  simp only [Finset.mul_sum, hterm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_eq_single_of_mem a ha]
  · rw [(hproj a).isIdempotentElem.eq]
  · intro b hb hne
    rw [horth a ha b hb hne.symm, mul_zero, zero_mul]

/-- Formalization-only auxiliary lemma for the projective-sum estimate at paper
lines 364--380: an orthogonal projective left sum is bounded by the full input
norm sum. -/
theorem norm_finset_sum_projector_mul_sq_le {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (P D : α → Op ι) (hproj : ∀ a, IsProj (P a))
    (horth : ∀ {a b}, a ≠ b → P a * P b = 0)
    (s : Finset α) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (∑ a ∈ s, P a * D a) ψ‖ ^ 2 ≤
      ∑ a : α, ‖applyOperatorToState (D a) ψ‖ ^ 2 := by
  classical
  have hgram :
      (∑ a ∈ s, P a * D a)ᴴ * (∑ a ∈ s, P a * D a) ≤
        ∑ a : α, (D a)ᴴ * D a := by
    rw [gram_finset_sum_projector_mul P D hproj s (fun _ _ _ _ h => horth h)]
    calc
      ∑ a ∈ s, (D a)ᴴ * P a * D a ≤
          ∑ a ∈ s, (D a)ᴴ * D a := by
        refine Finset.sum_le_sum ?_
        intro a _
        simpa [Matrix.star_eq_conjTranspose] using
          (star_left_conjugate_le_conjugate (hproj a).le_one (D a))
      _ ≤ ∑ a : α, (D a)ᴴ * D a :=
        Finset.sum_le_sum_of_subset_of_nonneg (by simp)
          (fun a _ _ => (Matrix.posSemidef_conjTranspose_mul_self (D a)).nonneg)
  rw [norm_applyOperatorToState_sq]
  calc
    (inner ℂ ψ (applyOperatorToState
        ((∑ a ∈ s, P a * D a)ᴴ * (∑ a ∈ s, P a * D a)) ψ)).re ≤
        (inner ℂ ψ (applyOperatorToState (∑ a : α, (D a)ᴴ * D a) ψ)).re :=
      quadratic_form_mono hgram ψ
    _ = ∑ a : α,
          (inner ℂ ψ (applyOperatorToState ((D a)ᴴ * D a) ψ)).re := by
      simp [applyOperatorToState]
    _ = ∑ a : α, ‖applyOperatorToState (D a) ψ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      exact (norm_applyOperatorToState_sq (D a) ψ).symm

/-- The state quadratic form is linear in real scalars on the operator. -/
theorem stateQForm_real_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (c : ℝ) (A : Op ι) :
    stateQForm ψ (c • A) = c * stateQForm ψ A := by
  rw [← Complex.coe_smul]
  simp only [stateQForm, applyOperatorToState, map_smul, LinearMap.smul_apply,
    inner_smul_right, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- The state quadratic form is invariant under simultaneous reindexing. -/
theorem stateQForm_reindexState {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (T : Op κ) (ψ : EuclideanSpace ℂ ι) :
    stateQForm (reindexState e ψ) T = stateQForm ψ (reindexOp e T) := by
  rw [stateQForm, applyOperatorToState_reindexState]
  simp only [reindexState_eq, LinearIsometryEquiv.inner_map_map, stateQForm]

/-- The quadratic form of `Wᴴ M W` in `ψ` is the quadratic form of `M` in
`W ψ`.  This is the conjugation identity behind the placed-sandwich
rewritings: conjugating transfers the outer operator to the state vector.
It is formalization-only auxiliary content, shared by the overlap-gap estimate
and the sandwich self-consistency argument. -/
theorem stateQForm_conjTranspose_mul_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (W M : Op ι) :
    stateQForm ψ (Wᴴ * M * W) = stateQForm (applyOperatorToState W ψ) M := by
  unfold stateQForm
  rw [applyOperatorToState_mul, applyOperatorToState_mul]
  congr 1
  exact inner_applyOperatorToState_adjoint W _ _

section

variable {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι) (a : α)
include α ι M a

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): every effect of a complete measurement is bounded by the identity. -/
theorem measurement_effect_le_one :
    M.effect a ≤ 1 := by
  calc
    M.effect a ≤ ∑ b : α, M.effect b :=
      Finset.single_le_sum (fun b _ => M.pos b) (Finset.mem_univ a)
    _ = 1 := M.sum_eq_one

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): every positive measurement effect is Hermitian. -/
theorem measurement_effect_hermitian :
    (M.effect a)ᴴ = M.effect a :=
  (Matrix.nonneg_iff_posSemidef.mp (M.pos a)).isHermitian.eq

end

/-- The squared effects of a POVM sum to at most the identity. This is the
formalization-only estimate `lem:sandwich-povm-square-sum` used in the
contractions underlying `lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem _root_.MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
    {α I : Type*} [Fintype α] [Fintype I] [DecidableEq I]
    (M : Quantum.Measurement α I) :
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ 1 := by
  calc
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ ∑ a : α, M.effect a := by
      apply Finset.sum_le_sum
      intro a _
      rw [measurement_effect_hermitian]
      exact MIPStarRE.Quantum.sq_le_self (M.pos a) (measurement_effect_le_one M a)
    _ = 1 := M.sum_eq_one

/-- Expand the squared state-dependent distance between two measurement effects. -/
private theorem norm_effect_sub_effect_sq_expand {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (A B : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (a : α) :
    ‖applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2 =
      stateQForm ψ (A.effect a * A.effect a) +
      stateQForm ψ (B.effect a * B.effect a) -
      2 * stateQForm ψ (A.effect a * B.effect a) := by
  rw [norm_applyOperatorToState_sub_sq]
  simp only [norm_applyOperatorToState_sq, measurement_effect_hermitian]

/-- Removing the diagonal term from a finite sum is subtraction of that term. -/
private theorem sum_if_eq_zero_else {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (a : α) :
    (∑ b : α, if a = b then 0 else f b) = (∑ b : α, f b) - f a := by
  rw [← Finset.sum_erase_eq_sub (Finset.mem_univ a), ← Finset.filter_ne']
  simp [Finset.sum_filter, eq_comm]

section

variable {α ι : Type*} [Fintype α]
include α ι

/-- Summing a complete measurement in the right factor leaves the first operator. -/
private theorem stateQForm_mul_sum_right
    [Fintype ι] [DecidableEq ι]
    (B : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (M : Op ι) :
    (∑ b : α, stateQForm ψ (M * B.effect b)) = stateQForm ψ M := by
  rw [← stateQForm_sum, ← Finset.mul_sum, B.sum_eq_one, mul_one]

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
  simp_rw [sum_if_eq_zero_else, stateQForm_mul_sum_right B ψ,
    Finset.sum_sub_distrib, stateQForm_effect_sum A ψ]

end

/-- Two pairs of complete measurements with the same overlap have the same defect. -/
theorem measurementDefect_eq_of_overlap {X α β I : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype I] [DecidableEq I] (μ : Distribution X)
    (A B : X → Quantum.Measurement α I) (C D : X → Quantum.Measurement β I)
    (ψ : EuclideanSpace ℂ I)
    (h : ∀ x, (∑ a, (A x).effect a * (B x).effect a) = ∑ b, (C x).effect b * (D x).effect b) :
    measurementDefect μ A B ψ = measurementDefect μ C D ψ := by
  unfold measurementDefect consistencyDefect
  exact avgOver_congr _ _ _ fun x => by
    simp only [point_defect_eq, ← stateQForm_finset_sum, h]

/-- Reversing complete measurements preserves real consistency. -/
theorem measurementDefect_symm {X α I : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    (μ : Distribution X) (A B : X → Quantum.Measurement α I) (ψ : EuclideanSpace ℂ I) :
    measurementDefect μ A B ψ = measurementDefect μ B A ψ := by
  unfold measurementDefect consistencyDefect
  refine avgOver_congr _ _ _ fun x => ?_
  rw [point_defect_eq (A x) (B x), point_defect_eq (B x) (A x)]
  simp only [stateQForm_mul_eq_inner, measurement_effect_hermitian]
  congr 1
  exact Finset.sum_congr rfl fun a _ => inner_re_symm (𝕜 := ℂ) _ _

section

variable {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (A B : MIPStarRE.Quantum.Measurement α ι) (ψ : EuclideanSpace ℂ ι)
include α ι A B ψ

private theorem sum_effect_diag_eq_two_defect :
    (∑ a, (stateQForm ψ (A.effect a) + stateQForm ψ (B.effect a) -
        2 * stateQForm ψ (A.effect a * B.effect a))) =
      2 * (∑ a, ∑ b, if a = b then 0 else stateQForm ψ (A.effect a * B.effect b)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    stateQForm_effect_sum, stateQForm_effect_sum, point_defect_eq]
  ring

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 1: pointwise measurement distance is at most twice the
inconsistency defect. -/
theorem point_distance_le_two_defect :
    (∑ a : α, ‖applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2) ≤
      2 * (∑ a : α, ∑ b : α,
        if a = b then 0 else stateQForm ψ (A.effect a * B.effect b)) := by
  rw [← sum_effect_diag_eq_two_defect A B ψ]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [norm_effect_sub_effect_sq_expand A B ψ a]
  exact sub_le_sub_right (add_le_add
    (quadratic_form_mono (MIPStarRE.Quantum.sq_le_self (A.pos a) (measurement_effect_le_one A a)) ψ)
    (quadratic_form_mono (MIPStarRE.Quantum.sq_le_self (B.pos a) (measurement_effect_le_one B a)) ψ)) _

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 2: projective measurements make distance exactly twice the
pointwise defect. -/
theorem point_distance_eq_two_defect_of_projective
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B) :
    (∑ a : α, ‖applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2) =
      2 * (∑ a : α, ∑ b : α,
        if a = b then 0 else stateQForm ψ (A.effect a * B.effect b)) := by
  rw [← sum_effect_diag_eq_two_defect A B ψ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [norm_effect_sub_effect_sq_expand A B ψ a,
    (hA a).isIdempotentElem.eq, (hB a).isIdempotentElem.eq]

end

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 2: state-dependent squared distance between operator families is
nonnegative. -/
theorem opFamilyDistSq_nonneg {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (M N : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    0 ≤ opFamilyDistSq μ M N ψ := by
  unfold opFamilyDistSq avgOver
  exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonnegative x)
    (Finset.sum_nonneg fun a _ => sq_nonneg _)

section

variable {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
include ι

/-- Regard a unit Euclidean vector as an LDT pure state. -/
noncomputable def pureStateOfUnitVector
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) : PureState ι where
  vector := ψ.ofLp
  unit := by
    calc
      star ψ.ofLp ⬝ᵥ ψ.ofLp = ψ.ofLp ⬝ᵥ star ψ.ofLp := dotProduct_comm _ _
      _ = inner ℂ ψ ψ := (EuclideanSpace.inner_eq_star_dotProduct ψ ψ).symm
      _ = (‖ψ‖ ^ 2 : ℂ) := inner_self_eq_norm_sq_to_K ψ
      _ = 1 := by rw [hψ]; norm_num

/-- View the coordinate function of an LDT pure state as a Euclidean vector.

This construction sends a pure state to its Euclidean coordinate vector, and
`pureStateOfUnitVector` above reads a unit Euclidean vector as a pure state.
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
      ((‖pureStateEuclideanVector ψ‖ ^ 2 : ℝ) : ℂ) =
          (‖pureStateEuclideanVector ψ‖ : ℂ) ^ 2 := by norm_cast
      _ = inner ℂ (pureStateEuclideanVector ψ)
          (pureStateEuclideanVector ψ) :=
        (inner_self_eq_norm_sq_to_K (pureStateEuclideanVector ψ)).symm
      _ = ψ.vector ⬝ᵥ star ψ.vector :=
        EuclideanSpace.inner_eq_star_dotProduct _ _
      _ = star ψ.vector ⬝ᵥ ψ.vector := dotProduct_comm _ _
      _ = 1 := ψ.unit
  have hsquare : ‖pureStateEuclideanVector ψ‖ ^ 2 = (1 : ℝ) := by
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
  change (inner ℂ (pureStateEuclideanVector ψ)
      (WithLp.toLp 2 (T *ᵥ ψ.vector))).re =
    (star ψ.vector ⬝ᵥ T *ᵥ ψ.vector).re
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

end

section

variable {X α I : Type*} [Fintype α] [Fintype I] [DecidableEq I]
include X α I

/-- Complete measurements have average squared effect mass at most one. -/
theorem measurement_mass_le_one
    (D : Distribution X) (A : X → Quantum.Measurement α I)
    (ψ : EuclideanSpace ℂ I) (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) :
    opFamilyDistSq D (fun x a => (A x).effect a) (fun _ _ => 0) ψ ≤ 1 := by
  rw [← avgOver_const_of_isProbability D hD (1 : ℝ)]
  apply avgOver_mono
  intro x
  simp only [sub_zero]
  rw [sum_norm_applyOperatorToState_sq, ← show stateQForm ψ (1 : Op I) = 1 by
    rw [stateQForm_one, hψ, one_pow]]
  exact quadratic_form_mono (measurement_sum_adjoint_mul_le_one (A x)) ψ

/-- Cauchy–Schwarz for the averaged real inner product of two operator families. -/
theorem abs_avgOver_inner_le
    (μ : Distribution X) (U V : X → α → Op I) (ψ : EuclideanSpace ℂ I) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((U x a)ᴴ * V x a))| ≤
      Real.sqrt (opFamilyDistSq μ U (fun _ _ => 0) ψ) *
        Real.sqrt (opFamilyDistSq μ V (fun _ _ => 0) ψ) := by
  simp only [opFamilyDistSq, sub_zero]
  refine Preliminaries.weightedFinsetCauchySchwarz μ _ _ _ ?_
    (fun _ _ => sq_nonneg _) (fun _ _ => sq_nonneg _)
  intro x a
  simp only [stateQForm_mul_eq_inner, Matrix.conjTranspose_conjTranspose,
    Real.sqrt_sq (norm_nonneg _)]
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)

/-- A complete measurement bounds the change in overlap by the root of the squared distance. -/
theorem abs_overlap_gap_le_sqrt_of_opFamilyDistSq
    (μ : Distribution X) (A : X → Quantum.Measurement α I) (B C : X → α → Op I)
    (ψ : EuclideanSpace ℂ I) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (ζ : ℝ) (hBC : opFamilyDistSq μ B C ψ ≤ ζ) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a)) -
        avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a))| ≤ Real.sqrt ζ := by
  have h := abs_avgOver_inner_le μ (fun x => (A x).effect) (fun x a => B x a - C x a) ψ
  have hdist : opFamilyDistSq μ (fun x a => B x a - C x a) (fun _ _ => 0) ψ ≤ ζ := by
    simpa only [opFamilyDistSq, sub_zero] using hBC
  simpa only [measurement_effect_hermitian, mul_sub, stateQForm_sub, Finset.sum_sub_distrib,
    avgOver_sub, Real.sqrt_one, one_mul] using h.trans
      (mul_le_mul (Real.sqrt_le_sqrt (measurement_mass_le_one μ A ψ hμ hψ))
        (Real.sqrt_le_sqrt hdist) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end

/-- Formalization-only auxiliary lemma for Proposition 4.29: on a unit state and
probability distribution, defect is one minus diagonal overlap. -/
theorem consistencyDefect_eq_one_sub_overlap {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) :
    measurementDefect μ A
        B ψ =
      1 - avgOver μ (fun x => ∑ a,
        stateQForm ψ ((A x).effect a * (B x).effect a)) := by
  simp only [measurementDefect, consistencyDefect, point_defect_eq, hψ, one_pow,
    avgOver_sub, avgOver_const_of_isProbability μ hμ]

/-- Formalization-only auxiliary lemma for Proposition 4.29: state-dependent
operator-family distance is symmetric. -/
theorem opFamilyDistSq_symm {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq μ A B ψ = opFamilyDistSq μ B A ψ := by
  unfold opFamilyDistSq
  apply avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  simp only [applyOperatorToState, map_sub, LinearMap.sub_apply]
  rw [norm_sub_rev]

end MIPStarRE.QPBT.DistanceCalculus
