module

public import QPBT.Combining.Lines
public import QPBT.Combining.ErrorBounds
public import QPBT.Games.DistanceTheorems.Support
public import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.InnerProduct

/-! # Consolidated overlap-gap inequalities, X/Z evaluation deficits, and extended lines -/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## Measurement-weighted Cauchy--Schwarz and overlap-gap estimates -/

theorem stateQForm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : Op ι) : stateQForm ψ Mᴴ = stateQForm ψ M := by
  unfold stateQForm
  change (inner ℂ ψ (Matrix.toEuclideanLin Mᴴ ψ)).re = (inner ℂ ψ (Matrix.toEuclideanLin M ψ)).re
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right,
    ← inner_conj_symm, Complex.conj_re]

theorem stateQForm_applyOperatorToState_eq_of_isProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) {A B : Op ι} (hB : IsProj B) (hAB : Commute A B) :
    stateQForm (applyOperatorToState B ψ) A = stateQForm ψ (A * B) := by
  rw [← stateQForm_conjTranspose_mul_mul, hB.isSelfAdjoint.isHermitian.eq,
    ← hAB.eq, mul_assoc, hB.isIdempotentElem.eq]

theorem sum_stateQForm_effect_eq_one {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : Measurement α ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) :
    (∑ a : α, stateQForm ψ (A.effect a)) = 1 := by
  have hs : (∑ a : α, stateQForm ψ (A.effect a)) = stateQForm ψ (∑ a, A.effect a) := by
    simp [stateQForm, applyOperatorToState]
  rw [hs, A.sum_eq_one, stateQForm_one, hψ, one_pow]

theorem abs_overlap_gap_le_sqrt_of_opFamilyDistSq {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A : X → Measurement α ι) (B C : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (ζ : ℝ) (hBC : opFamilyDistSq μ B C ψ ≤ ζ) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a)) -
      avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a))| ≤ Real.sqrt ζ := by
  have hnsq (M : Op ι) : ‖applyOperatorToState M ψ‖ ^ 2 = stateQForm ψ (Mᴴ * M) := by
    rw [@norm_sq_eq_re_inner ℂ]; unfold stateQForm applyOperatorToState
    rw [Matrix.toEuclideanLin_conjTranspose_mul_self]
    exact (congrArg Complex.re (LinearMap.adjoint_inner_right _ _ _)).symm
  have hmul (M N : Op ι) (hM : Mᴴ = M) :
      stateQForm ψ (M * N) = (inner ℂ (applyOperatorToState M ψ) (applyOperatorToState N ψ)).re := by
    rw [stateQForm, applyOperatorToState_mul]
    have hadj : (Matrix.toEuclideanLin M).adjoint = Matrix.toEuclideanLin M := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hM]
    have h := LinearMap.adjoint_inner_right (Matrix.toEuclideanLin M) ψ (applyOperatorToState N ψ)
    rw [hadj] at h
    exact congrArg Complex.re h
  have hleft (x : X) : (∑ a, ‖applyOperatorToState ((A x).effect a) ψ‖ ^ 2) ≤ 1 := by
    refine (Finset.sum_le_sum fun a _ => ?_).trans_eq (sum_stateQForm_effect_eq_one (A x) ψ hψ)
    rw [hnsq, measurement_effect_hermitian]
    exact quadratic_form_mono (MIPStarRE.Quantum.sq_le_self ((A x).pos a)
      (measurement_effect_le_one (A x) a)) ψ
  have hpt (x : X) : |∑ a, stateQForm ψ ((A x).effect a * (B x a - C x a))| ≤
      Real.sqrt (∑ a, ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2) := by
    let u := fun a => applyOperatorToState ((A x).effect a) ψ
    let v := fun a => applyOperatorToState (B x a - C x a) ψ
    rw [Finset.sum_congr rfl fun a _ => hmul _ _ (measurement_effect_hermitian (A x) a)]
    have h1 := (Finset.abs_sum_le_sum_abs
      (fun a => (inner ℂ (u a) (v a)).re) Finset.univ).trans
      (Finset.sum_le_sum fun a _ => (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (u a) (v a)))
    have h2 : ∑ a, ‖u a‖ * ‖v a‖ ≤ Real.sqrt (∑ a, ‖u a‖ ^ 2) * Real.sqrt (∑ a, ‖v a‖ ^ 2) := by
      simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun a => ‖u a‖) (fun a => ‖v a‖)
    have hone : Real.sqrt (∑ a, ‖u a‖ ^ 2) ≤ 1 := by simpa using Real.sqrt_le_sqrt (hleft x)
    exact (h1.trans h2).trans ((mul_le_mul_of_nonneg_right hone (Real.sqrt_nonneg _)).trans_eq (one_mul _))
  have hdiff : avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a)) -
      avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a)) =
      avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (B x a - C x a))) := by
    rw [← avgOver_sub]; refine avgOver_congr μ _ _ fun x => ?_
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun a _ => ?_
    simp [stateQForm, applyOperatorToState, mul_sub]
  rw [hdiff]
  exact (MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise μ _ _ hpt
    (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (by rw [hμ.weight_sum_eq_one])).trans
    (Real.sqrt_le_sqrt hBC)

theorem abs_avgOver_sum_re_inner_le_sqrt_mul_sqrt {X α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (μ : Distribution X) (A : X → α → Op ι)
    (hA : ∀ x a, 0 ≤ A x a) (u v : X → α → EuclideanSpace ℂ ι) :
    |avgOver μ (fun x => ∑ a, (inner ℂ (u x a) (applyOperatorToState (A x a) (v x a))).re)| ≤
      Real.sqrt (avgOver μ (fun x => ∑ a, (inner ℂ (u x a) (applyOperatorToState (A x a) (u x a))).re)) *
        Real.sqrt (avgOver μ (fun x => ∑ a, (inner ℂ (v x a) (applyOperatorToState (A x a) (v x a))).re)) := by
  have hcs_op {B : Op ι} (hB : 0 ≤ B) (w z : EuclideanSpace ℂ ι) :
      ‖inner ℂ w (applyOperatorToState B z)‖ ≤
        Real.sqrt (inner ℂ w (applyOperatorToState B w)).re *
          Real.sqrt (inner ℂ z (applyOperatorToState B z)).re := by
    let R : Op ι := CFC.sqrt B
    have hRR : R * R = B := CFC.sqrt_mul_sqrt_self B hB
    have hadj : (Matrix.toEuclideanLin R).adjoint = Matrix.toEuclideanLin R := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
        (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq]
    have hsp (p q : EuclideanSpace ℂ ι) :
        inner ℂ p (applyOperatorToState B q) = inner ℂ (applyOperatorToState R p) (applyOperatorToState R q) := by
      rw [← hRR, applyOperatorToState_mul]
      have h := LinearMap.adjoint_inner_right (Matrix.toEuclideanLin R) p (Matrix.toEuclideanLin R q)
      rwa [hadj] at h
    have hn (p : EuclideanSpace ℂ ι) :
        ‖applyOperatorToState R p‖ = Real.sqrt (inner ℂ p (applyOperatorToState B p)).re := by
      have h2 : ‖applyOperatorToState R p‖ ^ 2 =
          (inner ℂ (applyOperatorToState R p) (applyOperatorToState R p)).re := by
        rw [@norm_sq_eq_re_inner ℂ]; rfl
      rw [hsp, ← h2, Real.sqrt_sq (norm_nonneg _)]
    rw [hsp, ← hn, ← hn]; exact norm_inner_le_norm _ _
  let f : X → ℝ := fun x => ∑ a, (inner ℂ (u x a) (applyOperatorToState (A x a) (v x a))).re
  let g : X → ℝ := fun x => ∑ a, (inner ℂ (u x a) (applyOperatorToState (A x a) (u x a))).re
  let h : X → ℝ := fun x => ∑ a, (inner ℂ (v x a) (applyOperatorToState (A x a) (v x a))).re
  have hu (x a) : 0 ≤ (inner ℂ (u x a) (applyOperatorToState (A x a) (u x a))).re :=
    stateQForm_nonneg (u x a) (hA x a)
  have hv (x a) : 0 ≤ (inner ℂ (v x a) (applyOperatorToState (A x a) (v x a))).re :=
    stateQForm_nonneg (v x a) (hA x a)
  have hg0 (x) : 0 ≤ g x := Finset.sum_nonneg fun a _ => hu x a
  have hh0 (x) : 0 ≤ h x := Finset.sum_nonneg fun a _ => hv x a
  have hpt (x : X) : |f x| ≤ Real.sqrt (g x) * Real.sqrt (h x) := by
    have h1 := (Finset.abs_sum_le_sum_abs
      (fun a => (inner ℂ (u x a) (applyOperatorToState (A x a) (v x a))).re) Finset.univ).trans
      (Finset.sum_le_sum fun a _ => (Complex.abs_re_le_norm _).trans (hcs_op (hA x a) (u x a) (v x a)))
    refine (h1.trans (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)).trans_eq ?_
    rw [Finset.sum_congr rfl fun a _ => Real.sq_sqrt (hu x a),
      Finset.sum_congr rfl fun a _ => Real.sq_sqrt (hv x a)]
  change |avgOver μ f| ≤ Real.sqrt (avgOver μ g) * Real.sqrt (avgOver μ h)
  unfold avgOver
  have hs1 : |∑ x ∈ μ.support, μ.weight x * f x| ≤
      ∑ x ∈ μ.support, μ.weight x * (Real.sqrt (g x) * Real.sqrt (h x)) :=
    (Finset.abs_sum_le_sum_abs (fun x => μ.weight x * f x) μ.support).trans
      (Finset.sum_le_sum fun x _ => by
        rw [abs_mul, abs_of_nonneg (μ.nonnegative x)]
        exact mul_le_mul_of_nonneg_left (hpt x) (μ.nonnegative x))
  have hs2 : (∑ x ∈ μ.support, μ.weight x * (Real.sqrt (g x) * Real.sqrt (h x))) =
      ∑ x ∈ μ.support, Real.sqrt (μ.weight x * g x) * Real.sqrt (μ.weight x * h x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Real.sqrt_mul (μ.nonnegative x), Real.sqrt_mul (μ.nonnegative x),
      show Real.sqrt (μ.weight x) * Real.sqrt (g x) * (Real.sqrt (μ.weight x) * Real.sqrt (h x)) =
        Real.sqrt (μ.weight x) * Real.sqrt (μ.weight x) * (Real.sqrt (g x) * Real.sqrt (h x)) by ring,
      Real.mul_self_sqrt (μ.nonnegative x)]
  rw [hs2] at hs1
  refine (hs1.trans (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)).trans_eq ?_
  rw [Finset.sum_congr rfl fun x _ => Real.sq_sqrt (mul_nonneg (μ.nonnegative x) (hg0 x)),
    Finset.sum_congr rfl fun x _ => Real.sq_sqrt (mul_nonneg (μ.nonnegative x) (hh0 x))]

theorem avgOver_sum_stateQForm_mul_le_one {X α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (μ : Distribution X) (A : X → Measurement α ι)
    (C : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability)
    (hψ : ‖ψ‖ = 1) (hC : ∀ x a, IsProj (C x a)) (hAC : ∀ x a, Commute ((A x).effect a) (C x a)) :
    avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a)) ≤ 1 := by
  refine (avgOver_mono μ _ (fun _ => 1) fun x => ?_).trans_eq (avgOver_const_of_isProbability μ hμ 1)
  refine (Finset.sum_le_sum fun a _ => ?_).trans_eq (sum_stateQForm_effect_eq_one (A x) ψ hψ)
  have h1 : stateQForm ψ ((A x).effect a * (1 - C x a)) =
      stateQForm ψ ((A x).effect a) - stateQForm ψ ((A x).effect a * C x a) := by
    simp [stateQForm, applyOperatorToState, mul_sub]
  have h2 : 0 ≤ stateQForm ψ ((A x).effect a * (1 - C x a)) := by
    rw [← stateQForm_applyOperatorToState_eq_of_isProj ψ (hC x a).one_sub
      ((Commute.one_right _).sub_right (hAC x a))]
    exact stateQForm_nonneg _ ((A x).pos a)
  linarith

theorem abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] (μ : Distribution X)
    (A : X → Measurement α ι) (B C : X → α → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hB : ∀ x a, IsProj (B x a)) (hAB : ∀ x a, Commute ((A x).effect a) (B x a)) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (B x a * C x a)))| ≤
      Real.sqrt (avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a))) *
        Real.sqrt (avgOver μ (fun x => ∑ a, stateQForm (applyOperatorToState (C x a) ψ) ((A x).effect a))) := by
  have hrw (x) (a) : stateQForm ψ ((A x).effect a * (B x a * C x a)) =
      (inner ℂ (applyOperatorToState (B x a) ψ)
        (applyOperatorToState ((A x).effect a) (applyOperatorToState (C x a) ψ))).re := by
    unfold stateQForm
    rw [← mul_assoc, (hAB x a).eq, mul_assoc, applyOperatorToState_mul, applyOperatorToState_mul]
    congr 1
    have hadj : (Matrix.toEuclideanLin (B x a)).adjoint = Matrix.toEuclideanLin (B x a) := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, (hB x a).isSelfAdjoint.isHermitian.eq]
    have h := LinearMap.adjoint_inner_right (Matrix.toEuclideanLin (B x a)) ψ
      (applyOperatorToState ((A x).effect a) (applyOperatorToState (C x a) ψ))
    rwa [hadj] at h
  rw [show (fun x => ∑ a, stateQForm ψ ((A x).effect a * (B x a * C x a))) = _ from
      funext fun x => Finset.sum_congr rfl fun a _ => hrw x a,
    show (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a)) = _ from
      funext fun x => Finset.sum_congr rfl fun a _ =>
        (stateQForm_applyOperatorToState_eq_of_isProj ψ (hB x a) (hAB x a)).symm]
  exact abs_avgOver_sum_re_inner_le_sqrt_mul_sqrt μ (fun x a => (A x).effect a)
    (fun x a => (A x).pos a) (fun x a => applyOperatorToState (B x a) ψ)
    (fun x a => applyOperatorToState (C x a) ψ)

theorem abs_overlap_gap_le_sqrt_one_sub_of_isProj' {X α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (μ : Distribution X) (A : X → Measurement α ι)
    (B C CB : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability)
    (hψ : ‖ψ‖ = 1) (hB : ∀ x a, IsProj (B x a)) (hC : ∀ x a, IsProj (C x a))
    (hAB : ∀ x a, Commute ((A x).effect a) (B x a))
    (hAC : ∀ x a, Commute ((A x).effect a) (C x a))
    (hCB : ∀ x a, CB x a = C x a * B x a) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * CB x a)) -
      avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a))| ≤
      Real.sqrt (1 - avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a))) := by
  have hpt (x) : (∑ a, stateQForm ψ ((A x).effect a * C x a)) -
      (∑ a, stateQForm ψ ((A x).effect a * (C x a * B x a))) =
      ∑ a, stateQForm ψ ((A x).effect a * (C x a * (1 - B x a))) := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun a _ => ?_
    simp [stateQForm, applyOperatorToState, mul_sub]
  rw [avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ => by rw [hCB],
    abs_sub_comm, ← avgOver_sub, avgOver_congr μ _ _ hpt]
  have h1B (x) (a) : IsProj (1 - B x a) := (hB x a).one_sub
  have hA1B (x) (a) : Commute ((A x).effect a) (1 - B x a) := (Commute.one_right _).sub_right (hAB x a)
  have hcs := abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt μ A C (fun x a => 1 - B x a) ψ hC hAC
  have hsec : avgOver μ (fun x => ∑ a, stateQForm (applyOperatorToState (1 - B x a) ψ) ((A x).effect a)) =
      1 - avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a)) := by
    have hx (x) : (∑ a, stateQForm (applyOperatorToState (1 - B x a) ψ) ((A x).effect a)) =
        1 - ∑ a, stateQForm ψ ((A x).effect a * B x a) := by
      rw [← sum_stateQForm_effect_eq_one (A x) ψ hψ, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [stateQForm_applyOperatorToState_eq_of_isProj ψ (h1B x a) (hA1B x a)]
      simp [stateQForm, applyOperatorToState, mul_sub]
    rw [avgOver_congr μ _ _ hx, avgOver_sub, avgOver_const_of_isProbability μ hμ]
  have h1 : Real.sqrt (avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a))) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt (avgOver_sum_stateQForm_mul_le_one μ A C ψ hμ hψ hC hAC)
  rw [hsec] at hcs
  exact hcs.trans ((mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)).trans_eq (one_mul _))

theorem abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj' {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] (μ : Distribution X)
    (A : X → Measurement α ι) (W R : X → α → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) (hR : ∀ x a, IsProj (R x a))
    (hAR : ∀ x a, Commute ((A x).effect a) (R x a))
    (hAW : ∀ x a, Commute ((A x).effect a) (W x a)) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (W x a * R x a)))| ≤
      Real.sqrt (avgOver μ (fun x => ∑ a, ‖applyOperatorToState (W x a)ᴴ ψ‖ ^ 2)) := by
  have hrw (x) (a) : stateQForm ψ ((A x).effect a * (W x a * R x a)) =
      stateQForm ψ ((A x).effect a * (R x a * (W x a)ᴴ)) := by
    have hAWH : Commute ((A x).effect a) (W x a)ᴴ := by
      have h := congrArg Matrix.conjTranspose (hAW x a).eq
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, measurement_effect_hermitian] at h
      exact h.symm
    rw [← stateQForm_conjTranspose ψ ((A x).effect a * (W x a * R x a)),
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, measurement_effect_hermitian,
      (hR x a).isSelfAdjoint.isHermitian.eq]
    exact congrArg (stateQForm ψ) ((hAR x a).mul_right hAWH).eq.symm
  rw [avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ => hrw x a]
  have hcs := abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt μ A R (fun x a => (W x a)ᴴ) ψ hR hAR
  have h1 : Real.sqrt (avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * R x a))) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt (avgOver_sum_stateQForm_mul_le_one μ A R ψ hμ hψ hR hAR)
  have h2 : avgOver μ (fun x => ∑ a, stateQForm (applyOperatorToState (W x a)ᴴ ψ) ((A x).effect a)) ≤
      avgOver μ (fun x => ∑ a, ‖applyOperatorToState (W x a)ᴴ ψ‖ ^ 2) :=
    avgOver_mono μ _ _ fun x => Finset.sum_le_sum fun a _ => by
      rw [← stateQForm_one]
      exact quadratic_form_mono (measurement_effect_le_one (A x) a) _
  exact hcs.trans ((mul_le_mul h1 (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _) zero_le_one).trans_eq (one_mul _))

/-! ## Unified X/Z completed-point and subline evaluation deficits -/

theorem sum_option_prod_eq_of_none {β γ : Type*} [Fintype β] [Fintype γ]
    (F : Option β × Option γ → ℝ) (h1 : ∀ o2, F (none, o2) = 0) (h2 : ∀ o1, F (o1, none) = 0) :
    (∑ o, F o) = ∑ bc : β × γ, F (some bc.1, some bc.2) := by
  rw [Fintype.sum_prod_type (f := F), Fintype.sum_option, Finset.sum_eq_zero fun o2 _ => h1 o2,
    zero_add, Finset.sum_congr rfl fun b _ => by rw [Fintype.sum_option, h2 (some b), zero_add]]
  exact (Fintype.sum_prod_type (f := fun bc : β × γ => F (some bc.1, some bc.2))).symm

theorem completedPair_effect_some {β γ d : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] [Fintype d] [DecidableEq d]
    (Q : Measurement (β × γ) d) (bc : β × γ) :
    (Q.postprocess fun ab => (some ab.1, some ab.2)).effect (some bc.1, some bc.2) = Q.effect bc := by
  rw [Measurement.postprocess_effect,
    show (Finset.univ.filter fun cd : β × γ => (some cd.1, some cd.2) = (some bc.1, some bc.2)) = {bc} by
      ext cd; simp [Prod.ext_iff, eq_comm]]; simp

theorem completedPair_effect_eq_zero {β γ d : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] [Fintype d] [DecidableEq d]
    (Q : Measurement (β × γ) d) (o : Option β × Option γ)
    (ho : ∀ bc : β × γ, (some bc.1, some bc.2) ≠ o) :
    (Q.postprocess fun ab => (some ab.1, some ab.2)).effect o = 0 := by
  rw [Measurement.postprocess_effect]
  exact Finset.sum_eq_zero fun bc hbc => absurd (Finset.mem_filter.mp hbc).2 (ho bc)

theorem completedPair_isProjective {β γ d : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] [Fintype d] [DecidableEq d]
    (Q : Measurement (β × γ) d) (hQ : Measurement.IsProjective Q) :
    Measurement.IsProjective (Q.postprocess fun ab => (some ab.1, some ab.2)) := fun o => by
  by_cases h : ∃ bc : β × γ, (some bc.1, some bc.2) = o
  · obtain ⟨bc, rfl⟩ := h; rw [completedPair_effect_some]; exact hQ bc
  · push Not at h; rw [completedPair_effect_eq_zero Q o h]; exact IsStarProjection.zero _

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

theorem place_isProj (S : ProjectiveSetting P ε) (p : Placement)
    {E : Op (S.ExpandedLocalSpace p.side)} (hE : IsProj E) : IsProj (S.place p E) :=
  isStarProjection_iff'.2 ⟨by change S.place p E * S.place p E = S.place p E; rw [← place_mul, hE.isIdempotentElem.eq],
    by rw [Matrix.star_eq_conjTranspose, ← place_conjTranspose, hE.isSelfAdjoint.isHermitian.eq]⟩

theorem pointMeasExpOption_isProj (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P) (o : Option (PauliScalar P)) :
    IsProj ((S.pointMeasExpOption side W u).effect o) := by
  cases o with
  | none => rw [S.pointMeasExpOption_effect_none]; exact IsStarProjection.zero _
  | some a => rw [S.pointMeasExpOption_effect_some]; exact S.pointMeasExp_isProjective side W u a

theorem sum_norm_place_completedPair_sub_sq (S : ProjectiveSetting P ε) (p : Placement)
    (Q : Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace p.side))
    (Gc : Option (PauliScalar P) × Option (PauliScalar P) → Op (S.ExpandedLocalSpace p.side))
    (G : PauliScalar P × PauliScalar P → Op (S.ExpandedLocalSpace p.side))
    (hsome : ∀ ab, Gc (some ab.1, some ab.2) = G ab)
    (hnone1 : ∀ o2, Gc (none, o2) = 0) (hnone2 : ∀ o1, Gc (o1, none) = 0) :
    (∑ o, ‖applyOperatorToState (S.place p ((Q.postprocess fun ab => (some ab.1, some ab.2)).effect o) -
        S.place p (Gc o)) S.psiHat‖ ^ 2) =
      ∑ ab, ‖applyOperatorToState (S.place p (Q.effect ab) - S.place p (G ab)) S.psiHat‖ ^ 2 := by
  refine (sum_option_prod_eq_of_none _ (fun o2 => ?_) fun o1 => ?_).trans
    (Finset.sum_congr rfl fun ab _ => by rw [completedPair_effect_some, hsome])
  · rw [completedPair_effect_eq_zero Q (none, o2) (fun ab => by simp), hnone1, place_zero, sub_self]
    simp [applyOperatorToState]
  · rw [completedPair_effect_eq_zero Q (o1, none) (fun ab => by simp), hnone2, place_zero, sub_self]
    simp [applyOperatorToState]

theorem completedPair_norm_sq_sum_ZX (S : ProjectiveSetting P ε) {δ : ℝ}
    (points : CombinedPointsWitness S δ) (p : Placement) (x z : Fin P.m → PauliScalar P) :
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P), ‖applyOperatorToState
        (S.place p (((points.Q p.side x z).postprocess fun ab => (some ab.1, some ab.2)).effect o) -
          S.place p ((S.pointMeasExpOption p.side .Z z).effect o.2 *
            (S.pointMeasExpOption p.side .X x).effect o.1)) S.psiHat‖ ^ 2) =
      ∑ ab : PauliScalar P × PauliScalar P, ‖applyOperatorToState
        (S.place p ((points.Q p.side x z).effect ab) -
          S.place p ((S.pointMeasExp p.side .Z z).effect ab.2 *
            (S.pointMeasExp p.side .X x).effect ab.1)) S.psiHat‖ ^ 2 :=
  S.sum_norm_place_completedPair_sub_sq p (points.Q p.side x z) _ _
    (fun _ => by rw [S.pointMeasExpOption_effect_some, S.pointMeasExpOption_effect_some])
    (fun _ => by rw [S.pointMeasExpOption_effect_none, mul_zero])
    (fun _ => by rw [S.pointMeasExpOption_effect_none, zero_mul])

theorem completedPair_norm_sq_sum_XZ (S : ProjectiveSetting P ε) {δ : ℝ}
    (points : CombinedPointsWitness S δ) (p : Placement) (x z : Fin P.m → PauliScalar P) :
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P), ‖applyOperatorToState
        (S.place p (((points.Q p.side x z).postprocess fun ab => (some ab.1, some ab.2)).effect o) -
          S.place p ((S.pointMeasExpOption p.side .X x).effect o.1 *
            (S.pointMeasExpOption p.side .Z z).effect o.2)) S.psiHat‖ ^ 2) =
      ∑ ab : PauliScalar P × PauliScalar P, ‖applyOperatorToState
        (S.place p ((points.Q p.side x z).effect ab) -
          S.place p ((S.pointMeasExp p.side .X x).effect ab.1 *
            (S.pointMeasExp p.side .Z z).effect ab.2)) S.psiHat‖ ^ 2 :=
  S.sum_norm_place_completedPair_sub_sq p (points.Q p.side x z) _ _
    (fun _ => by rw [S.pointMeasExpOption_effect_some, S.pointMeasExpOption_effect_some])
    (fun _ => by rw [S.pointMeasExpOption_effect_none, zero_mul])
    (fun _ => by rw [S.pointMeasExpOption_effect_none, mul_zero])

end ProjectiveSetting

theorem one_sub_overlap_le_of_consistencyDefect {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A Q : X → Measurement α ι) (R W : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (hQ : ∀ x, Measurement.IsProjective (Q x)) (hR : ∀ x a, IsProj (R x a))
    (hAQ : ∀ x a, Commute ((A x).effect a) ((Q x).effect a))
    (hAR : ∀ x a, Commute ((A x).effect a) (R x a))
    (hAW : ∀ x a, Commute ((A x).effect a) (W x a))
    (hWR : ∀ x a, W x a * R x a = W x a)
    (hnonneg : ∀ x a, 0 ≤ stateQForm ψ ((A x).effect a * (Q x).effect a))
    (η ζ : ℝ)
    (hcons : consistencyDefect μ (fun x a => (A x).effect a) (fun x a => (Q x).effect a) ψ ≤ η)
    (hdist : opFamilyDistSq μ (fun x a => (Q x).effect a) (fun x a => (W x a)ᴴ) ψ ≤ ζ) :
    1 - avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * R x a)) ≤
      2 * Real.sqrt η + 2 * Real.sqrt ζ := by
  let ovQ := avgOver μ fun x => ∑ a, stateQForm ψ ((A x).effect a * (Q x).effect a)
  have h1 : 1 - ovQ ≤ η := (consistencyDefect_eq_one_sub_overlap μ A Q ψ hμ hψ) ▸ hcons
  have hov0 : 0 ≤ ovQ := avgOver_nonneg μ _ fun x => Finset.sum_nonneg fun a _ => hnonneg x a
  have hov1 : ovQ ≤ 1 := avgOver_sum_stateQForm_mul_le_one μ A (fun x a => (Q x).effect a) ψ hμ hψ
    (fun x a => hQ x a) hAQ
  have h1' : 1 - ovQ ≤ Real.sqrt η := by
    have h0 : 0 ≤ 1 - ovQ := by linarith
    exact (Real.sqrt_sq h0).symm.trans_le (Real.sqrt_le_sqrt (by nlinarith))
  have h2 : |ovQ - avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * W x a))| ≤ Real.sqrt ζ := by
    have hWc (x) (a) : stateQForm ψ ((A x).effect a * W x a) = stateQForm ψ ((A x).effect a * (W x a)ᴴ) := by
      rw [← stateQForm_conjTranspose ψ ((A x).effect a * W x a), Matrix.conjTranspose_mul,
        measurement_effect_hermitian]
      have h := congrArg Matrix.conjTranspose (hAW x a).eq
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, measurement_effect_hermitian] at h
      exact congrArg (stateQForm ψ) h
    rw [avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ => hWc x a]
    exact abs_overlap_gap_le_sqrt_of_opFamilyDistSq μ A (fun x a => (Q x).effect a)
      (fun x a => (W x a)ᴴ) ψ hμ hψ ζ hdist
  have h4 : |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) -
      avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * W x a))| ≤ Real.sqrt ζ := by
    have hpt (x) : (∑ a, stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) -
        (∑ a, stateQForm ψ ((A x).effect a * W x a)) =
        ∑ a, stateQForm ψ ((A x).effect a * (((Q x).effect a - W x a) * R x a)) := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun a _ => ?_
      rw [sub_mul, hWR]; simp [stateQForm, applyOperatorToState, mul_sub]
    rw [← avgOver_sub, avgOver_congr μ _ _ hpt]
    refine (abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj' μ A
      (fun x a => (Q x).effect a - W x a) R ψ hμ hψ hR hAR
      fun x a => (hAQ x a).sub_right (hAW x a)).trans (Real.sqrt_le_sqrt ?_)
    have hd' : avgOver μ (fun x => ∑ a, ‖applyOperatorToState ((Q x).effect a - (W x a)ᴴ) ψ‖ ^ 2) ≤ ζ := hdist
    refine le_of_eq_of_le (avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ => ?_) hd'
    rw [Matrix.conjTranspose_sub, measurement_effect_hermitian]
  have h5 : |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) -
      avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * R x a))| ≤ Real.sqrt η := by
    have hpt (x) : (∑ a, stateQForm ψ ((A x).effect a * R x a)) -
        (∑ a, stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) =
        ∑ a, stateQForm ψ ((A x).effect a * ((1 - (Q x).effect a) * R x a)) := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun a _ => ?_
      simp [stateQForm, applyOperatorToState, sub_mul, mul_sub]
    rw [abs_sub_comm, ← avgOver_sub, avgOver_congr μ _ _ hpt]
    have hcs := abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt μ A
      (fun x a => 1 - (Q x).effect a) R ψ (fun x a => (hQ x a).one_sub)
      fun x a => (Commute.one_right _).sub_right (hAQ x a)
    have hf : avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (1 - (Q x).effect a))) = 1 - ovQ := by
      have hx (x) : (∑ a, stateQForm ψ ((A x).effect a * (1 - (Q x).effect a))) =
          1 - ∑ a, stateQForm ψ ((A x).effect a * (Q x).effect a) := by
        rw [← sum_stateQForm_effect_eq_one (A x) ψ hψ, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp [stateQForm, applyOperatorToState, mul_sub]
      rw [avgOver_congr μ _ _ hx, avgOver_sub, avgOver_const_of_isProbability μ hμ]
    have hs : avgOver μ (fun x => ∑ a, stateQForm (applyOperatorToState (R x a) ψ) ((A x).effect a)) ≤ 1 := by
      rw [avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ =>
        stateQForm_applyOperatorToState_eq_of_isProj ψ (hR x a) (hAR x a)]
      exact avgOver_sum_stateQForm_mul_le_one μ A R ψ hμ hψ hR hAR
    rw [hf] at hcs
    exact (hcs.trans ((mul_le_mul_of_nonneg_left (by simpa using Real.sqrt_le_sqrt hs)
      (Real.sqrt_nonneg _)).trans_eq (mul_one _))).trans (Real.sqrt_le_sqrt h1)
  linarith [(abs_le.mp h2).1, (abs_le.mp h4).1, (abs_le.mp h5).1,
    (abs_le.mp h2).2, (abs_le.mp h4).2, (abs_le.mp h5).2]

abbrev LinePointPairSample (P : AdmissibleParams) :=
  (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
    (LineDesc P.toLdParams × (Fin P.m → PauliScalar P))

theorem restrictedLinePointDist_isProbability (P : AdmissibleParams) (kind : LineKind) (i : Fin P.m) :
    (restrictedLinePointDist P kind i).IsProbability := by
  cases kind
  · exact restrictedALineDist_isProbability P.toLdParams i
  · exact restrictedDLineDist_isProbability P.toLdParams i

theorem opFamilyDistSq_prod_restricted_points {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : AdmissibleParams) (kindX kindZ : LineKind) (i j : Fin P.m)
    (F G : (Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P) → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j))
      (fun s a => F (s.1.2, s.2.2) a) (fun s a => G (s.1.2, s.2.2) a) ψ =
      opFamilyDistSq (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P))) F G ψ := by
  have hsnd (k) (idx) : (restrictedLinePointDist P k idx).map Prod.snd =
      uniformDistribution (Fin P.m → PauliScalar P) := by
    rw [restrictedLinePointDist_eq_map_prod, Distribution.map_map]
    exact Distribution.prod_map_fst _ _ (Distribution.prod_isProbability _ _
      (subLineSeedDist_isProbability P idx) (uniformDistribution_isProbability _))
  have hmp : (Distribution.prod (restrictedLinePointDist P kindX i)
      (restrictedLinePointDist P kindZ j)).map (fun s => (s.1.2, s.2.2)) =
      uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) := by
    have h : Distribution.prod ((restrictedLinePointDist P kindX i).map Prod.snd)
        ((restrictedLinePointDist P kindZ j).map Prod.snd) =
        uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) := by
      rw [hsnd, hsnd, uniformDistribution_prod]
    rw [← h, Distribution.prod_map_left, Distribution.prod_map_right, Distribution.map_map]
  unfold opFamilyDistSq; rw [← hmp, Distribution.avgOver_map]

theorem CombinedLinesWitness.one_sub_basis_overlap_restricted_le {P : AdmissibleParams}
    {ε δQ δP : ℝ} {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (lines : CombinedLinesWitness S points δP) (W : PauliKind)
    (first second : Placement) (hopposite : first.IsOpposite second)
    (kindX kindZ : LineKind) (i j : Fin P.m) :
    (1 : ℝ) - avgOver (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j))
      (fun s => ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat (S.place first
          (((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
            (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)).effect o) *
          S.place second (match W with
            | .X => (S.pointMeasExpOption second.side .X s.1.2).effect o.1
            | .Z => (S.pointMeasExpOption second.side .Z s.2.2).effect o.2))) ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  let ν := Distribution.prod (restrictedLinePointDist P kindX i) (restrictedLinePointDist P kindZ j)
  have hν := Distribution.prod_isProbability _ _
    (restrictedLinePointDist_isProbability P kindX i) (restrictedLinePointDist_isProbability P kindZ j)
  let A := fun s : LinePointPairSample P => S.placedMeasurement first
    ((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
      (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2))
  let Q := fun s : LinePointPairSample P => S.placedMeasurement second
    ((points.Q second.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2))
  have hcons : consistencyDefect ν (fun s o => (A s).effect o) (fun s o => (Q s).effect o) S.psiHat ≤
      4 * (P.m : ℝ) ^ 2 * δP :=
    (avgOver_prod_restrictedLinePointDist_le _
      (fun s => consistencyDefect_integrand_nonneg S first second hopposite _ _) kindX kindZ i j).trans
      (mul_le_mul_of_nonneg_left (lines.consistent first second hopposite) (by positivity))
  have hnn (s : LinePointPairSample P) (o) := stateQForm_nonneg S.psiHat
    (S.place_mul_place_nonneg first second hopposite
      (((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
        (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)).pos o)
      (((points.Q second.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2)).pos o))
  have hQp (s : LinePointPairSample P) := S.placedMeasurement_isProjective second _
    (completedPair_isProjective _ (points.projective second.side s.1.2 s.2.2))
  cases W
  · refine one_sub_overlap_le_of_consistencyDefect ν A Q
      (fun s o => S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1))
      (fun s o => S.place second ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
        (S.pointMeasExpOption second.side .X s.1.2).effect o.1))
      S.psiHat hν S.psiHat_norm hQp (fun s o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
      (fun _ _ => S.place_comm first second hopposite _ _)
      (fun _ _ => S.place_comm first second hopposite _ _)
      (fun _ _ => S.place_comm first second hopposite _ _)
      (fun s o => (ProjectiveSetting.place_mul S second _ _).symm.trans (congrArg (S.place second) <| by
        rw [mul_assoc, (S.pointMeasExpOption_isProj second.side .X s.1.2 o.1).isIdempotentElem.eq]))
      hnn _ _ hcons ?_
    have hd : opFamilyDistSq ν (fun s o => (Q s).effect o)
        (fun s o => (S.place second ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1))ᴴ) S.psiHat =
        opFamilyDistSq (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
          (fun xz ab => S.place second ((points.Q second.side xz.1 xz.2).effect ab))
          (fun xz ab => S.place second ((S.pointMeasExp second.side .X xz.1).effect ab.1 *
            (S.pointMeasExp second.side .Z xz.2).effect ab.2)) S.psiHat := by
      refine (avgOver_congr _ _ _ fun s => Finset.sum_congr rfl fun o _ => ?_).trans
        ((opFamilyDistSq_prod_restricted_points P kindX kindZ i j _ _ _).trans
          (avgOver_congr _ _ _ fun xz => S.completedPair_norm_sq_sum_XZ points second xz.1 xz.2))
      dsimp only [Q, ProjectiveSetting.placedMeasurement_effect]
      rw [← ProjectiveSetting.place_conjTranspose S second, Matrix.conjTranspose_mul,
        (S.pointMeasExpOption_isProj second.side .X s.1.2 o.1).isSelfAdjoint.isHermitian.eq,
        (S.pointMeasExpOption_isProj second.side .Z s.2.2 o.2).isSelfAdjoint.isHermitian.eq]
    exact hd.trans_le (points.orderedXZ_dist_le second)
  · refine one_sub_overlap_le_of_consistencyDefect ν A Q
      (fun s o => S.place second ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2))
      (fun s o => S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
        (S.pointMeasExpOption second.side .Z s.2.2).effect o.2))
      S.psiHat hν S.psiHat_norm hQp (fun s o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
      (fun _ _ => S.place_comm first second hopposite _ _)
      (fun _ _ => S.place_comm first second hopposite _ _)
      (fun _ _ => S.place_comm first second hopposite _ _)
      (fun s o => (ProjectiveSetting.place_mul S second _ _).symm.trans (congrArg (S.place second) <| by
        rw [mul_assoc, (S.pointMeasExpOption_isProj second.side .Z s.2.2 o.2).isIdempotentElem.eq]))
      hnn _ _ hcons ?_
    have hd : opFamilyDistSq ν (fun s o => (Q s).effect o)
        (fun s o => (S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
          (S.pointMeasExpOption second.side .Z s.2.2).effect o.2))ᴴ) S.psiHat =
        opFamilyDistSq (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
          (fun xz ab => S.place second ((points.Q second.side xz.1 xz.2).effect ab))
          (fun xz ab => S.place second ((S.pointMeasExp second.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp second.side .X xz.1).effect ab.1)) S.psiHat := by
      refine (avgOver_congr _ _ _ fun s => Finset.sum_congr rfl fun o _ => ?_).trans
        ((opFamilyDistSq_prod_restricted_points P kindX kindZ i j _ _ _).trans
          (avgOver_congr _ _ _ fun xz => S.completedPair_norm_sq_sum_ZX points second xz.1 xz.2))
      dsimp only [Q, ProjectiveSetting.placedMeasurement_effect]
      rw [← ProjectiveSetting.place_conjTranspose S second, Matrix.conjTranspose_mul,
        (S.pointMeasExpOption_isProj second.side .Z s.2.2 o.2).isSelfAdjoint.isHermitian.eq,
        (S.pointMeasExpOption_isProj second.side .X s.1.2 o.1).isSelfAdjoint.isHermitian.eq]
    exact hd.trans_le (points.orderedZX_dist_le second)

theorem regroup_line_answer_sum_at {P : AdmissibleParams} {ε δQ δP : ℝ}
    {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (lines : CombinedLinesWitness S points δP) (first second : Placement)
    (lineX lineZ : LineDesc P.toLdParams) (x z : Fin P.m → PauliScalar P)
    (G : Option (PauliScalar P) → Option (PauliScalar P) → Op (S.ExpandedLocalSpace second.side)) :
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P), stateQForm S.psiHat
        ((S.placedMeasurement first ((lines.T first.side lineX lineZ).postprocess
          fun fs => (evalOpt lineX x fs.1, evalOpt lineZ z fs.2))).effect o * S.place second (G o.1 o.2))) =
      ∑ fX, ∑ fZ, stateQForm S.psiHat
        (S.place first ((lines.T first.side lineX lineZ).effect (fX, fZ)) *
          S.place second (G (evalOpt lineX x fX) (evalOpt lineZ z fZ))) := by
  have hs (o : Option (PauliScalar P) × Option (PauliScalar P)) :
      stateQForm S.psiHat ((S.placedMeasurement first ((lines.T first.side lineX lineZ).postprocess
        fun fs => (evalOpt lineX x fs.1, evalOpt lineZ z fs.2))).effect o * S.place second (G o.1 o.2)) =
      ∑ fs ∈ Finset.univ.filter (fun fs => (evalOpt lineX x fs.1, evalOpt lineZ z fs.2) = o),
        stateQForm S.psiHat (S.place first ((lines.T first.side lineX lineZ).effect fs) *
          S.place second (G (evalOpt lineX x fs.1) (evalOpt lineZ z fs.2))) := by
    rw [ProjectiveSetting.placedMeasurement_effect, Measurement.postprocess_effect, S.place_finsetSum,
      Finset.sum_mul, stateQForm_finset_sum]
    exact Finset.sum_congr rfl fun fs hfs => by rw [← (Finset.mem_filter.mp hfs).2]
  simp_rw [hs]
  exact (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).trans
    (Fintype.sum_prod_type (f := fun fs => stateQForm S.psiHat
      (S.place first ((lines.T first.side lineX lineZ).effect fs) *
        S.place second (G (evalOpt lineX x fs.1) (evalOpt lineZ z fs.2)))))

def basisPointOverlapAt {P : AdmissibleParams} {ε δQ δP : ℝ} {S : ProjectiveSetting P ε}
    {points : CombinedPointsWitness S δQ} (lines : CombinedLinesWitness S points δP)
    (W : PauliKind) (first second : Placement)
    (w : (LineDesc P.toLdParams × LineDesc P.toLdParams) × (Fin P.m → PauliScalar P)) : ℝ :=
  ∑ fX, ∑ fZ, stateQForm S.psiHat
    (S.place first ((lines.T first.side w.1.1 w.1.2).effect (fX, fZ)) *
      S.place second (match W with
        | .X => (S.pointMeasExpOption second.side .X w.2).effect (evalOpt w.1.1 w.2 fX)
        | .Z => (S.pointMeasExpOption second.side .Z w.2).effect (evalOpt w.1.2 w.2 fZ)))

theorem SubLineWitness.exists_avgOver_basis_eq_mixture (P : AdmissibleParams)
    (sublines : SubLineWitness P) (W : PauliKind)
    (F : (LineDesc P.toLdParams × LineDesc P.toLdParams) × (Fin P.m → PauliScalar P) → ℝ) :
    ∃ components : Distribution (SubLineComponent P), components.IsProbability ∧
      avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          (fun t => F (sample.2, (match W with | .X => projX | .Z => projZ)
            (directPointToPauli P (sample.1.base + t • sample.1.direction))))) =
      avgOver components (fun c =>
        avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
            (restrictedLinePointDist P c.1 c.2.2))
          (fun w => F ((w.1.1, w.2.1), match W with | .X => w.1.2 | .Z => w.2.2))) := by
  obtain ⟨components, hcomp, hX, hZ⟩ := sublines.source_mixture
  refine ⟨components, hcomp, ?_⟩
  cases W
  · have h1 : avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          (fun t => F (sample.2, projX (directPointToPauli P (sample.1.base + t • sample.1.direction))))) =
        avgOver ((subLinePointDist P sublines.D).map subLineXProjection) F := by
      rw [Distribution.avgOver_map, subLinePointDist, Distribution.avgOver_map,
        SandwichProduct.avgOver_distribution_prod]; rfl
    rw [h1, hX, avgOver_bind]; refine avgOver_congr _ _ _ fun c => ?_
    rw [subLineXComponentDist, Distribution.avgOver_map, Distribution.prod_map_right,
      Distribution.avgOver_map]
  · have h1 : avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          (fun t => F (sample.2, projZ (directPointToPauli P (sample.1.base + t • sample.1.direction))))) =
        avgOver ((subLinePointDist P sublines.D).map subLineZProjection) F := by
      rw [Distribution.avgOver_map, subLinePointDist, Distribution.avgOver_map,
        SandwichProduct.avgOver_distribution_prod]; rfl
    rw [h1, hZ, avgOver_bind]; refine avgOver_congr _ _ _ fun c => ?_
    rw [subLineZComponentDist, Distribution.avgOver_map, Distribution.prod_map_left,
      Distribution.avgOver_map]

theorem SubLineWitness.one_sub_avgOver_basisPointOverlap_le {P : AdmissibleParams} {ε δQ δP : ℝ}
    {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (sublines : SubLineWitness P) (lines : CombinedLinesWitness S points δP)
    (W : PauliKind) (first second : Placement) (hopposite : first.IsOpposite second) :
    1 - avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
        (fun t => basisPointOverlapAt lines W first second
          (sample.2, (match W with | .X => projX | .Z => projZ)
            (directPointToPauli P (sample.1.base + t • sample.1.direction))))) ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  obtain ⟨comp, hcomp, hmix⟩ := sublines.exists_avgOver_basis_eq_mixture P W
    (basisPointOverlapAt lines W first second)
  rw [hmix]
  cases W
  · have hsp : avgOver comp (fun c => (1 : ℝ) -
        avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
          (restrictedLinePointDist P c.1 c.2.2))
          (fun w => basisPointOverlapAt lines .X first second ((w.1.1, w.2.1), w.1.2))) =
        (1 : ℝ) - avgOver comp (fun c =>
          avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
            (restrictedLinePointDist P c.1 c.2.2))
            (fun w => basisPointOverlapAt lines .X first second ((w.1.1, w.2.1), w.1.2))) := by
      rw [avgOver_sub, avgOver_const_of_isProbability comp hcomp]
    rw [← hsp]
    refine (avgOver_mono _ _ _ fun c => ?_).trans_eq (avgOver_const_of_isProbability comp hcomp _)
    have hrw (w : LinePointPairSample P) :
        basisPointOverlapAt lines .X first second ((w.1.1, w.2.1), w.1.2) =
        ∑ o : Option (PauliScalar P) × Option (PauliScalar P), stateQForm S.psiHat
          (S.place first (((lines.T first.side w.1.1 w.2.1).postprocess fun fs =>
            (evalOpt w.1.1 w.1.2 fs.1, evalOpt w.2.1 w.2.2 fs.2)).effect o) *
            S.place second ((S.pointMeasExpOption second.side .X w.1.2).effect o.1)) :=
      (regroup_line_answer_sum_at lines first second w.1.1 w.2.1 w.1.2 w.2.2
        fun o1 _ => (S.pointMeasExpOption second.side .X w.1.2).effect o1).symm
    rw [avgOver_congr _ _ _ hrw]
    exact lines.one_sub_basis_overlap_restricted_le .X first second hopposite c.1 c.1 c.2.1 c.2.2
  · have hsp : avgOver comp (fun c => (1 : ℝ) -
        avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
          (restrictedLinePointDist P c.1 c.2.2))
          (fun w => basisPointOverlapAt lines .Z first second ((w.1.1, w.2.1), w.2.2))) =
        (1 : ℝ) - avgOver comp (fun c =>
          avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
            (restrictedLinePointDist P c.1 c.2.2))
            (fun w => basisPointOverlapAt lines .Z first second ((w.1.1, w.2.1), w.2.2))) := by
      rw [avgOver_sub, avgOver_const_of_isProbability comp hcomp]
    rw [← hsp]
    refine (avgOver_mono _ _ _ fun c => ?_).trans_eq (avgOver_const_of_isProbability comp hcomp _)
    have hrw (w : LinePointPairSample P) :
        basisPointOverlapAt lines .Z first second ((w.1.1, w.2.1), w.2.2) =
        ∑ o : Option (PauliScalar P) × Option (PauliScalar P), stateQForm S.psiHat
          (S.place first (((lines.T first.side w.1.1 w.2.1).postprocess fun fs =>
            (evalOpt w.1.1 w.1.2 fs.1, evalOpt w.2.1 w.2.2 fs.2)).effect o) *
            S.place second ((S.pointMeasExpOption second.side .Z w.2.2).effect o.2)) :=
      (regroup_line_answer_sum_at lines first second w.1.1 w.2.1 w.1.2 w.2.2
        fun _ o2 => (S.pointMeasExpOption second.side .Z w.2.2).effect o2).symm
    rw [avgOver_congr _ _ _ hrw]
    exact lines.one_sub_basis_overlap_restricted_le .Z first second hopposite c.1 c.1 c.2.1 c.2.2

theorem SubLineWitness.avgOver_zPointOverlap_le_one {P : AdmissibleParams} {ε δQ δP : ℝ}
    {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (sublines : SubLineWitness P) (lines : CombinedLinesWitness S points δP)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
        (fun t => basisPointOverlapAt lines .Z first second
          (sample.2, projZ (directPointToPauli P (sample.1.base + t • sample.1.direction))))) ≤ 1 := by
  obtain ⟨comp, hcomp, hmix⟩ := sublines.exists_avgOver_basis_eq_mixture P .Z
    (basisPointOverlapAt lines .Z first second)
  rw [hmix]
  refine (avgOver_mono _ _ (fun _ => 1) fun c => ?_).trans_eq (avgOver_const_of_isProbability comp hcomp 1)
  have hrw (w : LinePointPairSample P) :
      basisPointOverlapAt lines .Z first second ((w.1.1, w.2.1), w.2.2) =
      ∑ o : Option (PauliScalar P) × Option (PauliScalar P), stateQForm S.psiHat
        (S.place first (((lines.T first.side w.1.1 w.2.1).postprocess fun fs =>
          (evalOpt w.1.1 w.1.2 fs.1, evalOpt w.2.1 w.2.2 fs.2)).effect o) *
          S.place second ((S.pointMeasExpOption second.side .Z w.2.2).effect o.2)) :=
    (regroup_line_answer_sum_at lines first second w.1.1 w.2.1 w.1.2 w.2.2
      fun _ o2 => (S.pointMeasExpOption second.side .Z w.2.2).effect o2).symm
  rw [avgOver_congr _ _ _ hrw]
  have h := avgOver_sum_stateQForm_mul_le_one
    (Distribution.prod (restrictedLinePointDist P c.1 c.2.1) (restrictedLinePointDist P c.1 c.2.2))
    (fun w : LinePointPairSample P => S.placedMeasurement first
      ((lines.T first.side w.1.1 w.2.1).postprocess fun fs =>
        (evalOpt w.1.1 w.1.2 fs.1, evalOpt w.2.1 w.2.2 fs.2)))
    (fun w o => S.place second ((S.pointMeasExpOption second.side .Z w.2.2).effect o.2))
    S.psiHat (Distribution.prod_isProbability _ _
      (restrictedLinePointDist_isProbability P c.1 c.2.1)
      (restrictedLinePointDist_isProbability P c.1 c.2.2)) S.psiHat_norm
    (fun _ _ => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
    (fun _ _ => S.place_comm first second hopposite _ _)
  simpa only [ProjectiveSetting.placedMeasurement_effect] using h

/-! ## Conditional extended-line measurements, overlaps, and estimates -/

theorem directLinePointDist_line_weight_pos (params : DirectLdParams) (line : DirectLineDesc params) :
    0 < ((directLinePointDist params).map Prod.fst).weight line := by
  have hm_pos {S T : Type} [DecidableEq T] (law : Distribution S) (f : S → T) (s : S)
      (hp : 0 < law.weight s) : 0 < (law.map f).weight (f s) :=
    hp.trans_le (Finset.single_le_sum (fun x _ => law.nonnegative x)
      (Finset.mem_filter.mpr ⟨by by_contra hn; simp [law.outsideSupport s hn] at hp, rfl⟩))
  have hu (s : DirectLdSpace params) : 0 < (uniformDistribution (DirectLdSpace params)).weight s := by
    rw [uniformDistribution_weight_apply]; positivity
  refine hm_pos _ Prod.fst (line, line.base) ?_
  cases line with
  | axis base index baseFixed =>
    let s : DirectLdSpace params := ⟨base, index, 0⟩
    have ha := hm_pos (uniformDistribution (DirectLdSpace params))
      (fun src => (directALineDescOf params src, src.point)) s (hu s)
    have hd : directALineDescOf params s = .axis base index baseFixed := by
      simp [directALineDescOf, s, baseFixed]
    change 0 < (directALinePointDist params).weight _ at ha; rw [hd] at ha
    have ho := (directDLinePointDist params).nonnegative (DirectLineDesc.axis base index baseFixed, base)
    change 0 < (1 / 2 : ℝ) * (directALinePointDist params).weight _ +
      (1 - 1 / 2) * (directDLinePointDist params).weight _
    dsimp only [DirectLineDesc.base]; linarith
  | diagonal base index direction baseFixed prefixZero =>
    let s : DirectLdSpace params := ⟨base, index, direction⟩
    have hp : directPrefixProjection index direction = direction := by
      funext c; simp only [directPrefixProjection]; split_ifs with hb; exact (prefixZero c hb).symm; rfl
    have hd := hm_pos (uniformDistribution (DirectLdSpace params))
      (fun src => (directDLineDescOf params src, src.point)) s (hu s)
    have hdec : directDLineDescOf params s = .diagonal base index direction baseFixed prefixZero := by
      simp [directDLineDescOf, s, hp, baseFixed]
    change 0 < (directDLinePointDist params).weight _ at hd; rw [hdec] at hd
    have ho := (directALinePointDist params).nonnegative
      (DirectLineDesc.diagonal base index direction baseFixed prefixZero, base)
    change 0 < (1 / 2 : ℝ) * (directALinePointDist params).weight _ +
      (1 - 1 / 2) * (directDLinePointDist params).weight _
    dsimp only [DirectLineDesc.base]; linarith

abbrev SubLineWitness.Fiber {params : AdmissibleParams} (sublines : SubLineWitness params)
    (line : DirectLineDesc params.extendedDirectLd) :=
  ↥(sublines.D.support.filter fun sample => sample.1 = line)

theorem SubLineWitness.fiber_mass_pos {params : AdmissibleParams}
    (sublines : SubLineWitness params) (line : DirectLineDesc params.extendedDirectLd) :
    0 < (sublines.D.map Prod.fst).weight line :=
  sublines.extended_marginal ▸ directLinePointDist_line_weight_pos _ _

def SubLineWitness.conditionalLaw {params : AdmissibleParams}
    (sublines : SubLineWitness params) (line : DirectLineDesc params.extendedDirectLd) :
    Distribution (sublines.Fiber line) where
  support := Finset.univ
  weight s := sublines.D.weight s.val / (sublines.D.map Prod.fst).weight line
  nonnegative s := div_nonneg (sublines.D.nonnegative s.val) (sublines.fiber_mass_pos line).le
  outsideSupport s h := (h (Finset.mem_univ s)).elim

theorem SubLineWitness.conditionalLaw_isProbability {params : AdmissibleParams}
    (sublines : SubLineWitness params) (line : DirectLineDesc params.extendedDirectLd) :
    (sublines.conditionalLaw line).IsProbability := by
  change (∑ s : sublines.Fiber line, sublines.D.weight s.val / (sublines.D.map Prod.fst).weight line) = 1
  rw [← Finset.sum_div, Finset.sum_coe_sort]
  exact div_self (sublines.fiber_mass_pos line).ne'

def SubLineWitness.affineData {params : AdmissibleParams}
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hsample : sample ∈ sublines.D.support) : Fin 8 → PauliScalar params :=
  Classical.choose (show ∃ d : Fin 8 → PauliScalar params,
    IsCombineLineCompatible (directPointToPauli params sample.1.base)
      (directPointToPauli params sample.1.direction)
      sample.2.1.base sample.2.1.direction sample.2.2.base sample.2.2.direction
      (d 0) (d 1) (d 2) (d 3) (d 4) (d 5) (d 6) (d 7) from by
    obtain ⟨a, b, c, d, e, f, g, h, hc⟩ := sublines.compatibility sample hsample
    exact ⟨![a, b, c, d, e, f, g, h], hc⟩)

theorem SubLineWitness.affineData_compatible {params : AdmissibleParams}
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hsample : sample ∈ sublines.D.support) :
    let d := sublines.affineData sample hsample
    IsCombineLineCompatible (directPointToPauli params sample.1.base)
      (directPointToPauli params sample.1.direction)
      sample.2.1.base sample.2.1.direction sample.2.2.base sample.2.2.direction
      (d 0) (d 1) (d 2) (d 3) (d 4) (d 5) (d 6) (d 7) :=
  Classical.choose_spec (show ∃ d : Fin 8 → PauliScalar params,
    IsCombineLineCompatible (directPointToPauli params sample.1.base)
      (directPointToPauli params sample.1.direction)
      sample.2.1.base sample.2.1.direction sample.2.2.base sample.2.2.direction
      (d 0) (d 1) (d 2) (d 3) (d 4) (d 5) (d 6) (d 7) from by
    obtain ⟨a, b, c, d, e, f, g, h, hc⟩ := sublines.compatibility sample hsample
    exact ⟨![a, b, c, d, e, f, g, h], hc⟩)

def SubLineWitness.combinedPolynomial {params : AdmissibleParams}
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hsample : sample ∈ sublines.D.support)
    (p : DegPoly params.toLdParams (params.m * params.d) ×
      DegPoly params.toLdParams (params.m * params.d)) :
    DirectDegPoly params.extendedDirectLd (params.m * params.d + 1) :=
  let d := sublines.affineData sample hsample
  fun i => (extendedDirectScalarEquiv params).symm
    (combineLinePoly (d 0) (d 1) (d 2) (d 3) (d 4) (d 5) (d 6) (d 7) p.1 p.2 i)

def SubLineWitness.extendedMeasurement {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (side : PlayerSide) (line : DirectLineDesc params.extendedDirectLd) :
    Measurement (DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
      (setting.ExpandedLocalSpace side) :=
  let fam (s : sublines.Fiber line) :=
    (lines.T side s.val.2.1 s.val.2.2).postprocess
      (sublines.combinedPolynomial s.val (Finset.mem_filter.mp s.property).1)
  have hs : (∑ g, averageOperatorOverDistribution (sublines.conditionalLaw line)
      fun s => (fam s).effect g) = 1 := by
    rw [← averageOperatorOverDistribution_sum]; simp only [Measurement.sum_eq_one]
    exact averageOperatorOverDistribution_const_of_isProbability _
      (sublines.conditionalLaw_isProbability line) 1
  ⟨⟨fun g => averageOperatorOverDistribution (sublines.conditionalLaw line) fun s => (fam s).effect g,
    fun g => averageOperatorOverDistribution_nonneg _ _ fun s => (fam s).pos g,
    le_of_eq hs⟩, hs⟩

theorem SubLineWitness.avgOver_conditionalLaw {params : AdmissibleParams}
    (sublines : SubLineWitness params) (q : SubLineTriple params → ℝ) :
    avgOver (sublines.D.map Prod.fst) (fun l =>
      avgOver (sublines.conditionalLaw l) fun s => q s.val) = avgOver sublines.D q := by
  simp only [avgOver, SubLineWitness.conditionalLaw]
  refine (Finset.sum_congr rfl fun l _ => ?_).trans
    (Finset.sum_fiberwise_of_maps_to (fun s hs => Finset.mem_image.mpr ⟨s, hs, rfl⟩) _)
  rw [Finset.mul_sum]
  refine (Finset.sum_congr rfl fun s _ => ?_).trans (Finset.sum_coe_sort _ _)
  have hne := (sublines.fiber_mass_pos l).ne'
  field_simp [hne]

theorem SubLineWitness.combinedPolynomial_evalOpt {params : AdmissibleParams}
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hsample : sample ∈ sublines.D.support)
    (p : DegPoly params.toLdParams (params.m * params.d) ×
      DegPoly params.toLdParams (params.m * params.d))
    (pt : Fin params.extendedDirectLd.m → DirectScalarQ params.extendedDirectLd)
    (hpt : pt ∈ sample.1.pointSet) (vX vZ : PauliScalar params)
    (hX : evalOpt sample.2.1 (projX (directPointToPauli params pt)) p.1 = some vX)
    (hZ : evalOpt sample.2.2 (projZ (directPointToPauli params pt)) p.2 = some vZ) :
    (directEvalOpt sample.1 pt (sublines.combinedPolynomial sample hsample p)).map
      (extendedDirectScalarEquiv params) =
      some ((directPointToPauli params pt) (alphaVar params.m) * vX +
        (directPointToPauli params pt) (betaVar params.m) * vZ) := by
  have hev : DirectEvaluatesTo sample.1 (sublines.combinedPolynomial sample hsample p) pt
      ((extendedDirectScalarEquiv params).symm
        ((directPointToPauli params pt) (alphaVar params.m) * vX +
          (directPointToPauli params pt) (betaVar params.m) * vZ)) := by
    obtain ⟨t0, ht0⟩ := hpt
    refine ⟨⟨t0, ht0⟩, fun t ht => ?_⟩
    let d := sublines.affineData sample hsample
    have hc := sublines.affineData_compatible sample hsample
    have hf := combineLinePoly_spec (directPointToPauli params sample.1.base)
      (directPointToPauli params sample.1.direction)
      sample.2.1.base sample.2.1.direction sample.2.2.base sample.2.2.direction
      (d 0) (d 1) (d 2) (d 3) (d 4) (d 5) (d 6) (d 7) p.1 p.2 hc
      (extendedDirectScalarEquiv params t)
    have htr : directPointToPauli params pt = directPointToPauli params sample.1.base +
        extendedDirectScalarEquiv params t • directPointToPauli params sample.1.direction := by
      rw [ht, directPointToPauli_add, directPointToPauli_smul]
    have hvX := ((evalOpt_eq_some_iff _ _ _ _).mp hX).2 _ (htr ▸ hf.1)
    have hvZ := ((evalOpt_eq_some_iff _ _ _ _).mp hZ).2 _ (htr ▸ hf.2.1)
    apply (extendedDirectScalarEquiv params).injective
    have hesc {b : ℕ} (g : DirectDegPoly params.extendedDirectLd b) :
        extendedDirectScalarEquiv params (evalCoefficient g t) =
          evalCoefficient (fun i => extendedDirectScalarEquiv params (g i))
            (extendedDirectScalarEquiv params t) := by simp [evalCoefficient]
    rw [hesc, RingEquiv.apply_symm_apply]
    simp only [SubLineWitness.combinedPolynomial, RingEquiv.apply_symm_apply]
    rw [hf.2.2]; erw [hvX, hvZ]; rw [htr]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1]
  have hex : ∃ ans, DirectEvaluatesTo sample.1 (sublines.combinedPolynomial sample hsample p) pt ans :=
    ⟨_, hev⟩
  obtain ⟨t0, ht0⟩ := hev.1
  have hsome : directEvalOpt sample.1 pt (sublines.combinedPolynomial sample hsample p) =
      some ((extendedDirectScalarEquiv params).symm
        ((directPointToPauli params pt) (alphaVar params.m) * vX +
          (directPointToPauli params pt) (betaVar params.m) * vZ)) := by
    rw [directEvalOpt, dif_pos hex]
    exact congrArg some (((Classical.choose_spec hex).2 t0 ht0).symm.trans (hev.2 t0 ht0))
  rw [hsome]; simp

theorem combineLinePoly_axis_degree {S : Type*} [Field S] {b deg : ℕ}
    (hdeg : 1 ≤ deg) (d : Fin 8 → S) (pX pZ : Fin (b + 1) → S)
    (hdX : ∀ i, deg < i.val → pX i = 0) (hdZ : ∀ i, deg < i.val → pZ i = 0)
    (hax : (d 5 = 0 ∧ d 7 = 0) ∨ (d 1 = 0 ∧ d 3 = 0)) :
    ∀ i : Fin (b + 1 + 1), deg < i.val →
      combineLinePoly (d 0) (d 1) (d 2) (d 3) (d 4) (d 5) (d 6) (d 7) pX pZ i = 0 := by
  have hnat (f : Fin (b + 1) → S) (hf : ∀ i, deg < i.val → f i = 0) :
      (linePolynomialOfCoefficients f).natDegree ≤ deg := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    by_cases hi : i.val ≤ deg
    · refine Polynomial.natDegree_mul_le.trans ?_
      have hp := Polynomial.natDegree_pow_le (p := (Polynomial.X : Polynomial S)) (n := i.val)
      simp only [Polynomial.natDegree_X, Nat.mul_one] at hp; simpa using hp.trans hi
    · simp [hf i (Nat.lt_of_not_ge hi)]
  have haff (f : Polynomial S) (o sl : S) (hf : f.natDegree ≤ deg) :
      (f.comp (Polynomial.C o + Polynomial.C sl * Polynomial.X)).natDegree ≤ deg :=
    Polynomial.natDegree_comp_le.trans (by
      have ha : (Polynomial.C o + Polynomial.C sl * Polynomial.X).natDegree ≤ 1 :=
        (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) (Polynomial.natDegree_mul_le.trans (by simp)))
      simpa using Nat.mul_le_mul hf ha)
  have htot : (combineLinePolynomial (d 0) (d 1) (d 2) (d 3) (d 4) (d 5) (d 6) (d 7) pX pZ).natDegree ≤ deg := by
    unfold combineLinePolynomial
    rcases hax with ⟨ha, hb⟩ | ⟨hpX, hpZ⟩
    · simp only [ha, hb, Polynomial.C_0, zero_mul, add_zero]
      exact (Polynomial.natDegree_add_le _ _).trans (max_le
        (Polynomial.natDegree_mul_le.trans (by simpa using haff _ _ _ (hnat pX hdX)))
        (Polynomial.natDegree_mul_le.trans (by simpa using haff _ _ _ (hnat pZ hdZ))))
    · simp only [hpX, hpZ, Polynomial.C_0, zero_mul, add_zero, Polynomial.comp_C]
      have ht (c0 sl v : S) :
          ((Polynomial.C c0 + Polynomial.C sl * Polynomial.X) * Polynomial.C v).natDegree ≤ deg :=
        Polynomial.natDegree_mul_le.trans (by
          simp only [Polynomial.natDegree_C, Nat.add_zero]
          exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
            (Polynomial.natDegree_mul_le.trans (by simpa using hdeg))))
      exact (Polynomial.natDegree_add_le _ _).trans (max_le (ht _ _ _) (ht _ _ _))
  exact fun i hi => Polynomial.coeff_eq_zero_of_natDegree_lt (htot.trans_lt hi)

theorem SubLineWitness.affineData_axis {params : AdmissibleParams}
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hs : sample ∈ sublines.D.support) (haxis : sample.1.kind = .axis) :
    let d := sublines.affineData sample hs
    (d 5 = 0 ∧ d 7 = 0) ∨ (d 1 = 0 ∧ d 3 = 0) := by
  let d := sublines.affineData sample hs
  have hc := sublines.affineData_compatible sample hs
  have hsrc := sublines.axis_closure sample hs haxis
  have hcoord : directPointToPauli params sample.1.direction = coordinateDirection sample.1.index := by
    rcases sample with ⟨ln, _⟩
    cases ln with
    | axis => exact directPointToPauli_coordinateDirection params _
    | diagonal => cases haxis
  have hsl {pt bs dir : Fin params.m → PauliScalar params} {o sl : PauliScalar params}
      (hdir : dir ≠ 0) (hz0 : pt = bs + o • dir) (h1 : pt = bs + (o + sl) • dir) : sl = 0 :=
    (smul_eq_zero.mp (add_left_cancel (a := o • dir)
      (by simpa only [add_smul, add_zero] using (add_left_cancel (hz0.symm.trans h1)).symm))).resolve_right hdir
  have hne_ax (ln : LineDesc params.toLdParams) (ha : ln.kind = .axis) : ln.direction ≠ 0 := by
    cases ln with
    | axis _ sd _ => intro hz0; have h := congrFun hz0 (chiIndex params.toLdParams sd); simp [LineDesc.direction, coordinateDirection] at h
    | diagonal => cases ha
  by_cases hsp : sample.1.index = alphaVar params.m ∨ sample.1.index = betaVar params.m
  · right
    have hpr : projX (directPointToPauli params sample.1.direction) = 0 ∧
        projZ (directPointToPauli params sample.1.direction) = 0 := by
      rw [hcoord]; rcases hsp with ha | hb
      · rw [ha]; exact ⟨projX_coordinateDirection_alphaVar, projZ_coordinateDirection_alphaVar⟩
      · rw [hb]; exact ⟨projX_coordinateDirection_betaVar, projZ_coordinateDirection_betaVar⟩
    have hz0 := hc.2.2.2.2 0; have h1 := hc.2.2.2.2 1
    simp only [zero_smul, add_zero, mul_zero] at hz0
    simp only [one_smul, mul_one, projX_add, projZ_add, hpr.1, hpr.2, add_zero] at h1
    exact ⟨hsl (hne_ax _ hsrc.1) hz0.1 h1.1, hsl (hne_ax _ hsrc.2) hz0.2 h1.2⟩
  · left
    rw [← hc.2.1, ← hc.2.2.2.1, hcoord]
    simp [coordinateDirection, Ne.symm (not_or.mp hsp).1, Ne.symm (not_or.mp hsp).2]

theorem SubLineWitness.extendedMeasurement_axis_degree {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (side : PlayerSide) (line : DirectLineDesc params.extendedDirectLd)
    (poly : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
    (haxis : line.kind = .axis) (hdeg : ¬ ∀ idx, params.d < idx.val → poly idx = 0) :
    (sublines.extendedMeasurement lines side line).effect poly = 0 := by
  change averageOperatorOverDistribution (sublines.conditionalLaw line) _ = 0
  unfold averageOperatorOverDistribution
  refine Finset.sum_eq_zero fun s _ => ?_
  have hs := (Finset.mem_filter.mp s.property).1
  have hsa : s.val.1.kind = .axis := by rw [(Finset.mem_filter.mp s.property).2]; exact haxis
  have hsrc := sublines.axis_closure s.val hs hsa
  suffices hz : ((lines.T side s.val.2.1 s.val.2.2).postprocess
      (sublines.combinedPolynomial s.val hs)).effect poly = 0 by
    exact (congrArg ((sublines.conditionalLaw line).weight s • ·) hz).trans (smul_zero _)
  rw [Measurement.postprocess_effect]
  refine Finset.sum_eq_zero fun pair hp => ?_
  by_cases hdX : pair.1.FitsDegree params.d
  · by_cases hdZ : pair.2.FitsDegree params.d
    · refine (hdeg fun idx hidx => ?_).elim
      rw [← (Finset.mem_filter.mp hp).2]
      have hz0 := combineLinePoly_axis_degree params.hd (sublines.affineData s.val hs)
        pair.1 pair.2 hdX hdZ (sublines.affineData_axis s.val hs hsa) idx hidx
      change (extendedDirectScalarEquiv params).symm _ = 0
      erw [hz0]; exact map_zero _
    · exact lines.axis_degree_Z side _ _ _ _ hsrc.2 hdZ
  · exact lines.axis_degree_X side _ _ _ _ hsrc.1 hdX

def pairedSublineOverlap {params : AdmissibleParams} {error pointError lineError : ℝ}
    (setting : ProjectiveSetting params error) (points : CombinedPointsWitness setting pointError)
    (lines : CombinedLinesWitness setting points lineError) (first second : Placement)
    (sample : SubLineTriple params) : ℝ :=
  avgOver (uniformDistribution (DirectScalarQ params.extendedDirectLd)) fun parameter =>
    let point := directPointToPauli params (sample.1.base + parameter • sample.1.direction)
    ∑ pair, stateQForm setting.psiHat
      (setting.place first ((lines.T first.side sample.2.1 sample.2.2).effect pair) *
        setting.place second (((points.Q second.side (projX point) (projZ point)).postprocess
          fun values => (some values.1, some values.2)).effect
            (evalOpt sample.2.1 (projX point) pair.1, evalOpt sample.2.2 (projZ point) pair.2)))

theorem placed_overlap_postprocess {params : AdmissibleParams} {error : ℝ}
    {A O : Type*} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (S : ProjectiveSetting params error) (first second : Placement)
    (M : Measurement A (S.ExpandedLocalSpace first.side))
    (f : A → O) (R : O → Op (S.ExpandedLocalSpace second.side)) :
    (∑ o, stateQForm S.psiHat (S.place first ((M.postprocess f).effect o) * S.place second (R o))) =
      ∑ a, stateQForm S.psiHat (S.place first (M.effect a) * S.place second (R (f a))) := by
  simp only [Measurement.postprocess_effect, S.place_finsetSum, Finset.sum_mul, stateQForm_finset_sum]
  refine (Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun a ha => ?_).trans
    (Finset.sum_fiberwise _ _ _)
  rw [(Finset.mem_filter.mp ha).2]

theorem avgOver_directLinePointDist_resample_parameter (D : DirectLdParams)
    (q : DirectLineDesc D × (Fin D.m → DirectScalarQ D) → ℝ) :
    avgOver (directLinePointDist D) q =
      avgOver ((directLinePointDist D).map Prod.fst) fun l =>
        avgOver (uniformDistribution (DirectScalarQ D)) fun t =>
          q (l, l.base + t • l.direction) := by
  rw [Distribution.avgOver_map, directLinePointDist, avgOver_mix, avgOver_mix]; congr 1
  · congr 1; unfold directALinePointDist; simp only [Distribution.avgOver_map]
    rw [← uniformDistribution_map_equiv (directLdSpaceIndexEquiv D).symm]
    simp only [Distribution.avgOver_map, uniformDistribution_prod, SandwichProduct.avgOver_distribution_prod]
    refine avgOver_congr _ _ _ fun idx => ?_
    conv_lhs => rw [avgOver_comm]
    conv_rhs => rw [avgOver_comm]
    refine avgOver_congr _ _ _ fun dir => ?_
    simpa only [directLdSpaceIndexEquiv, Equiv.coe_fn_symm_mk, directALineDescOf,
      DirectLineDesc.base, DirectLineDesc.direction, lineRepMap_apply_self] using
      avgOver_uniform_lineRepMap_resample_parameter (coordinateDirection idx)
        fun bs pt => q (.axis (lineRepMap (coordinateDirection idx) bs) idx (lineRepMap_apply_self _ _), pt)
  · congr 1; unfold directDLinePointDist; simp only [Distribution.avgOver_map]
    rw [← uniformDistribution_map_equiv (directLdSpaceIndexEquiv D).symm]
    simp only [Distribution.avgOver_map, uniformDistribution_prod, SandwichProduct.avgOver_distribution_prod]
    refine avgOver_congr _ _ _ fun idx => ?_
    conv_lhs => rw [avgOver_comm]
    conv_rhs => rw [avgOver_comm]
    refine avgOver_congr _ _ _ fun dir => ?_
    simpa only [directLdSpaceIndexEquiv, Equiv.coe_fn_symm_mk, directDLineDescOf,
      DirectLineDesc.base, DirectLineDesc.direction, lineRepMap_apply_self] using
      avgOver_uniform_lineRepMap_resample_parameter (directPrefixProjection idx dir)
        fun bs pt => q (.diagonal (lineRepMap (directPrefixProjection idx dir) bs) idx
          (directPrefixProjection idx dir) (lineRepMap_apply_self _ _)
          (fun c hb => by simp [directPrefixProjection, hb]), pt)

theorem SubLineWitness.extended_consistencyDefect_le {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    consistencyDefect (directLinePointDist params.extendedDirectLd)
      (fun sample answer => setting.place first
        (((sublines.extendedMeasurement lines first.side sample.1).postprocess
          fun polynomial => (directEvalOpt sample.1 sample.2 polynomial).map
            (extendedDirectScalarEquiv params)).effect answer))
      (fun sample answer => setting.place second
        (((points.Q second.side (projX (directPointToPauli params sample.2))
          (projZ (directPointToPauli params sample.2))).postprocess fun values => some
            ((directPointToPauli params sample.2) (alphaVar params.m) * values.1 +
              (directPointToPauli params sample.2) (betaVar params.m) * values.2)).effect answer))
      setting.psiHat ≤ 1 - avgOver sublines.D
        (pairedSublineOverlap setting points lines first second) := by
  erw [consistencyDefect_eq_one_sub_overlap (directLinePointDist params.extendedDirectLd)
    (fun s => setting.placedMeasurement first ((sublines.extendedMeasurement lines first.side s.1).postprocess
      fun p => (directEvalOpt s.1 s.2 p).map (extendedDirectScalarEquiv params)))
    (fun s => setting.placedMeasurement second
      ((points.Q second.side (projX (directPointToPauli params s.2))
        (projZ (directPointToPauli params s.2))).postprocess fun v => some
          ((directPointToPauli params s.2) (alphaVar params.m) * v.1 +
            (directPointToPauli params s.2) (betaVar params.m) * v.2)))
    setting.psiHat (directLinePointDist_isProbability _) setting.psiHat_norm]
  refine sub_le_sub_left ?_ 1
  rw [avgOver_directLinePointDist_resample_parameter, ← sublines.extended_marginal, ← sublines.avgOver_conditionalLaw]
  refine avgOver_mono _ _ _ fun line => ?_
  unfold pairedSublineOverlap; rw [avgOver_comm]
  refine avgOver_mono _ _ _ fun t => ?_
  let pt := line.base + t • line.direction
  have hpt : pt ∈ line.pointSet := ⟨t, rfl⟩
  have hpl_avg {Smp : Type} (law : Distribution Smp)
      (fam : Smp → Op (setting.ExpandedLocalSpace first.side))
      (R : Op (setting.ExpandedLocalSpace second.side)) :
      stateQForm setting.psiHat
        (setting.place first (averageOperatorOverDistribution law fam) * setting.place second R) =
      avgOver law fun s => stateQForm setting.psiHat (setting.place first (fam s) * setting.place second R) := by
    unfold averageOperatorOverDistribution avgOver
    rw [setting.place_finsetSum, Finset.sum_mul, stateQForm_finset_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hrsm (r : ℝ) (M : Op (setting.ExpandedLocalSpace first.side)) :
        setting.place first (r • M) = r • setting.place first M := by
      ext r' c'; cases first <;> simp only [ProjectiveSetting.place, Matrix.smul_apply, Complex.real_smul] <;> ring
    rw [hrsm, smul_mul_assoc, show ∀ M : Op (SixReg params setting.toStrategy.ιA setting.toStrategy.ιB),
      law.weight s • M = (law.weight s : ℂ) • M from fun M => by ext; simp [Complex.real_smul]]
    simp only [stateQForm, WinImplications.applyOperatorToState_smul_op, inner_smul_right,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  refine (le_of_eq (avgOver_congr _ _ _ fun s => by rw [(Finset.mem_filter.mp s.property).2])).trans ?_
  dsimp only [ProjectiveSetting.placedMeasurement_effect]
  rw [placed_overlap_postprocess]
  change _ ≤ ∑ poly, stateQForm setting.psiHat
    (setting.place first (averageOperatorOverDistribution (sublines.conditionalLaw line)
      fun s => ((lines.T first.side s.val.2.1 s.val.2.2).postprocess
        (sublines.combinedPolynomial s.val (Finset.mem_filter.mp s.property).1)).effect poly) *
      setting.place second _)
  simp_rw [hpl_avg]; rw [← avgOver_sum]
  refine avgOver_mono _ _ _ fun ⟨sv, hs_prop⟩ => ?_
  conv_rhs => rw [placed_overlap_postprocess]
  apply Finset.sum_le_sum
  intro pair _
  have hs := (Finset.mem_filter.mp hs_prop).1
  have hln := (Finset.mem_filter.mp hs_prop).2
  have hle : (((points.Q second.side (projX (directPointToPauli params pt))
      (projZ (directPointToPauli params pt))).postprocess fun v => (some v.1, some v.2)).effect
        (evalOpt sv.2.1 (projX (directPointToPauli params pt)) pair.1,
          evalOpt sv.2.2 (projZ (directPointToPauli params pt)) pair.2)) ≤
      (((points.Q second.side (projX (directPointToPauli params pt))
        (projZ (directPointToPauli params pt))).postprocess fun v => some
          ((directPointToPauli params pt) (alphaVar params.m) * v.1 +
            (directPointToPauli params pt) (betaVar params.m) * v.2)).effect
        ((directEvalOpt line pt (sublines.combinedPolynomial sv hs pair)).map
          (extendedDirectScalarEquiv params))) := by
    let Q := points.Q second.side (projX (directPointToPauli params pt)) (projZ (directPointToPauli params pt))
    rw [← hln]
    cases hX : evalOpt sv.2.1 (projX (directPointToPauli params pt)) pair.1 with
    | none =>
      erw [completedPair_effect_eq_zero Q (none, _) fun _ => by simp]
      exact Submeasurement.pos _ _
    | some vX =>
      cases hZ : evalOpt sv.2.2 (projZ (directPointToPauli params pt)) pair.2 with
      | none =>
        erw [completedPair_effect_eq_zero Q (_, none) fun _ => by simp]
        exact Submeasurement.pos _ _
      | some vZ =>
        rw [sublines.combinedPolynomial_evalOpt sv hs pair pt (hln ▸ hpt) vX vZ hX hZ]
        erw [completedPair_effect_some Q (vX, vZ)]
        rw [Measurement.postprocess_effect]
        exact Finset.single_le_sum (fun _ _ => Q.pos _) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
  have hp_pos := setting.place_mul_place_nonneg first second hopposite
    ((lines.T first.side sv.2.1 sv.2.2).pos pair) (sub_nonneg.mpr hle)
  rw [setting.place_sub, mul_sub] at hp_pos
  exact quadratic_form_mono (sub_nonneg.mp hp_pos) setting.psiHat

set_option maxHeartbeats 800000 in
-- Combines paired-vs-ordered, X-removal, and Z-deficit overlap bounds.
theorem subline_joint_overlap_near_one_at :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (P : AdmissibleParams) (ε δQ δP : ℝ)
        (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
        (lines : CombinedLinesWitness S points δP) (sublines : SubLineWitness P)
        (first second : Placement), first.IsOpposite second →
        |avgOver sublines.D (pairedSublineOverlap S points lines first second) - 1| ≤
          constant * (δQ ^ (1 / 2 : ℝ) + Real.sqrt (P.m : ℝ) *
            (δP ^ (1 / 4 : ℝ) + δQ ^ (1 / 4 : ℝ) + ε ^ (1 / 4 : ℝ))) := by
  refine ⟨6, by norm_num, fun P ε δQ δP S points lines sublines first second hopposite => ?_⟩
  let law := Distribution.prod sublines.D (uniformDistribution (DirectScalarQ P.extendedDirectLd))
  have hprob : law.IsProbability := Distribution.prod_isProbability _ _ sublines.isProbability
    (uniformDistribution_isProbability _)
  have hδP : 0 ≤ δP := (avgOver_nonneg _ _ fun s =>
    consistencyDefect_integrand_nonneg S first second hopposite _ _).trans
    (lines.consistent first second hopposite)
  have hδQ : 0 ≤ δQ := (opFamilyDistSq_nonneg _ _ _ _).trans (points.self_consistent first second hopposite)
  have hm : (1 : ℝ) ≤ P.m := by exact_mod_cast P.one_le_m
  let pt (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd) :=
    directPointToPauli P (s.1.1.base + s.2 • s.1.1.direction)
  let ordOv : SubLineTriple P → ℝ := fun sample =>
    avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun t =>
      let p := directPointToPauli P (sample.1.base + t • sample.1.direction)
      ∑ pair, stateQForm S.psiHat
        (S.place first ((lines.T first.side sample.2.1 sample.2.2).effect pair) *
          S.place second ((S.pointMeasExpOption second.side .Z (projZ p)).effect
              (evalOpt sample.2.2 (projZ p) pair.2) *
            (S.pointMeasExpOption second.side .X (projX p)).effect
              (evalOpt sample.2.1 (projX p) pair.1)))
  let zOv := avgOver sublines.D fun sample =>
    avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun t =>
      basisPointOverlapAt lines .Z first second
        (sample.2, projZ (directPointToPauli P (sample.1.base + t • sample.1.direction)))
  let LM (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd) :=
    S.placedMeasurement first ((lines.T first.side s.1.2.1 s.1.2.2).postprocess fun fs =>
      (evalOpt s.1.2.1 (projX (pt s)) fs.1, evalOpt s.1.2.2 (projZ (pt s)) fs.2))
  have hrg (R : (SubLineTriple P × DirectScalarQ P.extendedDirectLd) →
      Option (PauliScalar P) × Option (PauliScalar P) → Op (S.ExpandedLocalSpace second.side)) :
      avgOver law (fun s => ∑ o, stateQForm S.psiHat ((LM s).effect o * S.place second (R s o))) =
      avgOver sublines.D fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun t =>
          ∑ pair, stateQForm S.psiHat
            (S.place first ((lines.T first.side sample.2.1 sample.2.2).effect pair) *
              S.place second (R (sample, t)
                (evalOpt sample.2.1 (projX (pt (sample, t))) pair.1,
                  evalOpt sample.2.2 (projZ (pt (sample, t))) pair.2))) := by
    dsimp only [law]; rw [SandwichProduct.avgOver_distribution_prod]
    exact avgOver_congr _ _ _ fun _ => avgOver_congr _ _ _ fun _ =>
      placed_overlap_postprocess S first second _ _ _
  have h1 : |avgOver sublines.D (pairedSublineOverlap S points lines first second) -
      avgOver sublines.D ordOv| ≤ 2 * δQ ^ (1 / 2 : ℝ) := by
    let jnt (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd) (o) :=
      S.place second (((points.Q second.side (projX (pt s)) (projZ (pt s))).postprocess
        fun v => (some v.1, some v.2)).effect o)
    let ord (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd) (o : Option (PauliScalar P) × Option (PauliScalar P)) :=
      S.place second ((S.pointMeasExpOption second.side .Z (projZ (pt s))).effect o.2 *
        (S.pointMeasExpOption second.side .X (projX (pt s))).effect o.1)
    have hdist : opFamilyDistSq law jnt ord S.psiHat ≤ 4 * δQ := by
      unfold opFamilyDistSq
      refine (le_of_eq (avgOver_congr law _ _ fun s =>
        S.completedPair_norm_sq_sum_ZX points second (projX (pt s)) (projZ (pt s)))).trans ?_
      dsimp only [law, pt]; rw [SandwichProduct.avgOver_distribution_prod,
        SubLineWitness.avgOver_projX_projZ P sublines fun c => ∑ ab, ‖applyOperatorToState
          (S.place second ((points.Q second.side c.1 c.2).effect ab) -
            S.place second ((S.pointMeasExp second.side .Z c.2).effect ab.2 *
              (S.pointMeasExp second.side .X c.1).effect ab.1)) S.psiHat‖ ^ 2]
      exact points.orderedZX_dist_le second
    have hg := abs_overlap_gap_le_sqrt_of_opFamilyDistSq law LM jnt ord S.psiHat hprob S.psiHat_norm
      (4 * δQ) hdist
    dsimp only [jnt, ord] at hg; rw [hrg, hrg] at hg
    have heq : Real.sqrt (4 * δQ) = 2 * δQ ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num [Real.sqrt_eq_rpow]
    exact hg.trans_eq heq
  have h2 : |avgOver sublines.D ordOv - zOv| ≤
      2 * Real.sqrt (P.m : ℝ) * (δP ^ (1 / 4 : ℝ) + δQ ^ (1 / 4 : ℝ)) := by
    have hcs := abs_overlap_gap_le_sqrt_one_sub_of_isProj' law LM
      (fun s o => S.place second ((S.pointMeasExpOption second.side .X (projX (pt s))).effect o.1))
      (fun s o => S.place second ((S.pointMeasExpOption second.side .Z (projZ (pt s))).effect o.2))
      (fun s o => S.place second ((S.pointMeasExpOption second.side .Z (projZ (pt s))).effect o.2 *
        (S.pointMeasExpOption second.side .X (projX (pt s))).effect o.1))
      S.psiHat hprob S.psiHat_norm
      (fun _ _ => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
      (fun _ _ => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
      (fun _ _ => S.place_comm first second hopposite _ _)
      (fun _ _ => S.place_comm first second hopposite _ _)
      (fun _ _ => ProjectiveSetting.place_mul S second _ _)
    rw [hrg, hrg, hrg] at hcs
    have hz_eq : (avgOver sublines.D fun sample => avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
        fun t => ∑ pair, stateQForm S.psiHat
          (S.place first ((lines.T first.side sample.2.1 sample.2.2).effect pair) *
            S.place second ((S.pointMeasExpOption second.side .Z (projZ (pt (sample, t)))).effect
              (evalOpt sample.2.2 (projZ (pt (sample, t))) pair.2)))) = zOv :=
      avgOver_congr _ _ _ fun sample => avgOver_congr _ _ _ fun t =>
        Fintype.sum_prod_type (f := fun pair => stateQForm S.psiHat
          (S.place first ((lines.T first.side sample.2.1 sample.2.2).effect pair) *
            S.place second ((S.pointMeasExpOption second.side .Z (projZ (pt (sample, t)))).effect
              (evalOpt sample.2.2 (projZ (pt (sample, t))) pair.2))))
    have hx_eq : (avgOver sublines.D fun sample => avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
        fun t => ∑ pair, stateQForm S.psiHat
          (S.place first ((lines.T first.side sample.2.1 sample.2.2).effect pair) *
            S.place second ((S.pointMeasExpOption second.side .X (projX (pt (sample, t)))).effect
              (evalOpt sample.2.1 (projX (pt (sample, t))) pair.1)))) =
        avgOver sublines.D fun sample => avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          fun t => basisPointOverlapAt lines .X first second (sample.2, projX (pt (sample, t))) :=
      avgOver_congr _ _ _ fun sample => avgOver_congr _ _ _ fun t =>
        Fintype.sum_prod_type (f := fun pair => stateQForm S.psiHat
          (S.place first ((lines.T first.side sample.2.1 sample.2.2).effect pair) *
            S.place second ((S.pointMeasExpOption second.side .X (projX (pt (sample, t)))).effect
              (evalOpt sample.2.1 (projX (pt (sample, t))) pair.1))))
    rw [hz_eq, hx_eq] at hcs
    exact hcs.trans ((Real.sqrt_le_sqrt
      (sublines.one_sub_avgOver_basisPointOverlap_le lines .X first second hopposite)).trans
      (sqrt_deficit_bound_le _ _ _ hm hδP hδQ))
  have h3 : |zOv - 1| ≤
      2 * Real.sqrt (P.m : ℝ) * (δP ^ (1 / 4 : ℝ) + δQ ^ (1 / 4 : ℝ) + ε ^ (1 / 4 : ℝ)) := by
    have hd := sublines.one_sub_avgOver_basisPointOverlap_le lines .Z first second hopposite
    have hl := sublines.avgOver_zPointOverlap_le_one lines first second hopposite
    have hn : 0 ≤ zOv := avgOver_nonneg _ _ fun s => avgOver_nonneg _ _ fun t =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => stateQForm_nonneg _
        (S.place_mul_place_nonneg first second hopposite ((lines.T _ _ _).pos _)
          ((S.pointMeasExpOption _ _ _).pos _))
    change 1 - zOv ≤ _ at hd; change zOv ≤ 1 at hl
    have h0 : 0 ≤ 1 - zOv := by linarith
    have habs : |zOv - 1| ≤ 2 * Real.sqrt (P.m : ℝ) * (δP ^ (1 / 4 : ℝ) + δQ ^ (1 / 4 : ℝ)) := by
      rw [abs_sub_comm, abs_of_nonneg h0, ← Real.sqrt_sq h0]
      exact (Real.sqrt_le_sqrt ((by nlinarith : (1 - zOv) ^ 2 ≤ 1 - zOv).trans hd)).trans
        (sqrt_deficit_bound_le _ _ _ hm hδP hδQ)
    refine habs.trans ?_
    have hq := rpow_quarter_nonneg ε; simp only [Real.rpow_eq_pow] at hq
    nlinarith [mul_nonneg (Real.sqrt_nonneg (P.m : ℝ)) hq]
  have hch := (abs_sub_le _ _ 1).trans (add_le_add h1 ((abs_sub_le _ zOv 1).trans (add_le_add h2 h3)))
  have hh : 0 ≤ δQ ^ (1 / 2 : ℝ) := by rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_nonneg _
  have hs : 0 ≤ δP ^ (1 / 4 : ℝ) + δQ ^ (1 / 4 : ℝ) := add_nonneg (rpow_quarter_nonneg _) (rpow_quarter_nonneg _)
  have hq := rpow_quarter_nonneg ε; simp only [Real.rpow_eq_pow] at hq
  refine hch.trans ?_
  nlinarith [mul_nonneg (Real.sqrt_nonneg (P.m : ℝ)) hs, mul_nonneg (Real.sqrt_nonneg (P.m : ℝ)) hq]

end

end MIPStarRE.QPBT
