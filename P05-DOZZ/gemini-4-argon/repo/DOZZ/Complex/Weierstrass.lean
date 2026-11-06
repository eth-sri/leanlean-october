/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Identity
public import Mathlib.MeasureTheory.Integral.TorusIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Finite-dimensional Weierstrass theorem

Uniform convergence on a closed polydisc passes through the product Cauchy
integral and its joint derivative. Smaller polydiscs provide neighborhoods
on which the resulting derivative convergence is uniform.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace DOZZ.Proofs

/-- The product Cauchy kernel without its contour Jacobian. -/
noncomputable def productCauchyKernel {N : ℕ} (z w : Fin N → ℂ) : ℂ :=
  ∏ i, (w i - z i)⁻¹

/-- Torus coordinates lie on the specified coordinate circles. -/
theorem torusMap_coordinate_mem_sphere {N} (a : Fin N → ℂ) (R : Fin N → ℝ)
    (hR : ∀ i, 0 ≤ R i) (θ : Fin N → ℝ) i :
    torusMap a R θ i ∈ Metric.sphere (a i) (R i) :=
  circleMap_mem_sphere (a i) (hR i) (θ i)

/-- The whole product torus lies in the closed coordinate polydisc. -/
theorem torusMap_mem_closed_pi {N} (a : Fin N → ℂ) (R : Fin N → ℝ)
    (hR : ∀ i, 0 ≤ R i) θ :
    torusMap a R θ ∈ Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)) := by
  intro i _
  exact Metric.sphere_subset_closedBall (torusMap_coordinate_mem_sphere a R hR θ i)

/-- The product torus parameterization is continuous. -/
theorem continuous_torusMap {N} (a : Fin N → ℂ) R :
    Continuous (torusMap a R) := by
  unfold torusMap
  fun_prop

/-- An interior coordinate cannot meet its boundary circle. -/
theorem coordinate_sub_ne_zero_on_torus {N} (a : Fin N → ℂ) (R : Fin N → ℝ)
    (hR : ∀ i, 0 < R i) z (hz : z ∈ complexPolydisc a R)
    (θ : Fin N → ℝ) i : torusMap a R θ i - z i ≠ 0 := by
  intro heq
  have hi := torusMap_coordinate_mem_sphere a R (fun i => (hR i).le) θ i
  rw [sub_eq_zero.mp heq, Metric.mem_sphere, dist_eq_norm] at hi
  exact (hz i).ne hi

/-- The product kernel is continuous on the torus for an interior parameter. -/
theorem continuous_productCauchyKernel_torus {N} (a : Fin N → ℂ)
    (R : Fin N → ℝ) (hR : ∀ i, 0 < R i)
    z (hz : z ∈ complexPolydisc a R) :
    Continuous (fun θ => productCauchyKernel z (torusMap a R θ)) := by
  unfold productCauchyKernel
  apply continuous_finsetProd
  intro i _
  exact (((continuous_apply i).comp (continuous_torusMap a R)).sub continuous_const).inv₀
    (coordinate_sub_ne_zero_on_torus a R hR z hz · i)

/-- A function continuous on the closed polydisc is continuous along its torus. -/
theorem continuous_on_torus {N} (a : Fin N → ℂ) (R : Fin N → ℝ)
    (hR : ∀ i, 0 < R i) (f : (Fin N → ℂ) → ℂ)
    (hf : ContinuousOn f (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)))) :
    Continuous (fun θ => f (torusMap a R θ)) := by
  rw [← continuousOn_univ]
  exact hf.comp (continuous_torusMap a R).continuousOn
    (fun θ _ => torusMap_mem_closed_pi a R (fun i => (hR i).le) θ)

/-- The Cauchy integrand is torus integrable. -/
theorem torusIntegrable_productCauchyKernel {N} (a : Fin N → ℂ)
    (R : Fin N → ℝ) (hR : ∀ i, 0 < R i) (f : (Fin N → ℂ) → ℂ)
    (hf : ContinuousOn f (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i))))
    z (hz : z ∈ complexPolydisc a R) :
    TorusIntegrable (fun w => f w * productCauchyKernel z w) a R := by
  exact ((continuous_on_torus a R hR f hf).mul
    (continuous_productCauchyKernel_torus a R hR z hz)).continuousOn.integrableOn_compact
    isCompact_Icc



/-- Inserting a fixed initial coordinate is complex differentiable. -/
theorem differentiable_cons_tail {N} (w : ℂ) :
    Differentiable ℂ (Fin.cons (α := fun _ => ℂ) w : (Fin N → ℂ) → (Fin (N + 1) → ℂ)) := by
  apply differentiable_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact differentiable_const w
  · simp only [Fin.cons_succ]
    exact (ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℂ] ℂ).differentiable

/-- Varying just the initial coordinate is complex differentiable. -/
theorem differentiable_cons_head {N : ℕ} (v : Fin N → ℂ) :
    Differentiable ℂ (fun w => Fin.cons (α := fun _ => ℂ) w v) := by
  apply differentiable_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact differentiable_id
  · simp only [Fin.cons_succ]
    exact differentiable_const (v j)

/-- Closed polydisc membership splits into initial and tail coordinates. -/
theorem mem_closed_pi_cons {N} (a : Fin (N + 1) → ℂ) (R : Fin (N + 1) → ℝ)
    w v :
    Fin.cons (α := fun _ => ℂ) w v ∈ Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)) ↔
      w ∈ Metric.closedBall (a 0) (R 0) ∧
      v ∈ Set.pi Set.univ (fun i => Metric.closedBall (a i.succ) (R i.succ)) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [Fin.cons_zero] using h 0 (mem_univ 0)
    · intro i _
      simpa only [Fin.cons_succ] using h i.succ (mem_univ i.succ)
  · rintro ⟨hw, hv⟩ i _
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using hw
    · simpa only [Fin.cons_succ] using hv j (mem_univ j)

/-- Iterated scalar Cauchy gives the exact product contour representation.

The induction uses `torusIntegral_succ`, whose Fubini hypothesis was established
from continuity of the nonsingular kernel on the compact product torus. At
every scalar boundary point the remaining closed polydisc stays in `U`, so
the induction applies even on the product's distinguished boundary.
-/
theorem torusIntegral_productCauchyKernel {N} U (hU : IsOpen U)
    (f : (Fin N → ℂ) → ℂ) (hf : DifferentiableOn ℂ f U)
    (a : Fin N → ℂ) (R : Fin N → ℝ) (hR : ∀ i, 0 < R i)
    (hclosed : Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)) ⊆ U)
    z (hz : z ∈ complexPolydisc a R) :
    torusIntegral (fun w => f w * productCauchyKernel z w) a R =
      (2 * Real.pi * I : ℂ) ^ N * f z := by
  have productCauchyKernel_cons {N} (z : Fin (N + 1) → ℂ) w v : productCauchyKernel z (Fin.cons (α := fun _ => ℂ) w v) = (w - z 0)⁻¹ * productCauchyKernel (z ∘ Fin.succ) v := by
    simp only [productCauchyKernel, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Function.comp_apply]
  have cons_zero_tail {N} (z : Fin (N + 1) → ℂ) : Fin.cons (z 0) (z ∘ Fin.succ) = z := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  induction N with
  | zero =>
      simp only [torusIntegral_dim0, productCauchyKernel, Fin.prod_univ_zero,
        mul_one, pow_zero, one_mul]
      congr 1
      exact Subsingleton.elim a z
  | succ N ih =>
      have hcont := hf.continuousOn.mono hclosed
      rw [torusIntegral_succ (torusIntegrable_productCauchyKernel a R hR f hcont z hz)]
      have htail : (z ∘ Fin.succ) ∈
          Set.pi Set.univ (fun i => Metric.closedBall (a i.succ) (R i.succ)) := by
        intro i _
        simpa only [Metric.mem_closedBall, dist_eq_norm, Function.comp_apply] using (hz i.succ).le
      have hstep : EqOn
          (fun w => torusIntegral (fun v => f (Fin.cons (α := fun _ => ℂ) w v) * productCauchyKernel z (Fin.cons (α := fun _ => ℂ) w v))
            (a ∘ Fin.succ) (R ∘ Fin.succ))
          (fun w => (2 * Real.pi * I : ℂ) ^ N * ((w - z 0)⁻¹ * f (Fin.cons (α := fun _ => ℂ) w (z ∘ Fin.succ))))
          (Metric.sphere (a 0) (R 0)) := by
        intro w hw
        dsimp only
        have hfun : (fun v => f (Fin.cons (α := fun _ => ℂ) w v) * productCauchyKernel z (Fin.cons (α := fun _ => ℂ) w v)) =
            (fun v => (w - z 0)⁻¹ * (f (Fin.cons (α := fun _ => ℂ) w v) * productCauchyKernel (z ∘ Fin.succ) v)) := by
          funext v
          rw [productCauchyKernel_cons]
          ring
        rw [hfun, torusIntegral_const_mul]
        change (w - z 0)⁻¹ * torusIntegral
          (fun v => (f ∘ Fin.cons (α := fun _ => ℂ) w) v * productCauchyKernel (z ∘ Fin.succ) v)
          (a ∘ Fin.succ) (R ∘ Fin.succ) = _
        rw [(ih ((Fin.cons (α := fun _ => ℂ) w) ⁻¹' U) (hU.preimage (differentiable_cons_tail w).continuous) (f ∘ Fin.cons (α := fun _ => ℂ) w) (hf.comp (differentiable_cons_tail w).differentiableOn (fun _ ht => ht)) (a ∘ Fin.succ) (R ∘ Fin.succ) (fun i => hR i.succ) (by intro v hv; exact hclosed ((mem_closed_pi_cons a R w v).mpr ⟨(Metric.sphere_subset_closedBall hw), hv⟩)) (z ∘ Fin.succ) (fun i => hz i.succ))]
        simp only [Function.comp_apply]
        ring
      rw [circleIntegral.integral_congr (hR 0).le hstep, circleIntegral.integral_const_mul]
      have hheadMap : MapsTo (fun w => Fin.cons (α := fun _ => ℂ) w (z ∘ Fin.succ))
          (Metric.closedBall (a 0) (R 0)) U := by
        intro w hw
        exact hclosed ((mem_closed_pi_cons a R w (z ∘ Fin.succ)).mpr ⟨hw, htail⟩)
      have hc : ContinuousOn (fun w => f (Fin.cons (α := fun _ => ℂ) w (z ∘ Fin.succ)))
          (Metric.closedBall (a 0) (R 0)) :=
        hf.continuousOn.comp (differentiable_cons_head (z ∘ Fin.succ)).continuous.continuousOn hheadMap
      have hd : ∀ w ∈ Metric.ball (a 0) (R 0) \ (∅ : Set ℂ),
          DifferentiableAt ℂ (fun w => f (Fin.cons (α := fun _ => ℂ) w (z ∘ Fin.succ))) w := by
        intro w hw
        exact (hf.differentiableAt (hU.mem_nhds (hheadMap (Metric.ball_subset_closedBall hw.1)))).comp w
          (differentiable_cons_head (z ∘ Fin.succ) w)
      have hscalar := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        countable_empty (show z 0 ∈ Metric.ball (a 0) (R 0) by
          simpa only [Metric.mem_ball, dist_eq_norm] using hz 0) hc hd
      simp only [smul_eq_mul, cons_zero_tail] at hscalar
      rw [hscalar, pow_succ]
      ring

/-- The joint complex derivative of the product Cauchy kernel. -/
noncomputable def productCauchyKernelDeriv {N : ℕ} (z w : Fin N → ℂ) :
    (Fin N → ℂ) →L[ℂ] ℂ :=
  ∑ i, (∏ j ∈ Finset.univ.erase i, (w j - z j)⁻¹) •
    (((w i - z i) ^ 2)⁻¹ • ContinuousLinearMap.proj i)



/-- Coordinate evaluation has operator norm at most one in the finite maximum norm. -/
theorem norm_coordinate_proj_le_one {N} (i : Fin N) :
    ‖(ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm z i

/-- Fixed coordinate bounds give a fixed bound for the joint derivative. -/
noncomputable def productCauchyDerivBound {N : ℕ} (b : Fin N → ℝ) : ℝ :=
  ∑ i, (∏ j ∈ Finset.univ.erase i, b j) * (b i) ^ 2



/-- Componentwise inverse bounds control the operator norm of the full derivative. -/
theorem norm_productCauchyKernelDeriv_le {N} (z w : Fin N → ℂ) (b : Fin N → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hbound : ∀ i, ‖(w i - z i)⁻¹‖ ≤ b i) :
    ‖productCauchyKernelDeriv z w‖ ≤ productCauchyDerivBound b := by
  unfold productCauchyKernelDeriv productCauchyDerivBound
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, norm_prod, norm_smul, norm_inv, norm_pow]
  have hterm : (‖w i - z i‖ ^ 2)⁻¹ *
      ‖(ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ)‖ ≤ (b i) ^ 2 := by
    calc
      _ ≤ (‖w i - z i‖ ^ 2)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (norm_coordinate_proj_le_one i) (by positivity)
      _ ≤ (b i) ^ 2 := by simpa only [mul_one] using (by rw [← inv_pow]; exact pow_le_pow_left₀ (by positivity) (by simpa only [norm_inv] using hbound i) 2)
  exact mul_le_mul (Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hbound j)) hterm (by positivity) (Finset.prod_nonneg fun j _ => hb j)

/-- The half-sized parameter polydisc stays a fixed distance from every contour coordinate. -/
theorem inverse_coordinate_bound_on_torus {N} (a : Fin N → ℂ) (R : Fin N → ℝ)
    (hR : ∀ i, 0 < R i) z
    (hz : z ∈ complexPolydisc a (fun i => R i / 2)) (θ : Fin N → ℝ) i :
    ‖(torusMap a R θ i - z i)⁻¹‖ ≤ (R i / 2)⁻¹ := by
  have hnorm : ‖torusMap a R θ i - a i‖ = R i := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using (torusMap_coordinate_mem_sphere a R (fun i => (hR i).le) θ i)
  have hdiff := norm_sub_norm_le (torusMap a R θ i - a i) (z i - a i)
  have hsub : (torusMap a R θ i - a i) - (z i - a i) = torusMap a R θ i - z i := by ring
  rw [hnorm, hsub] at hdiff
  have hden : R i / 2 ≤ ‖torusMap a R θ i - z i‖ := by linarith [hz i]
  have hhalf := half_pos (hR i)
  rw [norm_inv]
  exact (inv_le_inv₀ (hhalf.trans_le hden) hhalf).mpr hden

/-- The derivative kernel is continuous in the contour parameter. -/
theorem continuous_productCauchyKernelDeriv_torus {N} (a : Fin N → ℂ)
    (R : Fin N → ℝ) (hR : ∀ i, 0 < R i)
    z (hz : z ∈ complexPolydisc a R) :
    Continuous (fun θ => productCauchyKernelDeriv z (torusMap a R θ)) := by
  unfold productCauchyKernelDeriv
  apply continuous_finsetSum
  intro i _
  apply Continuous.fun_smul
  · apply continuous_finsetProd
    intro j _
    exact (((continuous_apply j).comp (continuous_torusMap a R)).sub continuous_const).inv₀
      (coordinate_sub_ne_zero_on_torus a R hR z hz · j)
  · apply Continuous.fun_smul
    · exact ((((continuous_apply i).comp (continuous_torusMap a R)).sub continuous_const).pow 2).inv₀
        (fun θ => pow_ne_zero _ (coordinate_sub_ne_zero_on_torus a R hR z hz θ i))
    · exact continuous_const

/-- The finite angle cube used by the torus integral. -/
def angleCube (N : ℕ) : Set (Fin N → ℝ) := Icc 0 (fun _ => 2 * Real.pi)

/-- The restricted angle measure is finite, including in dimension zero. -/
instance angleCube_finite (N : ℕ) : IsFiniteMeasure (volume.restrict (angleCube N)) :=
  ⟨by simpa [angleCube] using (measure_Icc_lt_top (a := (0 : Fin N → ℝ))
    (b := fun _ => 2 * Real.pi))⟩

/-- The Jacobian factor in the torus parametrization. -/
noncomputable def torusJacobian {N : ℕ} (R : Fin N → ℝ) (θ : Fin N → ℝ) : ℂ :=
  ∏ i, (R i : ℂ) * exp ((θ i : ℂ) * I) * I

/-- The Jacobian is continuous in the angle parameter. -/
theorem continuous_torusJacobian {N : ℕ} (R : Fin N → ℝ) :
    Continuous (torusJacobian R) := by
  unfold torusJacobian
  fun_prop

/-- Its norm is constant on the angle cube. -/
theorem norm_torusJacobian {N} (R θ : Fin N → ℝ) :
    ‖torusJacobian R θ‖ = ∏ i, |R i| := by
  simp [torusJacobian, norm_prod]

/-- The Cauchy transform of a boundary function. -/
noncomputable def polydiscCauchy {N : ℕ} (f : (Fin N → ℂ) → ℂ)
    (a : Fin N → ℂ) (R : Fin N → ℝ) (z : Fin N → ℂ) : ℂ :=
  torusIntegral (fun w => f w * productCauchyKernel z w) a R

/-- Its candidate joint complex derivative. -/
noncomputable def polydiscCauchyDeriv {N : ℕ} (f : (Fin N → ℂ) → ℂ)
    (a : Fin N → ℂ) (R : Fin N → ℝ) (z : Fin N → ℂ) : (Fin N → ℂ) →L[ℂ] ℂ :=
  ∫ θ in angleCube N,
    torusJacobian R θ • (f (torusMap a R θ) • productCauchyKernelDeriv z (torusMap a R θ))

/-- The half-sized polydisc is contained in the original one. -/
theorem half_complexPolydisc_subset {N} (a : Fin N → ℂ) (R : Fin N → ℝ)
    (hR : ∀ i, 0 < R i) :
    complexPolydisc a (fun i => R i / 2) ⊆ complexPolydisc a R := by
  intro z hz i
  exact (hz i).trans (half_lt_self (hR i))




/-- The derivative contour integrand is continuous. -/
theorem continuous_polydiscCauchyDeriv_integrand {N} (f : (Fin N → ℂ) → ℂ)
    (a : Fin N → ℂ) (R : Fin N → ℝ) (hR : ∀ i, 0 < R i)
    (hc : ContinuousOn f (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i))))
    (z : Fin N → ℂ) (hz : z ∈ complexPolydisc a R) :
    Continuous (fun θ => torusJacobian R θ •
      (f (torusMap a R θ) • productCauchyKernelDeriv z (torusMap a R θ))) :=
  (continuous_torusJacobian R).fun_smul ((continuous_on_torus a R hR f hc).fun_smul
    (continuous_productCauchyKernelDeriv_torus a R hR z hz))




/-- A fixed norm estimate transfers uniform convergence to another family of functions. -/
theorem tendstoUniformlyOn_of_norm_bound {X Z E : Type*} [NormedAddCommGroup E]
    (F : ℕ → X → ℂ) (f : X → ℂ) (G : ℕ → Z → E) (g : Z → E)
    S T C (hC : 0 ≤ C)
    (hlim : TendstoUniformlyOn F f atTop S)
    (hbound : ∀ n δ, 0 ≤ δ → (∀ x ∈ S, ‖F n x - f x‖ ≤ δ) →
      ∀ z ∈ T, ‖G n z - g z‖ ≤ C * δ) :
    TendstoUniformlyOn G g atTop T := by
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro ε hε
  have hden : 0 < C + 1 := by positivity
  filter_upwards [hlim (ε / (C + 1)) (div_pos hε hden)] with n hn
  intro z hz
  rw [dist_eq_norm, norm_sub_rev]
  refine (hbound n (ε / (C + 1)) (div_nonneg hε.le hden.le)
    (fun x hx => ?_) z hz).trans_lt ?_
  · simpa only [dist_eq_norm, norm_sub_rev] using (hn x hx).le
  · calc
      C * (ε / (C + 1)) < (C + 1) * (ε / (C + 1)) := by
        apply mul_lt_mul_of_pos_right (lt_add_one C) (div_pos hε hden)
      _ = ε := by field_simp




/-- A normalized Cauchy representation supplies the derivative of the represented function. -/
theorem hasFDerivAt_of_polydiscCauchy_eq {N} (f : (Fin N → ℂ) → ℂ)
    (a : Fin N → ℂ) (R : Fin N → ℝ) (hR : ∀ i, 0 < R i)
    (hc : ContinuousOn f (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i))))
    (heq : EqOn (polydiscCauchy f a R) (fun v => (2 * Real.pi * I : ℂ) ^ N * f v)
      (complexPolydisc a (fun i => R i / 2)))
    z (hz : z ∈ complexPolydisc a (fun i => R i / 2)) :
    HasFDerivAt f (((2 * Real.pi * I : ℂ) ^ N)⁻¹ • polydiscCauchyDeriv f a R z) z := by
  have hasFDerivAt_polydiscCauchy (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ θ, ‖f (torusMap a R θ)‖ ≤ M) (z : Fin N → ℂ) (hz : z ∈ complexPolydisc a (fun i => R i / 2)) : HasFDerivAt (polydiscCauchy f a R) (polydiscCauchyDeriv f a R z) z := by
    have hasFDerivAt_productCauchyKernel {N} (z : Fin N → ℂ) (w : Fin N → ℂ) (hne : ∀ i, w i - z i ≠ 0) : HasFDerivAt (fun v => productCauchyKernel v w) (productCauchyKernelDeriv z w) z := by
      have hasFDerivAt_inverse_coordinate (i : Fin N) (hne : w i - z i ≠ 0) : HasFDerivAt (fun v : Fin N → ℂ => (w i - v i)⁻¹) (((w i - z i) ^ 2)⁻¹ • (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ)) z := by
        simpa only [Function.comp_def, ContinuousLinearMap.proj_apply,
          neg_smul, smul_neg, neg_neg] using ((hasDerivAt_inv hne).comp_hasFDerivAt z (((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := z)).const_sub (w i)))
      simpa only [productCauchyKernel, productCauchyKernelDeriv, Finset.prod_apply] using (HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => hasFDerivAt_inverse_coordinate i (hne i)))
    let b : Fin N → ℝ := fun i => (R i / 2)⁻¹
    let B := (∏ i, |R i|) * M * productCauchyDerivBound b
    let F : (Fin N → ℂ) → (Fin N → ℝ) → ℂ := fun v θ =>
      torusJacobian R θ * (f (torusMap a R θ) * productCauchyKernel v (torusMap a R θ))
    let F' : (Fin N → ℂ) → (Fin N → ℝ) → ((Fin N → ℂ) →L[ℂ] ℂ) := fun v θ =>
      torusJacobian R θ • (f (torusMap a R θ) • productCauchyKernelDeriv v (torusMap a R θ))
    have hfcont := continuous_on_torus a R hR f hc
    have hF : ∀ v ∈ complexPolydisc a (fun i => R i / 2), Continuous (F v) := by
      intro v hv
      exact (continuous_torusJacobian R).mul (hfcont.mul
        (continuous_productCauchyKernel_torus a R hR v
          (half_complexPolydisc_subset a R hR hv)))
    have hdom : ∀ θ v, v ∈ complexPolydisc a (fun i => R i / 2) → ‖F' v θ‖ ≤ B := by
      intro θ v hv
      dsimp [F', B]
      rw [norm_smul, norm_smul, norm_torusJacobian]
      calc
        _ ≤ (∏ i, |R i|) * (M * productCauchyDerivBound b) := by
          apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => abs_nonneg _)
          exact mul_le_mul (hbound θ)
            (norm_productCauchyKernelDeriv_le v (torusMap a R θ) b (fun i => inv_nonneg.mpr (half_pos (hR i)).le)
              (inverse_coordinate_bound_on_torus a R hR v hv θ))
            (norm_nonneg _) hM
        _ = _ := (mul_assoc _ _ _).symm
    exact ((differentiableOn_integral_polydisc (volume.restrict (angleCube N)) a (fun i => R i / 2) (fun i => half_pos (hR i)) F F' (fun _ => B) (fun v hv => (hF v hv).aestronglyMeasurable) (fun v hv => ((show ∀ v ∈ complexPolydisc a (fun i => R i / 2), Continuous (F' v) by intro v hv; exact (continuous_torusJacobian R).fun_smul (hfcont.fun_smul (continuous_productCauchyKernelDeriv_torus a R hR v (half_complexPolydisc_subset a R hR hv)))) v hv).aestronglyMeasurable) ((hF a (mem_complexPolydisc_center a _ (fun i => half_pos (hR i)))).continuousOn.integrableOn_compact isCompact_Icc) (integrable_const B) (Eventually.of_forall fun θ v hv => hdom θ v hv) (Eventually.of_forall fun θ v hv => (show ∀ θ v, v ∈ complexPolydisc a (fun i => R i / 2) → HasFDerivAt (fun w => F w θ) (F' v θ) v by intro θ v hv; exact ((hasFDerivAt_productCauchyKernel v (torusMap a R θ) (coordinate_sub_ne_zero_on_torus a R hR v (half_complexPolydisc_subset a R hR hv) θ)).const_mul (f (torusMap a R θ))).const_mul (torusJacobian R θ)) θ v hv)).2 z hz).2.2
  obtain ⟨M, hM, hb⟩ := (show ∃ M > 0, ∀ θ, ‖f (torusMap a R θ)‖ ≤ M by obtain ⟨M, hM, hb⟩ := ((isCompact_closed_pi a R).image_of_continuousOn hc).isBounded.exists_pos_norm_le; exact ⟨M, hM, fun θ => hb _ (mem_image_of_mem f (torusMap_mem_closed_pi a R (fun i => (hR i).le) θ))⟩)
  apply ((hasFDerivAt_polydiscCauchy M hM.le hb z hz).const_mul (((2 * Real.pi * I : ℂ) ^ N)⁻¹)).congr_of_eventuallyEq
  filter_upwards [(isOpen_complexPolydisc a (fun i => R i / 2)).mem_nhds hz] with v hv
  rw [heq hv, ← mul_assoc, inv_mul_cancel₀ ((show (2 * Real.pi * I : ℂ) ^ N ≠ 0 by apply pow_ne_zero; exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)), one_mul]



/-- Proof of `DOZZ.differentiableOn_of_tendstoLocallyUniformlyOn_fin`: the locally uniform limit is
jointly holomorphic, with locally uniform convergence of its full complex Fréchet derivative. -/
theorem differentiableOn_of_tendstoLocallyUniformlyOn_fin {N}
    U (hU : IsOpen U)
    (F : ℕ → (Fin N → ℂ) → ℂ) (f : (Fin N → ℂ) → ℂ)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hlim : TendstoLocallyUniformlyOn F f atTop U) :
    DifferentiableOn ℂ f U ∧
      TendstoLocallyUniformlyOn (fun n => fderiv ℂ (F n)) (fderiv ℂ f) atTop U := by
  have weierstrass_on_polydisc (a : Fin N → ℂ) (R : Fin N → ℝ) (hR : ∀ i, 0 < R i) (hclosed : Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)) ⊆ U) (hf : ContinuousOn f (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)))) (hlim : TendstoUniformlyOn F f atTop (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)))) : DifferentiableOn ℂ f (complexPolydisc a (fun i => R i / 2)) ∧ TendstoUniformlyOn (fun n => fderiv ℂ (F n)) (fderiv ℂ f) atTop (complexPolydisc a (fun i => R i / 2)) := by
    have polydiscCauchy_eq_of_uniform_limit : EqOn (polydiscCauchy f a R) (fun v => (2 * Real.pi * I : ℂ) ^ N * f v) (complexPolydisc a (fun i => R i / 2)) := by
      have tendstoUniformlyOn_polydiscCauchy (hF : ∀ n, ContinuousOn (F n) (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)))) (hf : ContinuousOn f (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)))) (hlim : TendstoUniformlyOn F f atTop (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)))) : TendstoUniformlyOn (fun n => polydiscCauchy (F n) a R) (polydiscCauchy f a R) atTop (complexPolydisc a (fun i => R i / 2)) := by
        have polydiscCauchy_sub {N} (f : (Fin N → ℂ) → ℂ) (g : (Fin N → ℂ) → ℂ) (a : Fin N → ℂ) (R : Fin N → ℝ) (hR : ∀ i, 0 < R i) (hf : ContinuousOn f (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)))) (hg : ContinuousOn g (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)))) z (hz : z ∈ complexPolydisc a R) : polydiscCauchy (fun w => f w - g w) a R z = polydiscCauchy f a R z - polydiscCauchy g a R z := by
          unfold polydiscCauchy
          rw [(show (fun w => (f w - g w) * productCauchyKernel z w) = (fun w => f w * productCauchyKernel z w) - (fun w => g w * productCauchyKernel z w) by ext w; exact sub_mul _ _ _)]
          exact torusIntegral_sub (torusIntegrable_productCauchyKernel a R hR f hf z hz)
            (torusIntegrable_productCauchyKernel a R hR g hg z hz)
        have norm_polydiscCauchy_le {N} (f : (Fin N → ℂ) → ℂ) (a : Fin N → ℂ) (R : Fin N → ℝ) (hR : ∀ i, 0 < R i) M (hM : 0 ≤ M) (hb : ∀ θ, ‖f (torusMap a R θ)‖ ≤ M) z (hz : z ∈ complexPolydisc a (fun i => R i / 2)) : ‖polydiscCauchy f a R z‖ ≤ ((2 * Real.pi) ^ N * ∏ i, |R i|) * (M * ∏ i, (R i / 2)⁻¹) := by
          apply norm_torusIntegral_le_of_norm_le_const
          intro θ
          rw [norm_mul]
          exact mul_le_mul (hb θ)
            ((fun w b _hb hbound => by rw [productCauchyKernel, norm_prod]; exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hbound i)) (torusMap a R θ) (fun i => (R i / 2)⁻¹)
              (fun i => inv_nonneg.mpr (half_pos (hR i)).le) (inverse_coordinate_bound_on_torus a R hR z hz θ))
            (norm_nonneg _) hM
        let C := ((2 * Real.pi) ^ N * ∏ i, |R i|) * (∏ i, (R i / 2)⁻¹)
        apply tendstoUniformlyOn_of_norm_bound F f _ _ _ _ C (mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (Finset.prod_nonneg fun i _ => abs_nonneg _)) (Finset.prod_nonneg fun i _ => inv_nonneg.mpr (half_pos (hR i)).le)) hlim
        intro n δ hδ hb z hz
        rw [← polydiscCauchy_sub (F n) f a R hR (hF n) hf z
          (half_complexPolydisc_subset a R hR hz)]
        dsimp [C]
        convert (norm_polydiscCauchy_le (fun w => F n w - f w) a R hR δ hδ (fun θ => hb _ (torusMap_mem_closed_pi a R (fun i => (hR i).le) θ)) z hz) using 1
        ring
      intro z hz
      have hcontour := (tendstoUniformlyOn_polydiscCauchy
        (fun n => (hF n).continuousOn.mono hclosed) hf hlim).tendsto_at hz
      rw [(show (fun n => polydiscCauchy (F n) a R z) = (fun n => (2 * Real.pi * I : ℂ) ^ N * F n z) by funext n; exact torusIntegral_productCauchyKernel U hU (F n) (hF n) a R hR hclosed z (half_complexPolydisc_subset a R hR hz))] at hcontour
      exact tendsto_nhds_unique hcontour ((hlim.tendsto_at (complexPolydisc_subset_closed_pi a R (half_complexPolydisc_subset a R hR hz))).const_mul ((2 * Real.pi * I : ℂ) ^ N))
    have tendstoUniformlyOn_polydiscCauchyDeriv (hF : ∀ n, ContinuousOn (F n) (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)))) (hf : ContinuousOn f (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)))) (hlim : TendstoUniformlyOn F f atTop (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)))) : TendstoUniformlyOn (fun n => polydiscCauchyDeriv (F n) a R) (polydiscCauchyDeriv f a R) atTop (complexPolydisc a (fun i => R i / 2)) := by
      have polydiscCauchyDeriv_sub {N} (f : (Fin N → ℂ) → ℂ) (g : (Fin N → ℂ) → ℂ) (a : Fin N → ℂ) (R : Fin N → ℝ) (hR : ∀ i, 0 < R i) (hf : ContinuousOn f (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)))) (hg : ContinuousOn g (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)))) z (hz : z ∈ complexPolydisc a R) : polydiscCauchyDeriv (fun w => f w - g w) a R z = polydiscCauchyDeriv f a R z - polydiscCauchyDeriv g a R z := by
        unfold polydiscCauchyDeriv
        have heq : (fun θ => torusJacobian R θ • ((f (torusMap a R θ) - g (torusMap a R θ)) •
            productCauchyKernelDeriv z (torusMap a R θ))) =
            (fun θ => torusJacobian R θ • (f (torusMap a R θ) • productCauchyKernelDeriv z (torusMap a R θ))) -
            (fun θ => torusJacobian R θ • (g (torusMap a R θ) • productCauchyKernelDeriv z (torusMap a R θ))) := by
          funext θ
          ext x
          change torusJacobian R θ * ((f (torusMap a R θ) - g (torusMap a R θ)) *
            productCauchyKernelDeriv z (torusMap a R θ) x) =
            torusJacobian R θ * (f (torusMap a R θ) * productCauchyKernelDeriv z (torusMap a R θ) x) -
            torusJacobian R θ * (g (torusMap a R θ) * productCauchyKernelDeriv z (torusMap a R θ) x)
          ring
        rw [heq]
        exact integral_sub
          ((continuous_polydiscCauchyDeriv_integrand f a R hR hf z hz).continuousOn.integrableOn_compact
            isCompact_Icc)
          ((continuous_polydiscCauchyDeriv_integrand g a R hR hg z hz).continuousOn.integrableOn_compact
            isCompact_Icc)
      have norm_polydiscCauchyDeriv_le {N} (f : (Fin N → ℂ) → ℂ) (a : Fin N → ℂ) (R : Fin N → ℝ) (hR : ∀ i, 0 < R i) M (hM : 0 ≤ M) (hb : ∀ θ, ‖f (torusMap a R θ)‖ ≤ M) z (hz : z ∈ complexPolydisc a (fun i => R i / 2)) : ‖polydiscCauchyDeriv f a R z‖ ≤ (volume (angleCube N)).toReal * ((∏ i, |R i|) * (M * productCauchyDerivBound (fun i => (R i / 2)⁻¹))) := by
        unfold polydiscCauchyDeriv
        rw [mul_comm (volume (angleCube N)).toReal]
        rw [← (show (volume.restrict (angleCube N)).real Set.univ = (volume (angleCube N)).toReal by simp [Measure.real])]
        apply norm_integral_le_of_norm_le_const
        exact Eventually.of_forall fun θ => by
          rw [norm_smul, norm_smul, norm_torusJacobian]
          apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => abs_nonneg _)
          exact mul_le_mul (hb θ)
            (norm_productCauchyKernelDeriv_le z (torusMap a R θ) (fun i => (R i / 2)⁻¹)
              (fun i => inv_nonneg.mpr (half_pos (hR i)).le) (inverse_coordinate_bound_on_torus a R hR z hz θ))
            (norm_nonneg _) hM
      have productCauchyDerivBound_nonneg {N} (b : Fin N → ℝ) (hb : ∀ i, 0 ≤ b i) : 0 ≤ productCauchyDerivBound b := by
        unfold productCauchyDerivBound
        exact Finset.sum_nonneg fun i _ =>
          mul_nonneg (Finset.prod_nonneg fun j _ => hb j) (sq_nonneg _)
      let C := (volume (angleCube N)).toReal * ((∏ i, |R i|) *
        productCauchyDerivBound (fun i => (R i / 2)⁻¹))
      apply tendstoUniformlyOn_of_norm_bound F f _ _ _ _ C (mul_nonneg ENNReal.toReal_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => abs_nonneg _) (productCauchyDerivBound_nonneg _ fun i => inv_nonneg.mpr (half_pos (hR i)).le))) hlim
      intro n δ hδ hb z hz
      rw [← polydiscCauchyDeriv_sub (F n) f a R hR (hF n) hf z
        (half_complexPolydisc_subset a R hR hz)]
      dsimp [C]
      convert (norm_polydiscCauchyDeriv_le (fun w => F n w - f w) a R hR δ hδ (fun θ => hb _ (torusMap_mem_closed_pi a R (fun i => (hR i).le) θ)) z hz) using 1
      ring
    have hd := hasFDerivAt_of_polydiscCauchy_eq f a R hR hf (polydiscCauchy_eq_of_uniform_limit)
    have hdF : ∀ n z, z ∈ complexPolydisc a (fun i => R i / 2) →
        HasFDerivAt (F n) (((2 * Real.pi * I : ℂ) ^ N)⁻¹ • polydiscCauchyDeriv (F n) a R z) z := by
      intro n
      apply hasFDerivAt_of_polydiscCauchy_eq (F n) a R hR ((hF n).continuousOn.mono hclosed)
      intro z hz
      exact torusIntegral_productCauchyKernel U hU (F n) (hF n) a R hR hclosed z
        (half_complexPolydisc_subset a R hR hz)
    refine ⟨fun z hz => (hd z hz).differentiableAt.differentiableWithinAt, ?_⟩
    exact (((uniformContinuous_const_smul (((2 * Real.pi * I : ℂ) ^ N)⁻¹)).comp_tendstoUniformlyOn (tendstoUniformlyOn_polydiscCauchyDeriv (fun n => (hF n).continuousOn.mono hclosed) hf hlim)).congr_right (fun z hz => (hd z hz).fderiv.symm)).congr
      (Eventually.of_forall fun n z hz => (hdF n z hz).fderiv.symm)
  have hlocal : ∀ a ∈ U, ∃ R : Fin N → ℝ, (∀ i, 0 < R i) ∧
      DifferentiableOn ℂ f (complexPolydisc a (fun i => R i / 2)) ∧
      TendstoUniformlyOn (fun n => fderiv ℂ (F n)) (fderiv ℂ f) atTop
        (complexPolydisc a (fun i => R i / 2)) := by
    intro a ha
    obtain ⟨R, hR, hclosed, _⟩ := exists_closed_polydisc_subset_open U hU a ha
    exact ⟨R, hR, weierstrass_on_polydisc a R hR hclosed ((hlim.continuousOn (Eventually.of_forall fun n => (hF n).continuousOn).frequently).mono hclosed) ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closed_pi a R)).mp (hlim.mono hclosed))⟩
  constructor
  · intro a ha
    obtain ⟨R, hR, hd, _⟩ := hlocal a ha
    exact (hd.differentiableAt ((isOpen_complexPolydisc a _).mem_nhds
      (mem_complexPolydisc_center a _ (fun i => half_pos (hR i))))).differentiableWithinAt
  · rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε a ha
    obtain ⟨R, hR, _, hder⟩ := hlocal a ha
    refine ⟨complexPolydisc a (fun i => R i / 2),
      mem_nhdsWithin_of_mem_nhds ((isOpen_complexPolydisc a _).mem_nhds
        (mem_complexPolydisc_center a _ (fun i => half_pos (hR i)))), ?_⟩
    exact Metric.tendstoUniformlyOn_iff.mp hder ε hε

end DOZZ.Proofs
