module

public import PDEFoundation.Measure.FiniteVectorConvergence
public import PDEFoundation.Measure.LpTendsto
public import PDEFoundation.Measure.NormalizedLpTendsto
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Convergence
public import PDEFoundation.Sobolev.W1p.EuclideanGradient
public import PDEFoundation.Sobolev.W1p.Mean
public import PDEFoundation.Sobolev.W1p.Smooth
import Batteries.Tactic.Alias
import PDEFoundation.Sobolev.W1p.EuclideanGradient
public import PDEFoundation.Calculus.RegularityOrder




/-!
# Smooth density on bounded open convex domains

This file packages convex approximation as a sequence of smooth
`W1pFunction`s and records its exact convergence properties for every finite
exponent `p ≥ 1`.

The native gradient remains `Vec d`-valued. Coordinatewise convergence is
exported for compatibility, while the public gradient norm is the exact
Euclidean norm obtained through the internal Hilbert lift. Finite coordinate
sums occur only inside the convergence majorant supplied by
`PDEFoundation.Measure.FiniteVectorConvergence`.

Centering is performed against `normalizedVolumeOn U`, so convergence of
arithmetic means and centered values includes the endpoint `p = 1`.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

variable (hU : IsOpenBoundedConvexDomain U) (hp : 1 ≤ p)

variable (u : W1pFunction U p) (x0 : Vec d) {r : ℝ} (hr : 0 < r) (n : ℕ)

/-- The smooth `W^{1,p}` representative obtained from the standard convex
approximation kernel and scale. -/
noncomputable def convexApproxSmoothW1p
      : W1pFunction U p :=
  W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU
    ((contDiff_convexApproxSmoothRepresentative
      (U := U)
      (ρ := unitConvexApproxKernel )
      (u := u.toFun) (p := p)
      (x0 := x0) (r := r)
      (ε := unitConvexApproxScale n)
      hU.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel
        )
      hp u.memLp hr
      (unitConvexApproxScale_pos n)).of_le (by simp))

@[simp]
theorem convexApproxSmoothW1p_toFun
      :
    (convexApproxSmoothW1p hU hp u x0 hr n).toFun =
      convexApproxSmoothRepresentative U
        (unitConvexApproxKernel )
        u.toFun x0 r (unitConvexApproxScale n) :=
  rfl

@[simp]
theorem convexApproxSmoothW1p_grad
      :
    (convexApproxSmoothW1p hU hp u x0 hr n).grad =
      classicalGradient
        (convexApproxSmoothRepresentative U
          (unitConvexApproxKernel )
          u.toFun x0 r (unitConvexApproxScale n)) :=
  rfl

@[simp]
theorem convexApproxSmoothW1p_grad_apply
      (x : Vec d) (i : Fin d) :
    (convexApproxSmoothW1p hU hp u x0 hr n).grad x i =
      (fderiv ℝ
        (convexApproxSmoothRepresentative U
          (unitConvexApproxKernel )
          u.toFun x0 r (unitConvexApproxScale n)) x)
        (basisVec i) := by
  rw [convexApproxSmoothW1p_grad,
    classicalGradient_apply]

/-- Every member of the convex approximation sequence has a globally smooth
value representative. -/
theorem contDiff_convexApproxSmoothW1p_toFun
      :
    ContDiff ℝ PDE.smoothOrder
      (convexApproxSmoothW1p hU hp u x0 hr n).toFun := by
  rw [convexApproxSmoothW1p_toFun]
  exact
    contDiff_convexApproxSmoothRepresentative
      hU.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel
        )
      hp u.memLp hr (unitConvexApproxScale_pos n)

section
variable (hpTop : p ≠ ∞) (u : W1pFunction U p) {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)

include hpTop hball
/-- The values of the smooth convex approximants converge in
`L^p(U)` for every finite `p ≥ 1`. -/
theorem tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
      :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x =>
            (convexApproxSmoothW1p hU hp u x0 hr n).toFun x -
              u.toFun x)
          p (volumeOn U))
      atTop (𝓝 0) := (Tendsto.congr'
  (mp_mem (Eventually.mono ((tendsto_order.mp tendsto_unitConvexApproxScale_zero).right 1 zero_lt_one) fun x hn => hn)
    (univ_mem'
      (id fun n hScale =>
        eLpNorm_congr_ae
          (mp_mem (ae_restrict_mem (IsOpenBoundedConvexDomain.measurableSet hU))
            (univ_mem'
              (id fun x hx =>
                Eq.mpr
                  (id
                    (congrArg
                      (fun _a =>
                        convexApproxSmoothing unitConvexApproxKernel u.toFun x0 r (unitConvexApproxScale n) x -
                            u.toFun x =
                          _a - u.toFun x)
                      (convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem hU
                        isConvexApproxKernel_unitConvexApproxKernel hx hball hr (unitConvexApproxScale_pos n) hScale)))
                  (Eq.refl
                    (convexApproxSmoothing unitConvexApproxKernel u.toFun x0 r (unitConvexApproxScale n) x -
                      u.toFun x))))))))
  (tendsto_eLpNorm_sub_zero_unitConvexApproxSequence_of_memLpOn hU hp hpTop u.memLp hball hr))

/-- Every coordinate of the weak gradient of the smooth convex approximants
converges in `L^p(U)`. -/
theorem tendsto_convexApproxSmoothW1p_grad_coord_eLpNorm_sub
      (i : Fin d) :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x =>
            (convexApproxSmoothW1p hU hp u x0 hr n).grad x i -
              u.grad x i)
          p (volumeOn U))
      atTop (𝓝 0) := by
  let ρ  :=
    unitConvexApproxKernel (d := d)
  have hρ : IsConvexApproxKernel ρ := by
    exact isConvexApproxKernel_unitConvexApproxKernel

  have hScaleOne :
      ∀ᶠ n : ℕ in atTop,
        unitConvexApproxScale n < 1 :=
    (((tendsto_order.1
      tendsto_unitConvexApproxScale_zero).2
        1 zero_lt_one).mono fun _ hn => hn)
  have hRaw :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              (1 - unitConvexApproxScale n) *
                  convexApproxSmoothing ρ
                    (fun y => u.grad y i)
                    x0 r (unitConvexApproxScale n) x -
                u.grad x i)
            p (volumeOn U))
        atTop (𝓝 0) := by
    exact tendsto_eLpNorm_sub_zero_one_sub_mul_unitConvexApproxSequence_of_memLpOn
        hU hp hpTop (u.grad_memLp i) hball hr
  have hRepresentative :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              (fderiv ℝ
                (convexApproxSmoothRepresentative U ρ u.toFun
                  x0 r (unitConvexApproxScale n)) x)
                  (basisVec i) -
                u.grad x i)
            p (volumeOn U))
        atTop (𝓝 0) := by
    refine hRaw.congr' ?_
    filter_upwards [hScaleOne] with n hScale
    apply eLpNorm_congr_ae
    have hBridge :=
      ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec



        hU hρ hp u.memLp (u.grad_memLp i)
        (u.hasWeakPartialDerivOn i)
        hball hr (unitConvexApproxScale_pos n) hScale
    filter_upwards
      [hBridge, ae_restrict_mem hU.measurableSet] with
      x hxBridge hxU
    rw [hxBridge]
    rw [
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
        (u := fun y => u.grad y i)
        hU hρ hxU hball hr
        (unitConvexApproxScale_pos n) hScale]
  exact hRepresentative

/-- The exact Euclidean magnitude of the gradient difference converges to
zero in `L^p(U)`. The finite coordinate sum is used only inside the proof as a
majorant. -/
theorem
    tendsto_convexApproxSmoothW1p_grad_euclidean_eLpNorm_sub
      :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x =>
            vecEuclideanNorm
              ((convexApproxSmoothW1p hU hp u x0 hr n).grad x -
                u.grad x))
          p (volumeOn U))
      atTop (𝓝 0) := (tendsto_eLpNorm_vecEuclideanNorm_sub_zero_of_coordinate hp
  (fun n i =>
    AEStronglyMeasurable.sub (MemLp.aestronglyMeasurable (grad_memLp (convexApproxSmoothW1p hU hp u x0 hr n) i))
      (MemLp.aestronglyMeasurable (grad_memLp u i)))
  (tendsto_convexApproxSmoothW1p_grad_coord_eLpNorm_sub hU hp hpTop u hball hr))

/-- Hilbert-lift form of exact Euclidean-gradient difference convergence.
The lift is internal; its norm is definitionally bridged back to
`vecEuclideanNorm`. -/
theorem
    tendsto_convexApproxSmoothW1p_grad_hilbert_eLpNorm_sub
      :
    Tendsto
      (fun n =>
        eLpNorm
          (toHilbertVecField
            (fun x =>
              (convexApproxSmoothW1p hU hp u x0 hr n).grad x -
                u.grad x))
          p (volumeOn U))
      atTop (𝓝 0) := by
  have hEq : ∀ n,
      eLpNorm
          (toHilbertVecField
            (fun x =>
              (convexApproxSmoothW1p hU hp u x0 hr n).grad x - u.grad x))
          p (volumeOn U) =
        eLpNorm
          (fun x => vecEuclideanNorm
            ((convexApproxSmoothW1p hU hp u x0 hr n).grad x - u.grad x))
          p (volumeOn U) :=
    fun n => eLpNorm_toHilbertVecField_eq _ _ _
      (aemeasurable_pi_iff.2 fun i =>
        (((convexApproxSmoothW1p hU hp u x0 hr n).grad_memLp i).aestronglyMeasurable.sub
          (u.grad_memLp i).aestronglyMeasurable).aemeasurable).aestronglyMeasurable
  simpa only [hEq] using
    tendsto_convexApproxSmoothW1p_grad_euclidean_eLpNorm_sub
      hU hp hpTop u hball hr
end





variable (hU : IsOpenBoundedConvexDomain U) (hp : 1 ≤ p) (hpTop : p ≠ ∞) (u : W1pFunction U p) {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)

include hpTop hball in
/-- The `L^p` norms of the Hilbert lifts of the gradients converge. This is
the normed-space bridge used to obtain exact Euclidean-gradient norm
convergence. -/
theorem
    tendsto_convexApproxSmoothW1p_grad_hilbert_eLpNorm
     :
    Tendsto
      (fun n =>
        eLpNorm
          (toHilbertVecField
            (convexApproxSmoothW1p hU hp u x0 hr n).grad)
          p (volumeOn U))
      atTop
      (𝓝
        (eLpNorm (toHilbertVecField u.grad)
          p (volumeOn U))) := (tendsto_eLpNorm_of_tendsto_sub hp
  (fun n =>
    MemLp.aestronglyMeasurable
      (gradMemLpOn_iff_memLp_toHilbertVecField.mp (convexApproxSmoothW1p hU hp u x0 hr n).gradMemLp))
  (MemLp.aestronglyMeasurable (gradMemLpOn_iff_memLp_toHilbertVecField.mp u.gradMemLp))
  (MemLp.eLpNorm_ne_top (gradMemLpOn_iff_memLp_toHilbertVecField.mp u.gradMemLp))
  (Tendsto.congr'
    (Eventually.of_forall fun n =>
      Eq.refl
        ((fun n =>
            eLpNorm (toHilbertVecField fun x => (convexApproxSmoothW1p hU hp u x0 hr n).grad x - u.grad x) p
              (volumeOn U))
          n))
    (tendsto_convexApproxSmoothW1p_grad_hilbert_eLpNorm_sub hU hp hpTop u hball hr)))

include hpTop hball in
/-- The exact Euclidean-gradient `L^p` norms of the smooth approximants
converge to that of the original Sobolev representative. -/
theorem
    tendsto_convexApproxSmoothW1p_grad_euclidean_eLpNorm
     :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x =>
            vecEuclideanNorm
              ((convexApproxSmoothW1p hU hp u x0 hr n).grad x))
          p (volumeOn U))
      atTop
      (𝓝
        (eLpNorm
          (fun x => vecEuclideanNorm (u.grad x))
          p (volumeOn U))) := by
  have hGradMeas : ∀ v : W1pFunction U p,
      AEStronglyMeasurable v.grad (volumeOn U) := fun v =>
    (aemeasurable_pi_iff.2 fun i =>
      (v.grad_memLp i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  simpa only [eLpNorm_toHilbertVecField_eq _ _ _ (hGradMeas _)] using
    tendsto_convexApproxSmoothW1p_grad_hilbert_eLpNorm
      hU hp hpTop u hball hr

variable (hUPos : 0 < volume U)

include hpTop hball hUPos
/-- The normalized exact Euclidean-gradient `L^p` norms converge. The proof
uses the same explicit volume factor on both the approximating and limiting
unnormalized norms. -/
theorem
    tendsto_convexApproxSmoothW1p_grad_euclidean_eLpMeanNorm

     :
    Tendsto
      (fun n =>
        eLpMeanNormOn U p
          (fun x =>
            vecEuclideanNorm
              ((convexApproxSmoothW1p hU hp u x0 hr n).grad x)))
      atTop
      (𝓝
        (eLpMeanNormOn U p
          (fun x => vecEuclideanNorm (u.grad x)))) := by
  let C  :=
    (volume U)⁻¹ ^ (1 / p).toReal
  have hCTop : C ≠ ∞ := by
    dsimp only [C]
    exact
      (ENNReal.rpow_lt_top_of_nonneg
        (by positivity)
        (ENNReal.inv_ne_top.mpr hUPos.ne')).ne
  have hRaw :=
    tendsto_convexApproxSmoothW1p_grad_euclidean_eLpNorm
      hU hp hpTop u hball hr
  have hScaled :=
    ENNReal.Tendsto.const_mul
       hRaw (Or.inr hCTop)
  simpa only [C,
    eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn
      hU.volume_lt_top,
    eLpNormOn] using hScaled

/-- Value convergence with respect to normalized volume. -/
theorem tendsto_convexApproxSmoothW1p_toFun_eLpMeanNorm_sub

     :
    Tendsto
      (fun n =>
        eLpMeanNormOn U p
          ((convexApproxSmoothW1p hU hp u x0 hr n).toFun -
            u.toFun))
      atTop (𝓝 0) := (tendsto_eLpMeanNormOn_sub_zero_of_tendsto_eLpNormOn_sub_zero hUPos (IsOpenBoundedConvexDomain.volume_lt_top hU)
  (id (tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub hU hp hpTop u hball hr)))

/-- Subtracting the arithmetic mean preserves normalized `L^p` convergence
of the smooth convex approximants, including at `p = 1`. -/
theorem
    tendsto_convexApproxSmoothW1p_centered_eLpMeanNorm_sub

     :
    Tendsto
      (fun n =>
        eLpMeanNormOn U p
          (fun x =>
            ((convexApproxSmoothW1p hU hp u x0 hr n).toFun x -
                integralAverage U
                  (convexApproxSmoothW1p hU hp u x0 hr n).toFun) -
              (u.toFun x - integralAverage U u.toFun)))
      atTop (𝓝 0) := by
  let ψ  :=
    convexApproxSmoothW1p hU hp u x0 hr
  let μ  :=
    normalizedVolumeOn U
  let  :=
    hU.isFiniteMeasure_volumeOn
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
      hUPos hU.volume_lt_top
  have hψMeas :
      ∀ n, AEStronglyMeasurable (ψ n).toFun μ := by
    intro n
    simpa only [μ, normalizedVolumeOn] using
      (ψ n).memLp.aestronglyMeasurable.smul_measure
        ((volume U)⁻¹)
  have huIntegrable :
      Integrable u.toFun μ := by
    simpa only [μ, normalizedVolumeOn] using
      (u.memLp.integrable hp).smul_measure
        (ENNReal.inv_ne_top.mpr hUPos.ne')
  have hNormalized :
      Tendsto
        (fun n =>
          eLpNorm ((ψ n).toFun - u.toFun) p μ)
        atTop (𝓝 0) := by
    simpa only [ψ, μ, eLpMeanNormOn] using
      tendsto_convexApproxSmoothW1p_toFun_eLpMeanNorm_sub
        hU hp hpTop u hball hr hUPos
  have hCentered :=
    tendsto_eLpNorm_centered_sub_zero
      hp hpTop hψMeas huIntegrable hNormalized
  simpa only [ψ, μ, eLpMeanNormOn,
    integral_normalizedVolumeOn_eq_integralAverage] using
    hCentered

/-- The normalized `L^p` norms of the centered smooth values converge to the
normalized norm of the centered Sobolev value. -/
theorem tendsto_convexApproxSmoothW1p_centered_eLpMeanNorm

     :
    Tendsto
      (fun n =>
        eLpMeanNormOn U p
          (fun x =>
            (convexApproxSmoothW1p hU hp u x0 hr n).toFun x -
              integralAverage U
                (convexApproxSmoothW1p hU hp u x0 hr n).toFun))
      atTop
      (𝓝
        (eLpMeanNormOn U p
          (fun x =>
            u.toFun x - integralAverage U u.toFun))) := by
  let ψ  :=
    convexApproxSmoothW1p hU hp u x0 hr
  let μ  :=
    normalizedVolumeOn U
  let centered  :=
    fun n x =>
      (ψ n).toFun x -
        integralAverage U (ψ n).toFun
  let centeredLimit  :=
    fun x =>
      u.toFun x - integralAverage U u.toFun
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
      hUPos hU.volume_lt_top
  have hψMeas :
      ∀ n, AEStronglyMeasurable (ψ n).toFun μ := by
    intro n
    simpa only [μ, normalizedVolumeOn] using
      (ψ n).memLp.aestronglyMeasurable.smul_measure
        ((volume U)⁻¹)
  have hCenteredMeas :
      ∀ n, AEStronglyMeasurable (centered n) μ := by
    intro n
    exact
      (hψMeas n).sub aestronglyMeasurable_const
  have huMemNormalized :
      MemLp u.toFun p μ := by
    exact u.memLp.smul_measure
        (ENNReal.inv_ne_top.mpr hUPos.ne')
  have hCenteredLimitMem :
      MemLp centeredLimit p μ := huMemNormalized.sub
        (memLp_const
          (μ := μ) (p := p)
          (c := integralAverage U u.toFun))
  have hCenteredDifference :
      Tendsto
        (fun n =>
          eLpNorm (centered n - centeredLimit) p μ)
        atTop (𝓝 0) := by
    simpa only [ψ, μ, centered, centeredLimit,
      eLpMeanNormOn, Pi.sub_apply] using!
      tendsto_convexApproxSmoothW1p_centered_eLpMeanNorm_sub
        hU hp hpTop u hball hr hUPos
  have hNorm :=
    tendsto_eLpNorm_of_tendsto_sub
      hp hCenteredMeas
      hCenteredLimitMem.aestronglyMeasurable
      hCenteredLimitMem.eLpNorm_ne_top
      hCenteredDifference
  exact hNorm

end W1pFunction

end PDE
