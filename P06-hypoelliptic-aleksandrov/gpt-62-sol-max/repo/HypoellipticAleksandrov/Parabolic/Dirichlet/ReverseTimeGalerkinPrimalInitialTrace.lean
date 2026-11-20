module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalResidualDerivative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertBoundaryPairing

/-!
# Canonical initial trace of the reverse-time Galerkin limit

This module transfers the finite projected initial datum through the common
Galerkin subsequence to the canonical Gelfand initial trace.  The affine time
multiplier is deliberately handled here as a bounded Bochner multiplier: it
does not vanish at the initial endpoint and is therefore not a scalar test.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ lam : ℝ}
variable (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam)
variable (initial : PDE.ScalarLp Ω 2) (U : ReverseTimeL2V P.hΩ (r₁ - r₀)) (phi : ℕ → ℕ)
  (hphi : StrictMono phi) (hclm : P.WeakLimit initial U phi)
  (hdu : HasGelfandWeakTimeDerivative P.hΩ (r₁ - r₀) (sub_pos.mpr P.h₀₁) U (P.residual U))
include hphi hclm

private theorem reverseTimeGalerkinPrimal_initialTrace_pairing (k : ℕ) :
    inner ℝ (valueCLM P.hΩ (galerkinVector P.hΩ k))
        (reverseTimeInitialTrace P.hΩ (r₁ - r₀) (sub_pos.mpr P.h₀₁) U (P.residual U) hdu) =
      inner ℝ (valueCLM P.hΩ (galerkinVector P.hΩ k)) initial := by
  let T := r₁ - r₀
  have hT : 0 < T := sub_pos.mpr P.h₀₁
  let v := galerkinVector P.hΩ k
  let g := P.residual U
  let q (t : ℝ) := 1 - t / T
  let dq (_ : ℝ) := -T⁻¹
  letI := reverseTimeVolume_isFiniteMeasure T
  have hq : MemLp q ∞ (reverseTimeVolume T) := by
    apply memLp_of_bounded (a := 0) (b := 1) ?_ ?_ _
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact ⟨sub_nonneg.mpr ((div_le_one₀ hT).mpr ht.2.le),
        sub_le_self _ (div_nonneg ht.1.le hT.le)⟩
    · exact (continuous_const.sub (continuous_id.div_const T)).aestronglyMeasurable
  have hdq : MemLp dq ∞ (reverseTimeVolume T) := memLp_const _
  have hderiv (t : ℝ) (_ : t ∈ Icc 0 T) : HasDerivWithinAt q (dq t) (Icc 0 T) t := by
    simpa only [q, dq, div_eq_mul_inv, zero_sub, one_mul, Pi.sub_def, id_eq] using
      ((hasDerivAt_const (x := t) (1 : ℝ)).sub ((hasDerivAt_id (x := t)).mul_const T⁻¹)).hasDerivWithinAt (s := Icc 0 T)
  have h0 : q 0 = 1 := by simp [q]
  have hQT : q T = 0 := by simp [q, hT.ne']
  have hlim := ReverseTimeGalerkinProblem.WeakLimit.boundaryPairing P hclm hphi k q dq hq hdq
    hderiv continuousOn_const hQT
  dsimp only at hlim
  rw [h0, mul_one, reverseTimeGelfand_pairing_multiplier_eq_integral P.hΩ U dq hdq v,
    reverseTimeDualPairing_multiplier_eq_integral P.hΩ g q hq v (ae_of_all _ (fun _ => rfl))] at hlim
  have hrep := (reverseTimeHilbertRepresentative_spec P.hΩ T hT U g hdu).1
  have hmass :
      (∫ t, inner ℝ (valueCLM P.hΩ v)
        (Set.IccExtend hT.le (reverseTimeHilbertRepresentative P.hΩ T hT U g hdu) t) * dq t
        ∂reverseTimeVolume T) =
      ∫ t, inner ℝ (valueCLM P.hΩ v) (valueCLM P.hΩ (U t)) * dq t ∂reverseTimeVolume T := by
    refine integral_congr_ae ?_
    filter_upwards [hrep, ae_restrict_mem measurableSet_Ioo] with t hr ht
    rw [Set.IccExtend_of_mem hT.le _ ⟨ht.1.le, ht.2.le⟩, hr ht]
  have htrace := reverseTimeHilbertRepresentative_affine_initial_pairing P.hΩ T hT U g hdu v
  change _ = -(∫ t, g t v * q t ∂reverseTimeVolume T) - _ at htrace
  exact sub_right_inj.mp (htrace.symm.trans (hmass.trans hlim))

/-- A supplied common reverse-time Galerkin subsequence has the prescribed
canonical initial trace. -/
theorem reverseTimeGalerkinPrimal_initialTrace_of_strictMono_tendsto_clm :
    reverseTimeInitialTrace P.hΩ (r₁ - r₀) (sub_pos.mpr P.h₀₁) U
      (P.residual U) hdu = initial := by
  apply scalarLpToH10HilbertGraphDual_injective P.hΩ
  apply DFunLike.ext'
  refine Continuous.ext_on (denseRange_galerkinVector P.hΩ)
    (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _) ?_
  rintro _ ⟨k, rfl⟩
  simpa only [scalarLpToH10HilbertGraphDual_apply] using
    reverseTimeGalerkinPrimal_initialTrace_pairing P initial U phi hphi hclm hdu k

end HypoellipticAleksandrov.Parabolic.Dirichlet
