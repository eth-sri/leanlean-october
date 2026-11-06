module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaFourierCarrierBounds
public import TaoTrudgianYang2025.BetaTaylorJets
public import TaoTrudgianYang2025.BetaFourierModes
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Uniform second derivatives of the original normalized Poisson kernel

The phase derivatives come from the original model on (1,2). Outside
the cutoff's closed support the actual kernel is locally zero.
-/

noncomputable section

open Complex Set Filter Expdb
open scoped ContDiff FourierTransform Topology

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

theorem norm_modelPhaseBufferedKernel_le_one (l r η T N x : ℝ) (F : ℝ → ℝ) :
    ‖modelPhaseWeightedKernel (modelPhaseBufferedCutoff l r η) F T N x‖ ≤ 1 := by
  pm_1486 modelPhaseWeightedKernel

theorem modelPhaseBufferedKernel_uniform_second_derivative
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ T : ℝ), δ ≤ 1 →
        IsApproximateModelPhaseFunction F σ 1 δ →
        ∀ u : ℝ,
          ‖iteratedDeriv 2 (modelPhaseWeightedKernel
            (modelPhaseBufferedCutoff l r η) F T 1) u‖ ≤ C*(η⁻¹)^2*(1+|T|)^2 := by
  obtain ⟨M,hM,hcut⟩ := modelPhaseBufferedCutoff_uniform_c2
  let K := 1+modelPhaseJetCoefficient σ 0+modelPhaseJetCoefficient σ 1
  let D := (2*Real.pi)^2*K^2+2*Real.pi*K+1
  have hK : 1 ≤ K := by
    dsimp [K]
    linarith [modelPhaseJetCoefficient_nonneg σ 0,modelPhaseJetCoefficient_nonneg σ 1]
  have hD : 1 ≤ D := by
    have hK₀ : 0 ≤ K := by linarith
    dsimp [D]
    pm_998
  pm_1642
  intro l r η hl hr hη hη₁ F δ T hδ hF u
  let χ := modelPhaseBufferedCutoff l r η
  have heq : modelPhaseWeightedKernel χ F T 1 =
      fun x => (χ x : ℂ)*(𝐞 (T*F x) : ℂ) := by
    funext x
    simp only [modelPhaseWeightedKernel,div_one]
  by_cases hu : u ∈ tsupport χ
  · have hu' : u ∈ Ioo (1 : ℝ) 2 :=
      modelPhaseBufferedCutoff_tsupport_model hη hl hr hu
    have hphase := intervalC2Bound_fourierChar_of_derivative_bounds (a := u) (b := u) hK
      (F := F) (fun x hx => by
        pm_1641
        exact (approximateModelPhase_contDiffAt hF hu').of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (fun x hx => by
        pm_1641
        have hb := approximateModelPhase_iteratedDeriv_abs_le hσ hF hu' 0 (by norm_num)
        simp only [zero_add,iteratedDeriv_one] at hb
        dsimp [K]
        linarith [modelPhaseJetCoefficient_nonneg σ 1])
      (fun x hx => by
        pm_1641
        have hb := approximateModelPhase_iteratedDeriv_abs_le hσ hF hu' 1 le_rfl
        dsimp [K]
        linarith [modelPhaseJetCoefficient_nonneg σ 0]) T
    pm_1640
    have hp := ((hcut l r η u u hη).mono le_rfl hR₁).mul
      (hphase.mono le_rfl hR₂)
    pm_5636
  · have hz : modelPhaseWeightedKernel χ F T 1 =ᶠ[𝓝 u] fun _ => (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hu] with x hx
      pm_382 modelPhaseWeightedKernel div_one hx Pi.zero_apply Complex.ofReal_zero zero_mul
    rw [hz.iteratedDeriv_eq 2]
    simp only [iteratedDeriv_const,show (2 : ℕ) ≠ 0 by norm_num,ite_false,norm_zero]
    pm_255 hM₀ M hD₀ D
    positivity

end TaoTrudgianYang2025
