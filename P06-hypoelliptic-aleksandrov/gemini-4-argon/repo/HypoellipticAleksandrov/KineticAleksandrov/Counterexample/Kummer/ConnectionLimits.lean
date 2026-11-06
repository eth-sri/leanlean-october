module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.ConnectionFlux
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsMoments
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Endpoint limits of the renormalized integral

Dominated convergence applies to the genuinely integrable subtracted kernel.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Set Filter MeasureTheory
open scoped Topology

/- Laplace transform of the finite-part connection kernel. -/
def connectionIntegral (c z : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * connectionKernel c t

/- Integrability of the transformed finite-part kernel for nonnegative Laplace parameter. -/
theorem integrableOn_connectionLaplace (c z : ℝ) (hc : 0 < c) (hc1 : c < 1 / 3)
    (hz : 0 ≤ z) :
    IntegrableOn (fun t => Real.exp (-(z * t)) * connectionKernel c t) (Ioi 0) := by
  apply (integrableOn_connectionKernel c hc hc1).mono'
  · exact ContinuousOn.aestronglyMeasurable
      (((continuous_const.mul continuous_id).neg.rexp.continuousOn).mul
        (continuousOn_connectionKernel c)) measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (connectionKernel_nonneg c t hc1.le ht)]
    exact mul_le_of_le_one_left (connectionKernel_nonneg c t hc1.le ht)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hz ht.le)))

/- The finite-part transform tends to its exact integral at the lower endpoint. -/
theorem tendsto_connectionIntegral_zero (c : ℝ) (hc : 0 < c) (hc1 : c < 1 / 3) :
    Tendsto (connectionIntegral c) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0 : ℝ), connectionKernel c t)) := by
  apply tendsto_integral_filter_of_dominated_convergence (connectionKernel c)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact (integrableOn_connectionLaplace c z hc hc1 hz.le).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (connectionKernel_nonneg c t hc1.le ht)]
    exact mul_le_of_le_one_left (connectionKernel_nonneg c t hc1.le ht)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hz.le ht.le)))
  · exact integrableOn_connectionKernel c hc hc1
  · filter_upwards with t
    have h : Tendsto (fun z : ℝ => Real.exp (-(z * t))) (𝓝[>] 0) (𝓝 1) := by
      have hc : ContinuousAt (fun z : ℝ => Real.exp (-(z * t))) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h.mul_const (connectionKernel c t)

/- Exact decomposition of the positive integral into its singular term and finite part. -/
theorem UIr_connection_decomposition (c : Pos) (hc1 : c.1 < 1 / 3)
    (z : ℝ) (hz : 0 < z) :
    UIr c (4 / 3) z = (Real.Gamma c.1)⁻¹ *
      (z ^ (-(1 / 3 : ℝ)) * Real.Gamma (1 / 3) + connectionIntegral c.1 z) := by
  have hk := integrableOn_connectionLaplace c.1 z c.2 hc1 hz.le
  have hg := integrableOn_gammaKernel (1 / 3 : ℝ) z (by norm_num) hz
  have he : ∀ t ∈ Ioi (0 : ℝ), laplaceKernel c (4 / 3) z t =
      Real.exp (-(z * t)) * t ^ ((1 / 3 : ℝ) - 1) +
        Real.exp (-(z * t)) * connectionKernel c.1 t := by
    intro t ht
    dsimp [laplaceKernel, laplaceKernelReal, connectionKernel]
    rw [show (4 / 3 : ℝ) - c.1 - 1 = 1 / 3 - c.1 by ring,
      show (1 / 3 : ℝ) - 1 = -(2 / 3 : ℝ) by ring]
    ring
  rw [UIr, setIntegral_congr_fun measurableSet_Ioi he, integral_add hg hk,
    integral_gammaKernel (1 / 3 : ℝ) z (by norm_num) hz]
  rfl

/- The finite-part constant in the negative-parameter Gamma normalization. -/
theorem UNr_connection_decomposition (a : NegThird) (z : ℝ) (hz : 0 < z) :
    UNr a z = Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3) +
      z ^ (1 / 3 : ℝ) * (Real.Gamma (a.1 + 1 / 3))⁻¹ *
        connectionIntegral (a.1 + 1 / 3) z := by
  rw [UNr, UIr_connection_decomposition _ (by linarith [a.2.2]) z hz]
  have he : z ^ (1 / 3 : ℝ) * z ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hz, add_neg_cancel, Real.rpow_zero]
  calc
    _ = (Real.Gamma (a.1 + 1 / 3))⁻¹ * Real.Gamma (1 / 3) *
        (z ^ (1 / 3 : ℝ) * z ^ (-(1 / 3 : ℝ))) +
        z ^ (1 / 3 : ℝ) * (Real.Gamma (a.1 + 1 / 3))⁻¹ *
          connectionIntegral (a.1 + 1 / 3) z := by ring
    _ = _ := by rw [he]; ring

/- The limiting constant of the negative-parameter solution at zero. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
