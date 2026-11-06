module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.ConnectionBeta
import Mathlib.Tactic

/-!
# The finite part of the connection integral

Integration of a vanishing flux evaluates the subtracted kernel by a convergent Beta integral.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Set MeasureTheory Filter
open scoped Topology

/-- Flux for the finite part at the singular endpoint. -/
def connectionFlux (c t : ℝ) : ℝ :=
  t ^ c * (1 + t) ^ (1 / 3 - c) - t ^ (1 / 3 : ℝ)

variable (c : ℝ)

/-- The flux has a continuous zero endpoint extension. -/
theorem continuousAt_connectionFlux_zero  (hc : 0 < c) :
    ContinuousAt (connectionFlux c) 0 := ((Real.continuousAt_rpow_const 0 c (Or.inr hc.le)).mul
    ((continuousAt_const.add continuousAt_id).rpow_const
      (Or.inl (by norm_num)))).sub
    (Real.continuousAt_rpow_const 0 _ (Or.inr (by norm_num)))

/-- The flux vanishes at the lower endpoint. -/
theorem connectionFlux_zero  (hc : 0 < c) : connectionFlux c 0 = 0 := by
  simp [connectionFlux, Real.zero_rpow hc.ne']

/-- Factoring the flux at infinity. -/
theorem connectionFlux_factor (c t : ℝ) (ht : 0 < t) :
    connectionFlux c t = t ^ (1 / 3 : ℝ) *
      ((1 + t⁻¹) ^ (1 / 3 - c) - 1) := by
  have he : 1 + t = t * (1 + t⁻¹) := by grind
  rw [connectionFlux, he, Real.mul_rpow ht.le (by positivity),
    ← mul_assoc, ← Real.rpow_add ht]
  ring

/-- The flux vanishes at infinity. -/
theorem tendsto_connectionFlux_atTop  (hc : 0 < c) (hc1 : c < 1 / 3) :
    Tendsto (connectionFlux c) atTop (𝓝 0) := by
  have hl : Tendsto (fun t : ℝ => (1 / 3 - c) * t ^ (-(2 / 3 : ℝ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num)).const_mul
      _
  apply squeeze_zero' _ _ hl
  · filter_upwards [Ioi_mem_atTop (0)] with t ht
    rw [connectionFlux_factor c t ht]
    apply mul_nonneg (Real.rpow_nonneg ht.le _)
    exact sub_nonneg.mpr (Real.one_le_rpow (by linarith [inv_pos.mpr ht])
      (sub_pos.mpr hc1).le)
  · filter_upwards [Ioi_mem_atTop (0)] with t ht
    rw [connectionFlux_factor c t ht]
    have h := mul_le_mul_of_nonneg_left
      (one_add_rpow_sub_one_le (1 / 3 - c) t⁻¹ (sub_pos.mpr hc1).le
        (by linarith) (inv_pos.mpr ht).le) (Real.rpow_nonneg ht.le (1 / 3))
    have he : t ^ (1 / 3 : ℝ) * t⁻¹ = t ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
      ring
    exact h.trans_eq (by grind)

/-- Flux derivative in terms of integrable kernels. -/
theorem hasDerivAt_connectionFlux (c t : ℝ) (ht : 0 < t) :
    HasDerivAt (connectionFlux c)
      ((1 / 3 : ℝ) * connectionKernel c t +
        (c - 1 / 3) * (t ^ (c - 1) * (1 + t) ^ (-c - 2 / 3))) t := by
  have hp : 0 < 1 + t := add_pos zero_lt_one ht
  have hd := (((hasDerivAt_id t).rpow_const (p := c) (Or.inl ht.ne')).mul
    (((hasDerivAt_const t 1).add (hasDerivAt_id t)).rpow_const
      (p := 1 / 3 - c) (Or.inl hp.ne'))).sub
    ((hasDerivAt_id t).rpow_const (p := (1 / 3)) (Or.inl ht.ne'))
  convert hd using 1
  · rfl
  · dsimp only [Pi.add_apply, id_eq]
    rw [connectionKernel]
    have he : (1 + t) ^ (1 / 3 - c) =
        (1 + t) * (1 + t) ^ (-c - 2 / 3) := by
      conv_rhs => lhs; rw [← Real.rpow_one (1 + t)]
      rw [← Real.rpow_add hp]
      ring
    have he2 : t ^ c = t * t ^ (c - 1) := by
      conv_rhs => lhs; rw [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      ring
    grind

/-- Exact evaluation of the renormalized connection kernel. -/
theorem integral_connectionKernel_beta  (hc : 0 < c) (hc1 : c < 1 / 3) :
    (∫ t in Ioi (0 : ℝ), connectionKernel c t) =
      (1 - 3 * c) *
        (Real.Gamma c * Real.Gamma (2 / 3) / Real.Gamma (c + 2 / 3)) := by
  have hk := integrableOn_connectionKernel c hc hc1
  have hb := integrableOn_betaHalf c (2 / 3) hc (by norm_num)
  have hf := integral_Ioi_of_hasDerivAt_of_tendsto
    (continuousAt_connectionFlux_zero c hc).continuousWithinAt
    (fun t ht => hasDerivAt_connectionFlux c t ht)
    ((hk.const_mul _).add (hb.const_mul _))
    (tendsto_connectionFlux_atTop c hc hc1)
  rw [connectionFlux_zero c hc] at hf
  have hs := integral_add (hk.const_mul (1 / 3)) (hb.const_mul (c - 1 / 3))
  rw [hs, integral_const_mul, integral_const_mul, integral_betaHalf c _ hc
    (by norm_num)] at hf
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
