module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.PoissonShift
public import WeylPort.AFE.PowerWeights

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Actual constant and AFE weights as consumers of corrected Part I -/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory

/-- The actual AFE weights satisfy every regularity hypothesis of corrected Part I, including σ=0. -/
theorem afe_partIRegularity {sigma c a b : ℝ} (hsigma : 0 ≤ sigma) (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) : PartIRegularity (afePhase c) (afeWeight sigma) a b := by
  have hx (x : ℝ) (hxi : x ∈ Set.Icc a b) : 0 < x := ha.trans_le hxi.1
  have hdf (x : ℝ) (hxi : x ∈ Set.Icc a b) : deriv (afePhase c) x = c / x :=
    (afePhase_hasDerivAt c (hx x hxi)).deriv
  have hdg (x : ℝ) (hxi : x ∈ Set.Icc a b) :
      deriv (afeWeight sigma) x = -sigma * x ^ (-sigma - 1) :=
    (afeWeight_hasDerivAt sigma (hx x hxi)).deriv
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hxi => hx x hxi
  refine ⟨hab, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hxi
    exact (afePhase_hasDerivAt c (hx x hxi)).differentiableAt
  · have hd : ContinuousOn (fun x => c / x) (Set.Icc a b) :=
      continuousOn_const.div continuousOn_id (fun x hxi => (hx x hxi).ne')
    exact hd.congr hdf
  · intro x hxi
    rw [hdf x hxi]
    exact div_pos hc (hx x hxi)
  · intro x hxi y hyi hxy
    rw [hdf x hxi, hdf y hyi]
    exact div_le_div_of_nonneg_left hc.le (hx x hxi) hxy
  · intro x hxi
    exact (afeWeight_hasDerivAt sigma (hx x hxi)).differentiableAt
  · have hd : ContinuousOn (fun x => -sigma * x ^ (-sigma - 1)) (Set.Icc a b) :=
      continuousOn_const.mul (continuousOn_id.rpow_const (fun x hxi => Or.inl (hx x hxi).ne'))
    exact hd.congr hdg
  · intro x hxi
    exact (afeWeight_pos sigma (hx x hxi)).le
  · exact (afeWeight_antitone hsigma).mono hsub
  · exact (abs_deriv_afeWeight_antitone hsigma).mono hsub
  · exact (afe_derivative_quotient_antitone hsigma hc.le).mono hsub

/-- A half-integer left endpoint removes its boundary term exactly. -/
theorem norm_poissonBoundary_left_half_integer_le {f g : ℝ → ℝ} {a b : ℝ}
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : 0 ≤ g b) :
    ‖poissonBoundary f g a b‖ ≤ g b / 2 := by
  obtain ⟨k, rfl⟩ := ha
  have hf : Int.fract ((k : ℝ) + 1 / 2) = (1 / 2 : ℝ) := by
    rw [Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr (by norm_num)
  rw [poissonBoundary, hf, sub_self, Complex.ofReal_zero, mul_zero, zero_sub, norm_neg,
    norm_mul, norm_weightedWave hb, Complex.norm_real, Real.norm_eq_abs]
  simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left (abs_fract_sub_half_le b) hb


