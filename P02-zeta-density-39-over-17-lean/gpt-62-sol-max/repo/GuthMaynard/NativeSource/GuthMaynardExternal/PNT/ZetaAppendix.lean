module
/- Adapted from PrimeNumberTheoremAnd/IEANTN/ZetaAppendix.lean at upstream
revision 4ecb950126c4290293c5662dfe0e884123171df5 (Apache-2.0). The unrelated
Mertens import is omitted from this local proof closure. -/

public import Mathlib.Algebra.Lie.OfAssociative
public import WeylPort.Analytic.NonstationaryFoundation
public import WeylPort.AFE.AbelSawtooth
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.ConstantSpeed
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Data.Int.Star
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.NumberTheory.ZetaValues
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import GuthMaynard.NativeSource.GuthMaynardExternal.PNT.ZetaBoundsUpstream

@[expose] public section

namespace ZetaAppendix

open Real Complex MeasureTheory Finset Filter Topology Set Summable

-- may want to move this to a more globally accessible location

private noncomputable def e (α : ℝ) : ℂ := exp (2 * π * I * α)

private theorem h2piI_ne_zero : 2 * π * I ≠ 0 := by norm_num

private theorem continuousOn_e_comp (φ : ℝ → ℝ) (s : Set ℝ)
    (hφ : ContinuousOn φ s) : ContinuousOn (fun t ↦ e (φ t)) s := by
  simp only [e]; fun_prop

section
variable (φ : ℝ → ℝ) (a b : ℝ)
include φ a b

private theorem continuousOn_ofReal_deriv
    (hderiv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b)) :
    ContinuousOn (fun t ↦ (↑(deriv φ t) : ℂ)) (Set.Icc a b) :=
  continuous_ofReal.comp_continuousOn hderiv_cont

private theorem denom1_ne_zero
    (hphi_ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) :
    ∀ t ∈ Set.Icc a b, 2 * π * I * ↑(deriv φ t) ≠ 0 := by
  intro t ht
  exact mul_ne_zero h2piI_ne_zero (ofReal_ne_zero.mpr (hphi_ne t ht))

private theorem denom2_ne_zero
    (hphi_ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) :
    ∀ t ∈ Set.Icc a b, 2 * π * I * ↑(deriv φ t) ^ 2 ≠ 0 := by
  intro t ht
  exact mul_ne_zero h2piI_ne_zero (pow_ne_zero 2 (ofReal_ne_zero.mpr (hphi_ne t ht)))

private theorem continuousOn_denom1
    (hderiv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b)) :
    ContinuousOn (fun t ↦ 2 * π * I * ↑(deriv φ t)) (Set.Icc a b) := by
  exact ContinuousOn.mul continuousOn_const (continuousOn_ofReal_deriv φ a b hderiv_cont)

private theorem continuousOn_denom2
    (hderiv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b)) :
    ContinuousOn (fun t ↦ 2 * π * I * ↑(deriv φ t) ^ 2) (Set.Icc a b) := by
  exact ContinuousOn.mul continuousOn_const ((continuousOn_ofReal_deriv φ a b hderiv_cont).pow 2)

private theorem intervalIntegrable_v' (hab : a ≤ b)
    (hφ_cont : ContinuousOn φ (Set.Icc a b))
    (hderiv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b)) :
    IntervalIntegrable (fun t ↦ 2 * π * I * ↑(deriv φ t) * e (φ t)) volume a b :=
  (ContinuousOn.mul
    (continuousOn_denom1 φ a b hderiv_cont)
    (continuousOn_e_comp φ _ hφ_cont)).intervalIntegrable_of_Icc hab

end

private theorem continuousOn_rpow_const_Icc (a b p : ℝ) (ha_pos : 0 < a) :
    ContinuousOn (fun t ↦ t ^ p) (Set.Icc a b) := by
  apply ContinuousOn.rpow_const continuousOn_id
  intro x hx
  exact Or.inl (ne_of_gt (lt_of_lt_of_le ha_pos hx.1))

private theorem continuousOn_rpow_toComplex (a b p : ℝ) (ha_pos : 0 < a) :
    ContinuousOn (fun t ↦ ((t ^ p : ℝ) : ℂ)) (Set.Icc a b) :=
  continuous_ofReal.comp_continuousOn (continuousOn_rpow_const_Icc a b p ha_pos)

section
variable (σ : ℝ) (φ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (ha_pos : 0 < a)
include σ φ a b hab ha_pos

private theorem intervalIntegrable_term1
    (hφ_cont : ContinuousOn φ (Set.Icc a b))
    (hderiv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b))
    (hphi_ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) :
    IntervalIntegrable
      (fun x ↦ (x ^ (-σ - 1) : ℝ) / (2 * π * I * ↑(deriv φ x)) * e (φ x)) volume a b :=
  (ContinuousOn.mul
    (ContinuousOn.div
      (continuousOn_rpow_toComplex a b (-σ - 1) ha_pos)
      (continuousOn_denom1 φ a b hderiv_cont)
      (denom1_ne_zero φ a b hphi_ne))
    (continuousOn_e_comp φ _ hφ_cont)).intervalIntegrable_of_Icc hab

private theorem intervalIntegrable_term2
    (hφ_cont : ContinuousOn φ (Set.Icc a b))
    (hderiv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b))
    (hderiv2_cont : ContinuousOn (fun t ↦ deriv (deriv φ) t) (Set.Icc a b))
    (hphi_ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) :
    IntervalIntegrable
      (fun x ↦ (x ^ (-σ) : ℝ) * ↑(deriv (deriv φ) x) /
        (2 * π * I * ↑(deriv φ x) ^ 2) * e (φ x)) volume a b :=
  (ContinuousOn.mul
    (ContinuousOn.mul
      (ContinuousOn.mul
        (continuousOn_rpow_toComplex a b (-σ) ha_pos)
        (continuous_ofReal.comp_continuousOn hderiv2_cont))
      (ContinuousOn.inv₀ (continuousOn_denom2 φ a b hderiv_cont)
        (denom2_ne_zero φ a b hphi_ne)))
    (continuousOn_e_comp φ _ hφ_cont)).intervalIntegrable_of_Icc hab

private theorem intervalIntegrable_u'
    (hderiv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b))
    (hderiv2_cont : ContinuousOn (fun t ↦ deriv (deriv φ) t) (Set.Icc a b))
    (hphi_ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) :
    IntervalIntegrable
      (fun t ↦ (-σ * t ^ (-σ - 1) : ℝ) / (2 * π * I * ↑(deriv φ t)) +
        (t ^ (-σ) : ℝ) * (-↑(deriv (deriv φ) t) / (2 * π * I * ↑(deriv φ t) ^ 2)))
      volume a b :=
  (ContinuousOn.add
    (ContinuousOn.div
       (continuous_ofReal.comp_continuousOn
         (ContinuousOn.mul continuousOn_const
           (continuousOn_rpow_const_Icc a b (-σ - 1) ha_pos)))
      (continuousOn_denom1 φ a b hderiv_cont)
      (denom1_ne_zero φ a b hphi_ne))
    (ContinuousOn.mul
      (continuousOn_rpow_toComplex a b (-σ) ha_pos)
      (ContinuousOn.div
        (ContinuousOn.neg (continuous_ofReal.comp_continuousOn hderiv2_cont))
        (continuousOn_denom2 φ a b hderiv_cont)
        (denom2_ne_zero φ a b hphi_ne)))).intervalIntegrable_of_Icc hab

end

private theorem hasDerivAt_inv_phaseDeriv (φ : ℝ → ℝ) (t : ℝ)
    (hdiff2 : DifferentiableAt ℝ (deriv φ) t) (hne : deriv φ t ≠ 0) :
    HasDerivAt (fun x ↦ (1 : ℂ) / (2 * π * I * ↑(deriv φ x)))
      (-↑(deriv (deriv φ) t) / (2 * π * I * ↑(deriv φ t) ^ 2)) t := by
  have hne' : (↑(deriv φ t) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hne
  have hderiv_phi : HasDerivAt (fun x ↦ (↑(deriv φ x) : ℂ)) (↑(deriv (deriv φ) t)) t :=
    hdiff2.hasDerivAt.ofReal_comp
  have h_2piI_phi' : HasDerivAt (fun x ↦ 2 * π * I * ↑(deriv φ x))
      (2 * π * I * ↑(deriv (deriv φ) t)) t := hderiv_phi.const_mul (2 * π * I)
  have hinv : HasDerivAt (fun x ↦ (2 * π * I * ↑(deriv φ x))⁻¹)
      (-(2 * π * I * ↑(deriv (deriv φ) t)) / (2 * π * I * ↑(deriv φ t)) ^ 2) t := by
    have h2piI_phi'_ne : 2 * π * I * ↑(deriv φ t) ≠ 0 :=
      mul_ne_zero h2piI_ne_zero hne'
    have hinv_at : HasDerivAt (Inv.inv : ℂ → ℂ)
        (-((2 * π * I * ↑(deriv φ t)) ^ 2)⁻¹) (2 * π * I * ↑(deriv φ t)) :=
      hasDerivAt_inv h2piI_phi'_ne
    have hcomp := hinv_at.comp t h_2piI_phi'
    convert hcomp using 1
    · rfl
    field_simp
  convert hinv using 1
  · funext x; simp [div_eq_mul_inv]
  · field_simp [hne']

private theorem hasDerivAt_u_full (σ : ℝ) (φ : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hdiff2 : DifferentiableAt ℝ (deriv φ) t) (hne : deriv φ t ≠ 0) :
    HasDerivAt (fun x ↦ ((x ^ (-σ) : ℝ) : ℂ) / (2 * π * I * ↑(deriv φ x)))
      (((-σ * t ^ (-σ - 1) : ℝ) : ℂ) / (2 * π * I * ↑(deriv φ t)) +
       ((t ^ (-σ) : ℝ) : ℂ) * (-↑(deriv (deriv φ) t) / (2 * π * I * ↑(deriv φ t) ^ 2))) t := by
  have h1 : HasDerivAt (fun x ↦ ((x ^ (-σ) : ℝ) : ℂ)) (((-σ * t ^ (-σ - 1) : ℝ) : ℂ)) t :=
    (hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))).ofReal_comp
  have h2 := hasDerivAt_inv_phaseDeriv φ t hdiff2 hne
  have hprod := h1.mul h2
  convert hprod using 1
  · funext x
    rw [Pi.mul_apply]
    ring_nf
  · ring_nf

private theorem hasDerivAt_e_comp (φ : ℝ → ℝ) (t : ℝ) (hdiff : DifferentiableAt ℝ φ t) :
    HasDerivAt (fun x ↦ e (φ x)) (2 * π * I * ↑(deriv φ t) * e (φ t)) t := by
  have hcomp :
      HasDerivAt (fun x ↦ cexp (2 * π * I * (φ x : ℂ)))
        (cexp (2 * π * I * (φ t : ℂ)) * (2 * π * I * (↑(deriv φ t)))) t := by
    exact (hasDerivAt_exp (2 * π * I * (φ t : ℂ))).comp t
      ((hdiff.hasDerivAt.ofReal_comp).const_mul (2 * π * I))
  simpa only [e, mul_assoc, mul_left_comm, mul_comm] using hcomp

private theorem integral_Icc_eq_interval {a b : ℝ} (h : a ≤ b) (f : ℝ → ℂ) :
    ∫ t in Set.Icc a b, f t = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_of_le h]
  exact MeasureTheory.integral_Icc_eq_integral_Ioc

set_option backward.isDefEq.respectTransparency false in
private theorem integral_power_phase_ibp (σ : ℝ) (φ : ℝ → ℝ) (a b : ℝ) (hab : a < b) (ha_pos : 0 < a)
    (h_phi_ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0)
    (h_phi_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ φ t)
    (h_phi_diff2 : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (deriv φ) t)
    (h_phi_cont : ContinuousOn φ (Set.Icc a b))
    (h_deriv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b))
    (h_deriv2_cont : ContinuousOn (fun t ↦ deriv (deriv φ) t) (Set.Icc a b)) :
    let Φ : ℝ → ℂ := fun t ↦ (t ^ (-σ) : ℝ) * e (φ t) / (2 * π * I * (deriv φ t))
    ∫ t in Set.Icc a b, (t ^ (-σ) : ℝ) * e (φ t) = Φ b - Φ a +
      (σ * ∫ t in Set.Icc a b, (t ^ (-σ - 1) : ℝ) / (2 * π * I * (deriv φ t)) * e (φ t)) +
      ∫ t in Set.Icc a b, (t ^ (-σ) : ℝ) * (deriv (deriv φ) t) /
        (2 * π * I * (deriv φ t) ^ 2) * e (φ t) := by
  intro Φ
  have hab_le : a ≤ b := le_of_lt hab
  rw [integral_Icc_eq_interval hab_le, integral_Icc_eq_interval hab_le,
    integral_Icc_eq_interval hab_le]
  let u : ℝ → ℂ := fun t ↦ ((t ^ (-σ) : ℝ) : ℂ) / (2 * π * I * ↑(deriv φ t))
  let v : ℝ → ℂ := fun t ↦ e (φ t)
  let u' : ℝ → ℂ := fun t ↦ ((-σ * t ^ (-σ - 1) : ℝ) : ℂ) / (2 * π * I * ↑(deriv φ t)) +
      ((t ^ (-σ) : ℝ) : ℂ) * (-↑(deriv (deriv φ) t) / (2 * π * I * ↑(deriv φ t) ^ 2))
  let v' : ℝ → ℂ := fun t ↦ 2 * π * I * ↑(deriv φ t) * e (φ t)
  have h_uv_eq_Phi : ∀ t, u t * v t = Φ t := by
    intro t
    simp only [u, v, Φ]
    ring_nf
  have h_lhs : ∫ x in a..b, ((x ^ (-σ) : ℝ) : ℂ) * e (φ x) =
      ∫ x in a..b, u x * v' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab_le] at hx
    simp only [u, v']
    field_simp [h_phi_ne x hx]
  rw [h_lhs]
  have h_ibp : (∫ x in a..b, u x * v' x) = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
    have hIoo_to_Icc : ∀ {x : ℝ}, x ∈ Set.Ioo (min a b) (max a b) → x ∈ Set.Icc a b := by
      intro x hx
      rw [min_eq_left hab_le, max_eq_right hab_le] at hx
      exact Ioo_subset_Icc_self hx
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (by
        rw [uIcc_of_le hab_le]
        exact ContinuousOn.div
          (continuousOn_rpow_toComplex a b (-σ) ha_pos)
          (continuousOn_denom1 φ a b h_deriv_cont)
          (denom1_ne_zero φ a b h_phi_ne))
      (by
        rw [uIcc_of_le hab_le]
        exact continuousOn_e_comp φ _ h_phi_cont)
      (by
        intro x hx
        have hx_in : x ∈ Set.Icc a b := hIoo_to_Icc hx
        have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx_in.1
        exact hasDerivAt_u_full σ φ x hx_pos (h_phi_diff2 x hx_in) (h_phi_ne x hx_in))
      (by
        intro x hx
        exact hasDerivAt_e_comp φ x (h_phi_diff x (hIoo_to_Icc hx)))
      (by simpa [u'] using
        intervalIntegrable_u' σ φ a b hab_le ha_pos h_deriv_cont h_deriv2_cont h_phi_ne)
      (by simpa [v'] using intervalIntegrable_v' φ a b hab_le h_phi_cont h_deriv_cont)
  rw [h_ibp]
  simp only [h_uv_eq_Phi, sub_eq_add_neg, ← intervalIntegral.integral_neg, add_assoc]
  congr 1
  have h_cong : ∫ x in a..b, -(u' x * v x) =
      ∫ x in a..b,
        (σ * (((x ^ (-σ - 1) : ℝ) : ℂ) / (2 * π * I * ↑(deriv φ x)) * e (φ x)) +
          ((x ^ (-σ) : ℝ) : ℂ) * ↑(deriv (deriv φ) x) /
            (2 * π * I * ↑(deriv φ x) ^ 2) * e (φ x)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [u', v]
    rw [neg_mul, show (↑(-(σ * x ^ (-σ - 1))) : ℂ) = -((↑σ : ℂ) * ↑(x ^ (-σ - 1))) by norm_cast]
    ring_nf
  have h_int_term1 : IntervalIntegrable
      (fun x ↦ ((x ^ (-σ - 1) : ℝ) : ℂ) / (2 * π * I * ↑(deriv φ x)) * e (φ x)) volume a b :=
    intervalIntegrable_term1 σ φ a b hab_le ha_pos h_phi_cont h_deriv_cont h_phi_ne
  have h_int_term2 : IntervalIntegrable
      (fun x ↦ ((x ^ (-σ) : ℝ) : ℂ) * ↑(deriv (deriv φ) x) /
        (2 * π * I * ↑(deriv φ x) ^ 2) * e (φ x)) volume a b :=
    intervalIntegrable_term2 σ φ a b hab_le ha_pos h_phi_cont h_deriv_cont h_deriv2_cont h_phi_ne
  rw [h_cong, intervalIntegral.integral_add (h_int_term1.const_mul σ) h_int_term2,
      intervalIntegral.integral_const_mul, sub_eq_add_neg]

private theorem cpow_split_re_im (t : ℝ) (s : ℂ) (ht : 0 < t) :
    (t : ℂ) ^ s = (t : ℂ) ^ (s.re : ℂ) * cexp ((s.im * I) * Real.log t) := by
  have ht0 : (t : ℂ) ≠ 0 := ne_zero_of_re_pos ht
  conv_lhs => rw [← re_add_im s]
  rw [cpow_add _ _ ht0]
  congr 1
  rw [cpow_def_of_ne_zero ht0, ofReal_log ht.le, mul_comm]

private theorem phase_rewrite (t : ℝ) (s : ℂ) (ν : ℝ) (ht : 0 < t) :
    (t : ℂ) ^ (-s) * e (ν * t) =
      ((t ^ (-s.re) : ℝ) : ℂ) * e (ν * t - (s.im / (2 * π)) * Real.log t) := by
  have hsplit := cpow_split_re_im t (-s) ht
  calc
    (t : ℂ) ^ (-s) * e (ν * t) =
        ((t : ℂ) ^ ((-s).re : ℂ)) *
          (cexp (((-s).im * I) * Real.log t) * cexp (2 * π * I * (ν * t))) := by
      rw [hsplit, mul_assoc]
      congr 2
      rw [e, ofReal_mul]
    _ = ((t : ℂ) ^ ((-s).re : ℂ)) * cexp (((-s).im * I) * Real.log t + 2 * π * I * (ν * t)) := by
      rw [mul_assoc, ← Complex.exp_add]
    _ = ((t ^ (-s.re) : ℝ) : ℂ) *
        cexp (2 * π * I * (ν * t - (s.im / (2 * π)) * Real.log t)) := by
      congr 1
      · rw [neg_re, ofReal_cpow ht.le]
      · congr 1
        rw [neg_im, ofReal_neg, neg_mul]
        field_simp
        ring_nf
    _ = ((t ^ (-s.re) : ℝ) : ℂ) * e (ν * t - (s.im / (2 * π)) * Real.log t) := by
      simp only [e, ofReal_sub, ofReal_mul, ofReal_div, ofReal_ofNat]

private theorem deriv_linear_sub_log (ν c : ℝ) (t : ℝ) (ht : t ≠ 0) :
    deriv (fun t ↦ ν * t - c * Real.log t) t = ν - c * t⁻¹ := by
  have hf : deriv (fun t ↦ ν * t) t = ν := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id t).const_mul ν).deriv
  have hg : deriv (fun t ↦ c * Real.log t) t = c * t⁻¹ := by
    rw [deriv_const_mul_field, Real.deriv_log]
  have hdiff_f : DifferentiableAt ℝ (fun t ↦ ν * t) t := by fun_prop
  have hdiff_g : DifferentiableAt ℝ (fun t ↦ c * Real.log t) t :=
    (Real.differentiableAt_log ht).const_mul c
  rw [deriv_fun_sub hdiff_f hdiff_g, hf, hg]

private theorem phi_deriv_ne_zero (s : ℂ) (ν a t : ℝ)
    (ha : a > |s.im| / (2 * π * |ν|)) (ha_pos : 0 < a) (hν : ν ≠ 0)
    (ht : a ≤ t) :
    deriv (fun t ↦ ν * t - s.im / (2 * π) * Real.log t) t ≠ 0 := by
  have ht_pos : 0 < t := lt_of_lt_of_le ha_pos ht
  rw [deriv_linear_sub_log ν (s.im / (2 * π)) t ht_pos.ne']
  intro hzero
  have h_eq : s.im = 2 * π * ν * t := by
    field_simp at hzero
    linarith [hzero]
  have hpi_pos : 0 < (2 * π : ℝ) := by positivity
  have h_abs : |s.im| = 2 * π * |ν| * t := by
    rw [h_eq, abs_mul, abs_mul, abs_of_pos hpi_pos, abs_of_pos ht_pos]
  absurd ha
  rw [not_lt, h_abs]
  field_simp
  exact ht

private theorem lemma_aachIBP (s : ℂ) (ν : ℝ) (hν : ν ≠ 0) (a b : ℝ)
    (ha : a > |s.im| / (2 * π * |ν|)) (hb : b > a) :
    let φ : ℝ → ℝ := fun t ↦ ν * t - (s.im / (2 * π)) * Real.log t
    let Φ : ℝ → ℂ := fun t ↦
      (t ^ (-s.re) : ℝ) * e (φ t) / (2 * π * I * (deriv φ t))
    ∫ t in Set.Icc a b, t ^ (-s) * e (ν * t) = Φ b - Φ a +
      (s.re * ∫ t in Set.Icc a b,
        (t ^ (-s.re - 1) : ℝ) / (2 * π * I * (deriv φ t)) * e (φ t)) +
      ∫ t in Set.Icc a b, (t ^ (-s.re) : ℝ) * (deriv (deriv φ) t) /
        (2 * π * I * (deriv φ t) ^ 2) * e (φ t) := by
  have ha_pos : 0 < a := lt_of_le_of_lt (div_nonneg (abs_nonneg _) (by positivity)) ha
  intro φ Φ
  have hIcc_pos : Set.Icc a b ⊆ Set.Ioi 0 := fun t ht ↦ lt_of_lt_of_le ha_pos ht.1
  have h_lhs : ∫ t in Set.Icc a b, t ^ (-s) * e (ν * t) =
      ∫ t in Set.Icc a b, (t ^ (-s.re) : ℝ) * e (φ t) := by
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro t ht
    simpa [φ] using phase_rewrite t s ν (hIcc_pos ht)
  rw [h_lhs]
  have h_phi_ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0 := by
    intro t ht
    exact phi_deriv_ne_zero s ν a t ha ha_pos hν ht.1
  have hsmooth : ContDiffOn ℝ 2 φ (Set.Ioi 0) := by
    simp only [φ]
    apply ContDiffOn.sub
    · fun_prop
    · apply ContDiffOn.mul contDiffOn_const
      exact contDiffOn_log.mono (fun x hx ↦ ne_of_gt hx)
  have h_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ φ t :=
    fun t ht ↦ (hsmooth.differentiableOn (by norm_num)).differentiableAt
      (Ioi_mem_nhds (hIcc_pos ht))
  have h_diff2 : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (deriv φ) t := by
    intro t ht
    have h := hsmooth.contDiffAt (Ioi_mem_nhds (hIcc_pos ht))
    have h1 : ContDiffAt ℝ 1 (deriv φ) t := h.derivWithin (by norm_num)
    exact h1.differentiableAt (by norm_num)
  have h_cont : ContinuousOn φ (Set.Icc a b) :=
    (hsmooth.mono (fun x hx ↦ lt_of_lt_of_le ha_pos hx.1)).continuousOn
  have h_deriv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b) := by
    have h1 : ContinuousOn (deriv φ) (Set.Ioi 0) :=
      hsmooth.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
    exact h1.mono (fun x hx ↦ lt_of_lt_of_le ha_pos hx.1)
  have h_deriv2_cont : ContinuousOn (fun t ↦ deriv (deriv φ) t) (Set.Icc a b) := by
    have h1 : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi 0) :=
      ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).mp hsmooth).2.2
    exact (h1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono
      (fun x hx ↦ lt_of_lt_of_le ha_pos hx.1)
  exact integral_power_phase_ibp s.re φ a b hb ha_pos h_phi_ne h_diff h_diff2
    h_cont h_deriv_cont h_deriv2_cont

private theorem lemma_aachmonophase {a b : ℝ} (ha : a < b) (φ : ℝ → ℝ) (hφ_C1 : ContDiffOn ℝ 1 φ (Set.Icc a b))
    (hφ'_ne0 : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) (h g : ℝ → ℝ) (hg : ∀ t, g t = h t / deriv φ t)
    (hg_cont : ContinuousOn g (Set.Icc a b)) (hg_mon : AntitoneOn (fun t ↦ |g t|) (Set.Icc a b)) :
    ‖∫ t in Set.Icc a b, h t * e (φ t)‖ ≤ |g a| / π := nonstationary_phase_integral_bound ha φ hφ_C1 hφ'_ne0 h g hg hg_cont hg_mon

private theorem lemma_aachdecre (σ : ℝ) (hσ : 0 ≤ σ) (τ : ℝ) (ν : ℝ) (hν : ν ≠ 0) (a b : ℝ)
    (ha : a > |τ| / (2 * π * |ν|)) (k : ℕ) (hk : 1 ≤ k) :
    let f : ℝ → ℝ := fun t ↦ t ^ (-σ - k) * |2 * π * ν - τ / t| ^ (-(k : ℝ) - 1)
    AntitoneOn f (Set.Icc a b) := by
  have h_deriv_neg : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ -(σ + k) * Real.log t - (k + 1) * Real.log |2 * Real.pi * ν - τ / t|) t < 0 := by
    intro t ht
    have h_abs : |τ / (t * ν)| < 2 * Real.pi := by
      rw [abs_div, abs_mul]
      rw [div_lt_iff₀] at *
      all_goals cases abs_cases t <;> cases abs_cases ν <;>
        nlinarith [Real.pi_gt_three, ht.1, ht.2, mul_pos Real.pi_pos (abs_pos.mpr hν),
          abs_nonneg τ, mul_div_cancel₀ (|τ|) (by positivity : (2 * Real.pi * |ν|) ≠ 0)]
    have h_deriv_neg :
        deriv (fun t ↦ -(σ + k) * Real.log t - (k + 1) * Real.log |2 * Real.pi * ν - τ / t|) t =
          -(σ + k) / t - (k + 1) * (τ / t ^ 2) / (2 * Real.pi * ν - τ / t) := by
      have ht_ne : t ≠ 0 := by linarith [ht.1, show 0 < a from lt_of_le_of_lt (by positivity) ha]
      convert HasDerivAt.deriv (HasDerivAt.sub (HasDerivAt.const_mul (-(σ + k : ℝ))
        (Real.hasDerivAt_log (show t ≠ 0 from ht_ne))) (HasDerivAt.const_mul (k + 1 : ℝ)
        (HasDerivAt.log (HasDerivAt.sub (hasDerivAt_const _ _) (HasDerivAt.const_mul τ
        (hasDerivAt_inv (show t ≠ 0 from ht_ne)))) _))) using 1 <;> norm_num
      · congr! 1
      · ring
      · contrapose! h_abs
        field_simp
        rw [abs_div, abs_mul, le_div_iff₀ (mul_pos (abs_pos.mpr
          (by linarith [ht.1, lt_of_le_of_lt (by positivity) ha])) (abs_pos.mpr hν))]
        have ht_ne' : t ≠ 0 := by positivity
        cases abs_cases t <;> cases abs_cases ν <;> cases abs_cases τ <;> push_cast [*] <;>
          nlinarith [inv_mul_cancel_left₀ ht_ne' τ, inv_mul_cancel₀ ht_ne', Real.pi_pos]
    have h_deriv_eq :
        deriv (fun t ↦ -(σ + k) * Real.log t - (k + 1) * Real.log |2 * Real.pi * ν - τ / t|) t =
          -(σ + k) / t - (k + 1) * (τ / (t * ν)) / (2 * Real.pi - τ / (t * ν)) / t := by
      convert h_deriv_neg using 1; simp only [neg_add_rev, sub_right_inj]; ring_nf; grind
    have h_expr_neg : -(σ + k) - (k + 1) * (τ / (t * ν)) / (2 * Real.pi - τ / (t * ν)) < 0 := by
      rw [sub_div', div_lt_iff₀] <;> nlinarith [abs_lt.mp h_abs, show (k : ℝ) ≥ 1 by norm_cast]
    have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) ha) ht.1
    rw [h_deriv_eq]
    have h_goal : -(σ + k) / t - (k + 1) * (τ / (t * ν)) / (2 * Real.pi - τ / (t * ν)) / t =
        (-(σ + k) - (k + 1) * (τ / (t * ν)) / (2 * Real.pi - τ / (t * ν))) / t := by ring
    exact h_goal ▸ div_neg_of_neg_of_pos h_expr_neg ht_pos
  have h_decreasing : ∀ t1 t2 : ℝ, a ≤ t1 → t1 < t2 → t2 ≤ b →
      Real.exp ((-(σ + k) * Real.log t1) - (k + 1) * Real.log |2 * Real.pi * ν - τ / t1|) ≥
        Real.exp ((-(σ + k) * Real.log t2) - (k + 1) * Real.log |2 * Real.pi * ν - τ / t2|) := by
    intro t1 t2 ht1 ht2 ht3
    have h_mean_val : ∃ c ∈ Set.Ioo t1 t2,
        deriv (fun t ↦ -(σ + k) * Real.log t - (k + 1) * Real.log |2 * Real.pi * ν - τ / t|) c =
          ((fun t ↦ -(σ + k) * Real.log t - (k + 1) * Real.log |2 * Real.pi * ν - τ / t|) t2 -
            (fun t ↦ -(σ + k) * Real.log t - (k + 1) * Real.log |2 * Real.pi * ν - τ / t|) t1) /
              (t2 - t1) := by
      apply_rules [exists_deriv_eq_slope]
      · exact continuousOn_of_forall_continuousAt fun t ht ↦ DifferentiableAt.continuousAt <|
          differentiableAt_of_deriv_ne_zero <| ne_of_lt <| h_deriv_neg t ⟨by grind, by grind⟩
      · exact fun x hx ↦ DifferentiableAt.differentiableWithinAt (by
          exact differentiableAt_of_deriv_ne_zero (ne_of_lt
            (h_deriv_neg x ⟨by linarith [hx.1], by linarith [hx.2]⟩)))
    obtain ⟨c, ⟨hc1, hc2⟩, hc3⟩ := h_mean_val
    let f := fun t ↦ -(σ + ↑k) * Real.log t - (↑k + 1) * Real.log |2 * π * ν - τ / t|
    have h_diff_neg : f t2 - f t1 < 0 := neg_of_div_neg_left
      (hc3 ▸ h_deriv_neg c ⟨by linarith, by linarith⟩) (le_of_lt <| sub_pos.mpr ht2)
    exact exp_le_exp.mpr (le_of_lt <| sub_neg.mp h_diff_neg)
  have h_f_eq_exp : ∀ t ∈ Set.Icc a b,
      t ^ (-σ - k : ℝ) * |2 * Real.pi * ν - τ / t| ^ (-(k : ℝ) - 1) =
        Real.exp ((-(σ + k) * Real.log t) - (k + 1) * Real.log |2 * Real.pi * ν - τ / t|) := by
    intro t ht
    have h_pos : 0 < t ∧ 0 < |2 * Real.pi * ν - τ / t| := by
      have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) ha) ht.1
      constructor
      · exact ht_pos
      · rw [abs_pos, sub_ne_zero, ne_eq, eq_div_iff (ne_of_gt ht_pos)]
        intro h_eq
        have : |τ| / (2 * π * |ν|) ≥ a := by
          rw [ge_iff_le, le_div_iff₀ (by positivity)]
          calc a * (2 * π * |ν|) = 2 * π * |ν| * a := by ring
            _ ≤ 2 * π * |ν| * t := mul_le_mul_of_nonneg_left ht.1 (by positivity)
            _ = |2 * π * ν * t| := by
              rw [abs_mul, abs_mul, abs_of_pos Real.two_pi_pos, abs_of_pos ht_pos]
            _ = |τ| := by rw [h_eq]
        linarith
    rw [rpow_def_of_pos h_pos.1, rpow_def_of_pos h_pos.2, ← Real.exp_add]; ring_nf
  refine fun x hx y hy hxy ↦ by cases eq_or_lt_of_le hxy <;> simp_all only [Set.mem_Icc, and_imp, le_refl]

set_option backward.isDefEq.respectTransparency false in
private theorem lemma_aachfour (s : ℂ) (hsigma : 0 ≤ s.re) (ν : ℝ) (hν : ν ≠ 0) (a b : ℝ)
    (ha : a > |s.im| / (2 * π * |ν|)) (hb : b > a) :
    let φ : ℝ → ℝ := fun t ↦ ν * t - (s.im / (2 * π)) * Real.log t
    let Φ : ℝ → ℂ := fun t ↦ (t ^ (-s.re) : ℝ) * e (φ t) / (2 * π * I * (deriv φ t))
    let ϑ : ℝ := s.im / (2 * π * a)
    ∃ E, ∫ t in Set.Icc a b, t ^ (-s) * e (ν * t) = Φ b - Φ a +
      ((a ^ (-s.re - 1) : ℝ) / (2 * π ^ 2)) * E ∧
      ‖E‖ ≤ s.re / (|ν - ϑ| ^ 2) + |ϑ| / (|ν - ϑ| ^ 3) := by
  intro φ Φ ϑ
  rw [lemma_aachIBP s ν hν a b ha hb]
  dsimp only [φ, Φ]
  let g_1 : ℝ → ℝ := fun t ↦ t ^ (-s.re - 1) / (deriv φ t) ^ 2
  have ha_pos : 0 < a := lt_of_le_of_lt (div_nonneg (abs_nonneg _) (by positivity)) ha
  have hsmooth : ContDiffOn ℝ 2 φ (Set.Ioi 0) := by
    simp only [φ]
    apply ContDiffOn.sub
    · fun_prop
    · apply ContDiffOn.mul contDiffOn_const
      exact contDiffOn_log.mono (fun x hx ↦ ne_of_gt hx)
  have hcontdiffφ : ContDiffOn ℝ 1 φ (Set.Icc a b) := (hsmooth.mono (fun x hx ↦ lt_of_lt_of_le ha_pos hx.1)).of_le (by norm_num)
  have h_cont : ContinuousOn φ (Set.Icc a b) :=
    (hsmooth.mono (fun x hx ↦ lt_of_lt_of_le ha_pos hx.1)).continuousOn
  have h_deriv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b) := by
    have h1 : ContinuousOn (deriv φ) (Set.Ioi 0) :=
      hsmooth.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
    exact h1.mono (fun x hx ↦ lt_of_lt_of_le ha_pos hx.1)
  have h_deriv2_cont : ContinuousOn (fun t ↦ deriv (deriv φ) t) (Set.Icc a b) := by
    have h1 : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi 0) :=
      ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).mp hsmooth).2.2
    exact (h1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono
      (fun x hx ↦ lt_of_lt_of_le ha_pos hx.1)
  have hφ_deriv : ∀ t ∈ Set.Icc a b, deriv φ t = ν - s.im / (2 * π * t) := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) ha) ht.1
    rw [show φ = fun x ↦ ν * x - (s.im / (2 * π)) * Real.log x from rfl]
    convert HasDerivAt.deriv (HasDerivAt.sub (HasDerivAt.const_mul ν (hasDerivAt_id t))
      (HasDerivAt.const_mul (s.im / (2 * π)) (Real.hasDerivAt_log ht_pos.ne'))) using 1
    · rfl
    field_simp
  have hφ_deriv2 : ∀ t ∈ Set.Icc a b, deriv (deriv φ) t = s.im / (2 * π * t^2) := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) ha) ht.1
    have h_deriv_φ : ∀ x ∈ Set.Ioi 0, deriv φ x = ν - s.im / (2 * π * x) := by
      intro x hx
      rw [show φ = fun x ↦ ν * x - (s.im / (2 * π)) * Real.log x from rfl]
      convert HasDerivAt.deriv (HasDerivAt.sub (HasDerivAt.const_mul ν (hasDerivAt_id x))
        (HasDerivAt.const_mul (s.im / (2 * π)) (Real.hasDerivAt_log (ne_of_gt hx)))) using 1
      · rfl
      field_simp
    have : deriv φ =ᶠ[𝓝 t] fun x ↦ ν - s.im / (2 * π * x) := by
      apply eventuallyEq_of_mem (isOpen_Ioi.mem_nhds ht_pos)
      intro x hx
      exact h_deriv_φ x hx
    rw [this.deriv_eq]
    apply HasDerivAt.deriv
    rw [show (fun x ↦ ν - s.im / (2 * π * x)) = (fun x ↦ ν - (s.im / (2 * π)) * x⁻¹) by ext; field_simp]
    convert HasDerivAt.sub (hasDerivAt_const t ν)
      (HasDerivAt.const_mul (s.im / (2 * π)) (hasDerivAt_inv ht_pos.ne')) using 1
    field_simp [Real.two_pi_pos.ne']
    ring
  have h_deriv_ne_zero : (∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) := by
    intro t ht
    exact phi_deriv_ne_zero s ν a t ha ha_pos hν ht.1
  have g_1_cont : ContinuousOn g_1 (Set.Icc a b) := by
    apply ContinuousOn.div
    · apply continuousOn_rpow_const_Icc (ha_pos := ha_pos)
    · exact h_deriv_cont.pow 2
    · intro t ht
      specialize h_deriv_ne_zero t ht
      exact pow_ne_zero 2 h_deriv_ne_zero
  have hg_1_antitone : AntitoneOn (fun t ↦ |g_1 t|) (Set.Icc a b) := by
    let f : ℝ → ℝ := fun t ↦ t ^ (-s.re - 1) * |2 * π * ν - s.im / t| ^ (-2 : ℝ)
    have hf_anti : AntitoneOn f (Set.Icc a b) := by
      convert lemma_aachdecre s.re hsigma s.im ν hν a b ha 1 (by norm_num) using 1
      ext t
      dsimp [f]
      congr 2
      · simp
      · norm_num
    have h_scaled_anti : AntitoneOn (fun t ↦ (2 * π) ^ 2 * f t) (Set.Icc a b) := by
      intro x hx y hy hxy
      apply mul_le_mul_of_nonneg_left (hf_anti hx hy hxy)
      positivity
    have hg_eq : Set.EqOn (fun t ↦ |g_1 t|) (fun t ↦ (2 * π) ^ 2 * f t) (Set.Icc a b) := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) ha) ht.1
      dsimp only [g_1, f]
      rw [abs_div, abs_pow, abs_rpow_of_nonneg ht_pos.le]
      have hφ' : deriv φ t = ν - s.im / (2 * π * t) := by
        rw [show φ = fun x ↦ ν * x - (s.im / (2 * π)) * Real.log x from rfl]
        convert HasDerivAt.deriv (HasDerivAt.sub (HasDerivAt.const_mul ν (hasDerivAt_id t))
          (HasDerivAt.const_mul (s.im / (2 * π)) (Real.hasDerivAt_log ht_pos.ne'))) using 1
        · rfl
        field_simp
      rw [hφ']
      have h_inner : 2 * π * ν - s.im / t = 2 * π * (ν - s.im / (2 * π * t)) := by
        field_simp [ht_pos.ne', Real.two_pi_pos.ne']
      rw [h_inner]
      rw [abs_mul, abs_of_pos Real.two_pi_pos, mul_rpow Real.two_pi_pos.le (abs_nonneg _),
        abs_of_pos ht_pos, mul_left_comm ((2 * π) ^ 2)]
      field_simp
      have : 2 ^ 2 * π ^ 2 * (2 * π) ^ (-2 : ℝ) = 1 := by
        rw [Real.rpow_neg (by positivity), Real.rpow_two, mul_pow]
        field_simp [Real.two_pi_pos.ne']
      rw [this]
      simp only [sq_abs, one_div, rpow_neg_ofNat, Int.reduceNeg, zpow_neg, one_mul,
        inv_inj]
      symm; apply sq_abs
    exact h_scaled_anti.congr hg_eq.symm
  have g_1_integral_bound : ‖∫ t in Set.Icc a b, (t : ℂ) ^ ((-s.re - 1) : ℂ) / (2 * π * I * deriv φ t) * e (φ t)‖ ≤
    1 / (2 * π ^ 2) * (a ^ (-s.re - 1) / |ν - ϑ| ^ 2) := by
    let h : ℝ → ℝ := fun t ↦ t^(-s.re - 1) / deriv φ t
    have hg_1_eq_h_div_deriv_φ : (∀ (t : ℝ), g_1 t = h t / deriv φ t) := by
      intro t
      dsimp [g_1, h]
      rw [div_div, pow_two]
    have hmonophase := lemma_aachmonophase (a := a) (b := b) (φ := φ) (by simp [hb])
      (hcontdiffφ) (h_deriv_ne_zero) h g_1 hg_1_eq_h_div_deriv_φ g_1_cont hg_1_antitone
    simp only [ofReal_div, h] at hmonophase
    have h_factor : (fun t => (t ^ (-s.re - 1 : ℂ) / (2 * π * I * deriv φ t)) * e (φ t)) =
                (fun t => (1 / (2 * π * I)) * (t ^ (-s.re - 1 : ℂ) / deriv φ t * e (φ t))) := by
      ext t
      field_simp
    rw [h_factor]
    have step1 : ∫ (t : ℝ) in Set.Icc a b, 1 / (2 * π * I) * ((t : ℂ) ^ ((-s.re - 1) : ℂ) / (deriv φ t) * e (φ t))
           = 1 / (2 * π * I) * ∫ (t : ℝ) in Set.Icc a b, (t : ℂ) ^ ((-s.re - 1) : ℂ) / (deriv φ t) * e (φ t) :=
      integral_const_mul _ _
    rw [step1, norm_mul]
    have h_norm_const : ‖1 / (2 * ↑π * I)‖ = 1 / (2 * π) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
        norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, mul_eq_mul_right_iff, inv_inj,
        abs_eq_self, inv_eq_zero, OfNat.ofNat_ne_zero, or_false]
      positivity
    rw [h_norm_const]
    trans (1 / (2 * π)) * (|g_1 a| / π)
    · have h_int_eq : ∫ (t : ℝ) in Set.Icc a b, (t : ℂ) ^ (-s.re - 1 : ℂ) / ↑(deriv φ t) * e (φ t)
              = ∫ (t : ℝ) in Set.Icc a b, ↑(t ^ (-s.re - 1)) / ↑(deriv φ t) * e (φ t) := by
        refine setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
        rw [Complex.ofReal_cpow]
        · simp only [Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_one]
        · have : 0 ≤ |s.im| / (2 * π * |ν|) := by positivity
          linarith [ht.1, ha]
      rw [h_int_eq]
      apply mul_le_mul_of_nonneg_left hmonophase (by positivity)
    · rw [div_mul_eq_mul_div, mul_div_assoc]
      dsimp only [g_1]
      field_simp
      have hderivφ_eq_nu_minus_theta : deriv φ a = ν - ϑ := by
        rw [hφ_deriv _ (left_mem_Icc.mpr hb.le)]
      rw [hderivφ_eq_nu_minus_theta, abs_div, Real.abs_rpow_of_nonneg ha_pos.le,
        abs_pow, abs_of_pos ha_pos]
  let g_2 : ℝ → ℝ := fun t ↦ t ^ (-s.re) * deriv (deriv φ) t / (deriv φ t) ^ 3
  have g_2_cont : ContinuousOn g_2 (Set.Icc a b) := by
    apply ContinuousOn.div
    · refine ContinuousOn.mul ?_ h_deriv2_cont
      apply continuousOn_rpow_const_Icc (ha_pos := ha_pos)
    · exact h_deriv_cont.pow 3
    · intro t ht
      specialize h_deriv_ne_zero t ht
      exact pow_ne_zero 3 h_deriv_ne_zero
  have g_2_antitone : AntitoneOn (fun t ↦ |g_2 t|) (Set.Icc a b) := by
    set f : ℝ → ℝ := fun t ↦ t ^ (-s.re - 2) * |2 * π * ν - s.im / t| ^ (-3 : ℝ) with hf
    have hf_antitone : AntitoneOn f (Set.Icc a b) := by
      convert lemma_aachdecre s.re hsigma s.im ν hν a b ha 2 (by norm_num : 1 ≤ 2) using 1
      ext t
      simp only [hf]
      ring_nf
    have g2_eq_const_mul_f : ∀ t ∈ Set.Icc a b, |g_2 t| = |s.im| * (2 * π)^2 * f t := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) ha) ht.1
      dsimp [g_2, f]
      rw [hφ_deriv t ht, hφ_deriv2 t ht]
      calc
        |t ^ (-s.re) * (s.im / (2 * π * t ^ 2)) / (ν - s.im / (2 * π * t)) ^ 3|
        = |t ^ (-s.re)| * (|s.im| / |2 * π * t ^ 2|) / |ν - s.im / (2 * π * t)| ^ 3 := by
          rw [abs_div, abs_mul, abs_pow, abs_div]
        _ = t ^ (-s.re) * (|s.im| / (2 * π * t ^ 2)) / (|2 * π * ν - s.im / t| / (2 * π)) ^ 3 := by
          rw [Real.abs_rpow_of_nonneg ht_pos.le, abs_of_pos (by positivity : 0 < 2 * π * t ^ 2)]
          rw [abs_of_pos ht_pos]
          congr 1; congr 1
          field_simp [Real.two_pi_pos.ne', ht_pos.ne']
          rw [abs_div]
          ring_nf; field_simp
          rw [abs_of_pos (by positivity : 0 < π * t * 2), abs_div, abs_of_pos ht_pos]
          field_simp [ht_pos.ne']
        _ = (t ^ (-s.re) * t ^ (-2 : ℝ) * |s.im| * (2 * π) ^ 2) * |2 * π * ν - s.im / t| ^ (-3 : ℝ) := by
          field_simp
          rw [div_eq_mul_inv, ← Real.rpow_natCast, Real.rpow_neg (abs_nonneg _)]
          simp only [Nat.cast_ofNat, rpow_ofNat, rpow_neg_ofNat, Int.reduceNeg, zpow_neg,
            mul_eq_mul_right_iff, inv_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
            pow_eq_zero_iff, abs_eq_zero, div_eq_zero_iff]
          left; field_simp [ht_pos.ne']
        _ = |s.im| * (2 * π) ^ 2 * (t ^ (-s.re - 2) * |2 * π * ν - s.im / t| ^ (-3 : ℝ)) := by
          rw [← Real.rpow_add ht_pos]
          ring_nf
    intro x hx y hy hxy
    simp_rw [g2_eq_const_mul_f x hx, g2_eq_const_mul_f y hy]
    exact mul_le_mul_of_nonneg_left (hf_antitone hx hy hxy) (by positivity)
  have g_2_integral_bound : ‖∫ t in Set.Icc a b, (t : ℂ) ^ (-s.re : ℂ) * (deriv (deriv φ) t) /
      (2 * π * I * (deriv φ t) ^ 2) * e (φ t)‖ ≤
    1 / (2 * π ^ 2) * (a ^ (-s.re - 1) * |ϑ| / |ν - ϑ| ^ 3) := by
    let h : ℝ → ℝ := fun t ↦ t ^ (-s.re) * deriv (deriv φ) t / (deriv φ t) ^ 2
    have hg_2_eq_h_div_deriv_φ : (∀ (t : ℝ), g_2 t = h t / deriv φ t) := by
      intro t
      dsimp [g_2, h]
      rw [div_div, ← pow_succ]
    have hmonophase := lemma_aachmonophase (a := a) (b := b) (φ := φ) (by simp [hb])
      (hcontdiffφ) (h_deriv_ne_zero) h g_2 hg_2_eq_h_div_deriv_φ g_2_cont g_2_antitone
    simp only [ofReal_div, h, g_2] at hmonophase
    have h_factor : ∫ t in Set.Icc a b, (t : ℂ) ^ (-s.re : ℂ) * (deriv (deriv φ) t) /
        (2 * π * I * (deriv φ t) ^ 2) * e (φ t) =
        ∫ t in Set.Icc a b, (1 / (2 * π * I)) * (↑(h t) * e (φ t)) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp [h]
      simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_neg,
        Complex.ofReal_cpow (ha_pos.trans_le ht.1).le]
      field_simp [h_deriv_ne_zero t ht]
    rw [h_factor, integral_const_mul, norm_mul]
    have h_norm_const : ‖1 / (2 * ↑π * I)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_I, mul_one]
      simp only [Complex.norm_mul, Complex.norm_ofNat, norm_real, norm_eq_abs, one_div, mul_inv_rev,
        mul_eq_mul_right_iff, inv_inj, abs_eq_self, inv_eq_zero, OfNat.ofNat_ne_zero, or_false]; positivity
    rw [h_norm_const]
    calc
      1 / (2 * π) * ‖∫ t in Set.Icc a b, ↑(h t) * e (φ t)‖
      _ ≤ 1 / (2 * π) * (|g_2 a| / π) := by
        gcongr
        convert hmonophase using 1
        simp [h, ofReal_div, ofReal_mul]
      _ = 1 / (2 * π ^ 2) * |g_2 a| := by ring
      _ = 1 / (2 * π ^ 2) * (a ^ (-s.re - 1) * |ϑ| / |ν - ϑ| ^ 3) := by
        dsimp [g_2, ϑ]
        rw [hφ_deriv _ (left_mem_Icc.mpr hb.le), hφ_deriv2 _ (left_mem_Icc.mpr hb.le)]
        have : s.im / (2 * π * a ^ 2) = (s.im / (2 * π * a)) / a := by field_simp
        rw [this]
        simp only [abs_div, abs_mul, abs_pow, abs_of_pos ha_pos, ha_pos.le, Real.abs_rpow_of_nonneg]
        field_simp [Real.pi_pos.ne', ha_pos.ne', ϑ]
        rw [mul_assoc |s.im|, mul_comm a, ← Real.rpow_add_one ha_pos.ne']
        ring_nf
  let I1 := ∫ t in Set.Icc a b, (t ^ (-s.re - 1) : ℝ) / (2 * π * I * deriv φ t) * e (φ t)
  let I2 := ∫ t in Set.Icc a b, (t ^ (-s.re) : ℝ) * (deriv (deriv φ) t) /
      (2 * π * I * (deriv φ t) ^ 2) * e (φ t)
  abel_nf
  simp only [add_left_cancel_iff]
  refine ⟨(2 * π ^ 2 * a ^ (s.re + 1 : ℂ)) * (s.re * I1 + I2), ?_, ?_⟩
  · abel_nf
    field_simp [I1, I2]
    rw [Complex.ofReal_cpow ha_pos.le, ← Complex.cpow_add _ _ (ofReal_ne_zero.mpr ha_pos.ne')]
    ring_nf
    have : 1 + (s.re : ℂ) + ↑(-1 - s.re) = 0 := by push_cast; ring
    rw [this, Complex.cpow_zero]
    simp only [mul_one]
    congr 1
    · simp only [I1]; congr
      rw [show (fun t ↦ ν * t + s.im * π⁻¹ * Real.log t * (-1 / 2)) = φ by ext; dsimp [φ]; ring]
      ext x; ring_nf; -- simp
      simp only [mul_assoc]
      congr 1
      rw [show (ν * x + s.im * (Real.log x * (π⁻¹ * (-1 / 2))) = φ x) by dsimp [φ]; ring]
      ring
    · rw [one_mul]; congr 1; ext t
      simp only [div_eq_mul_inv, pow_two, mul_inv]
      rw [mul_comm, mul_assoc, mul_left_comm]
      ring_nf
      have h_fun : (fun t ↦ ν * t + s.im * π⁻¹ * Real.log t * (-1 / 2)) = φ := by
        ext x; simp only [φ, div_eq_mul_inv]; ring
      simp only [h_fun]; field_simp
      congr; unfold φ; field_simp; ring
  · calc
    ‖2 * ↑π ^ 2 * (a : ℂ) ^ ((s.re : ℂ) + 1) * (↑s.re * I1 + I2)‖
      = (2 * π ^ 2 * a ^ (s.re + 1)) * ‖↑s.re * I1 + I2‖ := by
        rw [norm_mul]
        congr
        simp only [Complex.norm_mul, Complex.norm_ofNat, norm_pow, norm_real, norm_eq_abs, sq_abs,
          mul_eq_mul_left_iff, mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true,
          pow_eq_zero_iff, pi_ne_zero, or_self, or_false]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ha_pos]
        simp
    _ ≤ (2 * π ^ 2 * a ^ (s.re + 1)) * (s.re * ‖I1‖ + ‖I2‖) := by
      field_simp
      refine (norm_add_le _ _).trans ?_
      simp [abs_of_nonneg hsigma]
    _ ≤ (2 * π ^ 2 * a ^ (s.re + 1)) * (s.re * (1 / (2 * π ^ 2) * (a ^ (-s.re - 1) / |ν - ϑ| ^ 2))
          + (1 / (2 * π ^ 2) * (a ^ (-s.re - 1) * |ϑ| / |ν - ϑ| ^ 3))) := by
      gcongr
      · convert g_1_integral_bound using 2
        refine setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
        rw [Complex.ofReal_cpow (by linarith [ht.1, ha_pos]), Complex.ofReal_sub, Complex.ofReal_one]
        ring_nf; simp only [Complex.ofReal_neg]; ring_nf
      · convert g_2_integral_bound using 2
        refine setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
        rw [Complex.ofReal_cpow (by linarith [ht.1, ha_pos])]
        ring_nf; simp only [Complex.ofReal_neg]; ring
    _ = s.re / |ν - ϑ| ^ 2 + |ϑ| / |ν - ϑ| ^ 3 := by
      field_simp [Real.pi_pos.ne', ha_pos.ne']
      rw [← Real.rpow_add ha_pos]; ring_nf; rw [Real.rpow_zero]; ring
    _ = s.re / |ν + -1 • ϑ| ^ 2 + |ϑ| / |ν + -1 • ϑ| ^ 3 := by
      simp only [sq_abs, Int.reduceNeg, neg_smul, one_smul]; ring_nf

/-- The `IsHalfInteger` definition used by the source-facing construction in `ZetaAppendix`. -/
def _root_.Real.IsHalfInteger (x : ℝ) : Prop := ∃ k : ℤ, x = k + 1 / 2


private theorem _root_.Real.IsHalfInteger.floor_add_three_halfs (M : ℝ) : (↑⌊M⌋ + 3 / 2 : ℝ).IsHalfInteger :=
  ⟨⌊M⌋ + 1, by push_cast; ring⟩

private theorem _root_.Real.floor_add_three_halfs_gt (M : ℝ) : M < ↑⌊M⌋ + 3 / 2 := by
  linarith [Int.lt_floor_add_one M]

/-- At half-integers, `(Φ n t + Φ (-n) t) / 2 = Ψ t` where `Φ` and `Ψ` are as in `lemma_aachcanc`. -/
private theorem lemma_aachcanc_pointwise (s : ℂ) {n : ℤ} (hn : n ≠ 0)
    (t : ℝ) (ht : t.IsHalfInteger) (ht_pos : t > 0)
    (h_deriv_n : deriv (fun x ↦ (n : ℝ) * x - (s.im / (2 * π)) * Real.log x) t ≠ 0)
    (h_deriv_neg_n : deriv (fun x ↦ -(n : ℝ) * x - (s.im / (2 * π)) * Real.log x) t ≠ 0)
    (h_denom : (n : ℂ) ^ 2 - (s.im / (2 * π * t)) ^ 2 ≠ 0) :
    let ϕ : ℝ → ℝ → ℝ := fun ν t ↦ ν * t - (s.im / (2 * π)) * Real.log t
    let Φ : ℝ → ℝ → ℂ := fun ν t ↦ (t ^ (-s.re) : ℝ) * e (ϕ ν t) / (2 * π * I * (deriv (ϕ ν) t))
    let Ψ : ℝ → ℂ := fun t ↦ (-1) ^ n * (t ^ (-s) : ℂ) * (s.im / (2 * π * t)) /
      (2 * π * I * (n ^ 2 - (s.im / (2 * π * t)) ^ 2))
    (1 / 2) * (Φ n t + Φ (-n) t) = Ψ t := by
  have h_exp : e (n * t - s.im / (2 * Real.pi) * Real.log t) = (-1 : ℝ) ^ n * t ^ (-s.im * I) ∧
      e (-n * t - s.im / (2 * Real.pi) * Real.log t) = (-1 : ℝ) ^ n * t ^ (-s.im * I) := by
    unfold e
    norm_num [exp_re, exp_im, log_re, log_im, cpow_def]
    ring_nf
    have h_inner : exp (Real.pi * I * n * t * 2) = (-1 : ℂ) ^ n ∧ exp (-Real.pi * I * n * t * 2) = (-1 : ℂ) ^ n := by
      obtain ⟨k, rfl⟩ := ht
      norm_num [Complex.ext_iff, exp_re, exp_im, mul_assoc, mul_comm Real.pi]
      rcases Int.even_or_odd' n with ⟨c, rfl | rfl⟩ <;>
      · norm_num [zpow_add₀, zpow_mul]
        ring_nf
        norm_num [mul_assoc, mul_comm Real.pi _, mul_div]
        constructor
        · rw [Real.cos_eq_one_iff]; use c * k * 2; push_cast; ring
        · rw [Real.sin_eq_zero_iff]; use c * k * 4; push_cast; ring
    simp_all [Complex.exp_sub]
    norm_num [ofReal_log ht_pos.le, mul_assoc, mul_comm, mul_left_comm, pi_ne_zero]
    norm_num [Complex.exp_neg, Complex.exp_log, ht_pos.ne', mul_assoc, mul_left_comm, pi_ne_zero]
    ring_nf
    field_simp
  simp_all only [ne_eq, gt_iff_lt, neg_mul, ofReal_neg, ofReal_one, one_div, ofReal_cpow ht_pos.le]
  norm_num [mul_comm, pi_ne_zero, ht_pos.ne', h_deriv_n, h_deriv_neg_n]
  rw [div_add_div, mul_div, div_eq_div_iff]
  · rw [show (-s : ℂ) = -(s.re : ℂ) - I * (s.im : ℂ) by simp [Complex.ext_iff]]
    rw [cpow_def_of_ne_zero (by norm_cast; positivity)]
    ring_nf
    rw [cpow_def_of_ne_zero (by norm_cast; positivity), cpow_def_of_ne_zero (by norm_cast; positivity)]
    ring_nf
    rw [sub_eq_add_neg, Complex.exp_add]
    ring_nf
  · simp_all only [sub_eq_iff_eq_add, zero_add, ne_eq, mul_eq_zero, I_ne_zero, ofReal_eq_zero,
      pi_ne_zero, OfNat.ofNat_ne_zero, false_or, not_or]
    constructor <;> exact fun h ↦ h_denom <| by linear_combination' h * h
  · simp_all [mul_assoc, mul_comm]
  · contrapose! h_deriv_n
    simp_all [mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, sub_eq_iff_eq_add]
  · norm_num [Complex.ext_iff, pi_ne_zero, ht_pos.ne'] at *
    norm_cast at *
    simp_all [mul_comm, div_eq_mul_inv]
    grind

private theorem lemma_aachcanc (s : ℂ) {n : ℤ} (hn : 0 < n) {a b : ℝ}
    (ha : a > |s.im| / (2 * π * n)) (hb : b > a)
    (ha' : a.IsHalfInteger) (hb' : b.IsHalfInteger) :
    let ϕ : ℝ → ℝ → ℝ := fun ν t ↦ ν * t - (s.im / (2 * π)) * Real.log t
    let Φ : ℝ → ℝ → ℂ := fun ν t ↦
      (t ^ (-s.re) : ℝ) * e (ϕ ν t) / (2 * π * I * (deriv (ϕ ν) t))
    let Ψ : ℝ → ℂ := fun t ↦ (-1) ^ n * (t ^ (-s) : ℂ) * (s.im / (2 * π * t)) /
      (2 * π * I * (n ^ 2 - (s.im / (2 * π * t)) ^ 2))
    (1 / 2) * (Φ n b - Φ n a + Φ (-n) b - Φ (-n) a) = Ψ b - Ψ a := by
  intro phi Φ Ψ
  have h_apply : ∀ t : ℝ, t > |s.im| / (2 * .pi * n) → t.IsHalfInteger → t > 0 →
      (1 / 2) * (Φ n t + Φ (-n) t) = Ψ t := by
    intro t ht ht' ht''
    have h_bound : |s.im| < t * (2 * .pi * n) := by
      rw [gt_iff_lt] at ht; exact (div_lt_iff₀ (by positivity)).mp ht
    convert lemma_aachcanc_pointwise s (show n ≠ 0 by linarith) t ht' ht'' ?_ ?_ ?_ using 1
    all_goals norm_num [mul_comm]
    · norm_num [ht''.ne', pi_ne_zero, mul_comm]
      field_simp
      cases abs_cases s.im <;> nlinarith [pi_pos, h_bound]
    · norm_num [ht''.ne', Real.differentiableAt_log]
      field_simp
      cases abs_cases s.im <;> nlinarith [pi_pos, h_bound]
    · rw [sub_eq_zero, eq_comm]
      norm_num [div_pow, ← mul_assoc, Complex.ext_iff]
      norm_cast
      norm_num
      rw [div_eq_iff (by positivity)]
      rw [abs_lt] at h_bound
      nlinarith [pi_pos]
  have hb_pos : b > 0 := lt_trans (lt_of_le_of_lt (by positivity) ha) hb
  trans (1 / 2) * (Φ n b + Φ (-n) b) - (1 / 2) * (Φ n a + Φ (-n) a)
  · ring
  rw [h_apply b (lt_trans ha hb) hb' hb_pos, h_apply a ha ha' (lt_of_le_of_lt (by positivity) ha)]

set_option backward.isDefEq.respectTransparency false in

private theorem proposition_applem (s : ℂ) (hsigma : 0 ≤ s.re) {a b : ℝ} (ha : a > |s.im| / (2 * π))
    (hb : b > a) (ha' : a.IsHalfInteger) (hb' : b.IsHalfInteger) {n : ℕ} (hn : 1 ≤ n) :
    let ϑ : ℝ := s.im / (2 * π * a)
    ∃ E, ∫ t in Set.Icc a b, (t : ℂ) ^ (-s) * Real.cos (2 * π * (n : ℝ) * t) =
      ((-1) ^ n * (b ^ (-s) : ℂ) * (s.im / (2 * π * b)) /
        (2 * π * I * ((n : ℝ) ^ 2 - (s.im / (2 * π * b)) ^ 2)) -
       (-1) ^ n * (a ^ (-s) : ℂ) * (s.im / (2 * π * a)) /
        (2 * π * I * ((n : ℝ) ^ 2 - (s.im / (2 * π * a)) ^ 2))) +
      ((a ^ (-s.re - 1) : ℝ) / (4 * π ^ 2)) * E ∧
      ‖E‖ ≤ s.re / ((n - ϑ) ^ 2) + s.re / ((n + ϑ) ^ 2) +
        |ϑ| / (|n - ϑ| ^ 3) + |ϑ| / (|n + ϑ| ^ 3) := by
  have h_pos_a : 0 < a := lt_of_le_of_lt (by positivity) ha
  have h_bound_aux : |s.im| / (2 * π * n) < a := by
    refine ha.trans_le' <| div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
    nlinarith [pi_gt_three, show (n : ℝ) ≥ 1 by norm_cast]
  have h_neg := lemma_aachfour s hsigma (-n : ℝ) (by norm_num; linarith) a b (by
    simp only [abs_neg, abs_of_nonneg (show 0 ≤ (n : ℝ) by positivity)]
    exact h_bound_aux) hb
  have h_pos := lemma_aachfour s hsigma (n : ℝ) (by norm_num; linarith) a b (by
    simp only [abs_of_nonneg (show 0 ≤ (n : ℝ) by positivity)]
    exact h_bound_aux) hb
  obtain ⟨E1, hE1_eq, hE1_bound⟩ := h_pos
  obtain ⟨E2, hE2_eq, hE2_bound⟩ := h_neg
  use E1 + E2
  have h_cont_pow : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (-s)) (Set.Icc a b) :=
    ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
      fun x hx ↦ Or.inl (by norm_cast; linarith [hx.1, h_pos_a])
  have h_integral : ∫ t in Set.Icc a b, (t : ℂ) ^ (-s) * (Real.cos (2 * Real.pi * n * t)) =
      (1 / 2) * (∫ t in Set.Icc a b, (t : ℂ) ^ (-s) * e (n * t)) +
        (1 / 2) * (∫ t in Set.Icc a b, (t : ℂ) ^ (-s) * e (-n * t)) := by
    rw [← mul_add, ← integral_add]
    · rw [← integral_const_mul]
      congr with t
      norm_num [e, Complex.cos]
      ring_nf
    · exact (h_cont_pow.mul (Complex.continuous_exp.comp (by continuity)).continuousOn).integrableOn_Icc
    · exact (h_cont_pow.mul (Complex.continuous_exp.comp (by continuity)).continuousOn).integrableOn_Icc
  constructor
  · have h_lem := lemma_aachcanc s (by grind) h_bound_aux hb ha' hb'
    simp only [zpow_natCast, Int.cast_natCast, one_div, neg_mul] at h_lem
    simp only [h_integral, hE1_eq, hE2_eq]
    convert congrArg (· + (↑(a ^ (-s.re - 1)) / (4 * ↑π ^ 2)) * (E1 + E2)) h_lem using 1; ring_nf
  · have : |-(n : ℝ) - s.im / (2 * π * a)| = |(n : ℝ) + s.im / (2 * π * a)| := by
      rw [show -(n : ℝ) - s.im / (2 * π * a) = -((n : ℝ) + s.im / (2 * π * a)) by ring, abs_neg]
    calc ‖E1 + E2‖ ≤ ‖E1‖ + ‖E2‖ := norm_add_le E1 E2
      _ ≤ _ := add_le_add hE1_bound hE2_bound
      _ = _ := by simp only [sq_abs, this]; ring

private theorem lemma_abadeulmac' {b : ℕ} (hb : 0 < b) {s : ℂ}
    (hs1 : s ≠ 1) (hsigma : 0 < s.re) :
    ∑ n ∈ Icc 1 b, (n : ℂ) ^ (-s) =
      riemannZeta s + (b ^ (1 - s) : ℂ) / (1 - s) + (b ^ (-s) : ℂ) / (2) +
      s * ∫ y in Set.Ioi (b : ℝ), (Int.fract y - 1 / 2) * ((y : ℂ) ^ (-(s + 1))) := by
  rw [← nativeMoment_Zeta0EqZeta hb (by linarith) hs1]
  unfold nativeMoment_riemannZeta0
  rw [show ∑ n ∈ Icc 1 b, (n : ℂ) ^ (-s) = (∑ n ∈ Icc 1 b, (n : ℂ) ^ (-s)) + 0 by ring]
  rw [show ∑ n ∈ range (b + 1), 1 / (n : ℂ) ^ s = ∑ n ∈ Icc 1 b, (n : ℂ) ^ (-s) by
    rw [range_eq_Ico]
    rw [sum_eq_sum_Ico_succ_bot (by linarith)]
    norm_cast
    rw [zero_cpow (by aesop)]
    simp only [div_zero, zero_add, one_div]
    rw [← Finset.Ico_succ_right_eq_Icc]
    congr
    ext x
    rw [cpow_neg]]
  rw [show (∑ n ∈ Icc 1 b, (n : ℂ) ^ (-s) + -(b : ℂ) ^ (1 - s) / (1 - s) + -(b : ℂ) ^ (-s) / 2 +
          s * ∫ (x : ℝ) in Set.Ioi ↑b, (⌊x⌋ + 1 / 2 - x : ℂ) / (x : ℂ) ^ (s + 1)) +
        (b : ℂ) ^ (1 - s) / (1 - s) +
      (b : ℂ) ^ (-s) / 2 +
    s * ∫ (y : ℝ) in Set.Ioi ↑b, ((Int.fract y) - 1 / 2) * (y : ℂ) ^ (-(s + 1)) =
      ∑ n ∈ Icc 1 b, (n : ℂ) ^ (-s) + (
          s * (∫ (x : ℝ) in Set.Ioi ↑b, (⌊x⌋ + 1 / 2 - x : ℂ) / (x : ℂ) ^ (s + 1))   +
    s * ∫ (y : ℝ) in Set.Ioi ↑b, ((Int.fract y) - 1 / 2) * (y : ℂ) ^ (-(s + 1))) by ring]
  congr! 1
  suffices h : ∫ (x : ℝ) in Set.Ioi ↑b, (⌊x⌋ + 1 / 2 - x : ℂ) / ↑x ^ (s + 1) =
             -∫ (y : ℝ) in Set.Ioi ↑b, ((Int.fract y) - 1 / 2 : ℂ) * ↑y ^ (-(s + 1)) by
    rw [h]; ring
  rw [← MeasureTheory.integral_neg]
  congr 1
  ext x
  unfold Int.fract
  rw [show (x : ℂ) ^ (-(s + 1)) = 1 / (↑x : ℂ) ^ (s + 1) by
    rw [cpow_neg, one_div]]
  rw [mul_one_div, ← neg_div]
  congr
  ring_nf
  push_cast
  ring_nf

set_option backward.isDefEq.respectTransparency false in

private theorem lemma_abadeulmac {b : ℝ} (hb : 0 < b) (hb' : b.IsHalfInteger) {s : ℂ}
    (hs1 : s ≠ 1) (hsigma : 0 < s.re) :
    ∑ n ∈ Icc 1 ⌊b⌋₊, (n : ℂ) ^ (-s) =
      riemannZeta s + (b ^ (1 - s) : ℂ) / (1 - s) +
      s * ∫ y in Set.Ioi b, (Int.fract y - 1 / 2 : ℂ) * ((y : ℂ) ^ (-(s + 1))) := by
  have := @lemma_abadeulmac'
  obtain ⟨k, rfl⟩:=hb'
  lift k to@ℕ using Int.le_of_lt_add_one (mod_cast (by linear_combination hb:0<(k: ℝ) + 1))
  specialize this k.succ_pos hs1 hsigma
  norm_num[k.floor_eq_iff (hb.le.trans ↑ _)|>.mpr, sum_Icc_succ_top]at*
  conv =>
    enter [2, 2, 2, 1, 2, 1]
    equals (1 : ℝ) / 2 + k => ring_nf
  rw [←Set.Ioc_union_Ioi_eq_Ioi (add_le_add_left one_half_lt_one.le _), MeasureTheory.setIntegral_union₀]
  · conv =>
      enter [2, 2, 2, 1, 1, 2, 1]
      equals (k : ℝ) + 1/2 => ring_nf
    conv =>
      enter [2, 2, 2, 1, 1, 2, 2]
      equals (k : ℝ) + 1 => ring_nf
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.setIntegral_congr_fun (g := fun x : ℝ => (x - k - 1/2 : ℂ) * x ^ (-1 + -s)) measurableSet_Ioo]
    · rw[MeasureTheory.setIntegral_congr_fun (g:=fun x:ℝ=>(x : ℂ)^(-s)-k*x^(-1+-s)-1/2*x^(-1+-s)) (measurableSet_Ioo),←MeasureTheory.integral_Ioc_eq_integral_Ioo]
      · norm_num[*,←intervalIntegral.integral_of_le _]
        have notmem : 0 ∉ Set.uIcc ((k : ℝ) + 1 / 2) ((k : ℝ) + 1) := by
          apply Set.notMem_uIcc_of_lt <;> positivity
        have  int1 : IntervalIntegrable (fun t ↦ (t : ℂ) ^ (-1 + -s)) volume (↑k + 1 / 2) (↑k + 1) := by
          exact intervalIntegral.intervalIntegrable_cpow (Or.inr notmem)
        have  int0 : IntervalIntegrable (fun t ↦ (t : ℂ) ^ (-s)) volume (↑k + 1 / 2) (↑k + 1) := by
          exact intervalIntegral.intervalIntegrable_cpow (Or.inr notmem)
        rw [intervalIntegral.integral_sub (int0.sub (int1.const_mul _)) (int1.const_mul _), intervalIntegral.integral_sub int0 (int1.const_mul _)]
        simp only [intervalIntegral.integral_const_mul]
        have ne_zero : s ≠ 0 := fun h ↦ (by simp_all)
        rw [integral_cpow (Or.inr ⟨(by grind), notmem⟩), integral_cpow (Or.inr ⟨(by simp[ne_zero]), notmem⟩)]
        norm_num
        rw [eq_sub_of_add_eq this]
        apply sub_eq_zero.mp
        field_simp [s.ne_zero_of_re_pos hsigma]
        ring_nf
        have {x : ℂ} (hx : x ≠ 0) : x ^ (1 - s) = x * x^(-s) := by
          rw [sub_eq_add_neg, cpow_add _ _ hx, cpow_one]
        rw [this, this]
        · have : 1 - s ≠ 0 := by grind
          field [s.ne_zero_of_re_pos hsigma]
        · rw [add_comm] at hb
          convert  ofReal_ne_zero.mpr hb.ne.symm
          simp
        · have : 1 + (k : ℝ) ≠ 0 := by linarith
          convert  ofReal_ne_zero.mpr this
          simp
      · use fun A B=>by norm_num[sub_mul,mul_comm (A : ℂ), (hb.trans B.1).ne',cpow_add,cpow_neg]
    · use fun and p=>by zify[Int.fract,Int.floor_eq_iff.2 (p.imp_left (by linear_combination·)),Int.cast_natCast]
  · norm_num[MeasureTheory.AEDisjoint]
  · norm_num
  · conv =>
      enter [2, 1]
      equals (k : ℝ) + 1/2 => ring_nf
    conv =>
      enter [2, 2]
      equals (k : ℝ) + 1 => ring_nf
    rw[integrableOn_Ioc_iff_integrableOn_Ioo,MeasureTheory.integrableOn_congr_fun (fun A B=>by rw [Int.fract,Int.floor_eq_iff.2 (B.imp_left (by linear_combination·))]) measurableSet_Ioo]
    exact (ContinuousOn.mul (by fun_prop) (.cpow_const (by fun_prop) fun and c=>.inl (hb.trans_le c.1))).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  · apply(integrableOn_Ioi_rpow_of_lt (by norm_num[*]:-1+-s.1< _) (by bound)).norm.mono' ((measurable_fract.complex_ofReal.sub_const _).mul (by fun_prop)).aestronglyMeasurable
    filter_upwards[MeasureTheory.ae_restrict_mem (by norm_num)] with S(F: S> _)
    have := k.cast_add_one_pos (α := ℝ)
    conv at this =>
      enter [2]
      equals (1 : ℝ) + k => ring_nf

    norm_num[abs_of_pos, S.rpow_pos_of_pos, (F.trans' this).le, norm_cpow_eq_rpow_re_of_nonneg, ne_of_gt,(norm_sub_le _ _).trans ∘le_of_lt]
    rw [norm_cpow_eq_rpow_re_of_nonneg]
    conv =>
      enter [1, 2, 2]
      equals (-1 : ℝ) + -s.re => simp
    · rw [abs_of_pos]
      · conv =>
          enter [2]
          equals (1 : ℝ) * S ^ (-1 + -s.re) => ring_nf
        gcongr
        · apply (S.rpow_pos_of_pos (by linarith) _).le

        exact (congr_arg _ (by zify)).trans_le ((norm_real (Int.fract S-1/2)).le.trans (max_le (by linear_combination Int.fract_lt_one S) (by linear_combination Int.fract_nonneg S)))
      · apply (S.rpow_pos_of_pos (by linarith) _)
    · linarith
    · simp only [add_re, neg_re, one_re, ne_eq]
      linarith

private theorem lemma_abadtoabsum {a b : ℝ} (ha : 0 < a) (hb' : b.IsHalfInteger) (hab : b > a) {s : ℂ}
    (hs1 : s ≠ 1) (hsigma : 0 < s.re) :
    ∃ E, ∑ n ∈ Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) = -∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
      (n : ℂ) ^ (-s) + riemannZeta s + (b ^ (1 - s) : ℂ) / (1 - s) + E ∧
      ‖E‖ ≤ ‖s‖ / (2 * s.re * (b ^ s.re : ℝ)) := by
  have hb_pos : 0 < b := ha.trans hab
  have hmac := lemma_abadeulmac hb_pos hb' hs1 hsigma
  let E := s * ∫ y in Set.Ioi b, (Int.fract y - 1 / 2 : ℂ) * ((y : ℂ) ^ (-(s + 1)))
  refine ⟨E, ?_, ?_⟩
  · have hfinset : (Icc 1 ⌊b⌋₊ : Finset ℕ) = Finset.Icc 1 ⌊a⌋₊ ∪ Ioc ⌊a⌋₊ ⌊b⌋₊ := by
      ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      refine ⟨fun ⟨h1, hn⟩ ↦ ?_, fun h ↦ ?_⟩
      · by_cases hn' : n ≤ ⌊a⌋₊
        · exact Or.inl ⟨h1, hn'⟩
        · exact Or.inr ⟨Nat.lt_of_not_le hn', hn⟩
      · rcases h with ⟨h1, hn⟩ | ⟨hn1, hn2⟩
        · exact ⟨h1, hn.trans <| Nat.floor_mono hab.le⟩
        · exact ⟨by omega, hn2⟩
    have hdisjoint : Disjoint (Finset.Icc 1 ⌊a⌋₊) (Ioc ⌊a⌋₊ ⌊b⌋₊) :=
      disjoint_left.mpr fun x hx₁ hx₂ ↦ by simp only [Finset.mem_Icc] at hx₁; simp only [Finset.mem_Ioc] at hx₂; omega
    rw [hfinset, sum_union hdisjoint] at hmac
    linear_combination' hmac
  · have h_integral_bound : ‖∫ y in Set.Ioi b, (Int.fract y - 1 / 2 : ℂ) * ((y : ℂ) ^ (-(s + 1)))‖ ≤
        (1 / 2) * (1 / (s.re * b ^ s.re)) := by
      have hstep1 : ‖∫ y in Set.Ioi b, (Int.fract y - 1 / 2 : ℂ) * ((y : ℂ) ^ (-(s + 1)))‖ ≤
          ∫ y in Set.Ioi b, ‖(Int.fract y - 1 / 2 : ℂ) * ((y : ℂ) ^ (-(s + 1)))‖ :=
        norm_integral_le_integral_norm _
      have : ∫ y in Set.Ioi b, ‖(Int.fract y - 1 / 2 : ℂ) * ((y : ℂ) ^ (-(s + 1)))‖ ≤
          ∫ y in Set.Ioi b, (1 / 2 : ℝ) * (y : ℝ) ^ (-(s.re + 1)) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
          ((integrableOn_Ioi_rpow_of_lt (by linarith) hb_pos).const_mul _) _
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos (hb_pos.trans hy), neg_add_rev, add_re,
          neg_re, one_re]
        apply mul_le_mul_of_nonneg_right _ (rpow_nonneg (hb_pos.trans hy).le _)
        rw [norm_sub_rev]
        have hfract_bound : ‖(1 / 2 : ℂ) - ↑(Int.fract y)‖ ≤ 1 / 2 := by
          have : (1 / 2 : ℂ) - ↑(Int.fract y) = ↑((1 / 2 : ℝ) - (Int.fract y : ℝ)) := by
            simp only [ofReal_sub, ofReal_div, ofReal_one, ofReal_ofNat]
          rw [this, norm_real, norm_eq_abs, abs_le]
          constructor <;> linarith [Int.fract_nonneg y, Int.fract_lt_one y]
        exact hfract_bound
      have : ∫ y in Set.Ioi b, (1 / 2 : ℝ) * (y : ℝ) ^ (-(s.re + 1)) =
          (1 / 2) * (1 / (s.re * b ^ s.re)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) hb_pos]
        have : -(s.re + 1) + 1 = -s.re := by ring
        have : b ^ (-s.re) = (b ^ s.re)⁻¹ := rpow_neg hb_pos.le s.re
        aesop
      linarith
    calc ‖E‖ = ‖s‖ * ‖∫ y in Set.Ioi b, (Int.fract y - 1 / 2 : ℂ) * ((y : ℂ) ^ (-(s + 1)))‖ := by simp only [E, norm_mul]
      _ ≤ ‖s‖ * ((1 / 2) * (1 / (s.re * b ^ s.re))) := mul_le_mul_of_nonneg_left h_integral_bound (norm_nonneg _)
      _ = ‖s‖ / (2 * s.re * b ^ s.re) := by ring

private theorem lemma_abadsumas_integrable_explog {s : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b) (k : ℤ) :
    IntervalIntegrable
      (fun y => ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) * e (↑k * y))
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hab)
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · apply continuous_ofReal.comp_continuousOn
      apply ContinuousOn.rpow continuousOn_id continuousOn_const
      exact fun _ hx => Or.inl (ne_of_gt (lt_of_lt_of_le ha hx.1))
    · apply continuousOn_e_comp
      apply ContinuousOn.mul continuousOn_const
      apply Real.continuousOn_log.mono
      exact fun _ hx => ne_of_gt (lt_of_lt_of_le ha hx.1)
  · dsimp [e]; fun_prop

set_option backward.isDefEq.respectTransparency false in
private theorem lemma_abadsumas_sum_fourier (s : ℂ) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) :
    let f : ℝ → ℂ := fun y ↦
      if a ≤ y ∧ y ≤ b then (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) else 0
    ∀ n : ℕ,
    FourierTransform.fourier f (n + 1) + FourierTransform.fourier f (-(n + 1 : ℤ)) =
    2 * ∫ y in a..b, (y : ℂ) ^ (-s) * Real.cos (2 * π * (n + 1) * y) := by
  intro f n
  have fourier_as_integral : ∀ n : ℤ, FourierTransform.fourier f n =
    ∫ y in a..b, (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) * e (-n * y) := by
    intro n
    calc FourierTransform.fourier f ↑n
      _ = ∫ (y : ℝ), Complex.exp (↑(-2 * π * y * ↑n) * Complex.I) • f y := fourier_real_eq_integral_exp_smul f ↑n
      _ = ∫ (y : ℝ) in a..b, Complex.exp (↑(-2 * π * y * ↑n) * Complex.I) • f y := by
        rw [intervalIntegral.integral_of_le hab.le, ← integral_indicator measurableSet_Ioc]
        apply MeasureTheory.integral_congr_ae
        filter_upwards [MeasureTheory.Measure.ae_ne volume a] with y hy_ne
        by_cases hy : y ∈ Set.Ioc a b
        · rw [Set.indicator_of_mem hy]
        · rw [Set.indicator_of_notMem hy]
          have h_f_zero : f y = 0 := by
            dsimp [f]
            split_ifs with h_bounds
            · exact (hy ⟨lt_of_le_of_ne h_bounds.1 hy_ne.symm, h_bounds.2⟩).elim
            · rfl
          rw [h_f_zero, smul_zero]
      _ = ∫ (y : ℝ) in a..b, ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) * e (-↑n * y) := by
        apply intervalIntegral.integral_congr
        intro y hy
        have h_bounds : a ≤ y ∧ y ≤ b := by
          rw [Set.uIcc_of_le hab.le] at hy
          exact ⟨hy.1, hy.2⟩
        have h_f_val : f y = (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) := by
          dsimp [f]
          rw [ite_eq_left h_bounds]
        dsimp only
        rw [h_f_val, e]
        calc cexp (↑(-2 * π * y * ↑n) * I) • (↑(y ^ (-s.re)) * cexp (2 * ↑π * I * ↑(-(s.im / (2 * π)) * Real.log y)))
            = ↑(y ^ (-s.re)) * cexp (2 * ↑π * I * ↑(-(s.im / (2 * π)) * Real.log y))
                * cexp (↑(-2 * π * y * ↑n) * I) := by
                  rw [smul_eq_mul]; ring
          _ = ↑(y ^ (-s.re)) * cexp (2 * ↑π * I * ↑(-(s.im / (2 * π)) * Real.log y))
                * e (-↑n * y) := by
                  rw [e]
                  congr 1
                  congr 1
                  push_cast
                  ring
  have sum_fourier_as_cosine : ∀ n : ℕ,
    FourierTransform.fourier f (n + 1) + FourierTransform.fourier f (-(n + 1 : ℤ)) =
    2 * ∫ y in a..b, (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) *
      Real.cos (2 * π * (n + 1) * y) := by
    intro n
    have h1 : FourierTransform.fourier f (↑n + 1) =
        ∫ y in a..b, ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) * e (-(↑n + 1 : ℤ) * y) := by
      exact_mod_cast fourier_as_integral (↑n + 1 : ℤ)
    have h2 : FourierTransform.fourier f (-↑(n + 1 : ℤ)) =
        ∫ y in a..b, ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) * e (↑(n + 1 : ℤ) * y) := by
      simpa only [Int.cast_neg, neg_neg] using fourier_as_integral (-↑((n + 1) : ℤ))
    rw [h1, h2]
    have hint1 : IntervalIntegrable
        (fun y => ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) * e (-(↑n + 1 : ℤ) * y))
        MeasureTheory.volume a b := by
      have := lemma_abadsumas_integrable_explog (s := s) ha hab (-(n + 1) : ℤ)
      simpa only [Int.cast_neg] using this
    have hint2 : IntervalIntegrable
        (fun y => ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) * e (↑(n + 1 : ℤ) * y))
        MeasureTheory.volume a b := lemma_abadsumas_integrable_explog ha hab (n + 1 : ℤ)
    rw [← intervalIntegral.integral_add hint1 hint2, ← intervalIntegral.integral_const_mul]
    congr 1
    ext y
    have heuler : e (-↑(n + 1 : ℤ) * y) + e (↑(n + 1 : ℤ) * y) =
    2 * ↑(Real.cos (2 * π * (↑n + 1) * y)) := by
      have hpos : e (↑(n + 1 : ℤ) * y) =
          Complex.exp (↑(2 * π * (↑n + 1) * y) * Complex.I) := by
        simp only [e]; push_cast; ring_nf
      have hneg : e (-↑(n + 1 : ℤ) * y) =
          Complex.exp (-(↑(2 * π * (↑n + 1) * y)) * Complex.I) := by
        simp only [e]; push_cast; ring_nf
      rw [hneg, hpos, add_comm, Complex.ofReal_cos, ← Complex.two_cos]
    linear_combination ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) * heuler
  rw [sum_fourier_as_cosine n]
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  simp only [neg_mul, ofReal_cos, ofReal_mul, ofReal_ofNat, ofReal_add, ofReal_natCast, ofReal_one,
  mul_eq_mul_right_iff]
  have hy_pos : 0 < y := by
    rw [Set.uIcc_of_le hab.le] at hy
    exact ha.trans_le hy.1
  have key : (y : ℂ) ^ (-s) =
      ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) := by
    have hyne : (y : ℂ) ≠ 0 := by exact_mod_cast hy_pos.ne'
    rw [Complex.cpow_def_of_ne_zero hyne]
    rw [← Complex.ofReal_log hy_pos.le]
    have hexp_split : (↑(Real.log y) : ℂ) * -s =
        ↑(-s.re * Real.log y) + ↑(-s.im * Real.log y) * Complex.I := by
      rw [← Complex.re_add_im s]
      push_cast
      ring_nf
      field_simp
      congr 1
      simp only [re_add_im]
      ring_nf
    rw [hexp_split, Complex.exp_add_mul_I]
    have hrpow : (y ^ (-s.re) : ℝ) = Real.exp (-s.re * Real.log y) := by
      rw [mul_comm, ← Real.rpow_def_of_pos hy_pos]
    have he_expand : e (-(s.im / (2 * π)) * Real.log y) =
        ↑(Real.cos (-s.im * Real.log y)) + ↑(Real.sin (-s.im * Real.log y)) * Complex.I := by
      rw [show ↑(Real.cos (-s.im * Real.log y)) + ↑(Real.sin (-s.im * Real.log y)) * I =
          Complex.exp (↑(-s.im * Real.log y) * I) from by
            rw [exp_mul_I]
            simp only [Complex.ofReal_cos, Complex.ofReal_sin]]
      simp [e]
      congr 1
      ring_nf; field_simp
    rw [hrpow, he_expand]
    push_cast
    ring
  simp [key]








private theorem B1_eq_fract_sub_half {x : ℝ} (hx0 : 0 ≤ x) :
    GuthMaynard.NativePNT.B1 x = Int.fract x - 1 / 2 := by
  unfold GuthMaynard.NativePNT.B1
  rw [Int.fract]
  have hfloor : ((⌊x⌋₊ : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
    norm_cast
    exact Int.natCast_floor_eq_floor hx0
  rw [hfloor]

section CosineIntegralIBP

private theorem hasDerivAt_sine_antideriv (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ ↦
        ((Real.sin (2 * Real.pi * (n + 1 : ℝ) * y) /
          (Real.pi * (n + 1 : ℝ))) : ℂ))
      ((2 * Real.cos (2 * Real.pi * (n + 1 : ℝ) * x)) : ℂ) x := by
  have hden : Real.pi * (n + 1 : ℝ) ≠ 0 := by positivity
  have hsin :
      HasDerivAt
        (fun y : ℝ ↦ Real.sin (2 * Real.pi * (n + 1 : ℝ) * y))
        ((2 * Real.pi * (n + 1 : ℝ)) *
          Real.cos (2 * Real.pi * (n + 1 : ℝ) * x)) x := by
    convert
      (Real.hasDerivAt_sin (2 * Real.pi * (n + 1 : ℝ) * x)).comp x
        ((hasDerivAt_id x).const_mul (2 * Real.pi * (n + 1 : ℝ))) using 1
    · rfl
    ring
  have hreal :
      HasDerivAt
        (fun y : ℝ ↦ Real.sin (2 * Real.pi * (n + 1 : ℝ) * y) /
          (Real.pi * (n + 1 : ℝ)))
        (2 * Real.cos (2 * Real.pi * (n + 1 : ℝ) * x)) x := by
    convert hsin.div_const (Real.pi * (n + 1 : ℝ)) using 1
    field_simp [hden]
  simpa using hreal.ofReal_comp

private theorem cosine_integral_by_parts_cpow {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (s : ℂ) (n : ℕ) :
    2 * ∫ y in a..b, (y : ℂ) ^ (-s) *
        Real.cos (2 * Real.pi * (n + 1 : ℝ) * y) =
      (b : ℂ) ^ (-s) *
          ((Real.sin (2 * Real.pi * (n + 1 : ℝ) * b) /
            (Real.pi * (n + 1 : ℝ))) : ℂ) -
        (a : ℂ) ^ (-s) *
          ((Real.sin (2 * Real.pi * (n + 1 : ℝ) * a) /
            (Real.pi * (n + 1 : ℝ))) : ℂ) -
        ∫ y in a..b,
          deriv (fun t : ℝ ↦ (t : ℂ) ^ (-s)) y *
            ((Real.sin (2 * Real.pi * (n + 1 : ℝ) * y) /
              (Real.pi * (n + 1 : ℝ))) : ℂ) := by
  let u : ℝ → ℂ := fun y ↦ (y : ℂ) ^ (-s)
  let v : ℝ → ℂ := fun y ↦
    ((Real.sin (2 * Real.pi * (n + 1 : ℝ) * y) /
      (Real.pi * (n + 1 : ℝ))) : ℂ)
  let u' : ℝ → ℂ := deriv (fun t : ℝ ↦ (t : ℂ) ^ (-s))
  let v' : ℝ → ℂ := fun y ↦
    ((2 * Real.cos (2 * Real.pi * (n + 1 : ℝ) * y)) : ℂ)
  have hIoo_to_Icc :
      ∀ {x : ℝ}, x ∈ Set.Ioo (min a b) (max a b) → x ∈ Set.Icc a b := by
    intro x hx
    rw [min_eq_left hab.le, max_eq_right hab.le] at hx
    exact Set.Ioo_subset_Icc_self hx
  have h_ibp :
      ∫ y in a..b, u y * v' y =
        u b * v b - u a * v a - ∫ y in a..b, u' y * v y := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (by
        simpa [u, Set.uIcc_of_le hab.le] using
          (Complex.continuousOn_ofReal_cpow (r := -s) (a := a) (b := b) ha))
      (by
        simp [v, Set.uIcc_of_le hab.le]
        fun_prop)
      (by
        intro x hx
        have hx_pos : 0 < x := lt_of_lt_of_le ha (hIoo_to_Icc hx).1
        have hdiff : DifferentiableAt ℝ (fun t : ℝ ↦ (t : ℂ) ^ (-s)) x := by
          by_cases hs : s = 0
          · simp [hs]
          · exact DifferentiableAt.ofReal_cpow_const
              (f := fun x : ℝ ↦ x) (c := -s) differentiableAt_id hx_pos.ne'
              (neg_ne_zero.mpr hs)
        simpa [u, u'] using hdiff.hasDerivAt)
      (by
        intro x _hx
        simpa [v, v'] using hasDerivAt_sine_antideriv n x)
      (by
        have hcont : ContinuousOn u' (Set.uIcc a b) := by
          simpa [u', Set.uIcc_of_le hab.le] using
            (Complex.continuousOn_deriv_ofReal_cpow_neg (s := s) (a := a) (b := b) ha)
        exact hcont.intervalIntegrable)
      (by
        apply ContinuousOn.intervalIntegrable
        simp [v', Set.uIcc_of_le hab.le]
        fun_prop)
  have h_lhs :
      ∫ y in a..b, u y * v' y =
        2 * ∫ y in a..b, (y : ℂ) ^ (-s) *
          Real.cos (2 * Real.pi * (n + 1 : ℝ) * y) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _hy
    simp [u, v']
    ring
  simpa [u, v, u'] using h_lhs.symm.trans h_ibp

end CosineIntegralIBP

section CpowSecondDerivative

private theorem hasDerivAt_deriv_ofReal_cpow_neg (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ ↦ deriv (fun t : ℝ ↦ (t : ℂ) ^ (-s)) y)
      (s * (s + 1) * (x : ℂ) ^ (-s - 2)) x := by
  have hnear : ∀ᶠ y in 𝓝 x, 0 < y := Ioi_mem_nhds hx
  have heq :
      (fun y : ℝ ↦ deriv (fun t : ℝ ↦ (t : ℂ) ^ (-s)) y) =ᶠ[𝓝 x]
        (fun y : ℝ ↦ -s * (y : ℂ) ^ (-s - 1)) := by
    filter_upwards [hnear] with y hy
    exact Complex.deriv_ofReal_cpow_neg s hy
  by_cases hpow : -s - 1 = 0
  · have hconst :
        HasDerivAt (fun _y : ℝ ↦ -s * (1 : ℂ)) 0 x := by
      simpa using (hasDerivAt_const (x := x) (c := -s * (1 : ℂ)))
    have hexp :
        (fun y : ℝ ↦ -s * (y : ℂ) ^ (-s - 1)) = fun _y : ℝ ↦ -s * (1 : ℂ) := by
      ext y
      rw [hpow, cpow_zero]
    have htarget : s * (s + 1) * (x : ℂ) ^ (-s - 2) = 0 := by
      have hs_add : s + 1 = 0 := by
        have hneg : -(s + 1) = 0 := by
          simpa [sub_eq_add_neg, neg_add, add_comm, add_left_comm, add_assoc] using hpow
        exact neg_eq_zero.mp hneg
      simp [hs_add]
    rw [htarget]
    exact hconst.congr_of_eventuallyEq (heq.trans (Filter.EventuallyEq.of_eq hexp))
  · have hbase :
        HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ (-s - 1))
          ((-s - 1) * (x : ℂ) ^ ((-s - 1) - 1)) x :=
      hasDerivAt_ofReal_cpow_const hx.ne' hpow
    have hmul :
        HasDerivAt (fun y : ℝ ↦ -s * (y : ℂ) ^ (-s - 1))
          ((-s) * ((-s - 1) * (x : ℂ) ^ ((-s - 1) - 1))) x :=
      hbase.const_mul (-s)
    have htarget :
        (-s) * ((-s - 1) * (x : ℂ) ^ ((-s - 1) - 1)) =
          s * (s + 1) * (x : ℂ) ^ (-s - 2) := by
      rw [show ((-s - 1) - 1 : ℂ) = -s - 2 by ring]
      ring
    exact (hmul.congr_deriv htarget).congr_of_eventuallyEq heq

private theorem continuousOn_second_deriv_ofReal_cpow_neg (s : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn
      (fun y : ℝ ↦ s * (s + 1) * (y : ℂ) ^ (-s - 2))
      (Set.Icc a b) := by
  exact (continuousOn_const.mul
    (Complex.continuousOn_ofReal_cpow (r := -s - 2) ha))

end CpowSecondDerivative

private theorem hasDerivAt_cos_antideriv (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ ↦
        ((-Real.cos (2 * Real.pi * (n + 1 : ℝ) * y) /
          (2 * Real.pi ^ 2 * (n + 1 : ℝ) ^ 2)) : ℂ))
      ((Real.sin (2 * Real.pi * (n + 1 : ℝ) * x) /
        (Real.pi * (n + 1 : ℝ))) : ℂ) x := by
  have hden : 2 * Real.pi ^ 2 * (n + 1 : ℝ) ^ 2 ≠ 0 := by positivity
  have hcos :
      HasDerivAt
        (fun y : ℝ ↦ Real.cos (2 * Real.pi * (n + 1 : ℝ) * y))
        (-(2 * Real.pi * (n + 1 : ℝ)) *
          Real.sin (2 * Real.pi * (n + 1 : ℝ) * x)) x := by
    convert
      (Real.hasDerivAt_cos (2 * Real.pi * (n + 1 : ℝ) * x)).comp x
        ((hasDerivAt_id x).const_mul (2 * Real.pi * (n + 1 : ℝ))) using 1
    · rfl
    ring
  have hreal :
      HasDerivAt
        (fun y : ℝ ↦
          -Real.cos (2 * Real.pi * (n + 1 : ℝ) * y) /
            (2 * Real.pi ^ 2 * (n + 1 : ℝ) ^ 2))
        (Real.sin (2 * Real.pi * (n + 1 : ℝ) * x) /
          (Real.pi * (n + 1 : ℝ))) x := by
    convert hcos.neg.div_const (2 * Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) using 1
    field_simp [hden]
  simpa using hreal.ofReal_comp

private theorem deriv_kernel_integral_by_parts_cpow {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (s : ℂ) (n : ℕ) :
    ∫ y in a..b,
        deriv (fun t : ℝ ↦ (t : ℂ) ^ (-s)) y *
          ((Real.sin (2 * Real.pi * (n + 1 : ℝ) * y) /
            (Real.pi * (n + 1 : ℝ))) : ℂ) =
      deriv (fun t : ℝ ↦ (t : ℂ) ^ (-s)) b *
          ((-Real.cos (2 * Real.pi * (n + 1 : ℝ) * b) /
            (2 * Real.pi ^ 2 * (n + 1 : ℝ) ^ 2)) : ℂ) -
        deriv (fun t : ℝ ↦ (t : ℂ) ^ (-s)) a *
          ((-Real.cos (2 * Real.pi * (n + 1 : ℝ) * a) /
            (2 * Real.pi ^ 2 * (n + 1 : ℝ) ^ 2)) : ℂ) -
        ∫ y in a..b,
          (s * (s + 1) * (y : ℂ) ^ (-s - 2)) *
            ((-Real.cos (2 * Real.pi * (n + 1 : ℝ) * y) /
              (2 * Real.pi ^ 2 * (n + 1 : ℝ) ^ 2)) : ℂ) := by
  let u : ℝ → ℂ := fun y ↦ deriv (fun t : ℝ ↦ (t : ℂ) ^ (-s)) y
  let v : ℝ → ℂ := fun y ↦
    ((-Real.cos (2 * Real.pi * (n + 1 : ℝ) * y) /
      (2 * Real.pi ^ 2 * (n + 1 : ℝ) ^ 2)) : ℂ)
  let u' : ℝ → ℂ := fun y ↦ s * (s + 1) * (y : ℂ) ^ (-s - 2)
  let v' : ℝ → ℂ := fun y ↦
    ((Real.sin (2 * Real.pi * (n + 1 : ℝ) * y) /
      (Real.pi * (n + 1 : ℝ))) : ℂ)
  have hIoo_to_Icc :
      ∀ {x : ℝ}, x ∈ Set.Ioo (min a b) (max a b) → x ∈ Set.Icc a b := by
    intro x hx
    rw [min_eq_left hab.le, max_eq_right hab.le] at hx
    exact Set.Ioo_subset_Icc_self hx
  have h_ibp :
      ∫ y in a..b, u y * v' y =
        u b * v b - u a * v a - ∫ y in a..b, u' y * v y := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (by
        simpa [u, Set.uIcc_of_le hab.le] using
          (Complex.continuousOn_deriv_ofReal_cpow_neg (s := s) (a := a) (b := b) ha))
      (by
        simp [v, Set.uIcc_of_le hab.le]
        fun_prop)
      (by
        intro x hx
        have hx_pos : 0 < x := lt_of_lt_of_le ha (hIoo_to_Icc hx).1
        simpa [u, u'] using hasDerivAt_deriv_ofReal_cpow_neg s hx_pos)
      (by
        intro x _hx
        simpa [v, v'] using hasDerivAt_cos_antideriv n x)
      (by
        have hcont : ContinuousOn u' (Set.uIcc a b) := by
          simpa [u', Set.uIcc_of_le hab.le] using
            (continuousOn_second_deriv_ofReal_cpow_neg (s := s) (a := a) (b := b) ha)
        exact hcont.intervalIntegrable)
      (by
        apply ContinuousOn.intervalIntegrable
        simp [v', Set.uIcc_of_le hab.le]
        fun_prop)
  simpa [u, v, u', v'] using h_ibp

private theorem summable_one_div_two_pi_sq_nat_add_one_sq :
    Summable fun n : ℕ ↦
      (1 : ℝ) / (2 * Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) := by
  have hp : Summable fun n : ℕ ↦ (1 : ℝ) / (n + 1 : ℝ) ^ 2 := by
    simpa [one_div] using
      ((summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)))
  have hscale := hp.mul_left ((2 * Real.pi ^ 2)⁻¹)
  convert hscale using 1
  ext n
  have hden : 2 * Real.pi ^ 2 ≠ 0 := by positivity
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hden, hn]

section EulerBridge

open Interval MeasureTheory

private theorem finite_euler_cpow_neg {a b : ℝ} (ha : 0 < a) (hab : a < b) (s : ℂ) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (k : ℂ) ^ (-s) =
      (a : ℂ) ^ (-s) * GuthMaynard.NativePNT.B1 a - (b : ℂ) ^ (-s) * GuthMaynard.NativePNT.B1 b +
        (∫ t in a..b, (t : ℂ) ^ (-s)) +
        ∫ t in a..b, deriv (fun t : ℝ ↦ (t : ℂ) ^ (-s)) t * GuthMaynard.NativePNT.B1 t := by
  exact GuthMaynard.NativePNT.sum_eq_integral_add_integral_deriv (𝕜 := ℂ)
    (a := a) (b := b) (f := fun t : ℝ ↦ (t : ℂ) ^ (-s))
    (le_of_lt ha) (le_of_lt hab)
    (fun t ht ↦ by
      have ht_pos : 0 < t := lt_of_lt_of_le ha ht.1
      by_cases hs : s = 0
      · simp [hs]
      · exact DifferentiableAt.ofReal_cpow_const
          (f := fun x : ℝ ↦ x) (c := -s) differentiableAt_id ht_pos.ne'
          (neg_ne_zero.mpr hs))
    (by
      simpa [Set.uIcc_of_le (le_of_lt hab)] using
        (Complex.continuousOn_deriv_ofReal_cpow_neg (s := s) (a := a) (b := b) ha))

end EulerBridge

section FourierPartialSums

private theorem sum_Icc_one_eq_sum_range_succ {α : Type*} [AddCommMonoid α] (F : ℕ → α) :
    ∀ N : ℕ, ∑ n ∈ Icc 1 N, F n = ∑ n ∈ range N, F (n + 1)
  | 0 => by simp
  | N + 1 => by
      rw [sum_range_succ, sum_Icc_succ_top]
      · rw [sum_Icc_one_eq_sum_range_succ F N]
      · omega

private theorem fourier_partial_sum_eq_range_cos (s : ℂ) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (N : ℕ) :
    let f : ℝ → ℂ := fun y ↦
      if a ≤ y ∧ y ≤ b then (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) else 0
    ∑ n ∈ Icc 1 N, (FourierTransform.fourier f n + FourierTransform.fourier f (-n)) =
      ∑ n ∈ range N,
        2 * ∫ y in a..b, (y : ℂ) ^ (-s) * Real.cos (2 * π * (n + 1) * y) := by
  dsimp only
  rw [sum_Icc_one_eq_sum_range_succ]
  apply sum_congr rfl
  intro n _hn
  simpa using (lemma_abadsumas_sum_fourier (s := s) (a := a) (b := b) ha hab n)

end FourierPartialSums

section FourierIBPDecomposition

private theorem fourier_partial_sum_eq_boundary_sub_deriv_kernel (s : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (N : ℕ) :
    let f : ℝ → ℂ := fun y ↦
      if a ≤ y ∧ y ≤ b then (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) else 0
    ∑ n ∈ Icc 1 N, (FourierTransform.fourier f n + FourierTransform.fourier f (-n)) =
      ((b : ℂ) ^ (-s) *
          ((∑ n ∈ range N,
            Real.sin (2 * Real.pi * (n + 1 : ℝ) * b) /
              (Real.pi * (n + 1 : ℝ))) : ℂ) -
        (a : ℂ) ^ (-s) *
          ((∑ n ∈ range N,
            Real.sin (2 * Real.pi * (n + 1 : ℝ) * a) /
              (Real.pi * (n + 1 : ℝ))) : ℂ)) -
        ∑ n ∈ range N,
          ∫ y in a..b,
            deriv (fun t : ℝ ↦ (t : ℂ) ^ (-s)) y *
              ((Real.sin (2 * Real.pi * (n + 1 : ℝ) * y) /
                (Real.pi * (n + 1 : ℝ))) : ℂ) := by
  dsimp only
  rw [fourier_partial_sum_eq_range_cos (s := s) (a := a) (b := b) ha hab N]
  calc
    ∑ n ∈ range N,
        2 * ∫ y in a..b, (y : ℂ) ^ (-s) *
          Real.cos (2 * Real.pi * (n + 1 : ℝ) * y)
        = ∑ n ∈ range N,
          ((b : ℂ) ^ (-s) *
              ((Real.sin (2 * Real.pi * (n + 1 : ℝ) * b) /
                (Real.pi * (n + 1 : ℝ))) : ℂ) -
            (a : ℂ) ^ (-s) *
              ((Real.sin (2 * Real.pi * (n + 1 : ℝ) * a) /
                (Real.pi * (n + 1 : ℝ))) : ℂ) -
            ∫ y in a..b,
              deriv (fun t : ℝ ↦ (t : ℂ) ^ (-s)) y *
                ((Real.sin (2 * Real.pi * (n + 1 : ℝ) * y) /
                  (Real.pi * (n + 1 : ℝ))) : ℂ)) := by
          apply sum_congr rfl
          intro n _hn
          exact cosine_integral_by_parts_cpow ha hab s n
    _ = ((b : ℂ) ^ (-s) *
          ((∑ n ∈ range N,
            Real.sin (2 * Real.pi * (n + 1 : ℝ) * b) /
              (Real.pi * (n + 1 : ℝ))) : ℂ) -
        (a : ℂ) ^ (-s) *
          ((∑ n ∈ range N,
            Real.sin (2 * Real.pi * (n + 1 : ℝ) * a) /
              (Real.pi * (n + 1 : ℝ))) : ℂ)) -
        ∑ n ∈ range N,
          ∫ y in a..b,
            deriv (fun t : ℝ ↦ (t : ℂ) ^ (-s)) y *
              ((Real.sin (2 * Real.pi * (n + 1 : ℝ) * y) /
                (Real.pi * (n + 1 : ℝ))) : ℂ) := by
          simp [sum_sub_distrib, mul_sum]

end FourierIBPDecomposition

section MainIntegral

private theorem integral_cpow_neg_eq_main {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {s : ℂ} (hs1 : s ≠ 1) :
    (∫ x in a..b, (x : ℂ) ^ (-s)) =
      ((b : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1
  · rw [(by ring : -s + 1 = 1 - s)]
  · right
    refine ⟨?_, ?_⟩
    · intro hs
      exact hs1 (neg_inj.mp hs)
    · intro hx
      have hx_pos : 0 < (0 : ℝ) := by
        exact lt_of_lt_of_le ha ((Set.mem_uIcc.mp hx).elim (fun h ↦ h.1) (fun h ↦ le_trans hab.le h.1))
      exact hx_pos.false

end MainIntegral

private theorem cos_antideriv_norm_bound (n : ℕ) (x : ℝ) :
    ‖((-Real.cos (2 * Real.pi * (n + 1 : ℝ) * x) /
      (2 * Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) : ℝ) : ℂ)‖ ≤
        1 / (2 * Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) := by
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi ^ 2 * (n + 1 : ℝ) ^ 2)]
  gcongr
  exact Real.abs_cos_le_one _

private theorem halfInteger_fract {x : ℝ} (hx : x.IsHalfInteger) : Int.fract x=1/2 := by
  obtain ⟨k,rfl⟩ := hx
  rw [add_comm,Int.fract_add_intCast,Int.fract_eq_self.mpr (by norm_num)]

private theorem halfInteger_sine_zero {x : ℝ} (hx : x.IsHalfInteger) (n : ℕ) :
    Real.sin (2*π*(n+1:ℝ)*x)=0 := by
  obtain ⟨k,rfl⟩ := hx
  convert Real.sin_int_mul_pi ((2*k+1)*(n+1 : ℤ)) using 1
  push_cast
  ring

open DhimanKadiriQuesadaHerrera2026 (expMode sawtoothMode integral_mul_sawtooth_eq_tsum)

private theorem sawtoothMode_succ (n : ℕ) (x : ℝ) :
    sawtoothMode (n+1) x = -((Real.sin (2*π*(n+1:ℝ)*x)/(π*(n+1:ℝ)) : ℝ) : ℂ) := by
  simp only [sawtoothMode,expMode,Complex.ofReal_div,Complex.ofReal_sin]
  push_cast
  let t : ℂ := 2*π*(n+1:ℂ)*x
  rw [show I * (-2*π*(n+1:ℂ)*x) = -t*I by dsimp [t]; ring,
    show I * (-2*π*(n+1:ℂ)*(-x)) = t*I by dsimp [t]; ring]
  rw [← neg_div]
  change (exp (-t*I)-exp (t*I))/(2*π*I*(n+1:ℂ)) = -sin t/(π*(n+1:ℂ))
  have hi : I*I=(-1:ℂ) := Complex.I_mul_I
  have he : exp (-t*I)-exp (t*I) = -2*sin t*I := by
    linear_combination I * Complex.two_sin (x:=t) + (exp (-t*I)-exp (t*I))*hi
  rw [he]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hn : (n+1:ℂ) ≠ 0 := Nat.cast_add_one_ne_zero _
  field_simp [hπ,hn,I_ne_zero]

/-- The integrated sine kernel is summable by one integration by parts.
Its Abel sum is therefore its ordinary sum. -/
private theorem tendsto_deriv_kernel_to_B1 {a b : ℝ} (ha : 0 < a) (hab : a < b) (s : ℂ) :
    Tendsto
      (fun N : ℕ ↦ -(∑ n∈range N, ∫ y in a..b,
        deriv (fun t : ℝ ↦ (t : ℂ)^(-s)) y *
          ((Real.sin (2*π*(n+1:ℝ)*y)/(π*(n+1:ℝ)) : ℝ) : ℂ)))
      atTop (𝓝 (∫ y in a..b, deriv (fun t : ℝ ↦ (t : ℂ)^(-s)) y * GuthMaynard.NativePNT.B1 y)) := by
  let u (y : ℝ) := deriv (fun t : ℝ => (t : ℂ)^(-s)) y
  let v (y : ℝ) := s*(s+1)*(y:ℂ)^(-s-2)
  let C (n : ℕ) (x : ℝ) : ℂ :=
    ((-Real.cos (2*π*(n+1:ℝ)*x)/(2*π^2*(n+1:ℝ)^2) : ℝ) : ℂ)
  have hsC x : Summable (fun n => C n x) :=
    summable_one_div_two_pi_sq_nat_add_one_sq.of_norm_bounded (fun n => cos_antideriv_norm_bound n x)
  obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_second_deriv_ofReal_cpow_neg (b:=b) s ha)
  have hK0 := (norm_nonneg _).trans (hK a (left_mem_Icc.mpr hab.le))
  have hsI : Summable (fun n => ∫ y in a..b,v y*C n y) := by
    refine (summable_one_div_two_pi_sq_nat_add_one_sq.mul_left (K*|b-a|)).of_norm_bounded (fun n => ?_)
    have hnorm (y : ℝ) (hy : y ∈ uIoc a b) : ‖v y*C n y‖ ≤ K*(1/(2*π^2*(n+1:ℝ)^2)) := by
      rw [uIoc_of_le hab.le] at hy
      rw [norm_mul]
      exact mul_le_mul (hK y ⟨hy.1.le,hy.2⟩) (cos_antideriv_norm_bound n y) (norm_nonneg _) hK0
    exact (intervalIntegral.norm_integral_le_of_norm_le_const hnorm).trans_eq (mul_right_comm ..)
  have hs : Summable (fun n : ℕ => ∫ y in a..b,u y*sawtoothMode n y) := by
    apply (summable_nat_add_iff 1).mp
    refine ((((hsC b).mul_left (u b)).sub ((hsC a).mul_left (u a))).sub hsI).neg.congr (fun n => ?_)
    simpa only [sawtoothMode_succ,mul_neg,intervalIntegral.integral_neg,neg_inj,
      u,v,C,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat] using
      (deriv_kernel_integral_by_parts_cpow ha hab s n).symm
  have hu : IntervalIntegrable u volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab.le]
    exact Complex.continuousOn_deriv_ofReal_cpow_neg (s:=s) ha
  have he : (∫ y in a..b,u y*GuthMaynard.NativePNT.B1 y) =
      ∑' n : ℕ, ∫ y in a..b,u y*sawtoothMode n y := by
    simp only [intervalIntegral.integral_of_le hab.le]
    rw [← integral_mul_sawtooth_eq_tsum hu.1 (by simpa only [intervalIntegral.integral_of_le hab.le] using hs)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    simp only [B1_eq_fract_sub_half (ha.le.trans hy.1.le)]
  rw [he]
  have hh := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine hh.congr (fun n => ?_)
  dsimp only [Function.comp_def]
  rw [Finset.sum_range_succ']
  simp only [show sawtoothMode 0 = 0 by ext x; simp [sawtoothMode], Pi.zero_apply,
    mul_zero, intervalIntegral.integral_zero, add_zero, u, sawtoothMode_succ,
    mul_neg,intervalIntegral.integral_neg,Finset.sum_neg_distrib]

private theorem lemma_abadusepoisson {a b : ℝ} (ha : a.IsHalfInteger) (hb : b.IsHalfInteger)
    (hab : b > a) (ha' : 0 < a) {s : ℂ} (hs1 : s ≠ 1) :
    let f : ℝ → ℂ := fun y ↦
      if a ≤ y ∧ y ≤ b then (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) else 0
    ∃ L : ℂ, Filter.atTop.Tendsto
      (fun (N : ℕ) ↦ ∑ n ∈ Icc 1 N,
        (FourierTransform.fourier f n + FourierTransform.fourier f (-n))) (nhds L) ∧
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (n : ℂ) ^ (-s) =
        ((b ^ (1 - s) : ℂ) - (a ^ (1 - s) : ℂ)) / (1 - s) + L := by
  dsimp only
  refine ⟨∫ y in a..b, deriv (fun t : ℝ => (t:ℂ)^(-s)) y * GuthMaynard.NativePNT.B1 y,?_,?_⟩
  · refine (tendsto_deriv_kernel_to_B1 ha' hab s).congr (fun N => ?_)
    rw [fourier_partial_sum_eq_boundary_sub_deriv_kernel s ha' hab N]
    simp only [halfInteger_sine_zero ha, halfInteger_sine_zero hb, zero_div, Finset.sum_const_zero,
      Complex.ofReal_zero, mul_zero, sub_zero, zero_sub, Complex.ofReal_div, Complex.ofReal_mul]
  · rw [finite_euler_cpow_neg ha' hab s,integral_cpow_neg_eq_main ha' hab hs1,
      B1_eq_fract_sub_half ha'.le,B1_eq_fract_sub_half (ha'.trans hab).le,
      halfInteger_fract ha,halfInteger_fract hb]
    simp

private theorem csc_cot_sub {z : ℂ} (hz : z ∈ integerComplement) :
    (π : ℂ) / Complex.sin (π*z) = π * Complex.cot (π*(z/2)) - π * Complex.cot (π*z) := by
  let u : ℂ := π*(z/2)
  have hu : (π:ℂ)*z = 2*u := by dsimp [u]; ring
  have h := sin_pi_mul_ne_zero hz
  rw [hu, Complex.sin_two_mul] at h
  have hs : Complex.sin u ≠ 0 := by intro he; simp [he] at h
  have hc : Complex.cos u ≠ 0 := by intro he; simp [he] at h
  change _ = π * Complex.cot u - _
  rw [hu,Complex.cot,Complex.cot,Complex.sin_two_mul,Complex.cos_two_mul]
  field_simp
  ring

private theorem summable_alternating_cotTerm {z : ℂ} (hz : z ∈ integerComplement) :
    Summable (fun n : ℕ => (-1 : ℂ)^(n+1)*cotTerm z n) :=
  (summable_cotTerm hz).norm.of_norm_bounded fun n => by simp

private theorem csc_series {z : ℂ} (hz : z ∈ integerComplement) :
    (π : ℂ) / Complex.sin (π*z) = 1/z + ∑' n : ℕ, (-1 : ℂ)^(n+1)*cotTerm z n := by
  have hz2 : z/2 ∈ integerComplement := by
    rintro ⟨k,h⟩
    exact hz ⟨2*k, by push_cast; linear_combination 2*h⟩
  let f (n : ℕ) := cotTerm z n
  let g (n : ℕ) := (-1 : ℂ)^(n+1)*f n
  have hsf : Summable f := summable_cotTerm hz
  have hsg : Summable g := summable_alternating_cotTerm hz
  have inj₀ : Function.Injective (fun n : ℕ => 2*n) := by intro a b h; dsimp at h; omega
  have inj₁ : Function.Injective (fun n : ℕ => 2*n+1) := by intro a b h; dsimp at h; omega
  have hodd : Summable (fun n : ℕ => f (2*n+1)) := hsf.comp_injective inj₁
  have h₂ : (∑' n : ℕ, cotTerm (z/2) n) = 2*∑' n : ℕ, f (2*n+1) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [f,cotTerm,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
    rw [show z/2-((n:ℂ)+1) = (z-(2*n+1+1))/2 by ring,
      show z/2+((n:ℂ)+1) = (z+(2*n+1+1))/2 by ring,
      div_div_eq_mul_div,div_div_eq_mul_div]
    ring
  have he : (∑' n : ℕ, g (2*n)) = -(∑' n : ℕ, f (2*n)) := by
    simp [g,pow_succ,pow_mul,tsum_neg]
  have ho : (∑' n : ℕ, g (2*n+1)) = ∑' n : ℕ, f (2*n+1) := by
    simp [g,pow_succ,pow_mul]
  have hf := tsum_even_add_odd (hsf.comp_injective inj₀) hodd
  have hg := tsum_even_add_odd (hsg.comp_injective inj₀) (hsg.comp_injective inj₁)
  change (∑' n : ℕ, g (2*n)) + (∑' n : ℕ, g (2*n+1)) = _ at hg
  rw [he,ho] at hg
  have hc₁ := cot_series_rep' hz
  have hc₂ := cot_series_rep' hz2
  rw [h₂] at hc₂
  change _ = 1/z + ∑' n : ℕ, g n
  rw [csc_cot_sub hz, ← hg]
  -- Apply the two cotangent expansions with the even and odd parts separated.
  change (_ - _ = ∑' n : ℕ, f n) at hc₁
  rw [← hf] at hc₁
  linear_combination hc₂ - hc₁

private theorem hasDerivAt_neg_pi_cot {z : ℂ} (hz : z ∈ integerComplement) :
    HasDerivAt (fun w ↦ -(π : ℂ) * Complex.cot (π * w))
      (π ^ 2 / sin (π * z) ^ 2) z := by
  have hsin := sin_pi_mul_ne_zero hz
  have h : HasDerivAt Complex.cot (-(sin (π * z) ^ 2)⁻¹) (π * z) := by
    unfold Complex.cot
    convert (Complex.hasDerivAt_cos (π * z)).div (Complex.hasDerivAt_sin (π * z)) hsin using 1
    field_simp
    linear_combination Complex.sin_sq_add_cos_sq (π * z)
  convert ((h.comp z ((hasDerivAt_id z).const_mul (π : ℂ))).const_mul (-(π : ℂ))) using 1
  · rfl
  · ring

private theorem summable_inverse_square_int (z : ℂ) :
    Summable (fun n : ℤ => (1 : ℂ)/(z-n)^2) := by
  refine (EisensteinSeries.linear_right_summable (-z) 1 (k:=2) (by norm_num)).congr fun n => ?_
  simp only [one_div,Int.cast_one,one_mul,zpow_ofNat]
  rw [show -z+(n:ℂ) = -(z-n) by ring,neg_sq]

open Metric in
set_option maxHeartbeats 600000 in
private theorem lemma_abadeulmit2 {z : ℂ} (hz : z ∈ integerComplement) :
    π ^ 2 / (sin (π * z) ^ 2) = ∑' n : ℤ, 1 / (z - n) ^ 2 := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp Complex.isOpen_compl_range_intCast z hz
  have hball' : ball z (r/2) ⊆ ball z r := ball_subset_ball (by linarith)
  have hnz (k : ℤ) : r ≤ ‖z - (k : ℂ)‖ := by
    by_contra! hk
    exact hball (show (k:ℂ) ∈ ball z r by simpa [dist_eq_norm,norm_sub_rev] using hk) ⟨k,rfl⟩
  have hloc (w : ℂ) (hw : w ∈ ball z (r/2)) (k : ℤ) :
      ‖1 / (w - (k : ℂ)) ^ 2‖ ≤ 4 * ‖1 / (z - (k : ℂ)) ^ 2‖ := by
    have ht := dist_triangle z w (k : ℂ)
    simp only [dist_eq_norm] at ht
    have hwr : ‖z-w‖ < r/2 := by simpa [dist_eq_norm,norm_sub_rev] using hw
    have h := hnz k
    have hlow : ‖z - (k : ℂ)‖/2 ≤ ‖w - (k : ℂ)‖ := by linarith
    simp only [norm_div,norm_one,norm_pow]
    calc
      _ ≤ 1 / (‖z - (k : ℂ)‖/2)^2 := one_div_le_one_div_of_le
        (by have := lt_of_lt_of_le hr (hnz k); positivity) (pow_le_pow_left₀ (by positivity) hlow 2)
      _ = _ := by ring
  let f (w : ℂ) (n : ℤ) := 1 / (w - (n : ℂ)) ^ 2
  have hs : Summable (f z) := summable_inverse_square_int z
  have hp : Summable (fun n : ℕ => f z ((n:ℤ)+1)) :=
    hs.comp_injective (i := fun n : ℕ => (n:ℤ)+1) (fun m n h => by simpa using h)
  have hm : Summable (fun n : ℕ => f z (-((n:ℤ)+1))) :=
    hs.comp_injective (i := fun n : ℕ => -((n:ℤ)+1)) (fun m n h => by simpa using h)
  let g (n : ℕ) (w : ℂ) := -(f w ((n:ℤ)+1) + f w (-((n:ℤ)+1)))
  have hg (n : ℕ) (w : ℂ) (hw : w ∈ ball z (r/2)) : HasDerivAt (fun x => cotTerm x n) (g n w) w := by
    have hne (k : ℤ) : w - (k : ℂ) ≠ 0 := sub_ne_zero.mpr fun h => hball (hball' hw) ⟨k,h.symm⟩
    have hd (k : ℤ) : HasDerivAt (fun x : ℂ => (x - (k:ℂ))⁻¹) (-f w k) w := by
      simpa only [f,one_div,one_mul,neg_div,Pi.inv_def,id_eq] using ((hasDerivAt_id w).sub_const (k:ℂ)).inv (hne k)
    convert (hd ((n:ℤ)+1)).add (hd (-((n:ℤ)+1))) using 1
    · ext x
      simp [cotTerm,one_div]; ring
    · simp [g,add_comm]
  let u (n : ℕ) := 4 * ‖f z ((n:ℤ)+1)‖ + 4 * ‖f z (-((n:ℤ)+1))‖
  have hu : Summable u := (hp.norm.mul_left 4).add (hm.norm.mul_left 4)
  have hgu (n : ℕ) (w : ℂ) (hw : w ∈ ball z (r/2)) : ‖g n w‖ ≤ u n := by
    rw [show g n w = -(f w ((n:ℤ)+1) + f w (-((n:ℤ)+1))) from rfl,norm_neg]
    exact (norm_add_le _ _).trans (add_le_add (hloc w hw _) (hloc w hw _))
  have hz' : z ∈ ball z (r/2) := mem_ball_self (by positivity)
  have hd := hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball z _).isPreconnected
    hg hgu hz' (summable_cotTerm hz) hz'
  have he : (fun w => (π : ℂ) * Complex.cot (π * w) - 1/w) =ᶠ[𝓝 z] fun w => ∑' n : ℕ, cotTerm w n := by
    filter_upwards [ball_mem_nhds z (by positivity : 0 < r/2)] with w hw
    exact cot_series_rep' (hball (hball' hw))
  have heq := (hd.congr_of_eventuallyEq he).unique (by
    simpa only [neg_mul,neg_neg,one_div,Pi.neg_def,Pi.sub_def] using
      (hasDerivAt_neg_pi_cot hz).neg.sub (hasDerivAt_inv (integerComplement.ne_zero hz)))
  have ht := tsum_of_add_one_of_neg_add_one hp hm
  change _ = ∑' n : ℤ,f z n
  rw [ht]
  simp only [g,tsum_neg] at heq
  rw [Summable.tsum_add hp hm] at heq
  simp only [f,Int.cast_zero,sub_zero,one_div] at heq ⊢
  linear_combination heq

private theorem lemma_abadimpseri (ϑ : ℝ) (hϑ : |ϑ| < 1) :
    ∑' n : ℕ, (1 / ((n + 1 : ℝ) - ϑ) ^ 3 + 1 / ((n + 1 : ℝ) + ϑ) ^ 3) ≤
      1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1 := by
  have h_sum_bound : ∀ n : ℕ, (1 / (n + 1 - ϑ) ^ 3 + 1 / (n + 1 + ϑ) ^ 3) ≤
      (1 / (n + 1 - |ϑ|) ^ 3 + 1 / (n + 1 + |ϑ|) ^ 3) := by intro n; cases abs_cases ϑ <;> grind
  have h_sum_bound_endpoints : (∑' n : ℕ, (1 / (n + 1 - |ϑ|) ^ 3 + 1 / (n + 1 + |ϑ|) ^ 3)) ≤
      (1 / (1 - |ϑ|) ^ 3) + 2 * (riemannZeta 3).re - 1 := by
    have h_sum_endpoints_bound : (∑' n : ℕ, (1 / (n + 2 - |ϑ|) ^ 3 + 1 / (n + 1 + |ϑ|) ^ 3)) ≤
        2 * (riemannZeta 3).re - 1 := by
      have h_term_bound : ∀ n : ℕ, (1 / (n + 2 - |ϑ|) ^ 3 + 1 / (n + 1 + |ϑ|) ^ 3) ≤
          (1 / (n + 1) ^ 3 + 1 / (n + 2) ^ 3) := by
        intro n
        rw [div_add_div, div_add_div, div_le_div_iff₀] <;> try positivity
        · have h_simp : (n + 1 + |ϑ|) ^ 3 + (n + 2 - |ϑ|) ^ 3 ≤ (n + 1) ^ 3 + (n + 2) ^ 3 := by
            nlinarith [abs_nonneg ϑ, pow_two_nonneg (|ϑ| : ℝ), pow_two_nonneg (n : ℝ),
              mul_lt_mul_of_pos_left hϑ <| Nat.cast_add_one_pos n]
          field_simp
          refine le_trans (mul_le_mul_of_nonneg_left h_simp <| by positivity) ?_
          have h_simp : (n + 1 : ℝ) ^ 3 * (n + 2) ^ 3 ≤ (n + 1 + |ϑ|) ^ 3 * (n + 2 - |ϑ|) ^ 3 := by
            rw [← mul_pow, ← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg ϑ]) _
          exact mul_le_mul h_simp (by linarith) (by positivity)
            (by exact mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by linarith [abs_nonneg ϑ]) _))
        · exact mul_pos (pow_pos (by linarith [abs_nonneg ϑ]) _) (pow_pos (by linarith [abs_nonneg ϑ]) _)
        · exact pow_ne_zero _ (by linarith [abs_nonneg ϑ])
      refine le_trans (Summable.tsum_le_tsum h_term_bound ?_ ?_) ?_
      · exact of_nonneg_of_le (fun n ↦ add_nonneg (one_div_nonneg.mpr (pow_nonneg (by linarith [abs_nonneg ϑ]) _))
          (one_div_nonneg.mpr (pow_nonneg (by linarith [abs_nonneg ϑ]) _)))
            h_term_bound (add (by exact_mod_cast summable_nat_add_iff 1 |>.2 <| summable_one_div_nat_pow.2 <| by omega)
              (by exact_mod_cast summable_nat_add_iff 2 |>.2 <| summable_one_div_nat_pow.2 <| by omega))
      · exact add (by simpa using summable_nat_add_iff 1 |>.2 <| summable_one_div_nat_pow.2 <| by omega)
          (by simpa using summable_nat_add_iff 2 |>.2 <| summable_one_div_nat_pow.2 <| by omega)
      · have h_sum_zeta : ∑' n : ℕ, (1 / (n + 1 : ℝ) ^ 3 + 1 / (n + 2 : ℝ) ^ 3) =
            2 * (∑' n : ℕ, (1 / (n + 1 : ℝ) ^ 3)) - 1 := by
          rw [Summable.tsum_add, Summable.tsum_eq_zero_add] <;> norm_num
          · norm_num [add_assoc]; ring
          · exact_mod_cast summable_nat_add_iff 1 |>.2 <| summable_nat_pow_inv.2 <| by omega
          · exact_mod_cast summable_nat_add_iff 1 |>.2 <| summable_nat_pow_inv.2 <| by omega
          · exact_mod_cast summable_nat_add_iff 2 |>.2 <| summable_nat_pow_inv.2 <| by omega
        convert h_sum_zeta.le using 2
        erw [zeta_eq_tsum_one_div_nat_add_one_cpow] <;> norm_num
        · have hh := congrArg Complex.re
            (Complex.ofReal_tsum (L := .unconditional ℕ) (fun n : ℕ => (((n : ℝ) + 1) ^ 3)⁻¹))
          simpa using hh.symm
    rw [Summable.tsum_eq_zero_add]
    · norm_num [add_assoc, add_left_comm, add_comm, div_eq_mul_inv, mul_add, mul_comm,
        mul_left_comm, tsum_mul_left] at *
      have hs₁ : Summable fun n : ℕ ↦ ((|ϑ| + (n + 1)) ^ 3)⁻¹ :=
        of_nonneg_of_le (fun n ↦ inv_nonneg.2 (pow_nonneg (by positivity) _))
          (fun n ↦ by simpa using inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity)
            (show (|ϑ| + (n + 1) : ℝ) ≥ n + 1 by linarith [abs_nonneg ϑ]) 3))
          (summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 <| by omega)
      have hs₂ : Summable fun n : ℕ ↦ (((n : ℝ) + 2 - |ϑ|) ^ 3)⁻¹ :=
        of_nonneg_of_le (fun n ↦ inv_nonneg.2 (pow_nonneg (by linarith [abs_nonneg ϑ]) _))
          (fun n ↦ by rw [inv_le_comm₀] <;> norm_num <;> ring_nf <;>
            nlinarith [abs_nonneg ϑ, pow_two_nonneg ((n : ℝ) + 1 - |ϑ|)])
          (summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two)
      rw [Summable.tsum_add hs₁ hs₂] at h_sum_endpoints_bound
      rw [Summable.tsum_add]
      · rw [show (∑' b : ℕ, ((|ϑ| + (b + 2)) ^ 3)⁻¹) = (∑' b : ℕ, ((|ϑ| + (b + 1)) ^ 3)⁻¹) - ((|ϑ| + 1) ^ 3)⁻¹ from ?_]
        · nlinarith [show 0 < (|ϑ| + 1) ^ 3 by positivity, inv_mul_cancel₀ (show (|ϑ| + 1) ^ 3 ≠ 0 by positivity)]
        · rw [eq_comm, Summable.tsum_eq_zero_add]
          · norm_num [add_assoc]
          · exact hs₁
      · exact_mod_cast of_nonneg_of_le (fun n ↦ by positivity)
          (fun n ↦ by rw [inv_le_comm₀] <;> norm_num <;> ring_nf <;> nlinarith only [abs_nonneg ϑ, hϑ])
            (summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two)
      · exact hs₂
    · refine Summable.add ?_ ?_
      · have : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ 3) := summable_one_div_nat_pow.2 (by omega)
        rw [← summable_nat_add_iff 1] at this ⊢
        exact of_nonneg_of_le (fun n ↦ one_div_nonneg.mpr (pow_nonneg (by cases abs_cases ϑ <;> linarith) _))
          (fun n ↦ one_div_le_one_div_of_le (by positivity)
            (pow_le_pow_left₀ (by positivity) (by cases abs_cases ϑ <;> linarith) _)) this
      · exact_mod_cast of_nonneg_of_le (fun n ↦ by positivity)
          (fun n ↦ by simpa using inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity)
            (show (n : ℝ) + 1 + |ϑ| ≥ n + 1 by linarith [abs_nonneg ϑ]) 3))
          (summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 <| by omega)
  refine le_trans (Summable.tsum_le_tsum h_sum_bound ?_ ?_) h_sum_bound_endpoints
  · have h_bound : ∀ n : ℕ,
        (1 / (n + 1 - ϑ) ^ 3 + 1 / (n + 1 + ϑ) ^ 3) ≤ 2 / (n + 1 - |ϑ|) ^ 3 := fun n ↦ by
      have : (1 / (n + 1 - ϑ) ^ 3 + 1 / (n + 1 + ϑ) ^ 3) ≤
          (1 / (n + 1 - |ϑ|) ^ 3 + 1 / (n + 1 - |ϑ|) ^ 3) := by
        cases abs_cases ϑ <;> simp only [add_le_add_iff_left, one_div, sub_neg_eq_add, add_le_add_iff_right, *]
        · exact inv_anti₀ (pow_pos (by linarith) _) (by gcongr <;> linarith)
        · exact inv_anti₀ (pow_pos (by linarith) _)
            (pow_le_pow_left₀ (by linarith) (by linarith) _)
      exact this.trans_eq (by ring)
    refine of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ h_bound n) ?_
    · exact add_nonneg (one_div_nonneg.mpr (pow_nonneg (by linarith [abs_lt.mp hϑ]) _))
        (one_div_nonneg.mpr (pow_nonneg (by linarith [abs_lt.mp hϑ]) _))
    · have : Summable (fun n : ℕ ↦ 2 / (n : ℝ) ^ 3) :=
        mul_left 2 <| Real.summable_nat_pow_inv.2 (by norm_num : (1 : ℕ) < 3)
      rw [← summable_nat_add_iff 1] at this ⊢
      exact of_nonneg_of_le (fun n ↦ div_nonneg zero_le_two (pow_nonneg (by linarith [abs_nonneg ϑ]) _))
        (fun n ↦ div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by linarith [abs_nonneg ϑ]) (by linarith [abs_nonneg ϑ]) _)) this
  · refine add ?_ ?_
    · rw [← summable_nat_add_iff 1]
      simp only [one_div, Nat.cast_add, Nat.cast_one] at *
      exact of_nonneg_of_le (fun n ↦ inv_nonneg.2 (pow_nonneg (by linarith [abs_nonneg ϑ]) _))
        (fun n ↦ by rw [inv_le_comm₀] <;> norm_num <;> ring_nf <;>
          nlinarith [abs_nonneg ϑ, pow_two_nonneg ((n : ℝ) ^ 2), pow_two_nonneg ((n : ℝ) + 1),
            pow_two_nonneg ((n : ℝ) + 1 - |ϑ|)]) (summable_nat_add_iff 1 |>.2 <| summable_one_div_nat_pow.2 one_lt_two)
    · exact of_nonneg_of_le (fun n ↦ by positivity)
        (fun n ↦ by simpa using inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity)
          (show (n : ℝ) + 1 + |ϑ| ≥ n + 1 by linarith [abs_nonneg ϑ]) 3))
            (summable_nat_add_iff 1 |>.2 <| summable_one_div_nat_pow.2 <| by omega)

private theorem lemma_abadsumas_not_in_integerComplement {ϑ : ℝ} (hϑ_lt : |ϑ| < 1) (hϑ : ϑ ≠ 0) :
    (ϑ : ℂ) ∈ integerComplement := by
  simp only [integerComplement, Set.mem_compl_iff, Set.mem_range, not_exists]
  intro n hn
  have hϑ_eq : ϑ = (n : ℝ) := by exact_mod_cast hn.symm
  have : |n| < 1 := by exact_mod_cast (hϑ_eq ▸ hϑ_lt : |(n : ℝ)| < 1)
  exact hϑ <| hϑ_eq.trans <| by rw [abs_lt] at this; exact_mod_cast (show n = 0 by omega)

private theorem alternating_theta_eq_cotTerm {θ : ℝ} (hθ : |θ| < 1) (n : ℕ) :
    ((-1 : ℂ)^(n+2)*2*θ/(((n:ℂ)+1)^2-(θ:ℂ)^2)) = (-1 : ℂ)^(n+1)*cotTerm θ n := by
  have hp : (n:ℝ)+1+θ > 0 := by linarith [(abs_lt.mp hθ).1, Nat.cast_nonneg (α:=ℝ) n]
  have hm : θ-((n:ℝ)+1) < 0 := by linarith [(abs_lt.mp hθ).2, Nat.cast_nonneg (α:=ℝ) n]
  have hp' : (θ:ℂ)+((n:ℂ)+1) ≠ 0 := by exact_mod_cast (by linarith : θ+((n:ℝ)+1) ≠ 0)
  have hm' : (θ:ℂ)-((n:ℂ)+1) ≠ 0 := by exact_mod_cast hm.ne
  rw [show ((n:ℂ)+1)^2-(θ:ℂ)^2 = -((θ:ℂ)-((n:ℂ)+1))*((θ:ℂ)+((n:ℂ)+1)) by ring,
    pow_succ, cotTerm]
  field_simp
  ring

private theorem lemma_abadsumas_summable_alternating_theta (θ : ℝ) (hθ : |θ| < 1) :
    Summable (fun n : ℕ ↦ ((-1) ^ (n + 2) * 2 * θ / ((n + 1) ^ 2 - θ ^ 2) : ℂ)) := by
  by_cases hz : θ=0
  · simp [hz]
  simpa only [alternating_theta_eq_cotTerm hθ] using
    summable_alternating_cotTerm (lemma_abadsumas_not_in_integerComplement hθ hz)

private theorem lemma_abadsumas_sum_main_term (θ : ℝ) (hθ : |θ| < 1) :
    ∑' n : ℕ, (-1 : ℂ)^(n+2)*2*θ/(((n:ℂ)+1)^2-(θ:ℂ)^2) =
      (π:ℂ)*(if θ ≠ 0 then 1 / Complex.sin (π * θ) - 1 / (π * θ : ℂ) else 0) := by
  by_cases hz : θ=0
  · simp [hz]
  simp only [ite_eq_left hz, alternating_theta_eq_cotTerm hθ]
  have h := csc_series (lemma_abadsumas_not_in_integerComplement hθ hz)
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcancel : (π:ℂ)/(π*(θ:ℂ)) = 1/θ := by
    simpa using (mul_div_mul_left (1:ℂ) (θ:ℂ) hπ)
  rw [mul_sub,mul_one_div,mul_one_div,hcancel]
  linear_combination -h

private theorem lemma_abadsumas_quad {s : ℂ} {a : ℝ} (ha : 0 < a)
    (haτ : a > |s.im| / (2 * π)) :
    let ϑ : ℝ := s.im / (2 * π * a)
    ∑' n : ℕ, (1 / (n + 1 - ϑ)^2 + 1/(n + 1 + ϑ)^2) =
    if ϑ = 0 then π^2/3
    else π^2 / Real.sin (π * ϑ)^2 - 1/ϑ^2 := by
  intro ϑ
  split_ifs with hϑ
  · simp only [hϑ, sub_zero, add_zero]
    simp_rw [show ∀ n : ℕ, (1 : ℝ) / ((↑n + 1) ^ 2) + 1 / ((↑n + 1) ^ 2) = 2 * (1 / ((↑n + 1) ^ 2)) from fun _ => by ring, tsum_mul_left]
    rw [show ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2 = π ^ 2 / 6 by
      have h := HasSum.tsum_eq hasSum_zeta_two
      rw [Summable.tsum_eq_zero_add hasSum_zeta_two.summable] at h
      simpa using h]
    ring
  · have hϑ_lt : |ϑ| < 1 := by
      simp only [ϑ]
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * π * a),
          div_lt_one (by positivity : (0:ℝ) < 2 * π * a)]
      have h2π : (0:ℝ) < 2 * π := by positivity
      have := haτ
      rw [gt_iff_lt, div_lt_iff₀ h2π] at this
      linarith [abs_nonneg s.im]
    have hweier := lemma_abadeulmit2 (lemma_abadsumas_not_in_integerComplement hϑ_lt hϑ)
    have hZ_summable := summable_inverse_square_int (ϑ:ℂ)
    have hC : (↑π : ℂ) ^ 2 / Complex.sin (↑π * ↑ϑ) ^ 2 =
        1 / (↑ϑ : ℂ) ^ 2 +
        ∑' n : ℕ, (1 / ((↑n + 1 - (↑ϑ : ℂ)) ^ 2) + 1 / ((↑n + 1 + (↑ϑ : ℂ)) ^ 2)) := by
      rw [hweier, tsum_int_eq_zero_add_tsum_pnat hZ_summable]
      simp only [Int.cast_zero, sub_zero]
      rw [add_assoc, add_left_cancel_iff]
      have hpos : ∑' (n : ℕ+), (1 : ℂ) / ((ϑ : ℂ) - ↑(↑↑n : ℤ)) ^ 2 =
          ∑' (n : ℕ), 1 / ((↑n + 1 - (ϑ : ℂ)) ^ 2) := by
        rw [← Equiv.tsum_eq Equiv.pnatEquivNat.symm]
        congr 1; ext n
        simp only [Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Int.cast_add,
          Int.cast_natCast, Int.cast_one, one_div, inv_inj]
        ring
      have hneg : ∑' (n : ℕ+), (1 : ℂ) / ((ϑ : ℂ) - ↑(-(↑↑n : ℤ))) ^ 2 =
          ∑' (n : ℕ), 1 / ((↑n + 1 + (ϑ : ℂ)) ^ 2) := by
        rw [← Equiv.tsum_eq Equiv.pnatEquivNat.symm]
        congr 1; ext n
        simp only [Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, neg_add_rev,
          Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one, Int.cast_natCast, one_div,
          inv_inj]
        ring
      have hsum1 : Summable (fun n : ℕ => (1 : ℂ) / ((↑n + 1 - (ϑ : ℂ)) ^ 2)) := by
        have h := hZ_summable.comp_injective
          (i := fun n : ℕ => (↑n + 1 : ℤ))
          (fun a b hab => by simpa using hab)
        refine h.congr (fun n => ?_)
        simp only [Function.comp]
        push_cast; ring
      have hsum2 : Summable (fun n : ℕ => (1 : ℂ) / ((↑n + 1 + (ϑ : ℂ)) ^ 2)) := by
        have h := hZ_summable.comp_injective
          (i := fun n : ℕ => -(↑n + 1 : ℤ))
          (fun a b hab => by simpa using hab)
        refine h.congr (fun n => ?_)
        simp only [Function.comp]
        push_cast; ring
      rw [hpos, hneg, ← Summable.tsum_add hsum1 hsum2]
    symm
    apply Complex.ofReal_inj.mp
    calc ((π ^ 2 / Real.sin (π * ϑ) ^ 2 - 1 / ϑ ^ 2 : ℝ) : ℂ)
      _ = (π : ℂ) ^ 2 / Complex.sin (π * ϑ) ^ 2 - 1 / (ϑ : ℂ) ^ 2 := by push_cast; rfl
      _ = 1 / (ϑ : ℂ) ^ 2 + ∑' (n : ℕ), (1 / ((n : ℂ) + 1 - (ϑ : ℂ)) ^ 2 + 1 / ((n : ℂ) + 1 + (ϑ : ℂ)) ^ 2) - 1 / (ϑ : ℂ) ^ 2 := by rw [hC]
      _ = ∑' (n : ℕ), (1 / ((n : ℂ) + 1 - (ϑ : ℂ)) ^ 2 + 1 / ((n : ℂ) + 1 + (ϑ : ℂ)) ^ 2) := by ring
      _ = (↑(∑' n : ℕ, (1 / (n + 1 - ϑ) ^ 2 + 1 / (n + 1 + ϑ) ^ 2 : ℝ)) : ℂ) := by rw [Complex.ofReal_tsum]; push_cast; rfl

private theorem lemma_abadsumas {s : ℂ} (hsigma : 0 ≤ s.re) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (ha' : a.IsHalfInteger) (hb' : b.IsHalfInteger) (haτ : a > |s.im| / (2 * π)) :
    let ϑ : ℝ := s.im / (2 * π * a)
    let ϑ_minus : ℝ := s.im / (2 * π * b)
    let f : ℝ → ℂ := fun y ↦
      if a ≤ y ∧ y ≤ b then (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) else 0
    let g : ℝ → ℂ := fun t ↦
      if t ≠ 0 then (1 / Complex.sin (π * t) : ℂ) - (1 / (π * t : ℂ)) else 0
    let C : ℝ :=
      if ϑ ≠ 0 then
        s.re / 2 * ((1 / (Complex.sin (π * ϑ) ^ 2 : ℂ)).re - (1 / ((π * ϑ) ^ 2 : ℂ)).re) +
          |ϑ| / (2 * π ^ 2) * ((1 / ((1 - |ϑ|) ^ 3 : ℝ)) + 2 * (riemannZeta 3).re - 1)
      else
        s.re / 6
    Summable (fun n : ℕ ↦ FourierTransform.fourier f (n + 1) + FourierTransform.fourier f (-(n + 1 : ℤ))) ∧
    ∃ E : ℂ, ∑' n : ℕ, (FourierTransform.fourier f (n + 1) + FourierTransform.fourier f (-(n + 1 : ℤ))) =
      ((a ^ (-s) : ℂ) * g ϑ) / (2 * I) - ((b ^ (-s) : ℂ) * g ϑ_minus) / (2 * I) + E ∧
      ‖E‖ ≤ C / a ^ (s.re + 1) := by
  intro ϑ ϑ_minus f g C
  have h_im_bound : |s.im| < 2 * π * a := by
    have hpos : 0 < 2 * π := by positivity
    rw [gt_iff_lt, div_lt_iff₀ hpos] at haτ
    linarith [mul_comm a (2 * π)]
  have apply_applem : ∀ n : ℕ, ∃ E_n : ℂ,
    FourierTransform.fourier f (n + 1) + FourierTransform.fourier f (-(n + 1 : ℤ)) =
    (↑a ^ (-s) / (2 * ↑π * I)) * ((-1 : ℂ) ^ (n + 2) * 2 * ↑ϑ / ((↑n + 1) ^ 2 - ↑ϑ ^ 2)) -
    (↑b ^ (-s) / (2 * ↑π * I)) * ((-1 : ℂ) ^ (n + 2) * 2 * ↑ϑ_minus / ((↑n + 1) ^ 2 - ↑ϑ_minus ^ 2)) +
    E_n ∧ ‖E_n‖ ≤ a ^ (-(s.re + 1)) / (2 * π ^ 2) *
      (s.re / (↑n + 1 - ϑ) ^ 2 + s.re / (↑n + 1 + ϑ) ^ 2 +
       |ϑ| / |↑n + 1 - ϑ| ^ 3 + |ϑ| / |↑n + 1 + ϑ| ^ 3) := by
    intro n
    obtain ⟨E_prop, hE_eq, hE_bound⟩ :=
      proposition_applem s hsigma haτ hab ha' hb' (n := n + 1) (by omega)
    refine ⟨↑(a ^ (-(s.re + 1))) / (2 * π ^ 2) * E_prop, ?_, ?_⟩
    · have hconv : ∫ y in (a : ℝ)..b, (y : ℂ) ^ (-s) * ↑(Real.cos (2 * π * (↑n + 1) * y)) =
          ∫ y in Set.Icc a b, (↑y : ℂ) ^ (-s) * ↑(Real.cos (2 * π * ↑(n + 1) * y)) := by
        have h_le : a ≤ b := le_of_lt hab
        rw [intervalIntegral.integral_of_le h_le]
        rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
        congr 1
        ext y
        push_cast
        rfl
      rw [lemma_abadsumas_sum_fourier s ha hab, hconv, hE_eq]
      simp only [ϑ, ϑ_minus]
      rw [show (-1 : ℂ) ^ (n + 2) = -(-1) ^ (n + 1) by ring]
      push_cast; field_simp; ring_nf
    · have hpos : (0 : ℝ) ≤ a ^ (-(s.re + 1)) / (2 * π ^ 2) := by positivity
      rw [show ‖(Complex.ofReal (a ^ (-(s.re + 1))) / (2 * Complex.ofReal π ^ 2)) * E_prop‖ =
        a ^ (-(s.re + 1)) / (2 * π ^ 2) * ‖E_prop‖ by
          have hreal : Complex.ofReal (a ^ (-(s.re + 1))) / (2 * Complex.ofReal π ^ 2) =
              Complex.ofReal (a ^ (-(s.re + 1)) / (2 * π ^ 2)) := by
            rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
          rw [hreal, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
      have hcast : (↑(n + 1) : ℝ) = ↑n + 1 := by push_cast; ring
      have hE_bound' : ‖E_prop‖ ≤
          s.re / (↑n + 1 - ϑ) ^ 2 + s.re / (↑n + 1 + ϑ) ^ 2 +
          |ϑ| / |↑n + 1 - ϑ| ^ 3 + |ϑ| / |↑n + 1 + ϑ| ^ 3 := by
        have hϑ : ϑ = s.im / (2 * π * a) := rfl
        simp only [hϑ, ← hcast]
        exact hE_bound
      exact mul_le_mul_of_nonneg_left hE_bound' hpos
  choose error_term error_term_eq error_term_bound using apply_applem
  have hϑ_lt : |ϑ| < 1 := by
    simp only [ϑ]
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * π * a),
        div_lt_one (by positivity : (0:ℝ) < 2 * π * a)]
    have h2π : (0:ℝ) < 2 * π := by positivity
    have := haτ
    rw [gt_iff_lt, div_lt_iff₀ h2π] at this
    linarith [abs_nonneg s.im]
  have hsin_pos : ϑ ≠ 0 → 0 < Real.sin (π * ϑ) ^ 2 := by
    intro hϑ0
    apply sq_pos_of_ne_zero
    intro hsin
    rw [Real.sin_eq_zero_iff] at hsin
    obtain ⟨n, hn⟩ := hsin
    have hπ : π ≠ 0 := Real.pi_ne_zero
    have hϑn : ϑ = (n : ℝ) := by
      have := mul_left_cancel₀ hπ (by linarith : π * ϑ = π * n)
      linarith
    have hn_abs : |(n : ℝ)| < 1 := hϑn ▸ hϑ_lt
    have hn_zero : n = 0 := by
      have : |n| < 1 := by exact_mod_cast hn_abs
      rw [abs_lt] at this
      omega
    exact hϑ0 (by rw [hϑn]; exact_mod_cast hn_zero)
  have hre : ϑ ≠ 0 → (1 / Complex.sin (π * ϑ : ℂ) ^ 2).re = 1 / (Real.sin (π * ϑ) ^ 2) := by
    intro hϑ0
    have him : (Complex.sin (π * ϑ)).im = 0 := by exact_mod_cast Complex.sin_ofReal_im (π * ϑ)
    have hre_eq : (Complex.sin (π * ϑ)).re = Real.sin (π * ϑ) := by exact_mod_cast Complex.sin_ofReal_re (π * ϑ)
    have h_is_real : Complex.sin (π * ϑ) = ↑(Real.sin (π * ϑ)) :=
      Complex.ext hre_eq (by simp [him])
    rw [h_is_real]
    norm_num [Complex.ofReal_pow]
    field_simp
    rw [show (Complex.sin (π * ϑ) ^ 2).re = Real.sin (π * ϑ) ^ 2 by
          simp [sq, Complex.mul_re, him, hre_eq]]
    have h_normSq : normSq (Complex.sin (π * ϑ)) = Real.sin (π * ϑ) ^ 2 := by
      rw [h_is_real, Complex.normSq_ofReal]
      ring
    calc Real.sin (π * ϑ) ^ 2 / normSq (Complex.sin (↑π * ↑ϑ)) ^ 2
        = Real.sin (π * ϑ) ^ 2 / (Real.sin (π * ϑ) ^ 2) ^ 2 := by
            rw [h_normSq]
      _ = 1 / Real.sin (π * ϑ) ^ 2 := by
            field_simp [hsin_pos hϑ0]
  have main_summable_a : Summable (fun n : ℕ ↦
    ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2) : ℂ)) := lemma_abadsumas_summable_alternating_theta ϑ hϑ_lt
  have main_summable_b : Summable (fun n : ℕ ↦
    ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1) ^ 2 - ϑ_minus ^ 2) : ℂ)) := by
    apply lemma_abadsumas_summable_alternating_theta
    dsimp [ϑ_minus, ϑ] at hϑ_lt ⊢
    rw [abs_div]
    have hb_pos : 0 < b := lt_trans ha hab
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * π * b),
        div_lt_one (by positivity)]
    nlinarith [Real.pi_pos, hab]
  have summable_term_a : Summable (fun n : ℕ ↦
    a ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2))) :=
    main_summable_a.mul_left (a ^ (-s) / (2 * π * I))
  have summable_term_b : Summable (fun n : ℕ ↦
    b ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1) ^ 2 - ϑ_minus ^ 2))) :=
    main_summable_b.mul_left (b ^ (-s) / (2 * π * I))
  have summable_diff : Summable (fun n : ℕ ↦
    a ^ (-s) / (2 * π * I) * ((-1 : ℂ) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2)) -
    b ^ (-s) / (2 * π * I) * ((-1 : ℂ) ^ (n + 2) * 2 * ϑ_minus / ((n + 1) ^ 2 - ϑ_minus ^ 2))) :=
    summable_term_a.sub summable_term_b
  have hpos_minus : ∀ n : ℕ, 0 < (n : ℝ) + 1 - ϑ := by
    intro n
    have := hϑ_lt
    have hϑ_le : ϑ ≤ |ϑ| := le_abs_self ϑ
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hpos_plus : ∀ n : ℕ, 0 < (n : ℝ) + 1 + ϑ := by
    intro n
    have hϑ_le : -|ϑ| ≤ ϑ := neg_abs_le ϑ
    linarith [Nat.cast_nonneg (α := ℝ) n, hϑ_lt]
  have habs_minus : ∀ n : ℕ, |(n : ℝ) + 1 - ϑ| = (n : ℝ) + 1 - ϑ :=
    fun n => abs_of_pos (hpos_minus n)
  have habs_plus : ∀ n : ℕ, |(n : ℝ) + 1 + ϑ| = (n : ℝ) + 1 + ϑ :=
    fun n => abs_of_pos (hpos_plus n)
  have helper_summable {k : ℕ} (hk : 1 < k) (c : ℝ) (hc : |c| < 1) (hpos : ∀ n : ℕ, 0 < (n : ℝ) + 1 + c) :
      Summable (fun n : ℕ => 1 / ((n : ℝ) + 1 + c) ^ k) := by
    apply Summable.of_norm_bounded_eventually (g := fun n : ℕ => 1 / (n : ℝ) ^ k)
    · exact Real.summable_one_div_nat_pow.mpr hk
    · rw [Nat.cofinite_eq_atTop]
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [norm_div, norm_one, norm_pow, norm_eq_abs, abs_of_pos (hpos n)]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      apply pow_le_pow_left₀ <;> linarith [abs_lt.mp hc]
  have hc_minus : |-ϑ| < 1 := by rwa [abs_neg]
  have hsumm_q : Summable fun n : ℕ => 1 / ((n : ℝ) + 1 - ϑ) ^ 2 + 1 / ((n : ℝ) + 1 + ϑ) ^ 2 :=
    (helper_summable (by norm_num) (-ϑ) hc_minus (fun n => by simpa using hpos_minus n)).add
      (helper_summable (by norm_num) ϑ hϑ_lt hpos_plus)
  have hsumm_c : Summable fun n : ℕ => 1 / ((n : ℝ) + 1 - ϑ) ^ 3 + 1 / ((n : ℝ) + 1 + ϑ) ^ 3 :=
    (helper_summable (by norm_num) (-ϑ) hc_minus (fun n => by simpa using hpos_minus n)).add
      (helper_summable (by norm_num) ϑ hϑ_lt hpos_plus)
  have sum_main_term_a : ∑' n : ℕ,
    ((-1 : ℂ) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2)) = π * g ϑ := lemma_abadsumas_sum_main_term ϑ hϑ_lt
  have hϑ_minus_lt : |ϑ_minus| < 1 := by
    dsimp [ϑ_minus]
    rw [abs_div]
    have hb_pos : 0 < b := lt_trans ha hab
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * π * b),
        div_lt_one (by positivity)]
    nlinarith [Real.pi_pos, hab]
  have sum_main_term_b : ∑' n : ℕ,
    ((-1 : ℂ) ^ (n + 2) * 2 * ϑ_minus / ((n + 1 : ℂ) ^ 2 - ϑ_minus ^ 2)) = π * g ϑ_minus := lemma_abadsumas_sum_main_term ϑ_minus hϑ_minus_lt
  let bound : ℕ → ℝ := fun n =>
    a ^ (-(s.re + 1)) / (2 * π ^ 2) *
      (s.re / (n + 1 - ϑ) ^ 2 + s.re / (n + 1 + ϑ) ^ 2 +
      |ϑ| / |n + 1 - ϑ| ^ 3 + |ϑ| / |n + 1 + ϑ| ^ 3)
  have hbound_summable : Summable bound := by
    simp_rw [bound, habs_minus, habs_plus]
    apply Summable.mul_left
    apply ((hsumm_q.mul_left s.re).add (hsumm_c.mul_left |ϑ|)).congr
    intro n
    ring
  have error_summable : Summable error_term := Summable.of_norm_bounded hbound_summable error_term_bound
  have fourier_decomp : (fun n : ℕ ↦ FourierTransform.fourier f (n + 1) +
    FourierTransform.fourier f (-↑(n + 1 : ℤ))) =
    (fun n : ℕ ↦ a ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2)) -
      b ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1) ^ 2 - ϑ_minus ^ 2)) +
      error_term n) := funext error_term_eq
  constructor
  · rw [fourier_decomp]
    exact summable_diff.add error_summable
  · use ∑' n : ℕ, error_term n
    constructor
    · have factor_const_a : ∑' (n : ℕ),
        a ^ (-s) / (2 * π * I) * ((-1 : ℂ) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2)) =
        a ^ (-s) / (2 * π * I) * ∑' (n : ℕ), ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1 : ℂ) ^ 2 - ϑ ^ 2)) :=
        main_summable_a.tsum_mul_left (a ^ (-s) / (2 * π * I))
      have factor_const_b : ∑' (n : ℕ),
        b ^ (-s) / (2 * π * I) * ((-1 : ℂ) ^ (n + 2) * 2 * ϑ_minus / ((n + 1) ^ 2 - ϑ_minus ^ 2)) =
        b ^ (-s) / (2 * π * I) * ∑' (n : ℕ), ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1 : ℂ) ^ 2 - ϑ_minus ^ 2)) :=
        main_summable_b.tsum_mul_left (b ^ (-s) / (2 * π * I))
      have algebra_simp : ∀ (z : ℂ) (w : ℂ), z / (2 * π * I) * (π * w) = z * w / (2 * I) := by
        intro z w; ring_nf; field_simp
      calc ∑' (n : ℕ), (FourierTransform.fourier f (n + 1) + FourierTransform.fourier f  (-↑(n + 1 : ℤ)))
          = ∑' (n : ℕ), (a ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2)) -
            b ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1) ^ 2 - ϑ_minus ^ 2)) +
            error_term n) := by
            exact congr_arg tsum fourier_decomp
        _ = ∑' (n : ℕ), (a ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2)) -
            b ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1) ^ 2 - ϑ_minus ^ 2))) +
            ∑' (n : ℕ), error_term n := by
            rw [Summable.tsum_add]
            · apply Summable.sub summable_term_a summable_term_b
            · exact error_summable
        _ = ∑' (n : ℕ), a ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1 : ℂ) ^ 2 - ϑ ^ 2)) -
            ∑' (n : ℕ), b ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1 : ℂ) ^ 2 - ϑ_minus ^ 2)) +
            ∑' (n : ℕ), error_term n := by
            rw [Summable.tsum_sub summable_term_a summable_term_b]
        _ = a ^ (-s) / (2 * π * I) * ∑' (n : ℕ), ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1 : ℂ) ^ 2 - ϑ ^ 2)) -
            b ^ (-s) / (2 * π * I) * ∑' (n : ℕ), ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1 : ℂ) ^ 2 - ϑ_minus ^ 2)) +
            ∑' (n : ℕ), error_term n := by
            rw [factor_const_a, factor_const_b]
        _ = a ^ (-s) / (2 * π * I) * (π * g ϑ) -
            b ^ (-s) / (2 * π * I) * (π * g ϑ_minus) +
            ∑' (n : ℕ), error_term n := by
            rw [sum_main_term_a, sum_main_term_b]
        _ = a ^ (-s) * g ϑ / (2 * I) - b ^ (-s) * g ϑ_minus / (2 * I) + ∑' (n : ℕ), error_term n := by
            rw [algebra_simp (a ^ (-s)) (g ϑ), algebra_simp (b ^ (-s)) (g ϑ_minus)]
    · have hquad : ∑' n : ℕ, (1 / (n + 1 - ϑ)^2 + 1/(n + 1 + ϑ)^2) =
          if ϑ = 0 then π^2/3
          else π^2 / Real.sin (π * ϑ)^2 - 1/ϑ^2 := lemma_abadsumas_quad ha haτ
      have hcubic : ∑' n : ℕ, (1/(n + 1 - ϑ)^3 + 1/(n + 1 + ϑ)^3) ≤
          1/(1-|ϑ|)^3 + 2*(riemannZeta 3).re - 1 :=
        lemma_abadimpseri ϑ hϑ_lt
      have hbound_le_half : ∑' n : ℕ, bound n ≤ (C / a ^ (s.re + 1)) := by
        simp only [bound, C]
        have hfactor : ∑' n : ℕ, bound n =
            a ^ (-(s.re + 1)) / (2 * π ^ 2) *
            (s.re * ∑' n : ℕ, (1/(n + 1 - ϑ)^2 + 1/(n + 1 + ϑ)^2) +
            |ϑ|  * ∑' n : ℕ, (1/(n + 1 - ϑ)^3 + 1/(n + 1 + ϑ)^3)) := by
          simp_rw [bound]
          simp_rw [fun n => habs_minus n, fun n => habs_plus n]
          rw [← tsum_mul_left]
          have hsplit := (hsumm_q.mul_left s.re).tsum_add (hsumm_c.mul_left |ϑ|)
          simp_rw [show ∀ n : ℕ,
              a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (s.re / (n + 1 - ϑ) ^ 2 + s.re / (n + 1 + ϑ) ^ 2 +
                 |ϑ| / (n + 1 - ϑ) ^ 3 + |ϑ| / (n + 1 + ϑ) ^ 3) =
              a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (s.re * (1 / (n + 1 - ϑ) ^ 2 + 1 / (n + 1 + ϑ) ^ 2) +
                 |ϑ| * (1 / (n + 1 - ϑ) ^ 3 + 1 / (n + 1 + ϑ) ^ 3))
            from fun n => by ring]
          rw [tsum_mul_left, hsplit, tsum_mul_left, tsum_mul_left]
        rw [hfactor]
        rcases eq_or_ne ϑ 0 with hϑ0 | hϑ0
        · simp only [hϑ0, abs_zero, add_zero, ne_eq, not_true, ite_false]
          rw [show 0 = ϑ from hϑ0.symm]
          simp only [neg_add_rev, hϑ0, sub_zero, one_div, zero_mul, add_zero, ge_iff_le]
          have hq : ∑' (n : ℕ), (1 / (↑n + 1 : ℝ) ^ 2 + 1 / (↑n + 1 : ℝ) ^ 2) = π ^ 2 / 3 := by
            simp only [hϑ0, sub_zero, add_zero, ite_true] at hquad
            exact hquad
          have hq' : ∑' (n : ℕ), (((↑n + 1 : ℝ) ^ 2)⁻¹ + ((↑n + 1 : ℝ) ^ 2)⁻¹) = π ^ 2 / 3 := by
            convert hq using 3
            simp only [one_div]
          have hexp : a ^ (-1 + -s.re) = a ^ (-(s.re + 1)) := by
            congr 1; ring
          rw [hq', hexp]
          have hpos_a : (0 : ℝ) < a ^ (s.re + 1) := by positivity
          rw [Real.rpow_neg (le_of_lt ha) _]
          have hpi2 : (0 : ℝ) < π ^ 2 := by positivity
          field_simp
          nlinarith [hsigma, hpos_a, hpi2]
        · have hquad' : ∑' n : ℕ, (1/(n+1-ϑ)^2 + 1/((n+1+ϑ)^2)) =
              π^2 / Real.sin (π * ϑ)^2 - 1/ϑ^2 := by
            rw [hquad]; simp [hϑ0]
          rw [hquad']
          simp only [hϑ0, ne_eq, not_false_eq_true, ite_true]
          have hre2 : (1 / ((π : ℂ) * (ϑ : ℂ)) ^ 2).re = 1 / (π * ϑ) ^ 2 := by
            have h : ((1 : ℂ) / ((π : ℂ) * (ϑ : ℂ)) ^ 2) = ((1 / (π * ϑ) ^ 2 : ℝ) : ℂ) := by
              push_cast; ring
            simpa only [Complex.ofReal_re] using congr_arg Complex.re h
          rw [hre hϑ0, hre2]
          have hrpow : a ^ (-(s.re + 1)) = (a ^ (s.re + 1))⁻¹ := Real.rpow_neg (le_of_lt ha) _
          have hquad_cancel :
              a ^ (-(s.re + 1)) / (2 * π ^ 2) * (s.re * (π ^ 2 / Real.sin (π * ϑ) ^ 2 - 1 / ϑ ^ 2))
              = (s.re / 2 * (1 / Real.sin (π * ϑ) ^ 2 - 1 / (π * ϑ) ^ 2)) / a ^ (s.re + 1) := by
            rw [hrpow]; field_simp
          have hS3_le :
              a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (|ϑ| * ∑' (n : ℕ), (1 / (n + 1 - ϑ) ^ 3 + 1 / (n + 1 + ϑ) ^ 3))
              ≤ a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (|ϑ| * (1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hcubic (abs_nonneg ϑ)
          have hrhs_eq :
                ((s.re / 2 * (1 / Real.sin (π * ϑ) ^ 2 - 1 / (π * ϑ) ^ 2) +
                    |ϑ| / (2 * π ^ 2) * (1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1)) /
                  a ^ (s.re + 1)) =
              (s.re / 2 * (1 / Real.sin (π * ϑ) ^ 2 - 1 / (π * ϑ) ^ 2)) / a ^ (s.re + 1) +
              a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (|ϑ| * (1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1)) := by
            rw [hrpow]; ring
          have hgoal_expand :
              a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (s.re * (π ^ 2 / Real.sin (π * ϑ) ^ 2 - 1 / ϑ ^ 2) +
                  |ϑ| * ∑' (n : ℕ), (1 / (n + 1 - ϑ) ^ 3 + 1 / (n + 1 + ϑ) ^ 3)) =
              a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (s.re * (π ^ 2 / Real.sin (π * ϑ) ^ 2 - 1 / ϑ ^ 2)) +
              a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (|ϑ| * ∑' (n : ℕ), (1 / (n + 1 - ϑ) ^ 3 + 1 / (n + 1 + ϑ) ^ 3)) := by
            ring
          linarith [hgoal_expand, hS3_le, hquad_cancel, hrhs_eq]
      have error_abs_summable : Summable (fun n ↦ ‖error_term n‖) :=
        Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) error_term_bound hbound_summable
      exact (norm_tsum_le_tsum_norm error_abs_summable).trans
        ((Summable.tsum_le_tsum error_term_bound error_abs_summable hbound_summable).trans
        hbound_le_half)

private noncomputable def dadaro_g (t : ℝ) : ℂ :=
  if t ≠ 0 then (1 / Complex.sin (π * t) - 1 / (π * t)) / (2 * I) else 0

private theorem proposition_dadaro_b_tendsto_zero_atTop {s : ℂ} (hsigma : 0 < s.re) : Tendsto
  (fun b : ℝ => (b : ℂ) ^ (-s) * dadaro_g (s.im / (2 * π * b)))
  atTop (𝓝 0) := by
  have h_pow_vanishes : Tendsto (fun b : ℝ => (b : ℂ) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : (fun b : ℝ ↦ ‖(b : ℂ) ^ (-s)‖) =ᶠ[atTop] (fun b ↦ b ^ (-s.re)) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with b hb
      simp [Complex.norm_cpow_eq_rpow_re_of_pos hb]
    exact (tendsto_congr' this).mpr (tendsto_rpow_neg_atTop hsigma)
  let g := dadaro_g
  have hne : ∀ᶠ x in 𝓝[≠] (0 : ℂ), x ≠ 0 :=
    eventually_nhdsWithin_of_forall fun x hx => hx
  have hsin : ∀ᶠ x in 𝓝[≠] (0 : ℂ), Complex.sin x ≠ 0 := by
    have hball : ∀ᶠ x in 𝓝[≠] (0 : ℂ), ‖x‖ < π := by
      apply eventually_nhdsWithin_of_eventually_nhds
      exact eventually_nhds_iff.mpr
        ⟨Metric.ball 0 π,
        fun y hy => by simpa [Metric.mem_ball, dist_zero_right] using hy,
        Metric.isOpen_ball,
        Metric.mem_ball_self (by positivity)⟩
    filter_upwards [hball, hne] with x hlt hxne
    rw [Complex.sin_ne_zero_iff]
    intro k
    by_cases hk : k = 0
    · simp [hk, hxne]
    · have hkπ : π ≤ ‖(k : ℂ) * ↑π‖ := by
        rw [norm_mul]
        suffices 1 ≤ ‖(k : ℂ)‖ by
          nth_rw 1 [← one_mul π]
          gcongr
          simp only [norm_real, norm_eq_abs]
          exact le_abs_self π
        simp only [norm_intCast]
        exact_mod_cast Int.one_le_abs hk
      intro heq
      linarith [heq ▸ hlt]
  have hl : (fun x ↦ 1 / Complex.sin x - 1 / x) =ᶠ[𝓝[≠] 0] (fun x ↦ (x - Complex.sin x) / (x * Complex.sin x)) := by
    filter_upwards [hsin, hne] with x hsinx hxne
    field_simp [hxne, hsinx]
  have hscale : Tendsto (fun t : ℝ ↦ (↑π * ↑t : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa only [Pi.mul_def, Complex.ofReal_zero, mul_zero] using (continuous_const.mul Complex.continuous_ofReal).tendsto (0 : ℝ)
  have h_pi : Tendsto (fun t : ℝ ↦ (↑π * ↑t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact tendsto_nhdsWithin_of_tendsto_nhds hscale
    · apply eventually_nhdsWithin_of_forall
      exact fun t ht ↦ mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (Complex.ofReal_ne_zero.mpr ht)
  have h2 : Tendsto (fun x ↦ x / Complex.sin x) (𝓝[≠] 0) (𝓝 1) := by
    have heq : Asymptotics.IsEquivalent (𝓝[≠] (0 : ℂ)) Complex.sin id := by
      unfold Asymptotics.IsEquivalent
      exact Complex.isEquivalent_sin.isLittleO.mono nhdsWithin_le_nhds
    have hsinx : Tendsto (fun x ↦ Complex.sin x / x) (𝓝[≠] 0) (𝓝 1) :=
      (Asymptotics.isEquivalent_iff_tendsto_one hne).mp heq
    have hflip : (fun x ↦ x / Complex.sin x) =ᶠ[𝓝[≠] (0 : ℂ)] (fun x ↦ (Complex.sin x / x)⁻¹) := by
      filter_upwards [hsin, hne] with x hsx hxne
      field_simp [hxne, hsx]
    rw [tendsto_congr' hflip]
    simpa using hsinx.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
  have hfactor : (fun x : ℂ ↦ (x - Complex.sin x) / (x * Complex.sin x))
      =ᶠ[𝓝[≠] 0] (fun x ↦ (x - Complex.sin x) / x ^ 2 * (x / Complex.sin x)) := by
    filter_upwards [hsin, hne]
      with x hsx hxne
    field_simp [hxne, hsx]
  have hquot : Tendsto (fun x : ℂ ↦ (x - Complex.sin x) / x ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have hkey : ∀ x : ℂ, x ≠ 0 → ‖x‖ ≤ 1 →
        ‖(x - Complex.sin x) / x ^ 2‖ ≤ ‖x‖ / 6 + ‖x‖ ^ 2 * (5 / 96) := by
      intro x hx hxn
      have hbound := sin_bound hxn
      have hxnorm : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
      rw [norm_div, norm_pow, div_le_iff₀ hxnorm]
      have htri : ‖x - Complex.sin x‖ ≤ ‖x‖ ^ 3 / 6 + ‖x‖ ^ 4 * (5 / 96) := by
        have : ‖x - Complex.sin x‖ ≤ ‖x ^ 3 / 6‖ + ‖x ^ 3 / 6 - (x - Complex.sin x)‖ :=
          calc ‖x - Complex.sin x‖
            = ‖x ^ 3 / 6 - (x ^ 3 / 6 - (x - Complex.sin x))‖ := by ring_nf
          _ ≤ ‖x ^ 3 / 6‖ + ‖x ^ 3 / 6 - (x - Complex.sin x)‖ := norm_sub_le _ _
        have h1 : ‖x ^ 3 / 6‖ = ‖x‖ ^ 3 / 6 := by
          rw [norm_div, norm_pow]; norm_num
        have h2 : ‖x ^ 3 / 6 - (x - Complex.sin x)‖ ≤ ‖x‖ ^ 4 * (5 / 96) := by
          have heq : x ^ 3 / 6 - (x - Complex.sin x) = Complex.sin x - (x - x ^ 3 / 6) := by ring
          rw [heq]
          have hp : ‖x‖ ^ 5 ≤ ‖x‖ ^ 4 := by
            calc ‖x‖ ^ 5 = ‖x‖ ^ 4 * ‖x‖ := by ring
                 _ ≤ ‖x‖ ^ 4 * 1 := mul_le_mul_of_nonneg_left hxn (by positivity)
                 _ = ‖x‖ ^ 4 := mul_one _
          exact hbound.trans (by nlinarith [pow_nonneg (norm_nonneg x) 4])
        linarith
      linarith [htri]
    have hsqueeze : Tendsto (fun x : ℂ ↦ ‖x‖ / 6 + ‖x‖ ^ 2 * (5 / 96)) (𝓝[≠] 0) (𝓝 0) := by
      rw [show (0 : ℝ) = 0 / 6 + 0 ^ 2 * (5 / 96) by norm_num]
      apply Filter.Tendsto.add
      · apply Tendsto.div_const
        refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
        exact tendsto_norm_zero
      · apply Filter.Tendsto.mul_const
        exact tendsto_nhdsWithin_of_tendsto_nhds (by
          simpa [Pi.pow_def] using (continuous_norm.pow 2).tendsto (0 : ℂ))
    apply squeeze_zero_norm' _ hsqueeze
    rw [eventually_nhdsWithin_iff]
    apply eventually_of_mem (Metric.ball_mem_nhds 0 one_pos)
    intro x hx hne
    apply hkey x hne
    simp only [Metric.mem_ball, dist_zero_right] at hx
    exact le_of_lt hx
  have h_f_lim : Tendsto (fun x : ℂ ↦ 1 / Complex.sin x - 1 / x) (𝓝[≠] 0) (𝓝 0) := by
    have hprod : Tendsto (fun x : ℂ ↦ (x - Complex.sin x) / x ^ 2 * (x / Complex.sin x))
        (𝓝[≠] 0) (𝓝 0) := by simpa using hquot.mul h2
    exact (hprod.congr' hfactor.symm).congr' hl.symm
  have h_f_lim_new : Tendsto (fun x : ℂ ↦ 1 / Complex.sin x - 1 / x) (𝓝 0) (𝓝 0) := by
    have h0 : (fun x : ℂ ↦ 1 / Complex.sin x - 1 / x) 0 = 0 := by
      simp [Complex.sin_zero]
    rw [← nhdsWithin_univ]
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simp only [nhdsWithin_univ]
      have hc : ContinuousAt (fun x ↦ 1 / Complex.sin x - 1 / x) 0 := by
        rw [continuousAt_iff_punctured_nhds]
        simp only [h0]
        exact h_f_lim
      simpa only [h0] using hc.tendsto
    · exact Filter.Eventually.of_forall (fun x => trivial)
  have h_g_limit : Tendsto g (𝓝 0) (𝓝 0) := by
    have hg_eq : g =ᶠ[𝓝 0] fun t : ℝ =>
        (1 / Complex.sin (↑π * ↑t) - 1 / (↑π * ↑t)) / (2 * I) := by
      exact Filter.Eventually.of_forall fun t ↦ by
        simp only [g, dadaro_g]
        split_ifs with ht
        · rfl
        · simp only [one_div, mul_inv_rev]
          field_simp
          push Not at ht
          simp [ht]
    have hcomp : Tendsto (fun t : ℝ =>
        1 / Complex.sin (↑π * ↑t) - 1 / (↑π * ↑t)) (𝓝 0) (𝓝 0) :=
      h_f_lim_new.comp hscale
    have hdiv : Tendsto (fun t : ℝ =>
        (1 / Complex.sin (↑π * ↑t) - 1 / (↑π * ↑t)) / (2 * I)) (𝓝 0) (𝓝 0) := by
      simpa using hcomp.div_const (2 * I)
    exact hdiv.congr' hg_eq.symm
  have h_arg_limit : Tendsto (fun b : ℝ ↦ s.im / (2 * π * b)) atTop (𝓝 0) := by
    apply Filter.Tendsto.const_div_atTop
    apply (tendsto_const_mul_atTop_of_pos ?_).mpr tendsto_id
    exact mul_pos two_pos pi_pos
  have h_trig_vanishes : Tendsto (fun b : ℝ ↦ g (s.im / (2 * π * b))) atTop (𝓝 0) :=
    h_g_limit.comp h_arg_limit
  simpa using h_pow_vanishes.mul h_trig_vanishes

private theorem proposition_dadaro_zero_lt {s : ℂ} (hs1 : s ≠ 1) (hsigma : 0 < s.re) {a : ℝ} (ha : 0 < a)
    (ha' : a.IsHalfInteger) (haτ : a > |s.im| / (2 * π)) :
    let ϑ : ℝ := s.im / (2 * π * a)
    let C : ℝ :=
      if ϑ ≠ 0 then
        s.re / 2 * ((1 / (Complex.sin (π * ϑ) ^ 2 : ℂ)).re - (1 / ((π * ϑ) ^ 2 : ℂ)).re) +
          |ϑ| / (2 * π ^ 2) * ((1 / ((1 - |ϑ|) ^ 3 : ℝ)) + 2 * (riemannZeta 3).re - 1)
      else
        s.re / 6
    let c : ℂ :=
      if ϑ ≠ 0 then
        I / 2 * ((1 / Complex.sin (π * ϑ) : ℂ) - (1 / (π * ϑ : ℂ)))
      else
        0
    ∃ E : ℂ, riemannZeta s =
      ∑ n ∈ Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) -
      (a ^ (1 - s) : ℂ) / (1 - s) - c * (a ^ (-s) : ℂ) + E ∧
      ‖E‖ ≤ C / (a ^ (s.re + 1 : ℝ)) := by
  intro ϑ C c
  let B := {b : ℝ | b.IsHalfInteger ∧ b > a}
  let g := dadaro_g
  have h_b_term_vanishes : Tendsto
      (fun b : ℝ => (b : ℂ) ^ (-s) * dadaro_g (s.im / (2 * π * b)))
      atTop (𝓝 0) := proposition_dadaro_b_tendsto_zero_atTop hsigma
  have h_for_each_b : ∀ b ∈ B, ∃ E₁ E₂ : ℂ,
      ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) =
        riemannZeta s + (a : ℂ) ^ (1 - s) / (1 - s) -
        (a : ℂ) ^ (-s) * g ϑ +
        ((b : ℂ) ^ (-s) * g (s.im / (2 * π * b)) - E₁ + E₂) ∧
      ‖E₁‖ ≤ C / a ^ (s.re + 1) ∧
      ‖E₂‖ ≤ 2 * ‖s‖ / (s.re * b ^ s.re) := by
    intro b hb
    obtain ⟨hb_half, hb_gt⟩ := hb
    obtain ⟨E_zeta, h_step1, h_E_zeta_bd⟩ :=
      lemma_abadtoabsum ha hb_half hb_gt hs1 hsigma
    obtain ⟨L, _hL_tendsto, hL_eq⟩ :=
      lemma_abadusepoisson ha' hb_half hb_gt ha hs1
    have h_combined : ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) =
        riemannZeta s + (a : ℂ) ^ (1 - s) / (1 - s) - L + E_zeta := by
      rw [h_step1, hL_eq]; ring
    obtain ⟨E₁, hL_decomp, hE₁_bd⟩ : ∃ E₁ : ℂ,
        L = (a : ℂ) ^ (-s) * g ϑ -
            (b : ℂ) ^ (-s) * g (s.im / (2 * π * b)) + E₁ ∧
        ‖E₁‖ ≤ C / a ^ (s.re + 1) := by
      refine ⟨L - (a : ℂ)^(-s) * g ϑ + (b : ℂ)^(-s) * g (s.im / (2 * π * b)), ?_, ?_⟩
      · ring
      · have h_fourier_ioc_bound :
            ‖L - (a : ℂ)^(-s) * g ϑ + (b : ℂ)^(-s) * g (s.im / (2 * π * b))‖
            ≤ C / a ^ (s.re + 1) := by
          obtain ⟨h_sum, E, h_E_eq, h_E_bd⟩ := lemma_abadsumas hsigma.le ha hb_gt ha' hb_half haτ
          have hL_eq : L = (a : ℂ)^(-s) * g ϑ - (b : ℂ)^(-s) * g (s.im / (2 * π * b)) + E := by
            let f : ℝ → ℂ := fun y ↦ if a ≤ y ∧ y ≤ b then ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) else 0
            have hL_tsum : L = ∑' n : ℕ, (FourierTransform.fourier f (n + 1) + FourierTransform.fourier f (-(n + 1 : ℤ))) := by
              apply tendsto_nhds_unique _hL_tendsto
              have h_eq : (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N,
                  (FourierTransform.fourier f ↑n + FourierTransform.fourier f (-↑n))) =ᶠ[atTop]
                  fun N ↦ ∑ n ∈ Finset.range N,
                  (FourierTransform.fourier f (n + 1) + FourierTransform.fourier f (-(n + 1 : ℤ))) := by
                apply Filter.Eventually.of_forall
                intro N
                apply Finset.sum_nbij (fun n => n - 1)
                · intro a ha
                  simp [Finset.mem_range, Finset.mem_Icc] at *
                  omega
                · intro n₁ a n₂ b h
                  simp only [] at h
                  simp only [Finset.coe_Icc, Set.mem_Icc] at a b
                  omega
                · intro n hn
                  simp only [Finset.coe_Icc, Finset.mem_coe, Finset.mem_range] at *
                  simp only [Set.mem_image, Set.mem_Icc]
                  exact ⟨n + 1, by omega, by omega⟩
                · intro n hn
                  simp only [Finset.mem_Icc] at hn
                  have : n = (n - 1) + 1 := (Nat.sub_add_cancel hn.1).symm
                  congr 1
                  · norm_cast
                    rw [this]
                    simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
                  · rw [this]
                    norm_cast
              exact h_sum.hasSum.tendsto_sum_nat.congr' h_eq.symm
            have hg_unfold : ∀ t : ℝ, g t =
                (fun t : ℝ ↦ if t ≠ 0 then (1 / Complex.sin (↑π * ↑t) : ℂ) - 1 / (↑π * ↑t) else 0) t / (2 * I) := by
              intro t
              simp only [g, dadaro_g]
              split_ifs with ht
              · rfl
              · simp
            rw [hL_tsum, h_E_eq]
            simp only [hg_unfold]
            have hϑ_def : ϑ = s.im / (2 * π * a) := rfl
            rw [hϑ_def]
            ring_nf
          have hE_eq : L - (a : ℂ)^(-s) * g ϑ + (b : ℂ)^(-s) * g (s.im / (2 * π * b)) = E := by
            rw [hL_eq]; ring
          rwa [hE_eq]
        linarith [h_fourier_ioc_bound]
    refine ⟨E₁, E_zeta, ?_, hE₁_bd, ?_⟩
    · rw [h_combined, hL_decomp]; ring
    · have hpos : (0 : ℝ) < s.re * b ^ s.re :=
        mul_pos hsigma (rpow_pos_of_pos (ha.trans hb_gt) s.re)
      calc ‖E_zeta‖
        _ ≤ ‖s‖ / (2 * s.re * b ^ s.re) := h_E_zeta_bd
        _ ≤ ‖s‖ / (s.re * b ^ s.re) := by
          apply div_le_div_of_nonneg_left (norm_nonneg s) (by positivity)
          linarith [hpos]
        _ ≤ 2 * ‖s‖ / (s.re * b ^ s.re) := by
          gcongr
          field_simp [hpos]
          linarith [norm_nonneg s]
  have h_E₂_vanishes : ∀ ε > 0, ∃ B₀ > a, B₀.IsHalfInteger ∧
      ∀ b, b.IsHalfInteger → b ≥ B₀ →
      (∃ E₂ : ℂ, ‖E₂‖ ≤ 2 * ‖s‖ / (s.re * b ^ s.re) ∧
            2 * ‖s‖ / (s.re * b ^ s.re) < ε) := by
    intro ε hε
    have h_limit : Tendsto (fun b : ℝ ↦ 2 * ‖s‖ / (s.re * b ^ s.re)) atTop (𝓝 0) := by
      have h_rw : (fun b : ℝ ↦ 2 * ‖s‖ / (s.re * b ^ s.re)) =ᶠ[atTop]
                  fun b : ℝ ↦ (2 * ‖s‖ / s.re) * b ^ (-s.re) := by
        filter_upwards [eventually_gt_atTop 0] with b hb
        rw [rpow_neg hb.le, div_mul_eq_div_div, div_eq_mul_one_div (2 * ‖s‖ / s.re)]
        field_simp
      refine (tendsto_congr' h_rw).mpr <| by
        rw [show (0 : ℝ) = (2 * ‖s‖ / s.re) * 0 by ring]
        exact Tendsto.const_mul _ (tendsto_rpow_neg_atTop hsigma)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_limit ε hε
    let M := max a N
    let B₀ : ℝ := ↑⌊M⌋ + 3 / 2
    use B₀
    refine ⟨?_, ?_, ?_⟩
    · have hM_a : M ≥ a := le_max_left a N
      have hB₀_M : B₀ > M := Real.floor_add_three_halfs_gt M
      linarith
    · exact Real.IsHalfInteger.floor_add_three_halfs M
    · intro b hb_hi hb_ge
      have hb_gt_a : b > a := by
        have hM_a : M ≥ a := le_max_left a N
        have hB₀_M : B₀ > M := Real.floor_add_three_halfs_gt M
        linarith
      have hb_in_B : b ∈ B := ⟨hb_hi, hb_gt_a⟩
      obtain ⟨_, E₂, _, _, hE₂_bd⟩ := h_for_each_b b hb_in_B
      use E₂
      refine ⟨hE₂_bd, ?_⟩
      have hb_ge_N : b ≥ N := by
        have hM_N : M ≥ N := le_max_right a N
        have hB₀_M : B₀ > M := Real.floor_add_three_halfs_gt M
        linarith
      have h_dist := hN b hb_ge_N
      rw [dist_zero_right] at h_dist
      have h_pos : 0 < 2 * ‖s‖ / (s.re * b ^ s.re) := by
        apply div_pos
        · have h_s_ne_zero : s ≠ 0 := by
            intro h
            rw [h] at hsigma
            simp at hsigma
          exact mul_pos zero_lt_two (norm_pos_iff.mpr h_s_ne_zero)
        · exact mul_pos hsigma (rpow_pos_of_pos (ha.trans hb_gt_a) _)
      have h_abs := _root_.abs_of_pos h_pos
      rw [Real.norm_eq_abs] at h_dist
      rwa [h_abs] at h_dist
  set c_a : ℂ := g (s.im / (2 * π * a))
  set c_b : ℝ → ℂ := fun b => g (s.im / (2 * π * b))
  set main_a : ℂ :=
    riemannZeta s + ↑a ^ (1 - s) / (1 - s) - ↑a ^ (-s) * c_a
  have h_E₁_exists : ∃ E₁ : ℂ, ‖E₁‖ ≤ C / a ^ (s.re + 1) ∧
      ∀ ε > 0, ∃ B₀ > a, B₀.IsHalfInteger ∧
      ∀ b : ℝ, b.IsHalfInteger → b ≥ B₀ →
      ∀ E₁_lem E₂_lem : ℂ,
      (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) =
        main_a + (((b : ℂ) ^ (-s) * c_b b) - E₁_lem + E₂_lem)) →
      ‖E₂_lem + (E₁ - E₁_lem) +
        (b : ℂ) ^ (-s) * c_b b‖ < ε := by
    refine ⟨main_a - ∑ n ∈ Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s), ?_, ?_⟩
    · apply le_of_forall_pos_le_add
      intro ε hε
      have hε2 : ε / 2 > 0 := by linarith
      obtain ⟨B₁, hB₁_prop⟩ := Metric.tendsto_atTop.mp h_b_term_vanishes (ε / 2) hε2
      obtain ⟨B₂, _hB₂_gt, _hB₂_hi, hB₂_prop⟩ := h_E₂_vanishes (ε / 2) hε2
      let M := max (max a B₁) B₂
      let b : ℝ := ↑⌊M⌋ + 3 / 2
      have hb_hi : b.IsHalfInteger := Real.IsHalfInteger.floor_add_three_halfs M
      have hb_gt_a : b > a := by
        have : b > M := Real.floor_add_three_halfs_gt M
        exact lt_of_le_of_lt ((le_max_left a B₁).trans (le_max_left (max a B₁) B₂)) this
      have hb_ge_B₁ : b ≥ B₁ := by
        have : b > M := Real.floor_add_three_halfs_gt M
        exact ((le_max_right a B₁).trans (le_max_left (max a B₁) B₂)).trans this.le
      have hb_ge_B₂ : b ≥ B₂ := by
        have : b > M := Real.floor_add_three_halfs_gt M
        exact (le_max_right (max a B₁) B₂).trans this.le
      have hb_in_B : b ∈ B := ⟨hb_hi, hb_gt_a⟩
      obtain ⟨E₁_b, E₂_b, h_formula, hE₁_b_bd, hE₂_b_bd⟩ := h_for_each_b b hb_in_B
      have h_rearrange : main_a - ∑ n ∈ Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) =
          E₁_b - ((b : ℂ) ^ (-s) * g (s.im / (2 * π * b)) + E₂_b) := by
        rw [h_formula]; ring
      rw [h_rearrange]
      calc ‖E₁_b - ((b : ℂ) ^ (-s) * g (s.im / (2 * π * b)) + E₂_b)‖
        _ ≤ ‖E₁_b‖ + ‖(b : ℂ) ^ (-s) * g (s.im / (2 * π * b)) + E₂_b‖ := norm_sub_le _ _
        _ ≤ C / a ^ (s.re + 1) + (‖(b : ℂ) ^ (-s) * g (s.im / (2 * π * b))‖ + ‖E₂_b‖) := by
          gcongr; exact norm_add_le _ _
        _ ≤ C / a ^ (s.re + 1) + (ε / 2 + ε / 2) := by
          gcongr
          · specialize hB₁_prop b hb_ge_B₁; rw [dist_zero_right] at hB₁_prop; exact hB₁_prop.le
          · obtain ⟨_, _, hE₂_bd_ε⟩ := hB₂_prop b hb_hi hb_ge_B₂; exact hE₂_b_bd.trans hE₂_bd_ε.le
        _ = C / a ^ (s.re + 1) + ε := by ring
    · intro ε hε
      obtain ⟨B₀, hB₀_gt, hB₀_hi, _⟩ := h_E₂_vanishes ε hε
      refine ⟨B₀, hB₀_gt, hB₀_hi, fun b _hb_hi _hb_ge E₁_lem E₂_lem hformula => ?_⟩
      have hcancel : E₂_lem + ((main_a - ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s)) - E₁_lem)
          + (b : ℂ) ^ (-s) * c_b b = 0 := by
        rw [hformula]
        ring
      rwa [hcancel, norm_zero]
  obtain ⟨E₁, hE₁_bound, hE₁_limit⟩ := h_E₁_exists
  use E₁
  let transient_error (b : ℝ) (E₂ : ℂ) : ℂ :=
    E₂ + (b : ℂ) ^ (-s) * g (s.im / (2 * π * b))
  have h_eq_for_large_b : ∀ ε > 0, ∃ B₀ > a, B₀.IsHalfInteger ∧
    ∀ b, b.IsHalfInteger → b ≥ B₀ →
    ∃ E₂ : ℂ,
      ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) =
        riemannZeta s + (a : ℂ) ^ (1 - s) / (1 - s) + c * (a : ℂ) ^ (-s) +
        (-E₁ + transient_error b E₂) ∧
      ‖transient_error b E₂‖ < ε := by
    intro ε hε
    have hε2 : ε / 2 > 0 := by linarith
    obtain ⟨B₁, hB₁_gt, hB₁_hi, hB₁_prop⟩ := h_E₂_vanishes (ε / 2) hε2
    have hB₂_exists : ∃ B₂ : ℝ, B₂ > a ∧ B₂.IsHalfInteger ∧
        ∀ b : ℝ, b.IsHalfInteger → b ≥ B₂ →
          ‖(↑b : ℂ) ^ (-s) * dadaro_g (s.im / (2 * π * b))‖ < ε / 2 := by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_b_term_vanishes (ε / 2) hε2
      let M := max a N
      let B₂ : ℝ := ↑⌊M⌋ + 3 / 2
      use B₂
      refine ⟨?_, ?_, ?_⟩
      · have hM_a : M ≥ a := le_max_left a N
        have hB₂_M : B₂ > M := Real.floor_add_three_halfs_gt M
        linarith
      · exact Real.IsHalfInteger.floor_add_three_halfs M
      · intro b _ hb_B₂
        have hb_N : b ≥ N := by
          have hM_N : M ≥ N := le_max_right a N
          have hB₂_M : B₂ > M := Real.floor_add_three_halfs_gt M
          linarith
        have h_dist := hN b hb_N
        rw [dist_zero_right] at h_dist
        exact h_dist
    obtain ⟨B₂, hB₂_gt, hB₂_hi, hB₂_prop⟩ := hB₂_exists
    obtain ⟨B₃, hB₃_gt, hB₃_hi, hB₃_prop⟩ := hE₁_limit ε hε
    obtain ⟨B₀, hB₀_gt, hB₀_hi, hB₀_ge₁, hB₀_ge₂, hB₀_ge₃⟩ :
      ∃ B₀ : ℝ,
        B₀ > a ∧
        B₀.IsHalfInteger ∧
        B₀ ≥ B₁ ∧
        B₀ ≥ B₂ ∧
        B₀ ≥ B₃ := by
      set M := max (max B₁ B₂) B₃
      set B₀ : ℝ := ↑⌊M⌋ + 3 / 2
      have hB₀M : B₀ > M := Real.floor_add_three_halfs_gt M
      refine ⟨B₀, ?_, ?_, ?_, ?_, ?_⟩
      · have hMa : M > a := by
          have h1 : M ≥ max B₁ B₂ := le_max_left (max B₁ B₂) B₃
          have h2 : max B₁ B₂ ≥ B₁ := le_max_left B₁ B₂
          linarith [h1, h2, hB₁_gt]
        linarith [hB₀M, hMa]
      · exact Real.IsHalfInteger.floor_add_three_halfs M
      · have hMa : M ≥ B₁ := le_trans (le_max_left B₁ B₂) (le_max_left _ _)
        linarith [hB₀M, hMa]
      · have hMa : M ≥ B₂ := le_trans (le_max_right B₁ B₂) (le_max_left _ _)
        linarith [hB₀M, hMa]
      · have hMa : M ≥ B₃ := le_max_right (max B₁ B₂) B₃
        linarith [hB₀M, hMa]
    refine ⟨B₀, hB₀_gt, hB₀_hi, fun b hb_hi hb_ge => ?_⟩
    have hb_gt_a : b > a := lt_of_lt_of_le hB₀_gt hb_ge
    have hb_in_B : b ∈ B := ⟨hb_hi, hb_gt_a⟩
    obtain ⟨E₁_lem, E₂_lem, hfb, _, _⟩ := h_for_each_b b hb_in_B
    have hfb_cb : ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) =
        main_a + (↑b ^ (-s) * c_b b - E₁_lem + E₂_lem) := by
      simp only [c_b, main_a, c_a] at *
      exact hfb
    have hmain : riemannZeta s + ↑a ^ (1 - s) / (1 - s) + c * ↑a ^ (-s) = main_a := by
      simp only [main_a, c_a, c, ϑ, g, dadaro_g] at *
      split_ifs with h
      · have h_sin : Complex.sin (↑π * ↑(s.im / (2 * π * a))) ≠ 0 := by
          set x := (↑π * ↑(s.im / (2 * π * a)) : ℂ)
          have hxnonzero : x ≠ 0 := by
            simp only [ofReal_div, ofReal_mul, ofReal_ofNat, ne_eq, mul_eq_zero, ofReal_eq_zero,
              pi_ne_zero, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_self, ha.ne', or_false, false_or,
              x]
            exact (div_ne_zero_iff.mp h).1
          have hxbound : ‖x‖ < π := by
            calc ‖x‖
              _ = ‖(Real.pi : ℂ) * (s.im / (2 * Real.pi * a) : ℂ)‖ := by simp [x]
              _ = ‖(Real.pi : ℂ)‖ * ‖(s.im / (2 * Real.pi * a) : ℂ)‖ := by
                exact norm_mul (Real.pi : ℂ) (s.im / (2 * Real.pi * a) : ℂ)
              _ = Real.pi * (|s.im| / (2 * Real.pi * a)) := by
                have h1 : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [abs_of_pos pi_pos]
                have h2 : ‖(s.im / (2 * Real.pi * a) : ℂ)‖ = |s.im| / (2 * Real.pi * a) := by
                  simp [abs_of_pos pi_pos, abs_of_pos ha]
                rw [h1, h2]
              _ = |s.im| / (2 * a) := by
                calc Real.pi * (|s.im| / (2 * Real.pi * a))
                  _ = (Real.pi * |s.im|) / (Real.pi * (2 * a)) := by ring
                  _ = |s.im| / (2 * a) := mul_div_mul_left _ _ pi_ne_zero
              _ < Real.pi := by
                rw [div_lt_iff₀ (by positivity)]
                have h4 : |s.im| / (2 * Real.pi) < a := haτ
                have h5 : |s.im| < a * (2 * Real.pi) := (div_lt_iff₀ (by positivity)).mp h4
                linarith
          rw [Complex.sin_ne_zero_iff]
          intro k
          by_cases hk : k = 0
          · simp [hk, hxnonzero]
          · have h_k_bound : π ≤ ‖(k : ℂ) * ↑π‖ := by
              rw [norm_mul]; simp only [norm_intCast, norm_real, norm_eq_abs]
              suffices 1 ≤ ‖(k : ℂ)‖ by
                have habs : 1 ≤ |( k : ℝ)| := by simpa [norm_eq_abs]
                have hpi  : |π| = π         := abs_of_pos Real.pi_pos
                rw [hpi]
                calc π = 1 * π       := (one_mul π).symm
                _ ≤ |(↑k)| * π := by
                  apply mul_le_mul_of_nonneg_right habs (le_of_lt Real.pi_pos)
              simp only [norm_intCast]
              norm_cast
              exact Int.one_le_abs hk
            intro heq
            linarith [heq ▸ hxbound]
        calc riemannZeta s + ↑a ^ (1 - s) / (1 - s) + (I / 2 * (1 / Complex.sin (↑π * ↑(s.im / (2 * π * a))) - 1 / (↑π * ↑(s.im / (2 * π * a))))) * ↑a ^ (-s)
          _ = riemannZeta s + ↑a ^ (1 - s) / (1 - s) - ((1 / Complex.sin (↑π * ↑(s.im / (2 * π * a))) - 1 / (↑π * ↑(s.im / (2 * π * a)))) / (2 * I)) * ↑a ^ (-s) := by
            field_simp [Complex.I_ne_zero, h_sin]
            ring_nf
            simp only [Complex.I_sq]
            ring
          _ = riemannZeta s + ↑a ^ (1 - s) / (1 - s)
          - ↑a ^ (-s) * ((1 / Complex.sin (↑π * ↑(s.im / (2 * π * a)))
              - 1 / (↑π * ↑(s.im / (2 * π * a)))) / (2 * I)) := by ring
          _ = _ := by
                simp only [ofReal_div, ofReal_mul, ofReal_ofNat, one_div, mul_inv_rev, inv_div]
      · simp only [zero_mul, add_zero, mul_zero, sub_zero]
    refine ⟨E₁ - E₁_lem + E₂_lem, ?_, ?_⟩
    · simp only [transient_error]
      have : -E₁ + (E₁ - E₁_lem + E₂_lem + ↑b ^ (-s) * c_b b) =
            ↑b ^ (-s) * c_b b - E₁_lem + E₂_lem := by ring
      rw [hmain, this]
      exact hfb_cb
    · have hnorm_eq : ‖transient_error b (E₁ - E₁_lem + E₂_lem)‖ =
          ‖E₂_lem + (E₁ - E₁_lem) + ↑b ^ (-s) * c_b b‖ := by
        simp only [transient_error, c_b]
        congr 1
        ring_nf
      rw [hnorm_eq]
      exact hB₃_prop b hb_hi (le_trans hB₀_ge₃ hb_ge) E₁_lem E₂_lem hfb_cb
  constructor
  · have h_dist_zero : ∀ ε > 0,
    ‖riemannZeta s - (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) -
                       (a : ℂ) ^ (1 - s) / (1 - s) - c * (a : ℂ) ^ (-s) + E₁)‖ < ε := by
      intro ε hε
      obtain ⟨B₀, hB₀a, hB₀half, hforallb⟩ := h_eq_for_large_b ε hε
      obtain ⟨E₂, hEq, hTbound⟩ := hforallb B₀ hB₀half le_rfl
      rwa [show riemannZeta s -
            (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) -
              (a : ℂ) ^ (1 - s) / (1 - s) -
              c * (a : ℂ) ^ (-s) + E₁) =
          -(transient_error B₀ E₂) by linear_combination -hEq, norm_neg]
    apply eq_of_norm_sub_eq_zero
    rw [norm_eq_zero]
    apply eq_of_forall_dist_le
    intro ε hε
    rw [dist_zero_right]
    exact le_of_lt (h_dist_zero ε hε)
  · exact hE₁_bound

private theorem proposition_dadaro_zero_eq {s : ℂ} (hs1 : s ≠ 1) (hsigma : 0 = s.re) {a : ℝ} (ha : 0 < a)
    (ha' : a.IsHalfInteger) (haτ : a > |s.im| / (2 * π)) :
    let ϑ : ℝ := s.im / (2 * π * a)
    let C : ℝ :=
      if ϑ ≠ 0 then
        s.re / 2 * ((1 / (Complex.sin (π * ϑ) ^ 2 : ℂ)).re - (1 / ((π * ϑ) ^ 2 : ℂ)).re) +
          |ϑ| / (2 * π ^ 2) * ((1 / ((1 - |ϑ|) ^ 3 : ℝ)) + 2 * (riemannZeta 3).re - 1)
      else
        s.re / 6
    let c : ℂ :=
      if ϑ ≠ 0 then
        I / 2 * ((1 / Complex.sin (π * ϑ) : ℂ) - (1 / (π * ϑ : ℂ)))
      else
        0
    ∃ E : ℂ, riemannZeta s =
      ∑ n ∈ Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) -
      (a ^ (1 - s) : ℂ) / (1 - s) - c * (a ^ (-s) : ℂ) + E ∧
      ‖E‖ ≤ C / (a ^ (s.re + 1 : ℝ)) := by
  intro ϑ C c
  have h_continuous_extension :
    ContinuousAt (fun σ : ℝ => riemannZeta (σ + I * s.im)) 0 ∧
    ContinuousAt (fun σ : ℝ => ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-(σ + I * s.im))) 0 ∧
    ContinuousAt (fun σ : ℝ => ↑a ^ (1 - (σ + I * s.im)) / (1 - (σ + I * s.im))) 0 ∧
    ContinuousAt (fun σ : ℝ => c * ↑a ^ (-(σ + I * s.im))) 0 := by
    have hs_zero : (↑(0 : ℝ) + I * ↑s.im : ℂ) = s := by
      apply Complex.ext <;> simp [hsigma.symm]
    repeat' constructor
    · rw [show (fun σ : ℝ ↦ riemannZeta (↑σ + I * ↑s.im))= riemannZeta ∘ (fun σ : ℝ ↦ ↑σ + I * ↑s.im)
        by ext σ; simp]
      apply ContinuousAt.comp (g := riemannZeta) (f := fun σ : ℝ ↦ ↑σ + I * ↑s.im)
      · exact hs_zero.symm ▸ (differentiableAt_riemannZeta hs1).continuousAt
      · fun_prop
    · apply tendsto_finsetSum
      intro i hi
      simp only [Finset.mem_Icc] at hi
      apply ContinuousAt.cpow
      · exact continuousAt_const
      · fun_prop
      · left; norm_cast
        linarith
    · apply ContinuousAt.div
      · apply ContinuousAt.cpow
        · exact continuousAt_const
        · fun_prop
        · left; norm_cast
      · fun_prop
      · exact hs_zero.symm ▸ sub_ne_zero.mpr hs1.symm
    · apply ContinuousAt.mul
      · exact continuousAt_const
      · apply ContinuousAt.cpow
        · exact continuousAt_const
        · fun_prop
        · left; norm_cast
  have h_nearby_approximation : ∀ σ ∈ Set.Ioo (0 : ℝ) 1,
    ∃ E_σ : ℂ,
      riemannZeta (σ + I * s.im) =
        ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-(σ + I * s.im)) -
        ↑a ^ (1 - (σ + I * s.im)) / (1 - (σ + I * s.im)) -
        c * ↑a ^ (-(σ + I * s.im)) + E_σ ∧
      ‖E_σ‖ ≤ (if ϑ ≠ 0 then
          σ / 2 * ((1 / Complex.sin (π * ϑ : ℂ) ^ 2).re - (1 / (π * ϑ : ℂ) ^ 2).re) +
            |ϑ| / (2 * π ^ 2) * (1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1)
        else σ / 6) / a ^ (σ + 1) := by
    intro σ hσ
    obtain ⟨hσ_pos, hσ_lt_one⟩ := hσ
    set s_σ : ℂ := ↑σ + I * ↑s.im with hs_σ_def
    have hs_σ_ne_one : s_σ ≠ 1 := by
      rw [ne_eq, Complex.ext_iff, not_and_or]
      left
      rw [hs_σ_def]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
        Complex.I_im, Complex.ofReal_im, one_mul, sub_self, Complex.one_re]
      linarith
    have hs_σ_re_pos : 0 < s_σ.re := by
      rw [hs_σ_def]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
                zero_mul, Complex.I_im, Complex.ofReal_im, one_mul, sub_self, add_zero, hσ_pos]
    have hs_σ_im_bound : a > |s_σ.im| / (2 * π) := by
      rw [hs_σ_def]
      simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
                Complex.I_re, Complex.ofReal_re, mul_zero, Complex.I_im, one_mul]
      exact haτ
    obtain ⟨E_σ, hE_eq, hE_bound⟩ :=
      proposition_dadaro_zero_lt hs_σ_ne_one hs_σ_re_pos ha ha' hs_σ_im_bound
    use E_σ
    constructor
    · convert hE_eq using 2
      simp only [c, ϑ, s_σ]
      simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.I_re,
        Complex.ofReal_re, mul_zero, Complex.I_im, one_mul]
    · have hϑ_match : s_σ.im / (2 * π * a) = ϑ := by
        rw [hs_σ_def]
        simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
                  Complex.I_re, Complex.ofReal_re, mul_zero, Complex.I_im, one_mul]
        rfl
      have hre_match : s_σ.re = σ := by
        rw [hs_σ_def]
        simp
      convert hE_bound using 2
      · simp only [← hϑ_match, ← hre_match]
      · simp only [hre_match]
  rw [show s.re + 1 = 1 by rw [← hsigma]; norm_num]
  have hs_canonical : s = I * s.im := by
    apply Complex.ext
    · simp [hsigma.symm]
    · simp
  rw [hs_canonical]
  let σ_n : ℕ → ℝ := fun n => 1 / (n + 2 : ℝ)
  have hσ_n_mem : ∀ n, σ_n n ∈ Set.Ioo (0 : ℝ) 1 := by
    intro n
    constructor
    · simp only [one_div, inv_pos, σ_n]; positivity
    · simp only [one_div, σ_n]
      rw [inv_lt_one₀]
      · linarith
      · positivity
  have hE_n : ∀ n, ∃ E_n : ℂ,
    riemannZeta (↑(σ_n n) + I * ↑s.im) =
      ∑ k ∈ Finset.Icc 1 ⌊a⌋₊, (k : ℂ) ^ (-(↑(σ_n n) + I * ↑s.im)) -
      ↑a ^ (1 - (↑(σ_n n) + I * ↑s.im)) / (1 - (↑(σ_n n) + I * ↑s.im)) -
      c * ↑a ^ (-(↑(σ_n n) + I * ↑s.im)) + E_n ∧
    ‖E_n‖ ≤ (if ϑ ≠ 0 then
        σ_n n / 2 * ((1 / Complex.sin (π * ϑ : ℂ) ^ 2).re - (1 / (π * ϑ : ℂ) ^ 2).re) +
          |ϑ| / (2 * π ^ 2) * (1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1)
      else σ_n n / 6) / a ^ (σ_n n + 1) := fun n ↦
    h_nearby_approximation (σ_n n) (hσ_n_mem n)
  choose E_n hE_n_eq hE_n_bound using hE_n
  have h_lim_σ : Tendsto σ_n atTop (𝓝 0) := by
    simp only [one_div, σ_n]
    apply tendsto_inv_atTop_zero.comp
    apply Filter.tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_atTop
  let E := riemannZeta (I * s.im) - (∑ k ∈ Finset.Icc 1 ⌊a⌋₊, (k : ℂ) ^ (-(I * s.im) : ℂ) -
             ↑a ^ (1 - (I * s.im) : ℂ) / (1 - (I * s.im) : ℂ) - c * ↑a ^ (-(I * s.im) : ℂ))
  have hE_converges : Filter.Tendsto E_n Filter.atTop (𝓝 E) := by
    have : Tendsto (fun n ↦ riemannZeta (↑(σ_n n) + I * ↑s.im) -
        (∑ k ∈ Finset.Icc 1 ⌊a⌋₊, (k : ℂ) ^ (-(↑(σ_n n) + I * ↑s.im) : ℂ) -
          ↑a ^ (1 - (↑(σ_n n) + I * ↑s.im) : ℂ) / (1 - (↑(σ_n n) + I * ↑s.im) : ℂ) -
        c * ↑a ^ (-(↑(σ_n n) + I * ↑s.im) : ℂ))) atTop (𝓝 E) := by
      have h1 : Tendsto (fun n ↦ riemannZeta (↑(σ_n n) + I * ↑s.im)) atTop
          (𝓝 (riemannZeta (I * ↑s.im))) := by
        simpa only [Function.comp_def, Complex.ofReal_zero, zero_add] using h_continuous_extension.1.tendsto.comp h_lim_σ
      have h2 : Tendsto (fun n ↦ ∑ k ∈ Finset.Icc 1 ⌊a⌋₊, (k : ℂ) ^ (-(↑(σ_n n) + I * ↑s.im) : ℂ))
          atTop (𝓝 (∑ k ∈ Finset.Icc 1 ⌊a⌋₊, (k : ℂ) ^ (-(I * s.im) : ℂ))) := by
        simpa only [Function.comp_def, Complex.ofReal_zero, zero_add] using h_continuous_extension.2.1.tendsto.comp h_lim_σ
      have h3 : Tendsto (fun n ↦ ↑a ^ (1 - (↑(σ_n n) + I * ↑s.im) : ℂ) /
          (1 - (↑(σ_n n) + I * ↑s.im) : ℂ)) atTop
          (𝓝 (↑a ^ (1 - (I * s.im) : ℂ) / (1 - (I * s.im) : ℂ))) := by
        simpa only [Function.comp_def, Complex.ofReal_zero, zero_add] using h_continuous_extension.2.2.1.tendsto.comp h_lim_σ
      have h4 : Tendsto (fun n ↦ c * ↑a ^ (-(↑(σ_n n) + I * ↑s.im) : ℂ)) atTop
          (𝓝 (c * ↑a ^ (-(I * s.im) : ℂ))) := by
        simpa only [Function.comp_def, Complex.ofReal_zero, zero_add] using h_continuous_extension.2.2.2.tendsto.comp h_lim_σ
      exact Tendsto.sub h1 (Tendsto.sub (Tendsto.sub h2 h3) h4)
    exact this.congr (fun n ↦ by rw [hE_n_eq n]; ring)
  have hnormE_converges : Tendsto (fun n ↦ ‖E_n n‖) atTop (𝓝 ‖E‖) := by
    apply Filter.Tendsto.norm hE_converges
  let bound_n : ℕ → ℝ := fun n =>
    (if ϑ ≠ 0 then
        σ_n n / 2 * ((1 / Complex.sin (π * ϑ : ℂ) ^ 2).re - (1 / (π * ϑ : ℂ) ^ 2).re) +
        |ϑ| / (2 * π ^ 2) * (1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1)
      else σ_n n / 6) / a ^ (σ_n n + 1)
  have h_bound_converges : Tendsto bound_n atTop (𝓝 (C / a)) := by
    by_cases hϑ : ϑ = 0
    · simp only [hϑ, ne_eq, not_true_eq_false, ↓reduceIte, bound_n]
      have h_num : Tendsto (fun n ↦ σ_n n / 6) atTop (𝓝 0) := by
        simpa using h_lim_σ.div_const 6
      have h_den : Tendsto (fun n ↦ a ^ (σ_n n + 1)) atTop (𝓝 a) := by
        convert Tendsto.rpow tendsto_const_nhds (h_lim_σ.add tendsto_const_nhds) (Or.inl ha.ne')
        simp
      rw [show C = 0 by simp [C, hϑ, hsigma.symm, zero_div]]
      apply h_num.div h_den ha.ne'
    · simp only [ne_eq, hϑ, not_false_eq_true, ↓reduceIte, one_div, inv_re, map_pow, map_mul,
      normSq_ofReal, bound_n]
      have hC : C = |ϑ| / (2 * π ^ 2) * (1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1) := by
        simp only [ite_not, hϑ, ↓reduceIte, one_div, inv_re, map_pow, map_mul, normSq_ofReal,
          add_eq_right, mul_eq_zero, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false, C]
        rw [← hsigma]; simp
      have hnum : Tendsto (fun n ↦ σ_n n / 2 * ((1 / Complex.sin (π * ϑ : ℂ) ^ 2).re - (1 / (π * ϑ : ℂ) ^ 2).re) +
          C) atTop (𝓝 C) := by
        nth_rw 2 [← zero_add C]
        apply Tendsto.add
        · convert (h_lim_σ.div_const 2).mul_const ((1 / Complex.sin (π * ϑ : ℂ) ^ 2).re - (1 / (π * ϑ : ℂ) ^ 2).re)
          simp
        · exact tendsto_const_nhds
      have hden : Tendsto (fun n ↦ a ^ (σ_n n + 1)) atTop (𝓝 a) := by
        convert Tendsto.rpow tendsto_const_nhds (h_lim_σ.add tendsto_const_nhds) (Or.inl ha.ne')
        simp
      convert hnum.div hden (by positivity) using 1
      · ext n; dsimp; congr 1; rw [hC]
        have h_sin : (1 / Complex.sin ((π : ℂ) * (ϑ : ℂ)) ^ 2).re =
            (Complex.sin ((π : ℂ) * (ϑ : ℂ)) ^ 2).re / normSq (Complex.sin ((π : ℂ) * (ϑ : ℂ))) ^ 2 := by
          simp
        have h_th : (1 / ((π : ℂ) * (ϑ : ℂ)) ^ 2).re = (((π : ℂ) * (ϑ : ℂ)) ^ 2).re / (π * π * (ϑ * ϑ)) ^ 2 := by simp
        simp only [h_sin, h_th]; ring
  have h_norm_continuous : Tendsto (fun n => ‖E_n n‖) atTop (𝓝 ‖E‖) := hE_converges.norm
  have h_norm_bounded : ∀ n, ‖E_n n‖ ≤ bound_n n := by
    intro n
    simp_rw [bound_n]
    exact hE_n_bound n
  use E
  constructor
  · have h_lhs : Filter.Tendsto (fun n => riemannZeta (↑(σ_n n) + I * ↑s.im))
      Filter.atTop (𝓝 (riemannZeta (I * ↑s.im))) := by
      have h_lim_σ : Tendsto σ_n atTop (𝓝 0) := by
        simp only [one_div, σ_n]
        apply tendsto_inv_atTop_zero.comp
        apply Filter.tendsto_atTop_add_const_right
        exact tendsto_natCast_atTop_atTop
      have h_cont := h_continuous_extension.1.tendsto
      simpa only [Function.comp_def, Complex.ofReal_zero, zero_add] using h_cont.comp h_lim_σ
    have h_rhs : Filter.Tendsto (fun n =>
        ∑ k ∈ Finset.Icc 1 ⌊a⌋₊, (k : ℂ) ^ (-(↑(σ_n n) + I * ↑s.im)) -
        ↑a ^ (1 - (↑(σ_n n) + I * ↑s.im)) / (1 - (↑(σ_n n) + I * ↑s.im)) -
        c * ↑a ^ (-(↑(σ_n n) + I * ↑s.im)))
      Filter.atTop (𝓝 (∑ k ∈ Finset.Icc 1 ⌊a⌋₊, (k : ℂ) ^ (-(I * ↑s.im)) -
        ↑a ^ (1 - I * ↑s.im) / (1 - I * ↑s.im) - c * ↑a ^ (-(I * ↑s.im)))) := by
      have h1 := h_continuous_extension.2.1.tendsto.comp h_lim_σ
      have h2 := h_continuous_extension.2.2.1.tendsto.comp h_lim_σ
      have h3 := h_continuous_extension.2.2.2.tendsto.comp h_lim_σ
      simpa only [Function.comp_def, Pi.sub_def, Complex.ofReal_zero, zero_add] using (h1.sub h2).sub h3
    simp [E]
  · exact le_of_tendsto_of_tendsto h_norm_continuous (by simp [h_bound_converges])
      (Filter.Eventually.of_forall h_norm_bounded)

theorem proposition_dadaro {s : ℂ} (hs1 : s ≠ 1) (hsigma : 0 ≤ s.re) {a : ℝ} (ha : 0 < a)
    (ha' : a.IsHalfInteger) (haτ : a > |s.im| / (2 * π)) :
    let ϑ : ℝ := s.im / (2 * π * a)
    let C : ℝ :=
      if ϑ ≠ 0 then
        s.re / 2 * ((1 / (Complex.sin (π * ϑ) ^ 2 : ℂ)).re - (1 / ((π * ϑ) ^ 2 : ℂ)).re) +
          |ϑ| / (2 * π ^ 2) * ((1 / ((1 - |ϑ|) ^ 3 : ℝ)) + 2 * (riemannZeta 3).re - 1)
      else
        s.re / 6
    let c : ℂ :=
      if ϑ ≠ 0 then
        I / 2 * ((1 / Complex.sin (π * ϑ) : ℂ) - (1 / (π * ϑ : ℂ)))
      else
        0
    ∃ E : ℂ, riemannZeta s =
      ∑ n ∈ Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) -
      (a ^ (1 - s) : ℂ) / (1 - s) - c * (a ^ (-s) : ℂ) + E ∧
      ‖E‖ ≤ C / (a ^ (s.re + 1 : ℝ)) := by
  rcases hsigma.eq_or_lt with hsigma_eq | hsigma_lt
  · exact proposition_dadaro_zero_eq hs1 hsigma_eq ha ha' haτ
  · exact proposition_dadaro_zero_lt hs1 hsigma_lt ha ha' haτ

end ZetaAppendix
