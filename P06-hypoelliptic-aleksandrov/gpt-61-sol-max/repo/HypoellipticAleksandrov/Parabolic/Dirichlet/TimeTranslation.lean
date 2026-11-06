module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Local translation continuity for reverse-time Bochner spaces

This module obtains local literal-representative `L²` translation continuity
from the continuous domain-add action on ambient `Lp`.  The local statements
use a zero extension only as an `Lp` representative; they make no derivative
claim for that extension.
-/

 public section

open Filter MeasureTheory Set Topology
open scoped ENNReal



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {E : Type*}

private theorem sqNorm_integral_eq_norm_sq_toLp
     [NormedAddCommGroup E]
    {μ : Measure ℝ} (F : ℝ → E) (hF : MemLp F (2 ) μ) :
    ∫ t, ‖F t‖ ^ 2 ∂μ = ‖hF.toLp F‖ ^ 2 := by
  rw [Lp.norm_def, eLpNorm_congr_ae hF.coeFn_toLp,
    hF.eLpNorm_eq_integral_rpow_norm]
  · simp
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)]
    exact (Real.rpow_inv_natCast_pow
      (integral_nonneg fun _ => sq_nonneg _) (by norm_num)).symm
  · norm_num
  · simp

private theorem tendsto_sqNorm_integral_translate_add_on_of_memLp_two
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 ) ) (s : Set ℝ) :
    Tendsto (fun h : ℝ => ∫ t in s, ‖F (t + h) - F t‖ ^ 2) (𝓝 0) (𝓝 0) := by
  let sharedTerm_fa63ca10ff := (Lp (α := ℝ) E (2 ) volume)
  let f : sharedTerm_fa63ca10ff := hF.toLp F
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

  have hzero : DomAddAct.mk (0 : ℝ) +ᵥ f = f := by
    simp

  have hvalue : (DomAddAct.mk (0 : ℝ) +ᵥ f) - f = 0 := by
    rw [hzero, sub_self]
  have hsub : Tendsto (fun h : ℝ => (DomAddAct.mk h +ᵥ f) - f) (𝓝 0) (𝓝 0) := by
    have hat : Tendsto (fun h : ℝ => (DomAddAct.mk h +ᵥ f) - f) (𝓝 0)
        (𝓝 ((DomAddAct.mk (0 : ℝ) +ᵥ f) - f)) :=
      ((continuous_vadd.comp (DomAddAct.continuous_mk.prodMk continuous_const)).sub continuous_const).continuousAt
    rw [hvalue] at hat
    exact hat

  refine squeeze_zero (g := fun h : ℝ => ‖(DomAddAct.mk h +ᵥ f) - f‖ ^ 2)
    (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun h => ?_) (by
        simpa using hsub.norm.pow 2)

  let hdiff : MemLp (fun t  => F (h + t) - F t) (2 )  :=
    (hF.comp_measurePreserving (measurePreserving_add_left volume h)).sub hF
  let q : sharedTerm_fa63ca10ff := hdiff.toLp _
  let qS : Lp  E (2 ) (volume.restrict s) :=
    ((Lp.memLp q).restrict s).toLp q


  have hsq : (∫ t in s, ‖F (t + h) - F t‖ ^ 2) = ‖qS‖ ^ 2 := by
    change (∫ t, ‖F (t + h) - F t‖ ^ 2 ∂volume.restrict s) = _
    have hqSsq := sqNorm_integral_eq_norm_sq_toLp _ (Lp.memLp qS)
    rw [Lp.toLp_coeFn qS (Lp.memLp qS)] at hqSsq
    rw [← hqSsq]
    apply integral_congr_ae
    filter_upwards [(show qS =ᵐ[volume.restrict s] q by
        simpa [qS] using MemLp.coeFn_toLp ((Lp.memLp q).restrict s)), ae_restrict_of_ae (hdiff.coeFn_toLp)] with t htS ht
    rw [htS, ht, add_comm]
  rw [hsq]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_Lp_toLp_restrict_le s q) 2

/-- Forward local translation continuity on a compact interval inside reverse time. -/
theorem tendsto_sqNorm_integral_forward_translate_on_Icc
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc a b, ‖f (t + h) - f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let S  := Ioo 0 T
  let F  := S.indicator f
  have hS : MeasurableSet S := by
    simp only [S]
    exact measurableSet_Ioo


  have hglobal := tendsto_sqNorm_integral_translate_add_on_of_memLp_two F (by
      simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
        (memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)) (Icc a b)

  apply Filter.Tendsto.congr' ?_ (hglobal.mono_left (nhdsWithin_le_nhds  (s := Ioi (0 ))))

  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < T - b :=
    (eventually_lt_nhds (sub_pos.mpr hb)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hsmall
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht


  simp only [F, Set.indicator_of_mem (show t + h ∈ S by
      change 0 < t + h ∧ t + h < T
      constructor
      · exact add_pos (lt_of_lt_of_le ha ht.1) hh
      ·
        calc
          t + h = h + t := add_comm _ _
          _ ≤ h + b := add_le_add_right ht.2 _
          _ = b + h := add_comm _ _
          _ < T := (by
              rw [add_comm]
              exact lt_sub_iff_add_lt.mp hsmall)), Set.indicator_of_mem (show t ∈ S by
      change 0 < t ∧ t < T
      constructor
      · exact lt_of_lt_of_le ha ht.1
      · calc
          t ≤ b := ht.2
          _ ≤ max a b := le_max_right _ _
          _ < T := (by
              rw [max_eq_right hab]
              exact hb))]

end HypoellipticAleksandrov.Parabolic.Dirichlet
