module
public import GuthMaynard.Improvement.ShortDetectorOrdinateTail
public import MathCollab.Density.Packing
import WeylPort.Analytic.RealLaplace

public section
open Complex MeasureTheory Set Filter
open scoped Topology
namespace GuthMaynard.Improvement

/-- One polynomial-decay envelope works for every beta in the short strip. -/
theorem short_gamma_decay :
    ∃ K : ℝ, 0 < K ∧ ∀ β t : ℝ, 9/13 ≤ β → β ≤ 1 →
      ‖Complex.Gamma (((1/2-β:ℝ):ℂ)+(t:ℂ)*I)‖ ≤ K/(1+|t|)^2 := by
  refine ⟨576*Real.exp 1,by positivity,?_⟩
  intro β t hβ hβ'
  pm_4569 β hg
  have hgamma : ‖Complex.Gamma (((1/2-β:ℝ):ℂ)+(t:ℂ)*I)‖ ≤ 96*(1+|t|)*Real.exp (-|t|) :=
    hg.trans (by gcongr)
  have hp := Real.pow_div_factorial_le_exp (1+|t|) (show 0 ≤ 1+|t| by positivity) 3
  norm_num at hp
  have hp' : (1+|t|)^3 ≤ 6*Real.exp (1+|t|) := by linarith
  have he : Real.exp (1+|t|)*Real.exp (-|t|) = Real.exp 1 := by
    pm_6012
  have hprod : (1+|t|)^3*Real.exp (-|t|) ≤ 6*Real.exp 1 := by
    calc
      _ ≤ (6*Real.exp (1+|t|))*Real.exp (-|t|) := mul_le_mul_of_nonneg_right hp' (Real.exp_pos _).le
      _ = _ := by grind
  pm_569 t
  calc
    _ ≤ (96*(1+|t|)*Real.exp (-|t|))*(1+|t|)^2 := mul_le_mul_of_nonneg_right hgamma (by positivity)
    _ = 96*((1+|t|)^3*Real.exp (-|t|)) := by ring
    _ ≤ _ := by nlinarith

/-- Restricted weighted fourth Hölder, with all compact-window integrability
proved from continuity. The proof is the two-Cauchy--Schwarz local analogue. -/
theorem short_window_fourth_holder {g F : ℝ → ℝ} (hg0 : ∀ t, 0 ≤ g t)
    (hg : Continuous g) (hf : Continuous F) (a b : ℝ) :
    (∫ t in Icc a b, g t*F t)^4 ≤
      (∫ t in Icc a b,g t)^3*(∫ t in Icc a b,g t*(F t)^4) := by
  let k := (Icc a b).indicator g
  have hk : Integrable k := hg.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have he (q : ℕ) : (fun t => k t*(F t)^q) = (Icc a b).indicator (fun t => g t*(F t)^q) := by
    funext t
    by_cases ht : t ∈ Icc a b <;> simp [k,ht]
  have hi (q : ℕ) : Integrable (fun t => k t*(F t)^q) := by
    rw [he]
    exact (hg.mul (hf.pow q)).integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hh := short_weighted_fourth_holder (g := k) (F := F)
    (fun t => indicator_nonneg (fun t _ => hg0 t) t) hk
    (by simpa only [pow_one] using hi 1) (hi 2) (hi 4)
  have hid : (fun t => k t*F t) = (Icc a b).indicator (fun t => g t*F t) := by
    simpa only [pow_one] using he 1
  rw [hid,he 4,integral_indicator measurableSet_Icc,integral_indicator measurableSet_Icc] at hh
  simpa only [k,integral_indicator measurableSet_Icc] using hh

/-- The short-strip Gamma L1 constant precedes all window and source choices. -/
theorem short_gamma_window_holder :
    ∃ G : ℝ, 0 < G ∧ ∀ β H u R : ℝ, 9/13 ≤ β → β ≤ 1 →
      (∫ t in Icc (-R) R, ‖Complex.Gamma (((1/2-β:ℝ):ℂ)+(t:ℂ)*I)‖*
        shortTwistedNorm H (u+t))^4 ≤ G^3*
      (∫ t in Icc (-R) R, ‖Complex.Gamma (((1/2-β:ℝ):ℂ)+(t:ℂ)*I)‖*
        (shortTwistedNorm H (u+t))^4) := by
  pm_155 G hG hmass short_uniform_detector_gamma_mass
  intro β H u R hβ hβ'
  pm_994 β
  have hg : Continuous g := (short_continuous_Gamma_detector_strip (by linarith) (by linarith)).norm
  have hf : Continuous (fun t => shortTwistedNorm H (u+t)) := (shortTwistedNorm_continuous H).comp (by fun_prop)
  have hh := short_window_fourth_holder (fun t => norm_nonneg _) hg hf (-R) R
  have hi := (hmass β hβ hβ').1.norm
  have hgi : (∫ t,g t) ≤ G := by
    apply le_trans _ (hmass β hβ hβ').2.2
    apply integral_mono hi (hmass β hβ hβ').2.1
    intro t
    nlinarith [abs_nonneg t,norm_nonneg (Complex.Gamma (((1/2-β:ℝ):ℂ)+(t:ℂ)*I))]
  have hmassR : (∫ t in Icc (-R) R,g t) ≤ G :=
    (setIntegral_le_integral hi (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).trans hgi
  have hpow := pow_le_pow_left₀ (integral_nonneg (fun _ => norm_nonneg _)) hmassR 3
  exact hh.trans (mul_le_mul_of_nonneg_right hpow (integral_nonneg (fun t => by positivity)))

end GuthMaynard.Improvement
