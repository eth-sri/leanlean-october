module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarTails
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarMatching
import Mathlib.Tactic

/-!
# Position-derivative leading-term cancellation

The source position derivative loses three similarity degrees. This uses actual differentiated
remainders, rather than differentiation of an undifferentiated asymptotic statement.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Asymptotics
open scoped Topology

variable (f : ℝ → ℝ)

/-- Differentiating the positive-ray power remainder at an actual differentiability point. -/
theorem scalar_power_remainder_deriv  (alpha c s : ℝ) (hs : 0 < s)
    (hf : DifferentiableAt ℝ f s) :
    deriv (fun t => f t - c * Real.rpow t alpha) s =
      deriv f s - c * alpha * Real.rpow s (alpha - 1) := by


  simpa only [Real.rpow_eq_pow, mul_assoc, Pi.sub_def] using (hf.hasDerivAt.sub ((Real.hasDerivAt_rpow_const (p := alpha) (Or.inl hs.ne')).const_mul c)).deriv

/-- Positive-ray cancellation of the leading homogeneous solution. -/
theorem scalar_power_cancellation  (gamma c s : ℝ) (hs : 0 < s)
    (hf : DifferentiableAt ℝ f s) :
    gamma * f s - s / 3 * deriv f s =
      gamma * (f s - c * Real.rpow s (3 * gamma)) - s / 3 *
        deriv (fun t => f t - c * Real.rpow t (3 * gamma)) s := by
  rw [scalar_power_remainder_deriv f (3 * gamma) c s hs hf]
  have he : s * Real.rpow s (3 * gamma - 1) = Real.rpow s (3 * gamma) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub hs, Real.rpow_one]
    field_simp
  calc
    _ = gamma * f s - s / 3 * deriv f s +
        c * gamma * (s * Real.rpow s (3 * gamma - 1) - Real.rpow s (3 * gamma)) := by
      rw [he]
      ring
    _ = _ := by ring

variable (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)

include hLam
/-- The actual joined profile's positive position-derivative tail has three lower degrees. -/
theorem F_position_cancellation_atTop  :
    IsBigO atTop (fun s => gamma.1 * F gamma Lam s - s / 3 * deriv (F gamma Lam) s)
      (fun s => Real.rpow s (3 * gamma.1 - 3)) := by
  let sharedTerm_9fc5c37e37 := ((3 * gamma.1 - 3))
  let c : ℝ := Real.rpow (9 * Lam) (-gamma.1)
  let E  := fun s => Fplus gamma Lam s - c * Real.rpow s (3 * gamma.1)


  have hM := Kummer.rpow_mul_isBigO_of_add_eq (deriv E) 1 (3 * gamma.1 - 4)
    sharedTerm_9fc5c37e37 (((Fplus_tail_derivatives gamma Lam hLam).1)) (by ring)
  have hR : IsBigO atTop (fun s => gamma.1 * E s - (1 / 3 : ℝ) * (s * deriv E s))
      (fun s => Real.rpow s sharedTerm_9fc5c37e37) := by

    exact ((Fplus_asymptotic gamma Lam hLam).const_mul_left gamma.1).sub ((show IsBigO atTop (fun s => s * deriv E s)
        (fun s => Real.rpow s sharedTerm_9fc5c37e37) by
        simpa only [Real.rpow_one] using hM).const_mul_left (1 / 3 : ℝ))
  apply hR.congr' _ (EventuallyEq.rfl)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have he : F gamma Lam =ᶠ[𝓝 s] Fplus gamma Lam := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    simp only [F, show 0 < t from ht, ↓reduceIte]
  have hd  :=
    ((F_contDiff_two gamma Lam hLam).differentiable (by norm_num) s).congr_of_eventuallyEq
      he.symm
  rw [he.eq_of_nhds, he.deriv_eq, scalar_power_cancellation _ gamma.1 c s hs hd]
  dsimp only [E]
  ring

/-- The actual joined profile has the corresponding cancellation on the negative ray. -/
theorem F_position_cancellation_atBot
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    IsBigO atBot (fun s => gamma.1 * F gamma Lam s - s / 3 * deriv (F gamma Lam) s)
      (fun s => Real.rpow |s| (3 * gamma.1 - 3)) := by
  let c : ℝ := Real.rpow (9 * Lam) (-gamma.1)
  let f  := fun s => Fminus gamma Lam (-s)
  let E  := fun s => f s - c * Real.rpow s (3 * gamma.1)
  have hE := Fminus_negative_ray_asymptotic_of_M_expansion
    Kummer.M_negative_expansion gamma Lam hLam
  have hdE := (Fminus_negative_ray_tail_derivatives_of_M_jets
    Kummer.M_negative_expansion_jet gamma Lam hLam).1
  rw [scalar_matching_trace_coefficient gamma Lam hLam hmatch] at hE hdE
  have hM := Kummer.rpow_mul_isBigO_of_add_eq (deriv E) 1 (3 * gamma.1 - 4)
    (3 * gamma.1 - 3) (hdE) (by ring)


  have hRay : IsBigO atTop (fun s => gamma.1 * F gamma Lam (-s) -
      (-s) / 3 * deriv (F gamma Lam) (-s))
      (fun s => Real.rpow s (3 * gamma.1 - 3)) := by
    apply ((hE.const_mul_left gamma.1).sub ((show IsBigO atTop (fun s => s * deriv E s)
      (fun s => Real.rpow s (3 * gamma.1 - 3)) by
        simpa only [Real.rpow_one] using hM).const_mul_left (1 / 3 : ℝ))).congr' _ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have he : F gamma Lam =ᶠ[𝓝 (-s)] Fminus gamma Lam := by
      filter_upwards [Iio_mem_nhds (neg_neg_of_pos hs)] with t ht
      simp only [F, show t < 0 from ht, not_lt.mpr (show t < 0 from ht).le, ↓reduceIte]

    rw [he.eq_of_nhds, he.deriv_eq]

    have hc := scalar_power_cancellation f gamma.1 c s hs ((contDiff_Fminus gamma Lam).differentiable (by norm_num) (-s) |>.comp s
          differentiableAt_id.neg)
    rw [(deriv_comp_neg _ _)] at hc
    dsimp only [f] at hc
    dsimp only [E, f]
    linear_combination -hc

  apply (hRay.comp_tendsto tendsto_neg_atBot_atTop).congr' _ _
  · exact Eventually.of_forall fun s => by simp only [Function.comp_def, neg_neg]
  · filter_upwards [eventually_lt_atBot (0 : ℝ)] with s hs
    simp only [Function.comp_def, abs_of_neg hs]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
