module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.HeatBarrier
import Mathlib.Topology.Algebra.Order.Field
public import PDEFoundation.Calculus.RegularityOrder


/-! # Positive-time regularity and terminal limit of the half-line killing barrier -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set Filter Topology

/-- The heat barrier is jointly smooth wherever its time parameter is positive. -/
theorem contDiffAt_intervalHeat {lam : ℝ} (hlam : 0 < lam)
    (p : ℝ × ℝ) (hp : 0 < p.1) :
    ContDiffAt ℝ PDE.smoothOrder (fun q : ℝ × ℝ => intervalHeat lam q.1 q.2) p := contDiff_intervalErf.contDiffAt.comp p
    (contDiffAt_snd.div (contDiffAt_const.mul ((contDiffAt_const.mul contDiffAt_fst).sqrt (mul_pos hlam hp).ne'))
      (mul_ne_zero (by norm_num) (Real.sqrt_pos.2 (mul_pos hlam hp)).ne'))

/-- Positive distance has terminal heat-barrier limit one as time decreases to zero. -/
theorem tendsto_intervalHeat_time_zero {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) :
    Tendsto (fun θ => intervalHeat lam θ x) (nhdsWithin 0 (Ioi 0)) (𝓝 1) := (Tendsto.comp tendsto_intervalErf_atTop
  (Tendsto.const_mul_atTop hx
    (Tendsto.inv_tendsto_nhdsGT_zero
      (tendsto_nhdsWithin_iff.mpr
        ⟨Eq.mp
            (congrArg (Tendsto (fun x => 2 * √(lam * x)) (𝓝[>] 0))
              (congrArg 𝓝 (Eq.trans (congrArg (HMul.hMul 2) Real.sqrt_zero) (mul_zero 2))))
            (Tendsto.mul tendsto_const_nhds
              (Tendsto.comp (ContinuousAt.tendsto (Continuous.continuousAt Real.continuous_sqrt))
                (Eq.mp (congrArg (Tendsto (fun x => lam * x) (𝓝[>] 0)) (congrArg 𝓝 (mul_zero lam)))
                  (Tendsto.mul tendsto_const_nhds (Tendsto.mono_left tendsto_id nhdsWithin_le_nhds))))),
          mp_mem self_mem_nhdsWithin
            (univ_mem'
              (id fun θ hθ =>
                mul_pos
                  (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl false))
                  (Real.sqrt_pos.mpr (mul_pos hlam hθ))))⟩))))

/-- Fixed positive-time heat barriers are increasing with spatial distance. -/
theorem intervalHeat_mono_distance {lam θ : ℝ} (hlam : 0 < lam) (hθ : 0 < θ) :
    Monotone (intervalHeat lam θ) := by
  intro x y hxy
  exact strictMono_intervalErf.monotone
    ((div_le_div_iff_of_pos_right (mul_pos (by norm_num)
      (Real.sqrt_pos.2 (mul_pos hlam hθ)))).mpr hxy)

end HypoellipticAleksandrov.KineticAleksandrov.Interval
