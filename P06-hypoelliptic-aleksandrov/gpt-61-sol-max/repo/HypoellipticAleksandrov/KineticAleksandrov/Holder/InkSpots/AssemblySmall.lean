module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots.AssemblyArithmetic
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Leakage
import Mathlib.Tactic

/-! # Assembly for small radius cutoffs and small delayed height -/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots

open Set MeasureTheory Covering

/-- Small-cutoff ink spots follow from critical density, delayed unions and the two shells. -/
theorem ink_spots_small_cutoff {d : ℕ} {E F : Set (KineticPoint d)}
    (hE : NullMeasurableSet E ) (hbounded : Bornology.IsBounded E)
    (hEQ : E ⊆ unitCylinder d) {eta R : ℝ} (heta : 0 < eta) (heta1 : eta < 1)
    (hR : 0 < R) (hRsmall : R ≤ 1/4) (m : ℕ) (hm : 0 < m)
    (hheight : (m : ℝ)*R^2 ≤ 1)
    (hstack : ∀ P r, 0 < r → backwardCylinder P r ⊆ unitCylinder d →
      (1-eta)*(volume (backwardCylinder P r)).toReal ≤
        (volume (E ∩ backwardCylinder P r)).toReal →
      r < R ∧ forwardStack P r m ⊆ F) :
    (volume E).toReal ≤ (((m : ℝ)+1)/(m : ℝ))*(1-coveringGain d*eta)*
      ((volume (F ∩ unitCylinder d)).toReal+coveringLeakage d*(m : ℝ)*R^2) := by
  let sharedTerm_427eeb7ab8 := (2 * (d : ℝ) * (volume (unitCylinder d)).toReal * R ^ 2)
  let sharedTerm_2c245da4ab := ((m : ℝ) * R ^ 2)
  have hcutoff  :=
    fun P r hr hsub hd => (hstack P r hr hsub hd).1

  have hred := criticalUnion_density_reduction hE heta.le hcutoff

  have hEfinite  := volume_bounded_ne_top hbounded


  have hsum := congrArg ENNReal.toReal (measure_inter_add_sdiff₀ (μ := volume) E
    (isOpen_criticalUnion E eta).measurableSet.nullMeasurableSet)
  rw [ENNReal.toReal_add (ne_top_of_le_ne_top hEfinite (measure_mono inter_subset_left)) (ne_top_of_le_ne_top hEfinite (measure_mono sdiff_subset))] at hsum
  have he : (volume E).toReal ≤ (1-coveringGain d*eta)*(volume (criticalUnion E eta)).toReal+
      sharedTerm_427eeb7ab8 := by
    have heq : eta/(8 : ℝ)^(4*d+2) = coveringGain d*eta := by
      rw [coveringGain, div_eq_mul_inv, mul_comm]
    rw [heq] at hred
    linarith only [hsum, hred, (volume_outside_criticalUnion_le hE hbounded hEQ heta hR hRsmall hcutoff)]
  have ha := density_factor_bounds d heta heta1

  have hdelay' := mul_le_mul_of_nonneg_left (criticalUnion_delay_bound hR (hRsmall.trans (by norm_num)) m hm hheight hstack)
    (by linarith only [ha.1] : 0 ≤ 1-coveringGain d*eta)


  have hb := absorb_covering_errors
    (ENNReal.toReal_nonneg (a := volume (unitCylinder d)))
    (by positivity : 0 ≤ (5 : ℝ)^d) (Nat.cast_nonneg d) ha.1 (delay_multiplier_ge_one hm)
    (by positivity : 0 ≤ sharedTerm_2c245da4ab) (show R^2 ≤ sharedTerm_2c245da4ab by
        have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
        nlinarith [sq_nonneg R]) (show (volume E).toReal ≤
      (1-coveringGain d*eta)*(((m : ℝ)+1)/(m : ℝ))*
        ((volume (F ∩ unitCylinder d)).toReal+
          2*(5 : ℝ)^d*(volume (unitCylinder d)).toReal*(sharedTerm_2c245da4ab))+
      sharedTerm_427eeb7ab8 by
        nlinarith only [he, hdelay'])
  simpa only [coveringLeakage, mul_assoc] using hb

end HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots
