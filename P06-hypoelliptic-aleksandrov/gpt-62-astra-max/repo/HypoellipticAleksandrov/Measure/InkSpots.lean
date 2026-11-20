module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicSaturation
public import HypoellipticAleksandrov.Measure.InkSpotsWind
public import HypoellipticAleksandrov.Measure.InkSpotsHotWind

/-!
# Aggregate ink-spots volume estimate

This file composes the dyadic saturation, wind, and hot-wind bounds into the
Krylov--Safonov Lemma 2.5 estimate for the third ink-spots enlargement.
-/

@[expose] public section

open MeasureTheory Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- Krylov--Safonov, Lemma 2.5: the initial measurable set is controlled by its third
ink-spots enlargement. -/
theorem volume_Gamma_le_inkSpotsD3
    (d : Nat) (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real)
    (hGamma : MeasurableSet Gamma)
    (hGammaUnit : Gamma ⊆ inkSpotsUnitBox d)
    (hxi : xi ∈ Set.Ioo (0 : Real) 1)
    (heta : eta ∈ Set.Ioo (0 : Real) 1)
    (hzeta : zeta ∈ Set.Ioo (0 : Real) 1)
    (hsubcritical : (volume Gamma).toReal <
      xi * (volume (inkSpotsUnitBox d)).toReal) :
    (volume Gamma).toReal ≤
      xi * (1 + eta) * zeta ^ (-((d : Int) + 2)) *
        (volume (inkSpotsD3 Gamma xi eta zeta)).toReal := by
  have hxi_nonneg := hxi.1.le
  calc
    (volume Gamma).toReal ≤ xi * (volume (inkSpotsD1 Gamma xi)).toReal := ((volume_Gamma_le_xi_volume_inkSpotsD1 d Gamma xi hGamma hGammaUnit hxi hsubcritical).2)
    _ ≤ xi * ((1 + eta) * (volume (inkSpotsD2 Gamma xi eta)).toReal) :=
      mul_le_mul_of_nonneg_left (volume_inkSpotsD1_toReal_le_one_add_eta_mul_D2 Gamma xi eta heta.1 heta.2) hxi_nonneg
    _ ≤ xi * ((1 + eta) * (zeta ^ (-((d : Int) + 2)) *
        (volume (inkSpotsD3 Gamma xi eta zeta)).toReal)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (volume_inkSpotsD2_toReal_le_zeta_zpow_mul_D3 Gamma xi eta zeta heta.1 hzeta.1 hzeta.2) ((add_pos_of_pos_of_nonneg zero_lt_one heta.1.le).le)) hxi_nonneg
    _ = xi * (1 + eta) * zeta ^ (-((d : Int) + 2)) *
        (volume (inkSpotsD3 Gamma xi eta zeta)).toReal := by
      simp [mul_assoc]

end

end HypoellipticAleksandrov.Parabolic
