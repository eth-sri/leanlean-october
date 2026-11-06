module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellCountBounds

/-! # The literal source box actions of full-space terminal and occupation measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical ENNReal

/- Full-space terminal mass in the physical source box is its elapsed box probability. -/
theorem positionStartBox_slab_ofReal_integral (E : FullSpaceEvolution) (z : Z)
    (r Y a b : ℝ) :
    ENNReal.ofReal (∫ t in Ioc a b, (kernelXV E (Real.toNNReal t) z (box 4 r Y)).toReal) =
      ∫⁻ t in Ioc a b, kernelXV E (Real.toNNReal t) z (box 4 r Y) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (position_box_probability_integrable E z 4 r Y a b)
    (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
  apply lintegral_congr
  intro t
  exact ENNReal.ofReal_toReal ((measure_mono (subset_univ _)).trans_lt
    ((kernelXV_mass_le_one E (Real.toNNReal t) z).trans_lt ENNReal.one_lt_top)).ne

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
