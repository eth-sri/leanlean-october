module

public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenDensity
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelGreen
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Finite-horizon cylinder Green measures and their source integrals -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open MeasureTheory SectionTwo

variable {d : ℕ}

variable (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 ))) (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)

/-- Whole-space Green measure ending at the cylinder's terminal time, in absolute coordinates. -/
def cylinderGreenMeasure
     (P : KineticPoint d) :
    Measure (KineticPoint d) :=
  if h : P.time < Z₀.time + R ^ 2 then
    ((greenMeasure K P.time (ENNReal.ofReal (Z₀.time + R ^ 2 - P.time))
      (ENNReal.ofReal_pos.mpr (sub_pos.mpr h))
      (Measure.dirac (kineticStartState d P))).map (greenKineticPoint d P.time)).restrict
      (forwardCylinder Z₀ R hR)
  else 0

/-- Interior source integrals are exactly the Section 2 Duhamel potentials. -/
theorem integral_cylinderGreenMeasure

    (g : HypoellipticAleksandrov.KineticScalarField d) (hg0 : ∀ P, 0 ≤ g P)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgQ : tsupport g ⊆ forwardCylinder Z₀ R hR)
    (P : KineticPoint d) (hP : P.time < Z₀.time + R ^ 2) :
    (∫ z, g z ∂cylinderGreenMeasure K Z₀ R hR P) =
      duhamelPotential K (Z₀.time + R ^ 2) (g ∘ sectionTwoPoint) (sectionTwoPoint P) := by
  classical
  rw [cylinderGreenMeasure, dite_eq_left hP]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun h => hz (hgQ h)))]
  rw [(measurableEmbedding_greenKineticPoint d P.time _).integral_map]
  symm


  exact duhamelPotential_eq_green K MeasurableSet.univ continuous_const
    (Z₀.time + R ^ 2) (g ∘ sectionTwoPoint) (fun q => hg0 _) (hg.comp (continuous_sectionTwoPoint d)) (hasCompactSupport_sectionTwoPoint hgc) P.time hP
    (kineticStartState d P) _
    (greenMeasure_spec K P.time _ _ _)

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
