module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityTransport
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityNormalized

/-! # Remove the actual velocity weight and obtain the physical pole density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal NNReal

/- The inverse velocity weight is masked to the actual physical active interval. -/
def poleInverseVelocity (c : Clock) (p : Point) : ℝ :=
  by
    classical
    exact if p.velocity 0 ∈ c.active then 1 / |p.velocity 0| else 0

/- The masked inverse velocity weight is Borel. -/
theorem poleInverseVelocity_measurable (c : Clock) : Measurable (poleInverseVelocity c) := by
  classical
  unfold poleInverseVelocity
  exact Measurable.ite (isOpen_Ioo.preimage ((continuous_apply 0).comp
    continuous_velocity)).measurableSet
    (measurable_const.div (((continuous_apply 0).comp continuous_velocity).abs.measurable))
    measurable_const

/- The masked inverse weight is everywhere nonnegative. -/
def polePhysicalDensity (c : Clock) (e : Point) (F : Point → ℝ) (p : Point) : ℝ :=
  ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p)) * poleInverseVelocity c p

/- The physical density formula is Borel. -/
theorem polePhysicalDensity_measurable (c : Clock) (e : Point) (F )
    (hF : Measurable F) : Measurable (polePhysicalDensity c e F) :=
  (measurable_const.mul (hF.comp (c.continuous_map e).measurable)).mul
    (poleInverseVelocity_measurable c)

/- The physical density formula is nonnegative when the normalized density is nonnegative. -/
theorem polePhysicalDensity_nonneg (c : Clock) (e : Point) (F : Point → ℝ)
    (hF : ∀ p, 0 ≤ F p) (p : Point) : 0 ≤ polePhysicalDensity c e F p := by
  have _h_inl_10 : 0 ≤ poleInverseVelocity c p := by
    unfold poleInverseVelocity
    split
    · exact div_nonneg zero_le_one (abs_nonneg _)
    · exact le_rfl
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (inv_nonneg.mpr (pow_nonneg c.positive.le _)))
    (hF _)) _h_inl_10

/- The actual physical Green has exactly the density computed from the actual normalized one. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
