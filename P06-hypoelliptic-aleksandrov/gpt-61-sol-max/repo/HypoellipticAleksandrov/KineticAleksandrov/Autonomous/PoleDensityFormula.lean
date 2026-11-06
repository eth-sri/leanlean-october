module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityTransport
import Aesop



/-! # Remove the actual velocity weight and obtain the physical pole density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal NNReal

variable (c : Clock)

/-- The inverse velocity weight is masked to the actual physical active interval. -/
def poleInverseVelocity  (p : Point) : ℝ :=
  by
    classical
    exact if p.velocity 0 ∈ c.active then 1 / |p.velocity 0| else 0

/-- The masked inverse velocity weight is Borel. -/
theorem poleInverseVelocity_measurable  : Measurable (poleInverseVelocity c) := by
  classical
  unfold poleInverseVelocity
  exact Measurable.ite (isOpen_Ioo.preimage ((continuous_apply 0).comp
    continuous_velocity)).measurableSet
    (measurable_const.div (((continuous_apply 0).comp continuous_velocity).abs.measurable))
    measurable_const

variable (p : Point)

/-- The masked inverse weight is everywhere nonnegative. -/
theorem poleInverseVelocity_nonneg   : 0 ≤ poleInverseVelocity c p := by
  simp_all [poleInverseVelocity] <;> aesop

/-- The active strip bounds the inverse velocity uniformly by twice the inverse centre speed. -/
theorem poleInverseVelocity_le   :
    poleInverseVelocity c p ≤ 2 / |c.vbar| := by
  have hc : 0 < |c.vbar| := abs_pos.mpr c.nonzero
  unfold poleInverseVelocity
  split
  next hp =>
    have hb := (c.active_abs_bounds hp).1

    apply (div_le_div_iff₀ (lt_of_lt_of_le (by linarith) hb) hc).mpr
    nlinarith
  next => exact div_nonneg (by norm_num) hc.le

variable (e : Point) (F : Point → ℝ)

/-- The literal physical pole density obtained by removing the velocity weight. -/
def polePhysicalDensity   (p : Point) : ℝ :=
  ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p)) * poleInverseVelocity c p

/-- The physical density formula is Borel. -/
theorem polePhysicalDensity_measurable
    (hF : Measurable F) : Measurable (polePhysicalDensity c e F) :=
  (measurable_const.mul (hF.comp (c.continuous_map e).measurable)).mul
    (poleInverseVelocity_measurable c)

/-- The physical density formula is nonnegative when the normalized density is nonnegative. -/
theorem polePhysicalDensity_nonneg
    (hF : ∀ p, 0 ≤ F p) (p : Point) : 0 ≤ polePhysicalDensity c e F p := mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (inv_nonneg.mpr (pow_nonneg c.positive.le _)))
    (hF _)) (poleInverseVelocity_nonneg c p)

/-- The actual physical Green has exactly the density computed from the actual normalized one. -/
theorem clock_physical_green_density
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active)
    (F : Point → ℝ) (hF : Measurable F) (hFn : ∀ p, 0 ≤ F p)
    (hFd : clockGreen hH hLE hlam hLam A c e he =
      volume.withDensity (fun p => ENNReal.ofReal (F p))) :
    stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩ =
      volume.withDensity (fun p => ENNReal.ofReal (polePhysicalDensity c e F p)) := by

  let sharedTerm_7e920acf5e := ((fun p => ENNReal.ofReal (poleInverseVelocity c p)))
  let μ := stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩


  have hm : Measurable (((fun p => ENNReal.ofReal ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p))))) := (measurable_const.mul (hF.comp
        (c.continuous_map e).measurable)).ennreal_ofReal
  have hp := withDensity_mul (volume : Measure Point) hm
    (poleInverseVelocity_measurable c).ennreal_ofReal

  exact (show (μ.withDensity (fun p => ENNReal.ofReal |p.velocity 0|)).withDensity
      sharedTerm_7e920acf5e = μ by
      rw [← withDensity_mul μ clock_velocity_weight_measurable
        (poleInverseVelocity_measurable c).ennreal_ofReal]

      exact (withDensity_congr_ae (by
          filter_upwards [stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval
            _] with p hp
          have hc : 0 < |c.vbar| := abs_pos.mpr c.nonzero


          change ENNReal.ofReal |p.velocity 0| * ENNReal.ofReal (poleInverseVelocity c p) = 1
          rw [poleInverseVelocity, ite_eq_left (show p.velocity 0 ∈ c.active from hp.2), ← ENNReal.ofReal_mul (abs_nonneg _),
            mul_one_div_cancel (show 0 < |p.velocity 0| from lt_of_lt_of_le (by linarith) (c.active_abs_bounds hp.2).1).ne', ENNReal.ofReal_one])).trans withDensity_one).symm.trans ((congrArg (fun ν : Measure Point => ν.withDensity
    sharedTerm_7e920acf5e) (clock_weightedGreen_density hH hLE hlam hLam A c e he F hF hFn hFd)).trans
      (hp.symm.trans (congrArg (fun g : Point → ℝ≥0∞ => volume.withDensity g) (by
          funext p
          exact (ENNReal.ofReal_mul (mul_nonneg (mul_nonneg
            (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (inv_nonneg.mpr (pow_nonneg c.positive.le _)))
            (hFn _))).symm))))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
