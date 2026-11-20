module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityTransport

/-! # Remove the actual velocity weight and obtain the physical pole density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal NNReal

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) (F : Point → ℝ) (hF : Measurable F)
    (p : Point)

include c p in
/-- The inverse velocity weight is masked to the actual physical active interval. -/
def poleInverseVelocity : ℝ :=
  by
    classical
    exact if p.velocity 0 ∈ c.active then 1 / |p.velocity 0| else 0

/-- The masked inverse velocity weight is Borel. -/
theorem poleInverseVelocity_measurable : Measurable (poleInverseVelocity c) := by
  classical
  exact Measurable.ite (isOpen_Ioo.preimage ((continuous_apply 0).comp
    continuous_velocity)).measurableSet
    (measurable_const.div (((continuous_apply 0).comp continuous_velocity).abs.measurable))
    measurable_const

/-- The masked inverse weight is everywhere nonnegative. -/
theorem poleInverseVelocity_nonneg : 0 ≤ poleInverseVelocity c p := by
  unfold poleInverseVelocity
  split
  · positivity
  positivity

/-- The active strip bounds the inverse velocity uniformly by twice the inverse centre speed. -/
theorem poleInverseVelocity_le :
    poleInverseVelocity c p ≤ 2 / |c.vbar| := by
  have hc := abs_pos.mpr c.nonzero
  unfold poleInverseVelocity
  split
  next hp =>
    have hb := (c.active_abs_bounds hp).1
    apply (div_le_div_iff₀ (lt_of_lt_of_le (by linarith) hb) hc).mpr
    nlinarith
  positivity

include c e F p in
/-- The literal physical pole density obtained by removing the velocity weight. -/
def polePhysicalDensity : ℝ :=
  ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p)) * poleInverseVelocity c p

include hF in
/-- The physical density formula is Borel. -/
theorem polePhysicalDensity_measurable : Measurable (polePhysicalDensity c e F) :=
  (measurable_const.mul (hF.comp (c.continuous_map e).measurable)).mul
    (poleInverseVelocity_measurable c)

/-- The physical density formula is nonnegative when the normalized density is nonnegative. -/
theorem polePhysicalDensity_nonneg
    (hF : ∀ p, 0 ≤ F p) (p : Point) : 0 ≤ polePhysicalDensity c e F p := mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (inv_nonneg.mpr (pow_nonneg c.positive.le _)))
    (hF _)) (poleInverseVelocity_nonneg c p)

include hF in
/-- The actual physical Green has exactly the density computed from the actual normalized one. -/
theorem clock_physical_green_density (hFn : ∀ p, 0 ≤ F p)
    (hFd : clockGreen hlam hLam A c e he =
      volume.withDensity (fun p => ENNReal.ofReal (F p))) :
    stripGreen hlam hLam A c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩ =
      volume.withDensity (fun p => ENNReal.ofReal (polePhysicalDensity c e F p)) := by
  let μ := stripGreen hlam hLam A c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩
  have hi : (μ.withDensity (fun p => ENNReal.ofReal |p.velocity 0|)).withDensity
      (fun p => ENNReal.ofReal (poleInverseVelocity c p)) = μ := by
    rw [← withDensity_mul μ clock_velocity_weight_measurable
      (poleInverseVelocity_measurable c).ennreal_ofReal]
    have hh : ((fun p => ENNReal.ofReal |p.velocity 0|) *
        fun p => ENNReal.ofReal (poleInverseVelocity c p)) =ᵐ[μ] 1 := by
      filter_upwards [stripGreen_infinite_ae_future_carrier hlam hLam A c.activeInterval
        ⟨e, WithTop.coe_lt_top _, he⟩] with p hp
      have hc := abs_pos.mpr c.nonzero
      have hv : 0 < |p.velocity 0| := lt_of_lt_of_le (by linarith) (c.active_abs_bounds hp.2).1
      have hpactive : p.velocity 0 ∈ c.active := hp.2
      change ENNReal.ofReal |p.velocity 0| * ENNReal.ofReal (poleInverseVelocity c p) = 1
      rw [poleInverseVelocity, ite_eq_left hpactive, ← ENNReal.ofReal_mul (abs_nonneg _),
        mul_one_div_cancel hv.ne', ENNReal.ofReal_one]
    exact (withDensity_congr_ae hh).trans withDensity_one
  have hw := clock_weightedGreen_density hlam hLam A c e he F hF hFn hFd
  have hm : Measurable (fun p => ENNReal.ofReal
      ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p))) := (measurable_const.mul (hF.comp
        (c.continuous_map e).measurable)).ennreal_ofReal
  have hp := withDensity_mul volume hm
    (poleInverseVelocity_measurable c).ennreal_ofReal
  have hg : ((fun p => ENNReal.ofReal
      ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p))) *
      fun p => ENNReal.ofReal (poleInverseVelocity c p)) =
      fun p => ENNReal.ofReal (polePhysicalDensity c e F p) := by
    funext p
    exact (ENNReal.ofReal_mul (mul_nonneg (mul_nonneg
      (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (inv_nonneg.mpr (pow_nonneg c.positive.le _)))
      (hFn _))).symm
  exact hi.symm.trans ((congrArg (fun ν : Measure Point => ν.withDensity
    (fun p => ENNReal.ofReal (poleInverseVelocity c p))) hw).trans
      (hp.symm.trans (congrArg (fun g : Point → ℝ≥0∞ => volume.withDensity g) hg)))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
