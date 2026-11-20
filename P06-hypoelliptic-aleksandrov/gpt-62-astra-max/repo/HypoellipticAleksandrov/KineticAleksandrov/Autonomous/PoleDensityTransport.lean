module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityNormalized

/-! # Exact pullback of physical normalized densities through the actual clock -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal NNReal

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) (F : Point → ℝ) (hF : Measurable F)

include hF in
/-- The inverse clock pulls a physical Lebesgue density back using the literal Jacobian map. -/
theorem poleDensity_clock_map_withDensity :
    ((volume : Measure Point).withDensity (fun p => ENNReal.ofReal (F p))).map (c.inverse e) =
      ((volume : Measure Point).map (c.inverse e)).withDensity
        (fun p => ENNReal.ofReal (F (c.map e p))) := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (c.continuous_inverse e).measurable hS,
    withDensity_apply _ ((c.continuous_inverse e).measurable hS), withDensity_apply _ hS]
  have hm := setLIntegral_map (μ := volume)
    (f := fun p => ENNReal.ofReal (F (c.map e p))) hS
    (hF.comp (c.continuous_map e).measurable).ennreal_ofReal
    (c.continuous_inverse e).measurable
  refine (lintegral_congr (fun p => ?_)).trans hm.symm
  exact congrArg (fun q : Point => ENNReal.ofReal (F q)) (c.map_inverse e p).symm

/-- Inverse mapping the actual pushforward recovers the original weighted physical Green. -/
theorem clock_weightedGreen_inverse :
    (stripGreen hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity (fun p => ENNReal.ofReal |p.velocity 0|) =
      ENNReal.ofReal (|c.vbar| * c.r ^ 2) •
        (clockGreen hlam hLam A c e he).map (c.inverse e) := by
  have hi (μ : Measure Point) : (μ.map (c.map e)).map (c.inverse e) = μ := by
    rw [Measure.map_map (c.continuous_inverse e).measurable (c.continuous_map e).measurable]
    have heq : c.inverse e ∘ c.map e = id := funext (c.inverse_map e)
    rw [heq, Measure.map_id]
  exact (hi _).symm.trans ((congrArg (fun μ : Measure Point => μ.map (c.inverse e)) (clock_green_pushforward hlam hLam A c e he)).trans (Measure.map_smul _ (c.continuous_inverse
    e).measurable.aemeasurable))

include hF in
/-- A proved real normalized density yields the exact weighted physical density with the clock
Jacobian factor; no density bridge is assumed. -/
theorem clock_weightedGreen_density (_hFn : ∀ p, 0 ≤ F p)
    (hFd : clockGreen hlam hLam A c e he =
      volume.withDensity (fun p => ENNReal.ofReal (F p))) :
    (stripGreen hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity (fun p => ENNReal.ofReal |p.velocity 0|) =
      volume.withDensity (fun p => ENNReal.ofReal
        ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p))) := by
  have hD : 0 ≤ |c.vbar| * c.r ^ 2 := mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hr : 0 ≤ (c.r ^ 6)⁻¹ := inv_nonneg.mpr (pow_nonneg c.positive.le _)
  refine (clock_weightedGreen_inverse hlam hLam A c e he).trans ((congrArg (fun μ : Measure Point => ENNReal.ofReal (|c.vbar| * c.r ^ 2) • μ.map (c.inverse e)) hFd).trans ?_)
  rw [(poleDensity_clock_map_withDensity c e F hF), (c.map_inverse_volume e), withDensity_smul_measure, smul_smul]
  have hx := withDensity_smul' (μ := volume)
    (ENNReal.ofReal (|c.vbar| * c.r ^ 2) * ENNReal.ofReal ((c.r ^ 6)⁻¹))
    (fun p => ENNReal.ofReal (F (c.map e p)))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  refine hx.symm.trans ?_
  apply congrArg (fun g : Point → ℝ≥0∞ => volume.withDensity g)
  funext p
  exact ((ENNReal.ofReal_mul (mul_nonneg hD hr)).trans
    (congrArg (fun x : ℝ≥0∞ => x * ENNReal.ofReal (F (c.map e p)))
      (ENNReal.ofReal_mul hD))).symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
