module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeak

/-! # Terminal traces for signed bounded Borel source potentials

The finite-time contraction gives continuity at the terminal face without regularity
of the source. Lateral continuity requires a separate uniform spatial barrier.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open Set Filter

open scoped Topology
variable {d : ℕ} {Ω : PDE.VelocityRegion d} {γ : ℝ → PDE.Vec d}

variable (K : MovingFiberKernel Ω γ) (g : HypoellipticAleksandrov.KineticScalarField d) (M : ℝ) (hM : 0 ≤ M) (hgb : ∀ p, |g p| ≤ M) (T : ℝ) (p : KineticPoint d) (hp : p.time = T)

include hM hgb hp
/-- Signed bounded potentials tend to zero at every point of the terminal face. -/
theorem tendsto_duhamelPotential_terminal  :
    Tendsto (duhamelPotential K T g) (𝓝 p) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2


  apply squeeze_zero (fun _ => norm_nonneg _) (fun q => ?_) (by
      simpa only [hp, sub_self, abs_zero, zero_mul] using ((show Continuous (fun q : KineticPoint d => |T - q.time| * M) from (continuous_const.sub continuous_time).abs.mul continuous_const).continuousAt (x := p)).tendsto)
  rw [Real.norm_eq_abs]
  exact abs_duhamelPotential_le_abs_time K g M hM hgb q T

/-- The zero extension is continuous at terminal points for every bounded signed source. -/
theorem continuousAt_duhamelPotential_terminal  :
    ContinuousAt (duhamelPotential K T g) p := by
  rw [ContinuousAt, duhamelPotential_eq_zero_of_terminal_le K T g p hp.ge]
  exact tendsto_duhamelPotential_terminal K g M hM hgb T p hp

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
