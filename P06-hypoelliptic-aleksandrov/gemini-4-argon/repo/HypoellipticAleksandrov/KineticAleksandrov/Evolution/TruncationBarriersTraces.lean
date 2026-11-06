module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FiniteSlabBarriers
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationBarriers
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierIntervalGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveLipschitz
import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

/-!
# Uniform boundary traces for the actual viscous solutions

Companion paper, (A.1), zero-viscosity part.  For a family `u_ε`, `ε ∈ (0, 1]`, of viscous classical
terminal solutions with smooth compactly supported terminal datum `F`, the terminal trace
`u_ε → F(p₀)` at a terminal point `p₀` and the lateral trace `u_ε → 0` at a lateral point `p₀` hold
uniformly in `ε`: the neighbourhood `O` of `p₀` for a given tolerance `η` does not depend on `ε`.

The proof chooses a finite slab around `p₀`, the Lipschitz constant of `γ` on it, the
collar scale `d_*` from the distance of the compact support of `F` to the terminal boundary, and
the operator bound `M` of `FiniteSlabBarriersTerminal`, and then applies the two barriers
on balls or on the whole space.
The admissible interval domains of dimension `1` are balls (`BarrierIntervalGeometry`).
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology MatrixOrder

/- The collar scale: the compact support of a terminal datum of the moving ball lies at positive
distance from the terminal boundary, so some `d_* < r/4` has `2 d_* ≤` that distance. -/
theorem terminal_trace_of_window {n } {ι : Type*} {Ω γ τ} (F : BoundedBorel (EvolutionAmbientState n))
    (hF : Continuous (F : EvolutionAmbientState n → ℝ)) (u : ι → KineticPoint n → ℝ)
    {M δ₀ : ℝ} (hM0 : 0 ≤ M) (hδ₀ : 0 < δ₀)
    (hwin : ∀ i, ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, τ - δ₀ < p.time →
      |u i p - F (p.position, p.velocity)| ≤ (τ - p.time) * M)
    {p₀ : KineticPoint n} (hp₀ : p₀.time = τ) {η : ℝ} (hη : 0 < η) :
    ∃ O : Set (KineticPoint n), IsOpen O ∧ p₀ ∈ O ∧
      ∀ i, ∀ p ∈ O ∩ evolutionPastClosedCylinder Ω γ τ,
        |u i p - F (p₀.position, p₀.velocity)| ≤ η := by
  have hK : 0 < η / (2 * (M + 1)) := by positivity
  set δ := min δ₀ (η / (2 * (M + 1))) with hδ
  have hδpos := lt_min hδ₀ hK
  have hFe :=
    hF.comp (continuous_position.prodMk continuous_velocity)
  refine ⟨{p | τ - δ < p.time} ∩
    {p | |F (p.position, p.velocity) - F (p₀.position, p₀.velocity)| < η / 2}, ?_, ?_, ?_⟩
  · exact (isOpen_lt continuous_const continuous_time).inter
      (isOpen_lt ((hFe.sub continuous_const).abs) continuous_const)
  · refine ⟨?_, ?_⟩
    · show τ - δ < p₀.time
      rw [hp₀]
      linarith
    · show |F (p₀.position, p₀.velocity) - F (p₀.position, p₀.velocity)| < η / 2
      simp only [sub_self, abs_zero]
      linarith
  · rintro i p ⟨⟨hpt, hpF⟩, hcyl⟩
    have hpt' : τ - δ < p.time := hpt
    have hpF' : |F (p.position, p.velocity) - F (p₀.position, p₀.velocity)| < η / 2 := hpF
    have hδ₀le : δ ≤ δ₀ := min_le_left _ _
    have hδKle : δ ≤ η / (2 * (M + 1)) := min_le_right _ _
    have h1 := hwin i p hcyl (by linarith)
    have h2 : (τ - p.time) * M ≤ δ * M :=
      mul_le_mul_of_nonneg_right (by linarith) hM0
    have h3 : δ * M ≤ η / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right hδKle hM0
    have h4 : η / (2 * (M + 1)) * M ≤ η / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h5 := abs_sub_le (u i p) (F (p.position, p.velocity)) (F (p₀.position, p₀.velocity))
    linarith

/- **Uniform traces** (companion paper, (A.1), zero-viscosity part).  Uniform terminal and lateral
traces for the family of actual viscous solutions: for every terminal point `p₀` and tolerance `η`
there is a neighbourhood `O` of `p₀`, independent of `ε ∈ (0, 1]`, on which `|u_ε - F(p₀)| ≤ η`
(past cylinder), and likewise `|u_ε| ≤ η` near every lateral frontier point.  The standing premises
(`Ω` admissible, `γ` continuous piecewise `C¹`, the Loewner bounds of `B`, the Lipschitz drift)
are explicit. -/
end HypoellipticAleksandrov.KineticAleksandrov
