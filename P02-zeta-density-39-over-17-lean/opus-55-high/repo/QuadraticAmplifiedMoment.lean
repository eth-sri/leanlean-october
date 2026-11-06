module
public import QuadraticScalarMass
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The intended amplified fourth-moment comparison for the actual finite
polynomial and actual centered matrices. Every amplifier and operator input
is proved. The centered quadratic trace is retained. -/
theorem finite_quadratic_amplified_moment (w : MathCollab.Density.ComparisonCutoff)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T N L : ℝ, 1 < T → 1 ≤ N → N ≤ L → L ≤ T →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (W.card:ℝ)^2*V^4 ≤ C*T^η*((N*L)^2+(N^3/L)*
        (Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^2)).re) := by
  have hδ : 0 < η/2 := by positivity
  pm_107 A D hA hD h finite_quadratic_large_value_comparison w hδ
  let C₀ := (2*A*2^(η/2))^2
  pm_64 hC₀ C₀
  refine ⟨4*C₀*(D^2+2),by positivity,?_⟩
  intro T N L hT hN hNL hLT a ha W V hV hlarge hsep
  pm_4516
  have hLp : 0 < L := hNp.trans_le hNL
  let P := A*(1+L)^(η/2)*(N+1)
  let Z := (Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^2)).re
  pm_64 hP P
  have hgate := h N L hNp hNL a ha W V hV hlarge hsep
  change (L/(2*N))*(max (((W.card:ℝ)*V^2)/P-D*L) 0)^2 ≤ Z at hgate
  pm_349 quadratic_mass_scalar
  have hpcube : P^2 ≤ C₀*T^η*N^2 := by
    have hb : (1+L)^(η/2) ≤ 2^(η/2)*T^(η/2) := by
      calc
        _ ≤ (2*T)^(η/2) := Real.rpow_le_rpow (by positivity) (by linarith) hδ.le
        _ = _ := Real.mul_rpow (by norm_num) hTp.le
    have hp : P ≤ (2*A*2^(η/2))*T^(η/2)*N := by
      calc
        _ ≤ A*(2^(η/2)*T^(η/2))*(2*N) := by
          pm_6519
        _ = _ := by ring
    have he : (T^(η/2))^2 = T^η := by
      rw [← Real.rpow_natCast (T^(η/2)) 2,← Real.rpow_mul hTp.le]
      congr 1
      ring
    have hh := pow_le_pow_left₀ hP.le hp 2
    simpa only [mul_pow,he,C₀] using hh
  pm_561
  have hbr : (D*L)^2+2*(N/L)*Z ≤ (D^2+2)*(L^2+(N/L)*Z) := by
    have hp : 0 ≤ (D^2)*((N/L)*Z) := by positivity
    have hq : 0 ≤ 2*L^2 := by positivity
    nlinarith
  have hfinal : ((W.card:ℝ)*V^2)^2 ≤
      4*(C₀*T^η*N^2)*((D^2+2)*(L^2+(N/L)*Z)) := by
    pm_5699
  have he : N^2*(L^2+(N/L)*Z) = (N*L)^2+(N^3/L)*Z := by ring
  calc
    _ = ((W.card:ℝ)*V^2)^2 := by ring
    _ ≤ _ := hfinal
    _ = (4*C₀*(D^2+2))*T^η*((N*L)^2+(N^3/L)*Z) := by rw [← he]; ring

end Montgomery.RationalMoment
