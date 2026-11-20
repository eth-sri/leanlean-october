/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.SegFactors
public import DOZZ.ShiftEquations.DualR.DualL
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
import DOZZ.Brownian.Reflection.WitnessIndependence
import DOZZ.Brownian.Reflection.RtheorAnalytic
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
import DOZZ.ShiftEquations.Rbar.Continuation
public import DOZZ.ShiftEquations.Representatives

/-!
# The second dual crossing seed on its whole two-triple extended domain

The second dual crossing seed (`DOZZ.dual_crossing_seed_two`, [KRV, Proposition 9.10])
`R(ε) C(2Q - ε - 2/γ, α, α') = L(ε, α, α') R(α) C(ε, 2Q - α - 2/γ, α')` holds for `ε, α, α' < Q`
with `α + ε + α' > 2Q + 2/γ`. The real points where both triples lie in the extended Seiberg domain
form a convex set containing that seed region, and every factor is meromorphic along its segments
(the reflection coefficient through a strip-meromorphic representative `R`, the structure constants
through `DOZZ.unitVolumeStructureConstant_holomorphic_near_extended_domain`, `L` through `l`).
Continuing along a segment from the seed region gives the identity at every point of that set where
all factors are analytic: the source's first continuation step in the proof of the `2/γ` shift
equation ([KRV, §10.5]).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **The second dual crossing seed on the two-triple extended domain.** `hSeed` is the conclusion
of `DOZZ.dual_crossing_seed_two` at the given field, chaos and coupling; `R` is any
strip-meromorphic function with the physical reflection values. -/
theorem seed_full {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hSeed : HasDualCrossing P X M γ μ)
    {hR : ℝ} (hhR : 0 < hR) {R : ℂ → ℂ} (hRm : MeromorphicOn R (horizontalStrip hR))
    {BR : ℝ → Ω → BrownianPath × BrownianPath} {ZR : Ω → Measure ℝ}
    (hBR : IsReflectionFamily P γ BR ZR)
    (hRv : RepresentsReflection P γ μ BR ZR R)
    {ε α α' : ℝ} (h₁ : ExtendedSeiberg3 γ (2 * Q γ - ε - 2 / γ) α α')
    (h₂ : ExtendedSeiberg3 γ ε (2 * Q γ - α - 2 / γ) α')
    (hRε : AnalyticAt ℂ R (ε : ℂ)) (hRα : AnalyticAt ℂ R (α : ℂ))
    (hs₁ : AnalyticAt ℂ Complex.Gamma (sExp γ (2 * Q γ - ε - 2 / γ) α α' : ℂ))
    (hs₂ : AnalyticAt ℂ Complex.Gamma (sExp γ ε (2 * Q γ - α - 2 / γ) α' : ℂ))
    (g₁ : AnalyticAt ℂ Complex.Gamma (dualArg₁ γ ε))
    (g₂ : AnalyticAt ℂ Complex.Gamma (dualArg₂ γ α))
    (g₃ : AnalyticAt ℂ Complex.Gamma (1 - dualArg₃ γ ε α α'))
    (g₄ : AnalyticAt ℂ Complex.Gamma (1 - dualArg₄ γ ε α α')) :
    R ε * (structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' : ℂ) =
      dualLC γ ε α α' * R α * (structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α' : ℂ) := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh := half_gamma_lt_two_div hγ hγ2
  have h2γ : 0 < 2 / γ := by positivity
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  -- the seed point
  set e₀ : ℝ := Q γ - γ / 12 with he₀
  have hq₀₁ : ExtendedSeiberg3 γ (2 * Q γ - e₀ - 2 / γ) e₀ e₀ :=
    extendedSeiberg3_of_lt hγ (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)
  have hq₀₂ : ExtendedSeiberg3 γ e₀ (2 * Q γ - e₀ - 2 / γ) e₀ :=
    extendedSeiberg3_of_lt hγ (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)
  have hstart : ∀ᶠ t : ℝ in 𝓝[>] 0,
      let e := e₀ + t * (ε - e₀)
      let a := e₀ + t * (α - e₀)
      let b := e₀ + t * (α' - e₀)
      R e * (structureConstant P M γ μ (2 * Q γ - e - 2 / γ) a b : ℂ) =
        dualLC γ e a b * R a * (structureConstant P M γ μ e (2 * Q γ - a - 2 / γ) b : ℂ) := by
    have h0 : e₀ < Q γ := by linarith
    have hs : 2 * Q γ + 2 / γ < e₀ + e₀ + e₀ := by linarith
    filter_upwards [eventually_segC_mem (b := ε) (N := Iio (Q γ)) isOpen_Iio h0,
      eventually_segC_mem (b := α) (N := Iio (Q γ)) isOpen_Iio h0,
      eventually_segC_mem (b := α') (N := Iio (Q γ)) isOpen_Iio h0,
      eventually_segC_mem (b := ε + α + α') (N := Ioi (2 * Q γ + 2 / γ)) isOpen_Ioi hs]
      with t he ha hb hsum
    dsimp only at he ha hb hsum ⊢
    set e := e₀ + t * (ε - e₀)
    set a := e₀ + t * (α - e₀)
    set b := e₀ + t * (α' - e₀)
    have hsum' : 2 * Q γ + 2 / γ < a + e + b := by linarith [mem_Ioi.mp hsum]
    obtain ⟨Be, Ba, Z, -, hBe, hBa, hseed⟩ := hSeed a e b ha he hb hsum'
    have heγ : γ / 2 < e := by linarith [mem_Iio.mp ha, mem_Iio.mp hb]
    have haγ : γ / 2 < a := by linarith [mem_Iio.mp he, mem_Iio.mp hb]
    rw [dualLC_ofReal hγ.ne', hRv _ heγ he, hRv _ haγ ha,
      reflectionR_eq_of_isReflectionData P P γ μ _ (BR _) ZR Be Z (hBR _ heγ he) hBe,
      reflectionR_eq_of_isReflectionData P P γ μ _ (BR _) ZR Ba Z (hBR _ haγ ha) hBa]
    exact_mod_cast hseed
  simpa only [one_mul, sub_zero] using
    (dual_seed_eq_at_segment_end P X M hγ hγ2 hμ hX hM hhR hRm (δ := 0) (A := fun _ _ _ => 1)
      (fun _ => analyticAt_const.meromorphicAt) analyticAt_const (by simpa using hq₀₁) hq₀₂
      (by simpa using h₁) h₂ hRε hRα (by simpa using hs₁) hs₂ g₁ g₂ g₃ g₄
      (by simpa only [one_mul, sub_zero] using hstart))

end DOZZ.Proofs

end
