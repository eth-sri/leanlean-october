/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.FirstShiftFull
import DOZZ.ShiftEquations.Gluing.BandNear
import DOZZ.Brownian.Reflection.RtheorAnalytic
import DOZZ.Brownian.Reflection.WitnessIndependence
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
import DOZZ.ShiftEquations.Rbar.Continuation
public import DOZZ.ShiftEquations.Representatives

/-!
# The reflected γ/2 shift on the whole two-triple extended domain

For spectators near `Q` and `x ∈ (Q, Q + γ)` the reflected shift
`R(x) C(2Q - x) = -𝒜(x - γ/2) C(x - γ)/(πμ)` holds at exact real points where `R` is analytic
(`DOZZ.structureConstant_reflected_shift_and_gluing`, `reflectedShift_exact_of_strip`), for any
strip-meromorphic `R` with the physical reflection values. The real triples `(x, b, c)` with
`(2Q - x, b, c)` and `(x - γ, b, c)` in the extended Seiberg domain form a convex set along whose
segments all factors are meromorphic. Continuing from the near-`Q` box gives the reflected shift at
every real point of that set where `R`, `Γ` at both `s`-parameters and the shift coefficient are
analytic: the second half of the gluing lemma ([KRV, Lemma 10.5]).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) {γ μ : ℝ}
  (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
include hγ hγ2 hμ hX hM

/-- **The reflected shift near `Q` from `DOZZ.structureConstant_reflected_shift_and_gluing`**, for a
strip-meromorphic `R` with the physical reflection values, at every real point of the near-`Q` box
where `R` is analytic. -/
theorem reflectedShift_nearQ_of_reflected_shift_and_gluing {η : ℝ} (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hShiftGluing : HasShiftGluingAt P X M γ μ η)
    {hR : ℝ} (hhR : 0 < hR) {R : ℂ → ℂ} (hRm : MeromorphicOn R (horizontalStrip hR))
    {BR : ℝ → Ω → BrownianPath × BrownianPath} {ZR : Ω → Measure ℝ}
    (hBR : IsReflectionFamily P γ BR ZR)
    (hRv : RepresentsReflection P γ μ BR ZR R)
    (y b c : ℝ) (hy₁ : Q γ < y) (hy₂ : y < Q γ + γ) (hb₁ : Q γ - η < b) (hb₂ : b < Q γ)
    (hc₁ : Q γ - η < c) (hc₂ : c < Q γ) (hRy : AnalyticAt ℂ R (y : ℂ)) :
    R y * (structureConstant P M γ μ (2 * Q γ - y) b c : ℂ) = -(1 / (Real.pi * μ)) *
      shiftCoeffA γ (γ / 2) ((y : ℂ) - γ / 2) b c * (structureConstant P M γ μ (y - γ) b c : ℂ) := by
  obtain ⟨V₃, f₃, hExt⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  obtain ⟨B, Z, -, hBd, h, hh, C, Rs, hCm, hRsm, hCv, hRsv, -, hrefl⟩ :=
    hShiftGluing b c ⟨hb₁, hb₂⟩ ⟨hc₁, hc₂⟩
  set h' : ℝ := min h hR with hh'
  have hh'pos  := lt_min hh hhR
  have hsub₁ : horizontalStrip h' ⊆ {z : ℂ | |z.im| < h} := fun z hz =>
    lt_of_lt_of_le (show |z.im| < h' from hz) (min_le_left _ _)
  have hsub₂ : horizontalStrip h' ⊆ horizontalStrip hR := fun z hz =>
    lt_of_lt_of_le (show |z.im| < h' from hz) (min_le_right _ _)
  have hRsR : ∀ α : ℝ, γ / 2 < α → α < Q γ → Rs (α : ℂ) = R (α : ℂ) := fun α h1 h2 => by
    rw [hRsv α h1 h2, hRv α h1 h2,
      reflectionR_eq_of_isReflectionData P P γ μ α (B α) Z (BR α) ZR (hBd α h1 h2) (hBR α h1 h2)]
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  have hgood : ShiftCoeffGood γ ((y : ℂ) - γ / 2) b c :=
    shiftCoeffGood_of_lt hγ (by linarith) (by linarith [hη.1, hη.2])
      (by linarith [hη.1, hη.2]) (by linarith [hη.1, hη.2]) (by linarith [hη.1, hη.2])
  have hAy  :=
    analyticAt_shiftCoeffA_comp (f₁ := id) (f₂ := fun _ => (b : ℂ)) (f₃ := fun _ => (c : ℂ))
      analyticAt_id analyticAt_const analyticAt_const hgood
  exact reflectedShift_exact_of_strip P M hγ hγ2 hμ hη ⟨hb₁, hb₂⟩ ⟨hc₁, hc₂⟩ hExt hh'pos (hCm.mono_set hsub₁) (hRsm.mono_set hsub₁) (hRm.mono_set hsub₂) hCv hRsR hrefl
    hy₁ hy₂ hRy hAy

/-- **The reflected shift on the two-triple extended domain**, from
`DOZZ.structureConstant_reflected_shift_and_gluing`: for a strip-meromorphic `R` with the physical
reflection values, at every real `(x, b, c)` with `(2Q - x, b, c)` and `(x - γ, b, c)` in the
extended Seiberg domain, `R` analytic at `x`, `Γ` analytic at both `s`-parameters and the shift
coefficient analytic. -/
theorem reflectedShift_full
    (hShiftGluing : HasShiftGluing P X M γ μ)
    {hR : ℝ} (hhR : 0 < hR) {R : ℂ → ℂ} (hRm : MeromorphicOn R (horizontalStrip hR))
    {BR : ℝ → Ω → BrownianPath × BrownianPath} {ZR : Ω → Measure ℝ}
    (hBR : IsReflectionFamily P γ BR ZR)
    (hRv : RepresentsReflection P γ μ BR ZR R)
    {x b c : ℝ} (h₁ : ExtendedSeiberg3 γ (2 * Q γ - x) b c)
    (h₂ : ExtendedSeiberg3 γ (x - γ) b c) (hRx : AnalyticAt ℂ R (x : ℂ))
    (hs₁ : AnalyticAt ℂ Complex.Gamma (sExp γ (2 * Q γ - x) b c : ℂ))
    (hs₂ : AnalyticAt ℂ Complex.Gamma (sExp γ (x - γ) b c : ℂ))
    (hA : ShiftCoeffGood γ ((x : ℂ) - γ / 2) b c) :
    R x * (structureConstant P M γ μ (2 * Q γ - x) b c : ℂ) = -(1 / (Real.pi * μ)) *
      shiftCoeffA γ (γ / 2) ((x : ℂ) - γ / 2) b c * (structureConstant P M γ μ (x - γ) b c : ℂ) := by
  obtain ⟨V₃, f₃, hExt⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh := half_gamma_lt_two_div hγ hγ2
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  set η₀ : ℝ := (Q γ - γ) / 4 with hη₀
  have hη : 0 < η₀ ∧ Q γ - 2 * η₀ > γ := ⟨by rw [hη₀]; linarith, by rw [hη₀]; linarith⟩
  have hbox := reflectedShift_nearQ_of_reflected_shift_and_gluing P X M hγ hγ2 hμ hX hM hη (hShiftGluing η₀ hη) hhR hRm hBR hRv
  -- a start point where `R` is analytic
  set x₁ : ℝ := Q γ + γ / 2 with hx₁
  obtain ⟨u, hu, hRu⟩ : ∃ u : ℝ, u ∈ Ioo (-(γ / 4)) (γ / 4) ∧
      AnalyticAt ℂ R ((x₁ + u : ℝ) : ℂ) := by
    have hmer  := hRm _ (ofReal_mem_horizontalStrip hhR x₁)
    have hev := eventually_analyticAt_affine hmer (a := 1) one_ne_zero
    have hI : Ioo (-(γ / 4)) (γ / 4) ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) (by linarith)
    obtain ⟨u, hu1, hu2⟩ := (hev.and (nhdsWithin_le_nhds hI)).exists
    exact ⟨u, hu2, by simpa using hu1⟩
  set x₀ : ℝ := x₁ + u with hx₀
  set b₀ : ℝ := Q γ - η₀ / 2 with hb₀
  have hx₀1 : Q γ < x₀ := by rw [hx₀, hx₁]; linarith [hu.1]
  have hx₀2 : x₀ < Q γ + γ := by rw [hx₀, hx₁]; linarith [hu.2]
  have hb₀1 : Q γ - η₀ < b₀ := by rw [hb₀]; linarith
  have hb₀2 : b₀ < Q γ := by rw [hb₀]; linarith
  have hq₀₁ : ExtendedSeiberg3 γ (2 * Q γ - x₀) b₀ b₀ :=
    extendedSeiberg3_of_lt hγ (by linarith) hb₀2 hb₀2 (by linarith) (by linarith) (by linarith)
      (by linarith)
  have hq₀₂ : ExtendedSeiberg3 γ (x₀ - γ) b₀ b₀ :=
    extendedSeiberg3_of_lt hγ (by linarith) hb₀2 hb₀2 (by linarith) (by linarith) (by linarith)
      (by linarith)
  have he (y : ℝ) : -1 * y + 2 * Q γ = 2 * Q γ - y := by ring
  have key := affineLeftShift_of_box P M hγ hμ hExt (-1) (2 * Q γ) hhR hRm
    (fun y b' c' hy₁ hy₂ hb₁ hb₂ hc₁ hc₂ hRy => by
      simpa only [he] using hbox y b' c' hy₁ hy₂ hb₁ hb₂ hc₁ hc₂ hRy)
    ⟨hx₀1, hx₀2⟩ ⟨hb₀1, hb₀2⟩ ⟨hb₀1, hb₀2⟩ hRu (by simpa only [he] using hq₀₁) hq₀₂
    (by simpa only [he] using h₁) h₂ hRx (by simpa only [he] using hs₁) hs₂ hA
  simpa only [he] using key

end

end DOZZ.Proofs

end
