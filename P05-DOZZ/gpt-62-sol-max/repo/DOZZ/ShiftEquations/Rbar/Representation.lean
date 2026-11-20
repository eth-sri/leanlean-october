/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import DOZZ.FourPoint.Crossing.GammaHalfCrossing
import DOZZ.Correlations.Residue.Assembly
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
public import DOZZ.ShiftEquations.Rbar.Residue
public import DOZZ.ShiftEquations.Rbar.Continuation
public import DOZZ.Statements.Correlations.BridgeMultiplicity
public import DOZZ.Statements.Brownian.ReflectionBarR
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsGMCOf
import DOZZ.Correlations.Symmetry.ReflectionMomentSwap
import DOZZ.Brownian.Reflection.WitnessIndependence
import DOZZ.ShiftEquations.Reflection.Witness
public import DOZZ.Correlations.Analytic.UnitVolumeExtension

/-!
# The `R̄` representation from the γ/2 crossing, the residue bridge and the holomorphic extension

Fix `γ/2 < a < Q`. For `γ/2 < ε < min (2/γ) (2a - γ/2)` the continued diagonal crossing gives
`(ε - γ/2) C̄(a - γ/2, ε, a) = [(ε - γ/2) T(a, ε, a)] C̄(a, ε + γ/2, a)`. As `ε ↓ γ/2` the left side
tends to `2 p R̄(a)` by the residue bridge (with `α₂ = a - γ/2 ≠ α₃ = a`, after swapping the first
two charges), and the right side to `2 p · coefficient(a) · C̄(a, γ, a)` by the residue of the
multiplier and the continuity of the holomorphic extension of `C̄` at `(a, γ, a)`. Since `p > 0`,
`R̄(a) = coefficient(a) · C̄(a, γ, a)` ([KRV, §10.1], erratum K29,
see docs/ERRATA-AND-DEVIATIONS.md). The holomorphic representation is `f(z) = C̄ₕ(z, γ, z)` on
`{γ/2 < Re z < Q} ∩ {(z, γ, z) ∈ V}`, where the coefficient is holomorphic.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace DOZZ.Proofs

/-- The charges `(a, γ, a)` lie in the extended domain for `γ/2 < a < Q`. -/
theorem extendedSeiberg3_diag_gamma {γ a : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (ha₁ : γ / 2 < a)
    (ha₂ : a < Q γ) : ExtendedSeiberg3 γ a γ a := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hQ2 : 2 * Q γ = 4 / γ + γ := by
    rw [hQ]
    ring
  have hγh := half_gamma_lt_two_div hγ hγ2
  refine extendedSeiberg3_of_lt hγ ha₂ (by rw [hQ]; linarith) ha₂ ?_ ?_ ?_ ?_ <;> linarith

/-- The charge triple `(z, γ, z)` of the `R̄` representation. -/
noncomputable def reflectionTriple (γ : ℝ) (z : ℂ) : Fin 3 → ℂ := ![z, (γ : ℂ), z]

theorem differentiable_reflectionTriple (γ : ℝ) : Differentiable ℂ (reflectionTriple γ) := by
  rw [differentiable_pi]
  intro i
  fin_cases i
  · exact differentiable_id
  · exact differentiable_const _
  · exact differentiable_id

theorem reflectionTriple_ofReal (γ t : ℝ) :
    reflectionTriple γ (t : ℂ) = complexifyNCharges ![t, γ, t] := by
  funext i
  fin_cases i <;> simp [reflectionTriple, complexifyNCharges]

/-- **`R̄ = coefficient · C̄(a, γ, a)`** from the diagonal crossing, the holomorphic extension of
`C̄`, and a residue-bridge limit with value `R`. -/
theorem eq_rbarCoefficientReal_mul_of_bridge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (M : Ω → Measure ℂ) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    {V₃ : Set (Fin 3 → ℂ)} {f₃ : (Fin 3 → ℂ) → ℂ}
    (hExt : IsUnitVolumeExtension P M γ V₃ f₃)
    {a : ℝ} (ha₁ : γ / 2 < a) (ha₂ : a < Q γ) {R : ℝ}
    (hLim : Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
        (a - (a - γ / 2) + ε) (a - γ / 2) a) (𝓝[>] 0)
      (𝓝 (bridgeMultiplicity (a - γ / 2) a * reflectionExponent γ a * R))) :
    R = rbarCoefficientReal γ a * unitVolumeStructureConstant P M γ a γ a := by
  have hγh := half_gamma_lt_two_div hγ hγ2
  have hlt : γ / 2 < min (2 / γ) (2 * a - γ / 2) := lt_min hγh (by linarith)
  have hmult : bridgeMultiplicity (a - γ / 2) a = 2 := by
    have hne : a - γ / 2 ≠ a := fun h => by linarith
    simp only [bridgeMultiplicity, hne, ↓reduceIte]
  -- the left side: the residue bridge, shifted and with the first two charges swapped
  have hshift : Tendsto (fun ε : ℝ => ε - γ / 2) (𝓝[>] (γ / 2)) (𝓝[>] 0) := by
    have h := (by fun_prop : Continuous fun ε : ℝ => ε - γ / 2).tendsto (γ / 2)
    rw [sub_self] at h
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (h.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun _ hε => sub_pos.mpr hε)
  have hLeft : Tendsto (fun ε : ℝ => (ε - γ / 2) * unitVolumeStructureConstant P M γ
      (a - γ / 2) ε a) (𝓝[>] (γ / 2))
      (𝓝 (bridgeMultiplicity (a - γ / 2) a * reflectionExponent γ a * R)) := by
    refine (hLim.comp hshift).congr fun ε => ?_
    simp [Function.comp_apply, show a - (a - γ / 2) + (ε - γ / 2) = ε by ring, unitVolumeStructureConstant_swap12 P X M γ ε (a - γ / 2) a hγ hγ2 hX hM]
  -- on the right: the continued crossing
  have hev : ∀ᶠ ε in 𝓝[>] (γ / 2),
      (ε - γ / 2) * unitVolumeStructureConstant P M γ (a - γ / 2) ε a =
        (ε - γ / 2) * crossingMultiplierReal γ ε a *
          unitVolumeStructureConstant P M γ a (ε + γ / 2) a := by
    filter_upwards [Ioo_mem_nhdsGT hlt] with ε hε
    have hε₂ : ε < 2 / γ := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hεa : ε < 2 * a - γ / 2 := lt_of_lt_of_le hε.2 (min_le_right _ _)
    rw [unitVolume_crossing_diag_continued P M hγ hε.1 hε₂
      (fun a' h1 h2 => gammaHalf_unit_crossing P X M γ hγ hγ2 hX hM
        1 a' ε a' one_pos hε.1 hε₂ h1 h1 h2) hExt (by linarith) ha₂]
    ring
  -- continuity of `C̄(a, ε + γ/2, a)` at `ε = γ/2`, through the holomorphic extension
  have hES0 := extendedSeiberg3_diag_gamma hγ hγ2 ha₁ ha₂
  have hcurve : Continuous fun ε : ℝ => complexifyNCharges ![a, ε + γ / 2, a] := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · show Continuous fun _ : ℝ => ((a : ℝ) : ℂ)
      exact continuous_const
    · show Continuous fun ε : ℝ => ((ε + γ / 2 : ℝ) : ℂ)
      fun_prop
    · show Continuous fun _ : ℝ => ((a : ℝ) : ℂ)
      exact continuous_const
  have hcurve0 : complexifyNCharges ![a, γ / 2 + γ / 2, a] = complexifyNCharges ![a, γ, a] := by
    rw [add_halves]
  have hf₃c : Tendsto (fun ε : ℝ => f₃ (complexifyNCharges ![a, ε + γ / 2, a])) (𝓝 (γ / 2))
      (𝓝 (f₃ (complexifyNCharges ![a, γ, a]))) :=
    (hExt.holomorphic.differentiableAt (hExt.isOpen.mem_nhds (hExt.mem ![a, γ, a] hES0))).continuousAt.tendsto.comp
      (hcurve.tendsto' (γ / 2) _ hcurve0)
  have hval : (f₃ (complexifyNCharges ![a, γ, a])).re = unitVolumeStructureConstant P M γ a γ a :=
    (congrArg Complex.re (hExt.value ![a, γ, a] hES0)).trans (Complex.ofReal_re _)
  have hRight0 : Tendsto (fun ε : ℝ => unitVolumeStructureConstant P M γ a (ε + γ / 2) a)
      (𝓝[>] (γ / 2)) (𝓝 (unitVolumeStructureConstant P M γ a γ a)) := by
    rw [← hval]
    refine (((Complex.continuous_re.tendsto _).comp hf₃c).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hlt] with ε hε
    have hε₂ : ε < 2 / γ := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hεa : ε < 2 * a - γ / 2 := lt_of_lt_of_le hε.2 (min_le_right _ _)
    exact (congrArg Complex.re (hExt.value ![a, ε + γ / 2, a]
      (extendedSeiberg3_raise (a := a) hγ hε.1 hε₂ (by linarith) ha₂))).trans
        (Complex.ofReal_re _)
  have hRight := (tendsto_sub_mul_crossingMultiplierReal hγ hγ2 ha₁ ha₂).mul hRight0
  have huniq := tendsto_nhds_unique (hLeft.congr' hev) hRight
  rw [hmult] at huniq
  have hp : 0 < reflectionExponent γ a := by
    unfold reflectionExponent
    exact div_pos (by linarith) hγ
  have h2p : (2 : ℝ) * reflectionExponent γ a ≠ 0 := by positivity
  apply mul_left_cancel₀ h2p
  rw [huniq]
  ring

/-- The holomorphic representation of `R̄` on a subset of the reflection interval. -/
theorem reflectionBarR_holomorphic_representation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (I : Set ℝ) (hI : ∀ α ∈ I, γ / 2 < α ∧ α < Q γ) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α ∈ I,
            IsReflectionData P γ α (B α) Z) ∧
            ∃ V : Set ℂ, IsOpen V ∧
              (∀ α ∈ I, (α : ℂ) ∈ V) ∧
              ∃ f : ℂ → ℂ, DifferentiableOn ℂ f V ∧
                (∀ α ∈ I,
                  f (α : ℂ) =
                    (unitVolumeStructureConstant P M γ α γ α : ℂ)) ∧
                DifferentiableOn ℂ
                  (fun z => rbarCoefficient γ z * f z) V ∧
                (∀ α ∈ I,
                  rbarCoefficient γ (α : ℂ) * f (α : ℂ) =
                    (reflectionBarR P γ α (B α) Z : ℂ)) := by
  obtain ⟨V₃, f₃, hExt⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh := half_gamma_lt_two_div hγ hγ2
  -- the witnesses: one bridge datum, extended to a family over all charges below `Q`
  set a₀ : ℝ := (γ / 2 + Q γ) / 2 with ha₀
  obtain ⟨B₀, Z, hSLP, hRD₀, -⟩ :=
    unitVolumeStructureConstant_threeToTwo_residue_bridge P X M γ (a₀ - γ / 2) a₀ hγ hγ2
    ⟨by rw [ha₀, hQ]; linarith, by linarith, by rw [ha₀, hQ]; linarith,
      by rw [ha₀, hQ]; linarith⟩ hX hM
  obtain ⟨B, hB⟩ := exists_reflectionData_family_of_isReflectionData P X γ a₀ M Z (B₀ a₀)
    hSLP hRD₀
  -- the representation
  have hf : ∀ α : ℝ, γ / 2 < α → α < Q γ →
      f₃ (reflectionTriple γ (α : ℂ)) = (unitVolumeStructureConstant P M γ α γ α : ℂ) :=
    fun α h1 h2 => by
      rw [reflectionTriple_ofReal]
      exact hExt.value ![α, γ, α] (extendedSeiberg3_diag_gamma hγ hγ2 h1 h2)
  have hR : ∀ α : ℝ, γ / 2 < α → α < Q γ →
      reflectionBarR P γ α (B α) Z =
        rbarCoefficientReal γ α * unitVolumeStructureConstant P M γ α γ α := fun α h1 h2 => by
    obtain ⟨B', Z', -, hRD', hLim⟩ :=
      unitVolumeStructureConstant_threeToTwo_residue_bridge P X M γ (α - γ / 2) α hγ hγ2
        ⟨by linarith, by linarith, h1, h2⟩ hX hM
    rw [reflectionBarR_eq_of_isReflectionData P P γ α (B α) Z (B' α) Z' (hB α h2) hRD']
    exact eq_rbarCoefficientReal_mul_of_bridge P X M hγ hγ2 hX hM hExt h1 h2 hLim
  refine ⟨B, Z, hSLP, fun α hα => hB α (hI α hα).2,
    reflectionStrip γ ∩ reflectionTriple γ ⁻¹' V₃,
    (isOpen_reflectionStrip γ).inter (hExt.isOpen.preimage (differentiable_reflectionTriple γ).continuous),
    fun α hα => ⟨⟨by rw [Complex.ofReal_re]; exact (hI α hα).1,
      by rw [Complex.ofReal_re]; exact (hI α hα).2⟩, by
        change reflectionTriple γ (α : ℂ) ∈ V₃
        rw [reflectionTriple_ofReal]
        exact hExt.mem ![α, γ, α] (extendedSeiberg3_diag_gamma hγ hγ2 (hI α hα).1 (hI α hα).2)⟩,
    fun z => f₃ (reflectionTriple γ z),
    hExt.holomorphic.comp (differentiable_reflectionTriple γ).differentiableOn fun _ hz => hz.2,
    fun α hα => hf α (hI α hα).1 (hI α hα).2,
    ((differentiableOn_rbarCoefficient hγ).mono inter_subset_left).mul
      (hExt.holomorphic.comp (differentiable_reflectionTriple γ).differentiableOn fun _ hz => hz.2),
    fun α hα => ?_⟩
  simp [hf α (hI α hα).1 (hI α hα).2, hR α (hI α hα).1 (hI α hα).2, rbarCoefficient_ofReal]

end DOZZ.Proofs

end
