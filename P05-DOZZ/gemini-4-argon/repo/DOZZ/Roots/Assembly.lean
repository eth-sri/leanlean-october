/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Roots.CubeContinuation
public import DOZZ.Roots.FormulaGammaContinuity
public import DOZZ.Roots.GammaDensity
public import DOZZ.Roots.ParameterFamilies
public import DOZZ.ShiftEquations.Residual.Assembly

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ.Proofs

theorem roots_small_cube γ (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ η : ℝ, 0 < η ∧ η ≤ γ / 4 ∧ Q γ - 2 * η > γ ∧ 3 * η < Q γ := by
  have hQ : γ < Q γ := by
    unfold Q; linarith only [((lt_div_iff₀ hγ).mpr (by nlinarith only [hγ, hγ2]) : γ / 2 < 2 / γ)]
  let η := min ((Q γ - γ) / 8) (γ / 4)
  have hη1 : η ≤ (Q γ - γ) / 8 := min_le_left _ _
  exact ⟨η, lt_min (by linarith only [hQ]) (by positivity), min_le_right _ _,
    by linarith only [hQ, hη1], by linarith only [hQ, hγ, hη1]⟩

theorem dozz_main γ μ (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (α₁ α₂ α₃ : ℝ) (hα : ExtendedSeiberg3 γ α₁ α₂ α₃)
    (hs : ∀ n : ℕ, sExp γ α₁ α₂ α₃ ≠ -(n : ℝ))
    U (hU : IsUpsilon γ U)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (M : Ω → Measure ℂ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    (structureConstant P M γ μ α₁ α₂ α₃ : ℂ) = dozzFormula γ μ U α₁ α₂ α₃ := by
  obtain ⟨N, hNγ, hN⟩ := roots_GMC_family_through P X hX γ M hM
  obtain ⟨V, hVγ, hV⟩ := roots_Upsilon_family_through γ U hU
  have hC : ContinuousAt (fun g => (structureConstant P (N g) g μ α₁ α₂ α₃ : ℂ)) γ :=
    Complex.continuous_ofReal.continuousAt.comp
      (roots_structureConstant_gamma_continuousAt P X N hX hN γ μ α₁ α₂ α₃ hγ hγ2 hμ hα hs)
  have hD := roots_dozzFormula_gamma_continuousAt V hV γ μ α₁ α₂ α₃ hγ hγ2 hμ hα hs
  have heq : ∃ᶠ g : ℝ in nhds γ,
      (structureConstant P (N g) g μ α₁ α₂ α₃ : ℂ) = dozzFormula g μ (V g) α₁ α₂ α₃ := by
    apply ((roots_frequently_irrational_sq γ hγ).and_eventually ((roots_extended_parameters_nhds hγ hγ2 hα).and (roots_poleFree_gamma_nhds γ α₁ α₂ α₃ hγ.ne' hs))).mono
    rintro g ⟨hgirr, ⟨hg, hg2, hgα⟩, hgs⟩
    obtain ⟨η, hη, _, hηshift, hηQ⟩ := roots_small_cube g hg hg2
    exact roots_structureConstant_of_unitVolume_value P (N g) g μ α₁ α₂ α₃ hμ hgs _
      (roots_unitVolume_of_cube P X (N g) g μ η hg hg2 hμ hη hηQ (V g) (hV g ⟨hg, hg2⟩) hX
        (hN g hg hg2) (unitVolume_residual_factor_eq_one P X (N g) g μ η (V g) hg hg2 hgirr hμ
          ⟨hη, hηshift, hηQ⟩ hX (hN g hg hg2) (hV g ⟨hg, hg2⟩)) α₁ α₂ α₃ hgα hgs)
  simpa only [hNγ, hVγ] using tendsto_nhds_unique_of_frequently_eq hC.tendsto hD.tendsto heq

theorem dozz_unitVolume (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (α₁ α₂ α₃ : ℝ) (hα : ExtendedSeiberg3 γ α₁ α₂ α₃)
    U (hU : IsUpsilon γ U)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (M : Ω → Measure ℂ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    Tendsto
      (fun a : ℝ × ℝ × ℝ =>
        ((μ : ℂ) ^ (sExp γ a.1 a.2.1 a.2.2 : ℂ) / Complex.Gamma (sExp γ a.1 a.2.1 a.2.2)) *
          dozzFormula γ μ U a.1 a.2.1 a.2.2)
      (𝓝[{a | ExtendedSeiberg3 γ a.1 a.2.1 a.2.2 ∧
              ∀ n : ℕ, sExp γ a.1 a.2.1 a.2.2 ≠ -(n : ℝ)}] (α₁, α₂, α₃))
      (𝓝 (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ)) := by
  obtain ⟨V, hVo, hVα, f, hfd, hfv⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  let A : ℝ × ℝ × ℝ → Fin 3 → ℂ := fun a => complexifyNCharges ![a.1, a.2.1, a.2.2]
  have hA : Continuous A := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Complex.continuous_ofReal.comp continuous_fst
    · exact Complex.continuous_ofReal.comp (continuous_fst.comp continuous_snd)
    · exact Complex.continuous_ofReal.comp (continuous_snd.comp continuous_snd)
  have hc : ContinuousAt (fun a => f (A a)) (α₁, α₂, α₃) :=
    (hfd.continuousOn.continuousAt (hVo.mem_nhds (hVα ![α₁, α₂, α₃] hα))).comp (f := A) hA.continuousAt
  have hl : Tendsto (fun a => f (A a))
      (𝓝[{a : ℝ × ℝ × ℝ | ExtendedSeiberg3 γ a.1 a.2.1 a.2.2 ∧
        ∀ n : ℕ, sExp γ a.1 a.2.1 a.2.2 ≠ -(n : ℝ)}] (α₁, α₂, α₃))
      (𝓝 (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ)) := by
    have he : f (A (α₁, α₂, α₃)) = (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ) :=
      hfv ![α₁, α₂, α₃] hα
    rw [← he]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [show f (A a) = (unitVolumeStructureConstant P M γ a.1 a.2.1 a.2.2 : ℂ) from
    hfv ![a.1, a.2.1, a.2.2] ha.1,
    ← roots_unitVolume_normalization P M γ μ a.1 a.2.1 a.2.2 hμ ha.2,
    dozz_main γ μ hγ hγ2 hμ a.1 a.2.1 a.2.2 ha.1 ha.2 U hU P X M hX hM]

end DOZZ.Proofs
