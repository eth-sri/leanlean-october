/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.MeasureTranslationFinite
public import DOZZ.Statements.Brownian.IsLateralGMCOf
public import DOZZ.Statements.Brownian.BrownianPath

/-!
# Random translation of locally finite lateral measures

The measurable action is first extended to all measures by a countable disjoint exhaustion. It
agrees with ordinary pushforward on locally finite measures, which is the almost-sure domain of
the lateral GMC carrier.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

private theorem measurable_fixedLocallyFiniteTranslation (t : ℝ) :
    Measurable (fun μ : Measure ℝ => locallyFiniteTranslation (t, μ)) := measurable_locallyFiniteTranslation.comp (measurable_const.prodMk measurable_id)

/-- Deterministic stationarity of the original lateral measure transfers to the measurable
extension of translation on its locally finite carrier. -/
private theorem locallyFiniteTranslation_stationary
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ)
    (hZ : IsLateralGMCOf P γ Z) (hZA : AEMeasurable Z P) (t : ℝ) :
    (P.map Z).map (fun μ => locallyFiniteTranslation (t, μ)) = P.map Z := by
  have hloc : (fun ω => locallyFiniteTranslation (t, Z ω)) =ᵐ[P]
      fun ω => (Z ω).map (fun s => s + t) := by
    filter_upwards [hZ.2.2.2.2.1] with ω hfinite
    apply locallyFiniteTranslation_eq_map t (Z ω)
    tauto
  calc
    (P.map Z).map (fun μ => locallyFiniteTranslation _) =
        P.map (fun ω => locallyFiniteTranslation _) :=
      AEMeasurable.map_map_of_aemeasurable
        (measurable_fixedLocallyFiniteTranslation t).aemeasurable hZA
    _ = P.map (fun ω => (Z ω).map (fun s => s + t)) := Measure.map_congr hloc
    _ = P.map Z := (hZ.2.2.2.2.2.1 t)

/-- A random measurable translation of one coordinate preserves a product law when every fixed
translation preserves the second marginal. -/
private theorem product_randomTranslation_invariant
    {A : Type*} [MeasurableSpace A]
    (μA : Measure A) (μB : Measure (Measure ℝ))
    [IsProbabilityMeasure μA] [IsProbabilityMeasure μB]
    (hstat : ∀ t : ℝ, μB.map (fun μ => locallyFiniteTranslation (t, μ)) = μB)
    (T : A → ℝ) (hT : Measurable T) :
    (μA.prod μB).map (fun z : A × Measure ℝ =>
      (z.1, locallyFiniteTranslation (T z.1, z.2))) =
      μA.prod μB := by
  let G : A × Measure ℝ → A × Measure ℝ :=
    fun z => (z.1, locallyFiniteTranslation (T z.1, z.2))
  have hinput : Measurable (fun z : A × Measure ℝ => (T z.1, z.2)) :=
    by fun_prop
  have hG : Measurable G := measurable_fst.prodMk
    (measurable_locallyFiniteTranslation.comp hinput)
  symm
  apply Measure.prod_eq
  intro S U hS hU
  rw [Measure.map_apply hG (hS.prod hU)]
  rw [Measure.prod_apply (hG (hS.prod hU))]
  have hsection (a : A) :
      μB ((Prod.mk a) ⁻¹' G ⁻¹' (S ×ˢ U)) =
        (S.indicator (fun _ => μB U)) a := by
    by_cases ha : a ∈ S
    · have hshift :=
        measurable_fixedLocallyFiniteTranslation (T a)
      have hsection_eq : (Prod.mk a) ⁻¹' G ⁻¹' (S ×ˢ U) =
          (fun b => locallyFiniteTranslation (T a, b)) ⁻¹' U := by
        aesop
      rw [hsection_eq, ← Measure.map_apply hshift hU, hstat (T a), Set.indicator_of_mem ha]
    · have hsection_eq : (Prod.mk a) ⁻¹' G ⁻¹' (S ×ˢ U) = ∅ := by
        aesop
      simp_all
  calc
    (∫⁻ a, μB _ ∂μA) =
        ∫⁻ a, (S.indicator (fun _ => μB U)) a ∂μA := by
          simp_all
    _ = μB U * μA S := by simp_all
    _ = μA S * μB U := mul_comm ..
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
section
variable (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) (D : Ω → BrownianPath) (hD : AEMeasurable D P)
include hZ hD

/-- The random translated lateral measure is almost-everywhere measurable. -/
theorem lateralGMC_randomTranslation_aemeasurable
    (T : BrownianPath → ℝ) (hT : Measurable T) :
    AEMeasurable (fun ω => (Z ω).map (fun s => s + T (D ω))) P := by
  have hparam :=
    AEMeasurable.prodMk (hT.comp_aemeasurable hD) hZ.2.2.2.1
  have hsurrogate :=
    measurable_locallyFiniteTranslation.comp_aemeasurable hparam
  have htranslate : (fun ω => (Z ω).map (fun s => s + T (D ω))) =ᵐ[P]
      fun ω => locallyFiniteTranslation (T (D ω), Z ω) := by
    filter_upwards [hZ.2.2.2.2.1] with ω hloc
    exact (locallyFiniteTranslation_eq_map _ (Z ω) (by
      tauto)).symm
  exact (aemeasurable_congr htranslate).2 hsurrogate

/-- Proof of the complete random-translation statement `DOZZ.lateralGMC_random_translation`:
independence replaces the input law by a product, while deterministic stationarity preserves the
second marginal in every section. -/
theorem lateralGMC_random_translation
    (hInd : IndepFun D Z P) (T : BrownianPath → ℝ) (hT : Measurable T) :
    AEMeasurable (fun ω => (Z ω).map (fun s => s + T (D ω))) P ∧
      P.map (fun ω => (Z ω).map (fun s => s + T (D ω))) = P.map Z ∧
      IndepFun D (fun ω => (Z ω).map (fun s => s + T (D ω))) P := by
  let Y : Ω → Measure ℝ := fun ω => (Z ω).map (fun s => s + T (D ω))
  let μD := P.map D
  let μZ := P.map Z
  have hZA := hZ.2.2.2.1
  have hY := lateralGMC_randomTranslation_aemeasurable P γ Z hZ D hD T hT
  have : IsProbabilityMeasure P := hZ.2.2.1
  have : IsProbabilityMeasure μD := (Measure.isProbabilityMeasure_map_iff hD).2 inferInstance
  have : IsProbabilityMeasure μZ := (Measure.isProbabilityMeasure_map_iff hZA).2 inferInstance
  have hDZ : P.map (fun ω => (D ω, Z ω)) = μD.prod μZ :=
    (indepFun_iff_map_prod_eq_prod_map_map hD hZA).1 hInd
  have hstat : ∀ t : ℝ, μZ.map (fun μ => locallyFiniteTranslation (t, μ)) = μZ := by
    intro t
    exact locallyFiniteTranslation_stationary P γ Z hZ hZA t
  let G : BrownianPath × Measure ℝ → BrownianPath × Measure ℝ := fun z =>
    (z.1, locallyFiniteTranslation (T z.1, z.2))
  have hTprod : Measurable (fun z : BrownianPath × Measure ℝ => (T z.1, z.2)) :=
    by fun_prop
  have hG := measurable_fst.prodMk
    (measurable_locallyFiniteTranslation.comp hTprod)
  have htranslate : Y =ᵐ[P] fun ω => locallyFiniteTranslation (T (D ω), Z ω) := by
    filter_upwards [hZ.2.2.2.2.1] with ω hloc
    exact (locallyFiniteTranslation_eq_map _ (Z ω) (by
      intro n
      exact hloc (-n) n)).symm
  have hpairY := hD.prodMk hY
  have hpairLaw : P.map (fun ω => (D ω, Y ω)) = μD.prod μZ := by
    calc
      P.map (fun ω => (D ω, Y ω)) = P.map (fun ω => G _) :=
        Measure.map_congr (Filter.EventuallyEq.prodMk Filter.EventuallyEq.rfl htranslate)
      _ = (P.map (fun ω => (D ω, Z ω))).map G := by
        symm
        exact AEMeasurable.map_map_of_aemeasurable hG.aemeasurable (hD.prodMk hZA)
      _ = (μD.prod μZ).map G := congrArg (fun m => m.map G) hDZ
      _ = μD.prod μZ := (product_randomTranslation_invariant μD μZ hstat T hT)
  have hYlaw : P.map Y = μZ := by
    calc
      P.map Y = (P.map (fun ω => (D ω, Y ω))).map Prod.snd := by
        symm
        exact AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hpairY
      _ = (μD.prod μZ).map Prod.snd := congrArg (fun m => m.map Prod.snd) hpairLaw
      _ = μZ := by simp
  refine ⟨hY, hYlaw, ?_⟩
  apply (indepFun_iff_map_prod_eq_prod_map_map hD hY).2
  rwa [hYlaw]

end

end


end DOZZ.Proofs

end
