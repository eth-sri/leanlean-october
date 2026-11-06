/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.KernelInverseExpectation
public import DOZZ.FourPoint.Reflected.ReinsertedInnerSqueeze
public import DOZZ.FourPoint.Reflected.CopiedSourceMoment
public import DOZZ.FourPoint.Reflected.SourceOuterMoments
/-! The actual copied spatial kernel has the integrated radial Williams squeeze. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem reflected_source_copied_kernel_inverse_squeeze
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) Xc (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    γ (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : Measurable N) (hi : IndepFun (originRadialPath Xc) N P)
    (heq : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))))
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    α₁ α₂ α₃ ξ p R (hp : 0 < p)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    z (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hzn : ‖z‖ ≤ 1)
    (hr : 0 < ‖z‖^(1-ξ)) (hz : ‖z‖ < ‖z‖^(1-ξ)) (hr1 : ‖z‖^(1-ξ) ≤ 1)
    (T : ℝ≥0) (hR : 0 ≤ R) (hR1 : R < 1)
    (hT : Real.exp (-(T : ℝ)) < 1) (hsep : Real.exp (-(T : ℝ)) ≤ R*‖z‖) :
    let η := Real.exp (-(T : ℝ))
    let D := (∫⁻ ω : Ω × Ω, (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω.1) z ξ+
      ENNReal.ofReal (‖z‖^(γ^2/2))*(∫⁻ x in reflected_innerRegion η,
        ENNReal.ofReal (‖x‖^(-(γ*α₁)))*
          ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x) ∂N ω.2))^(-p) ∂P.prod P).toReal-
      (∫⁻ ω, gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ^(-p) ∂P).toReal
    let E := (reflected_copied_separatedMoment P Xc N γ α₁ α₂ α₃ z η (‖z‖^(1-ξ)) p).toReal-
      (∫⁻ ω, gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ^(-p) ∂P).toReal
    max 1 ((1+R)^(γ^2/2)*(1-η)⁻¹^|γ*α₂|)*D ≤ E ∧ E ≤ min 1 ((1-R)^(γ^2/2)*(1-η)⁻¹^(-|γ*α₂|))*D := by
  let _ : IsProbabilityMeasure P := hX.1
  let η := Real.exp (-(T : ℝ))
  let U := reflected_innerRegion η
  let A := fun ω => gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ
  let I := fun ω : Ω × Ω => ∫⁻ x in U,
    ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)*
      ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x) ∂N ω.2
  have hA := (reflected_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  have hU : MeasurableSet U := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hU0 : U ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx
    simpa only [mem_compl_iff,mem_singleton_iff] using norm_pos_iff.mp hx.1
  have hAr := originRadialPath_aemeasurable P X Xc hc hcont
  have hbase : (∫⁻ ω : Ω × Ω, A ω.1^(-p) ∂P.prod P) = ∫⁻ ω, A ω^(-p) ∂P := by
    have he := lintegral_map' (by rw [(measurePreserving_fst (μ := P) (ν := P)).map_eq]; exact hA.pow_const (-p))
      (measurable_fst.aemeasurable : AEMeasurable (Prod.fst : Ω × Ω → Ω) (P.prod P))
    rw [(measurePreserving_fst (μ := P) (ν := P)).map_eq] at he
    exact he.symm
  obtain ⟨C,_,hC⟩ := reflected_outerMass_inverse_moment_uniform P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ p hp.le
  have hs := reflected_kernel_inverse_expectation_squeeze (P.prod P) (fun ω : Ω × Ω => A ω.1) (fun ω : Ω × Ω => ENNReal.ofReal (‖z‖^(γ^2/2))*(∫⁻ x in U, ENNReal.ofReal (‖x‖^(-(γ*α₁)))* ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x) ∂N ω.2)) I
    (hA.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving) ((measurable_const : Measurable (fun _ => ENNReal.ofReal (‖z‖^(γ^2/2)))).aemeasurable.mul (reflected_copied_region_mass_aemeasurable P (originRadialPath Xc) N hAr hN hfin γ U hU hU0 _ (by fun_prop))) (reflected_copied_region_mass_aemeasurable P (originRadialPath Xc) N hAr hN hfin γ U hU hU0 _ (reflected_gammaHalfKernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal)
    p ((1-R)^(γ^2/2)*(1-η)⁻¹^(-|γ*α₂|)) ((1+R)^(γ^2/2)*(1-η)⁻¹^|γ*α₂|) hp (mul_pos (Real.rpow_pos_of_pos (sub_pos.mpr hR1) _) (Real.rpow_pos_of_pos (inv_pos.mpr (sub_pos.mpr hT)) _)) (mul_pos (Real.rpow_pos_of_pos (by linarith only [hR] : 0 < 1+R) _) (Real.rpow_pos_of_pos (inv_pos.mpr (sub_pos.mpr hT)) _)) ((measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae ((reflected_source_outerMass_positive_finite_ae P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ ξ hα₁ hα₂ hα₃ z hz0 hz1 hzn hr1).mono fun _ hω => ⟨hω.1,hω.2.ne⟩ : ∀ᵐ ω ∂P, 0 < A ω ∧ A ω ≠ ⊤)) (Filter.Eventually.of_forall fun ω => reflected_reinserted_inner_kernel_mass_squeeze γ α₁ α₂ α₃ R z (originRadialPath Xc ω.1) (N ω.2) T hR hR1 (norm_pos_iff.mpr hz0) hT hsep) (by rw [hbase]; exact lt_of_le_of_lt (hC z ξ hzn hr1) ENNReal.ofReal_lt_top)
  rw [hbase] at hs
  have he := reflected_copied_separatedMoment_source P X hX Xc hc hcont γ hγ hγ₂ M hM
    N hN hi heq hfin α₁ α₂ α₃ ξ η p z hr hz
  change reflected_copied_separatedMoment P Xc N γ α₁ α₂ α₃ z η (‖z‖^(1-ξ)) p =
    ∫⁻ ω : Ω × Ω, (I ω+A ω.1)^(-p) ∂P.prod P at he
  simp_rw [add_comm] at he
  dsimp only
  rw [he]
  exact hs.2.2

end DOZZ.Proofs
