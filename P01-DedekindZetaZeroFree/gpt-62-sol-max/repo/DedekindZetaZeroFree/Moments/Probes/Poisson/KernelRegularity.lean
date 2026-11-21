module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.SubpowerBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.MaskedIdentification
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.AnalyticContinuation

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawKernelRegularity31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open DedekindZetaZeroFree.Quantitative.EulerDomain
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem plus_differentiableAt (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (s : ℂ) (hs : 0 < s.re) : DifferentiableAt ℂ ((pkg D).plus u) s :=
  ((pkg D).plus_diff u ((pkg D).nonprincipal u hu).1).differentiableAt
    ((RowHeckeBridge.isOpen_re_gt 0).mem_nhds hs)

theorem minus_differentiableAt (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (s : ℂ) (hs : 0 < s.re) : DifferentiableAt ℂ ((pkg D).minus u) s :=
  ((pkg D).minus_diff u ((pkg D).nonprincipal u hu).2).differentiableAt
    ((RowHeckeBridge.isOpen_re_gt 0).mem_nhds hs)

theorem minus_ne_zero_of_not_isLZero (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (ξ : ℂ) (hξ : 0 < ξ.re)
    (hz : ¬ DetectorDef.IsLZero (primMinus D u) ξ) : (pkg D).minus u ξ ≠ 0 := by
  rw [RawHeckeIdentification31.minus_eq_hecke_mul_mask D u hu ξ hξ]
  refine mul_ne_zero ?_ (RowHeckeBridge.mask_ne_zero _ _ ((pkg D).deletion_finite u) ξ hξ)
  intro h0
  apply hz
  refine ⟨hξ, (RowHeckeBridge.hecke D.recipe.A (primMinus D u)
    ((pkg D).nonprincipal u hu).2).L, RowHeckeBridge.hecke_analyticOn _ _ _,
    fun z hz1 => RowHeckeBridge.hecke_eq_idealLSeries _ _ _ z hz1, h0⟩

theorem rawKernel_differentiableAt (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) (p : ℂ × ℂ × ℂ) (hp : p ∈ OmegaStar) (hz : 1 / 6 < p.2.2.re)
    (hξ : (pkg D).minus u p.1 ≠ 0) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => rawKernel D u p.1 p.2.1 p.2.2 Z) p := by
  have hq : 0 < frequencyNorm D.recipe u := by
    rw [← rawFrequency_norm D u]
    exact_mod_cast D.recipe.A.exteriorNorm_pos _
  have hz1 : 6 * p.2.2 ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  refine RowAnalyticContinuation.kernel_product_differentiableAt D.M D.W1Hat Z _ hZ hq p
    (E := fun p => rawFactor D u p.1 p.2.1 p.2.2)
    (D.M_differentiableOn.differentiableAt ((RowHeckeBridge.isOpen_re_gt 0).mem_nhds hp.2.2.1))
    (RowAnalyticContinuation.W1Hat_differentiable D _)
    ?_
  exact RowAnalyticContinuation.euler_quotient_differentiableAt D p ((pkg D).plus u) ((pkg D).minus u)
      (plus_differentiableAt D u hu _ hp.2.1) (minus_differentiableAt D u hu _ hp.1) hξ hp.2.2.1 hz1
      ((RawEulerProduct31.correctionProduct_differentiableOn D (rawFrequency D u)).differentiableAt
        (OmegaStar_isOpen.mem_nhds hp))


theorem minus_ne_zero_of_not_exceptional (ρ U : ℝ) (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (hU1 : U ≤ frequencyNorm D.recipe u)
    (hU2 : frequencyNorm D.recipe u < 2 * U) (hexc : u ∉ FixedData.rawExceptionalSet D ρ U)
    (ξ : ℂ) (hx : DetectorDef.σ₀ ≤ ξ.re) (hx0 : 0 < ξ.re) (him : |ξ.im| ≤ 4 * U ^ ρ) :
    ¬ (primMinus D u).character.IsPrincipal ∧ (pkg D).minus u ξ ≠ 0 := by
  refine ⟨((pkg D).nonprincipal u hu).2, minus_ne_zero_of_not_isLZero D u hu ξ hx0 ?_⟩
  intro hz
  exact hexc ⟨hu, hU1, hU2, ξ, hz, hx, him⟩

end

end DedekindZetaZeroFree.Quantitative.RawKernelRegularity31
