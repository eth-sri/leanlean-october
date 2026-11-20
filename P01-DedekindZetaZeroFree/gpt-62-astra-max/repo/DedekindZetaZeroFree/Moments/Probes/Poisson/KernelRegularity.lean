module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.FrequencyNormalConvergence
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
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

section

variable (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)

include hu in
theorem plus_differentiableAt
    (s : ℂ) (hs : 0 < s.re) : DifferentiableAt ℂ ((pkg D).plus u) s :=
  ((pkg D).plus_diff u ((pkg D).nonprincipal u hu).1).differentiableAt
    ((RowHeckeBridge.isOpen_re_gt 0).mem_nhds hs)

include hu in
theorem minus_differentiableAt
    (s : ℂ) (hs : 0 < s.re) : DifferentiableAt ℂ ((pkg D).minus u) s :=
  ((pkg D).minus_diff u ((pkg D).nonprincipal u hu).2).differentiableAt
    ((RowHeckeBridge.isOpen_re_gt 0).mem_nhds hs)

include hu in
theorem minus_ne_zero_of_not_isLZero (ξ : ℂ) (hξ : 0 < ξ.re)
    (hz : ¬ DetectorDef.IsLZero (primMinus D u) ξ) : (pkg D).minus u ξ ≠ 0 := by
  rw [RawHeckeIdentification31.minus_eq_hecke_mul_mask D u hu ξ hξ]
  refine mul_ne_zero ?_ (RowHeckeBridge.mask_ne_zero _ _ ((pkg D).deletion_finite u) ξ hξ)
  intro h0
  apply hz
  refine ⟨hξ, (RowHeckeBridge.hecke D.recipe.A (primMinus D u)
    ((pkg D).nonprincipal u hu).2).L, RowHeckeBridge.hecke_analyticOn _ _ _,
    fun z hz1 => RowHeckeBridge.hecke_eq_idealLSeries _ _ _ z hz1, h0⟩

include hu in
theorem rawKernel_differentiableAt
    (Z : ℝ) (hZ : 0 < Z) (p : ℂ × ℂ × ℂ) (hp : p ∈ OmegaStar) (hz : 1 / 6 < p.2.2.re)
    (hξ : (pkg D).minus u p.1 ≠ 0) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => rawKernel D u p.1 p.2.1 p.2.2 Z) p := by
  obtain ⟨ξ, w, z⟩ := p
  have hcomp : ∀ (g : ℂ → ℂ) (f : ℂ × ℂ × ℂ → ℂ), DifferentiableAt ℂ f (ξ, w, z) →
      DifferentiableAt ℂ g (f (ξ, w, z)) →
      DifferentiableAt ℂ (fun p => g (f p)) (ξ, w, z) :=
    fun g f hf hg => hg.comp (ξ, w, z) hf
  have hq : 0 < frequencyNorm D.recipe u := by
    rw [← rawFrequency_norm D u]
    exact_mod_cast D.recipe.A.exteriorNorm_pos _
  have hz1 : 6 * z ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    have h6 : (6 * z).re = 6 * z.re := by simp
    rw [h6] at this
    simp at this
    linarith
  have hzeta : DifferentiableAt ℂ D.recipe.L (6 * z) := by
    exact (RightHeckeBounds.zetaSCont_analyticOnNhd D (6 * z) (⟨by show 0 < (6 * z).re; simp; linarith, hz1⟩)).differentiableAt
  unfold rawKernel
  refine ((((((DifferentiableAt.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).mul (DifferentiableAt.cexp (by fun_prop))).mul (hcomp D.M (fun p => p.2.2) (by fun_prop) (D.M_differentiableOn.differentiableAt ((RowHeckeBridge.isOpen_re_gt 0).mem_nhds hp.2.2.1)))).mul (hcomp D.W1Hat (fun p => p.2.1) (by fun_prop)
    ((RowAnalyticContinuation.W1Hat_differentiable D) w))).mul (DifferentiableAt.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hq.ne')))).mul ?_)
  unfold rawFactor
  simp only [div_eq_mul_inv]
  exact (((hcomp D.recipe.L (fun p => 6 * p.2.2) (by fun_prop) hzeta).mul (hcomp ((pkg D).plus u) (fun p => p.2.1) (by fun_prop) (plus_differentiableAt D u hu w hp.2.1))).mul ((RawEulerProduct31.correctionProduct_differentiableOn D (rawFrequency D u)).differentiableAt
    (OmegaStar_isOpen.mem_nhds hp))).mul ((hcomp ((pkg D).minus u) (fun p => p.1) (by fun_prop) (minus_differentiableAt D u hu ξ hp.1)).inv hξ)

include hu in
theorem rawKernel_continuousAt_heights (Z : ℝ) (hZ : 0 < Z) (x y v : ℝ)
    (hp : ((x : ℂ), (y : ℂ), (v : ℂ)) ∈ OmegaStar) (hv : 1 / 6 < v) (t : ℝ × ℝ × ℝ)
    (hξ : (pkg D).minus u ((x : ℂ) + (t.1 : ℂ) * Complex.I) ≠ 0) :
    ContinuousAt (fun t : ℝ × ℝ × ℝ => rawKernel D u ((x : ℂ) + (t.1 : ℂ) * Complex.I)
      ((y : ℂ) + (t.2.1 : ℂ) * Complex.I) ((v : ℂ) + (t.2.2 : ℂ) * Complex.I) Z) t := by
  have hmem : (((x : ℂ) + (t.1 : ℂ) * Complex.I), ((y : ℂ) + (t.2.1 : ℂ) * Complex.I),
      ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)) ∈ OmegaStar := by
    simpa [OmegaStar] using hp
  have hd := rawKernel_differentiableAt D u hu Z hZ _ hmem (by simpa using hv) hξ
  have hcont : Continuous (fun t : ℝ × ℝ × ℝ => (((x : ℂ) + (t.1 : ℂ) * Complex.I,
      (y : ℂ) + (t.2.1 : ℂ) * Complex.I, (v : ℂ) + (t.2.2 : ℂ) * Complex.I) : ℂ × ℂ × ℂ)) := by
    fun_prop
  exact ContinuousAt.comp
    (f := fun t : ℝ × ℝ × ℝ => (((x : ℂ) + (t.1 : ℂ) * Complex.I,
      (y : ℂ) + (t.2.1 : ℂ) * Complex.I, (v : ℂ) + (t.2.2 : ℂ) * Complex.I) : ℂ × ℂ × ℂ))
    (x := t) hd.continuousAt hcont.continuousAt

end

theorem minus_ne_zero_of_not_exceptional (ρ U : ℝ) (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (hU1 : U ≤ frequencyNorm D.recipe u)
    (hU2 : frequencyNorm D.recipe u < 2 * U) (hexc : u ∉ FixedData.rawExceptionalSet D ρ U)
    (ξ : ℂ) (hx : DetectorDef.σ₀ ≤ ξ.re) (hx0 : 0 < ξ.re) (him : |ξ.im| ≤ 4 * U ^ ρ) :
    (pkg D).minus u ξ ≠ 0 := by
  refine minus_ne_zero_of_not_isLZero D u hu ξ hx0 ?_
  intro hz
  exact hexc ⟨hu, hU1, hU2, ξ, hz, hx, him⟩

end

end DedekindZetaZeroFree.Quantitative.RawKernelRegularity31
