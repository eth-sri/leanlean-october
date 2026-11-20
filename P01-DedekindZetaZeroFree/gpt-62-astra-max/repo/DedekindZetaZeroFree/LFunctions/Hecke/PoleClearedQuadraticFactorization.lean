module

public import DedekindZetaZeroFree.LFunctions.Hecke.CompletionScaling
public import DedekindZetaZeroFree.Arithmetic.LocalFields.TotallyComplexQuadraticSignature
public import DedekindZetaZeroFree.LFunctions.Hecke.AbsoluteEulerProducts
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticLocalEulerFactors

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

noncomputable section
open scoped NumberField Classical Topology
open Filter IsDedekindDomain

private theorem norm_le_one_of_cube {F : Type} [Field F] [NumberField F]
    {f : Ideal (𝓞 F)} (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I) (I : Ideal (𝓞 F)) : ‖η I‖ ≤ 1 := by
  rcases mul_eq_zero.mp (by
    have : η I * (η I ^ 2 - 1) = η I ^ 3 - η I := by ring
    rw [this, hq I, sub_self]) with h0 | h1
  · simp [h0]
  · have h2 : ‖η I‖ * ‖η I‖ = 1 := by
      rw [← norm_mul, ← pow_two, (sub_eq_zero.mp h1)]; simp
    nlinarith [norm_nonneg (η I)]

section

variable (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F) (f : Ideal (𝓞 F))
    (hf : f ≠ ⊥) (η : DedekindZetaZeroFree.RayClassCharacter F f) (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hn : ¬ η.IsPrincipal) (hp : η.IsPrimitive) (d : QuadraticRayExtensionData η)

include hF hf hq hn hp in
private theorem quadratic_idealHeckeL_factorization_aux (s : ℂ) (hs : 1 < s.re) :
    idealHeckeL (principalUnitRayCharacter d.extension) s =
      idealHeckeL (principalUnitRayCharacter F) s * idealHeckeL η s := by
  have hfun : (fun p : HeightOneSpectrum (𝓞 F) =>
        ∏' Q : {Q : HeightOneSpectrum (𝓞 d.extension) //
          Q.asIdeal.LiesOver p.asIdeal},
          (1 - (Ideal.absNorm Q.val.asIdeal : ℂ) ^ (-s))⁻¹) =
      (fun p : HeightOneSpectrum (𝓞 F) =>
        (1 - (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹ *
          (1 - η p.asIdeal * (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹) := by
    funext p
    exact quadratic_local_euler_factors F hF f hf η hq hn hp d p s hs
  exact HasProd.unique (principal_idealHeckeL_euler_finite_fibers_grouped F d.extension s hs).2 (hfun.symm ▸ (((principal_idealHeckeL_absolute_euler_product F s hs).2.1).mul ((idealHeckeL_absolute_euler_product η s hf (fun I => norm_le_one_of_cube η hq I) hs).2)))

include hF hf hq hn hp in
private theorem poleCleared_agrees_on_halfplane
    (pF : PrincipalHeckeWitness (principalUnitRayCharacter F))
    (pE : PrincipalHeckeWitness (principalUnitRayCharacter d.extension))
    (w : EntireHeckeWitness η) :
    ∀ s : ℂ, 1 < s.re →
      pE.Λ s = heckeCompletionFactor d.extension ⊤ s *
        idealHeckeL (principalUnitRayCharacter d.extension) s := by
  intro s hs
  refine HasSum.unique (pE.hasSum s hs) ?_
  exact ((principal_idealHeckeL_absolute_euler_product d.extension s hs).1.hasSum).mul_left _

end

private theorem poleCleared_base_series
    (F : Type) [Field F] [NumberField F]
    (pF : PrincipalHeckeWitness (principalUnitRayCharacter F)) :
    ∀ s : ℂ, 1 < s.re →
      pF.Λ s = heckeCompletionFactor F ⊤ s *
        idealHeckeL (principalUnitRayCharacter F) s := by
  intro s hs
  refine HasSum.unique (pF.hasSum s hs) ?_
  exact ((principal_idealHeckeL_absolute_euler_product F s hs).1.hasSum).mul_left _

private theorem poleCleared_eta_series
    {F : Type} [Field F] [NumberField F]
    {f : Ideal (𝓞 F)} (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hη : ∀ I, ‖η I‖ ≤ 1)
    (w : EntireHeckeWitness η) :
    ∀ s : ℂ, 1 < s.re →
      w.Λ s = heckeCompletionFactor F f s * idealHeckeL η s := by
  intro s hs
  refine HasSum.unique (w.hasSum s hs) ?_
  exact ((idealHeckeL_absolute_euler_product η s hf hη hs).1.hasSum).mul_left _

private theorem eq_of_agrees_on_halfplane {A B : ℂ → ℂ}
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (h : ∀ s : ℂ, 1 < s.re → A s = B s) : ∀ s : ℂ, A s = B s := by
  have hmem : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by norm_num
  have hev : A =ᶠ[𝓝 (2 : ℂ)] B := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem] with s hs using h s hs
  have hEq := AnalyticOnNhd.eq_of_eventuallyEq (Complex.analyticOnNhd_univ_iff_differentiable.mpr hA) (Complex.analyticOnNhd_univ_iff_differentiable.mpr hB) hev
  exact fun s => congr_fun hEq s

theorem poleClearedHecke_factorization
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hn : ¬ η.IsPrincipal) (hp : η.IsPrimitive)
    (d : QuadraticRayExtensionData η)
    (pF : PrincipalHeckeWitness (principalUnitRayCharacter F))
    (pE : PrincipalHeckeWitness (principalUnitRayCharacter d.extension))
    (w : EntireHeckeWitness η) :
    ∀ s : ℂ, pE.U s =
      Complex.exp ((heckeCompletionLogScale F d.extension f : ℂ) * s) *
        pF.U s * w.Λ s := by
  have hexp : Differentiable ℂ (fun s : ℂ =>
      Complex.exp ((heckeCompletionLogScale F d.extension f : ℂ) * s)) :=
    Complex.differentiable_exp.comp
      ((differentiable_const (c := (heckeCompletionLogScale F d.extension f : ℂ))).mul
        differentiable_id)
  have hB : Differentiable ℂ (fun s : ℂ =>
      Complex.exp ((heckeCompletionLogScale F d.extension f : ℂ) * s) * pF.U s * w.Λ s) :=
    (hexp.mul pF.differentiable_U).mul w.differentiable
  refine eq_of_agrees_on_halfplane pE.differentiable_U hB ?_
  intro s hs
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  rw [(pE.poleClearing s hs0 hs1), (pF.poleClearing s hs0 hs1), (poleCleared_agrees_on_halfplane F hF f hf η hq hn hp d pF pE w s hs), (poleCleared_base_series F pF s hs), (poleCleared_eta_series hf η (fun I => norm_le_one_of_cube η hq I) w s hs), (quadratic_idealHeckeL_factorization_aux F hF f hf η hq hn hp d s hs), (heckeCompletionFactor_scaling F d.extension f hf (quadraticExtension_signature F d.extension hF d.degree_two).2 s)]
  ring

end

end DedekindZetaZeroFree.LargeSieve
