module

public import DedekindZetaZeroFree.LFunctions.Hecke.IdealSeriesAbsoluteConvergence
public import DedekindZetaZeroFree.Analysis.MultiplicativeEulerProducts
public import DedekindZetaZeroFree.Arithmetic.Ideals.PrimeExponentEquivalence
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalUnitCharacter

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F] {f : Ideal (𝓞 F)}

alias idealHeckeL_summable := IdealEuler.summable_idealHeckeSummand

theorem idealHeckeL_euler_hasProd
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (s : ℂ)
    (hf : f ≠ ⊥) (hη : ∀ I, ‖η I‖ ≤ 1) (hs : 1 < s.re) :
    HasProd (fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      (1 - η p.asIdeal * (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹)
      (idealHeckeL η s) := by
  classical
  have hzero : IdealEuler.idealHeckeSummandHom η s
      ((IdealEuler.primeExponentEquiv (𝓞 F)) 0).val = 1 := by
    rw [IdealEuler.primeExponentEquiv_zero]
    exact IdealEuler.idealHeckeSummandHom_top η s
  have h1 := IdealEuler.hasProd_finsupp_euler
    (fun d : IsDedekindDomain.HeightOneSpectrum (𝓞 F) →₀ ℕ =>
      IdealEuler.idealHeckeSummandHom η s
        ((IdealEuler.primeExponentEquiv (𝓞 F)) d).val)
    hzero (by
      intro x y
      rw [IdealEuler.primeExponentEquiv_add, map_mul]) (((IdealEuler.primeExponentEquiv (𝓞 F)).summable_iff).mpr ((IdealEuler.summable_norm_idealHeckeSummand η s hf hη hs).subtype _))
  have hfac : (fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      (1 - IdealEuler.idealHeckeSummandHom η s
        ((IdealEuler.primeExponentEquiv (𝓞 F)) (Finsupp.single p 1)).val)⁻¹) =
      (fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      (1 - η p.asIdeal * (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹) := by
    funext p
    rw [IdealEuler.primeExponentEquiv_single, pow_one, IdealEuler.idealHeckeSummandHom_apply]
  have hval : (∑' d : IsDedekindDomain.HeightOneSpectrum (𝓞 F) →₀ ℕ,
      IdealEuler.idealHeckeSummandHom η s
        ((IdealEuler.primeExponentEquiv (𝓞 F)) d).val) = idealHeckeL η s := by
    rw [(IdealEuler.primeExponentEquiv (𝓞 F)).tsum_eq
      (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => IdealEuler.idealHeckeSummandHom η s I.val)]
    show (∑' I : {I : Ideal (𝓞 F) // I ∈ ({J : Ideal (𝓞 F) | J ≠ ⊥})},
      IdealEuler.idealHeckeSummandHom η s I.val) = idealHeckeL η s
    rw [tsum_subtype_eq_of_support_subset ?_]
    · rw [idealHeckeL]
      exact tsum_congr fun I => (IdealEuler.idealHeckeSummandHom_apply η s I).symm
    · intro I hI
      exact fun h => hI (by rw [h]; exact IdealEuler.idealHeckeSummandHom_bot η s)
  rw [hfac, hval] at h1
  exact h1

variable (F : Type) [Field F] [NumberField F] (s : ℂ)

theorem principal_idealHeckeL_euler_hasProd (hs : 1 < s.re) :
    HasProd (fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      (1 - (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹)
      (idealHeckeL (principalUnitRayCharacter F) s) := by
  classical
  have hη : ∀ I : Ideal (𝓞 F), ‖principalUnitRayCharacter F I‖ ≤ 1 := by
    intro I
    rw [principalUnitRayCharacter_apply]
    split <;> simp
  have h := idealHeckeL_euler_hasProd (principalUnitRayCharacter F) s top_ne_bot hη hs
  have hfac : (fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      (1 - principalUnitRayCharacter F p.asIdeal *
        (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹) =
      (fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      (1 - (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹) := by
    funext p
    rw [principalUnitRayCharacter_apply]
    simp [p.ne_bot]
  rw [hfac] at h
  exact h

theorem principal_idealHeckeL_eq_tsum_nonzero :
    idealHeckeL (principalUnitRayCharacter F) s =
      ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, (Ideal.absNorm I.val : ℂ) ^ (-s) := by
  classical
  have hpt : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      principalUnitRayCharacter F I.val * (Ideal.absNorm I.val : ℂ) ^ (-s) =
        (Ideal.absNorm I.val : ℂ) ^ (-s) := by
    intro I
    rw [principalUnitRayCharacter_apply, if_neg I.2, one_mul]
  rw [idealHeckeL]
  rw [← tsum_subtype_eq_of_support_subset
     ?_]
  · refine tsum_congr fun I => ?_
    exact hpt I
  · intro I hI
    exact fun h => hI (by simp [h])

theorem principal_idealHeckeL_summable (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 F) =>
      principalUnitRayCharacter F I * (Ideal.absNorm I : ℂ) ^ (-s)) := by
  classical
  refine idealHeckeL_summable (principalUnitRayCharacter F) s top_ne_bot ?_ hs
  intro I
  rw [principalUnitRayCharacter_apply]
  split <;> simp

end DedekindZetaZeroFree.LargeSieve
