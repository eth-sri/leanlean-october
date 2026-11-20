module
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.IntegralPrincipalCongruence

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.FullModulusAndIntegralIdealUnits
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsRayCongruent
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayLocalHigherUnitOneAdd

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical WithZero
open WithZeroMulInt
open NumberField

variable {F : Type*} [Field F] [NumberField F]

private lemma maximalIdeal_pow_mem_iff_exp (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (n : ℕ) (y : v.adicCompletionIntegers F) :
    y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n ↔
      Valued.v (y : v.adicCompletion F) ≤ WithZero.exp (-(n : ℤ)) := by
  haveI : IsDiscreteValuationRing (v.adicCompletionIntegers F) := inferInstance
  haveI hw : ((Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).IsRankOneDiscrete := inferInstance
  let O := v.adicCompletionIntegers F
  let ϖ : O := Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal O)
  have hspan : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (Ideal.span_singleton_generator _).symm
  have hunif : Valuation.IsUniformizer (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) ϖ :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span
      (v := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)) hspan
  have hval : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [Valuation.IsUniformizer.iff.mp hunif,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (v := Valued.v) (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective F v), Units.val_mk0]
  rw [← SetLike.mem_coe,
    Valuation.Integers.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow
       (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers F v) ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hspan) n]
  simp only [Set.mem_setOf_eq]
  have hval' : Valued.v
      (algebraMap O (v.adicCompletion F) ϖ) = WithZero.exp (-1 : ℤ) := by
    exact hval
  rw [hval']
  have hpow : (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) ^ n = WithZero.exp (-(n : ℤ)) := by
    rw [← WithZero.exp_nsmul, nsmul_eq_mul]
    norm_num
  rw [hpow]
  simp

private lemma valued_algebraMap_eq_intValuation (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (a : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletion F) =
      v.intValuation a := by
  rw [(IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply (𝓞 F) F v a), IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
      (algebraMap (𝓞 F) F a),
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap v a]

private alias local_power_mem_iff := IntegralPrincipalCongruence.loc_local_power_mem_iff

variable (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (x : Fˣ)
    (hx : ClassFieldTheory.IsRayCongruent (fullModulus m hm) x)

include hx in
theorem ray_congruent_sub_mem
    (a b : 𝓞 F) (hab : (a : F) = (x : F) * (b : F)) :
    a - b ∈ m := by
  rw [← Ideal.iInf_maxPowDividing_eq hm, Ideal.mem_iInf]
  intro v
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing]
  let n : ℕ := (Associates.mk v.asIdeal).count (Associates.mk m).factors
  change a - b ∈ v.asIdeal ^ n
  by_cases hn : n = 0
  · rw [hn, pow_zero]
    simp
  · have hfp : (fullModulus m hm).finitePart v = n := rfl
    have hlocal := hx.1 v (by
      rw [Finsupp.mem_support_iff, hfp]
      exact hn)
    rw [hfp] at hlocal
    obtain ⟨t, ht, hxeq⟩ :=
      (ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff_exists_one_add v n (Nat.one_le_iff_ne_zero.mpr hn)
        (ClassFieldTheory.finitePlaceUnitEmbedding v x)).mp hlocal
    rw [← local_power_mem_iff v n (a - b)]
    have hxe : algebraMap F (v.adicCompletion F) (x : F) = 1 + t := by
      have h1 : algebraMap F (v.adicCompletion F) (x : F) =
          ((ClassFieldTheory.finitePlaceUnitEmbedding v x : (v.adicCompletion F)ˣ) :
            v.adicCompletion F) := by
        simp [ClassFieldTheory.finitePlaceUnitEmbedding]
      rw [h1, hxeq]
      simp
    have hG : (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (a - b) : v.adicCompletion F) =
        (algebraMap (𝓞 F) (v.adicCompletionIntegers F) b : v.adicCompletion F) *
          t := by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
        IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
        map_sub (algebraMap (𝓞 F) F) a b]
      show algebraMap F (v.adicCompletion F) ((a : F) - (b : F)) =
        algebraMap F (v.adicCompletion F) (b : F) * t
      rw [hab, map_sub, map_mul, hxe]
      ring
    have hEq : algebraMap (𝓞 F) (v.adicCompletionIntegers F) (a - b) =
        algebraMap (𝓞 F) (v.adicCompletionIntegers F) b * t := by
      apply Subtype.ext
      rw [hG]
      simp
    rw [hEq]
    exact Ideal.mul_mem_left _ _ ht

include hx in
theorem ray_congruent_pos :
    ∀ φ : F →+* ℝ, 0 < φ (x : F) := by
  intro φ
  let ψ := Complex.ofRealHom.comp φ
  have hψ : ComplexEmbedding.IsReal ψ := by
    rw [ComplexEmbedding.isReal_iff]
    ext s
    simp [RingHom.star_apply, ψ, Complex.conj_ofReal]
  let w := InfinitePlace.mk ψ
  have hw : w.IsReal := ⟨ψ, hψ, rfl⟩
  have hpos := hx.2 ⟨w, hw⟩ (Finset.mem_univ _)
  have hconv : InfinitePlace.embedding_of_isReal hw (x : F) = φ (x : F) := by
    apply Complex.ofReal_injective
    rw [InfinitePlace.embedding_of_isReal_apply]
    rw [(InfinitePlace.embedding_mk_eq_of_isReal hψ)]
    rfl
  rwa [hconv] at hpos

end DedekindZetaZeroFree.LargeSieve.RayBridge

end
