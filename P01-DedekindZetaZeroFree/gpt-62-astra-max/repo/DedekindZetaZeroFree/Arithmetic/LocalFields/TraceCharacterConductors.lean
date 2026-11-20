module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.ResiduePhases.ResidueTracePhases
public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceCharacterConductor

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain LocalFieldTheory WithZero
open ValuationTheory.DiscreteValuationField
open scoped ValuativeRel nonZeroDivisors

namespace DedekindZetaZeroFree.ArithmeticContext
noncomputable section
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]

private theorem primeBelow_eq_adapter (v : HeightOneSpectrum (𝓞 F)) :
    ResidueTrace.rationalPrimeBelow v = PlaceTraceAdapter.prime F v := by exact ResidueTraceFactorProductFormula.GlobalTraceProductFormula.residuePrime_eq_adapter v

private theorem character_eq_adapter (v : HeightOneSpectrum (𝓞 F)) :
    ResidueTrace.localTraceCharacter v = localFiniteCharacter F v := by
  have hp := primeBelow_eq_adapter v
  have hgeneral (p : Nat.Primes) (m : ℚ_[p] →+* v.adicCompletion F)
      (hmc : Continuous m)
      (hmq : ∀ q : ℚ, m (q : ℚ_[p]) =
        algebraMap F (v.adicCompletion F) (algebraMap ℚ F q))
      (hp : p = PlaceTraceAdapter.prime F v) :
      (letI := m.toAlgebra
       (rationalPadicCharacter p).compAddMonoidHom
        (Algebra.trace ℚ_[p] (v.adicCompletion F)).toAddMonoidHom) = localFiniteCharacter F v := by
    subst p
    have hmap : m = PlaceTraceAdapter.padicMap F v := by
      apply DFunLike.coe_injective
      apply (Padic.denseRange_ratCast (PlaceTraceAdapter.prime F v)).equalizer hmc
      · letI : Algebra ℚ ((PlaceTraceAdapter.rationalPlace F v).adicCompletion ℚ) :=
          HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ _
        exact (finitePlaceAdicCompletionMap_continuous ℚ F _ _).comp
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (PlaceTraceAdapter.rationalPlace F v)).symm.continuous
      · funext q
        exact (hmq q).trans (by simp)
    subst m
    rfl
  exact hgeneral _ _ (ResidueTrace.baseEmbedding_spec v).1
    (ResidueTrace.baseEmbedding_spec v).2 hp

alias TraceCharacterConductors.character_eq_adapter := character_eq_adapter

private theorem codifferent_eq_integers_of_good (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    (localCodifferent F v : Set (v.adicCompletion F)) =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  rw [localCodifferent_eq_inverse_different, localDifferent_eq_top_of_not_dvd_different F v hv,
    IsLocalization.coeSubmodule_top]
  have hdiv : (1 : Submodule (LocalConductor.target F v).valuationSubring (v.adicCompletion F)) / 1 = 1 := by
    ext x
    rw [Submodule.mem_div_iff_forall_mul_mem]
    constructor
    · intro h
      simpa using h 1 (by simp)
    · intro h y hy
      simpa using Submodule.mul_mem_mul h hy
  rw [hdiv]
  ext x
  change x ∈ (1 : Submodule (LocalConductor.target F v).valuationSubring (v.adicCompletion F)) ↔ _
  rw [Submodule.mem_one]
  rw [← LocalConductor.target_integerRing_eq F v]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ z.property, fun h => ⟨⟨x,h⟩,rfl⟩⟩

theorem exists_trace_exclusion_set (F : Type) [Field F] [NumberField F] :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ v : HeightOneSpectrum (𝓞 F), v ∉ T → ResidueTrace.IsSelfDual v := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ differentIdeal ℤ (𝓞 F)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  refine ⟨hfin.toFinset, ?_⟩
  intro v hv
  intro x
  rw [character_eq_adapter]
  change (∀ o : v.adicCompletionIntegers F, localFiniteCharacter F v (x * o) = 1) ↔ x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  rw [← (codifferent_eq_integers_of_good v (by simpa using hv))]
  change (∀ o : v.adicCompletionIntegers F, localFiniteCharacter F v (x * o) = 1) ↔ x ∈ localCodifferent F v
  unfold localCodifferent
  rw [RamificationTheory.DiscreteValuationField.ValuedExtension.mem_codifferentSubmodule_iff_trace_mul_integral_of_finite_separable]
  have ha (a : v.adicCompletion F) : a ∈ (1 : Submodule (LocalConductor.target F v).valuationSubring (v.adicCompletion F)) ↔
      a ∈ v.adicCompletionIntegers F := by
    rw [Submodule.mem_one]
    change (∃ z : (LocalConductor.target F v).valuationSubring, z = a) ↔ a ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    rw [← LocalConductor.target_integerRing_eq F v]
    exact ⟨fun ⟨z, hz⟩ => hz ▸ z.property, fun h => ⟨⟨a,h⟩,rfl⟩⟩
  have hb (t : ℚ_[PlaceTraceAdapter.prime F v]) :
      IsIntegral (LocalConductor.base F v).valuationSubring t ↔
        rationalPadicCharacter (PlaceTraceAdapter.prime F v) t = 1 := by
    rw [rationalPadicCharacter_eq_one_iff, IsIntegrallyClosed.isIntegral_iff]
    have hmem (z : ℚ_[PlaceTraceAdapter.prime F v]) : z ∈ (LocalConductor.base F v).valuation.valuationSubring ↔ ‖z‖ ≤ 1 := by
      simp only [LocalConductor.base, localCompleteDVF_valuation_eq]
      exact LocalFieldTheory.Padic.integer_mem_iff_norm_le_one _ z
    exact ⟨fun ⟨z,hz⟩ => ⟨⟨z, (hmem z).mp z.property⟩,hz⟩,
      fun ⟨z,hz⟩ => ⟨⟨z, (hmem z).mpr z.property⟩,hz⟩⟩
  simp only [ha, hb]
  constructor
  · intro h a ha
    exact h ⟨a, ha⟩
  · intro h o
    exact h o o.property

end
end DedekindZetaZeroFree.ArithmeticContext
