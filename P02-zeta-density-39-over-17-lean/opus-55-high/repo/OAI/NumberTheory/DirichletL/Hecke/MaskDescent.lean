module
public import OAI.NumberTheory.DirichletL.Moments.HeckeVolume
public import OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

open scoped Classical

namespace SevenEighths.HeckeMaskDescent
open HeckeFamily CenteredExceptionalProfile CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem exists_coprime_shift (a c r : O) (hac : IsCoprime a c) (hr : r ≠ 0) :
    ∃ t : O, IsCoprime (a+t*c) r := by
  let : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  pm_8491 normalizedFactors r
  refine ⟨s.prod, IsCoprime.symm ?_⟩
  pm_6149 hr hpr
  · have hpc : ¬p ∣ c := fun h => hp.not_isUnit (hac.isUnit_of_dvd' hpa h)
    have hps : ¬p ∣ s.prod := by
      intro h
      obtain ⟨q,hq,hpq⟩ := hp.exists_mem_multiset_dvd h
      obtain ⟨hqr,hqa⟩ := Multiset.mem_filter.mp hq
      exact hqa ((hp.associated_of_dvd (prime_of_normalized_factor q hqr) hpq).dvd'.trans hpa)
    have ht : p ∣ s.prod*c := by convert dvd_sub hpnew hpa using 1 ; ring
    exact (hp.dvd_or_dvd ht).elim hps hpc
  · obtain ⟨q,hq,hpq⟩ := exists_mem_normalizedFactors_of_dvd hr hp.irreducible hpr
    have hqs : q ∈ s := Multiset.mem_filter.mpr ⟨hq,fun h => hpa (hpq.dvd.trans h)⟩
    have ht : p ∣ s.prod*c := dvd_mul_of_dvd_left (hpq.dvd.trans (Multiset.dvd_prod hqs)) c
    exact hpa (by convert dvd_sub hpnew ht using 1 ; ring)

theorem exists_primitive_above (χ : Character) (Q : Ideal O)
    (hdesc : FiniteConductor.FactorsThroughIdeal χ.residue
      (Q.map (Ideal.Quotient.mk χ.modulus))) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ ψ := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  obtain ⟨K,φ,hMK,hQK,hK,hprim,hnorm,hmask⟩ :=
    ConductorPresentation.exists_primitive_presentation_above_quotient
      χ.modulus χ.residue (Q.map (Ideal.Quotient.mk χ.modulus)) hdesc
  have hu : IdealCharacter.UnitInvariant K φ := by
    intro u
    have h := hmask (u : O)
    simpa only [χ.unit_trivial u,u.isUnit.map (Ideal.Quotient.mk χ.modulus),ite_true] using h.symm
  refine ⟨Character.ofResidue K hK φ hu,hprim,?_,?_⟩
  · exact (Ideal.le_comap_map).trans hQK
  · exact IdealCharacter.ofResidue_source_mask χ.modulus K χ.residue φ χ.unit_trivial hu hmask

section
variable (χ χ' ψ : Character) (r : O)
include χ χ' ψ r
theorem descent_of_mask (hr : r ≠ 0)
    (he : ∀ n, elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0)
    (hind : InducedBy χ' ψ) :
    FiniteConductor.FactorsThroughIdeal χ.residue
      (ψ.modulus.map (Ideal.Quotient.mk χ.modulus)) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  pm_1026
  let a : O := 1+q
  have ha : Ideal.Quotient.mk χ.modulus a = (u : O ⧸ χ.modulus) := by
    dsimp [a];rw [map_add,map_one,hqu];ring
  have hψa : Ideal.Quotient.mk ψ.modulus a = 1 := by
    simp only [a,map_add,map_one,Ideal.Quotient.eq_zero_iff_mem.mpr hq,add_zero]
  let c := idealGenerator (χ.modulus*ψ.modulus)
  have hc : IsCoprime a c := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [show Ideal.span {c}=χ.modulus*ψ.modulus from span_idealGenerator _]
    apply IsCoprime.mul_right
    · exact (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (ha ▸ u.isUnit)
    · exact (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hψa ▸ isUnit_one)
  obtain ⟨t,htall⟩ := exists_coprime_shift a c (r*goodLambda) hc
    (mul_ne_zero hr goodLambda_prime.ne_zero)
  have ht := htall.of_mul_right_left
  let n := a+t*c
  have hmem : c ∈ χ.modulus*ψ.modulus := by
    rw [← span_idealGenerator (χ.modulus*ψ.modulus)]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hnχ : Ideal.Quotient.mk χ.modulus n = (u : O ⧸ χ.modulus) := by
    pm_6835 Ideal.mul_le_left ha
  have hnψ : Ideal.Quotient.mk ψ.modulus n = 1 := by
    pm_6835 Ideal.mul_le_right hψa
  have hnχ' : elementCoeff χ' n ≠ 0 := by
    rw [he n,ite_eq_left ht]
    exact MulChar.apply_ne_zero_iff.mpr (hnχ ▸ u.isUnit)
  have hn0 : n ≠ 0 := by
    intro hz
    have hunit : IsUnit goodLambda := (htall.of_mul_right_right).isUnit_of_dvd'
      (by change goodLambda ∣ n; rw [hz]; exact dvd_zero _) (dvd_refl _)
    exact goodLambda_prime.not_isUnit hunit
  have hcop : IsCoprime (Ideal.span {n}) χ'.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hnχ')
  have heq := elementCoeff_eq_of_inducedBy χ' ψ hind n hn0 hcop
  rw [he n,ite_eq_left ht] at heq
  change χ.residue (Ideal.Quotient.mk χ.modulus n) = ψ.residue (Ideal.Quotient.mk ψ.modulus n) at heq
  simpa only [hnχ,hnψ,map_one] using heq

theorem inducedBy_mask
    (he : ∀ n, elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0)
    (hind : InducedBy χ ψ) : InducedBy χ' ψ := by
  intro I
  by_cases hI : I = 0
  pm_6693
  · have hn' := CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I |>.mpr ⟨hI,hc⟩
    pm_5100 idealGenerator hn0 idealGenerator_ne_zero hspan span_idealGenerator
    pm_7913 hval' χ'
    pm_7913 hval χ
    have hm := he n
    have hcr : IsCoprime n r := by
      by_contra hr
      rw [ite_eq_right hr,hval'] at hm
      exact hn' hm
    rw [ite_eq_left hcr,hval',hval] at hm
    have hn := hm ▸ hn'
    pm_8554 hcχ
    rw [ite_eq_left hc,hm,hind I,ite_eq_left hcχ]
  · have hz : idealCoeff χ' I = 0 := by
      pm_7210
    rw [ite_eq_right hc,hz]
end

theorem fixed_inducing_mask_iff (χ χ' : Character) (r : O) (hr : r ≠ 0)
    (he : ∀ n, elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0) (Q : Ideal O) :
    (∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ' ψ) ↔
    (∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ ψ) := by
  constructor
  · rintro ⟨ψ,hprim,hQ,hind⟩
    obtain ⟨ρ,hρ,hmod,hindρ⟩ := exists_primitive_above χ ψ.modulus
      (descent_of_mask χ χ' ψ r hr he hind)
    exact ⟨ρ,hρ,hQ.trans hmod,hindρ⟩
  · rintro ⟨ψ,hprim,hQ,hind⟩
    exact ⟨ψ,hprim,hQ,inducedBy_mask χ χ' ψ r he hind⟩
end SevenEighths.HeckeMaskDescent


end OAI
