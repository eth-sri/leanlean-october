module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.Residues.GlobalQuotientEquivalence

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSumCompatibility
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
    {A : SArithmeticData F} {σ : F →+* ℂ}
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem reduction_isUnit (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : n ≠ 0) (x : Residue C p n) :
    IsUnit (reduction C p n hn x) ↔ IsUnit x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) r) ↔
    IsUnit (Ideal.Quotient.mk (Ideal.span {generator C p ^ n}) r)
  rw [← Ideal.span_singleton_pow, (generator_generates C p).2]
  exact (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk _ hn).symm

alias exterior_notMem := DedekindZetaZeroFree.CompatiblePrimeRawLocal.SIntegerConductor.exterior_notMem
end DedekindZetaZeroFree.LocalFiniteSumCompatibility

end
