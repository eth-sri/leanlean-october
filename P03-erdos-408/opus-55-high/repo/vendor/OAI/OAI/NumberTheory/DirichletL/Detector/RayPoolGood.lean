module

public import OAI.NumberTheory.DirichletL.Detector.RaySlots

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical CanonicalQuadraticSieve
local notation "Id" => Ideal HeckeFamily.O

theorem prime_coprime_of_norm_gt (η : Character) (P : PrimeIdeal)
    (hN : (η.modulus.absNorm:ℝ)<(P.val.absNorm:ℝ)) : IsCoprime P.val η.modulus := by
  apply Ideal.coprime_of_no_prime_ge
  intro J hPJ hηJ hJ
  have hmax := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have heq := hmax.eq_of_le hJ.ne_top hPJ
  rw [←heq] at hηJ
  have hd : P.val∣η.modulus := Ideal.dvd_iff_le.mpr hηJ
  have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot))
    (map_dvd Ideal.absNorm hd)
  exact (not_le_of_gt hN) (by simp_all)

theorem pool_supported (C : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b x : ℝ) (P : PrimeIdeal) (hP : P∈pool C S a b x) : Supported P.val :=
  outside_prime_supported S hS.bad P ((mem_pool C S a b x P).mp hP).2.2.2

end SevenEighths.ProbeRaySlots
end

end OAI
