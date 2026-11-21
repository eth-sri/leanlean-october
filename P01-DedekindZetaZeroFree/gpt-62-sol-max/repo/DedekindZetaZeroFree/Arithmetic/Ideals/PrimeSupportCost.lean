module

public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorFinsets

@[expose] public section

open scoped NumberField Classical
open UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.LargeSieve

lemma primeSupportCost_le_divisorCount {F : Type} [Field F] [NumberField F]
    (u : Ideal (𝓞 F)) (hu : u ≠ ⊥) :
    (2 : ℝ) ^ (normalizedFactors u).toFinset.card ≤ (idealDivisorCount u : ℝ) := by
  let S := (normalizedFactors u).toFinset
  have mem (s : Finset (Ideal (𝓞 F))) (hs : s ∈ S.powerset) {p} (hp : p ∈ s.val) :
      p ∈ normalizedFactors u := Multiset.mem_toFinset.mp ((Finset.mem_powerset.mp hs) hp)
  have factors (s : Finset (Ideal (𝓞 F))) (hs : s ∈ S.powerset) :
      normalizedFactors s.val.prod = s.val := by
    rw [normalizedFactors_prod_eq _ (fun p hp => irreducible_of_normalized_factor p (mem s hs hp)),
      Multiset.map_congr rfl (fun p hp => normalize_normalized_factor p (mem s hs hp)),
      Multiset.map_id']
  have hc : S.powerset.card ≤ (idealDivisors u).card := by
    apply Finset.card_le_card_of_injOn (fun s => s.val.prod)
    · intro s hs
      apply (mem_idealDivisors hu).mpr
      rw [← Ideal.prod_normalizedFactors_eq_self hu]
      exact Multiset.prod_dvd_prod_of_le ((Multiset.le_iff_subset s.nodup).mpr (fun p hp => mem s hs hp))
    · intro s hs t ht h
      exact Finset.val_inj.mp ((factors s hs).symm.trans ((congrArg normalizedFactors h).trans (factors t ht)))
  rw [Finset.card_powerset] at hc
  exact_mod_cast hc

end DedekindZetaZeroFree.LargeSieve
