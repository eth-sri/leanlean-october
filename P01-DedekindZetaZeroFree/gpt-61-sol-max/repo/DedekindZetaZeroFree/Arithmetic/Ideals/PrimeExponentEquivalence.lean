module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section


namespace DedekindZetaZeroFree.LargeSieve.IdealEuler

open scoped Classical
open IsDedekindDomain

universe u

section Helpers

open UniqueFactorizationMonoid

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

section
variable (e : HeightOneSpectrum R →₀ ℕ)
include e
private theorem product_eq   :
    e.prod (fun p n => p.asIdeal ^ n) =
      (e.toMultiset.map HeightOneSpectrum.asIdeal).prod := by
  classical
  induction e using Finsupp.induction with
  | zero => simp [Finsupp.toMultiset_zero]
  | @single_add p n e hp hn ih =>
    rw [Finsupp.prod_add_index' (fun p : HeightOneSpectrum R => pow_zero p.asIdeal) (fun p : HeightOneSpectrum R => pow_add p.asIdeal),
      Finsupp.toMultiset_add, Finsupp.toMultiset_single, Multiset.map_add,
      Multiset.prod_add, ← ih]
    rw [← Multiset.coe_mapAddMonoidHom, map_nsmul, Multiset.prod_nsmul]
    simp

theorem product_nonzero   :
    e.prod (fun p n => p.asIdeal ^ n) ≠ (⊥ : Ideal R) := by
  rw [product_eq]
  apply Multiset.prod_ne_zero_of_prime
  intro p hp
  obtain ⟨q, _, rfl⟩ := Multiset.mem_map.mp hp
  exact q.prime

private theorem factors_product   :
    normalizedFactors (e.prod (fun p n => p.asIdeal ^ n)) =
      e.toMultiset.map HeightOneSpectrum.asIdeal := by
  rw [product_eq]
  apply normalizedFactors_prod_of_prime
  intro p hp
  obtain ⟨q, _, rfl⟩ := Multiset.mem_map.mp hp
  exact q.prime

noncomputable def exponentProduct   :
    {I : Ideal R // I ≠ ⊥} := ⟨e.prod (fun p n => p.asIdeal ^ n), product_nonzero e⟩
end


theorem exponentProduct_bijective : Function.Bijective (@exponentProduct R _ _) := by
  classical
  constructor
  · intro e d h
    have h' := congrArg (fun I : {I : Ideal R // I ≠ ⊥} => normalizedFactors I.val) h
    change normalizedFactors (e.prod _) = normalizedFactors (d.prod _) at h'
    rw [factors_product, factors_product] at h'
    have := Multiset.map_injective HeightOneSpectrum.asIdeal_injective h'
    simpa using congrArg Multiset.toFinsupp this
  · intro I
    let m := (normalizedFactors I.val).attach.map
      (fun p => HeightOneSpectrum.ofPrime (prime_of_normalized_factor p.val p.property))
    have hm : m.map HeightOneSpectrum.asIdeal = normalizedFactors I.val := by
      simp [m, Multiset.map_map, Function.comp_def]
    refine ⟨m.toFinsupp, Subtype.ext ?_⟩
    change (m.toFinsupp.prod (fun p n => p.asIdeal ^ n)) = I.val
    rw [product_eq, Multiset.toFinsupp_toMultiset, hm]
    exact Ideal.prod_normalizedFactors_eq_self I.property

end Helpers

section
variable (R : Type u) [CommRing R] [IsDedekindDomain R]
include R
noncomputable def primeExponentEquiv   :
    (HeightOneSpectrum R →₀ ℕ) ≃ {I : Ideal R // I ≠ ⊥} := Equiv.ofBijective exponentProduct exponentProduct_bijective

theorem primeExponentEquiv_apply  
    (e : HeightOneSpectrum R →₀ ℕ) :
    (primeExponentEquiv R e).val = e.prod (fun p n => p.asIdeal ^ n) := rfl

theorem primeExponentEquiv_zero   :
    (primeExponentEquiv R 0).val = ⊤ := by
  rw [primeExponentEquiv_apply]
  simp

theorem primeExponentEquiv_single  
    (p : HeightOneSpectrum R) (n : ℕ) :
    (primeExponentEquiv R (Finsupp.single p n)).val = p.asIdeal ^ n := by
  rw [primeExponentEquiv_apply]
  simp

theorem primeExponentEquiv_add  
    (e d : HeightOneSpectrum R →₀ ℕ) :
    (primeExponentEquiv R (e + d)).val =
      (primeExponentEquiv R e).val * (primeExponentEquiv R d).val := by
  simp only [primeExponentEquiv_apply]
  exact Finsupp.prod_add_index' (fun p : HeightOneSpectrum R => pow_zero p.asIdeal)
    (fun p : HeightOneSpectrum R => pow_add p.asIdeal)
end


end DedekindZetaZeroFree.LargeSieve.IdealEuler
