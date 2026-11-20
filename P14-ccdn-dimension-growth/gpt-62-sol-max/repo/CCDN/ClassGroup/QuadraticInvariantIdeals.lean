/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
import CCDN.ClassGroup.QuadraticNormConjugation
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! Prime ideal orbits in a quadratic number-field extension.
These are the arithmetic inputs for factoring invariant ideals into
extended base ideals and ramified prime factors. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField Ideal
open scoped Pointwise

variable (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [FiniteDimensional F K]

private theorem quadratic_prime_orbit_eq_pair
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] :
    (Q.under (𝓞 F)).primesOver (𝓞 K) = {Q, σ • Q} := by
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  
  ext P
  constructor
  · intro hP
    have : P.IsPrime := hP.1
    have : P.LiesOver (Q.under (𝓞 F)) := hP.2
    obtain ⟨τ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
      (Q.under (𝓞 F)) Q P (K ≃ₐ[F] K)
    rcases quadratic_automorphism_eq_one_or F K hd σ hσ τ with rfl | rfl
    · simp
    · simp
  · intro hP
    rcases Set.mem_insert_iff.mp hP with rfl | hP
    tauto
    · 
      subst P
      exact ⟨inferInstance, inferInstance⟩

/-- Extending the prime below `Q` gives its two conjugates in the moving case,
and the first or second power of `Q` in the fixed case. -/
theorem quadratic_prime_extension
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    let E := (Q.under (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 K))
    if σ • Q = Q then E = Q ∨ (Q.ramificationIdx (𝓞 F) = 2 ∧ E = Q ^ 2)
    else E = Q * (σ • Q) := by
  classical
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  let : IsGaloisGroup (K ≃ₐ[F] K) (𝓞 F) (𝓞 K) := IsGaloisGroup.of_isFractionRing _ _ _ F K
  let P := Q.under (𝓞 F)
  have hP : P ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) hQ
  let : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hP
  have hmap := Ideal.map_algebraMap_eq_finsetProd_pow (R := 𝓞 K) hP
  have hdeg := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn P (𝓞 K) (K ≃ₐ[F] K)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx P Q (K ≃ₐ[F] K),
    Ideal.inertiaDegIn_eq_inertiaDeg P Q (K ≃ₐ[F] K), IsGalois.card_aut_eq_finrank, hd] at hdeg
  have hpair : P.primesOver (𝓞 K) = {Q, σ • Q} := quadratic_prime_orbit_eq_pair F K hd σ hσ Q
  have hset : (P.primesOver (𝓞 K)).toFinset = {Q, σ • Q} := by
    ext x
    rw [Set.mem_toFinset, hpair]
    simp
  rw [hpair] at hdeg
  rw [hset] at hmap
  dsimp only
  split_ifs with hfix
  · have hdvd : Q.ramificationIdx (𝓞 F) ∣ 2 :=
      ⟨Q.inertiaDeg (𝓞 F), by simpa [hfix] using hdeg.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with he | he
    · exact Or.inl (by simpa [P, hfix, he] using hmap)
    · exact Or.inr ⟨he, by simpa [P, hfix, he] using hmap⟩
  · have hn : Q ≠ σ • Q := fun h => hfix h.symm
    have he : Q.ramificationIdx (𝓞 F) = 1 := by simp_all
    have he' : (σ • Q).ramificationIdx (𝓞 F) = 1 := by simpa using he
    simpa [P, hn, he, he'] using hmap

end
end CCDN
