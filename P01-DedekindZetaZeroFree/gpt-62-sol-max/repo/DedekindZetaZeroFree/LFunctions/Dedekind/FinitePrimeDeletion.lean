module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization

public section

open IsDedekindDomain
open scoped Classical

namespace DedekindZetaZeroFree

/-- Deleting finitely many prime factors from a multiplicative ideal sum. -/
theorem finite_prime_delete_hasSum {R : Type*} [CommRing R] [IsDedekindDomain R]
    {W : Ideal R → ℂ} {L : ℂ} (hmul : ∀ I J, W (I * J) = W I * W J)
    (hW : HasSum W L) (V : Finset (HeightOneSpectrum R)) :
    HasSum (fun I => if ∃ v ∈ V, I ≤ v.asIdeal then 0 else W I)
      (L * ∏ v ∈ V, (1 - W v.asIdeal)) := by
  induction V using Finset.induction_on with
  | empty => simpa using hW
  | @insert p V hp ih =>
    let G : Ideal R → ℂ := fun I => if ∃ v ∈ V, I ≤ v.asIdeal then 0 else W I
    let H : Ideal R → ℂ := fun I => if I ≤ p.asIdeal then G I else 0
    have hle (v : HeightOneSpectrum R) (hv : v ∈ V) : ¬ p.asIdeal ≤ v.asIdeal :=
      fun h => hp (HeightOneSpectrum.ext (p.isMaximal.eq_of_le v.isMaximal.ne_top h).symm ▸ hv)
    have hi : Function.Injective (fun I : Ideal R => I * p.asIdeal) :=
      mul_left_injective₀ p.ne_bot
    have hH : HasSum H ((L * ∏ v ∈ V, (1 - W v.asIdeal)) * W p.asIdeal) := by
      apply (hi.hasSum_iff ?_).mp
      · refine (ih.mul_right _).congr_fun fun I => ?_
        have hmask : (∃ v ∈ V, I * p.asIdeal ≤ v.asIdeal) ↔ ∃ v ∈ V, I ≤ v.asIdeal := by
          exact ⟨fun ⟨v, hv, h⟩ => ⟨v, hv, (v.isPrime.mul_le.mp h).resolve_right (hle v hv)⟩,
            fun ⟨v, hv, h⟩ => ⟨v, hv, Ideal.mul_le_left.trans h⟩⟩
        simp only [Function.comp_apply, H, Ideal.mul_le_right, ite_true, G, hmask, hmul]
        split_ifs <;> simp
      · intro I hI
        refine ite_eq_right fun h => hI ?_
        obtain ⟨J, rfl⟩ := Ideal.dvd_iff_le.mpr h
        exact ⟨J, mul_comm _ _⟩
    convert ih.sub hH using 1
    · funext I
      by_cases hI : I ≤ p.asIdeal <;> by_cases hV : ∃ v ∈ V, I ≤ v.asIdeal <;>
        simp [H, G, hI, hV]
    · rw [Finset.prod_insert hp]
      ring

end DedekindZetaZeroFree
