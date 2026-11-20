module

public import DedekindZetaZeroFree.Arithmetic.Ideals.FractionalResidues.QuotientModule

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

def fractionalResidueLiftIdeal (I : FractionalIdeal R⁰ K) (β : K) :
    FractionalIdeal R⁰ K :=
  FractionalIdeal.spanSingleton R⁰ β * I⁻¹

variable (m : Ideal R) (I : FractionalIdeal R⁰ K) (hm : m ≠ ⊥) (hm1 : m ≠ ⊤) (hI : I ≠ 0)
    (z : fractionalResidueModule m I) (hz : Function.Surjective (fun k : R ⧸ m => k • z)) (β : K)
    (hβ : β ∈ I)

include hm hm1 hI hz in
theorem fractionalResidueGenerator_lift_properties
    (hlift : Submodule.Quotient.mk (p := fractionalResidueDenominator m I)
      ⟨β, hβ⟩ = z) :
    β ≠ 0 ∧
      (m : FractionalIdeal R⁰ K) * I + FractionalIdeal.spanSingleton R⁰ β = I ∧
      fractionalResidueLiftIdeal I β ≠ 0 ∧
      fractionalResidueLiftIdeal I β ≤ 1 ∧
      (m : FractionalIdeal R⁰ K) + fractionalResidueLiftIdeal I β = 1 := by
  have hspan :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hβ
  have heq : m * I +
      FractionalIdeal.spanSingleton R⁰ β = I := by
    apply le_antisymm
    · exact add_le (fractionalResidue_mul_le m I) hspan
    · intro x hx
      obtain ⟨k, hk⟩ := hz (Submodule.Quotient.mk
         ⟨x, hx⟩)
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective k
      dsimp only at hk
      rw [← hlift, fractionalResidueModule_mk_smul_mk] at hk
      apply (FractionalIdeal.mem_add _ _ _).mpr
      exact ⟨x - r • β, ((Submodule.Quotient.eq (fractionalResidueDenominator m I)).mp hk.symm), r • β,
        (FractionalIdeal.mem_spanSingleton R⁰).mpr ⟨r, rfl⟩, sub_add_cancel _ _⟩
  have hsum : m + fractionalResidueLiftIdeal I β = 1 := by
    simpa [add_mul, mul_assoc, mul_inv_cancel₀ hI, fractionalResidueLiftIdeal] using (congrArg (fun J : FractionalIdeal R⁰ K => J * I⁻¹) heq)
  have hne : β ≠ 0 := by
    intro hzero
    apply hm1
    apply FractionalIdeal.coeIdeal_injective (K := K)
    exact (by
      simp_all [fractionalResidueLiftIdeal])
  refine ⟨hne, heq, ?_, ?_, hsum⟩
  · exact mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hne) (inv_ne_zero hI)
  · exact Trans.trans (mul_le_mul_of_nonneg_right hspan (FractionalIdeal.zero_le I⁻¹)) (mul_inv_cancel₀ hI)

include hm hm1 hI hz in
theorem fractionalResidueGenerator_lift_coprime_ideal
    (hlift : Submodule.Quotient.mk (p := fractionalResidueDenominator m I)
      ⟨β, hβ⟩ = z) :
    ∃ b : Ideal R,
      (b : FractionalIdeal R⁰ K) = fractionalResidueLiftIdeal I β ∧
      b ≠ ⊥ ∧ m ⊔ b = ⊤ ∧
      FractionalIdeal.spanSingleton R⁰ β = (b : FractionalIdeal R⁰ K) * I := by
  obtain ⟨_, _, hbne, hble, hsum⟩ :=
    fractionalResidueGenerator_lift_properties m I hm hm1 hI z hz β hβ hlift
  obtain ⟨b, hb⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hble
  refine ⟨b, hb, ?_, ?_, ?_⟩
  · intro hzero
    apply hbne
    simp_all [hb]
  · apply FractionalIdeal.coeIdeal_injective (K := K)
    simp_all
  · simp_all [hb, fractionalResidueLiftIdeal, mul_assoc]

end

end DedekindZetaZeroFree.Hecke
