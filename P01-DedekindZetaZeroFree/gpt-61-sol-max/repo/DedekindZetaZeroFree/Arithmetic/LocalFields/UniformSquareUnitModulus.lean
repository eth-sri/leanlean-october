module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData

@[expose] public section


namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

def squareUnitOrdTwo (v : HeightOneSpectrum (𝓞 F))  :=
  ((IsDiscreteValuationRing.addVal (v.adicCompletionIntegers F)
    (2 : v.adicCompletionIntegers F)).toNat : ℤ)

def squareUnitDepth (v : HeightOneSpectrum (𝓞 F))  :=
  2 * (squareUnitOrdTwo v).toNat + 1

theorem squareUnitDepth_bounds (v : HeightOneSpectrum (𝓞 F)) :
    1 ≤ squareUnitDepth v ∧ 2 * squareUnitOrdTwo v < (squareUnitDepth v : ℤ) := by
  dsimp [squareUnitDepth]
  omega

section
variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (r : HeightOneSpectrum (𝓞 F) → ℕ)
include Sf r
def squareUnitModulus    :=
  ∏ v ∈ Sf, v.asIdeal ^ r v

theorem squareUnitModulus_ne_bot   : squareUnitModulus Sf r ≠ ⊥ := by
  rw [squareUnitModulus]
  rw [show (⊥ : Ideal (𝓞 F)) = 0 from rfl]
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ v.prime.ne_zero)
end


private theorem prime_dvd_prime_pow_iff {p q : Ideal (𝓞 F)} (hp : Prime p) (hq : Prime q)
    (n : ℕ) : p ∣ q ^ n ↔ p = q ∧ 1 ≤ n := by
  have hp'  := Ideal.isPrime_of_prime hp
  have hq'  := Ideal.isPrime_of_prime hq
  constructor
  · intro h
    have hn : n ≠ 0 := by
      rintro rfl
      have h1  := Ideal.dvd_iff_le.mp (by simpa using h)
      apply hp'.ne_top <;> aesop
    have hpq : p ∣ q := hp.dvd_of_dvd_pow h
    exact ⟨(hq'.isMaximal hq.ne_zero |>.eq_of_le hp'.ne_top (Ideal.dvd_iff_le.mp hpq)).symm,
      Nat.one_le_iff_ne_zero.mpr hn⟩
  · intro h
    rw [h.1]
    apply dvd_pow_self <;> aesop

section
variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (r : HeightOneSpectrum (𝓞 F) → ℕ)
    (hr : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ Sf → 1 ≤ r v)
include Sf r hr
theorem squareUnitModulus_support  
    (v : HeightOneSpectrum (𝓞 F)) :
    squareUnitModulus Sf r ≤ v.asIdeal ↔ v ∈ Sf := by
  rw [← Ideal.dvd_iff_le, squareUnitModulus, Prime.dvd_finset_prod_iff v.prime]
  constructor
  · rintro ⟨w, hw, hdvd⟩
    obtain ⟨hvw, -⟩ := (prime_dvd_prime_pow_iff v.prime w.prime (r w)).mp hdvd
    have hv  := HeightOneSpectrum.ext hvw
    rwa [hv]
  · intro hv
    exact ⟨v, hv, (prime_dvd_prime_pow_iff v.prime v.prime (r v)).mpr ⟨rfl, hr v hv⟩⟩

theorem squareUnitModulus_primeSupport   :
    idealPrimeSupport (squareUnitModulus Sf r) = Sf.image HeightOneSpectrum.asIdeal := by
  have hne  := squareUnitModulus_ne_bot Sf r
  ext q
  rw [idealPrimeSupport, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hne,
    Finset.mem_image]
  constructor
  · rintro ⟨hq, hle⟩
    have hq0 : q ≠ ⊥ := fun h => hne (le_bot_iff.mp (h ▸ hle))
    exact ⟨⟨q, hq, hq0⟩,
      (squareUnitModulus_support Sf r hr ⟨q, hq, hq0⟩).mp hle, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, (squareUnitModulus_support Sf r hr v).mpr hv⟩
end


def uniformSquareUnitModulus (Sf : Finset (HeightOneSpectrum (𝓞 F)))  :=
  squareUnitModulus Sf squareUnitDepth

theorem uniformSquareUnitModulus_spec (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    uniformSquareUnitModulus Sf ≠ ⊥ ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        uniformSquareUnitModulus Sf ≤ v.asIdeal ↔ v ∈ Sf) ∧
      idealPrimeSupport (uniformSquareUnitModulus Sf) = Sf.image HeightOneSpectrum.asIdeal := ⟨squareUnitModulus_ne_bot Sf squareUnitDepth,
    fun v => squareUnitModulus_support Sf squareUnitDepth
      (fun w _ => (squareUnitDepth_bounds w).1) v,
    squareUnitModulus_primeSupport Sf squareUnitDepth
      (fun w _ => (squareUnitDepth_bounds w).1)⟩

end
end DedekindZetaZeroFree
