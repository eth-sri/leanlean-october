module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SixthRootAlignment

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.NumericalSpherical
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain UniqueFactorizationMonoid
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]

local notation "KPFinitePlace" F => HeightOneSpectrum (𝓞 F)

private lemma ord_mul (q : KPFinitePlace F) (x y : Fˣ) :
    ThetaBranch.order q (x * y) = ThetaBranch.order q x + ThetaBranch.order q y := by apply @DedekindZetaZeroFree.ThetaBranch.ord_mul <;> assumption

lemma ord_pow (q : KPFinitePlace F) (x : Fˣ) (n : ℕ) :
    ThetaBranch.order q (x ^ n) = n * ThetaBranch.order q x := by apply @DedekindZetaZeroFree.ThetaBranch.ExteriorFrequencyBranchCoordinates.pow_order <;> assumption

lemma ord_prod {ι : Type*} (q : KPFinitePlace F) (T : Finset ι) (x : ι → Fˣ) :
    ThetaBranch.order q (∏ i ∈ T, x i) = ∑ i ∈ T, ThetaBranch.order q (x i) := by
  induction T using Finset.induction_on with
  | empty => simp [ThetaBranch.order]
  | @insert i T hi ih => rw [Finset.prod_insert hi, ord_mul, ih, Finset.sum_insert hi]

lemma prime_ord (A : SArithmeticData F) (G : ThetaBranch.AllowedRecipe A)
    (p q : ThetaBranch.ExteriorPrime A) :
    ThetaBranch.order p.val (G.generator (ThetaBranch.primeIdeal A q)) =
      if q = p then 1 else 0 := by
  rw [ThetaBranch.generator_order]
  by_cases h : q = p
  · subst q
    simp [ThetaBranch.primeIdeal, idealPrimeExponent,
      normalizedFactors_irreducible p.val.irreducible]
  · have hI : p.val.asIdeal ≠ q.val.asIdeal := fun he => h
      (Subtype.ext (HeightOneSpectrum.ext he.symm))
    simp [h, ThetaBranch.primeIdeal, idealPrimeExponent,
      normalizedFactors_irreducible q.val.irreducible, hI]

private alias symbol_six := DedekindZetaZeroFree.ThetaPhaseSeparation.QuadraticPhaseSeparation.symbol_six

section

variable (A : SArithmeticData F) (G : ThetaBranch.AllowedRecipe A) (σ : F →+* ℂ)
    (ψ : ∀ p : ThetaBranch.ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)

theorem spherical_table
    (p : ThetaBranch.ExteriorPrime A) (x : Fˣ) (d k : ℕ) (hd : d = 0 ∨ d = 1)
    (hx : ThetaBranch.order p.val x = (d + 3 * k : ℕ)) :
    ThetaBranch.sphericalFactor A G σ ψ p x =
      (idealNorm p.val.asIdeal : ℂ) ^ (-(k : ℤ)) *
      (Real.sqrt (idealNorm p.val.asIdeal) : ℂ)⁻¹ ^ d *
      ThetaBranch.gaussTwo A σ ψ p ^ d *
      ThetaBranch.symbol A σ p (ThetaBranch.localUnit A G p x) ^ (2 * d) := by
  have h6 := symbol_six A σ p (ThetaBranch.localUnit A G p x)
    (ThetaBranch.localUnit_order A G p x)
  have hcard : (Fintype.card (DHCubic.Residue F p.val) : ℝ) = idealNorm p.val.asIdeal := by
    simp only [idealNorm, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hcardC : (Fintype.card (DHCubic.Residue F p.val) : ℂ) = (idealNorm p.val.asIdeal : ℂ) := by
    exact_mod_cast hcard
  rw [ThetaBranch.sphericalFactor, hx]
  rcases hd with rfl | rfl
  · have he : (2 : ℤ) * (0 + 3 * (k : ℤ)) = (6 * k : ℕ) := by push_cast; ring
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, zero_add,
      he, zpow_natCast, pow_mul, h6, one_pow, mul_one, pow_zero]
    simp only [sexticSphericalCoefficient]
    rw [if_neg (by omega), if_pos (by omega), hcardC]
    rw [show (3 * (k : ℤ)) / 3 = k by omega,
      show (2 : ℤ) * (3 * (k : ℤ)) = (6 * k : ℕ) by push_cast; ring,
      zpow_natCast, pow_mul, h6, one_pow, mul_one]
  · have he : (2 : ℤ) * (1 + 3 * (k : ℤ)) = (2 + 6 * k : ℕ) := by push_cast; ring
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, he,
      zpow_natCast, pow_add, pow_mul, h6, one_pow, mul_one, pow_one]
    simp only [sexticSphericalCoefficient, ThetaBranch.gaussTwo]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), hcard, hcardC,
      show (1 + 3 * (k : ℤ)) / 3 = k by omega]
    rw [show (2 + 6 * (k : ℤ)) = (2 + 6 * k : ℕ) by push_cast; ring,
      zpow_natCast, pow_add, pow_mul, h6, one_pow, mul_one]

theorem sphericalFactor_generatorProduct
    (P : Finset (ThetaBranch.ExteriorPrime A)) (d k : ThetaBranch.ExteriorPrime A → ℕ)
    (p : ThetaBranch.ExteriorPrime A) (hp : p ∈ P) (hd : d p = 0 ∨ d p = 1) :
    let b := ∏ q ∈ P, G.generator (ThetaBranch.primeIdeal A q) ^ (d q + 3 * k q)
    ThetaBranch.sphericalFactor A G σ ψ p b =
      (idealNorm p.val.asIdeal : ℂ) ^ (-(k p : ℤ)) *
      (Real.sqrt (idealNorm p.val.asIdeal) : ℂ)⁻¹ ^ d p *
      ThetaBranch.gaussTwo A σ ψ p ^ d p *
      ThetaBranch.symbol A σ p
        (∏ q ∈ P.erase p, G.generator (ThetaBranch.primeIdeal A q) ^ (d q + 3 * k q)) ^ (2 * d p) := by
  dsimp only
  let b := ∏ q ∈ P, G.generator (ThetaBranch.primeIdeal A q) ^ (d q + 3 * k q)
  have hx : ThetaBranch.order p.val b = (d p + 3 * k p : ℕ) := by
    dsimp [b]
    rw [ord_prod]
    simp_rw [ord_pow, prime_ord]
    simp [hp]
  rw [spherical_table A G σ ψ p b (d p) (k p) hd hx]
  congr 2
  unfold ThetaBranch.localUnit
  rw [hx, zpow_natCast]
  congr 1
  dsimp [b]
  rw [← (Finset.prod_erase_mul P (fun q => G.generator (ThetaBranch.primeIdeal A q) ^
    (d q + 3 * k q)) hp)]
  exact mul_div_cancel_right _ _

end

private alias char_one := DedekindZetaZeroFree.NormalizedProbe.PrincipalExteriorCharacter.char_one

private lemma symbol_integral (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ThetaBranch.ExteriorPrime A) (x : Fˣ) (t : A.R) (hx : (x : F) = (t : F)) :
    ThetaBranch.symbol A σ p x = σ (A.sexticResidue (ThetaBranch.primeIdeal A p) t) := by
  have he : x = ThetaReflectionData.rowUnit A ⟨t, fun h => x.ne_zero (hx.trans (by simp [h]))⟩ := Units.ext hx
  rw [he, NormalizedProbe.principal_prime_symbol_eq_sexticResiduePowerChar, char_one]

theorem generatorProduct_phase (A : SArithmeticData F) (G : ThetaBranch.AllowedRecipe A)
    (σ : F →+* ℂ) (P : Finset (ThetaBranch.ExteriorPrime A))
    (d k : ThetaBranch.ExteriorPrime A → ℕ)
    (r : ThetaBranch.ExteriorPrime A → A.R)
    (hr : ∀ q, (G.generator (ThetaBranch.primeIdeal A q) : F) = (r q : F))
    (p : ThetaBranch.ExteriorPrime A) :
    ThetaBranch.symbol A σ p
      (∏ q ∈ P.erase p, G.generator (ThetaBranch.primeIdeal A q) ^ (d q + 3 * k q)) ^ (2 * d p) =
      ∏ q ∈ P.erase p, σ (A.sexticResidue (ThetaBranch.primeIdeal A p) (r q)) ^ (2 * d p * d q) := by
  have hval : ((∏ q ∈ P.erase p, G.generator (ThetaBranch.primeIdeal A q) ^
      (d q + 3 * k q) : Fˣ) : F) = ((∏ q ∈ P.erase p, r q ^ (d q + 3 * k q) : A.R) : F) := by
    rw [Units.coe_prod]
    change _ = A.R.subtype (∏ q ∈ P.erase p, r q ^ (d q + 3 * k q))
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro q hq
    simp only [Units.val_pow_eq_pow_val, map_pow, hr q]
    rfl
  rw [symbol_integral A σ p _ _ hval]
  have hprod (T : Finset (ThetaBranch.ExteriorPrime A)) :
      σ (A.sexticResidue (ThetaBranch.primeIdeal A p) (∏ q ∈ T, r q ^ (d q + 3 * k q))) =
        ∏ q ∈ T, σ (A.sexticResidue (ThetaBranch.primeIdeal A p) (r q)) ^ (d q + 3 * k q) := by
    unfold SArithmeticData.sexticResidue SArithmeticData.residueValue
    simp
  rw [hprod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro q hq
  have hne := (Finset.mem_erase.mp hq).1
  have horder : ThetaBranch.order p.val (G.generator (ThetaBranch.primeIdeal A q)) = 0 := by
    rw [ThetaBranch.generator_order]
    have hI : p.val.asIdeal ≠ q.val.asIdeal := fun he => hne (Subtype.ext (HeightOneSpectrum.ext he.symm))
    simp [ThetaBranch.primeIdeal, idealPrimeExponent, normalizedFactors_irreducible q.val.irreducible, hI]
  have h6 : σ (A.sexticResidue (ThetaBranch.primeIdeal A p) (r q)) ^ 6 = 1 := by
    rw [← symbol_integral A σ p _ _ (hr q)]
    exact symbol_six A σ p _ horder
  rw [← pow_mul, show (d q + 3 * k q) * (2 * d p) =
    2 * d p * d q + 6 * (k q * d p) by ring, pow_add,
    pow_mul _ 6 (k q * d p), h6, one_pow, mul_one]

end DedekindZetaZeroFree.ExteriorWhittakerValues.NumericalSpherical

end
