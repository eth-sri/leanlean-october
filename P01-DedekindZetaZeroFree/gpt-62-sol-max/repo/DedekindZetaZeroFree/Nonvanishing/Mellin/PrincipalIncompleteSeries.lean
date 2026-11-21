module

public import DedekindZetaZeroFree.LFunctions.Dedekind.FinitePrimeDeletion
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.SeparatedHeckeFactors
public import DedekindZetaZeroFree.Moments.Probes.PrincipalThetaContext
public import DedekindZetaZeroFree.Nonvanishing.Mellin.NormalizedProbeArithmeticData

public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.PrincipalMellin.ActualRecipe

variable {F : Type} [Field F] [NumberField F] {S : SArithmeticData F}
  {η : RayClassCharacter F S.modulus}

theorem L_eq_zeta (R : ActualRecipe S η) (s : ℂ) (hs : 1 < s.re) :
    R.L s = InitialSeparatedEuler.zetaS R.A s := by
  let W : Ideal (𝓞 F) → ℂ := fun I => R.target I * (Ideal.absNorm I : ℂ) ^ (-s)
  have hWmul (a b : Ideal (𝓞 F)) : W (a * b) = W a * W b := by
    dsimp [W]
    rw [R.target.map_mul', map_mul Ideal.absNorm, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have hdel := finite_prime_delete_hasSum hWmul (R.continuation.series s hs) R.A.Sf
  let g : Ideal (𝓞 F) → ℂ := fun I => if ∃ v ∈ R.A.Sf, I ≤ v.asIdeal then 0 else W I
  have hmask (I : NonzeroIdeal F) :
      I.val ⊔ R.A.cS = ⊤ ↔ ¬ ∃ v ∈ R.A.Sf, I.val ≤ v.asIdeal := by
    rw [R.A.exterior_iff I]
    exact ⟨fun h ⟨v, hv, hle⟩ => v.isMaximal.ne_top
      (top_unique ((h v hv) ▸ sup_le hle le_rfl)),
      fun h v hv => by
        by_contra hn
        exact h ⟨v, hv, (v.isMaximal.eq_of_le hn le_sup_right).symm ▸ le_sup_left⟩⟩
  have hg : Function.support g ⊆ {I | I ≠ ⊥ ∧ I ⊔ R.A.cS = ⊤} := by
    intro I hI
    have hi : I ≠ ⊥ := by
      rintro rfl
      exact hI (by simp [g, W, (R.target.eq_zero_iff' ⊥).mpr (Or.inl rfl)])
    exact ⟨hi, (hmask ⟨I, hi⟩).mpr fun h => hI (by simp [g, h])⟩
  have hext := (hasSum_subtype_iff_of_support_subset hg).mpr hdel
  have heq (I : R.A.Exterior) : (Ideal.absNorm I.val : ℂ) ^ (-s) = g I.val := by
    have hn := (hmask ⟨I.val, I.property.1⟩).mp I.property.2
    have hη := R.probe.principal I.val I.property.1
      (PrincipalProbeConstruction.Inputs.exterior_coprime R.A I)
    simp [g, hn, W, hη]
  have hsum : HasSum (fun I : R.A.Exterior => (Ideal.absNorm I.val : ℂ) ^ (-s)) _ :=
    hext.congr_fun heq
  unfold InitialSeparatedEuler.zetaS
  rw [hsum.tsum_eq]
  unfold L comparisonPrincipalIncompleteL
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  have hq : 0 < idealNorm v.asIdeal := by
    change (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)
    exact_mod_cast Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  have hp : (idealNorm v.asIdeal : ℂ) ^ (-s) = comparisonRealPower (idealNorm v.asIdeal) (-s) := by
    rw [comparisonRealPower, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'),
      Complex.ofReal_log hq.le, mul_comm]
  rw [← hp]
  simp only [W, idealNorm, Complex.ofReal_natCast]

end DedekindZetaZeroFree.PrincipalMellin.ActualRecipe
