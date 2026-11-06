module

public import OAI.NumberTheory.DirichletL.Moments.Canonical
public import OAI.NumberTheory.DirichletL.ResidueCharacter

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeLocalRamification
open CenteredMomentCorrelation CenteredMomentCanonical
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O

theorem primePowerCharacter_eq_one_iff (P : Ideal O) [P.IsMaximal]
    {c : ℕ} (hc : 1 ≤ c) (χ : MulChar (O ⧸ P) ℂ) :
    primePowerCharacter P hc χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    apply MulChar.ext
    intro u
    obtain ⟨x,hx⟩ := primePowerReduction_surjective P hc (u : O ⧸ P)
    have hux : IsUnit x := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      apply (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
      change Ideal.Quotient.mk P a = (u : O ⧸ P) at hx
      rw [hx]
      exact u.isUnit
    have heq := congrArg (fun f : MulChar (O ⧸ P^c) ℂ => f x) h
    rw [primePowerCharacter_apply, hx, MulChar.one_apply hux] at heq
    simpa only [MulChar.one_apply u.isUnit] using heq
  · rintro rfl
    apply MulChar.ext
    intro u
    rw [primePowerCharacter_apply, MulChar.one_apply u.isUnit,
      MulChar.one_apply (u.isUnit.map (primePowerReduction P hc))]

theorem canonicalPrimePowerCharacter_eq_one_iff (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) : canonicalPrimePowerCharacter P hg hc = 1 ↔ 6 ∣ c := by
  rw [canonicalPrimePowerCharacter, primePowerCharacter_eq_one_iff,
    ← orderOf_dvd_iff_pow_eq_one, actualSextic_order_six P hg hchar]

end SevenEighths.HeckeLocalRamification

end

end OAI
