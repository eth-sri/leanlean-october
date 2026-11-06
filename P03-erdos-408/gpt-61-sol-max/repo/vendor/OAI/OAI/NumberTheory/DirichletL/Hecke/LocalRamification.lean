module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.Canonical
public import OAI.NumberTheory.DirichletL.ResidueCharacter

@[expose] public section

namespace OAI


open scoped Classical BigOperators
namespace SevenEighths.HeckeLocalRamification
open CenteredMomentCorrelation CenteredMomentCanonical
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O

section
variable (P : Ideal O) [P.IsMaximal]

theorem primePowerCharacter_eq_one_iff    
    {c : ℕ} (hc : 1 ≤ c)  χ  :
    primePowerCharacter P hc χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    apply MulChar.ext
    intro u
    obtain ⟨x,hx⟩ := primePowerReduction_surjective P hc (u : O ⧸ P)
    have hux : IsUnit x := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      apply (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
      solve_by_elim
    have heq := congrArg (fun f : MulChar (O ⧸ P^c) ℂ => f x) h
    rw [primePowerCharacter_apply, hx, MulChar.one_apply hux] at heq
    simpa only [MulChar.one_apply u.isUnit] using heq
  · rintro rfl
    apply MulChar.ext
    intro u
    rw [primePowerCharacter_apply, MulChar.one_apply u.isUnit,
      MulChar.one_apply (u.isUnit.map (primePowerReduction P hc))]

theorem canonicalPrimePowerCharacter_eq_one_iff    
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) : canonicalPrimePowerCharacter P hg hc = 1 ↔ 6 ∣ c := by
  rw [canonicalPrimePowerCharacter, primePowerCharacter_eq_one_iff,
    ← orderOf_dvd_iff_pow_eq_one, actualSextic_order_six P hg hchar]

end

end SevenEighths.HeckeLocalRamification



end OAI
