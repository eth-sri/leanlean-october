module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.Residues.ArtinModelEquivalence

@[expose] public section

open scoped NumberField Classical ValuativeRel
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSumCompatibility
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
    {A : SArithmeticData F} {σ : F →+* ℂ}
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
local instance (p : ExteriorPrime A) : ValuativeRel (LocalField p) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F p.val

theorem exterior_tame (p : ExteriorPrime A) :
    ValuativeRel.valuation (LocalField p) (6 : LocalField p) = 1 := (KPHilbert.tame_place_iff F p.val).mpr
    (fun h => exterior_notMem p (A.above_six p.val h))

alias chi_exact_order := intrinsic_chi_order

local instance (p : ExteriorPrime A) : IsNonarchimedeanLocalField (LocalField p) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F p.val

theorem sexticPower_eq_chi_pow (p : ExteriorPrime A) (a : ℤ) :
    A.sexticResiduePowerChar σ (primeIdeal p) a =
      chi (σ := σ) p ^ SArithmeticData.sexticExponent a := by
  simp [chi, SArithmeticData.sexticResiduePowerChar, SArithmeticData.sexticExponent]

section

variable (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ) (hn : n ≠ 0) (a : ℤ)
    (x : Residue C p n)

theorem maskedPower_eq_reduction :
    maskedPower C p n a x =
      (chi (σ := σ) p ^ SArithmeticData.sexticExponent a) (reduction C p n hn x) := by
  unfold maskedPower
  rw [dif_neg hn, ← sexticPower_eq_chi_pow]
  by_cases hx : IsUnit x
  · exact if_pos hx
  · rw [if_neg hx]
    exact (A.sexticResiduePowerChar_nonunit σ (primeIdeal p) a _
      (fun h => hx ((reduction_isUnit C p n hn x).mp h))).symm

include hn in
theorem maskedPower_nonunit
    (hx : ¬ IsUnit x) : maskedPower C p n a x = 0 := by
  simp [maskedPower, hn, hx]

end

theorem maskedPower_zero_depth (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (a : ℤ) (x : Residue C p 0) :
    maskedPower C p 0 a x = 1 := by
  simp [maskedPower]

end DedekindZetaZeroFree.LocalFiniteSumCompatibility

end
