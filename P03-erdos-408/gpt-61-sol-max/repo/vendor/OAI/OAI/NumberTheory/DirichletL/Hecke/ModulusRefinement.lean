module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Hecke.IdealOperations
public import OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFamily
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def Character.refineModulus (η : Character) (M ) (hM : M ≠ ⊥)
    (hle : M ≤ η.modulus)  :=
  Character.ofResidue M hM (ResidueCharacter.inflate hle η.residue)
    (ResidueCharacter.inflate_global_units hle η.residue η.unit_trivial)

theorem elementCoeff_refineModulus  η   M   hM 
     hle   n  :
    elementCoeff (η.refineModulus M hM hle) n =
      if IsUnit (Ideal.Quotient.mk M n) then elementCoeff η n else 0 :=
  ResidueCharacter.inflate_mk hle η.residue n

theorem idealCoeff_refineModulus  η   M   hM 
     hle   I  :
    idealCoeff (η.refineModulus M hM hle) I =
      if IsCoprime I M then idealCoeff η I else 0 :=
  IdealCharacter.ofResidue_source_mask M η.modulus _ _ _ _
    (ResidueCharacter.inflate_mk hle η.residue) I

theorem idealCoeff_source_mask  η   I  :
    idealCoeff η I = if IsCoprime I η.modulus then idealCoeff η I else 0 := by
  apply IdealCharacter.ofResidue_source_mask η.modulus η.modulus η.residue η.residue
    η.unit_trivial η.unit_trivial _ I
  intro n
  split_ifs with hn
  · rfl
  · exact MulChar.map_nonunit _ hn

def Character.excludePrimes (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P)  :=
  η.refineModulus (η.modulus * ∏ P ∈ S, P)
    (mul_ne_zero η.modulus_ne_bot (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)))
    Ideal.mul_le_left

theorem idealCoeff_excludePrimes  η   S 
     hS   I  :
    idealCoeff (η.excludePrimes S hS) I =
      if ∀ P ∈ S, IsCoprime I P then idealCoeff η I else 0 := by
  rw [Character.excludePrimes, idealCoeff_refineModulus, IsCoprime.mul_right_iff,
    IsCoprime.prod_right_iff]
  grind [IsCoprime, idealCoeff, idealCoeff_source_mask]

theorem excludePrimes_mask  η   S 
     hS   I  :
    idealCoeff (η.excludePrimes S hS) I =
      if IsCoprime I (η.excludePrimes S hS).modulus then idealCoeff η I else 0 :=
  idealCoeff_refineModulus η _ _ _ I

end SevenEighths.HeckeFamily

end

end OAI
