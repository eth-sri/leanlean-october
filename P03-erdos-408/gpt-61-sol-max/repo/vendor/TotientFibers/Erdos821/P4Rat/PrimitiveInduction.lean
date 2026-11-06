module
public import Mathlib.Tactic

public import Erdos821.Blueprint.Analytic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators Classical

namespace Erdos821.P4Rat

open Blueprint.Analytic

/-- Every character mod r is represented by its primitive inducing character
in the packet of conductors at most Q, at all integers coprime to r. -/
def PrimitiveInductionTask  :=
  ∀ (Q r : ℕ), 1 ≤ r → r ≤ Q → ∀ ψ : DirichletCharacter ℂ r,
    ∃ χ ∈ primitiveCharacters Q, ∀ n : ℕ, Nat.Coprime n r →
      charValue χ n = ψ (n : ZMod r)

section
variable {m n : ℕ} (h : m = n) (χ : DirichletCharacter ℂ n)



lemma ind_apply_cast_nat_helper      
    (k : ℕ) : (h ▸ χ) ((k : ZMod m)) = χ ((k : ZMod n)) := by
  cases h
  rfl

end

theorem PrimitiveInductionTask_proof : PrimitiveInductionTask := by
  intro Q r hr hQr ψ
  have hr_pos : 0 < r := by omega
  have : NeZero r := ⟨by omega⟩
  have hc_pos : 0 < ψ.conductor := Nat.pos_of_ne_zero ψ.conductor_ne_zero
  have hc_dvd : ψ.conductor ∣ r := ψ.conductor_dvd_level
  have hc_le : ψ.conductor ≤ r := Nat.le_of_dvd hr_pos hc_dvd
  have hc_leQ : ψ.conductor ≤ Q := le_trans hc_le hQr
  let qFin : Fin Q := ⟨ψ.conductor - 1, by omega⟩
  have h_eq : qFin.val + 1 = ψ.conductor := by
    grind
  let χ₂ : DirichletCharacter ℂ (qFin.val + 1) :=
    h_eq ▸ ψ.primitiveCharacter
  have hPrim0 : ψ.primitiveCharacter.IsPrimitive := ψ.primitiveCharacter_isPrimitive
  have hPrim : χ₂.IsPrimitive := by
    grind
  let χ : CharacterIndex Q := ⟨qFin, χ₂⟩
  have hmem : χ ∈ primitiveCharacters Q := by
    grind [primitiveCharacters]
  refine ⟨χ, hmem, fun n hn => ?_⟩
  show χ₂ ((n : ZMod (qFin.val + 1))) = ψ ((n : ZMod r))
  have hcast : χ₂ ((n : ZMod (qFin.val + 1))) =
      ψ.primitiveCharacter ((n : ZMod ψ.conductor)) :=
    ind_apply_cast_nat_helper h_eq ψ.primitiveCharacter n
  rw [hcast]
  have hInt : ψ.primitiveCharacter (((n : ℤ)) : ZMod ψ.conductor) =
      ψ ((((n : ℤ))) : ZMod r) :=
    ψ.primitiveCharacter_apply_of_isCoprime hn.isCoprime
  simp_all

end Erdos821.P4Rat
