module

public import OAI.NumberTheory.DirichletL.Hecke.MaskDescent

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFixedRowMask
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge

theorem row_mask_mul (η : Character) (m r A z n : HeckeFamily.O)
    (hmLam : goodLambda ∣ m) (hm2 : (2:HeckeFamily.O) ∣ m) :
    rowTwist (elementHom η) (m*r) 1 (A*z) n =
      if IsCoprime n r then rowTwist (elementHom η) m 1 (A*z) n else 0 := by
  by_cases hs : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ _ _ _ _ hs,
      rowTwist_extract_sixth_mask _ _ _ _ _ hs]
    change elementHom η n * (if IsCoprime (m*r) n then (1:ℂ) else 0) * _ = _
    rw [IsCoprime.mul_left_iff]
    by_cases hm : IsCoprime m n <;> by_cases hr : IsCoprime n r <;>
      simp [coprimalityMask, hr, show IsCoprime r n ↔ IsCoprime n r from isCoprime_comm]
  · rw [rowTwist_zero_of_not_supported _ _ _ _ _
        (hmLam.trans (dvd_mul_right _ _)) (hm2.trans (dvd_mul_right _ _)) hs,
      rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hs]
    simp

theorem fixedInducingRow_mul_mask_iff (η : Character) (Q : Ideal HeckeFamily.O)
    (m r A z : HeckeFamily.O) (hm : m ≠ 0) (hr : r ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:HeckeFamily.O) ∣ m) :
    FixedInducingRow η Q (m*r) A z ↔ FixedInducingRow η Q m A z := by
  obtain ⟨χ,hχ⟩ := exists_row_character η m 1 (A*z) hm one_ne_zero
    (by positivity) hmLam hm2
  obtain ⟨χ',hχ'⟩ := exists_row_character η (m*r) 1 (A*z) (by positivity)
    one_ne_zero (by positivity) (hmLam.trans (by simp))
      (hm2.trans (by simp))
  have hmask (n : HeckeFamily.O) : elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0 := by
    rw [hχ' n,hχ n,row_mask_mul η m r A z n hmLam hm2]
  have transport (ρ : Character) (mask : HeckeFamily.O)
      (hρ : ∀ n,elementCoeff ρ n=rowTwist (elementHom η) mask 1 (A*z) n) :
      FixedInducingRow η Q mask A z ↔
        ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
          Q ≤ ψ.modulus ∧ InducedBy ρ ψ := by
    constructor
    · rintro ⟨ρ₀,ψ,hprim,hind,hQ,hρ₀⟩
      exact ⟨ψ,hprim,hQ,CenteredMomentHeckeVolume.inducedBy_of_elementCoeff_eq
        ρ₀ ρ ψ (by grind) hind⟩
    · rintro ⟨ψ,hprim,hQ,hind⟩
      exact ⟨ρ,ψ,hprim,hind,hQ,hρ⟩
  rw [transport χ' (m*r) hχ',transport χ m hχ]
  exact HeckeMaskDescent.fixed_inducing_mask_iff χ χ' r hr hmask Q
end SevenEighths.CenteredMomentFixedRowMask

end

end OAI
