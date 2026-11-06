/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.QuadraticInvolution
public import CCDN.ClassGroup.QuadraticObstructionFibers
import CCDN.ClassGroup.AmbiguousIdealRelativeNorm
import CCDN.ClassGroup.FractionalIdealConjugation
import CCDN.ClassGroup.QuadraticNormConjugation

/-! A cardinal bound for fixed two-torsion classes in terms of
strongly ambiguous classes and the unit-norm quotient. This is
the obstruction-fiber part of genus theory; the ramified-ideal estimate
for the strongly ambiguous subgroup is a separate step. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
open scoped NumberField nonZeroDivisors

variable (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K]

/-- The two-torsion subgroup of the strongly ambiguous subgroup. -/
abbrev stronglyAmbiguousTwoTorsion (σ : K ≃ₐ[F] K) :=
  (powMonoidHom 2 : stronglyAmbiguousClassGroup F K σ →*
    stronglyAmbiguousClassGroup F K σ).ker

/-- The quadratic two-torsion count is reduced to the strongly
ambiguous subgroup, with a proved degree-only unit factor. -/
theorem classGroupTwoTorsionCard_le_stronglyAmbiguous
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) :
    classGroupTwoTorsionCard K ≤
      (Nat.card (stronglyAmbiguousTwoTorsion F K σ) * 2 ^ Module.finrank ℚ F) ^ 2 := by
  let G := fixedClassGroupTwoTorsion K σ.toRingEquiv
  let emb : G →* ClassGroup (𝓞 K) :=
    (classGroupTwoTorsion K).subtype.comp G.subtype
  let S := (stronglyAmbiguousClassGroup F K σ).comap emb
  let := quadraticUnitNormQuotient_finite F K hd
  choose I hI using fun c : G => ClassGroup.mk0_surjective c.val.val
  choose x y u hx hy hxy hu using fun c : G =>
    ambiguous_numberField_ideal_norm_unit F K σ (I c)
      (by rw [hI c]; exact (mem_fixedClassGroupTwoTorsion K σ.toRingEquiv c.val).mp c.property)
  let o : G → quadraticUnitNormQuotient F K := fun c => QuotientGroup.mk (u c)
  have ho (c e : G) (hce : o c = o e) : c / e ∈ S := by
    change c.val.val / e.val.val ∈ stronglyAmbiguousClassGroup F K σ
    rw [← hI c, ← hI e, ← ClassGroup.mk_mk0 K (I c), ← ClassGroup.mk_mk0 K (I e)]
    have hcomp (d : G) := integral_ideal_scalar_fractional_comparison (K := K)
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv (I d) (x d) (y d) (hx d) (hy d) (hxy d)
    have hnorm (d : G) : Algebra.norm F
        ((Units.mk0 (y d : K) (RingOfIntegers.coe_ne_zero_iff.mpr (hy d)) /
          Units.mk0 (x d : K) (RingOfIntegers.coe_ne_zero_iff.mpr (hx d)) : Kˣ) : K) =
        ((u d : 𝓞 F) : F) := by
      simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      change Algebra.norm F ((y d : K) * (x d : K)⁻¹) = _
      simpa only [div_eq_mul_inv] using hu d
    exact equal_unit_obstructions_stronglyAmbiguous F K hd σ hσ
      (FractionalIdeal.mk0 K (I c)) (FractionalIdeal.mk0 K (I e)) _ _ (u c) (u e)
      (hcomp c) (hcomp e) (hnorm c) (hnorm e) hce
  let r : G ⧸ S → G := fun x => Classical.choose (QuotientGroup.mk_surjective x)
  have hr (x : G ⧸ S) : QuotientGroup.mk (r x) = x :=
    Classical.choose_spec (QuotientGroup.mk_surjective x)
  have hinj : Function.Injective (fun x : G ⧸ S => o (r x)) := fun x y h => by
    rw [← hr x, ← hr y]
    exact div_eq_one.mp (by rw [← QuotientGroup.mk_div]; exact (QuotientGroup.eq_one_iff _).mpr (ho _ _ h))
  have hc : Nat.card G ≤ Nat.card S * Nat.card (quadraticUnitNormQuotient F K) := by
    rw [← S.card_mul_index]
    exact Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective _ hinj)
  let incl : S → stronglyAmbiguousTwoTorsion F K σ := fun c =>
    ⟨⟨c.val.val.val, c.property⟩, Subtype.ext c.val.val.property⟩
  have hincl : Function.Injective incl := fun c e h =>
    Subtype.ext (Subtype.ext (Subtype.ext
      (congrArg (fun x : stronglyAmbiguousTwoTorsion F K σ => x.val.val) h)))
  have hcard : Nat.card G ≤ Nat.card (stronglyAmbiguousTwoTorsion F K σ) * 2 ^ Module.finrank ℚ F :=
    (hc.trans (Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective incl hincl))).trans
      (Nat.mul_le_mul_left _ (quadraticUnitNormQuotient_card_le_degree F K hd))
  exact (classGroupTwoTorsionCard_le_fixed_square K σ.toRingEquiv
    (quadratic_automorphism_involutive F K hd σ)).trans (Nat.pow_le_pow_left hcard 2)

end
end CCDN
