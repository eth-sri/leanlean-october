module

public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Frobenius

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Order of arithmetic Frobenius at an unramified prime

For a prime `w` of `L` above `v` of `K`, unramifiedness kills the inertia
subgroup.  The arithmetic Frobenius therefore has order equal to the residue
degree at `w`.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain
open scoped Pointwise

universe u v

/-- At an unramified prime, the order of arithmetic Frobenius is the inertia
(residue) degree. -/
theorem orderOf_arithmeticFrobeniusAt_eq_inertiaDegree
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    orderOf (arithmeticFrobeniusAt (K := K) w) =
      w.asIdeal.inertiaDeg (𝓞 K) := by
  classical
  let P := v.asIdeal
  let Q := w.asIdeal
  let G := L ≃ₐ[K] L
  let g : G := arithmeticFrobeniusAt w
  let := hw
  let := hunram
  let := Ideal.Quotient.field P
  let := Ideal.Quotient.field Q
  let :=
    Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let :=
    Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  let : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hF : IsArithFrobAt (𝓞 K) g Q := by
    exact IsArithFrobAt.arithFrobAt (𝓞 K) G Q
  let gs : MulAction.stabilizer G Q := ⟨g, hF.mem_stabilizer⟩
  have hImage :
      Ideal.Quotient.stabilizerHom Q P G gs =
        FiniteField.frobeniusAlgEquivOfAlgebraic
          ((𝓞 K) ⧸ P) ((𝓞 L) ⧸ Q) := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.stabilizerHom_apply]
    simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    have h := hF.mk_apply y
    rw [hw.over.symm, Nat.card_eq_fintype_card] at h
    exact h
  have hImageOrder :
      orderOf (Ideal.Quotient.stabilizerHom Q P G gs) =
        Q.inertiaDeg (𝓞 K) := by
    rw [hImage, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
    exact (Ideal.inertiaDeg_eq_of_isMaximal P Q).symm
  have hCard : Nat.card (MulAction.stabilizer G Q) =
      Q.inertiaDeg (𝓞 K) := by
    rw [Ideal.card_stabilizer_eq P Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx P Q G,
      Ideal.inertiaDegIn_eq_inertiaDeg P Q G,
      Ideal.ramificationIdx_eq_one Q (𝓞 K), one_mul]
  refine (Subgroup.orderOf_coe gs).trans
    (Nat.dvd_antisymm ?_ ?_)
  · rw [← hCard]
    exact orderOf_dvd_natCard gs
  · rw [← hImageOrder]
    exact orderOf_map_dvd (Ideal.Quotient.stabilizerHom Q P G) gs

end ClassFieldTheory

end
