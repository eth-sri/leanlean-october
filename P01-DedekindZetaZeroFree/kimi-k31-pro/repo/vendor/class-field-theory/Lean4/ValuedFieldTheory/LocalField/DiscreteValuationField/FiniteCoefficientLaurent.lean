module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RingHom.Finite

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/











set_option autoImplicit false

/-!
# Coefficient-field descent for Laurent series

This file starts the remaining equal-characteristic descent in the local-field structure classification: a finite coefficient field `k` of characteristic `p` gives a canonical
coefficientwise map from `F_p((X))` to `k((X))`.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace FiniteCoefficientLaurent

open scoped LaurentSeries PowerSeries

section PowerSeriesFinite

variable {R : Type u} {A : Type v} [Field R] [Field A] [Algebra R A]



end PowerSeriesFinite

variable (p : ℕ) (k : Type u) [Fact p.Prime] [Field k] [CharP k p]





/-- Coefficientwise map on power series induced by the prime-field embedding
`ZMod p -> k`. -/
noncomputable def zmodPowerSeriesCoeffMap :
    (ZMod p)⟦X⟧ →+* k⟦X⟧ := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  exact PowerSeries.map (algebraMap (ZMod p) k)

/--
Establishes the identity `zmodPowerSeriesCoeffMap p k (PowerSeries.C a) = PowerSeries.C
((ZMod.castHom (m := p) dvd_rfl k) a)`.
-/
@[simp]
theorem zmodPowerSeriesCoeffMap_C (a : ZMod p) :
    zmodPowerSeriesCoeffMap p k (PowerSeries.C a) =
      PowerSeries.C ((ZMod.castHom (m := p) dvd_rfl k) a) := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  rw [zmodPowerSeriesCoeffMap, PowerSeries.map_C]
  change PowerSeries.C ((algebraMap (ZMod p) k) a) =
    PowerSeries.C ((ZMod.castHom (m := p) dvd_rfl k) a)
  rfl

/-- Establishes the identity `zmodPowerSeriesCoeffMap p k PowerSeries.X = PowerSeries.X`. -/
@[simp]
theorem zmodPowerSeriesCoeffMap_X :
    zmodPowerSeriesCoeffMap p k PowerSeries.X = PowerSeries.X := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  simp [zmodPowerSeriesCoeffMap]





/-- Coefficientwise Laurent-series map induced from `ZMod p -> k`. -/
noncomputable def zmodLaurentCoeffMap :
    (ZMod p)⸨X⸩ →+* k⸨X⸩ := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let φ : ZMod p →+* k := algebraMap (ZMod p) k
  exact
  { toFun := fun f => f.map φ
    map_zero' := by
      change HahnSeries.map (0 : (ZMod p)⸨X⸩) φ.toZeroHom = 0
      exact HahnSeries.map_zero (Γ := ℤ) (R := ZMod p) (S := k) φ.toZeroHom
    map_one' := by
      change HahnSeries.map (1 : (ZMod p)⸨X⸩) φ.toMonoidWithZeroHom = 1
      exact
        HahnSeries.map_one (Γ := ℤ) (R := ZMod p) (S := k)
          φ.toMonoidWithZeroHom
    map_add' := by
      intro x y
      change
        HahnSeries.map (x + y) φ.toAddMonoidHom =
          HahnSeries.map x φ.toAddMonoidHom +
            HahnSeries.map y φ.toAddMonoidHom
      exact
        HahnSeries.map_add (Γ := ℤ) (R := ZMod p) (S := k)
          φ.toAddMonoidHom
    map_mul' := by
      intro x y
      change
        HahnSeries.map (x * y) φ.toNonUnitalRingHom =
          HahnSeries.map x φ.toNonUnitalRingHom *
            HahnSeries.map y φ.toNonUnitalRingHom
      exact
        HahnSeries.map_mul (Γ := ℤ) (R := ZMod p) (S := k)
          φ.toNonUnitalRingHom }

/--
Establishes the identity `(zmodLaurentCoeffMap p k f).coeff n = (ZMod.castHom (m := p) dvd_rfl k)
(f.coeff n)`.
-/
@[simp]
theorem zmodLaurentCoeffMap_coeff (f : (ZMod p)⸨X⸩) (n : ℤ) :
    (zmodLaurentCoeffMap p k f).coeff n =
      (ZMod.castHom (m := p) dvd_rfl k) (f.coeff n) := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  change (HahnSeries.map f (algebraMap (ZMod p) k)).coeff n =
    (ZMod.castHom (m := p) dvd_rfl k) (f.coeff n)
  have hφ :
      algebraMap (ZMod p) k = ZMod.castHom (m := p) dvd_rfl k := rfl
  rw [hφ]
  rfl

/--
Establishes the identity `zmodLaurentCoeffMap p k (HahnSeries.C (Γ := ℤ) a : (ZMod p)⸨X⸩) =
(HahnSeries.C (Γ := ℤ) ((ZMod.castHom (m := p) dvd_rfl k) a) : k⸨X⸩)`.
-/
@[simp]
theorem zmodLaurentCoeffMap_C (a : ZMod p) :
    zmodLaurentCoeffMap p k (HahnSeries.C (Γ := ℤ) a : (ZMod p)⸨X⸩) =
      (HahnSeries.C (Γ := ℤ) ((ZMod.castHom (m := p) dvd_rfl k) a) :
        k⸨X⸩) := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  change
    HahnSeries.map (HahnSeries.C (Γ := ℤ) a : (ZMod p)⸨X⸩)
        (algebraMap (ZMod p) k) =
      (HahnSeries.C (Γ := ℤ) ((ZMod.castHom (m := p) dvd_rfl k) a) :
        k⸨X⸩)
  rw [HahnSeries.map_C]
  change
    HahnSeries.C ((algebraMap (ZMod p) k) a) =
      (HahnSeries.C ((ZMod.castHom (m := p) dvd_rfl k) a) : k⸨X⸩)
  rfl

/--
Establishes the identity `(zmodLaurentCoeffMap p k).comp (algebraMap (ZMod p)⟦X⟧ (ZMod p)⸨X⸩) =
(algebraMap k⟦X⟧ k⸨X⸩).comp (zmodPowerSeriesCoeffMap p k)`.
-/
theorem zmodLaurentCoeffMap_comp_powerSeries :
    (zmodLaurentCoeffMap p k).comp
        (algebraMap (ZMod p)⟦X⟧ (ZMod p)⸨X⸩) =
      (algebraMap k⟦X⟧ k⸨X⸩).comp
        (zmodPowerSeriesCoeffMap p k) := by
  ext f n
  cases n with
  | ofNat n =>
      simp [zmodLaurentCoeffMap, zmodPowerSeriesCoeffMap,
        LaurentSeries.coe_algebraMap, LaurentSeries.coeff_coe_powerSeries,
        PowerSeries.coeff_map]
  | negSucc n =>
      simp [zmodLaurentCoeffMap, zmodPowerSeriesCoeffMap,
        LaurentSeries.coe_algebraMap, PowerSeries.coeff_coe]

/--
Establishes the identity `zmodLaurentCoeffMap p k ((algebraMap (ZMod p)⟦X⟧ (ZMod p)⸨X⸩)
(PowerSeries.X : (ZMod p)⟦X⟧)) = (algebraMap k⟦X⟧ k⸨X⸩) (PowerSeries.X : k⟦X⟧)`.
-/
@[simp]
theorem zmodLaurentCoeffMap_powerSeries_X :
    zmodLaurentCoeffMap p k
        ((algebraMap (ZMod p)⟦X⟧ (ZMod p)⸨X⸩)
          (PowerSeries.X : (ZMod p)⟦X⟧)) =
      (algebraMap k⟦X⟧ k⸨X⸩) (PowerSeries.X : k⟦X⟧) := by
  change
    ((zmodLaurentCoeffMap p k).comp
        (algebraMap (ZMod p)⟦X⟧ (ZMod p)⸨X⸩))
      (PowerSeries.X : (ZMod p)⟦X⟧) =
    (algebraMap k⟦X⟧ k⸨X⸩) (PowerSeries.X : k⟦X⟧)
  rw [zmodLaurentCoeffMap_comp_powerSeries]
  simp

/-- The induced algebra structure of `k((X))` over `F_p((X))`. -/
@[reducible]
noncomputable def zmodLaurentCoeffAlgebra :
    Algebra ((ZMod p)⸨X⸩) (k⸨X⸩) :=
  RingHom.toAlgebra (zmodLaurentCoeffMap p k)



/-- The Laurent series whose coefficients are one coordinate of the coefficients
of `f` with respect to a fixed `ZMod p`-basis of `k`. -/
noncomputable def zmodLaurentCoeffCoord {ι : Type*} [Algebra (ZMod p) k]
    (b : Module.Basis ι (ZMod p) k) (f : k⸨X⸩) (i : ι) :
    (ZMod p)⸨X⸩ :=
  HahnSeries.ofSuppBddBelow
    (fun n : ℤ => b.repr (f.coeff n) i)
    (by
      refine ⟨f.order, ?_⟩
      intro n hn
      by_contra hlt
      have hzero : f.coeff n = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_order (not_le.mp hlt)
      exact hn (by simp [hzero]))

omit [CharP k p] in
/--
Establishes the identity `(zmodLaurentCoeffCoord (p := p) (k := k) b f i).coeff n = b.repr
(f.coeff n) i`.
-/
@[simp]
theorem zmodLaurentCoeffCoord_coeff {ι : Type*} [Algebra (ZMod p) k]
    (b : Module.Basis ι (ZMod p) k) (f : k⸨X⸩) (i : ι) (n : ℤ) :
    (zmodLaurentCoeffCoord (p := p) (k := k) b f i).coeff n =
      b.repr (f.coeff n) i := by
  exact congrFun
    (HahnSeries.coeff_ofSuppBddBelow
      (f := fun m : ℤ => b.repr (f.coeff m) i))
    n







end FiniteCoefficientLaurent
end LocalFieldTheory.DiscreteValuationField

end
