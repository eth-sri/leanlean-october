module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlaceNegativeRoot

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Negative units and the real infinite-place Artin map
-/

open scoped Classical NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable (K : Type) [Field K] [NumberField K]

private theorem ringEquiv_unit_div_neg_one
    {F : Type*} [Field F] (e : F ≃+* ℝ) (x : Fˣ) :
    e ((x / (-1 : Fˣ) : Fˣ) : F) = -e (x : F) := by
  calc
    _ =
        e (x : F) / e (-1 : F) :=
      by
        rw [Units.val_div_eq_div_val]
        exact map_div₀ e (x : F) (-1 : F)
    _ = -e (x : F) := by
      rw [map_neg, map_one, div_neg, div_one]

private theorem monoidHom_eq_of_div_apply_eq_one
    {G H : Type*} [Group G] [Monoid H]
    (f : G →* H) (x y : G) (h : f (x / y) = 1) :
    f x = f y := by
  calc
    f x = f ((x / y) * y) := by simp
    _ = f (x / y) * f y := map_mul f _ _
    _ = f y := by rw [h, one_mul]

omit [NumberField K] in
/-- At a real infinite place, the Artin value of a negative global unit is
the Artin value of `-1`. -/
theorem chosenInfinitePlaceArtin_globalUnit_eq_neg_one_of_real_of_neg
    {L : Type} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (v : InfinitePlace K) (hv : v.IsReal) (a : Kˣ)
    (ha : InfinitePlace.embedding_of_isReal hv (a : K) < 0) :
    chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v
        (Units.map (algebraMap K v.Completion).toMonoidHom a) =
      chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v
        (-1 : v.Completionˣ) := by
  let e :=
    InfinitePlace.Completion.ringEquivRealOfIsReal hv
  let a_v :=
    Units.map (algebraMap K v.Completion).toMonoidHom a
  let q := a_v / (-1 : v.Completionˣ)
  have hqCoord :
      e (q : v.Completion) =
        -InfinitePlace.embedding_of_isReal hv (a : K) := by
    rw [show e (q : v.Completion) = -e (a_v : v.Completion) by
      exact ringEquiv_unit_div_neg_one e a_v]
    rw [(realInfinitePlace_globalUnit_realCoordinate K v hv a)]
  let artin := chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v
  have hqArtin : artin q = 1 := chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos
      (K := K) (L := L) v hv q (by
        rw [hqCoord]
        linarith)
  apply monoidHom_eq_of_div_apply_eq_one artin
  simpa only [q] using hqArtin

end Reciprocity
end GlobalClassFieldTheory

end
