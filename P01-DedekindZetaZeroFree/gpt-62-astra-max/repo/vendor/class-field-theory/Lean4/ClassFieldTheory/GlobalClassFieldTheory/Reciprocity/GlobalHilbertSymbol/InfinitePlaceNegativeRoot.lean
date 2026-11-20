module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlaceRamification
public import Mathlib.Analysis.Complex.Order

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Complex conjugation on a negative quadratic Kummer root
-/

open scoped Classical ComplexConjugate ComplexOrder NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory

variable (K : Type) [Field K] [NumberField K]

/-- At a real place where the quadratic radicand is negative, the actual
infinite-place Artin value of `-1` sends the chosen Kummer root to its
negative. -/
theorem chosenInfinitePlaceArtin_neg_one_apply_kummerRoot_of_real_of_radical_neg
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : InfinitePlace K) (b : Kˣ)
    (hn : (n : ℕ) = 2) (hv : v.IsReal)
    (hb : InfinitePlace.embedding_of_isReal hv (b : K) < 0) :
    let L := chosenSimpleKummerExtension K n hnK b
    letI : FiniteDimensional K L :=
      chosenSimpleKummerExtension_finiteDimensional K n hnK b
    letI : IsAbelianGalois K L :=
      chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
    letI : NumberField L := NumberField.of_module_finite K L
    let beta : L := (chosenSimpleKummerRootUnit K n hnK b : Lˣ)
    chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v
        (-1 : v.Completionˣ) beta = -beta := by
  let L := chosenSimpleKummerExtension K n hnK b
  let :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let := NumberField.of_module_finite K L
  let beta := (chosenSimpleKummerRootUnit K n hnK b : Lˣ)
  have hbeta : beta ^ 2 = algebraMap K L (b : K) := by
    have hunit := congrArg Units.val
      (chosenSimpleKummerRootUnit_pow K n hnK b)
    rw [hn] at hunit
    exact hunit
  let w := chosenInfinitePlaceAbove (L := L) v
  have hw : w.comap (algebraMap K L) = v :=
    chosenInfinitePlaceAbove_comap (L := L) v
  have hsq :
      (w.embedding beta) ^ 2 =
        (InfinitePlace.embedding_of_isReal hv (b : K) : ℂ) := by
    calc
      _ = w.embedding (beta ^ 2) := by rw [map_pow]
      _ = w.embedding (algebraMap K L (b : K)) := by rw [hbeta]
      _ = (w.comap (algebraMap K L)).embedding (b : K) := by
        rw [(InfinitePlace.comap_embedding_of_isReal
          (algebraMap K L) (by
            rw [hw]
            exact hv))]
        rfl
      _ = v.embedding (b : K) := by rw [hw]
      _ = (InfinitePlace.embedding_of_isReal hv (b : K) : ℂ) := by
        rw [InfinitePlace.embedding_of_isReal_apply]
  have hstar : star (w.embedding beta) = -w.embedding beta := by
    apply Complex.ext
    · simp [(Complex.sq_nonpos_iff.mp (by
      rw [hsq]
      exact (Complex.real_le_real).2 hb.le))]
    · simp
  have hRamified : w.IsRamified K := by
    simpa using
      chosenSimpleKummerExtension_chosenInfinitePlace_isRamified_of_real_of_radical_neg
        K n hnK hmu v b hn hv hb
  apply w.embedding.injective
  calc
    w.embedding
        (chosenInfinitePlaceArtinMonoidHom v
          (-1 : v.Completionˣ) beta) =
        star (w.embedding beta) := (chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
          v hRamified).eq beta
    _ = -w.embedding beta := hstar
    _ = w.embedding (-beta) := by rw [map_neg]

end Reciprocity
end GlobalClassFieldTheory

end
