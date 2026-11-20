module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlaceNegative

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Complete infinite-place Kummer root-character comparison
-/

open scoped Classical NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory

variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
/-- A global unit positive at a real place has trivial infinite-place Kummer
root character. -/
theorem infinitePlaceKummerRootCharacter_eq_one_of_real_of_left_pos
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : InfinitePlace K) (a b : Kˣ) (hv : v.IsReal)
    (ha : 0 < InfinitePlace.embedding_of_isReal hv (a : K)) :
    infinitePlaceKummerRootCharacter K n hnK hmu v a b = 1 := by
  let L := chosenSimpleKummerExtension K n hnK b
  let :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let a_v :=
    Units.map (algebraMap K v.Completion).toMonoidHom a
  change
    (nthRootsSubgroupEquivOfPrimitiveRoots K L n hmu).symm
        (chosenSimpleKummerRootCharacter K n hnK hmu b
          (chosenInfinitePlaceArtinMonoidHom
              v a_v)) = 1
  rw [(chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos
    v hv a_v ((realInfinitePlace_globalUnit_realCoordinate K v hv a).symm ▸ ha)), map_one, map_one]

omit [NumberField K] in
/-- In the quadratic real case, positivity of the first argument gives the
explicit local--global comparison. -/
theorem infinitePlaceKummerRootCharacter_localGlobal_of_real_of_left_pos
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : InfinitePlace K) (a b : Kˣ)
    (hn : (n : ℕ) = 2) (hv : v.IsReal)
    (ha : 0 < InfinitePlace.embedding_of_isReal hv (a : K)) :
    infinitePlaceKummerRootCharacter K n hnK hmu v a b =
      infinitePlaceHilbertSymbol K n v a b := by
  rw [infinitePlaceKummerRootCharacter_eq_one_of_real_of_left_pos
    K n hnK hmu v a b hv ha]
  symm
  apply Subtype.ext
  simp [infinitePlaceHilbertSymbol, hn, hv, (not_lt_of_ge ha.le)]

variable (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : InfinitePlace K) (a b : Kˣ)

/-- Complete quadratic comparison at a real infinite place. -/
theorem infinitePlaceKummerRootCharacter_localGlobal_of_real_of_two
    (hn : (n : ℕ) = 2) (hv : v.IsReal) :
    infinitePlaceKummerRootCharacter K n hnK hmu v a b =
      infinitePlaceHilbertSymbol K n v a b := by
  have haNe : InfinitePlace.embedding_of_isReal hv (a : K) ≠ 0 := by
    intro haZero
    apply a.ne_zero
    apply (InfinitePlace.embedding_of_isReal hv).injective
    exact haZero.trans (InfinitePlace.embedding_of_isReal hv).map_zero.symm
  rcases lt_trichotomy
      (InfinitePlace.embedding_of_isReal hv (a : K)) 0 with
    haNeg | haZero | haPos
  · have hbNe : InfinitePlace.embedding_of_isReal hv (b : K) ≠ 0 := by
      intro hbZero
      apply b.ne_zero
      apply (InfinitePlace.embedding_of_isReal hv).injective
      exact hbZero.trans (InfinitePlace.embedding_of_isReal hv).map_zero.symm
    rcases lt_trichotomy
        (InfinitePlace.embedding_of_isReal hv (b : K)) 0 with
      hbNeg | hbZero | hbPos
    · exact
        infinitePlaceKummerRootCharacter_localGlobal_of_real_of_neg_neg
          K n hnK hmu v a b hn hv haNeg hbNeg
    · exact False.elim (hbNe hbZero)
    · exact
        infinitePlaceKummerRootCharacter_localGlobal_of_real_of_radical_pos
          K n hnK hmu v a b hn hv hbPos
  · exact False.elim (haNe haZero)
  · exact
      infinitePlaceKummerRootCharacter_localGlobal_of_real_of_left_pos
        K n hnK hmu v a b hn hv haPos

/-- At every infinite place, the actual infinite-place Artin root character
equals the explicit Hilbert factor. -/
theorem infinitePlaceKummerRootCharacter_localGlobal :
    infinitePlaceKummerRootCharacter K n hnK hmu v a b =
      infinitePlaceHilbertSymbol K n v a b := by
  by_cases hv : v.IsReal
  let infinitePlaceKummerRootCharacter₀ := infinitePlaceKummerRootCharacter K n hnK hmu v a b
  · have hnLe : (n : ℕ) ≤ 2 := by
      by_contra hnLarge
      have hTwoLt : 2 < (n : ℕ) := by omega
      obtain ⟨zeta, hzeta⟩ := hmu
      have hRealZero :=
        InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
          hTwoLt ((mem_primitiveRoots n.pos).mp hzeta)
      have hRealPos : 0 < InfinitePlace.nrRealPlaces K :=
        Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
      omega
    have hnPos := n.pos
    have hnCases : (n : ℕ) = 1 ∨ (n : ℕ) = 2 := by
      omega
    rcases hnCases with hnOne | hnTwo
    let infinitePlaceHilbertSymbol₀ := infinitePlaceHilbertSymbol K n v a b
    · apply Subtype.ext
      have hleftOne :
          (infinitePlaceKummerRootCharacter₀).1 = 1 := by
        calc
          _ =
              (infinitePlaceKummerRootCharacter₀).1 ^ 1 :=
            (pow_one _).symm
          _ = (infinitePlaceKummerRootCharacter₀).1 ^
                (n : ℕ) := congrArg
                  (fun m : ℕ =>
                    (infinitePlaceKummerRootCharacter₀).1 ^ m) hnOne.symm
          _ = 1 := ((infinitePlaceKummerRootCharacter₀).2)
      have hrightOne :
          (infinitePlaceHilbertSymbol₀).1 = 1 := by
        calc
          _ =
              (infinitePlaceHilbertSymbol₀).1 ^ 1 :=
            (pow_one _).symm
          _ = (infinitePlaceHilbertSymbol₀).1 ^ (n : ℕ) :=
            congrArg
              (fun m : ℕ => (infinitePlaceHilbertSymbol₀).1 ^ m)
              hnOne.symm
          _ = 1 := ((infinitePlaceHilbertSymbol₀).2)
      exact hleftOne.trans hrightOne.symm
    · exact
        infinitePlaceKummerRootCharacter_localGlobal_of_real_of_two
          K n hnK hmu v a b hnTwo hv
  · exact
      infinitePlaceKummerRootCharacter_localGlobal_of_isComplex
        K n hnK hmu v a b (InfinitePlace.not_isReal_iff_isComplex.mp hv)

end Reciprocity
end GlobalClassFieldTheory

end
