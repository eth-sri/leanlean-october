module

public import GaloisCohomology.Kummer.Concrete.RootCharacters
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Hilbert symbols at infinite places

At a complex place the Hilbert symbol is trivial.  At a real place, once the
base field contains the relevant roots of unity, the only nontrivial case is
the quadratic one: its value is `-1` exactly when both arguments are negative.
The definition below records that evaluation directly in `μₙ(K)`.
-/

open scoped Classical NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory

variable (K : Type) [Field K] [NumberField K]

/-- The Hilbert symbol of two global units at an infinite place.  Complex
places and nonquadratic exponents contribute `1`; a real quadratic place
contributes `-1` precisely when both real embeddings are negative. -/
def infinitePlaceHilbertSymbol
    (n : ℕ+) (v : InfinitePlace K) (a b : Kˣ) :
    nthRootsSubgroup K (n : ℕ) := by
  by_cases hn : (n : ℕ) = 2
  · by_cases hv : v.IsReal
    · by_cases ha : InfinitePlace.embedding_of_isReal hv (a : K) < 0
      · by_cases hb : InfinitePlace.embedding_of_isReal hv (b : K) < 0
        · refine ⟨(-1 : Kˣ), ?_⟩
          simp_all
        · exact 1
      · exact 1
    · exact 1
  · exact 1

omit [NumberField K] in
/-- Every complex infinite place has trivial Hilbert symbol. -/
@[simp]
theorem infinitePlaceHilbertSymbol_eq_one_of_isComplex
    (n : ℕ+) (v : InfinitePlace K) (a b : Kˣ)
    (hv : v.IsComplex) :
    infinitePlaceHilbertSymbol K n v a b = 1 := by
  have hvNotReal : ¬v.IsReal :=
    InfinitePlace.not_isReal_iff_isComplex.mpr hv
  simp [infinitePlaceHilbertSymbol, hvNotReal]
