module

public import GaloisCohomology.Kummer.Concrete.SimpleExtension
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Local Hilbert symbols

This file constructs the local Hilbert symbol from the public Kummer-theory
and local-reciprocity APIs.

For `b : Kˣ`, a root `β` of `X ^ n - b` is chosen in the separable closure
and the literal simple extension `K(β)` is formed.  If `K` contains the
`n`-th roots of unity, Kummer theory makes this extension finite abelian
Galois.  The Hilbert symbol is the root quotient of the local Artin
automorphism, transported back to `μₙ(K)`.
-/

noncomputable section

namespace LocalClassFieldTheory
namespace Kummer

open CyclicCohomology KummerTheory ClassFormation
open LocalFieldTheory LocalClassFieldTheory

variable (K : Type) [Field K]

variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The local Artin automorphism of the concrete Kummer extension. -/
def chosenSimpleKummerNormResidueAutomorphism
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    Kˣ →* Gal((chosenSimpleKummerExtension K n hnK b)/K) := by
  let E := chosenSimpleKummerExtension K n hnK b
  letI : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  exact abelianLocalArtinMonoidHom K E

/-- The local Hilbert symbol `(a,b)ₙ`, valued in the actual subgroup
`μₙ(K)`. -/
def localHilbertSymbol
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    nthRootsSubgroup K (n : ℕ) :=
  (nthRootsSubgroupEquivOfPrimitiveRoots
    K (chosenSimpleKummerExtension K n hnK b) n hmu).symm
      (chosenSimpleKummerRootCharacter K n hnK hmu b
        (chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b a))

/-- For fixed `b`, the local Hilbert symbol is a homomorphism in its first
argument. -/
def localHilbertSymbolHom
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    Kˣ →* nthRootsSubgroup K (n : ℕ) :=
  (nthRootsSubgroupEquivOfPrimitiveRoots
      K (chosenSimpleKummerExtension K n hnK b) n hmu).symm.toMonoidHom.comp
    ((chosenSimpleKummerRootCharacter K n hnK hmu b).comp
      (chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b))

@[simp]
theorem localHilbertSymbolHom_apply
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    localHilbertSymbolHom K n hnK hmu b a =
      localHilbertSymbol K n hnK hmu a b :=
  rfl

/-- Base change sends the Hilbert symbol to its defining root quotient. -/
theorem localHilbertSymbol_map_eq_rootQuotient
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    nthRootsSubgroupMap K (chosenSimpleKummerExtension K n hnK b) (n : ℕ)
        (localHilbertSymbol K n hnK hmu a b) =
      ⟨rootQuotient
          (K := K) (L := chosenSimpleKummerExtension K n hnK b)
          (chosenSimpleKummerRootUnit K n hnK b)
          (chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b a),
        chosenSimpleKummer_rootQuotient_mem K n hnK b
          (chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b a)⟩ := by
  change
    (nthRootsSubgroupEquivOfPrimitiveRoots
      K (chosenSimpleKummerExtension K n hnK b) n hmu)
        ((nthRootsSubgroupEquivOfPrimitiveRoots
          K (chosenSimpleKummerExtension K n hnK b) n hmu).symm
            (chosenSimpleKummerRootCharacter K n hnK hmu b
              (chosenSimpleKummerNormResidueAutomorphism
                K n hnK hmu b a))) = _
  simp

/-- The concrete Artin homomorphism has precisely the local norm subgroup
as its kernel. -/
theorem chosenSimpleKummerNormResidueAutomorphism_ker
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    (chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b).ker =
      LocalFieldTheory.localNormSubgroup K
        (chosenSimpleKummerExtension K n hnK b) := by
  let E := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  change (abelianLocalArtinMonoidHom K E).ker =
    LocalFieldTheory.localNormSubgroup K E
  exact abelianLocalArtinMonoidHom_ker K E
