module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueAbelianization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturality
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteTowerNormProof

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Naturality of finite-Galois global reciprocity in abelianizations

For a finite tower `K ⊆ M ⊆ N` with `N / K` Galois, this file proves
that ordinary idèle-class norm from `M` to `K` corresponds to restriction
from `Gal(N / M)` to `Gal(N / K)`, after passing both Galois groups to their
abelianizations.  The intermediate extension `M / K` is not assumed Galois.
-/

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open AlgebraicNumberTheory
open LocalClassFieldTheory
open KummerTheory
open CyclicCohomology

 theorem abelianizationNaturalityIdeleClassIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) := by apply normIdeleClassGroup_isMulCommutative <;> assumption

attribute [local instance] abelianizationNaturalityIdeleClassIsMulCommutative

/-- Transport by an equality-induced field equivalence leaves the underlying
rational direct-limit idèle class unchanged. -/
private theorem rationalIdeleClassEquivFixed_congr_apply_val
    {A B : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    (h : A = B)
    (e : B ≃ₐ[ℚ] A)
    (he : e.trans (IntermediateField.equivOfEq h) =
      (AlgEquiv.refl : B ≃ₐ[ℚ] B))
    (c : Additive (IdeleClassGroup B)) :
    ((rationalIdeleClassEquivFixed A)
        (MulEquiv.toAdditive (ideleClassCongr e) c)).1 =
      ((rationalIdeleClassEquivFixed B) c).1 := by
  cases h
  have he' : e = AlgEquiv.refl := by
    apply AlgEquiv.ext
    intro x
    have hx := DFunLike.congr_fun he x
    change e x = x at hx
    exact hx
  simp_all
