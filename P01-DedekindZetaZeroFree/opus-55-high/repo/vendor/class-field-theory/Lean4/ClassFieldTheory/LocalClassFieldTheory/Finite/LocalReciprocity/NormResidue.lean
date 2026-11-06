module

public import Mathlib.GroupTheory.Abelianization.Defs
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The actual abelian local Artin map

For a finite abelian Galois extension, finite local reciprocity takes values
in the actual Galois group, not merely its abelianization.  This module
provides both the algebraic homomorphism and its continuous refinement for
the native topologies.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory
open scoped IsMulCommutative

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The finite local Artin homomorphism with values in the actual Galois
group of an abelian extension. -/
def abelianLocalArtinMonoidHom :
    Kˣ →* Gal(L / K) :=
  ((Abelianization.equivOfComm (H := Gal(L / K))).symm).toMonoidHom.comp
    (localArtinMonoidHom K L)

/-- The actual abelian local Artin homomorphism is surjective. -/
theorem abelianLocalArtinMonoidHom_surjective :
    Function.Surjective (abelianLocalArtinMonoidHom K L) :=
  (Abelianization.equivOfComm (H := Gal(L / K))).symm.surjective.comp
    (localArtinMonoidHom_surjective K L)

/-- The kernel of the actual abelian local Artin homomorphism is the norm
subgroup. -/
theorem abelianLocalArtinMonoidHom_ker :
    MonoidHom.ker (abelianLocalArtinMonoidHom K L) =
      localNormSubgroup K L := by
  rw [← localArtinMonoidHom_ker K L]
  ext a
  simp only [MonoidHom.mem_ker, abelianLocalArtinMonoidHom,
    MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · intro ha
    apply (Abelianization.equivOfComm (H := Gal(L / K))).symm.injective
    simpa using ha
  simp_all
