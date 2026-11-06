module

public import Mathlib.RepresentationTheory.Rep.Iso
public import DedekindZetaZeroFree.RepresentationTheory.Irreducible.SubrepresentationsAndEigenvectors
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import DedekindZetaZeroFree.RepresentationTheory.FiniteDimensional.CharactersAndKernels
public import DedekindZetaZeroFree.RepresentationTheory.GroupAlgebra.ModuleRepresentations
public import DedekindZetaZeroFree.RepresentationTheory.Restriction.ChangeOfGroup

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Invariants.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

namespace Representation
end Representation

namespace Representation

end Representation

namespace Representation
end Representation

namespace Representation.IsIrreducible

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

theorem invariants_eq_bot {ρ : Representation k G V} (h : ρ.IsIrreducible)
    (hρ : ρ ≠ trivial k G V) : ρ.invariants = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun v hv => by_contra fun hv0 => hρ ?_
  let f : IntertwiningMap (trivial k G k) ρ :=
    (LinearMap.toSpanSingleton k V v).intertwiningMap_of_isIntertwiningMap _ _ fun g c => by
      simp_all
  have hf_one : f.toLinearMap 1 = v := by
    simp [f]
  have hsurj : Function.Surjective f.toLinearMap :=
    (IsIrreducible.surjective_or_eq_zero f).resolve_right fun hf =>
      hv0 <| calc
        v = f.toLinearMap 1 := hf_one.symm
        _ = (0 : IntertwiningMap (trivial k G k) ρ).toLinearMap 1 :=
          congrArg (fun φ : IntertwiningMap (trivial k G k) ρ => φ.toLinearMap 1) hf
        _ = 0 := rfl
  ext g x
  obtain ⟨c, rfl⟩ := hsurj x
  simpa using (IntertwiningMap.isIntertwining (trivial k G k) ρ f g c).symm

theorem invariants_eq_bot_of_finrank_ne_one {ρ : Representation k G V} (h : ρ.IsIrreducible)
    (hV : Module.finrank k V ≠ 1) : ρ.invariants = ⊥ := by
  refine h.invariants_eq_bot fun hρ => hV ?_
  subst ρ
  let _ := h.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let f : IntertwiningMap (trivial k G k) (trivial k G V) :=
    (LinearMap.toSpanSingleton k V v).intertwiningMap_of_isIntertwiningMap _ _ fun g c => by
      simp only [trivial_apply, LinearMap.toSpanSingleton_apply, map_smul]
  have hsurj : Function.Surjective f.toLinearMap :=
    (IsIrreducible.surjective_or_eq_zero f).resolve_right fun hf =>
      hv <| calc
        v = f.toLinearMap 1 := by simp [f]
        _ = (0 : IntertwiningMap (trivial k G k) (trivial k G V)).toLinearMap 1 :=
          congrArg (fun φ : IntertwiningMap (trivial k G k) (trivial k G V) =>
            φ.toLinearMap 1) hf
        _ = 0 := rfl
  apply finrank_eq_one v hv
  intro w
  obtain ⟨c, hc⟩ := hsurj w
  exact ⟨c, by simpa only [f, LinearMap.intertwiningMap_of_isIntertwiningMap,
    LinearMap.toSpanSingleton_apply] using hc⟩

end Representation.IsIrreducible

namespace DedekindZetaZeroFree.TauCeti

variable {k G : Type*} [CommRing k] [Group G] (S : Subgroup G) [S.Normal]

instance : (Rep.quotientToInvariantsFunctor k S).Additive where
