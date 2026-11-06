import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.SmallCoatomSeeds

/-! # Constructed maximal coatom amalgamation at every arity

The two small seeds and initialized grade recursion give the actual finite
supplier. The Henkin and spectrum applications remain in `CanonicalCoatomSupply`,
which reexports this producer. No model-existence consumer is imported here.
-/

namespace VaughtConjecture.Knight.CanonicalCoatomSupply
section

private theorem faceMap_label {α : Ordinal₀} {a b : ℕ}
    (p : S α b) (r : S α a) (f : Fin a ↪ Fin b)
    (hv : Finset.univ.image f ∈ p.scheme.scheme.plan)
    (hs : p.scheme.restrictFace f hv = r.scheme) (h : typeMap f p = some r)
    (d : Cell r.scheme.scheme) :
    p.label (SemSchemeBoundaryInput.faceMap p.scheme r.scheme f hv hs d) = r.label d := by simp_all [VaughtConjecture.Knight.typeMap] <;> aesop

/-- Compatibility supplies label agreement even at empty common roots. -/
theorem compatible_labels {α : Ordinal₀} {n : ℕ} (C : CoatomPair n)
    {pa pb : S α (n + 1)} (h : C.Compatible pa pb) :
    let I := (CoatomBoundaryPresentation.of_compatible C h).input
    ∀ i, pa.label (I.shared.f i) = pb.label (I.shared.g i) := by
  dsimp 
  intro i
  let r := Classical.choose h
  have hl := (Classical.choose_spec h).1
  have hr := (Classical.choose_spec h).2
  exact (faceMap_label pa r C.g₁ _ _ hl i).trans (faceMap_label pb r C.g₂ _ _ hr i).symm

theorem arity_one {α} (hα : Order.IsSuccLimit α) (C : CoatomPair 0)
    {pa pb} (h : C.Compatible pa pb) :
    ∃ t : S α 2, C.IsAmalgam pa pb t ∧ t.HasMaximalFullCell := by
  let I := (CoatomBoundaryPresentation.of_compatible C h).input
  obtain ⟨t, hl, hr, hm⟩ := CoatomSeedInstallation.install I (SmallCoatomSeeds.one I)
    hα pa.respects pb.respects pa.label_bound pb.label_bound (compatible_labels C h)
  exact ⟨t, ⟨hl, hr⟩, hm⟩

theorem arity_two {α} (hα : Order.IsSuccLimit α) (C : CoatomPair 1)
    {pa pb} (h : C.Compatible pa pb) :
    ∃ t : S α 3, C.IsAmalgam pa pb t ∧ t.HasMaximalFullCell := by
  let I := (CoatomBoundaryPresentation.of_compatible C h).input
  obtain ⟨t, hl, hr, hm⟩ := CoatomSeedInstallation.install I (SmallCoatomSeeds.two I)
    hα pa.respects pb.respects pa.label_bound pb.label_bound (compatible_labels C h)
  exact ⟨t, ⟨hl, hr⟩, hm⟩

/-- The finite supplier, with no completion or lifting assumptions on an output. -/
theorem supply {α} (hα : Order.IsSuccLimit α) :
    MaximalCoatomAmalgamationSupply α := by
  intro n C pa pb h
  rcases n with _ | _ | n
  · exact arity_one hα C h
  · exact arity_two hα C h
  · exact?

