/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.AmalgamatedBoundaryPlan
public import VaughtConjecture.Knight.ProfileBoundaryOrder

/-! # An ordered boundary on an arbitrary binary support plan

The constructor retains every occurrence of both old schemes, identifying
only the specified entire overlap. Both old orders and every inherited
lower domain are exact. Completeness is proved at every proper index.
Full-scope cells and their semantics are not supplied by this boundary.
-/

@[expose] public section

namespace VaughtConjecture.Knight.AmalgamatedBoundary

open AmalgamationPlan AmalgamatedBoundaryPlan

variable {ι : Type*} [DecidableEq ι]

/-- Put a scheme on an injective image of its point domain, without changing
its occurrence enumeration. -/
def pointImage {κ : Type*} [DecidableEq κ] {B : Finset ι} {C : Finset κ}
    (D : CellScheme B) (e : ι ↪ κ) (he : B.image e = C) : CellScheme C where
  plan := D.plan.image (Finset.image e)
  isPlan := he ▸ Plan.isPlan_image e D.isPlan
  card := D.card
  cell d := ((D.scope d).image e, D.grade d)
  cell_mem d := by
    obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (D.cell_mem d)
    refine Plan.mem_gradedPlan.mpr ⟨Finset.mem_image.mpr ⟨_, hm, rfl⟩, hp, ?_⟩
    change D.grade d ≤ (D.scope d).card at hc
    simpa [Finset.card_image_of_injective _ e.injective] using hc

theorem pointImage_complete {κ : Type*} [DecidableEq κ] {B : Finset ι} {C : Finset κ}
    (D : CellScheme B) (e : ι ↪ κ) (he : B.image e = C) (hD : D.IsComplete) :
    (pointImage D e he).IsComplete := by
  intro BJ hBJ
  obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp hBJ
  obtain ⟨K, hK, hKB⟩ := Finset.mem_image.mp hm
  have hj : BJ.2 ≤ K.card := by
    rw [← hKB, Finset.card_image_of_injective _ e.injective] at hc
    exact hc
  obtain ⟨d, hd⟩ := hD (K, BJ.2) (Plan.mem_gradedPlan.mpr ⟨hK, hp, hj⟩)
  aesop

/-- Exact shared occurrences of two ordered faces in one ambient point set.
The exhaustion fields concern geometry only, not labels or transformations. -/
structure Overlap {B C : Finset ι} (D : CellScheme B) (E : CellScheme C) (k : ℕ) where
  f : Fin k ↪ Cell D
  g : Fin k ↪ Cell E
  f_mono : StrictMono f
  g_mono : StrictMono g
  shared : ∀ i, D.cell (f i) = E.cell (g i)
  left_exhaustive : ∀ d, D.scope d ⊆ C → ∃ i, f i = d
  right_exhaustive : ∀ e, E.scope e ⊆ B → ∃ i, g i = e

end VaughtConjecture.Knight.AmalgamatedBoundary
