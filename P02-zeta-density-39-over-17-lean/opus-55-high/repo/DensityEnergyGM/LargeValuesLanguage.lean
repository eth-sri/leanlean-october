module
public import Mathlib.Combinatorics.Additive.Energy
public import GuthMaynard.NativeSource.GuthMaynard.LargeValuesDefinitions
public import GuthMaynard.NativeSource.GuthMaynard.Separated
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Finset

namespace GuthMaynard.NativeMoment

/-!
# Reindexing and floor-bin language for approximate additive energy

This file supplies the finite quantitative language used in Guth--Maynard's
affine and energy arguments.  In particular it connects the source's
tolerance-one real energy with Mathlib's exact additive energy.
-/

/-- Apply a reindexing map to all four entries of an additive quadruple. -/
def mapAdditiveQuadruple {α β : Type*} (f : α → β)
    (q : (α × α) × (α × α)) : (β × β) × (β × β) :=
  ((f q.1.1, f q.1.2), (f q.2.1, f q.2.2))

/-- Translation of a finite real set, with the additive convention used by
the large-values energy argument. -/
noncomputable def gmTranslate (c : ℝ) (W : Finset ℝ) : Finset ℝ :=
  W.image (fun x => x + c)

section
variable (η c : ℝ) (W : Finset ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ))
include η c W q
theorem mapAdditiveQuadruple_translate_mem
    (hq : q ∈ approximateAdditiveQuadruples η W) :
    mapAdditiveQuadruple (fun x => x + c) q ∈
      approximateAdditiveQuadruples η (gmTranslate c W) := by
  pm_4145
  · exact Finset.mem_image.mpr ⟨q.1.1, h1, rfl⟩
  · exact Finset.mem_image.mpr ⟨q.1.2, h2, rfl⟩
  · exact Finset.mem_image.mpr ⟨q.2.1, h3, rfl⟩
  · exact Finset.mem_image.mpr ⟨q.2.2, h4, rfl⟩
  · rw [show
      (mapAdditiveQuadruple (fun x => x + c) q).1.1 +
        (mapAdditiveQuadruple (fun x => x + c) q).1.2 -
        (mapAdditiveQuadruple (fun x => x + c) q).2.1 -
        (mapAdditiveQuadruple (fun x => x + c) q).2.2 =
          q.1.1 + q.1.2 - q.2.1 - q.2.2 by
        simp only [mapAdditiveQuadruple]
        ring]
    exact hd

theorem mapAdditiveQuadruple_untranslate_mem
    (hq : q ∈ approximateAdditiveQuadruples η (gmTranslate c W)) :
    mapAdditiveQuadruple (fun x => x - c) q ∈
      approximateAdditiveQuadruples η W := by
  pm_4145
  · rcases Finset.mem_image.mp h1 with ⟨x, hx, hxeq⟩
    have : q.1.1 - c = x := by linarith
    aesop
  · rcases Finset.mem_image.mp h2 with ⟨x, hx, hxeq⟩
    have : q.1.2 - c = x := by linarith
    aesop
  · rcases Finset.mem_image.mp h3 with ⟨x, hx, hxeq⟩
    have : q.2.1 - c = x := by linarith
    aesop
  · rcases Finset.mem_image.mp h4 with ⟨x, hx, hxeq⟩
    have : q.2.2 - c = x := by linarith
    simpa [mapAdditiveQuadruple, this] using hx
  · rw [show
      (mapAdditiveQuadruple (fun x => x - c) q).1.1 +
        (mapAdditiveQuadruple (fun x => x - c) q).1.2 -
        (mapAdditiveQuadruple (fun x => x - c) q).2.1 -
        (mapAdditiveQuadruple (fun x => x - c) q).2.2 =
          q.1.1 + q.1.2 - q.2.1 - q.2.2 by
        simp only [mapAdditiveQuadruple]
        ring]
    exact hd
end

/-- Approximate additive energy is translation invariant. -/
theorem approxAddEnergy_translate (η c : ℝ) (W : Finset ℝ) :
    ApproxAddEnergy η (gmTranslate c W) = ApproxAddEnergy η W := by
  apply Nat.le_antisymm
  · unfold ApproxAddEnergy
    apply Finset.card_le_card_of_injOn
      (mapAdditiveQuadruple fun x => x - c)
    · exact mapAdditiveQuadruple_untranslate_mem η c W
    pm_4146
  · unfold ApproxAddEnergy
    apply Finset.card_le_card_of_injOn
      (mapAdditiveQuadruple fun x => x + c)
    · exact mapAdditiveQuadruple_translate_mem η c W
    pm_4146

/-- Image of the ordinate set under the integer floor map. -/
noncomputable def floorImage (W : Finset ℝ) : Finset ℤ :=
  W.image Int.floor

theorem floor_injective_on_of_separated (W : Finset ℝ)
    (hW : IsSeparated 1 W) :
    ∀ x ∈ W, ∀ y ∈ W, ⌊x⌋ = ⌊y⌋ → x = y := by
  intro x hx y hy hfloor
  by_contra hxy
  have hsep : 1 ≤ |x - y| := by
    simpa [Real.dist_eq] using hW x hx y hy hxy
  have hxfloor := Int.floor_le x
  have hyfloor := Int.floor_le y
  have hxupper := Int.lt_floor_add_one x
  have hyupper := Int.lt_floor_add_one y
  have hxylt : x - y < 1 := by
    rw [hfloor] at hxupper
    linarith
  have hyxlt : -(1 : ℝ) < x - y := by
    rw [← hfloor] at hyupper
    linarith
  exact (not_lt_of_ge hsep) (abs_lt.mpr ⟨hyxlt, hxylt⟩)

end GuthMaynard.NativeMoment
