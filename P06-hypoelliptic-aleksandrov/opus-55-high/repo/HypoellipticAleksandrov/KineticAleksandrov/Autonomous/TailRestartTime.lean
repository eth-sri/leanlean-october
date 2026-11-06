module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Elapsed
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

/-! # Exact translation of the positive elapsed-time measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory SectionTwo
open scoped ENNReal

/-- Shift a positive elapsed time by a nonnegative restart delay. -/
def tailElapsedShift (t : ℝ) (ht : 0 ≤ t) (tau : ElapsedTime ⊤) : ElapsedTime ⊤ :=
  ⟨t + tau.1, add_pos_of_nonneg_of_pos ht tau.2.1, ENNReal.ofReal_lt_top⟩

variable (t : ℝ) (ht : 0 ≤ t)

/-- The restart translation is Borel. -/
theorem measurable_tailElapsedShift  :
    Measurable (tailElapsedShift t ht) :=
  (measurable_const.add measurable_subtype_coe).subtype_mk

/-- Translation gives precisely the strict later-time restriction of elapsed Lebesgue measure. -/
theorem tailElapsedShift_map  :
    (elapsedVolume ⊤).map (tailElapsedShift t ht) =
      (elapsedVolume ⊤).restrict {tau | t < tau.1} := by
  ext B hB
  have hm : MeasurableSet {tau : ElapsedTime ⊤ | t < tau.1} :=
    measurable_subtype_coe measurableSet_Ioi
  rw [Measure.map_apply (measurable_tailElapsedShift t ht) hB,
    elapsedVolume_apply _ _ ((measurable_tailElapsedShift t ht) hB),
    Measure.restrict_apply hB, elapsedVolume_apply _ _ (hB.inter hm)]
  have he : Subtype.val '' (B ∩ {tau | t < tau.1}) =
      (fun x : ℝ => t + x) ''
        (Subtype.val '' ((tailElapsedShift t ht) ⁻¹' B)) := by
    ext x
    constructor
    · rintro ⟨tau, ⟨hBtau, httau⟩, rfl⟩
      let a : ElapsedTime ⊤ := ⟨tau.1 - t, sub_pos.mpr httau, ENNReal.ofReal_lt_top⟩
      have ha : tailElapsedShift t ht a = tau := Subtype.ext (by
        dsimp [tailElapsedShift]
        ring)
      have hb : a ∈ (tailElapsedShift t ht) ⁻¹' B := by
        simp_all
      grind
    · rintro ⟨x, ⟨tau, hBtau, rfl⟩, rfl⟩
      exact ⟨tailElapsedShift t ht tau, ⟨hBtau, by
        change t < t + tau.1; grind⟩, rfl⟩
  simp_all

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
