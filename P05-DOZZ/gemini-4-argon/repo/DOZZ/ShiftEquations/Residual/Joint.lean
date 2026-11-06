/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.ShiftCoeffA
public import DOZZ.Statements.Defs.DualMu
public import DOZZ.Statements.Defs.StructureConstant
public import DOZZ.Statements.Complex.HorizontalStrip
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Topology.DiscreteSubset
import DOZZ.ShiftEquations.Shift.ShiftGluing
import DOZZ.ShiftEquations.Shift.Reflection
import DOZZ.ShiftEquations.Gluing.Meromorphy
import DOZZ.Complex.Basic

/-!
# One representative with both shifts

The first structure shift (`structureConstant_first_shift_strip`) and the first-case dual structure
shift (`structureConstant_dual_shift_strip_first_case`, `η ≤ γ/4`) are separate existential
statements. Their functions agree with the structure constant on `(2η, Q)`, hence as germs on a
common strip. Cutting one of them off outside a thinner strip gives a single function, meromorphic
on the thinner strip, that satisfies both shifts along the codiscrete filter of `ℂ`
(`exists_joint_representative`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- The cut-off of `F` outside the strip `S_k`. -/
noncomputable def cutoffStrip (k : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  if |z.im| < k then F z else 0

theorem cutoffStrip_of_lt {k} {F : ℂ → ℂ} {z : ℂ} (hz : |z.im| < k) :
    cutoffStrip k F z = F z := by
  simp [cutoffStrip, hz]

theorem cutoffStrip_of_not_lt {k} {F : ℂ → ℂ} {z : ℂ} (hz : ¬ |z.im| < k) :
    cutoffStrip k F z = 0 := by
  simp [cutoffStrip, hz]

theorem abs_im_add_ofReal (z : ℂ) (t : ℝ) : |(z + (t : ℂ)).im| = |z.im| := by
  simp

/-- **Cut-off representatives.** A relation `F (z + t₁) = m z * F (z + t₂)` with real `t₁, t₂`,
holding near every point of `S_h`, holds along the codiscrete filter of `ℂ` for the cut-off of
`F` outside `S_{h/2}`. -/
theorem cutoff_relation_codiscrete {F m : ℂ → ℂ} {h : ℝ} (hh : 0 < h) (t₁ t₂ : ℝ)
    (hrel : ∀ w ∈ horizontalStrip h, ∀ᶠ z in 𝓝[≠] w, F (z + t₁) = m z * F (z + t₂)) :
    ∀ᶠ z in codiscrete ℂ,
      cutoffStrip (h / 2) F (z + t₁) = m z * cutoffStrip (h / 2) F (z + t₂) := by
  have hzero : ∀ z : ℂ, ¬ |z.im| < h / 2 →
      cutoffStrip (h / 2) F (z + t₁) = m z * cutoffStrip (h / 2) F (z + t₂) := fun z hz => by
    rw [cutoffStrip_of_not_lt (by rwa [abs_im_add_ofReal]),
      cutoffStrip_of_not_lt (by rwa [abs_im_add_ofReal]), mul_zero]
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
  intro x
  by_cases hx : |x.im| < h
  · filter_upwards [hrel x hx] with z hz
    by_cases hzk : |z.im| < h / 2
    · rw [cutoffStrip_of_lt (by rwa [abs_im_add_ofReal]),
        cutoffStrip_of_lt (by rwa [abs_im_add_ofReal])]
      exact hz
    · exact hzero z hzk
  · have hopen : IsOpen {w : ℂ | h / 2 < |w.im|} :=
      isOpen_lt continuous_const Complex.continuous_im.abs
    have hxo : h / 2 < |x.im| := by
      have := not_lt.mp hx
      linarith
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hxo)] with z hz
    exact hzero z (not_lt.mpr (le_of_lt hz))

/-- The cut-off is meromorphic on the thinner strip. -/
theorem meromorphicOn_cutoffStrip {F : ℂ → ℂ} {h} (hF : MeromorphicOn F (horizontalStrip h))
    {k} (hk : k ≤ h) : MeromorphicOn (cutoffStrip k F) (horizontalStrip k) := by
  intro z hz
  have hz' := hz
  refine (hF z (lt_of_lt_of_le hz' hk)).congr ?_
  filter_upwards [nhdsWithin_le_nhds ((isOpen_horizontalStrip k).mem_nhds hz')] with w hw
  exact (cutoffStrip_of_lt hw).symm

end DOZZ.Proofs

end
