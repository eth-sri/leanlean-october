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
public import DOZZ.ShiftEquations.Representatives

/-! # Restricting meromorphic representatives to a thinner strip -/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- The cut-off of `F` outside the strip `S_k`. -/
noncomputable def cutoffStrip (k : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  if |z.im| < k then F z else 0

section
variable {k : ℝ} {F : ℂ → ℂ} {z : ℂ}

theorem cutoffStrip_of_lt (hz : |z.im| < k) :
    cutoffStrip k F z = F z := by
  simp [cutoffStrip, hz]

end

/-- A relation of punctured germs on a strip is codiscrete if it is automatic outside a
strictly thinner strip. -/
theorem codiscrete_of_strip {p : ℂ → Prop} {k h : ℝ} (hk : k < h)
    (hin : ∀ w ∈ horizontalStrip h, ∀ᶠ z in 𝓝[≠] w, p z)
    (hout : ∀ z : ℂ, k ≤ |z.im| → p z) : ∀ᶠ z in codiscrete ℂ, p z := by
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
  intro w
  by_cases hw : |w.im| < h
  · exact hin w hw
  · have hU : IsOpen {z : ℂ | k < |z.im|} := isOpen_lt continuous_const Complex.continuous_im.abs
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds (hk.trans_le (le_of_not_gt hw)))] with z hz
    exact hout z hz.le

/-- **Cut-off representatives.** A relation `F (z + t₁) = m z * F (z + t₂)` with real `t₁, t₂`,
holding near every point of `S_h`, holds along the codiscrete filter of `ℂ` for the cut-off of
`F` outside `S_{h/2}`. -/
theorem cutoff_relation_codiscrete {F m : ℂ → ℂ} {h : ℝ} (hh : 0 < h) (t₁ t₂ : ℝ)
    (hrel : ∀ w ∈ horizontalStrip h, ∀ᶠ z in 𝓝[≠] w, F (z + t₁) = m z * F (z + t₂)) :
    ∀ᶠ z in codiscrete ℂ,
      cutoffStrip (h / 2) F (z + t₁) = m z * cutoffStrip (h / 2) F (z + t₂) := by
  have hout (z : ℂ) (hz : ¬ |z.im| < h / 2) :
      cutoffStrip (h / 2) F (z + t₁) = m z * cutoffStrip (h / 2) F (z + t₂) := by
    simp [cutoffStrip, hz]
  refine codiscrete_of_strip (half_lt_self hh) (fun w hw => ?_) (fun z hz => hout z hz.not_gt)
  filter_upwards [hrel w hw] with z hz
  by_cases h : |z.im| < h / 2
  · simpa [cutoffStrip, h] using hz
  · exact hout z h

/-- The cut-off is meromorphic on the thinner strip. -/
theorem meromorphicOn_cutoffStrip {F : ℂ → ℂ} {h : ℝ} (hF : MeromorphicOn F (horizontalStrip h))
    {k : ℝ} (hk : k ≤ h) : MeromorphicOn (cutoffStrip k F) (horizontalStrip k) := by
  exact fun z hz =>
    have hz' := hz;
    MeromorphicAt.congr (hF z (lt_of_lt_of_le hz' hk))
      (have hopen := isOpen_horizontalStrip k;
      mp_mem (nhdsWithin_le_nhds (IsOpen.mem_nhds hopen hz')) (univ_mem' (id fun w hw => Eq.symm (cutoffStrip_of_lt hw))))

end DOZZ.Proofs

end
