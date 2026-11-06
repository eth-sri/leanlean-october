/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.ShiftCoeffA
public import DOZZ.Statements.Complex.HorizontalStrip
public import Mathlib.Analysis.Meromorphic.Complex
import DOZZ.ShiftEquations.Quotient.Divisors
import DOZZ.Complex.Basic
import Mathlib.Tactic

/-!
# Meromorphic germs for the gluing identities

The shift coefficient `z ↦ 𝒜(χ, z, α₂, α₃)` is meromorphic on `ℂ`; real translations and the
reflection `z ↦ c - z` preserve horizontal strips and meromorphy. Identities between such germs
that hold frequently near one point of a strip hold near every point of it.
-/

public section

open Filter Topology Set

namespace DOZZ.Proofs

/-- **The shift coefficient is meromorphic in its first charge.** -/
theorem meromorphic_shiftCoeffA (γ : ℝ) (χ α₂ α₃ : ℂ) :
    Meromorphic (fun z => shiftCoeffA γ χ z α₂ α₃) := by
  intro x
  unfold shiftCoeffA

  have h2 := meromorphicAt_lFun_comp (f := fun z : ℂ => χ * z) (z := x) (by fun_prop)
  have h3 := meromorphicAt_lFun_comp (f := fun z : ℂ => χ * z - χ ^ 2) (z := x) (by fun_prop)
  have h4 := meromorphicAt_lFun_comp (f := fun z : ℂ => χ / 2 * ((z + α₂ + α₃) - 2 * z - χ))
    (z := x) (by fun_prop)
  have h5 := meromorphicAt_lFun_comp
    (f := fun z : ℂ => χ / 2 * ((z + α₂ + α₃) - χ - 2 * Q γ)) (z := x) (by fun_prop)
  have h6 := meromorphicAt_lFun_comp
    (f := fun z : ℂ => χ / 2 * ((z + α₂ + α₃) - 2 * α₃ - χ)) (z := x) (by fun_prop)
  have h7 := meromorphicAt_lFun_comp
    (f := fun z : ℂ => χ / 2 * ((z + α₂ + α₃) - 2 * α₂ - χ)) (z := x) (by fun_prop)
  fun_prop (disch := positivity)

/-- Real translations preserve horizontal strips. -/
theorem add_ofReal_mem_horizontalStrip_glue {h : ℝ} {z : ℂ} (hz : z ∈ horizontalStrip h) (t : ℝ) :
    z + (t : ℂ) ∈ horizontalStrip h := by
  simp_all

/-- Reflections across real points preserve horizontal strips. -/
theorem ofReal_sub_mem_horizontalStrip_glue {h : ℝ} {z : ℂ} (hz : z ∈ horizontalStrip h) (t : ℝ) :
    (t : ℂ) - z ∈ horizontalStrip h := by
  have hz' : |z.im| < h := hz
  change |((t : ℂ) - z).im| < h
  simpa [abs_neg] using hz'

variable {f : ℂ → ℂ} {h : ℝ} (hf : MeromorphicOn f (horizontalStrip h)) (t : ℝ)

include f h hf t in
/-- Meromorphy is preserved by a real translation of the variable. -/
theorem MeromorphicOn.comp_add_ofReal  : MeromorphicOn (fun z => f (z + t)) (horizontalStrip h) := fun z hz =>
  (hf _ (add_ofReal_mem_horizontalStrip_glue hz t)).comp_analyticAt (g := fun w => w + (t : ℂ))
    (by fun_prop)

include f h hf t in
/-- Meromorphy is preserved by a reflection of the variable across a real point. -/
theorem MeromorphicOn.comp_ofReal_sub  : MeromorphicOn (fun z => f ((t : ℂ) - z)) (horizontalStrip h) := fun z hz =>
  (hf _ (ofReal_sub_mem_horizontalStrip_glue hz t)).comp_analyticAt (g := fun w => (t : ℂ) - w)
    (by fun_prop)

/-- Horizontal strips are preconnected. -/
theorem isPreconnected_horizontalStrip (h : ℝ) : IsPreconnected (horizontalStrip h) := by
  exact   have hconv := convex_horizontalStrip h;   Convex.isPreconnected hconv

end DOZZ.Proofs

end
