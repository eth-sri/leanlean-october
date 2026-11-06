/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.TorusBoxL2

/-!
# DOZZ.GFF.TorusFourierTestPullback

The compactly supported cosine and sine modes are the real and imaginary parts of the complex
Fourier characters on the chosen torus box.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace Topology lp

namespace DOZZ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure GFFUnitTorus2) := by
  infer_instance

private theorem mFourier_realBox_eq_exp (k : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    UnitAddTorus.mFourier k (fun i => (x i : UnitAddCircle)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((k 0 : ℝ) * x 0 + (k 1 : ℝ) * x 1)) := by
  rw [UnitAddTorus.mFourier]
  simp
  rw [← Complex.exp_add]
  congr 1
  ring
section
variable (L : ℝ)
section
variable (hL : 0 < L) (k : Fin 2 → ℤ) (t : GFFUnitTorus2)
include hL

/-- A torus character evaluated at the scaled representative point has the phase used by the
local trigonometric tests. -/
theorem mFourier_torusBoxPoint_eq_exp :
    UnitAddTorus.mFourier k t =
      Complex.exp (Complex.I * torusModePhase L k (torusBoxPoint L t)) := by
  let e := UnitAddTorus.measurableEquivPiIoc
    (fun _ : Fin 2 => (-1 / 2 : ℝ))
  let x := (e t).1
  have ht : t = fun i => (x i : UnitAddCircle) := by
    aesop
  have hbox : torusBoxPoint L t = ⟨L * x 0, L * x 1⟩ := by
    rfl
  rw [ht, mFourier_realBox_eq_exp]
  have hphase : 2 * Real.pi * Complex.I *
      ((k 0 : ℝ) * x 0 + (k 1 : ℝ) * x 1) =
      Complex.I * torusModePhase L k (torusBoxPoint L t) := by
    rw [hbox, torusModePhase]
    push_cast
    field_simp [ne_of_gt hL]
  simp_all

theorem torusBox_cos_eq_mFourier_re :
    Real.cos (torusModePhase L k (torusBoxPoint L t)) =
      (UnitAddTorus.mFourier k t).re := by
  rw [mFourier_torusBoxPoint_eq_exp L hL k t]
  rw [show Complex.I * torusModePhase L k (torusBoxPoint L t) =
      torusModePhase L k _ * Complex.I by ring]
  simp

theorem torusBox_sin_eq_mFourier_im :
    Real.sin (torusModePhase L k (torusBoxPoint L t)) =
      (UnitAddTorus.mFourier k t).im := by
  rw [mFourier_torusBoxPoint_eq_exp L hL k t]
  rw [show Complex.I * torusModePhase L k (torusBoxPoint L t) =
      torusModePhase L k _ * Complex.I by ring]
  simp

end

end
section
variable (R L : ℝ) (hR : 0 < R)
section
variable (hL : 0 < L) (k : Fin 2 → ℤ) (t : GFFUnitTorus2)
include hL

theorem localTorusCosTest_torusBoxPoint :
    localTorusCosTest R L hR k (torusBoxPoint L t) =
      localTorusCutoff R hR (torusBoxPoint L t) *
        (UnitAddTorus.mFourier k t).re := by
  rw [localTorusCosTest_apply, torusBox_cos_eq_mFourier_re L hL k t]

theorem localTorusSinTest_torusBoxPoint :
    localTorusSinTest R L hR k (torusBoxPoint L t) =
      localTorusCutoff R hR (torusBoxPoint L t) *
        (UnitAddTorus.mFourier k t).im := by
  rw [localTorusSinTest_apply, torusBox_sin_eq_mFourier_im L hL k t]

end

end

end DOZZ

end
