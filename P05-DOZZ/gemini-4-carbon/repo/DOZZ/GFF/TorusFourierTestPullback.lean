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

section


namespace DOZZ



/-- A torus character evaluated at the scaled representative point has the phase used by the
local trigonometric tests. -/
theorem mFourier_torusBoxPoint_eq_exp (L : ℝ) (hL : 0 < L)
    (k : Fin 2 → ℤ) (t : GFFUnitTorus2) :
    UnitAddTorus.mFourier k t =
      Complex.exp (Complex.I * torusModePhase L k (torusBoxPoint L t)) := by
  have mFourier_realBox_eq_exp (k : Fin 2 → ℤ) (x : Fin 2 → ℝ) : UnitAddTorus.mFourier k (fun i => (x i : UnitAddCircle)) =
        Complex.exp (2 * Real.pi * Complex.I *
          ((k 0 : ℝ) * x 0 + (k 1 : ℝ) * x 1)) := by
    rw [UnitAddTorus.mFourier]
    simp only [ContinuousMap.coe_mk, Fin.prod_univ_two, fourier_coe_apply]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  let e := UnitAddTorus.measurableEquivPiIoc
    (fun _ : Fin 2 => (-1 / 2 : ℝ))
  let x := (e t).1
  have ht : t = fun i => (x i : UnitAddCircle) := by
    exact (e.symm_apply_apply t).symm
  have hbox : torusBoxPoint L t = ⟨L * x 0, L * x 1⟩ := by rfl
  rw [ht, mFourier_realBox_eq_exp]
  have hphase : 2 * Real.pi * Complex.I *
      ((k 0 : ℝ) * x 0 + (k 1 : ℝ) * x 1) =
      Complex.I * torusModePhase L k (torusBoxPoint L t) := by
    rw [hbox, torusModePhase]
    push_cast
    field_simp [ne_of_gt hL]
  rw [← ht, hphase]



section
variable (R L : ℝ) (hR : 0 < R) (hL : 0 < L) (k : Fin 2 → ℤ) (t : GFFUnitTorus2)
include hR hL k t

theorem localTorusCosTest_torusBoxPoint :
    localTorusCosTest R L hR k (torusBoxPoint L t) =
      localTorusCutoff R hR (torusBoxPoint L t) *
        (UnitAddTorus.mFourier k t).re := by
  have torusBox_cos_eq_mFourier_re : Real.cos (torusModePhase L k (torusBoxPoint L t)) =
        (UnitAddTorus.mFourier k t).re := by
    rw [mFourier_torusBoxPoint_eq_exp L hL k t]
    rw [show Complex.I * torusModePhase L k (torusBoxPoint L t) =
        torusModePhase L k (torusBoxPoint L t) * Complex.I by ring]
    exact (Complex.exp_ofReal_mul_I_re _).symm
  rw [localTorusCosTest_apply, torusBox_cos_eq_mFourier_re]

theorem localTorusSinTest_torusBoxPoint :
    localTorusSinTest R L hR k (torusBoxPoint L t) =
      localTorusCutoff R hR (torusBoxPoint L t) *
        (UnitAddTorus.mFourier k t).im := by
  have torusBox_sin_eq_mFourier_im : Real.sin (torusModePhase L k (torusBoxPoint L t)) =
        (UnitAddTorus.mFourier k t).im := by
    rw [mFourier_torusBoxPoint_eq_exp L hL k t]
    rw [show Complex.I * torusModePhase L k (torusBoxPoint L t) =
        torusModePhase L k (torusBoxPoint L t) * Complex.I by ring]
    exact (Complex.exp_ofReal_mul_I_im _).symm
  rw [localTorusSinTest_apply, torusBox_sin_eq_mFourier_im]


end
end DOZZ

end
