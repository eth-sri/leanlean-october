/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.ShiftCoeffA
public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
public import DOZZ.Statements.Hypergeom.GaussParameterA
public import DOZZ.Statements.Hypergeom.GaussParameterB
public import DOZZ.Statements.Hypergeom.GaussParameterC
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The diagonal Gauss coefficient ratio as a shift coefficient

On the diagonal `Q = χ + 1/χ` the Gauss parameters `a`, `b`, `c` of the physical hypergeometric
family satisfy, with `Σ = z + α₂ + α₃`,
`c = χ z - χ²`, `a = χ/2 (Σ - χ - 2 Q)`, `b = χ/2 (Σ - 2 α₃ - χ)`,
`a - c + 1 = χ/2 (Σ - 2 z - χ)`, `c - b = χ/2 (Σ - 2 α₂ - χ)` and `2 - c = 2 + χ² - χ z`.

Consequently `shiftCoeffA` is `l(-χ²) l(χ z) l(c)` times the Gamma quotient `X / Y` (with
`X = Γ(1-a) Γ(1-b) Γ(a-c+1) Γ(b-c+1)` and `Y = Γ(c-a) Γ(c-b) Γ(a) Γ(b)`), while
`gaussCoefficientRatio` is `-(Γ(c) / Γ(2-c))²` times the same quotient. The scalar identity
`-(Γ(c) / Γ(2-c))² l(2-c) = l(c)` for `c ≠ 1` glues the two. All Gamma identities are proved over
`ℝ` and cast to `ℂ` once.
-/

@[expose] public section

namespace DOZZ.Proofs

/-- The real-variable `l` function `Γ(x) / Γ(1 - x)` (literal quotient, no nonvanishing
hypotheses). -/
noncomputable def gaussRatio_l (x : ℝ) : ℝ := Real.Gamma x / Real.Gamma (1 - x)

/-! ### Parameter identities on the diagonal `Q = χ + 1/χ` -/

section Parameters

variable {γ χ z α₂ α₃ : ℝ}

/-- `c = χ z - χ²`. -/
theorem gaussRatio_param_c (hχ : χ ≠ 0) (hQ : Q γ = χ + 1 / χ) :
    gaussParameterC γ χ z = χ * z - χ ^ 2 := by
  unfold gaussParameterC
  rw [hQ]
  field_simp
  ring






end Parameters

/-! ### The real Gamma identities -/





/-! ### Passage to `ℂ` -/


/-- `lFun` at a complex number equal to a real cast. -/
theorem gaussRatio_lFun_of_eq {x} {r : ℝ} (h : x = (r : ℂ)) :
    lFun x = (gaussRatio_l r : ℂ) := by
  have gaussRatio_lFun_ofReal (x : ℝ) : lFun (x : ℂ) = (gaussRatio_l x : ℂ) := by
    unfold lFun gaussRatio_l
    rw [(show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring), Complex.Gamma_ofReal, Complex.Gamma_ofReal]
    push_cast
    rfl
  rw [h]
  exact gaussRatio_lFun_ofReal r


/-- The instance `χ = γ/2` of `gaussCoefficientRatio_mul_eq_shiftCoeffA`. -/
theorem gaussCoefficientRatio_mul_eq_shiftCoeffA_half {γ z α₂ α₃} (hγ : 0 < γ)
    (hc : gaussParameterC γ (γ / 2) z ≠ 1) :
    (gaussCoefficientRatio (gaussParameterA γ (γ / 2) z α₂ α₃)
        (gaussParameterB γ (γ / 2) z α₂ α₃) (gaussParameterC γ (γ / 2) z) : ℂ) *
      (lFun (-((γ / 2 : ℝ) : ℂ) ^ 2) * lFun (((γ / 2 : ℝ) : ℂ) * z) *
        lFun (2 + ((γ / 2 : ℝ) : ℂ) ^ 2 - ((γ / 2 : ℝ) : ℂ) * z)) =
      shiftCoeffA γ ((γ / 2 : ℝ) : ℂ) z α₂ α₃ := by
  have gaussCoefficientRatio_mul_eq_shiftCoeffA {γ} {χ : ℝ} {z} {α₂} {α₃} (hχ : χ ≠ 0) (hQ : Q γ = χ + 1 / χ) (hc : gaussParameterC γ χ z ≠ 1) : (gaussCoefficientRatio (gaussParameterA γ χ z α₂ α₃) (gaussParameterB γ χ z α₂ α₃) (gaussParameterC γ χ z) : ℂ) * (lFun (-(χ : ℂ) ^ 2) * lFun ((χ : ℂ) * z) * lFun (2 + (χ : ℂ) ^ 2 - (χ : ℂ) * z)) = shiftCoeffA γ χ z α₂ α₃ := by
    have gaussRatio_real_identity {a} {b} {c} (hc : c ≠ 1) L₁ L₂ : gaussCoefficientRatio a b c * (L₁ * L₂ * gaussRatio_l (2 - c)) = L₁ * L₂ * gaussRatio_l c * gaussRatio_l (a - c + 1) / (gaussRatio_l a * gaussRatio_l b * gaussRatio_l (c - b)) := by
      have gaussRatio_key : -(Real.Gamma c / Real.Gamma (2 - c)) ^ 2 * gaussRatio_l (2 - c) = gaussRatio_l c := by
        have h1 : Real.Gamma c = (c - 1) * Real.Gamma (c - 1) := by
          have := Real.Gamma_add_one (sub_ne_zero.mpr hc)
          rwa [sub_add_cancel] at this
        have h2 : Real.Gamma (2 - c) = (1 - c) * Real.Gamma (1 - c) := by
          have := Real.Gamma_add_one (sub_ne_zero.mpr hc.symm)
          rwa [show 1 - c + 1 = 2 - c by ring] at this
        rw [(show gaussRatio_l (2 - c) = Real.Gamma (2 - c) / Real.Gamma (c - 1) by unfold gaussRatio_l; rw [show 1 - (2 - c) = c - 1 by ring])]
        unfold gaussRatio_l
        rw [h1, h2]
        generalize Real.Gamma (c - 1) = g
        generalize Real.Gamma (1 - c) = h
        by_cases hg : g = 0
        · simp [hg]
        by_cases hh : h = 0
        · simp [hh]
        field_simp
        ring
      rw [← gaussRatio_key, (show gaussRatio_l (a - c + 1) = Real.Gamma (a - c + 1) / Real.Gamma (c - a) by unfold gaussRatio_l; rw [show 1 - (a - c + 1) = c - a by ring]), (show gaussRatio_l (c - b) = Real.Gamma (c - b) / Real.Gamma (b - c + 1) by unfold gaussRatio_l; rw [show 1 - (c - b) = b - c + 1 by ring])]
      unfold gaussCoefficientRatio
      generalize gaussRatio_l (2 - c) = T
      unfold gaussRatio_l
      simp only [div_eq_mul_inv, mul_inv, inv_inv]
      ring
    have gaussRatio_param_c_sub_b : gaussParameterC γ χ z - gaussParameterB γ χ z α₂ α₃ = χ / 2 * ((z + α₂ + α₃) - 2 * α₂ - χ) := by
      unfold gaussParameterB gaussParameterC
      rw [hQ]
      field_simp
      ring
    have gaussRatio_param_a_sub_c : gaussParameterA γ χ z α₂ α₃ - gaussParameterC γ χ z + 1 = χ / 2 * ((z + α₂ + α₃) - 2 * z - χ) := by
      unfold gaussParameterA gaussParameterC
      rw [hQ]
      field_simp
      ring
    have gaussRatio_param_b : gaussParameterB γ χ z α₂ α₃ = χ / 2 * ((z + α₂ + α₃) - 2 * α₃ - χ) := by
      unfold gaussParameterB
      rw [hQ]
      field_simp
      ring
    have gaussRatio_param_a : gaussParameterA γ χ z α₂ α₃ = χ / 2 * ((z + α₂ + α₃) - χ - 2 * Q γ) := by
      unfold gaussParameterA
      rw [hQ]
      field_simp
      ring
    have hreal := gaussRatio_real_identity (a := gaussParameterA γ χ z α₂ α₃)
      (b := gaussParameterB γ χ z α₂ α₃) hc (gaussRatio_l (-χ ^ 2)) (gaussRatio_l (χ * z))
    unfold shiftCoeffA
    rw [(gaussRatio_lFun_of_eq (by push_cast; ring) : lFun (-(χ : ℂ) ^ 2) = (gaussRatio_l (-χ ^ 2) : ℂ)), (gaussRatio_lFun_of_eq (by push_cast; ring) : lFun ((χ : ℂ) * z) = (gaussRatio_l (χ * z) : ℂ)), (gaussRatio_lFun_of_eq (by rw [(show 2 - gaussParameterC γ χ z = 2 + χ ^ 2 - χ * z by rw [gaussRatio_param_c hχ hQ]; ring)]; push_cast; ring) : lFun (2 + (χ : ℂ) ^ 2 - (χ : ℂ) * z) = (gaussRatio_l (2 - gaussParameterC γ χ z) : ℂ)), (gaussRatio_lFun_of_eq (by rw [gaussRatio_param_c hχ hQ]; push_cast; ring) : lFun ((χ : ℂ) * z - (χ : ℂ) ^ 2) = (gaussRatio_l (gaussParameterC γ χ z) : ℂ)), (gaussRatio_lFun_of_eq (by rw [gaussRatio_param_a_sub_c]; push_cast; ring) : lFun ((χ : ℂ) / 2 * ((z + α₂ + α₃ : ℂ) - 2 * z - χ)) = (gaussRatio_l (gaussParameterA γ χ z α₂ α₃ - gaussParameterC γ χ z + 1) : ℂ)), (gaussRatio_lFun_of_eq (by rw [gaussRatio_param_a]; push_cast; ring) : lFun ((χ : ℂ) / 2 * ((z + α₂ + α₃ : ℂ) - χ - 2 * (Q γ : ℂ))) = (gaussRatio_l (gaussParameterA γ χ z α₂ α₃) : ℂ)), (gaussRatio_lFun_of_eq (by rw [gaussRatio_param_b]; push_cast; ring) : lFun ((χ : ℂ) / 2 * ((z + α₂ + α₃ : ℂ) - 2 * α₃ - χ)) = (gaussRatio_l (gaussParameterB γ χ z α₂ α₃) : ℂ)), (gaussRatio_lFun_of_eq (by rw [gaussRatio_param_c_sub_b]; push_cast; ring) : lFun ((χ : ℂ) / 2 * ((z + α₂ + α₃ : ℂ) - 2 * α₂ - χ)) = (gaussRatio_l (gaussParameterC γ χ z - gaussParameterB γ χ z α₂ α₃) : ℂ))]
    exact_mod_cast hreal
  refine gaussCoefficientRatio_mul_eq_shiftCoeffA (by positivity) ?_ hc
  unfold Q
  field_simp
  ring


end DOZZ.Proofs

end
