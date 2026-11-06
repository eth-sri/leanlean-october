module
public import GuthMaynard.NativeSource.GuthMaynard.TypeIReflection

@[expose] public section

open Complex Finset MeasureTheory Real Set
open scoped BigOperators ContDiff FourierTransform SchwartzMap

namespace GuthMaynard.NativeMoment

/-!
# Shared logarithmic Fourier deweighting

The main theorem is deliberately independent of the Type-I cutoff.  Any
Schwartz weight in logarithmic coordinates is removed by the same exact
Fourier-inversion identity, so the theorem applies both before reflection and
to the smooth weight on the reflected `T/N` block.
-/

/-- Source smooth weight in logarithmic coordinates, including the fixed
real-part factor. -/
noncomputable def typeILogWeight
    (Y A r : ℕ) (σ u : ℝ) : ℂ :=
  (typeISourceSmoothWeight Y A r (Real.exp u) : ℂ) *
    Complex.exp ((((-σ * u : ℝ) : ℂ)))

theorem contDiff_typeILogWeight
    (Y A r : ℕ) (σ : ℝ) : ContDiff ℝ ∞ (typeILogWeight Y A r σ) := by
  unfold typeILogWeight
  have hExp : ContDiff ℝ ∞ (fun u : ℝ => Real.exp u) := Real.contDiff_exp
  have hWeight : ContDiff ℝ ∞ (fun u : ℝ =>
      (typeISourceSmoothWeight Y A r (Real.exp u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_typeISourceSmoothWeight Y A r).comp hExp)
  have hPower : ContDiff ℝ ∞ (fun u : ℝ =>
      Complex.exp ((((-σ * u : ℝ) : ℂ)))) := by
    have hInside : ContDiff ℝ ∞ (fun u : ℝ => -σ * u) := by fun_prop
    exact Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.comp hInside)
  exact hWeight.mul hPower

theorem hasCompactSupport_typeILogWeight
    (Y A r : ℕ) (σ : ℝ) (hY : 0 < Y) :
    HasCompactSupport (typeILogWeight Y A r σ) := by
  let Q : ℝ := (2 ^ r * Y : ℕ)
  have hQ : 0 < Q := by
    dsimp only [Q]
    positivity
  have hhalf : 0 < Q / 2 := by positivity
  have htwo : 0 < 2 * Q := by positivity
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact
      (Set.Icc (Real.log (Q / 2)) (Real.log (2 * Q))))
  intro u hu
  rw [Set.mem_Icc, not_and_or] at hu
  have hcut : typeIDyadicCutoff (Real.exp u / Q) = 0 := by
    rcases hu with hu | hu
    · apply typeIDyadicCutoff_eq_zero_of_le_half
      rw [div_le_iff₀ hQ]
      have hexp : Real.exp u ≤ Q / 2 := by
        rw [← Real.exp_log hhalf]
        exact Real.exp_le_exp.mpr (le_of_lt (lt_of_not_ge hu))
      linarith
    · apply typeIDyadicCutoff_eq_zero_of_two_le
      rw [le_div_iff₀ hQ]
      have hexp : 2 * Q ≤ Real.exp u := by
        rw [← Real.exp_log htwo]
        exact Real.exp_le_exp.mpr (le_of_lt (lt_of_not_ge hu))
      exact hexp
  unfold typeILogWeight typeISourceSmoothWeight
  change ((typeITailBoundary Y A (Real.exp u) *
      typeIDyadicCutoff (Real.exp u / Q) : ℝ) : ℂ) *
        Complex.exp (((-σ * u : ℝ) : ℂ)) = 0
  rw [hcut]
  simp

/-- The logarithmic source weight as a Schwartz function. -/
noncomputable def typeILogWeightSchwartz
    (Y A r : ℕ) (σ : ℝ) (hY : 0 < Y) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_typeILogWeight Y A r σ hY).toSchwartzMap
    (contDiff_typeILogWeight Y A r σ)

@[simp]
theorem typeILogWeightSchwartz_apply
    (Y A r : ℕ) (σ u : ℝ) (hY : 0 < Y) :
    typeILogWeightSchwartz Y A r σ hY u =
      typeILogWeight Y A r σ u := rfl

/-- The phase-derived leading weight after the medium Type-I B-process,
written in logarithmic coordinates.  For Mathlib's Fourier convention the
negative mode `-m` has stationary point `t / (2πm)`.  Thus, with
`C = t / (2πQ)`, the weight is `ψ(C/eᵘ) (C/eᵘ)^(1-σ)`.

The displayed formula in ANTEDB Lemma 11.5 has `2πt/(mQ)` instead.  That
factor is incompatible with the derivative of the phase in the same display;
this definition follows the exact Poisson identity proved in
`typeIReflectionFourier_neg_eq_stationaryIntegral`. -/
noncomputable def typeIReflectedLogWeight
    (Q : ℕ) (t σ u : ℝ) : ℂ :=
  let C := t / (2 * Real.pi * Q)
  (typeIDyadicCutoff (C * Real.exp (-u)) : ℂ) *
    Complex.exp (((((1 - σ) * (Real.log C - u) : ℝ) : ℂ)))

theorem contDiff_typeIReflectedLogWeight
    (Q : ℕ) (t σ : ℝ) :
    ContDiff ℝ ∞ (typeIReflectedLogWeight Q t σ) := by
  unfold typeIReflectedLogWeight
  have hlinear : ContDiff ℝ ∞ (fun u : ℝ =>
      (1 - σ) * (Real.log (t / (2 * Real.pi * (Q : ℝ))) - u)) :=
    contDiff_const.mul (contDiff_const.sub contDiff_id)
  exact (Complex.ofRealCLM.contDiff.comp
      (contDiff_typeIDyadicCutoff.comp (by fun_prop))).mul
    (Complex.contDiff_exp.comp
      (Complex.ofRealCLM.contDiff.comp hlinear))

theorem hasCompactSupport_typeIReflectedLogWeight
    (Q : ℕ) (t σ : ℝ) (hQ : 0 < Q) (ht : 0 < t) :
    HasCompactSupport (typeIReflectedLogWeight Q t σ) := by
  let C : ℝ := t / (2 * Real.pi * Q)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hhalf : 0 < C / 2 := by positivity
  have htwo : 0 < 2 * C := by positivity
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact
      (Set.Icc (Real.log (C / 2)) (Real.log (2 * C))))
  intro u hu
  rw [Set.mem_Icc, not_and_or] at hu
  have hcut : typeIDyadicCutoff (C * Real.exp (-u)) = 0 := by
    rcases hu with hu | hu
    · apply typeIDyadicCutoff_eq_zero_of_two_le
      have hu' : u < Real.log (C / 2) := lt_of_not_ge hu
      have hexp : Real.exp u < C / 2 := by
        rw [← Real.exp_log hhalf]
        exact Real.exp_lt_exp.mpr hu'
      have hexpPos : 0 < Real.exp u := Real.exp_pos u
      rw [show Real.exp (-u) = (Real.exp u)⁻¹ by rw [Real.exp_neg]]
      rw [show C * (Real.exp u)⁻¹ = C / Real.exp u by ring]
      rw [le_div_iff₀ hexpPos]
      nlinarith
    · apply typeIDyadicCutoff_eq_zero_of_le_half
      have hu' : Real.log (2 * C) < u := lt_of_not_ge hu
      have hexp : 2 * C < Real.exp u := by
        rw [← Real.exp_log htwo]
        exact Real.exp_lt_exp.mpr hu'
      have hexpPos : 0 < Real.exp u := Real.exp_pos u
      rw [show Real.exp (-u) = (Real.exp u)⁻¹ by rw [Real.exp_neg]]
      rw [mul_inv_le_iff₀ hexpPos]
      nlinarith
  unfold typeIReflectedLogWeight
  change (typeIDyadicCutoff (C * Real.exp (-u)) : ℂ) *
      Complex.exp (((((1 - σ) * (Real.log C - u) : ℝ) : ℂ))) = 0
  rw [hcut]
  simp

/-- Schwartz realization of the reflected logarithmic amplitude. -/
noncomputable def typeIReflectedLogWeightSchwartz
    (Q : ℕ) (t σ : ℝ) (hQ : 0 < Q) (ht : 0 < t) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_typeIReflectedLogWeight Q t σ hQ ht).toSchwartzMap
    (contDiff_typeIReflectedLogWeight Q t σ)

@[simp]
theorem typeIReflectedLogWeightSchwartz_apply
    (Q : ℕ) (t σ u : ℝ) (hQ : 0 < Q) (ht : 0 < t) :
    typeIReflectedLogWeightSchwartz Q t σ hQ ht u =
      typeIReflectedLogWeight Q t σ u := rfl

end GuthMaynard.NativeMoment
