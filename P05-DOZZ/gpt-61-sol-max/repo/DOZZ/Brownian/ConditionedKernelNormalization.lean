/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelGaussianIntegrals
public import DOZZ.Statements.Brownian.ConditionedPositiveTransitionDensity

/-!
# Normalization of the explicit conditioned transition kernel

The positive-drift transition density is expanded into four translated Gaussian terms. Pairing
the two terms with opposite shifts gives its total mass by the half-line Gaussian identity.
-/

public section

open MeasureTheory Set

namespace DOZZ.Proofs

/-- Completing the square shifts a heat density by the Gaussian exponential tilt. -/
theorem brownianHeatDensity_tilt {t ν z : ℝ} (ht : 0 < t) :
    Real.exp (ν * z - ν ^ 2 * t / 2) * brownianHeatDensity t z =
      brownianHeatDensity t (z - ν * t) := by
  
  have hden : Real.sqrt (2 * Real.pi * t) ≠ 0 := by positivity
  simp only [brownianHeatDensity, ht, ite_true]
  field_simp [hden]
  rw [← Real.exp_add, Real.exp_injective.eq_iff]
  field_simp [ht.ne']
  ring_nf

private theorem brownianHeatDensity_shift_exp {t ν z : ℝ} (ht : 0 < t) :
    Real.exp (-2 * ν * z) * brownianHeatDensity t (z - ν * t) =
      brownianHeatDensity t (z + ν * t) := by
  
  have hden : Real.sqrt (2 * Real.pi * t) ≠ 0 := by positivity
  simp only [brownianHeatDensity, ht, ite_true]
  field_simp [hden]
  rw [← Real.exp_add, Real.exp_injective.eq_iff]
  field_simp [ht.ne']
  ring_nf

private theorem integrable_brownianHeatDensity_translate {t a : ℝ} (ht : 0 < t) :
    Integrable (fun y : ℝ => brownianHeatDensity t (y + a)) (volume : Measure ℝ) := by
  have he  :=
    (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + a) = volume :=
    Measure.IsAddRightInvariant.map_add_right_eq_self a
  have hmapInt : Integrable (brownianHeatDensity t)
      ((volume : Measure ℝ).map (fun y : ℝ => y + a)) := by
    rw [hmap]
    exact integrable_brownianHeatDensity ht
  exact he.integrable_map_iff.mp hmapInt

/-- For positive drift and positive start, the explicit transition density integrates to one. -/
theorem conditionedPositiveTransitionDensity_integral_eq_one_pos
    {ν t x : ℝ} (hν : 0 < ν) (ht : 0 < t) (hx : 0 < x) :
    ∫ y in Set.Ioi 0, conditionedPositiveTransitionDensity ν t x y
      ∂(volume : Measure ℝ) = 1 := by
  have hH : conditionedH ν x = 1 - Real.exp (-2 * ν * x) := by
    simp [conditionedH, hν.ne']
  have hexpansion : ∀ y : ℝ, 0 < y →
      conditionedPositiveTransitionDensity ν t x y =
        (brownianHeatDensity t (y - (x + ν * t)) -
          Real.exp (-2 * ν * x) * brownianHeatDensity t (y + (x - ν * t)) -
          Real.exp (-2 * ν * x) * brownianHeatDensity t (y - (x - ν * t)) +
          brownianHeatDensity t (y + (x + ν * t))) /
          conditionedH ν x := by
    intro y hy
    have htilt₁ := brownianHeatDensity_tilt (t := t) (ν := ν) (z := y - x) ht
    have htilt₂ := brownianHeatDensity_tilt (t := t) (ν := ν) (z := y + x) ht
    have hshift₁ := brownianHeatDensity_shift_exp (t := t) (ν := ν) (z := y - x) ht
    have hshift₂ := brownianHeatDensity_shift_exp (t := t) (ν := ν) (z := y + x) ht
    have hfactor₂ : Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
        brownianHeatDensity t (y + x) =
          Real.exp (-2 * ν * x) * brownianHeatDensity t (y + x - ν * t) := by
      rw [show ν * (y - x) - ν ^ 2 * t / 2 =
          (-2 * ν * x) + (ν * (y + x) - ν ^ 2 * t / 2) by ring,
        Real.exp_add]
      rw [mul_assoc, htilt₂]
    have hcross₁ : Real.exp (-2 * ν * y) *
        brownianHeatDensity t (y - x - ν * t) =
          Real.exp (-2 * ν * x) * brownianHeatDensity t (y - x + ν * t) := by
      rw [show -2 * ν * y = (-2 * ν * x) + (-2 * ν * (y - x)) by ring,
        Real.exp_add]
      rw [mul_assoc, hshift₁]
    have hcross₂ : Real.exp (-2 * ν * (x + y)) *
        brownianHeatDensity t (y + x - ν * t) =
          brownianHeatDensity t (y + x + ν * t) := by
      simpa only [add_comm x y] using hshift₂
    have htilt₁' : Real.exp (ν * y - ν * x - ν ^ 2 * t / 2) *
        brownianHeatDensity t (y - x) =
          brownianHeatDensity t (y - (x + ν * t)) := by
      grind
    have hfactor₂' : Real.exp (ν * y - ν * x - ν ^ 2 * t / 2) *
        brownianHeatDensity t (y + x) =
          Real.exp (-2 * ν * x) * brownianHeatDensity t (y + (x - ν * t)) := by
      grind
    have hcross₁' : brownianHeatDensity t (y - x - ν * t) * Real.exp (-2 * ν * y) =
        Real.exp (-2 * ν * x) * brownianHeatDensity t (y - (x - ν * t)) := by
      grind
    have hcross₂' : Real.exp (-2 * ν * x) *
        brownianHeatDensity t (y + x - ν * t) * Real.exp (-2 * ν * y) =
        brownianHeatDensity t (y + x + ν * t) := by
      calc
        _ = (Real.exp (-2 * ν * x) * Real.exp (-2 * ν * y)) *
            brownianHeatDensity t (y + x - ν * t) := by ring
        _ = Real.exp (-2 * ν * x + -2 * ν * y) *
            brownianHeatDensity t (y + x - ν * t) := by rw [← Real.exp_add]
        _ = Real.exp (-2 * ν * (x + y)) * brownianHeatDensity t (y + x - ν * t) := by
          noncomm_ring
        _ = _ := hcross₂
    
    
    rw [conditionedPositiveTransitionDensity]
    rw [ite_eq_left (show 0 ≤ ν ∧ 0 < t ∧ 0 < x ∧ 0 < y by exact ⟨hν.le, ht, hx, hy⟩)]
    have hH_y : conditionedH ν y = 1 - Real.exp (-2 * ν * y) := by
      simp [conditionedH, hν.ne']
    grind
  have hAint : Integrable (fun y : ℝ => brownianHeatDensity t (y - (x + ν * t)))
      (volume : Measure ℝ) := integrable_brownianHeatDensity_translate ht
  have hBint  :=
    integrable_brownianHeatDensity_translate (t := t) (a := x - ν * t) ht
  have hCint : Integrable (fun y : ℝ => brownianHeatDensity t (y - (x - ν * t)))
      (volume : Measure ℝ) := integrable_brownianHeatDensity_translate ht
  have hDint  :=
    integrable_brownianHeatDensity_translate (t := t) (a := x + ν * t) ht
  have hA : IntegrableOn (fun y : ℝ => brownianHeatDensity t (y - (x + ν * t)))
      (Set.Ioi 0) (volume : Measure ℝ) := hAint.integrableOn
  have hB : IntegrableOn (fun y : ℝ => brownianHeatDensity t (y + (x - ν * t)))
      (Set.Ioi 0) (volume : Measure ℝ) := hBint.integrableOn
  have hC : IntegrableOn (fun y : ℝ => brownianHeatDensity t (y - (x - ν * t)))
      (Set.Ioi 0) (volume : Measure ℝ) := hCint.integrableOn
  have hD : IntegrableOn (fun y : ℝ => brownianHeatDensity t (y + (x + ν * t)))
      (Set.Ioi 0) (volume : Measure ℝ) := hDint.integrableOn
  have hsum  :=
    integral_brownianHeatDensity_halfline_pair ht (a := x + ν * t)
  have hsum'  :=
    integral_brownianHeatDensity_halfline_pair ht (a := x - ν * t)
  
  
  have hsum'' :
      (∫ y in Set.Ioi 0, brownianHeatDensity t (y + (x - ν * t)) ∂(volume : Measure ℝ)) +
        ∫ y in Set.Ioi 0, brownianHeatDensity t (y - (x - ν * t)) ∂(volume : Measure ℝ) = 1 := by
    rw [add_comm]
    exact hsum'
  have hlin :
      (∫ y in Set.Ioi 0, (brownianHeatDensity t (y - (x + ν * t)) -
        Real.exp (-2 * ν * x) * brownianHeatDensity t (y + (x - ν * t)) -
        Real.exp (-2 * ν * x) * brownianHeatDensity t (y - (x - ν * t)) +
        brownianHeatDensity t (y + (x + ν * t))) ∂(volume : Measure ℝ)) =
        1 - Real.exp (-2 * ν * x) := by
    calc
      _ = ∫ y in Set.Ioi 0,
          (brownianHeatDensity t (y - (x + ν * t)) +
            brownianHeatDensity t (y + (x + ν * t)) -
            Real.exp (-2 * ν * x) *
              (brownianHeatDensity t (y + (x - ν * t)) +
                brownianHeatDensity t (y - (x - ν * t)))) ∂(volume : Measure ℝ) := by
          grind
      _ = (∫ y in Set.Ioi 0,
          brownianHeatDensity t (y - (x + ν * t)) +
            brownianHeatDensity t (y + (x + ν * t)) ∂(volume : Measure ℝ)) -
          ∫ y in Set.Ioi 0,
            Real.exp (-2 * ν * x) *
              (brownianHeatDensity t (y + (x - ν * t)) +
                brownianHeatDensity t (y - (x - ν * t))) ∂(volume : Measure ℝ) := integral_sub (hA.add hD) ((hB.add hC).const_mul _)
      _ = ((∫ y in Set.Ioi 0, brownianHeatDensity t (y - (x + ν * t)) ∂(volume : Measure ℝ)) +
          ∫ y in Set.Ioi 0, brownianHeatDensity t (y + (x + ν * t)) ∂(volume : Measure ℝ)) -
          Real.exp (-2 * ν * x) *
            ((∫ y in Set.Ioi 0, brownianHeatDensity t (y + (x - ν * t)) ∂(volume : Measure ℝ)) +
              ∫ y in Set.Ioi 0, brownianHeatDensity t (y - (x - ν * t)) ∂(volume : Measure ℝ)) := by
          rw [integral_add hA hD, integral_const_mul, integral_add hB hC]
      _ = 1 - Real.exp (-2 * ν * x) := by rw [hsum, hsum'']; ring
  have hint :
      (∫ y in Set.Ioi 0, conditionedPositiveTransitionDensity ν t x y
        ∂(volume : Measure ℝ)) =
          (∫ y in Set.Ioi 0,
          (brownianHeatDensity t (y - (x + ν * t)) -
            Real.exp (-2 * ν * x) * brownianHeatDensity t (y + (x - ν * t)) -
            Real.exp (-2 * ν * x) * brownianHeatDensity t (y - (x - ν * t)) +
            brownianHeatDensity t (y + (x + ν * t))) / conditionedH ν x ∂(volume : Measure ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    exact hexpansion y hy
  have hscale :
      (∫ y in Set.Ioi 0,
        (brownianHeatDensity t (y - (x + ν * t)) -
          Real.exp (-2 * ν * x) * brownianHeatDensity t (y + (x - ν * t)) -
          Real.exp (-2 * ν * x) * brownianHeatDensity t (y - (x - ν * t)) +
          brownianHeatDensity t (y + (x + ν * t))) / conditionedH ν x
        ∂(volume : Measure ℝ)) =
        (∫ y in Set.Ioi 0,
          brownianHeatDensity t (y - (x + ν * t)) -
            Real.exp (-2 * ν * x) * brownianHeatDensity t (y + (x - ν * t)) -
            Real.exp (-2 * ν * x) * brownianHeatDensity t (y - (x - ν * t)) +
            brownianHeatDensity t (y + (x + ν * t)) ∂(volume : Measure ℝ)) /
          conditionedH ν x := by
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const]
  have hHpos : 0 < conditionedH ν x := by
    simp_all
  grind

end DOZZ.Proofs

end
