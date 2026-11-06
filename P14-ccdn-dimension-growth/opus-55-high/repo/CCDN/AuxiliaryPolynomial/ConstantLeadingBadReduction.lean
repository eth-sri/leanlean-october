/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.BivariateTotalDegree
import CCDN.Noether.ClosedFormHeight
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Determinant.ClosedFormIntegerMinor
import CCDN.Determinant.ClosedFormMinorCharge
import CCDN.ForMathlib.Matrix
import CCDN.Noether.ClosedFormScaling

/-! Bad reduction for integer bivariate equations with a nonzero constant
outer leading coefficient. A leading-coefficient factor in the witness also
covers degree-dropping reductions. -/

namespace CCDN
open Polynomial Real

/-- Full outer degree forces the outer leading coefficient to be constant. -/
lemma bivariate_leadingCoeff_eq_constant {R : Type*} [CommRing R]
    (f : R[X][X]) (htotal : bivariateTotalDegree f ≤ f.natDegree) :
    f.leadingCoeff = C (f.leadingCoeff.coeff 0) := by
  by_cases hc : f.leadingCoeff = 0
  · simp_all
  have hn :=
    Polynomial.leadingCoeff_ne_zero.mpr hc
  have h := bivariateTotalDegree_coeff_le f f.natDegree f.leadingCoeff.natDegree hn
  exact eq_C_of_natDegree_eq_zero (by omega)

lemma bivariateMap_constant_leading {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R[X][X]) (a : R) (ha : φ a ≠ 0)
    (hl : f.leadingCoeff = C a) :
    (bivariateMap φ f).natDegree = f.natDegree ∧
      (bivariateMap φ f).leadingCoeff = C (φ a) := by
  have hn : (Polynomial.mapRingHom φ) f.leadingCoeff ≠ 0 := by simp_all
  constructor
  · exact natDegree_map_of_leadingCoeff_ne_zero (Polynomial.mapRingHom φ) hn
  · exact (leadingCoeff_map_of_leadingCoeff_ne_zero (Polynomial.mapRingHom φ) hn).trans
      (by simp_all)

/-- Bad reduction includes both lost total degree and geometric reducibility. -/
def BivariateBadReduction (f : ℤ[X][X]) (d p : ℕ) : Prop :=
  ∃ hp : p.Prime, let _ : Fact p.Prime := ⟨hp⟩
    let fₚ := bivariateMap (Int.castRingHom (AlgebraicClosure (ZMod p))) f
    bivariateTotalDegree fₚ ≠ d ∨ ¬Irreducible fₚ

variable (d : ℕ)

/-- A full-outer-degree integer equation has a height-controlled positive
witness for every bad prime, including loss of degree. Integer monicity is
not required. -/
theorem exists_full_outer_bad_prime_witness
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (hd : 1 ≤ d) (f : ℤ[X][X]) (hdeg : f.natDegree = d)
    (htotal : bivariateTotalDegree f ≤ d)
    (hir : Irreducible (bivariateMap (Int.castRingHom F) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : BivariateCoefficientBound f H) :
    ∃ D : ℤ, 0 < D ∧
      Real.log D ≤ (27 * (d : ℝ) ^ 4) * (1 + 2 * Real.log H / (d : ℝ) ^ 2) ∧
      ∀ p : ℕ, d < p → BivariateBadReduction f d p → (p : ℤ) ∣ D := by
  have hf : f ≠ 0 := by grind
  let a := f.leadingCoeff.coeff 0
  have hl : f.leadingCoeff = C a := bivariate_leadingCoeff_eq_constant f (hdeg ▸ htotal)
  have ha : a ≠ 0 := by
    intro hz
    simp_all
  obtain ⟨hdegF, hlF⟩ := bivariateMap_constant_leading (Int.castRingHom F) f a
    (Int.cast_ne_zero.mpr ha) hl
  have hr := closedForm_rank_lower_of_constant_leading d (a : F) (Int.cast_ne_zero.mpr ha) _ hlF
    hir (hdegF.trans hdeg)
  obtain ⟨r, c, -, -, hdet⟩ := Matrix.exists_det_submatrix_ne_zero_of_le_rank
    (closedFormCoefficientMatrix d (bivariateMap (Int.castRingHom F) f)) (2 * d ^ 2 - 1) (by omega)
  have hD : ((closedFormCoefficientMatrix d f).submatrix r c).det ≠ 0 := fun hz =>
    hdet (by rw [← closedForm_minor_map, hz, map_zero])
  let D := ((closedFormCoefficientMatrix d f).submatrix r c).det
  have hp := mul_ne_zero ha hD
  refine ⟨|a * D|, abs_pos.mpr hp, ?_, ?_⟩
  · have hd1 : (1 : ℝ) ≤ d := mod_cast hd
    have haH := hcoeff f.natDegree 0
    have ha0 : (a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
    have hla := Real.log_le_log (abs_pos.mpr ha0) haH
    have hminor := closedForm_minor_log_height d (2 * d ^ 2 - 1) hd (by omega) f H hH hcoeff
      hdeg.le (fun i => (bivariate_coefficient_natDegree_le_totalDegree f i).trans htotal) r c hD
    rw [Int.cast_abs, Int.cast_mul, abs_mul,
      Real.log_mul (abs_ne_zero.mpr ha0) (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hD))]
    have he : (27 * d ^ 4) * (1 + 2 * Real.log H / d ^ 2) =
        (27 * (d : ℝ) ^ 4) * (1 + Real.log H / (d : ℝ) ^ 2) +
          27 * (d : ℝ) ^ 2 * Real.log H := by grind
    have hlog := Real.log_nonneg hH
    have hfac : 0 ≤ 27 * (d : ℝ) ^ 2 - 1 := by nlinarith
    nlinarith
  · intro p hp hbad
    exact (dvd_abs _ _).mpr
      (show (p : ℤ) ∣ a * ((closedFormCoefficientMatrix d f).submatrix r c).det by
          by_cases hpa : (p : ℤ) ∣ a
          · exact dvd_mul_of_dvd_left hpa _
          obtain ⟨hpp, hbad⟩ := hbad
          let : Fact p.Prime := ⟨hpp⟩
          let K := AlgebraicClosure (ZMod p)
          let g := bivariateMap (Int.castRingHom K) f
          have haK : (a : K) ≠ 0 := by
            intro hz
            exact hpa ((CharP.intCast_eq_zero_iff K p a).mp hz)
          obtain ⟨hdegK, hlK⟩ := bivariateMap_constant_leading (Int.castRingHom K) f a haK hl
          have ht : bivariateTotalDegree g ≤ d := (bivariateTotalDegree_map_le _ f).trans htotal
          have he : bivariateTotalDegree g = d := by
            have hn := bivariate_natDegree_le_totalDegree g
            grind
          have hred := hbad.resolve_left (not_ne_iff.mpr he)
          have hr := closedForm_rank_drop_of_constant_leading d (by omega) (.of_charP hp) (a : K) haK g hlK hred
            (hdegK.trans hdeg) ht
          apply dvd_mul_of_dvd_right
          apply characteristic_dvd_closedForm_minor_of_rank_lt (K := K) p d (2 * d ^ 2 - 1) f r c
          dsimp [g] at hr
          omega)

