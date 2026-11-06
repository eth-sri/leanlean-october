/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.Algebra.Module.ZLattice.Covolume
import CCDN.ClassGroup.LatticeMinimaFlag
import CCDN.ForMathlib.ZLattice
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! A uniform product-of-minima bound from Blichfeldt's principle.
The constant n^n is sufficient for the number-field lattice application. -/

public section
namespace CCDN
open Module MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Any positive monotone sequence of flag minima has product at
most n^n times the lattice covolume. -/
theorem lattice_flag_minima_product_le
    {n : ℕ} (hn : 0 < n) (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (c : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (hpos : ∀ i, 0 < a i) (hmono : Monotone a)
    (hminimum : ∀ i x, x ∈ L → x ∉ Submodule.span ℝ (c '' Set.Iio i) → a i ≤ ‖x‖) :
    ∏ i, a i ≤ ↑n ^ n * ZLattice.covolume L := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let r := fun i => a i / n
  have hr (i) : 0 < r i := div_pos (hpos i) hnR
  let u := c.toBasis.unitsSMul (fun i => Units.mk0 (r i) (hr i).ne')
  have hrepr (x : E) (i : Fin n) :
      c.toBasis.repr x i = r i * u.repr x i := by
    grind [Basis.repr_unitsSMul, Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul]
  have hcoord (x : E) (hx : x ∈ ZSpan.fundamentalDomain u) (i : Fin n) :
      0 ≤ c.toBasis.repr x i ∧ c.toBasis.repr x i < r i := by
    simp_all +arith
  have hsep : ∀ x ∈ ZSpan.fundamentalDomain u,
      ∀ y ∈ ZSpan.fundamentalDomain u, x - y ∈ L → x = y := by
    intro x hx y hy hxy
    apply sub_eq_zero.mp
    apply lattice_flag_coordinate_box_zero hn L c a hmono hminimum hxy
    intro i
    have hxi := hcoord x hx i
    have hyi := hcoord y hy i
    rw [map_sub, Finsupp.sub_apply]
    apply abs_lt.mpr
    change -(r i) < _ ∧ _ < r i
    constructor <;> linarith
  have hbound := ZLattice.measureReal_le_covolume L volume
    (ZSpan.fundamentalDomain_measurableSet u) hsep
  have hunit : volume.real (ZSpan.fundamentalDomain c.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped c.toBasis volume)]
    change (volume (parallelepiped c)).toReal = 1
    rw [c.volume_parallelepiped, ENNReal.toReal_one]
  have hvol : volume.real (ZSpan.fundamentalDomain u) =
      (∏ i, a i) / ↑n ^ n := by
    rw [ZSpan.measureReal_fundamentalDomain u volume c.toBasis]
    rw [hunit, mul_one]
    rw [Basis.det_unitsSMul_self]
    simp only [Units.val_mk0]
    rw [abs_of_pos (Finset.prod_pos (fun i _ => hr i))]
    simp only [r, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hvol] at hbound
  exact (div_le_iff₀ (pow_pos hnR n)).mp hbound |>.trans_eq (mul_comm _ _)

end CCDN
