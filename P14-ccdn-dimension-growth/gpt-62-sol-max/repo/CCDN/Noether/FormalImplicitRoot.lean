/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.Topology.UniformSpace.DiscreteUniformity
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! A simple root over the constant field lifts to a formal power
series root by Weierstrass preparation after translating the simple root to zero. -/

@[expose] public section
namespace CCDN
noncomputable section

open PowerSeries
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

variable {K : Type*} [Field K] (f : Polynomial (PowerSeries K))

/-- Every simple root of the constant polynomial lifts to a formal root. -/
theorem exists_formal_simple_root (b : K)
    (hroot : (f.map PowerSeries.constantCoeff).eval b = 0)
    (hder : (f.derivative.map PowerSeries.constantCoeff).eval b ≠ 0) :
    ∃ g : PowerSeries K, PowerSeries.constantCoeff g = b ∧ f.eval g = 0 := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  let P := Polynomial.taylor (C b) f
  let g : PowerSeries (PowerSeries K) := ↑P
  let ρ := IsLocalRing.residue (PowerSeries K)
  have residue_zero (x : PowerSeries K) : ρ x = 0 ↔ constantCoeff x = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, ← ker_coeff_eq_max_ideal, RingHom.mem_ker]
  have hz : (g.map ρ).constantCoeff = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, residue_zero, Polynomial.coeff_coe,
      Polynomial.taylor_coeff_zero, ← Polynomial.eval_map_apply, constantCoeff_C]
    exact hroot
  have h1 : coeff 1 (g.map ρ) ≠ 0 := by
    rw [coeff_map, ne_eq, residue_zero, Polynomial.coeff_coe,
      Polynomial.taylor_coeff_one, ← Polynomial.eval_map_apply, constantCoeff_C]
    exact hder
  have ho :=
    le_antisymm (order_le 1 h1) (one_le_order_iff_constCoeff_eq_zero.mpr hz)
  obtain ⟨r, u, H⟩ := g.exists_isWeierstrassFactorization (exists_coeff_ne_zero_iff_ne_zero.mp ⟨1, h1⟩)
  have hd : r.natDegree = 1 := by
    have h := H.natDegree_eq_toNat_order_map
    change r.natDegree = (g.map ρ).order.toNat at h
    simpa [ho] using h
  have hc := (residue_zero _).mp
    ((IsLocalRing.residue_eq_zero_iff _).mpr (H.isDistinguishedAt.mem (n := 0) (by omega)))
  have hr := H.isDistinguishedAt.monic.eq_X_add_C hd
  let : UniformSpace K := ⊥
  
  let a := -r.coeff 0
  have ha : constantCoeff a = 0 := by simp [a, hc]
  have har : r.eval a = 0 := by rw [hr]; simp [a]
  have hEval : HasEval a := PowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero ha
  let ev := eval₂Hom (φ := RingHom.id (PowerSeries K)) continuous_id hEval
  have hev (p : Polynomial (PowerSeries K)) : ev (p : PowerSeries (PowerSeries K)) = p.eval a := by
    simp only [ev, coe_eval₂Hom, eval₂_coe, Polynomial.eval₂_id]
  have he : P.eval a = r.eval a * ev u := by
    simpa only [map_mul, g, hev] using congrArg ev H.eq_mul
  refine ⟨a + C b, by simp [ha], ?_⟩
  simpa [P, Polynomial.taylor_eval, har] using he

end
end CCDN
