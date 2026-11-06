/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.CharZeroOrGT
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Derivation.MapCoeffs
import CCDN.Noether.DifferentialResidue

/-!
A low-degree algebraic relation detects differential constants.
If t'=1, no nonzero polynomial in t of degree below the characteristic
can have differential-constant coefficients and vanish. Applied to a
bivariate relation, this gives constant descent directly from elimination.

Bounded-degree differential constants, in characteristic zero or above
the degree. In positive characteristic the degree restrictions are essential. These
lemmas isolate the constant-descent step in Gao's differential criterion;
they do not supply the resultant bounds for residues or a Bertini theorem.
-/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential

/-- A differential constant satisfying a nonzero bivariate relation of
t-degree below the characteristic (or in characteristic zero) lies in the algebraically closed base.
The inner variable represents the constant; the outer variable represents t. -/
theorem differential_constant_mem_base_of_relation
    {F L : Type*} [Field F] [IsAlgClosed F] [Field L] [Algebra F L]
    [Differential L]
    (hbase : ∀ a : F, (algebraMap F L a)′ = 0)
    (t x : L) (ht : t′ = 1) (hx : x′ = 0)
    (R : F[X][X]) (hR : R ≠ 0) (hchar : CharZeroOrGT L R.natDegree)
    (hroot : (R.map (aeval x).toRingHom).eval t = 0) :
    x ∈ (algebraMap F L).range := by
  have hmap : Differential.mapCoeffs (R.map (aeval x).toRingHom) = 0 := by
    ext i
    simp only [Differential.coeff_mapCoeffs, coeff_map, coeff_zero, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    induction R.coeff i using Polynomial.induction_on' with
    | add f g hf hg => simp only [map_add, hf, hg, add_zero]
    | monomial n a => rw [aeval_monomial]; simp [Derivation.leibniz, hbase, hx]
  have hz : R.map (aeval x).toRingHom = 0 := by
    have hchar' : CharZeroOrGT L (R.map (aeval x).toRingHom).natDegree :=
      hchar.mono natDegree_map_le
    generalize R.map (aeval x).toRingHom = f at hchar' hmap hroot
    induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
    | h n ih =>
      have he : f = C (f.coeff 0) := by
        by_cases hn0 : n = 0
        · exact eq_C_of_natDegree_eq_zero (hn.trans hn0)
        · have hderroot : f.derivative.eval t = 0 := by
            have h := Differential.deriv_aeval_eq t f
            simp only [aeval_def, Algebra.algebraMap_self, eval₂_id] at h
            rw [hroot, map_zero, hmap, eval_zero, ht, mul_one, zero_add] at h
            exact h.symm
          have hdz := ih f.derivative.natDegree (hn ▸ natDegree_derivative_lt (by omega))
            f.derivative (hchar'.mono ((natDegree_derivative_le f).trans (Nat.sub_le _ _)))
            (by rw [← derivative_differential_mapCoeffs, hmap, derivative_zero]) hderroot rfl
          ext i
          by_cases hi : i = 0
          · subst i; simp
          · rw [coeff_C, ite_eq_right hi]
            by_cases hlarge : f.natDegree < i
            · exact coeff_eq_zero_of_natDegree_lt hlarge
            · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
              have h := congrArg (fun q : L[X] => q.coeff j) hdz
              simp only [coeff_derivative, coeff_zero] at h
              exact (mul_eq_zero.mp h).resolve_right (by
                simpa only [Nat.cast_succ] using hchar'.natCast_ne_zero hi (Nat.le_of_not_gt hlarge))
      rw [he, eval_C] at hroot
      rw [he, hroot, C_0]
  let i := R.natDegree
  have hi : R.coeff i ≠ 0 := by simpa only [i, coeff_natDegree] using leadingCoeff_ne_zero.mpr hR
  have hiRoot : ((R.coeff i).map (algebraMap F L)).IsRoot x := by
    simpa only [coeff_map, coeff_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      IsRoot, eval_map, aeval_def] using congrArg (fun f : L[X] => f.coeff i) hz
  exact (IsAlgClosed.splits (R.coeff i)).mem_range_of_isRoot hi hiRoot

end
end CCDN
