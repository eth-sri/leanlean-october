/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.FilteredIntersection
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.PDeriv
import CCDN.Algebra.CharZeroOrGT
import CCDN.AuxiliaryPolynomial.PlaneFrobeniusAuxiliary
import CCDN.Determinant.PlaneSingularities
import CCDN.ForMathlib.MvPolynomialDerivative
import CCDN.Plane.Bezout
import CCDN.Plane.FrobeniusSystem

/-! The Stepanov point bound with an explicit finite-dimensional inequality.
The polynomial bases, auxiliary coefficients, formal branches and multiplicity
argument are explicit, given a numerical choice of degrees. -/

namespace CCDN
section
open MvPolynomial

variable {ι : Type*} [Fintype ι] (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 2) (ZMod p)) (hf : Irreducible f) {D A N : ℕ}
include hf

/-- Include the points where the selected partial derivative vanishes.
Their number is bounded by d(d-1) using the proper derivative section. -/
theorem plane_stepanov_bound
    (hpos : 0 < f.totalDegree) (hchar : f.totalDegree < p)
    (z : ι → Fin 2 → ZMod p) (hz : Function.Injective z)
    (hzero : ∀ i, eval (z i) f = 0)
    (hD : f.totalDegree * D < p) (hN : N ≤ p)
    (hdim : (∑ r : Fin N, Module.finrank (ZMod p)
      (filteredCoordinateSpace (Ideal.span {f}) (D + A + r.val * f.totalDegree))) <
      Module.finrank (ZMod p) (filteredCoordinateSpace (Ideal.span {f}) D) *
      Module.finrank (ZMod p) (filteredCoordinateSpace (Ideal.span {f}) A)) :
    Fintype.card ι * N ≤ f.totalDegree * (D + p * A) +
      f.totalDegree * (f.totalDegree - 1) * N := by
  classical
  obtain ⟨k, hk⟩ := exists_pderiv_ne_zero hpos (CharZeroOrGT.of_charP hchar)
  let P (i : ι) := eval (z i) (pderiv k f) = 0
  have hgood : Fintype.card {i // ¬ P i} * N ≤ f.totalDegree * (D + p * A) := by
    let z' : {i // ¬ P i} → Fin 2 → ZMod p := fun i => z i.val
    have hzero' (i) : eval (z' i) f = 0 := hzero i.val
    have hsmooth' : ∀ i, eval (z' i) (pderiv k.rev.rev f) ≠ 0 := by grind
    obtain ⟨h, hd, hi⟩ := exists_filtered_polynomial_basis (Ideal.span {f}) D
    obtain ⟨b, hb, hbi⟩ := exists_filtered_polynomial_basis (Ideal.span {f}) A
    obtain ⟨a, ha, hne, hdiv⟩ := exists_planeFrobenius_coefficients f k.rev h b hd hb hbi
      (by aesop)
    obtain _ | ⟨⟨i⟩⟩ := isEmpty_or_nonempty {i // ¬ P i}
    · simp
    have hnd := planeFrobeniusAuxiliary_not_dvd p f hf (z' i) k.rev.rev (hzero' i)
      (hsmooth' i) h a hD hd hi hne
    choose ψ hconst hparam hfaith using fun i =>
      exists_faithful_formal_plane_branch f hf (z' i) k.rev.rev (hzero' i) (hsmooth' i)
    exact (formal_plane_multiplicity_bound f hf z' (hz.comp Subtype.val_injective) ψ (fun i => (hfaith i f).mpr dvd_rfl) hconst
      (fun _ => k.rev) (by grind) (planeFrobeniusAuxiliary p h a) hnd N fun i => by
        have hu : IsUnit (ψ i (pderiv k.rev.rev f)) := by
          rw [PowerSeries.isUnit_iff_constantCoeff, hconst]
          exact (hsmooth' i).isUnit
        apply powerSeries_weighted_derivatives_vanishing _ hu N
          fun _ hn hnN ↦ CharP.natCast_ne_zero_of_lt _ hn.ne' (hnN.trans_le hN)
        intro r hr
        have hiter (r : ℕ) : ((fun g => ψ i (pderiv k.rev.rev f) * PowerSeries.derivative g)^[r]
            (ψ i (planeFrobeniusAuxiliary p h a))) =
            ψ i ((planeTangent f k.rev)^[r] (planeFrobeniusAuxiliary p h a)) := by
          induction r with
          | zero => rfl
          | succ r hr =>
            rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hr]
            exact (formal_plane_tangent f (ψ i) ((hfaith i f).mpr dvd_rfl) k.rev (z' i k.rev)
              (by grind) _).symm
        rw [hiter, hconst]
        exact planeFrobeniusAuxiliary_tangent_vanishing p f k.rev h a r (hdiv r hr) (z' i) (hzero' i)).trans (Nat.mul_le_mul_left _ (show (planeFrobeniusAuxiliary p h a).totalDegree ≤ D + p * A by
            apply totalDegree_finsetSum_le
            intro i _
            exact (totalDegree_mul _ _).trans (Nat.add_le_add (hd i)
              ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left p (ha i))))))
  have hnd : ¬ f ∣ pderiv k f := by
    rintro ⟨u, hu⟩
    have hun : u ≠ 0 := by grind
    have he := totalDegree_mul_of_isDomain hf.ne_zero hun
    rw [← hu] at he
    have hd := pderiv_totalDegree_le f k
    omega
  have hbad := (plane_common_zeros_card_le f (pderiv k f) hf hnd
    (fun i : {i // P i} => z i.val) (hz.comp Subtype.val_injective)
    (fun i => hzero i.val) (fun i => i.property)).trans
    (Nat.mul_le_mul_left _ (pderiv_totalDegree_le f k))
  have hpartition : Fintype.card {i // P i} + Fintype.card {i // ¬ P i} = Fintype.card ι := by
    rw [Fintype.card_subtype_compl]
    exact Nat.add_sub_of_le (Fintype.card_subtype_le P)
  nlinarith

