/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousMonomials
import CCDN.Determinant.HeightDeterminant
import CCDN.Height.CountingHypotheses
import CCDN.Algebra.HomogeneousRankDichotomy
import CCDN.Determinant.HomogeneousDeterminantComparison

/-! The determinant comparison for polynomial homogeneous-coordinate maps of
integer plane-curve points. The residue geometry comes from the plane
equation, so coordinates such as (H,x,y) need no rational rows. -/

namespace CCDN
section
open MvPolynomial Matrix Real Finset

/-- Evaluating the composite `g ∘ τ` of a polynomial map `τ` and a polynomial `g` at `z` is
evaluating `g` at `τ(z)`. -/
lemma eval_polynomial_coordinate_map {R : Type*} [CommRing R] {n m : ℕ}
    (τ : Fin m → MvPolynomial (Fin n) R) (g : MvPolynomial (Fin m) R) (z : Fin n → R) :
    eval z (aeval τ g) = eval (fun j => eval z (τ j)) g := by
  change eval z (eval₂ C τ g) = _
  rw [← eval_assoc]
  rfl

/-- The complete comparison on the image of any polynomial coordinate map.
The sharp finite-field count is an explicit hypothesis. -/
theorem polynomial_map_no_auxiliary_height_comparison
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d) (hdM : d ≤ M)
    {q : MvPolynomial (Fin 2) ℤ} {H : ℝ} (hq : IsBoundedPlaneCurve F q d H)
    (τ : Fin 3 → MvPolynomial (Fin 2) ℤ) (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, eval (z i) q = 0)
    {B C : ℝ} (himage : IsBoxZeroFamily f B (fun i j => eval (z i) (τ j))) (hC : 0 ≤ C)
    (hrel : ∀ g : MvPolynomial (Fin 3) ℤ, g.IsHomogeneous M →
      (∀ i, eval (fun j => eval (z i) (τ j)) g = 0) → f ∣ g)
    (hcount : PlaneResidueCountBound C d q) :
    ∃ s : ℕ, 2 * s + d ^ 2 = d * (2 * M + 3) ∧
      (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d -
        Real.log (1 + Real.log H / (d : ℝ) ^ 2) - heightDeterminantError C) ≤
        Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
          s * M * Real.log B -
          (((2 + M).choose M : ℝ) - s) * Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  obtain ⟨s, a, hr, hi, hupper⟩ :=
    homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM
      (fun i j => eval (z i) (τ j)) himage.eval_eq_zero himage.one_le_radius himage.abs_le hrel
  have hs := (plane_homogeneous_rank_bounds hd hdM hr).1
  refine ⟨s, plane_homogeneous_rank_identity hdM hr, ?_⟩
  let g := fun k => aeval τ (monomial (homogeneousMonomials 2 M k) (1 : ℤ))
  have he : (Matrix.of fun i k => eval ((z ∘ a) i) (aeval τ (monomial (homogeneousMonomials 2 M k) (1 : ℤ)))) =
      evaluationMatrix (homogeneousMonomials 2 M) (fun i j => eval ((z ∘ a) i) (τ j)) := by
    ext i k
    change eval ((z ∘ a) i) (aeval τ (monomial (homogeneousMonomials 2 M k) (1 : ℤ))) =
      (homogeneousMonomials 2 M k).prod (fun j e => eval ((z ∘ a) i) (τ j) ^ e)
    have h := eval_polynomial_coordinate_map τ (monomial (homogeneousMonomials 2 M k) (1 : ℤ)) ((z ∘ a) i)
    simpa [eval_monomial, one_mul] using h
  have hi' : LinearIndependent ℚ
      ((Matrix.of fun i k => eval ((z ∘ a) i) (g k)).map ((↑) : ℤ → ℚ)).row := by
    rwa [show (Matrix.of fun i k => eval ((z ∘ a) i) (g k)) = _ from he]
  have hqdegree := hq.totalDegree_eq
  have hqpos : 0 < q.totalDegree := by grind
  have hcount' := hcount
  rw [← hqdegree] at hcount'
  refine le_trans ?_ hupper
  erw [show evaluationMatrix _ _ = Matrix.of fun i k => eval ((z ∘ a) i) (g k) from he.symm,
    ← hqdegree]
  have hz' : ∀ i, eval ((z ∘ a) i) q = 0 := fun i => hz (a i)
  clear_value g
  generalize z ∘ a = w at hz' hi' ⊢
  obtain ⟨B, hmem, hcharge⟩ := exists_plane_bad_prime_set q hqpos hq.irreducible H hq.one_le_height hq.coeff_le
  have hred (p : ℕ) (hp : p ∈ ((Ioc 0 s).filter Nat.Prime) \ B)
      (hlo : stepanovThreshold (q.totalDegree : ℝ) < (p : ℝ)) :
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) q) := by
    have hpp := (mem_filter.mp (mem_sdiff.mp hp).1).2
    let : Fact p.Prime := ⟨hpp⟩
    apply irreducible_reduction_of_not_hypersurfaceBadReduction q p
    intro hbad
    exact (mem_sdiff.mp hp).2 ((hmem p).mpr ⟨hlo, hbad⟩)
  have hupper (p : ℕ) (hp : p ∈ ((Ioc 0 s).filter Nat.Prime) \ B)
      (hlo : stepanovThreshold (q.totalDegree : ℝ) < (p : ℝ)) :
      (Nat.card (PlaneResidue q p) : ℝ) ≤ p + C * (q.totalDegree : ℝ) ^ 2 * Real.sqrt p :=
    hcount' p (mem_filter.mp (mem_sdiff.mp hp).1).2 hlo (hred p hp hlo)
  rw [← Nat.floor_natCast (R := ℝ) s] at hred hupper
  have hd1 : (1 : ℝ) ≤ q.totalDegree := mod_cast hqpos
  have hd4 : (q.totalDegree : ℝ) ≤ (q.totalDegree : ℝ) ^ 4 := by bound
  have hdL : (q.totalDegree : ℝ) ^ 4 ≤ stepanovThreshold (q.totalDegree : ℝ) :=
    le_mul_of_one_le_left (by positivity) (by norm_num)
  let m : ℕ → ℝ := fun p =>
    (Nat.card (PlaneResidue q p) + q.totalDegree ^ 2 * (q.totalDegree - 1) : ℕ)
  have hlocal (p : ℕ) (hp : p ∈ ((Ioc 0 ⌊(s : ℝ)⌋₊).filter Nat.Prime) \ B)
      (hpL : stepanovThreshold (q.totalDegree : ℝ) < (p : ℝ)) :
      0 < m p ∧ ∃ e : ℕ, (s : ℝ) ^ 2 / 2 / m p - s ≤ e ∧
        (p : ℤ) ^ e ∣ Int.Matrix.minorGcd (Matrix.of fun i k => eval (w i) (g k)) := by
    have : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
    obtain ⟨hm, e, he, hdiv⟩ : let m : ℕ := Nat.card (PlaneResidue q p) + q.totalDegree ^ 2 * (q.totalDegree - 1)
          0 < m ∧ ∃ e : ℕ, (s : ℝ) ^ 2 / (2 * m) - s ≤ e ∧
            (p : ℤ) ^ e ∣ Int.Matrix.minorGcd (Matrix.of fun i k => eval (w i) (g k)) := by
        dsimp
        obtain ⟨hM, e, he, hdiv⟩ : 0 < planeTotalMultiplicity q p (hred p hp hpL).ne_zero ∧ ∃ e : ℕ,
            (s : ℝ) ^ 2 / (2 * planeTotalMultiplicity q p (hred p hp hpL).ne_zero) - s ≤ e ∧
            (p : ℤ) ^ e ∣ Int.Matrix.minorGcd (Matrix.of fun i k => eval (w i) (g k)) := by
          let red : Fin s → PlaneResidue q p := fun i =>
            ⟨(fun k => (w i k : ZMod p)), by simp_all [← cast_plane_eval]⟩
          let c := Fintype.card (PlaneResidue q p)
          let E := Fintype.equivFin (PlaneResidue q p)
          let label : Fin s → Fin c := fun i => E (red i)
          let a : Fin c → Fin 2 → ℤ := fun i => planeResidueLift (E.symm i)
          let μ : Fin c → ℕ := fun i => planeResidueMultiplicity q p (hred p hp hpL).ne_zero (E.symm i)
          let n : Fin c → ℕ := fun i => Fintype.card {k : Fin s // label k = i}
          let e := ∑ i : Fin c, hypersurfaceMultiplicityExponent 1 (μ i) (n i)
          have hμ (i : Fin c) := planeResidueMultiplicity_spec q p (hred p hp hpL).ne_zero (E.symm i)
          have hsum : ∑ i : Fin c, μ i = planeTotalMultiplicity q p (hred p hp hpL).ne_zero :=
            E.symm.sum_comp (planeResidueMultiplicity q p (hred p hp hpL).ne_zero)
          have hsize := sum_residue_class_sizes label
          have hc := Fintype.card_pos_iff.mpr ⟨red ⟨0, hs⟩⟩
          have hpos :=
            hc.trans_le (planeTotalMultiplicity_bounds q p (hred p hp hpL).ne_zero).1
          refine ⟨hpos, e, cutoff_exponent_lower hpos fun K => ?_, ?_⟩
          · have h := aggregate_hypersurface_exponents_cutoff 0 n μ (fun i => (hμ i).1) K
            grind
          · apply residue_prime_powers_dvd_minorGcd _ label
            intro i cols
            have := origin_filtration_pow_dvd_det_mod (originShift (a i) q)
              (fun k j => w (residueRows label i k) j - a i j) (fun k j => ?_)
              (hypersurfaceMultiplicityExponent_le_origin _ (hμ i).2.2.1 (hμ i).2.2.2)
              (fun k => by simp [eval_sub_originShift, hz']) (fun j => originShift (a i) (g (cols j)))
            · simp [eval_sub_originShift] at this
              exact this
            apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
            rw [Int.cast_sub, cast_planeResidueLift]
            grind [residueRows_label]
        have hbound : planeTotalMultiplicity q p (hred p hp hpL).ne_zero ≤
            Fintype.card (PlaneResidue q p) + q.totalDegree ^ 2 * (q.totalDegree - 1) := by
          classical
          let S : Finset (PlaneResidue q p) :=
            Finset.univ.filter (fun a => 2 ≤ planeResidueMultiplicity q p (hred p hp hpL).ne_zero a)
          have hd : (map (Int.castRingHom (ZMod p)) q).totalDegree ≤ q.totalDegree := by
            rw [map_eq_eval₂Hom_C_comp]
            exact linear_eval₂_totalDegree_le _ X (fun j => le_of_eq (totalDegree_X j)) q
          have hpoint (a : PlaneResidue q p) : planeResidueMultiplicity q p (hred p hp hpL).ne_zero a ≤
              1 + if a ∈ S then q.totalDegree else 0 := by
            have hbound := (planeResidueMultiplicity_spec q p (hred p hp hpL).ne_zero a).2.1
            by_cases ha : a ∈ S
            · grind
            · grind
          have hsum : planeTotalMultiplicity q p (hred p hp hpL).ne_zero ≤
              Fintype.card (PlaneResidue q p) + S.card * q.totalDegree := by
            calc _ ≤ ∑ a : PlaneResidue q p, (1 + if a ∈ S then q.totalDegree else 0) :=
                   Finset.sum_le_sum fun a _ => hpoint a
                 _ = _ := by simp [Finset.sum_add_distrib]
          have hmul := Nat.mul_le_mul_right q.totalDegree (by
            have hc := plane_singular_points_card_le _ (hred p hp hpL) (MvPolynomial.totalDegree_pos_of_irreducible (hred p hp hpL)) (hd.trans_lt (mod_cast hd4.trans_lt (hdL.trans_lt hpL)))
              (fun a : S => a.val.val)
              (fun a b h => Subtype.ext (Subtype.ext h))
              (fun a => by rw [eval_map]; exact a.val.property)
              (fun a j => planeResidueMultiplicity_singular q (hred p hp hpL).ne_zero a.val
                (Finset.mem_filter.mp a.property).2 j)
            have hc' : S.card ≤ (map (Int.castRingHom (ZMod p)) q).totalDegree *
                ((map (Int.castRingHom (ZMod p)) q).totalDegree - 1) := by simp_all
            exact hc'.trans (Nat.mul_le_mul hd (Nat.sub_le_sub_right hd 1)))
          nlinarith
        rw [← Nat.card_eq_fintype_card] at hbound
        refine ⟨hM.trans_le hbound, e, ?_, hdiv⟩
        apply le_trans (sub_le_sub_right ?_ (s : ℝ)) he
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left (mod_cast hbound) (by norm_num)
    exact ⟨by positivity, e, by rwa [div_div], hdiv⟩
  have h := determinant_log_lower_of_local_divisors (mod_cast hs) hqpos hdL
    (by linarith : 0 ≤ C + 1)
    (show 0 ≤ (s : ℝ) ^ 2 / 2 by positivity) (Nat.cast_nonneg s) B ∅ (empty_subset B)
    (by simp) 0 m (one_pos.trans_le (Int.Matrix.one_le_minorGcd hi'))
    (fun p hp hpL => (hlocal p hp hpL).1) (fun p hp hpL => by
      have hcorr := singular_correction_absorb hqpos hdL hpL
      grind) (fun p hp hpL => (hlocal p hp hpL).2) (by simp)
  rw [sum_empty, add_zero, stepanovThreshold, Real.log_mul (by norm_num) (by positivity),
    Real.log_pow] at h
  have hh := mul_le_mul_of_nonneg_left hcharge (show 0 ≤ (s : ℝ) ^ 2 / 2 by positivity)
  dsimp [heightDeterminantError, degreeFourDeterminantError]
  push_cast at h
  linarith

