/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousSlice
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.ForMathlib.MvPolynomial

/-! Prime scaling changes the geometric bad-prime factor by at most an
absolute constant. Outside the scaling prime, the homogeneous models are
related by an invertible change of coordinates and a nonzero scalar. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma scaledHomogenize_map_irreducible_iff {K : Type*} [Field K] {n d : ℕ}
    (φ : ℤ →+* K) (h : ℤ) (hh : φ h ≠ 0)
    (f : MvPolynomial (Fin n) ℤ) (hd : f.totalDegree ≤ d) :
    Irreducible (map φ (scaledHomogenize d h f)) ↔
      Irreducible (map φ (scaledHomogenize d 1 f)) := by
  rw [scaledHomogenize_map, scaledHomogenize_map, map_one]
  let g := map φ f
  have hgd : g.totalDegree ≤ d := (totalDegree_map_le _ _).trans hd
  have hscale : firstCoordinateScaleHom K (φ h) (scaledHomogenize d (φ h) g) =
      C (φ h ^ d) * scaledHomogenize d 1 g := by
    refine affineChart_injective_on_homogeneous
      (firstCoordinateScaleHom_homogeneous (φ h) (scaledHomogenize_homogeneous (φ h) g hgd))
      ((scaledHomogenize_homogeneous 1 g hgd).C_mul (φ h ^ d)) ?_
    rw [← homogeneousSlice_eq_chart_scale, homogeneousSlice_scaledHomogenize (φ h) g hgd,
      map_mul, affineChart_scaledHomogenize_one]
    simp [affineChart]
  have he := MulEquiv.irreducible_iff (f := firstCoordinateScale K (φ h) hh)
    (x := scaledHomogenize d (φ h) g)
  change Irreducible (firstCoordinateScaleHom K (φ h) (scaledHomogenize d (φ h) g)) ↔
    Irreducible (scaledHomogenize d (φ h) g) at he
  rw [hscale, irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr (pow_ne_zero d hh)).map C)] at he
  exact he.symm

/-- Prime scaling preserves all geometric bad primes away from the scaling
prime, and therefore multiplies the paper's bad-prime factor by at most `e`. -/
theorem hypersurfaceBadPrimeFactor_scaledHomogenize_le {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) {p : ℕ} (hp : p.Prime) :
    hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree (p : ℤ) f) ≤
      Real.exp 1 * hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f) := by
  classical
  let fp := scaledHomogenize f.totalDegree (p : ℤ) f
  let f1 := scaledHomogenize f.totalDegree 1 f
  have hpZ : (p : ℤ) ≠ 0 := mod_cast hp.ne_zero
  by_cases hfp : AbsolutelyIrreducible fp
  · have hf1 : AbsolutelyIrreducible f1 :=
      (scaledHomogenize_map_irreducible_iff _ (p : ℤ)
        (by simpa only [Int.coe_castRingHom, Int.cast_natCast] using
          (show (p : AlgebraicClosure ℚ) ≠ 0 by exact_mod_cast hp.ne_zero)) f le_rfl).mp hfp
    have hd : fp.totalDegree = f1.totalDegree := by
      rw [(scaledHomogenize_homogeneous (p : ℤ) f le_rfl).totalDegree
          (scaledHomogenize_ne_zero f.totalDegree hpZ hf),
        (scaledHomogenize_homogeneous (1 : ℤ) f le_rfl).totalDegree
          (scaledHomogenize_ne_zero f.totalDegree one_ne_zero hf)]
    let S := (finite_fin_hypersurface_bad_primes fp hfp
      (absolute_integer_polynomial_totalDegree_pos fp hfp)).toFinset
    let T := (finite_fin_hypersurface_bad_primes f1 hf1
      (absolute_integer_polynomial_totalDegree_pos f1 hf1)).toFinset
    have hS (q : ℕ) : q ∈ S ↔ stepanovThreshold fp.totalDegree < q ∧ HypersurfaceBadReduction fp q :=
      Set.Finite.mem_toFinset _
    have hT (q : ℕ) : q ∈ T ↔ stepanovThreshold f1.totalDegree < q ∧ HypersurfaceBadReduction f1 q :=
      Set.Finite.mem_toFinset _
    have hsub : S ⊆ insert p T := fun q hq => by
      rcases eq_or_ne q p with rfl | he
      · exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert.mpr (Or.inr ((hT q).mpr ⟨hd ▸ ((hS q).mp hq).1, ?_⟩))
        have hbad := ((hS q).mp hq).2
        let : Fact q.Prime := ⟨hbad.1⟩
        have hpK : (p : AlgebraicClosure (ZMod q)) ≠ 0 := by
          rw [Ne, CharP.cast_eq_zero_iff _ q]
          exact fun h => he ((Nat.prime_dvd_prime_iff_eq hbad.1 hp).mp h)
        rw [homogeneous_hypersurfaceBadReduction_iff _ (scaledHomogenize_homogeneous _ _ le_rfl)
          (scaledHomogenize_ne_zero _ hpZ hf)] at hbad
        rw [homogeneous_hypersurfaceBadReduction_iff _ (scaledHomogenize_homogeneous _ _ le_rfl)
          (scaledHomogenize_ne_zero _ one_ne_zero hf)]
        exact (not_congr (scaledHomogenize_map_irreducible_iff _ (p : ℤ)
          (by simpa using hpK) f le_rfl)).mp hbad
    have hnonneg (q : ℕ) : 0 ≤ Real.log q / q := by
      rcases eq_or_ne q 0 with rfl | hq
      · simp
      · exact div_nonneg (Real.log_nonneg (mod_cast Nat.one_le_iff_ne_zero.mpr hq))
          (Nat.cast_nonneg q)
    have h₁ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => hnonneg q
    have h₂ : (∑ q ∈ insert p T, Real.log q / q) ≤ (∑ q ∈ T, Real.log q / q) + Real.log p / p := by
      by_cases hmem : p ∈ T
      · rw [Finset.insert_eq_of_mem hmem]; exact le_add_of_nonneg_right (hnonneg p)
      · rw [Finset.sum_insert hmem]; exact (add_comm _ _).le
    have hpR : (0 : ℝ) < p := mod_cast hp.pos
    have h₃ : Real.log p / p ≤ 1 := (div_le_one hpR).mpr (by linarith [Real.log_le_sub_one_of_pos hpR])
    rw [hypersurfaceBadPrimeFactor_eq_exp fp hfp rfl S hS,
      hypersurfaceBadPrimeFactor_eq_exp f1 hf1 rfl T hT, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [hypersurfaceBadPrimeFactor_eq_zero fp hfp]
    exact mul_nonneg (Real.exp_pos _).le (hypersurfaceBadPrimeFactor_nonneg f1)

end
end CCDN
