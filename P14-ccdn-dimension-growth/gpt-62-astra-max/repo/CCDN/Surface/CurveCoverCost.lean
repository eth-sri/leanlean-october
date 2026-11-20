/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Surface.CurveComponents
public import CCDN.Algebra.PolynomialPredicates
import CCDN.Surface.DegreeOneCount
import CCDN.Curve.AffineCurveCount

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real

private lemma curve_cost {δ : ℕ} (hδ : 2 ≤ δ) {B M : ℝ} (hB : 1 ≤ B) (hM : (δ:ℝ) ≤ M) :
    curveBound δ B ≤ 2 * exp 1 * δ * (B^(1/2:ℝ)*(log B+1)^3 + M^3) := by
  have hd : (2:ℝ) ≤ δ := by exact_mod_cast hδ
  have hd0 : (0:ℝ) < δ := by linarith
  have h := log_nonneg hB
  have hM0 : 0 ≤ M := by linarith
  have hB0 : 0 < B := by linarith
  have he : 1 ≤ exp 1 := one_le_exp (by norm_num)
  unfold curveBound
  by_cases hs : (δ:ℝ) ≤ log B+1
  · have hp := rpow_le_rpow_of_exponent_le hB (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hd)
    calc
      _ ≤ (δ:ℝ)*(log B+1)^2*B^(1/2:ℝ)*(2*(log B+1)) := by rw [pow_succ' _ 2]; gcongr; linarith
      _ = 2*δ*(B^(1/2:ℝ)*(log B+1)^3) := by ring
      _ ≤ _ := by gcongr <;> nlinarith [pow_nonneg hM0 3]
  · have hp : B^(1/(δ:ℝ)) ≤ exp 1 := by rw [rpow_def_of_pos hB0,exp_le_exp,mul_one_div,div_le_one hd0]; linarith
    calc
      _ ≤ (δ:ℝ)*M^2*exp 1*(2*M) := by rw [pow_succ' _ 2]; gcongr; linarith
      _ = 2*exp 1*δ*M^3 := by ring
      _ ≤ _ := by exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)

/-- The lines cost a single surface term. Per unit of degree a nonlinear curve
costs at most a cubic polylog times `√B` below the logarithmic cutoff,
and at most the cube of the degree cap above it. -/
theorem surface_curve_cover_cost :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : IntegerPolynomial 3), HasAbsIrreducibleTopForm f → 3 ≤ f.totalDegree →
      ∀ (S : Finset (Ideal (CoordinatePolynomial 3))) (δ : Ideal (CoordinatePolynomial 3) → ℕ)
        (M E B : ℝ), 1 ≤ B → 0 ≤ M →
        (∀ I ∈ S, IsSurfaceCurve (rationalEquation f) I (δ I) ∧ 0 < δ I) →
        (∀ I ∈ S, (δ I:ℝ) ≤ M) → (∑ I ∈ S, (δ I:ℝ)) ≤ E →
        (count (⋃ I ∈ S, idealZeroLocus I) B : ℝ) ≤
          C * ((f.totalDegree:ℝ)^6 * B + E * (B^(1/2:ℝ)*(log B+1)^3 + M^3)) := by
  classical
  obtain ⟨L,hL,line⟩ := surface_degree_one_component_contribution
  obtain ⟨K,hK,curve⟩ := affine_curve_count 3 (by omega)
  let c := K * (2*exp 1)
  have hc : 0 ≤ c := by positivity
  refine ⟨L+1+c,by positivity,?_⟩
  intro f top hd S δ M E B hB hM hS cap budget
  let T := S.filter (fun I => δ I = 1)
  let U := S.filter (fun I => δ I ≠ 1)
  let W := B^(1/2:ℝ)*(log B+1)^3 + M^3
  have ht := log_nonneg hB
  have hW : 1 ≤ W := by
    have := one_le_mul_of_one_le_of_one_le (one_le_rpow hB (by norm_num : (0:ℝ)≤1/2)) (one_le_pow₀ (n:=3) (show 1 ≤ log B+1 by linarith))
    dsimp [W]; linarith [pow_nonneg hM 3]
  have hE : 0 ≤ E := (sum_nonneg (fun _ _ => Nat.cast_nonneg _)).trans budget
  have hlin := line f top hd B (by linarith) T (fun I h => by
    obtain ⟨hI,e⟩ := mem_filter.mp h
    exact e ▸ (hS I hI).1)
  have hcard : (T.card:ℝ) ≤ E := by
    calc
      _ = ∑ _ ∈ T, (1:ℝ) := by simp
      _ ≤ ∑ I ∈ T, (δ I:ℝ) := sum_le_sum fun I hi => by simp [(mem_filter.mp hi).2]
      _ ≤ ∑ I ∈ S, (δ I:ℝ) := by gcongr; exact filter_subset ..
      _ ≤ _ := budget
  have hcur : (count (⋃ I ∈ U, idealZeroLocus I) B : ℝ) ≤ c*(E*W) := by
    calc
      _ ≤ ∑ I ∈ U, (count (idealZeroLocus I) B : ℝ) := by exact_mod_cast count_biUnion_finset_le U idealZeroLocus B
      _ ≤ ∑ I ∈ U, (δ I:ℝ)*(c*W) := by
        apply sum_le_sum; intro I hi
        obtain ⟨hI,hn⟩ := mem_filter.mp hi
        obtain ⟨hP,hp⟩ := hS I hI
        have hh := mul_le_mul_of_nonneg_left (curve_cost (by omega : 2 ≤ δ I) hB (cap I hI)) hK.le
        exact (curve I hP.isPrime _ hp hP.degree B hB).trans (hh.trans_eq (by dsimp only [c,W]; ring))
      _ = (∑ I ∈ U, (δ I:ℝ))*(c*W) := (sum_mul ..).symm
      _ ≤ E*(c*W) := by gcongr; exact (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (by intros; positivity)).trans budget
      _ = _ := by ring
  have he : S = T ∪ U := (filter_union_filter_not_eq ..).symm
  have cov := count_union_le (⋃ I ∈ T, idealZeroLocus I) (⋃ I ∈ U, idealZeroLocus I) B
  rw [he,Finset.set_biUnion_union]
  have htotal := (Nat.cast_le (α:=ℝ)).mpr cov
  push_cast at htotal
  have hl : 0 ≤ (f.totalDegree:ℝ)^6*B := by positivity
  have hw := le_mul_of_one_le_right hE hW
  change _ ≤ (L+1+c)*(_+E*W)
  nlinarith only [htotal,hlin,hcur,hcard,hw, mul_nonneg hc hl, mul_nonneg (le_of_lt hL) (mul_nonneg hE (by linarith : 0 ≤ W)), hl]

end
end CCDN
