/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Surface.CurveCoverCost
import CCDN.Surface.CompleteIntersectionDegreeBudget
import CCDN.Surface.TopFormAuxiliary
import CCDN.Surface.TopFormBadPrimes
import CCDN.Algebra.FieldMapIrreducible
import CCDN.Analysis.SmallDegreeSurfaceNumerics

@[expose] public section
namespace CCDN
open MvPolynomial Real Finset
noncomputable section

/-- At degree sixteen the fourth power of the Bézout budget is linear in `B`. -/
theorem affine_surface_count_large_degree : ∃ C : ℝ, 0 < C ∧ ∀ f : IntegerPolynomial 3,
    HasAbsIrreducibleTopForm f → 16 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
    (count (zeroLocus (rationalEquation f)) B : ℝ) ≤ C * (f.totalDegree:ℝ)^18 * B := by
  obtain ⟨C,hC,curves⟩ := surface_curve_cover_cost
  let K := topFormAuxiliaryConstant 1
  have hK : 0 < K := topFormAuxiliaryConstant_pos 1
  let H := (Nat.factorial 3:ℝ)/(1/4:ℝ)^3*exp (1/4)
  have hH : 0 ≤ H := by positivity
  refine ⟨C*(1+K*H+K^4),by positivity,?_⟩
  intro f top hd B hB
  let d := (f.totalDegree:ℝ)
  have hd1 : 1 ≤ d := by dsimp [d]; exact_mod_cast (show 1 ≤ f.totalDegree by omega)
  have hd0 : 0 < d := by linarith
  have hB0 : 0 < B := by linarith
  let E := K*d^(9/2:ℝ)*B^(1/4:ℝ)
  obtain ⟨g,-,proper,hdeg,hzero⟩ := top_form_auxiliary_rational (n:=1) f top hB
  obtain ⟨S,δ,hS,cover,budget⟩ := integer_surface_section (rational_irreducible_of_charZero_map f
    (absolute_irreducible_of_top_homogeneousComponent_irreducible f top)) proper hzero
  have hg : (g.totalDegree:ℝ) ≤ K*d^(7/2:ℝ)*B^(1/sqrt d) := by simpa only [← sqrt_eq_rpow,K,d] using (by norm_num at hdeg; simpa [one_div] using hdeg : (g.totalDegree:ℝ) ≤ K*d^(7/2:ℝ)*B^(1/d^(1/2:ℝ)))
  have hsum : (∑ I ∈ S, (δ I:ℝ)) ≤ E := by
    have hp : 1/sqrt d ≤ 1/4 := one_div_le_one_div_of_le (by norm_num) (le_sqrt_of_sq_le (by dsimp [d]; exact_mod_cast hd))
    apply budget.trans ((mul_le_mul_of_nonneg_left hg hd0.le).trans ?_)
    dsimp only [E]; rw [show (9/2:ℝ)=7/2+1 by norm_num,rpow_add_one hd0.ne']
    calc d*(K*d^(7/2:ℝ)*B^(1/sqrt d)) = K*(d^(7/2:ℝ)*d)*B^(1/sqrt d) := by ring
      _ ≤ _ := by gcongr
  have hcount := curves f top (by omega) S δ E E B hB (by positivity) (fun I h => ⟨(hS I h).toIsSurfaceCurve,(hS I h).pos⟩)
    (fun I h => (single_le_sum (fun i _ => Nat.cast_nonneg (α:=ℝ) (δ i)) h).trans hsum) hsum
  have hfour : E^4 = K^4*d^18*B := by
    dsimp [E]; rw [mul_pow,mul_pow,← rpow_mul_natCast hd0.le,← rpow_mul_natCast hB0.le]; norm_num
  have ht := log_nonneg hB
  have hp := logarithm_add_one_pow_le_rpow 3 (by norm_num : (0:ℝ)<1/4) hB
  have hpow : d^(9/2:ℝ) ≤ d^18 := by simpa using rpow_le_rpow_of_exponent_le hd1 (by norm_num : (9/2:ℝ)≤18)
  have hlow : E*(B^(1/2:ℝ)*(log B+1)^3) ≤ K*H*d^18*B := by
    calc _ ≤ (K*d^18*B^(1/4:ℝ))*(B^(1/2:ℝ)*(H*B^(1/4:ℝ))) := by dsimp only [E]; gcongr
         _ = (K*H*d^18)*B^(1/4+1/2+1/4:ℝ) := by rw [rpow_add hB0,rpow_add hB0]; ring
         _ = _ := by norm_num
  have hd6 := pow_le_pow_right₀ hd1 (by omega : 6 ≤ 18)
  have hz : count (zeroLocus (rationalEquation f)) B ≤ count (⋃ I ∈ S, idealZeroLocus I) B :=
    count_le_of_box_imp fun x hx hf => cover x hx (mem_integer_zeroLocus.mp hf)
  apply (Nat.cast_le (α:=ℝ)).mpr hz |>.trans (hcount.trans ?_)
  change C*(d^6*B+E*(_+E^3)) ≤ _
  rw [mul_add E,← pow_succ',hfour]
  calc _ ≤ C*(d^18*B+K*H*d^18*B+K^4*d^18*B) := by rw [← add_assoc]; gcongr
       _ = _ := by dsimp only [d]; ring

end
end CCDN
