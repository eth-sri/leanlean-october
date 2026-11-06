module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.LowOriginalPools

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots

local notation "Id" => Ideal ActualEisensteinCubic.O

def lowUnselectedLength {K } (ell : Fin K→ℝ) (J : Finset (Fin K))  := ∑i∈J,ell i

def lowSelectedLength {K } (ell : Fin K→ℝ) (J : Finset (Fin K))  := ∑i : SelectedSlot J,ell i.val

section
variable {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6) (a : ℝ) (C : CalibrationData) (Z : ℝ) (ha : 0<a) (L c d : ℝ) (hZ : 0<Z) (slots : Fin K→Finset ActualEisensteinCubic.O) (hslots : ∀i x,x∈slots i→a*Z^(ell i)≤elementNorm x) (J : Finset (Fin K))

lemma lowLength_sum       :
    lowUnselectedLength ell J+lowSelectedLength ell J=∑i,ell i := by
  rw [lowUnselectedLength,lowSelectedLength,Finset.sum_coe_sort]
  exact Finset.sum_add_sum_compl J ell

include hell hsum in
lemma lowLength_bounds      
        :
    0≤lowUnselectedLength ell J ∧ lowUnselectedLength ell J≤1/6 ∧
    0≤lowSelectedLength ell J ∧ lowSelectedLength ell J≤1/6-lowUnselectedLength ell J := by
  have hu : 0≤lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=>hell i)
  have hs : 0≤lowSelectedLength ell J := Finset.sum_nonneg (fun i _=>hell i.val)
  grind [lowLength_sum]

include ha hZ hslots in
lemma lowUnselectedProduct_norm_lower    
           
     
      (p : LowUnselectedTuple slots J) :
    (min 1 a)^K*Z^(lowUnselectedLength ell J)≤elementNorm (∏i : J,(p i).val) := by
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤a^J.card*Z^(lowUnselectedLength ell J) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (pow_le_pow_of_le_one (le_of_lt (lt_min zero_lt_one ha)) (min_le_left _ _) hc).trans
        (pow_le_pow_left₀ (by positivity) (min_le_right _ _) _)
    _=∏i : J,a*Z^(ell i.val) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hZ,Finset.sum_coe_sort]
      rfl
    _≤_ := Finset.prod_le_prod₀ (fun _ _=>by positivity) (fun i _=>hslots i.val _ (p i).property)

include hZ in
lemma lowPhysicalScale_source       :
    lowPhysicalScale C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)=
      elementNorm C.generator*Z^(5/6:ℝ)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^(17/48:ℝ)*Z^(23/48:ℝ)=Z^(5/6:ℝ) := by rw [←Real.rpow_add hZ];norm_num
  rw [←he]
  ring

include hZ in
lemma lowPhysicalScale_nominal_bound    
      (hc : 0<c) (hL : c*Z^d≤L) :
    lowPhysicalScale C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)≤
      (elementNorm C.generator/c^2)*Z^(5/6-2*d:ℝ) := by
  
  rw [lowPhysicalScale_source C Z L hZ]
  calc
    _≤elementNorm C.generator*Z^(5/6:ℝ)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,hp,Real.rpow_sub hZ]
      ring

lemma lowSelectedScale_product      
    (Z : ℝ) (hZ : 0<Z) :
    (∏i∈Finset.univ\J,Z^(ell i))=Z^(lowSelectedLength ell J) := by
  rw [lowSelectedLength,Finset.sum_coe_sort,Real.rpow_sum_of_pos hZ]

include hell in
lemma lowSelectedCaps_product      
      (Z b : ℝ) (hZ : 1≤Z) :
    (∏i : SelectedSlot J,max 1 (b*Z^(ell i.val)))≤
      (max 1 b)^K*Z^(lowSelectedLength ell J) := by
  have hc : Fintype.card (SelectedSlot J)≤K := by
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ (Finset.univ\J))
  calc
    _≤∏i : SelectedSlot J,max 1 b*Z^(ell i.val) := by
      apply Finset.prod_le_prod₀ (fun _ _=>le_trans zero_le_one (le_max_left _ _))
      intro i hi
      apply max_le
      · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i.val))
      bound
    _=(max 1 b)^(Fintype.card (SelectedSlot J))*Z^(lowSelectedLength ell J) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        ←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
      rfl
    _≤_ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) hc) (by positivity)

end

end SevenEighths.ProbePhysical
end

end OAI
