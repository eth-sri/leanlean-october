module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.LowSourceScales

@[expose] public section

namespace OAI


open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss


section
variable {K : ℕ} (C : CalibrationData) (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6) (b Z : ℝ) (hb : 1≤b) (hZ : 1≤Z) (slots : Fin K→Finset ActualEisensteinCubic.O)

lemma elementNorm_finset_prod {ι : Type*} (F : Finset ι) (p : ι→ActualEisensteinCubic.O) :
    elementNorm (∏i∈F,p i)=∏i∈F,elementNorm (p i) := by
  induction F using Finset.induction_on with
  | empty => simp [elementNorm_one]
  | @insert i F hi ih => simp only [Finset.prod_insert hi,elementNorm_mul,ih]

lemma lowUnselectedProduct_norm_ge_one    
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    1≤elementNorm (∏i : J,(a i).val) := by
  have hn : (∏i : J,(a i).val)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hslots i.val _ (a i).property)
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hn))

include hell hsum hb hZ in
lemma lowUnselectedProduct_norm_bound    
       
           
    (hslots : ∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(a i).val)≤b^K*Z^(1/6:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hsub : ∑i∈J,ell i≤1/6 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hell i)).trans hsum
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,b*Z^(ell i.val) := Finset.prod_le_prod₀ (fun _ _=>by unfold elementNorm;positivity)
      (fun i _=>hslots i.val _ (a i).property)
    _=b^J.card*Z^(∑i∈J,ell i) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hz,Finset.sum_coe_sort]
    _≤b^K*Z^(1/6:ℝ) := (by gcongr <;> first | assumption | positivity | linarith)

include C hell hsum hb in
theorem eventually_original_slot_scales      
            :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧
      ∀(slots : Fin K→Finset ActualEisensteinCubic.O)(_hslots : ∀i x,x∈slots i→x≠0),
      (∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))→
      ∀(J : Finset (Fin K))(a : LowUnselectedTuple slots J),
      let L := elementNorm (∏i : J,(a i).val)
      1≤Z^(23/48:ℝ)/L ∧
      1≤(Z^(23/48:ℝ)/L)^2/lowPhysicalScale C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm C.generator/L)*Z^(3/16+(23/96)*δ:ℝ) := by
  filter_upwards [eventually_compensated_source_scales C (b^K)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro slots hslots hnorm J a
  exact hZ.2.2 _ (lowUnselectedProduct_norm_ge_one slots hslots J a)
    (lowUnselectedProduct_norm_bound ell hell hsum b Z hb hZ.1 slots hnorm J a)

end

end SevenEighths.ProbePhysical


end OAI
