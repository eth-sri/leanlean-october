module

public import OAI.NumberTheory.DirichletL.Detector.PhysicalRows
public import OAI.NumberTheory.DirichletL.Detector.GaussianDensityBudget

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma physicalRows_common_finset {α : Type*} (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (X Y : α→ℝ) (hX : ∀k∈F,0<X k) (hY : ∀k∈F,0<Y k) :
    ∃R : Finset PhysicalRowIndex,∀k∈F,∀r,r∉R→physicalRowWeight C W0 W1 (X k) (Y k) r=0 := by
  have hf (k : {k // k∈F}) := physicalRowWeight_finite_support C W0 W1 hW0 hW1
    (X k.val) (Y k.val) (by grind) (by grind)
  let R := F.attach.biUnion (fun k=>(hf k).toFinset)
  refine ⟨R,?_⟩
  intro k hk r hr
  by_contra hn
  apply hr
  exact Finset.mem_biUnion.mpr ⟨⟨k,hk⟩,by simp,by simp_all⟩

theorem physical_selected_gaussian_reassembly {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (a : α→ℂ) (D : α→Id) (X Y : α→ℝ)
    (hX : ∀k∈F,0<X k) (hY : ∀k∈F,0<Y k) (Z : ℝ) (hZ : 0<Z)
    (q : α→ι→ℝ) (hq : ∀k∈F,∀i,0<q k i) :
    (∑k∈F,a k*(∏i,W i (q k i))*markedPhysicalProbe η C (D k) W0 W1
      (X k) (Y k) (Z*∏i,q k i))=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,a k*
        (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
          correctedCompletedT C.excluded (D k) (physicalRowMonoid η C r)
            (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j))*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  obtain ⟨R,hR⟩ := physicalRows_common_finset C W0 W1 hW0 hW1 F X Y hX hY
  have hs (k : α) (hk : k∈F) (f : PhysicalRowIndex→ℂ) :
      (∑'r,physicalRowWeight C W0 W1 (X k) (Y k) r*f r)=
      ∑r∈R,physicalRowWeight C W0 W1 (X k) (Y k) r*f r :=
    tsum_eq_sum (fun r hr=>by simp_all)
  let A (p : α×PhysicalRowIndex) := a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2
  have hh := gaussian_selected_tuple_reassembly W V hV hsep (F×ˢR) A C.excluded
    (fun p=>D p.1) (fun p=>physicalRowMonoid η C p.2)
    (fun p _=>physicalRowMonoid_norm η C p.2) Z hZ (fun p=>q p.1)
    (by grind)
  calc
    _ = ∑p∈F×ˢR,A p*(∏i,W i (q p.1 i))*correctedCompletedT C.excluded (D p.1)
      (physicalRowMonoid η C p.2) gaussianCompletedProfile (Z*∏i,q p.1 i) := by
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro k hk
        rw [markedPhysicalProbe_eq_gaussian_rows η C (D k) W0 W1 hW0 hW1
          (X k) (Y k) _ (by grind) (by grind) (mul_pos hZ (Finset.prod_pos (by grind))),hs k hk]
        rw [Finset.mul_sum]
        grind
    _ = _ := hh
    _ = _ := by
      apply tsum_congr
      intro j
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      congr 1
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hs k hk,Finset.mul_sum,Finset.sum_mul]
      grind

end SevenEighths.ProbePhysical
end

end OAI
