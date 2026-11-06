module
public import GafniTao.WooleySourceMean
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# The source integer model specializes to the finite box model

This file embeds a coefficient family on `1,...,Q` into Wooley's actual
finitely supported integer sequence space.  The embedding is injective, so
no coefficients or residue classes are merged.
-/

open Finset Polynomial

namespace GafniTao

noncomputable section

/-- The literal source-box embedding `n : Fin Q ↦ n+1 : ℤ`. -/
def wooleyBoxIndexEmbedding (Q : ℕ) : Fin Q ↪ ℤ where
  toFun n := ((n : ℕ) + 1 : ℕ)
  inj' := by
    intro m n h
    apply Fin.ext
    change (((m : ℕ) + 1 : ℕ) : ℤ) = (((n : ℕ) + 1 : ℕ) : ℤ) at h
    grind

@[simp] theorem wooleyBoxIndexEmbedding_apply {Q : ℕ} (n : Fin Q) :
    wooleyBoxIndexEmbedding Q n = (((n : ℕ) + 1 : ℕ) : ℤ) := rfl

/-- A finite box coefficient family, viewed as a finitely supported integer
sequence without changing its values. -/
def wooleyBoxSourceSequence {Q : ℕ} (gamma : Fin Q → ℂ) :
    WooleySourceSequence :=
  Finsupp.embDomain (wooleyBoxIndexEmbedding Q)
    (Finsupp.equivFunOnFinite.symm gamma)

section
variable {Q : ℕ} (gamma : Fin Q → ℂ)
include Q gamma
@[simp] theorem wooleyBoxSourceSequence_apply_index (n : Fin Q) :
    wooleyBoxSourceSequence gamma (wooleyBoxIndexEmbedding Q n) = gamma n := by
  rw [wooleyBoxSourceSequence, Finsupp.embDomain_apply_self]
  rfl

/-- The support is exactly the image of the nonzero box coefficients. -/
theorem wooleyBoxSourceSequence_support :
    (wooleyBoxSourceSequence gamma).support =
      (Finset.univ.filter fun n : Fin Q => gamma n ≠ 0).map
        (wooleyBoxIndexEmbedding Q) := by
  rw [wooleyBoxSourceSequence, Finsupp.support_embDomain]
  ext n
  simp
end

/-- The source and box `L²` masses agree exactly. -/
theorem wooleyBoxSourceSequence_massSq {Q : ℕ} (gamma : Fin Q → ℂ) :
    wooleySourceMassSq (wooleyBoxSourceSequence gamma) =
      wooleyWeightedMassSq gamma := by
  rw [wooleySourceMassSq, wooleyWeightedMassSq,
    wooleyBoxSourceSequence_support]
  rw [Finset.sum_map]
  simp only [wooleyBoxSourceSequence_apply_index]
  pm_2821

/-- Residue `L²` masses agree under the box embedding. -/
theorem wooleySourceResidueMassSq_box {Q q : ℕ}
    (gamma : Fin Q → ℂ) (xi : ZMod q) :
    wooleySourceResidueMassSq (wooleyBoxSourceSequence gamma) q xi =
      wooleyWeightedResidueMassSq gamma xi := by
  unfold wooleySourceResidueMassSq wooleyWeightedResidueMassSq
    wooleyResidueClass
  rw [wooleyBoxSourceSequence_support]
  pm_327 Finset.filter_map Finset.sum_map Function.comp_apply wooleyBoxSourceSequence_apply_index
  simp only [wooleyBoxIndexEmbedding_apply]
  have hcast (n : Fin Q) :
      (((((n : ℕ) + 1 : ℕ) : ℤ) : ZMod q)) =
        ((((n : ℕ) + 1 : ℕ) : ZMod q)) := by norm_num
  simp_rw [hcast]
  change
    (∑ n ∈ ((Finset.univ : Finset (Fin Q)).filter
        fun n => gamma n ≠ 0).filter
        (fun n : Fin Q => ((((n : ℕ) + 1 : ℕ) : ZMod q)) = xi),
        ‖gamma n‖ ^ 2) =
      ∑ n ∈ (Finset.univ : Finset (Fin Q)).filter
        (fun n : Fin Q => ((((n : ℕ) + 1 : ℕ) : ZMod q)) = xi),
        ‖gamma n‖ ^ 2
  pm_2822

section
variable {Q k q : ℕ} [NeZero q]
include Q k q
/-- The monomial source phase agrees with the earlier literal box phase. -/
theorem wooleySourcePolynomialPhase_box_monomial (alpha : Fin k → ZMod q) (n : Fin Q) :
    wooleySourcePolynomialPhase (wooleyMonomialPolynomialSystem k) alpha
        (wooleyBoxIndexEmbedding Q n) =
      wooleyMonomialGridPhase q k Q alpha n := by
  pm_8730 wooleyMonomialGridPhase
  simp [wooleyMonomialPolynomialSystem, wooleyBoxIndexEmbedding]

/-- The source phase agrees with the finite-box polynomial phase for every
integer polynomial system, not merely the monomial specialization. -/
theorem wooleySourcePolynomialPhase_box (phi : WooleyPolynomialSystem k)
    (alpha : Fin k → ZMod q) (n : Fin Q) :
    wooleySourcePolynomialPhase phi alpha (wooleyBoxIndexEmbedding Q n) =
      wooleyPolynomialGridPhase phi q Q alpha n := by
  pm_8730 wooleyPolynomialGridPhase
  rfl

/-- General polynomial-system version of the source/box global-sum bridge. -/
theorem wooleySourcePolynomialSum_box (phi : WooleyPolynomialSystem k)
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod q) :
    wooleySourcePolynomialSum phi (wooleyBoxSourceSequence gamma) alpha =
      wooleyPolynomialWeightedGridSum phi q gamma alpha := by
  pm_8482 wooleyPolynomialWeightedGridSum wooleySourcePolynomialPhase_box
  pm_2821
end

/-- General polynomial-system version of the residue-sum bridge. -/
theorem wooleySourcePolynomialResidueSum_box
    {Q k q qH : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod q) (xi : ZMod qH) :
    wooleySourcePolynomialResidueSum phi (wooleyBoxSourceSequence gamma)
        alpha xi =
      wooleyPolynomialWeightedResidueGridSum phi q gamma alpha xi := by
  unfold wooleySourcePolynomialResidueSum
    wooleyPolynomialWeightedResidueGridSum wooleyResidueClass
  pm_6867 wooleySourcePolynomialPhase_box
  pm_2823
  pm_2824 wooleyPolynomialGridPhase phi q
  pm_2822

theorem wooleySourceNormalizedPolynomialSum_box
    {Q k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod q) :
    wooleySourceNormalizedPolynomialSum phi
        (wooleyBoxSourceSequence gamma) alpha =
      wooleyPolynomialNormalizedGridSum phi q gamma alpha := by
  unfold wooleySourceNormalizedPolynomialSum
    wooleyPolynomialNormalizedGridSum
  rw [wooleyBoxSourceSequence_massSq, wooleySourcePolynomialSum_box]

theorem wooleySourceNormalizedPolynomialResidueSum_box
    {Q k q qH : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod q) (xi : ZMod qH) :
    wooleySourceNormalizedPolynomialResidueSum phi
        (wooleyBoxSourceSequence gamma) alpha xi =
      wooleyPolynomialNormalizedResidueGridSum phi q gamma alpha xi := by
  unfold wooleySourceNormalizedPolynomialResidueSum
    wooleyPolynomialNormalizedResidueGridSum
  rw [wooleySourceResidueMassSq_box,
    wooleySourcePolynomialResidueSum_box]

/-- General polynomial-system source mean equals its finite-box realization. -/
theorem wooleySourcePolynomialMean_box
    {Q k q s : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : Fin Q → ℂ) :
    wooleySourcePolynomialMean s q phi (wooleyBoxSourceSequence gamma) =
      wooleyPolynomialWeightedGridMean phi s q gamma := by
  unfold wooleySourcePolynomialMean wooleyPolynomialWeightedGridMean
  simp_rw [wooleySourceNormalizedPolynomialSum_box]

/-- General polynomial-system conditioned source mean equals its finite-box
realization. -/
theorem wooleySourcePolynomialConditionedMean_box
    {Q k q qH s : ℕ} [NeZero q] [NeZero qH]
    (phi : WooleyPolynomialSystem k) (gamma : Fin Q → ℂ) :
    wooleySourcePolynomialConditionedMean s q qH phi
        (wooleyBoxSourceSequence gamma) =
      wooleyPolynomialConditionedGridMean phi s q qH gamma := by
  unfold wooleySourcePolynomialConditionedMean
    wooleyPolynomialConditionedGridMean
  pm_5502 wooleySourceNormalizedPolynomialResidueSum_box

/-- The source global sum is literally the earlier box sum. -/
theorem wooleySourcePolynomialSum_box_monomial
    {Q k q : ℕ} [NeZero q] (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod q) :
    wooleySourcePolynomialSum (wooleyMonomialPolynomialSystem k)
        (wooleyBoxSourceSequence gamma) alpha =
      wooleyWeightedGridSum q k gamma alpha := by
  pm_8482 wooleyWeightedGridSum wooleySourcePolynomialPhase_box_monomial
  pm_2821

/-- Residue exponential sums agree under the box embedding. -/
theorem wooleySourcePolynomialResidueSum_box_monomial
    {Q k q qH : ℕ} [NeZero q] (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod q) (xi : ZMod qH) :
    wooleySourcePolynomialResidueSum (wooleyMonomialPolynomialSystem k)
        (wooleyBoxSourceSequence gamma) alpha xi =
      wooleyWeightedResidueGridSum q k gamma alpha xi := by
  unfold wooleySourcePolynomialResidueSum wooleyWeightedResidueGridSum
    wooleyResidueClass
  pm_6867 wooleySourcePolynomialPhase_box_monomial
  pm_2823
  pm_2824 wooleyMonomialGridPhase q k
  pm_2822

theorem wooleySourceNormalizedPolynomialSum_box_monomial
    {Q k q : ℕ} [NeZero q] (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod q) :
      wooleySourceNormalizedPolynomialSum
        (wooleyMonomialPolynomialSystem k)
        (wooleyBoxSourceSequence gamma) alpha =
      wooleyWeightedNormalizedGridSum q k gamma alpha := by
  unfold wooleySourceNormalizedPolynomialSum
    wooleyWeightedNormalizedGridSum
  rw [wooleyBoxSourceSequence_massSq,
    wooleySourcePolynomialSum_box_monomial]

theorem wooleySourceNormalizedPolynomialResidueSum_box_monomial
    {Q k q qH : ℕ} [NeZero q] (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod q) (xi : ZMod qH) :
      wooleySourceNormalizedPolynomialResidueSum
        (wooleyMonomialPolynomialSystem k)
        (wooleyBoxSourceSequence gamma) alpha xi =
      wooleyWeightedNormalizedResidueGridSum q k gamma alpha xi := by
  unfold wooleySourceNormalizedPolynomialResidueSum
    wooleyWeightedNormalizedResidueGridSum
  rw [wooleySourceResidueMassSq_box,
    wooleySourcePolynomialResidueSum_box_monomial]

/-- The source global mean recovers the finite box polynomial mean. -/
theorem wooleySourcePolynomialMean_box_monomial
    {Q k q s : ℕ} [NeZero q] (gamma : Fin Q → ℂ) :
      wooleySourcePolynomialMean s q (wooleyMonomialPolynomialSystem k)
        (wooleyBoxSourceSequence gamma) =
      wooleyWeightedGridMean s k q gamma := by
  unfold wooleySourcePolynomialMean wooleyWeightedGridMean
  simp_rw [wooleySourceNormalizedPolynomialSum_box_monomial]

/-- The source conditioned mean recovers the finite box conditioned mean. -/
theorem wooleySourcePolynomialConditionedMean_box_monomial
    {Q k q qH s : ℕ} [NeZero q] [NeZero qH]
    (gamma : Fin Q → ℂ) :
      wooleySourcePolynomialConditionedMean s q qH
        (wooleyMonomialPolynomialSystem k)
        (wooleyBoxSourceSequence gamma) =
      wooleyWeightedConditionedGridMean s k q qH gamma := by
  unfold wooleySourcePolynomialConditionedMean
    wooleyWeightedConditionedGridMean
  pm_5502 wooleySourceNormalizedPolynomialResidueSum_box_monomial

end

end GafniTao
