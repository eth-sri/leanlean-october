import RequestProject.PresCocycleCoverCoordinates
import RequestProject.CoverFoxPrefixSum
import RequestProject.CoverComplexFinsupp
import RequestProject.Tac


namespace FiniteChains.PresModel.PresCocycleCover
open Comb
variable {α J : Type u} [DecidableEq α] (w : J → List (α × Bool))
  (N : Subgroup (FreeGroup α)) [N.Normal]

omit [DecidableEq α] in
theorem quotient_wordVal (l : List (α × Bool)) :
    wordVal (qof N) l = (QuotientGroup.mk (FreeGroup.mk l) : FreeGroup α ⧸ N) := by
  have h : FreeGroup.lift (qof N) = QuotientGroup.mk' N := by
    aesop
  exact DFunLike.congr_fun h _

variable (hword : ∀ j, FreeGroup.mk (w j) ∈ N)

include hword in
omit [DecidableEq α] in
theorem quotient_relators_close (j : J) : wordVal (qof N) (w j) = 1 := by
  simp_all [quotient_wordVal]

abbrev QuotientCover := Space w _ (quotient_relators_close w N hword)
abbrev quotientProjection := projection w _ (quotient_relators_close w N hword)
abbrev quotientCovering := covering w _ (quotient_relators_close w N hword)

/-- The actual geometric attaching boundary is exactly the finitely supported Fox boundary. -/
theorem quotient_relator_boundary_coordinates
    c :
    fsCoords N α
      (generatorCoordinates w (qof N) (quotient_relators_close w N hword)
        (presCoverRelatorGeneratorBoundary w (quotientProjection w N hword)
          (quotientCovering w N hword) c)) =
      coverSecondBoundary N (fun j => FreeGroup.mk (w j))
        (fsCoords N J (relatorCoordinates w (qof N)
          (quotient_relators_close w N hword) c)) := by
  classical
  lin_ind c p n =>
    have hone : fsCoords N α
        (generatorCoordinates w _ _
          (presCoverRelatorGeneratorBoundary w _
            (quotientCovering w N hword) (Finsupp.single p 1))) =
        coverSecondBoundary N (fun j => FreeGroup.mk (w j))
          (fsCoords N J (relatorCoordinates w _
            _ (Finsupp.single p 1))) := by
      rw [presCoverRelatorGeneratorBoundary_single]
      simp only [map_sum, map_smul, generatorCoordinates_single, relatorCoordinates_single,
        relatorLetterMidpoint_sheet, fsCoords_single]
      rw [coverSecondBoundary_single]
      apply Finsupp.ext
      intro i
      simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply,
        coe_coverFoxGradient, foxVec, smul_eq_mul]
      rw [coverFox_mk_prefix_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hp : prefixVal w (qof N) p.val.2 k.val =
          (QuotientGroup.mk (FreeGroup.mk ((w p.val.2).take k.val))) :=
        quotient_wordVal N _
      rw [hp]
      by_cases hi : i = ((w p.val.2)[k.val]).1
      · cases hb : ((w p.val.2)[k.val]).2 <;>
          simp [hi, qof, MonoidAlgebra.single_mul_single, ← mul_assoc]
      simp_all
    have hs : Finsupp.single p n = n • Finsupp.single p (1) := by simp
    rw [hs]
    simpa only [map_smul, map_zsmul] using congrArg _ hone

/-- Injectivity of the actual Fox boundary annihilates actual strict cover two-cycles. -/
theorem quotient_two_cycle_zero (hpos : ∀ j, 0 < (w j).length)
    (hinj : Function.Injective (coverSecondBoundary N (fun j => FreeGroup.mk (w j))))
    (c : StrictOrdTri (QuotientCover w N hword) →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx (QuotientCover w N hword)) c = 0) : c = 0 := by
  let r := presCoverRelatorChain w (quotientProjection w N hword)
    (quotientCovering w N hword) hpos c
  have hr : presCoverRelatorGeneratorBoundary w _
      (quotientCovering w N hword) r = 0 :=
    (presCoverCollapsedRelatorBoundary_eq_zero_iff_generator w
      _ _ r).mp
      (presCover_cycle_collapsed_relator_boundary_zero w _
        _ hpos c hc)
  have hz : fsCoords N J (relatorCoordinates w _
      _ r) = 0 := by
    apply hinj
    simp [← quotient_relator_boundary_coordinates, hr, map_zero]
  have hr0 : r = 0 := by
    simp_all
  exact presCoverRelatorChain_cycle_injective w _
    (quotientCovering w N hword) hpos c 0 hc (map_zero _) (by grind)
