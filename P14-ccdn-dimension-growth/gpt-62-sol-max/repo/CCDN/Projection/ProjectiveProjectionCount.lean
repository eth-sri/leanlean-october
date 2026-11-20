/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.ProjectiveCurveDegree
public import CCDN.Projection.ProjectionHeight
public import CCDN.Height.ProjectiveZeroLocus
public import CCDN.Height.ProjectiveBox
import CCDN.Projection.BoundedDegreeNormalizationFiber
import CCDN.Projection.BoundedBirationalHypersurfaceProjection
import CCDN.Projection.DerivativeReconstruction
import CCDN.Projection.CurveRationalInverse
import CCDN.Projection.HomogeneousProjectionEquation
import CCDN.Projection.ProjectiveLinearCountTransfer
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! Projective curve projection uses the same reconstruction as the affine case;
the proper derivative section accounts for the exceptional points. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Bounded plane projection of a projective curve, with at most `d²` exceptional points. -/
theorem exists_projective_plane_count_reduction {n d : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime]
    (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) :
    ∃ f : MvPolynomial (Fin 3) ℚ, f.IsHomogeneous d ∧ Irreducible f ∧
      ∀ B : ℝ, 1 ≤ B → projectiveCount (projectiveIdealZeroLocus I) B ≤
        projectiveCount (projectiveZeroLocus f) (projectionBoxFactor (n + 1) d * B) + d ^ 2 := by
  classical
  obtain ⟨J, hJ, hhom, hJI, hdeg, hdim⟩ := exists_homogeneous_projective_curve I hd hdegree
  obtain ⟨b, f, hb, hN, hP, rfl⟩ := exists_bounded_birational_hypersurface_projection 1 (n + 1) J d hdim
  let a := fun i => integerLinearForm (b i)
  have ha (i) : (a i).IsHomogeneous 1 := linearForm_isHomogeneous _
  have hf := homogeneous_projection_equation J hhom a ha f hP.irreducible.ne_zero hP.ker_eq
  let Q := pderiv 0 f
  let g := aeval a Q
  have hg : g.IsHomogeneous (f.totalDegree - 1) := by
    simpa only [one_mul] using (hf.pderiv (i := (0 : Fin 3))).aeval a ha
  obtain ⟨P, hQ, hrec⟩ := exists_projection_reconstruction J a (fun i => (ha i).totalDegree_le)
    hN.injective f hP.irreducible.ne_zero hdim hP.ker_eq
  refine ⟨f, hf, hP.irreducible, fun B hB => ?_⟩
  have hsub : projectiveIdealZeroLocus I ⊆ projectiveIdealZeroLocus J :=
    fun _ hx v hv he p hp => hx v hv he p (hJI hp)
  refine (projectiveCount_mono hsub le_rfl).trans ?_
  let H := projectionEntryBound (n + 1) f.totalDegree
  have hH : 0 ≤ H := (projectionEntryBound_one_le _ _).trans' zero_le_one
  have hgood := projective_integer_linear_count_transfer J b f hf hP.aeval_mem g hg f.totalDegree 1
    (fun s hs hz => linear_normalization_fiber_card_le J (fun i => a i.succ)
      (fun i => (ha i.succ).totalDegree_le) hN.injective hN.filtered _ hdim 0 s hs
      (fun x hx i => hz x hx i.succ))
    (fun z s hs hgs hzs => Finset.card_le_one.mpr (fun x hx y hy =>
      projection_injective_off_reconstruction J a Q P hrec x y (hs x hx) (hs y hy) (hgs x hx)
        (funext fun i => (hzs x hx i).trans (hzs y hy i).symm)))
    H B hH (fun i j => projectionEntryBound_le hd (hb i j))
  rw [one_mul] at hgood
  let S := projectivePoints (projectiveIdealZeroLocus J) B
  let T := S.filter (fun x => ¬ eval x.rep g ≠ 0)
  have hbad : T.card ≤ f.totalDegree * (f.totalDegree - 1) := by
    simpa only [Fintype.card_coe] using projective_section_card_le_degree J hdeg g hg hQ
      (fun x : T => x.val) Subtype.val_injective
      (fun x => (mem_projectivePoints.mp (Finset.mem_filter.mp x.property).1).2)
      (fun x => not_not.mp (Finset.mem_filter.mp x.property).2)
  have hfib := Finset.card_filter_add_card_filter_not (s := S) (p := fun x => eval x.rep g ≠ 0)
  have hheight : ((n + 1 : ℕ) : ℝ) * H * B ≤ projectionBoxFactor (n + 1) f.totalDegree * B := by
    unfold projectionBoxFactor
    gcongr
    linarith
  have himg := projectiveCount_mono (Set.Subset.rfl : projectiveZeroLocus f ⊆ projectiveZeroLocus f) hheight
  have herr : f.totalDegree * (f.totalDegree - 1) ≤ f.totalDegree ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left f.totalDegree (Nat.sub_le f.totalDegree 1)
  change S.card ≤ _
  rw [← hfib]
  exact Nat.add_le_add (hgood.trans himg) (hbad.trans herr)

end
end CCDN
