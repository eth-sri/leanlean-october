module

public import CCDN.Statements
import CCDN.Algebra.ProjectiveChartIdeal
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.Plane.ProjectivePlaneLinearCount
import CCDN.Projection.BoundedDegreePreservingProjection
import CCDN.Projection.DegreePreservingProjectionBox
import CCDN.Projection.ProjectivePlaneProjection
import CCDN.Projection.ScaleAbsorption

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private def projectivePermutedIdeal {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : Equiv.Perm (Fin (n + 1))) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  RingHom.ker ((Ideal.Quotient.mkₐ K I).comp (renameEquiv K e).toAlgHom)

private lemma mem_projectivePermutedIdeal {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : Equiv.Perm (Fin (n + 1)))
    (f : MvPolynomial (Fin (n + 1)) K) :
    f ∈ projectivePermutedIdeal I e ↔ rename e f ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem

private instance projectivePermutedIdeal_isPrime {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (e : Equiv.Perm (Fin (n + 1))) : (projectivePermutedIdeal I e).IsPrime :=
  RingHom.ker_isPrime _

private theorem projectiveCurveDegree_permuted {K : Type*} [Field K] {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : Equiv.Perm (Fin (n + 1)))
    (hdegree : HasProjectiveCurveDegree I d) :
    HasProjectiveCurveDegree (projectivePermutedIdeal I e) d := by
  obtain ⟨N, c, hN⟩ := hdegree
  refine ⟨N, c, fun M hM => ?_⟩
  let ψ := (Ideal.Quotient.mkₐ K I).comp (renameEquiv K e).toAlgHom
  let φ := Ideal.kerLiftAlg ψ
  let V := homogeneousCoordinateSpace (RingHom.ker ψ) M
  have he : V.map φ.toLinearMap = homogeneousCoordinateSpace I M := by
    ext x; constructor
    · rintro hx
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hu
      exact Submodule.mem_map.mpr ⟨rename e f, hf.rename_isHomogeneous, rfl⟩
    · rintro hx
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
      refine Submodule.mem_map.mpr ⟨(Ideal.Quotient.mk (RingHom.ker ψ)) (rename e.symm f),
        Submodule.mem_map.mpr ⟨rename e.symm f, hf.rename_isHomogeneous, rfl⟩, ?_⟩
      exact congrArg (Ideal.Quotient.mk I) ((renameEquiv K e).apply_symm_apply f)
  have hh := (Submodule.equivMapOfInjective φ.toLinearMap (Ideal.kerLiftAlg_injective ψ) V).finrank_eq
  rw [he] at hh
  change ((projectiveHilbertFunction (projectivePermutedIdeal I e) M : ℕ) : ℤ) = _
  rw [show projectiveHilbertFunction (projectivePermutedIdeal I e) M =
    projectiveHilbertFunction I M from hh]
  exact hN M hM

private theorem projectiveCount_le_permuted {n : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) (e : Equiv.Perm (Fin (n + 1))) (B : ℝ) :
    projectiveCount (projectiveIdealZeroLocus I) B ≤
      projectiveCount (projectiveIdealZeroLocus (projectivePermutedIdeal I e)) B := by
  let L : (Fin (n + 1) → ℚ) →ₗ[ℚ] (Fin (n + 1) → ℚ) :=
    { toFun := fun v => v ∘ e, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hLinj : Function.Injective L := fun v w he =>
    funext fun j => by simpa [L] using congrFun he (e.symm j)
  let P := Projectivization.map L hLinj
  refine Finset.card_le_card_of_injOn P (fun x hx => ?_) (Projectivization.map_injective _ _).injOn
  obtain ⟨hxB, hxI⟩ := mem_projectivePoints.mp hx
  refine mem_projectivePoints.mpr ⟨?_, fun v hv hvx f hf => ?_⟩
  · conv_lhs => rw [← x.mk_rep]
    dsimp only [P]
    rw [Projectivization.map_mk, Projectivization.mulHeight_mk]
    change Height.mulHeight (x.rep ∘ e) ≤ B
    rwa [Height.mulHeight_comp_equiv, projective_rep_height]
  · have hxperm : L x.rep ≠ 0 := fun h => x.rep_nonzero (hLinj (by simpa only [map_zero] using h))
    have he : Projectivization.mk ℚ v hv = Projectivization.mk ℚ (L x.rep) hxperm := by
      change Projectivization.mk ℚ v hv = P (Projectivization.mk ℚ x.rep x.rep_nonzero)
      rw [x.mk_rep]; exact hvx
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℚ _ _ _ _).mp he
    have hw : (c : ℚ) • x.rep ≠ 0 := smul_ne_zero c.ne_zero x.rep_nonzero
    have hwx : Projectivization.mk ℚ ((c : ℚ) • x.rep) hw = x :=
      ((Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mpr ⟨c, rfl⟩).trans x.mk_rep
    have hh := hxI ((c : ℚ) • x.rep) hw hwx (rename e f) ((mem_projectivePermutedIdeal I e f).mp hf)
    rw [eval_rename] at hh
    have hv' : ((c : ℚ) • x.rep) ∘ e = v := hc
    rwa [hv'] at hh

private theorem exists_projective_plane_count_reduction {n d : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime] (hX : X 0 ∉ I)
    (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) :
    ∃ f : MvPolynomial (Fin 3) ℚ, f.IsHomogeneous d ∧ Irreducible f ∧
      ∀ B : ℝ, 1 ≤ B →
        projectiveCount (projectiveIdealZeroLocus I) B ≤
          projectiveCount (projectiveZeroLocus f) (projectionBoxFactor n d * B) + d ^ 2 := by
  classical
  let J := projectiveChartIdeal I
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hfir, hfd, hker, hcount⟩ :=
    exists_bounded_projection_card_le J d hd (projectiveChartIdeal_degree I hX hdegree)
  have hfI : aeval ![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁] f ∈ J :=
    (hker f).mpr dvd_rfl
  refine ⟨scaledHomogenize d 1 f, scaledHomogenize_homogeneous 1 f hfd.le,
    by simpa only [hfd] using scaledHomogenize_irreducible f hfir one_ne_zero, fun B hB => ?_⟩
  let S := projectivePoints (projectiveIdealZeroLocus I) B
  let T := S.filter fun x => x.rep 0 ≠ 0
  let U := S.filter fun x => ¬ x.rep 0 ≠ 0
  let R := T.image projectiveAffineCoordinates
  let π : RatPoint n → RatPoint 2 := fun z =>
    ![eval z (momentCoordinate ℚ n k₀), eval z (momentCoordinate ℚ n k₁)]
  have hR : ∀ z ∈ R, ∀ g ∈ J, eval z g = 0 := fun z hz => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
    exact projectiveChartIdeal_point I hX x (mem_projectivePoints.mp hxS).2 hx0
  have hc := hcount R hR
  have hRT : R.card = T.card := Finset.card_image_of_injOn fun x hx y hy he =>
    projectiveAffineCoordinates_injective (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 he
  rw [hRT] at hc
  have himage : (R.image π).card ≤
      projectiveCount (projectiveZeroLocus (scaledHomogenize d 1 f))
        (projectionBoxFactor n d * B) := by
    rw [← Finset.card_image_of_injective (R.image π) (affineProjectivePoint_injective 2)]
    refine Finset.card_le_card fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxB, hxI⟩ := mem_projectivePoints.mp hxS
    exact mem_projectivePoints.mpr
      ⟨projectivePlaneChartProjection_height hk₀ hk₁ x hx0 hB hxB,
        projectivePlaneChartProjection_zero I hX f hfd hfI x hxI hx0⟩
  have hU : U.card ≤ d := by
    simpa only [Fintype.card_coe, mul_one] using
      projective_section_card_le_degree I hdegree (X 0) (isHomogeneous_X _ _) hX
        (fun x : U => x.val) Subtype.val_injective
        (fun x => (mem_projectivePoints.mp (Finset.mem_filter.mp x.property).1).2)
        (fun x => by simpa using (Finset.mem_filter.mp x.property).2)
  have hc' : T.card ≤ (R.image π).card + d * (d - 1) := by convert hc using 2
  have hsum : T.card + U.card = S.card := Finset.card_filter_add_card_filter_not _
  have hdcalc : d * (d - 1) + d = d ^ 2 := by have := Nat.sub_add_cancel hd; nlinarith
  change S.card ≤ _; omega

theorem projectiveCurveBound : ProjectiveCurveBound := by
  intro n _
  let K₀ := projectivePlaneAbsoluteConstant * Real.exp (2 * projectionLogConstant n) + 1
  have hP0 := projectivePlaneAbsoluteConstant_pos
  refine ⟨K₀, by dsimp [K₀]; positivity, fun I hI d hd hdegree B hB => ?_⟩
  classical
  have : I.IsPrime := hI
  by_cases hS : (projectivePoints (projectiveIdealZeroLocus I) B).Nonempty
  · obtain ⟨x, hx⟩ := hS
    have hxI := (mem_projectivePoints.mp hx).2
    obtain ⟨j, hj⟩ := Function.ne_iff.mp x.rep_nonzero
    change x.rep j ≠ 0 at hj
    let e := Equiv.swap (0 : Fin (n + 1)) j
    let J := projectivePermutedIdeal I e
    have hX : X 0 ∉ J := fun h => hj <| by
      have hXj : X j ∈ I := by simpa [e] using (mem_projectivePermutedIdeal I e (X 0)).mp h
      simpa using projectiveIdealZeroLocus_rep hxI (X j) hXj
    obtain ⟨f, hf, hir, hreduce⟩ :=
      exists_projective_plane_count_reduction J hX hd (projectiveCurveDegree_permuted I e hdegree)
    have hA1 := projectionBoxFactor_one_le n d
    have hA0 : 0 < projectionBoxFactor n d := zero_lt_one.trans_le hA1
    have hplane := projective_plane_equation_bound f hf hd hir (one_le_mul_of_one_le_of_one_le hA1 hB)
    have hR : (projectiveCount (projectiveIdealZeroLocus J) B : ℝ) ≤
        projectiveCount (projectiveZeroLocus f) (projectionBoxFactor n d * B) + (d : ℝ) ^ 2 :=
      mod_cast hreduce B hB
    have hd0 : (0 : ℝ) < d := mod_cast hd
    have herr : (d : ℝ) ^ 2 ≤ projectiveCurveEstimate d B :=
      (pow_le_pow_right₀ (mod_cast hd : (1 : ℝ) ≤ d) (by norm_num)).trans
        (le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hB (by positivity)))
    have hscale : projectiveCurveEstimate d (projectionBoxFactor n d * B) ≤
        Real.exp (2 * projectionLogConstant n) * projectiveCurveEstimate d B := by
      have hpow : (projectionBoxFactor n d) ^ (2 / (d : ℝ)) ≤ Real.exp (2 * projectionLogConstant n) := by
        rw [Real.rpow_def_of_pos hA0, Real.exp_le_exp, ← mul_div_assoc]
        exact (div_le_iff₀ hd0).mpr (by linarith [projectionBoxFactor_log_le n hd])
      unfold projectiveCurveEstimate
      rw [Real.mul_rpow hA0.le (by linarith)]
      convert mul_le_mul_of_nonneg_left hpow
        (show 0 ≤ (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) by positivity) using 1 <;> ring
    have hperm : (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        projectiveCount (projectiveIdealZeroLocus J) B :=
      mod_cast projectiveCount_le_permuted I e B
    calc (projectiveCount (projectiveIdealZeroLocus I) B : ℝ)
        ≤ projectiveCount (projectiveZeroLocus f) (projectionBoxFactor n d * B) + (d : ℝ) ^ 2 :=
          hperm.trans hR
      _ ≤ projectivePlaneAbsoluteConstant *
            projectiveCurveEstimate d (projectionBoxFactor n d * B) +
          projectiveCurveEstimate d B := by
          rw [projectiveCurveEstimate, ← mul_assoc]; exact add_le_add hplane herr
      _ ≤ projectivePlaneAbsoluteConstant *
            (Real.exp (2 * projectionLogConstant n) * projectiveCurveEstimate d B) +
          projectiveCurveEstimate d B := by gcongr
      _ = K₀ * projectiveCurveEstimate d B := by dsimp [K₀]; ring
  · unfold projectiveCount
    rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by dsimp [K₀]; positivity) (by unfold projectiveCurveEstimate; positivity)

end
end CCDN
