module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSectors.CutoffMultipliers
public import DedekindZetaZeroFree.Analysis.ContinuousLinearMaps.DenseBoundedExtension
public import DedekindZetaZeroFree.Analysis.FunctionalAnalysis.DenseLinearExtension

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualFormCutoffClosedProduct

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings
open KPContActualSectorTestDifferentialDescent KPContActualSquareEndPartition
open KPContActualCotangentMeasurableFamilies KPContCotangentOverlapRationalBranches
open KPContActualSectorCotangentL2 KPContActualCotangentIntrinsicHilbertIntegral
open KPContActualCotangentCountableShrinking

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

local notation "D" => KPContActualSectorFriedrichsSynthesis.A_U
  F ζ hζ U R P H μG hμG hR realization
local notation "𝓗" => KPContSectorClosedLpSubspace.H F ζ hζ R U
local notation "𝓥" => KPContActualSectorCotangentL2.V F ζ hζ U R P H

include μG hμG hR realization

 section

variable (f : S_U F ζ hζ U R P H)

theorem graphTest_mem :
    WithLp.toLp 2 (iota f, j (D_U f)) ∈ closedGradientGraph D := by
  change (iota f, j (D_U f)) ∈ (D).closure.graph
  apply LinearPMap.le_graph_of_le (D).le_closure
  have hg := (D).mem_graph ⟨iota f, LinearMap.mem_range_self iota f⟩
  simpa only [KPContActualSectorFriedrichsSynthesis.A_U,
    KPTestOperator.descend_image] using hg

def graphTestLift : ClosedGradientSpace D :=
  ⟨WithLp.toLp 2 (iota f, j (D_U f)),
    graphTest_mem F ζ hζ U R P H μG hμG hR realization f⟩

end

def graphTestLinear : S_U F ζ hζ U R P H →ₗ[ℂ] ClosedGradientSpace D where
  toFun f := graphTestLift F ζ hζ U R P H μG hμG hR realization f
  map_add' f g := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    simp [graphTestLift, map_add, WithLp.toLp_add, WithLp.ofLp_add, WithLp.ofLp_toLp]
  map_smul' c f := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    simp [graphTestLift, map_smul, WithLp.toLp_smul, WithLp.ofLp_smul, WithLp.ofLp_toLp]

private theorem fst_embedding (w : ClosedGradientSpace D) :
    closedGradientEmbedding D w = (WithLp.ofLp (w : WithLp 2 (𝓗 × 𝓥))).1 := by
  simp [closedGradientEmbedding, WithLp.fstL]

private theorem closedGradientEmbedding_graphTestLinear (f : S_U F ζ hζ U R P H) :
    closedGradientEmbedding D (graphTestLinear F ζ hζ U R P H μG hμG hR realization f)
      = iota f := by
  rw [show graphTestLinear F ζ hζ U R P H μG hμG hR realization f
    = graphTestLift F ζ hζ U R P H μG hμG hR realization f from rfl]
  rw [fst_embedding F ζ hζ U R P H μG hμG hR realization]
  simp [graphTestLift, WithLp.ofLp_toLp]

private theorem graphTestLinear_dense :
    DenseRange (graphTestLinear F ζ hζ U R P H μG hμG hR realization) := by
  intro w
  rw [mem_closure_iff_seq_limit]
  have hprops := kp_cont_actual_sector_friedrichs_synthesis F ζ hζ μG hμG U R hR P H realization
  have hemb := closedGradientEmbedding_properties D hprops.gradient_dense hprops.gradient_closable
  have hmem : (WithLp.linearEquiv 2 ℂ (𝓗 × 𝓥)) w ∈ (D).closure.graph :=
    w.property
  obtain ⟨hv, hvv⟩ := (D).closure.mem_graph_iff.mp hmem
  rw [WithLp.coe_linearEquiv] at hvv
  have hfd :=
    fst_embedding F ζ hζ U R P H μG hμG hR realization w
  have hu : closedGradientEmbedding D w ∈ (D).closure.domain := by
    rw [hfd, ← hvv.1]
    exact hv.property
  obtain ⟨s, hs1, hs2, -⟩ := hprops.form_core ⟨closedGradientEmbedding D w, hu⟩
  refine ⟨fun n => graphTestLinear F ζ hζ U R P H μG hμG hR realization (s n),
    fun n => ⟨s n, rfl⟩, ?_⟩
  rw [tendsto_subtype_rng]
  have hw : w =
      WithLp.toLp 2 (closedGradientEmbedding D w,
        (D).closure ⟨closedGradientEmbedding D w, hu⟩) := by
    apply WithLp.ofLp_injective
    rw [WithLp.ofLp_toLp]
    apply Prod.ext
    · exact hfd.symm
    · rw [← hvv.2]
      congr 1
      exact Subtype.ext (hvv.1.trans hfd.symm)
  rw [hw]
  refine ((WithLp.prod_continuous_toLp 2 𝓗 𝓥).tendsto _).comp (hs1.prodMk_nhds hs2)

alias ClosedGradientCutoffProduct.graphTestLinear_dense := graphTestLinear_dense

private theorem j_norm_sq (η : RealSmoothCutoff F ζ hζ U R P H) (f : S_U F ζ hζ U R P H) :
    ‖j (cutoffGradientTimes η f)‖ ^ 2 =
      ∫ x, (normSquare (cutoffGradientTimes η f).val x : ℝ)
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
  have h := KPContActualCotangentIntrinsicHilbertIntegral.norm_sq_eq_integral (KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H) (j (cutoffGradientTimes η f))
    (cotangentSquareFamily (cutoffGradientTimes η f)) rfl
  simpa [cotangentSquareFamily] using h

private theorem iota_norm_sq (f : S_U F ζ hζ U R P H) :
    ‖iota f‖ ^ 2 =
      ∫ x, (scalarPair f f x).re ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
  have hE := kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H realization
  have hstep : (∫ x, (scalarPair f f x).re
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) =
      ∫ x, Complex.reCLM (scalarPair f f x)
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
    simp [Complex.reCLM_apply]
  rw [hstep, ContinuousLinearMap.integral_comp_comm Complex.reCLM (hE.scalar_pair_integrable f f),
    ← hE.scalar_inner f f, Complex.reCLM_apply]
  have hz : inner ℂ (iota f) (iota f) = ((‖iota f‖ : ℂ)) ^ 2 :=
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (iota f)
  rw [hz, ← Complex.ofReal_pow, Complex.ofReal_re]

section

variable (η : RealSmoothCutoff F ζ hζ U R P H) (D₀ : ℝ) (hD₀ : 0 ≤ D₀)

include hD₀ in
private theorem normSquare_cutoffGradientTimes_le
    (hdη : ∀ (a : ActualChart (U := U) (H := H))
      (y : KPContCotangentOverlapRationalBranches.omega a),
      ‖cutoffDifferential η a y‖ ≤ D₀)
    (f : S_U F ζ hζ U R P H) (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ((normSquare (cutoffGradientTimes η f).val x : ℝ≥0) : ℝ) ≤
      D₀ ^ 2 * (scalarPair f f x).re := by
  obtain ⟨cov⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  have hcov : ∀ x : KPFiniteCuspAtlas.rawXU F ζ hζ U,
      ∃ n, x ∈ (cov.chart n).baseDomain := by
    intro x
    have h := cov.covers
    rw [Set.eq_univ_iff_forall] at h
    simpa [Set.mem_iUnion] using h x
  obtain ⟨n, hn⟩ := hcov x
  obtain ⟨y, hy⟩ := hn
  let x' :=
    KPContCotangentActualOverlap.labeledAInv
      (KPContCotangentActualOverlap.placeEquiv F ζ hζ) y.val
  have hx' : KPContCotangentActualOverlap.labeledA
      (KPContCotangentActualOverlap.placeEquiv F ζ hζ) x' = y.val := by
    funext k
    show (CotangentLogCoframe.A (KPContCotangentActualOverlap.d F))
        ((CotangentLogCoframe.A (KPContCotangentActualOverlap.d F)).symm
          (fun k' => y.val (KPContCotangentActualOverlap.placeEquiv F ζ hζ k')))
        ((KPContCotangentActualOverlap.placeEquiv F ζ hζ).symm k) = y.val k
    rw [ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hmem : x' ∈ omega (cov.chart n) := by
    show KPContCotangentActualOverlap.labeledA
      (KPContCotangentActualOverlap.placeEquiv F ζ hζ) x' ∈ (cov.chart n).domain
    rw [hx']; exact y.property
  let x'' : omega (cov.chart n) := ⟨x', hmem⟩
  have hqx : q (cov.chart n) x''.val = x := by
    rw [← hy]
    unfold KPContCotangentOverlapRationalBranches.q ShrunkChart.toBase
    rw [hx']
  rw [← hqx, normSquare_chart (cutoffGradientTimes η f).val (cov.chart n) x'']
  let val₀ := f.val (cov.chart n) x''
  have hsp : (scalarPair f f (q (cov.chart n) x''.val)).re
      = ‖val₀‖ ^ 2 := by
    rw [(kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H realization).scalar_pair_chart f f (cov.chart n) x'']
    have hz : inner ℂ (val₀) (val₀)
        = ((‖val₀‖ : ℂ)) ^ 2 :=
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _
    rw [hz, ← Complex.ofReal_pow, Complex.ofReal_re]
  let coefficient₀ := coefficient (cutoffGradientTimes η f).val (cov.chart n) x''
  have hns : ((‖coefficient₀‖₊ ^ 2
        : ℝ≥0) : ℝ)
      = ‖val₀‖ ^ 2
        * ‖cutoffDifferential η (cov.chart n) x''‖ ^ 2 := by
    have hc : coefficient₀
        = val₀ • cutoffDifferential η (cov.chart n) x'' := rfl
    have hcoe : ((‖coefficient₀‖₊ ^ 2
        : ℝ≥0) : ℝ) = ‖coefficient₀‖ ^ 2 := by
      rw [NNReal.coe_pow]
      rfl
    rw [hcoe, hc, norm_smul]
    ring
  rw [hns, hsp]
  have h1 : ‖cutoffDifferential η (cov.chart n) x''‖ ^ 2 ≤ D₀ ^ 2 := by
    nlinarith [hdη (cov.chart n) x'',
      norm_nonneg (cutoffDifferential η (cov.chart n) x''), hD₀]
  nlinarith [h1, sq_nonneg ‖val₀‖]

include hD₀ in
private theorem cutoffGradientTimes_norm_bound
    (hdη : ∀ (a : ActualChart (U := U) (H := H))
      (y : KPContCotangentOverlapRationalBranches.omega a),
      ‖cutoffDifferential η a y‖ ≤ D₀)
    (f : S_U F ζ hζ U R P H) :
    ‖j (cutoffGradientTimes η f)‖ ≤ D₀ * ‖iota f‖ := by
  have hmain : ‖j (cutoffGradientTimes η f)‖ ^ 2 ≤ D₀ ^ 2 * ‖iota f‖ ^ 2 := by
    rw [j_norm_sq F ζ hζ U R P H μG hμG hR realization η f,
      iota_norm_sq F ζ hζ U R P H μG hμG hR realization f]
    calc _
        ≤ ∫ x, D₀ ^ 2 * (scalarPair f f x).re
          ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P :=
          integral_mono (KPContActualCotangentIntrinsicHilbertIntegral.integrable_normSquare
            (cotangentSquareFamily (cutoffGradientTimes η f))) (((kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H realization).scalar_pair_integrable f f).re.const_mul _) (fun x => normSquare_cutoffGradientTimes_le F ζ hζ U R P H μG hμG
            hR realization η D₀ hD₀ hdη f x)
      _ = D₀ ^ 2 * ∫ x, (scalarPair f f x).re
          ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P :=
          integral_const_mul _ _
  have hsq : (D₀ * ‖iota f‖) ^ 2 = D₀ ^ 2 * ‖iota f‖ ^ 2 := by ring
  nlinarith [hmain, hsq, norm_nonneg (j (cutoffGradientTimes η f)),
    mul_nonneg hD₀ (norm_nonneg (iota f))]

include hD₀ in
private theorem exists_scalar_to_cotangent
    (hdη : ∀ (a : ActualChart (U := U) (H := H))
      (y : KPContCotangentOverlapRationalBranches.omega a),
      ‖cutoffDifferential η a y‖ ≤ D₀) :
    ∃ C : 𝓗 →L[ℂ] 𝓥, ‖C‖ ≤ D₀ ∧
      ∀ f : S_U F ζ hζ U R P H, C (iota f) = j (cutoffGradientTimes η f) := by
  have hdense := KPContActualSectorFriedrichsSynthesis.scalarDense
    F ζ hζ U R P H μG hμG hR realization
  have hbound :=
    fun f => cutoffGradientTimes_norm_bound F ζ hζ U R P H μG hμG hR realization
      η D₀ hD₀ hdη f
  refine ⟨LinearMap.extendOfNorm
    ((j).comp (cutoffGradientTimes η))
    (iota), ?_, ?_⟩
  · exact LinearMap.opNorm_extendOfNorm_le hdense hD₀ hbound
  · intro f
    exact LinearMap.extendOfNorm_eq hdense ⟨D₀, hbound⟩ f

end

private theorem graphTestLinear_bound
    (η : RealSmoothCutoff F ζ hζ U R P H) (M : SectorMultiplier F ζ hζ U R P H η)
    (B D₀ : ℝ) (hB : 0 ≤ B) (hD₀ : 0 ≤ D₀)
    (hη : ∀ x, |η.val x| ≤ B)
    (hdη : ∀ (a : ActualChart (U := U) (H := H))
      (y : KPContCotangentOverlapRationalBranches.omega a),
      ‖cutoffDifferential η a y‖ ≤ D₀) :
    ∃ K : ℝ, ∀ f : S_U F ζ hζ U R P H,
      ‖graphTestLinear F ζ hζ U R P H μG hμG hR realization (scalarMultiply η f)‖
        ≤ K * ‖graphTestLinear F ζ hζ U R P H μG hμG hR realization f‖ := by
  obtain ⟨C, hCnorm, hCeq⟩ := exists_scalar_to_cotangent F ζ hζ U R P H μG hμG hR realization
    η D₀ hD₀ hdη
  obtain ⟨N, hNnorm, hNeq⟩ := KPContActualCotangentBoundedScalarMultiplier.exists_multiplier
    F ζ hζ U R P H μG hμG hR realization η B hB hη
  have hdp := fun f => (kp_cont_actual_sector_test_differential_descent F ζ hζ μG hμG U R hR P H
    realization).differential_product η f
  have hM0 : (0 : ℝ) ≤ ‖M.op‖ := ContinuousLinearMap.opNorm_nonneg M.op
  refine ⟨‖M.op‖ + B + D₀, ?_⟩
  intro f
  have hnormsq : ∀ g : S_U F ζ hζ U R P H,
      ‖graphTestLinear F ζ hζ U R P H μG hμG hR realization g‖ ^ 2
        = ‖iota g‖ ^ 2 + ‖j (D_U g)‖ ^ 2 := by
    intro g
    have hv : (graphTestLinear F ζ hζ U R P H μG hμG hR realization g :
        WithLp 2 (𝓗 × 𝓥)) = WithLp.toLp 2 (iota g, j (D_U g)) := rfl
    rw [show ‖graphTestLinear F ζ hζ U R P H μG hμG hR realization g‖
        = ‖(graphTestLinear F ζ hζ U R P H μG hμG hR realization g : WithLp 2 (𝓗 × 𝓥))‖
        from rfl, hv, WithLp.prod_norm_sq_eq_of_L2]
    simp
  set a : ℝ := ‖iota f‖ with ha
  set b : ℝ := ‖j (D_U f)‖ with hb
  have ha0 : 0 ≤ a := by rw [ha]; exact norm_nonneg _
  have hb0 : 0 ≤ b := by rw [hb]; exact norm_nonneg _
  set G : ℝ := ‖graphTestLinear F ζ hζ U R P H μG hμG hR realization f‖ with hG
  have hG0 : 0 ≤ G := by rw [hG]; exact norm_nonneg _
  have hG2 : G ^ 2 = a ^ 2 + b ^ 2 := by rw [hG, hnormsq f, ha, hb]
  have haG : a ≤ G := by nlinarith [ha0, hb0, hG2]
  have hbG : b ≤ G := by nlinarith [ha0, hb0, hG2]
  have hgrad : j (D_U (scalarMultiply η f)) = N (j (D_U f)) + C (iota f) := by
    rw [hdp f, map_add, hNeq (D_U f), hCeq f]
  have hX : ‖iota (scalarMultiply η f)‖ ≤ ‖M.op‖ * G := by
    rw [← M.test_commutes f]
    exact le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_left haG (norm_nonneg _))
  have hY : ‖j (D_U (scalarMultiply η f))‖ ≤ (B + D₀) * G := by
    rw [hgrad]
    calc ‖N (j (D_U f)) + C (iota f)‖ ≤ ‖N (j (D_U f))‖ + ‖C (iota f)‖ := norm_add_le _ _
      _ ≤ ‖N‖ * b + ‖C‖ * a := by
          rw [hb, ha]
          exact add_le_add (ContinuousLinearMap.le_opNorm _ _)
            (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ B * G + D₀ * G :=
          add_le_add (mul_le_mul hNnorm hbG hb0 hB) (mul_le_mul hCnorm haG ha0 hD₀)
      _ = (B + D₀) * G := by ring
  have hX2 : ‖iota (scalarMultiply η f)‖ ^ 2 ≤ (‖M.op‖ * G) ^ 2 := by
    nlinarith [hX, norm_nonneg (iota (scalarMultiply η f)), hG0, norm_nonneg M.op]
  have hY2 : ‖j (D_U (scalarMultiply η f))‖ ^ 2 ≤ ((B + D₀) * G) ^ 2 := by
    nlinarith [hY, norm_nonneg (j (D_U (scalarMultiply η f))), hG0, hB, hD₀]
  have hKG : (‖M.op‖ * G) ^ 2 + ((B + D₀) * G) ^ 2
      ≤ ((‖M.op‖ + B + D₀) * G) ^ 2 := by
    nlinarith [sq_nonneg G, norm_nonneg M.op, hB, hD₀,
      mul_nonneg (norm_nonneg M.op) (add_nonneg hB hD₀)]
  have hgoal : ‖graphTestLinear F ζ hζ U R P H μG hμG hR realization (scalarMultiply η f)‖
      ≤ (‖M.op‖ + B + D₀) * G := by
    have hsq : ‖graphTestLinear F ζ hζ U R P H μG hμG hR realization (scalarMultiply η f)‖ ^ 2
        ≤ ((‖M.op‖ + B + D₀) * G) ^ 2 := by
      rw [hnormsq (scalarMultiply η f)]
      linarith [hX2, hY2, hKG]
    have h2 : 0 ≤ (‖M.op‖ + B + D₀) * G :=
      mul_nonneg (add_nonneg (add_nonneg hM0 hB) hD₀) hG0
    have h3 := sq_le_sq.mp hsq
    rw [abs_of_nonneg h2] at h3
    simpa using h3
  exact hgoal

theorem exists_lift
    (η : RealSmoothCutoff F ζ hζ U R P H)
    (M : SectorMultiplier F ζ hζ U R P H η)
    (B D₀ : ℝ) (hB : 0 ≤ B) (hD₀ : 0 ≤ D₀)
    (hη : ∀ x, |η.val x| ≤ B)
    (hdη : ∀ (a : ActualChart (U := U) (H := H))
      (y : KPContCotangentOverlapRationalBranches.omega a),
      ‖cutoffDifferential η a y‖ ≤ D₀) :
    ∃ A : ClosedGradientSpace D →L[ℂ] ClosedGradientSpace D,
      (closedGradientEmbedding D).comp A =
        M.op.comp (closedGradientEmbedding D) ∧
      ∀ f : S_U F ζ hζ U R P H,
        A (graphTestLift F ζ hζ U R P H μG hμG hR realization f) =
          graphTestLift F ζ hζ U R P H μG hμG hR realization (scalarMultiply η f) := by
  obtain ⟨K, hbound⟩ := graphTestLinear_bound F ζ hζ U R P H μG hμG hR realization
    η M B D₀ hB hD₀ hη hdη
  have hclosable : (D).IsClosable :=
    (kp_cont_actual_sector_friedrichs_synthesis F ζ hζ μG hμG U R hR P H
      realization).gradient_closable
  haveI hNS : NormedSpace ℂ (ClosedGradientSpace D) :=
    Submodule.normedSpace (closedGradientGraph D)
  haveI hBS : IsBoundedSMul ℂ (ClosedGradientSpace D) :=
    IsBoundedSMul.of_norm_smul_le
      (fun c x => norm_smul_le c (x : WithLp 2 (𝓗 × 𝓥)))
  haveI hCS : CompleteSpace (ClosedGradientSpace D) :=
    (closedGradientGraph_isClosed D hclosable).completeSpace_coe
  let graphTestLinear₀ := graphTestLinear F ζ hζ U R P H μG hμG hR realization
  have hdenseE : DenseRange (graphTestLinear₀) :=
    graphTestLinear_dense F ζ hζ U R P H μG hμG hR realization
  set L : ClosedGradientSpace D →L[ℂ] ClosedGradientSpace D :=
    LinearMap.extendOfNorm (σ₁₂ := RingHom.id ℂ)
      ((graphTestLinear₀).comp (scalarMultiply η))
      (graphTestLinear₀) with hLdef
  have hLeq : ∀ f : S_U F ζ hζ U R P H,
      L (graphTestLinear₀ f)
        = graphTestLinear₀ (scalarMultiply η f) := by
    intro f
    rw [hLdef]
    exact LinearMap.extendOfNorm_eq hdenseE ⟨K, hbound⟩ f
  have hLproj : (closedGradientEmbedding D).comp L
      = M.op.comp (closedGradientEmbedding D) := by
    apply DFunLike.coe_injective
    refine DenseRange.equalizer hdenseE ((closedGradientEmbedding D).comp L).continuous
      (M.op.comp (closedGradientEmbedding D)).continuous ?_
    funext f
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hLeq f,
      closedGradientEmbedding_graphTestLinear F ζ hζ U R P H μG hμG hR realization
        (scalarMultiply η f),
      closedGradientEmbedding_graphTestLinear F ζ hζ U R P H μG hμG hR realization f]
    exact (M.test_commutes f).symm
  refine ⟨L, hLproj, fun f => ?_⟩
  show L (graphTestLinear₀ f)
      = graphTestLinear₀ (scalarMultiply η f)
  exact hLeq f

end DedekindZetaZeroFree.KPContActualFormCutoffClosedProduct

end
