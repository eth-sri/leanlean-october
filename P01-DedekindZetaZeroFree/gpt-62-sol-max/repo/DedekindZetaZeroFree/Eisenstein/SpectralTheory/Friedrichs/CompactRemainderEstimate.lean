module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspForms.ExteriorLowerBound
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Friedrichs.IMSIdentity
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Friedrichs.CompactLocalFormRestriction

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCompactRemainderEstimate

open KPContActualSquareEndPartition KPContActualFormLocalRestrictionCompact

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def errorSup {T : ℝ} (partition : SquareEndPartition F ζ hζ U R P H T) : ℝ :=
  sSup (Set.range (collarError F ζ hζ U R P H partition.χ₀ partition.χ))

def coefficient {T : ℝ} (partition : SquareEndPartition F ζ hζ U R P H T) : ℝ :=
  KPContActualCuspRadialFormComparison.d F + errorSup F ζ hζ U R P H partition

variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

local notation "HU" => KPContSectorClosedLpSubspace.H F ζ hζ R U
local notation "Q" => KPContActualFormIMSIdentity.Q_U F ζ hζ U R P H μG hμG hR realization
local notation "jU" => KPContActualFormIMSIdentity.j_U F ζ hζ U R P H μG hμG hR realization
local notation "qU" => KPContActualFormIMSIdentity.q_U F ζ hζ U R P H μG hμG hR realization
local notation "BU" => KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ U R P H μG hμG hR realization
local notation "bU" => b_U F ζ hζ U R P H μG hμG hR realization
local notation "AU" => KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization
local notation "ΔU" => KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization
local notation "dF" => KPContActualCuspRadialFormComparison.d F
local notation "μcov" => KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U
local notation "qcov" => KPContSectorCoveredQuotientVocabulary.q F ζ hζ U

def remainder {T : ℝ} (partition : SquareEndPartition F ζ hζ U R P H T)
    (multiplier : MultiplierData F ζ hζ U R P H μG hμG hR realization
      (fun x => (partition.ρ.val x : ℂ))) : HU →L[ℂ] HU :=
  (Real.sqrt (coefficient F ζ hζ U R P H partition) : ℂ) •
    (multiplier.M_ρ.comp BU)

private theorem coord_eq_closure_of_embedding
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) (w : ClosedGradientSpace D) (u : D.closure.domain)
    (hw : closedGradientEmbedding D w = (u : H)) :
    closedGradientCoordinate D w = D.closure u := by
  have h := w.property
  simp only [closedGradientGraph, Submodule.mem_comap] at h
  rw [LinearPMap.mem_graph_iff] at h
  obtain ⟨y, hy1, hy2⟩ := h
  have hA : ((WithLp.linearEquiv 2 ℂ (H × V)) (w : WithLp 2 (H × V))).1 =
      closedGradientEmbedding D w := by
    simp only [WithLp.coe_linearEquiv, WithLp.ofLp_fst, closedGradientEmbedding,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, WithLp.fstL_apply]
  have hB : ((WithLp.linearEquiv 2 ℂ (H × V)) (w : WithLp 2 (H × V))).2 =
      closedGradientCoordinate D w := by
    simp only [WithLp.coe_linearEquiv, WithLp.ofLp_snd, closedGradientCoordinate,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, WithLp.sndL_apply]
  have hy1' : (y : H) = closedGradientEmbedding D w := hy1.trans hA
  have hy2' : D.closure y = closedGradientCoordinate D w := hy2.trans hB
  have hy : y = u := by
    apply Subtype.ext
    rw [hy1', hw]
  rw [← hy2', hy]

private theorem lp_norm_sq_here {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (w : Lp ℂ 2 μ) : ‖w‖ ^ 2 = ∫ x, ‖w x‖ ^ 2 ∂μ := by
  have hi := L2.inner_def (𝕜 := ℂ) w w
  have h2 : ∫ x, inner ℂ (w x) (w x) ∂μ = ((∫ x, ‖w x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    have hcongr : ∫ x, inner ℂ (w x) (w x) ∂μ
        = ∫ x, ((‖w x‖ ^ 2 : ℝ) : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [inner_self_eq_norm_sq_to_K]; norm_num
    rw [hcongr]; exact integral_ofReal
  have h3 : (inner ℂ w w).re = ‖w‖ ^ 2 := by
    have hz : inner ℂ w w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_num
    rw [hz, Complex.ofReal_re]
  rw [← h3, hi, h2, Complex.ofReal_re]

private theorem norm_sq_ofReal_mul (r : ℝ) (hr : 0 ≤ r) (z : ℂ) :
    ‖(r : ℂ) * z‖ ^ 2 = r ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, mul_pow]

private theorem measurable_sectionNorm_here (s : KPContSectorLineL2Isometry.BorelL2Sections F ζ hζ U R P H) :
    Measurable (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ U R P H s.val) := by
  have hme : Measurable (fun x =>
      KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ U R P H s.val x ^ 2) := by
    have h := ENNReal.measurable_toReal.comp
      (KPContSectorLineL2Isometry.squaredNorm_measurable F ζ hζ U R P H s.val s.property.1)
    simpa only [Function.comp_def, KPContSectorLineL2Isometry.squaredNorm,
      ENNReal.toReal_ofReal (sq_nonneg _)] using h
  have heq : KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ U R P H s.val =
      fun x => Real.sqrt
        (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ U R P H s.val x ^ 2) := by
    funext x
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    obtain ⟨⟨i, w⟩, rfl⟩ := (H.atlas U).components.surjective x
    obtain ⟨z, rfl⟩ := Quotient.exists_rep w
    rw [KPContSectorSmoothFramesSupport.sectionNorm_component]
    exact norm_nonneg _
  rw [heq]; exact hme.sqrt

private theorem weighted_integral_eq_here {T : ℝ}
    (partition : SquareEndPartition F ζ hζ U R P H T)
    (w : Q) (s : KPContSectorLineL2Isometry.BorelL2Sections F ζ hζ U R P H)
    (hs : KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ U R P H (jU w) =
      KPContSectorLineL2Isometry.mk F ζ hζ U R P H s) :
    (∫ x, collarError F ζ hζ U R P H partition.χ₀ partition.χ
        (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x) *
        ‖(jU w).val x‖ ^ 2
        ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U) =
      ∫ x, collarError F ζ hζ U R P H partition.χ₀ partition.χ x *
        KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ U R P H s.val x ^ 2
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
  have hs' : (KPContSectorLineL2Isometry.lineToSector F ζ hζ U R P H).symm
      (jU w) = KPContSectorLineL2Isometry.mk F ζ hζ U R P H s := hs
  have hts : KPContSectorLineL2Isometry.toSector F ζ hζ U R P H s = jU w := by
    have h := congrArg (KPContSectorLineL2Isometry.lineToSector F ζ hζ U R P H) hs'
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hval : (jU w).val =
      (KPContSectorLineL2Isometry.representative_memLp F ζ hζ U R P H s).toLp
        (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H s.val).val := by
    rw [← hts]; rfl
  have hcoe : (KPContSectorLineL2Isometry.representative_memLp F ζ hζ U R P H s).toLp
        (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H s.val).val
      =ᵐ[KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U]
        (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H s.val).val :=
    (KPContSectorLineL2Isometry.representative_memLp F ζ hζ U R P H s).coeFn_toLp
  have hstep1 : (∫ x, collarError F ζ hζ U R P H partition.χ₀ partition.χ
        (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x) *
        ‖(jU w).val x‖ ^ 2
        ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U) =
      ∫ x, collarError F ζ hζ U R P H partition.χ₀ partition.χ
        (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x) *
        ‖(KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H s.val).val x‖ ^ 2
        ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U := by
    apply integral_congr_ae
    filter_upwards [hcoe] with x hx
    rw [hval, hx]
  rw [hstep1]
  rw [show KPContActualSectorCotangentL2.muU F ζ hζ U R P =
      Measure.map (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U)
        (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U) from
      (KPContSectorFixedPushforwardSupport.map_q_coveredMeasure F ζ hζ R P U).symm]
  rw [MeasureTheory.integral_map]
  · apply integral_congr_ae
    filter_upwards with x
    have hS : KPContSectorScalarLineAlgebra.S F ζ hζ U R P H
        (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H s.val) = s.val :=
      (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H).apply_symm_apply s.val
    have hsn : KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ U R P H s.val
        (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x) =
        ‖(KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H s.val).val x‖ := by
      conv_lhs => rw [← hS]
      exact KPContSectorSmoothFramesSupport.sectionNorm_pullback F ζ hζ U R P H _ x
    rw [hsn]
  · exact (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).aemeasurable
  · have hEc : Continuous (collarError F ζ hζ U R P H partition.χ₀ partition.χ) :=
      collarError_continuous_nonnegative F ζ hζ U R P H partition.χ₀ partition.χ |>.1
    have hm : Measurable (fun y => collarError F ζ hζ U R P H partition.χ₀ partition.χ y *
        KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ U R P H s.val y ^ 2) :=
      hEc.measurable.mul ((measurable_sectionNorm_here F ζ hζ U R P H s).pow_const 2)
    exact hm.aestronglyMeasurable

theorem compact_remainder_estimate :
    ∃ K : HU →L[ℂ] HU, IsCompactOperator K ∧
      ∀ u : HU, dF * ‖BU u‖ ^ 2 ≤ (inner ℂ (BU u) (u - BU u)).re + ‖K u‖ ^ 2 := by
  classical
  have hfr := kp_cont_actual_sector_test_friedrichs F ζ hζ μG hμG U R hR P H realization
  have hd := KPContActualCuspRadialFormComparison.positive_dimension_proof F
  obtain ⟨T, hTthr, hextb⟩ :=
    kp_cont_actual_cusp_exterior_form_bound F ζ hζ μG hμG U R hR P H realization
  obtain ⟨part⟩ := kp_cont_actual_square_end_partition F ζ hζ U R P H realization T hTthr
  obtain ⟨ims⟩ := kp_cont_actual_form_ims_identity F ζ hζ U R P H μG hμG hR realization T part
  have hρsm : SmoothScalar F ζ hζ U R P H (fun x => (part.ρ.val x : ℂ)) := by
    refine ⟨Complex.continuous_ofReal.comp part.ρ.continuous, fun a => ?_⟩
    obtain ⟨g, hg, hgv⟩ := part.ρ.smooth a
    exact ⟨fun x => (g x : ℂ), Complex.ofRealCLM.contDiff.comp_contDiffOn hg,
      fun x => congrArg Complex.ofReal (hgv x)⟩
  have hρc := part.compact_rho_support.comp_left Complex.ofReal_zero
  obtain ⟨mult⟩ :=
    multiplierData_nonempty F ζ hζ U R P H μG hμG hR realization
      (fun x => (part.ρ.val x : ℂ)) hρsm hρc
  have hsupBdd : BddAbove (Set.range (collarError F ζ hζ U R P H part.χ₀ part.χ)) := by
    obtain ⟨C, _, hC⟩ := part.error_bounded
    exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  have hsup : 0 ≤ errorSup F ζ hζ U R P H part :=
    Real.sSup_nonneg (by rintro _ ⟨x, rfl⟩; exact part.error_nonnegative x)
  have hle : ∀ x, collarError F ζ hζ U R P H part.χ₀ part.χ x ≤
      errorSup F ζ hζ U R P H part := by
    intro x
    rw [errorSup]
    exact le_csSup hsupBdd (Set.mem_range_self x)
  have hcoef : 0 ≤ coefficient F ζ hζ U R P H part := by
    rw [coefficient]
    exact add_nonneg (hd.le) hsup
  have hbind : mult.M_ρ = part.rho_multiplier.op := by
    ext u
    filter_upwards [mult.global_formula u, part.rho_multiplier.ae_apply u] with x hx1 hx2
    rw [hx1, hx2]
  have hsqrt : ‖(Real.sqrt (coefficient F ζ hζ U R P H part) : ℂ)‖ =
      Real.sqrt (coefficient F ζ hζ U R P H part) := by
    simp [Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hnsq : ∀ u : HU, ‖remainder F ζ hζ U R P H μG hμG hR realization part mult u‖ ^ 2 =
      coefficient F ζ hζ U R P H part * ‖mult.M_ρ (BU u)‖ ^ 2 := by
    intro u
    rw [remainder, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, norm_smul,
      hsqrt, mul_pow, Real.sq_sqrt hcoef]
  have hformbound : ∀ v : Q,
      dF * ‖jU v‖ ^ 2 ≤
        qU v + coefficient F ζ hζ U R P H part * ‖mult.M_ρ (jU v)‖ ^ 2 := by

    have hcusp : ∀ (c : KPContActualCuspRadialFormComparison.Cusp F ζ hζ U R P H) (v : Q),
        dF * ‖jU (ims.A (some c) v)‖ ^ 2 ≤
          qU (ims.A (some c) v) := by
      intro c
      have hcont : Continuous (fun v : Q =>
          qU (ims.A (some c) v) - dF *
            ‖jU (ims.A (some c) v)‖ ^ 2) := by
        have h1 : Continuous (fun v : Q => qU (ims.A (some c) v)) := by
          show Continuous (fun v : Q => ‖KPContActualFormIMSIdentity.closedGradient F ζ hζ U R P H
            μG hμG hR realization (ims.A (some c) v)‖ ^ 2)
          exact (((KPContActualFormIMSIdentity.closedGradient F ζ hζ U R P H μG hμG hR
            realization).comp (ims.A (some c))).continuous.norm.pow 2)
        have h2 : Continuous (fun v : Q => ‖jU (ims.A (some c) v)‖ ^ 2) :=
          ((((jU).comp (ims.A (some c))).continuous).norm.pow 2)
        exact h1.sub (continuous_const.mul h2)
      have hnonneg : ∀ v ∈ Set.range (KPContActualFormIMSIdentity.coreLift F ζ hζ U R P H
          μG hμG hR realization),
          0 ≤ qU (ims.A (some c) v) - dF *
            ‖jU (ims.A (some c) v)‖ ^ 2 := by
        rintro v ⟨f, rfl⟩
        have hsupp : KPContActualSectorSmoothTestModules.scalarSupport
            (KPContActualSectorTestDifferentialDescent.scalarMultiply (part.χ c) f).val ⊆
            KPContActualCuspRadialFormComparison.endSet F ζ hζ U R P H c T := by
          refine subset_trans ?_ (part.cusp_support_in_tail c)
          rw [KPContActualSectorSmoothTestModules.scalarSupport, tsupport]
          apply closure_mono
          rintro x ⟨a, y, hq, hne⟩
          simp only [Function.mem_support]
          intro hzero
          exact hne (by
            show (KPContActualSectorTestDifferentialDescent.scalarMultiply (part.χ c) f).val a y = 0
            rw [show (KPContActualSectorTestDifferentialDescent.scalarMultiply (part.χ c) f).val a y =
                KPContActualSectorTestDifferentialDescent.cutoffLift (part.χ c) a y * f.val a y
                from rfl,
              KPContActualSectorTestDifferentialDescent.cutoffLift, hq, hzero,
              Complex.ofReal_zero, zero_mul])
        have hext := hextb c (KPContActualSectorTestDifferentialDescent.scalarMultiply
          (part.χ c) f) hsupp
        have hA : ims.A (some c) (KPContActualFormIMSIdentity.coreLift F ζ hζ U R P H
            μG hμG hR realization f) =
            KPContActualFormIMSIdentity.coreLift F ζ hζ U R P H μG hμG hR realization
              (KPContActualSectorTestDifferentialDescent.scalarMultiply (part.χ c) f) :=
          ims.test_lift (some c) f
        rw [hA]
        have hjs : jU (KPContActualFormIMSIdentity.coreLift F ζ hζ U R P H μG hμG hR
            realization (KPContActualSectorTestDifferentialDescent.scalarMultiply (part.χ c) f)) =
            KPContActualSectorTestEmbeddings.iota
              (KPContActualSectorTestDifferentialDescent.scalarMultiply (part.χ c) f) :=
          KPContActualFormIMSIdentity.coreLift_scalar F ζ hζ U R P H μG hμG hR realization _
        rw [hjs]
        have hqe : qU (KPContActualFormIMSIdentity.coreLift F ζ hζ U R P H μG hμG hR
            realization (KPContActualSectorTestDifferentialDescent.scalarMultiply (part.χ c) f)) =
            KPContActualCuspRadialFormComparison.q_U F ζ hζ U R P H μG hμG hR realization
              (KPContActualCuspRadialFormComparison.coreLift F ζ hζ U R P H μG hμG hR
                realization (KPContActualSectorTestDifferentialDescent.scalarMultiply
                  (part.χ c) f)) := rfl
        rw [hqe]
        linarith [hext]
      intro v
      have hv : v ∈ closure {b | 0 ≤ qU (ims.A (some c) b) -
          dF * ‖jU (ims.A (some c) b)‖ ^ 2} :=
        closure_mono hnonneg
          (by rw [Dense.closure_eq (KPContActualFormIMSIdentity.coreLift_dense
              F ζ hζ U R P H μG hμG hR realization)]; exact Set.mem_univ v)
      exact le_of_sub_nonneg ((isClosed_le continuous_const hcont).closure_subset hv)
    intro v

    obtain ⟨s, hs⟩ := ims.line_representative v
    have hims := ims.ims v s hs
    have hcore_nonneg : 0 ≤ qU (ims.A none v) := by
      show 0 ≤ ‖KPContActualFormIMSIdentity.closedGradient F ζ hζ U R P H μG hμG hR
        realization (ims.A none v)‖ ^ 2
      positivity
    have hcusp_sum : ∑ c : KPContActualCuspRadialFormComparison.Cusp F ζ hζ U R P H,
        dF * ‖jU (ims.A (some c) v)‖ ^ 2 ≤
        ∑ c : KPContActualCuspRadialFormComparison.Cusp F ζ hζ U R P H,
          qU (ims.A (some c) v) :=
      Finset.sum_le_sum (fun c _ => hcusp c v)
    have hsum_opt : ∑ c : KPContActualCuspRadialFormComparison.Cusp F ζ hζ U R P H,
        qU (ims.A (some c) v) ≤
        ∑ i : KPContActualFormIMSIdentity.Index F ζ hζ U R P H, qU (ims.A i v) := by
      rw [Fintype.sum_option (fun i => qU (ims.A i v))]
      exact le_add_of_nonneg_left hcore_nonneg

    have herr : dF * ‖jU (ims.A none v)‖ ^ 2 +
        (∫ x, collarError F ζ hζ U R P H part.χ₀ part.χ x *
          KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ U R P H s.val x ^ 2
          ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) ≤
        coefficient F ζ hζ U R P H part * ‖mult.M_ρ (jU v)‖ ^ 2 := by
        have ha : (0 : ℝ) ≤ dF := hd.le

        obtain ⟨V, _hVopen, hVsub, hVone⟩ := part.rho_one_neighborhood
        have hpt : ∀ x : KPContActualSquareEndPartition.Base F ζ hζ U,
            dF * part.χ₀.val x ^ 2 +
              collarError F ζ hζ U R P H part.χ₀ part.χ x ≤
            coefficient F ζ hζ U R P H part * part.ρ.val x ^ 2 := by
          intro x
          by_cases hx : x ∈ V
          · have h1 : part.ρ.val x = 1 := hVone x hx
            have hχ2 : part.χ₀.val x ^ 2 ≤ 1 := by nlinarith [part.core_range x]
            have hmul : dF * part.χ₀.val x ^ 2 ≤
                dF := by
              simpa using mul_le_mul_of_nonneg_left hχ2 ha
            have hE := hle x
            rw [h1, one_pow, mul_one, coefficient]
            linarith
          · have hχ0 : part.χ₀.val x = 0 := by
              by_contra h
              exact hx (hVsub (Or.inl (subset_closure (Function.mem_support.mpr h))))
            have hE0 : collarError F ζ hζ U R P H part.χ₀ part.χ x = 0 := by
              by_contra h
              exact hx (hVsub (Or.inr (subset_closure (Function.mem_support.mpr h))))
            rw [hχ0, hE0]
            linarith [mul_nonneg hcoef (sq_nonneg (part.ρ.val x))]

        have hcore_sq : Integrable (fun x =>
            ‖(part.core_multiplier.op (jU v)).val x‖ ^ 2) μcov :=
          (Lp.memLp (part.core_multiplier.op (jU v) : Lp ℂ 2 μcov)).integrable_norm_pow (p := 2)
            (by norm_num)
        have hrho_sq : Integrable (fun x =>
            ‖(part.rho_multiplier.op (jU v)).val x‖ ^ 2) μcov :=
          (Lp.memLp (part.rho_multiplier.op (jU v) : Lp ℂ 2 μcov)).integrable_norm_pow (p := 2)
            (by norm_num)
        have hw_sq : Integrable (fun x => ‖(jU v).val x‖ ^ 2) μcov :=
          (Lp.memLp (jU v : Lp ℂ 2 μcov)).integrable_norm_pow (p := 2) (by norm_num)
        have hcore_int : Integrable (fun x =>
            dF *
              ‖(part.core_multiplier.op (jU v)).val x‖ ^ 2) μcov :=
          hcore_sq.const_mul _
        have hrho_int : Integrable (fun x =>
            coefficient F ζ hζ U R P H part *
              ‖(part.rho_multiplier.op (jU v)).val x‖ ^ 2) μcov :=
          hrho_sq.const_mul _
        have hE_int : Integrable (fun x =>
            collarError F ζ hζ U R P H part.χ₀ part.χ (qcov x) *
              ‖(jU v).val x‖ ^ 2) μcov := by
          refine Integrable.mono_nonneg
            (g := fun x => errorSup F ζ hζ U R P H part * ‖(jU v).val x‖ ^ 2)
            (hw_sq.const_mul _) ?_ ?_ ?_
          · exact ((((collarError_continuous_nonnegative F ζ hζ U R P H part.χ₀
                part.χ).1.comp
                (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U)).measurable.aemeasurable).mul
              ((Lp.aestronglyMeasurable (jU v : Lp ℂ 2 μcov)).norm.aemeasurable.pow_const 2)).aestronglyMeasurable
          · filter_upwards with x
            exact mul_nonneg (part.error_nonnegative (qcov x)) (sq_nonneg _)
          · filter_upwards with x
            exact mul_le_mul_of_nonneg_right (hle (qcov x)) (sq_nonneg _)

        have hcore_ae := part.core_multiplier.ae_apply (jU v)
        have hrho_ae := part.rho_multiplier.ae_apply (jU v)
        have hpt_ae : (fun x =>
            dF *
                ‖(part.core_multiplier.op (jU v)).val x‖ ^ 2 +
              collarError F ζ hζ U R P H part.χ₀ part.χ (qcov x) *
                ‖(jU v).val x‖ ^ 2)
            ≤ᵐ[μcov] fun x => coefficient F ζ hζ U R P H part *
              ‖(part.rho_multiplier.op (jU v)).val x‖ ^ 2 := by
          filter_upwards [hcore_ae, hrho_ae] with x hcx hrx
          rw [hcx, hrx, norm_sq_ofReal_mul _ (part.core_range (qcov x)).1,
            norm_sq_ofReal_mul _ (part.rho_range (qcov x)).1]
          calc dF *
                (part.χ₀.val (qcov x) ^ 2 * ‖(jU v).val x‖ ^ 2) +
                collarError F ζ hζ U R P H part.χ₀ part.χ (qcov x) *
                  ‖(jU v).val x‖ ^ 2
              = (dF * part.χ₀.val (qcov x) ^ 2 +
                  collarError F ζ hζ U R P H part.χ₀ part.χ (qcov x)) *
                  ‖(jU v).val x‖ ^ 2 := by ring
            _ ≤ (coefficient F ζ hζ U R P H part * part.ρ.val (qcov x) ^ 2) *
                  ‖(jU v).val x‖ ^ 2 :=
                mul_le_mul_of_nonneg_right (hpt (qcov x)) (sq_nonneg _)
            _ = coefficient F ζ hζ U R P H part *
                  (part.ρ.val (qcov x) ^ 2 * ‖(jU v).val x‖ ^ 2) := by ring
        have hA0 : jU (ims.A none v) = part.core_multiplier.op (jU v) := by
          have h := DFunLike.congr_fun (ims.intertwines none) v
          simpa only [ContinuousLinearMap.comp_apply,
            KPContActualFormIMSIdentity.sectorMultiplier] using h
        have hnorm_core : ‖part.core_multiplier.op (jU v)‖ ^ 2 =
            ‖(part.core_multiplier.op (jU v) : Lp ℂ 2 μcov)‖ ^ 2 := by
          rw [Submodule.norm_coe]
        have hnorm_rho : ‖part.rho_multiplier.op (jU v)‖ ^ 2 =
            ‖(part.rho_multiplier.op (jU v) : Lp ℂ 2 μcov)‖ ^ 2 := by
          rw [Submodule.norm_coe]
        rw [hA0, hbind, hnorm_core, hnorm_rho,
          lp_norm_sq_here (μ := μcov) (part.core_multiplier.op (jU v) : Lp ℂ 2 μcov),
          lp_norm_sq_here (μ := μcov) (part.rho_multiplier.op (jU v) : Lp ℂ 2 μcov),
          ← weighted_integral_eq_here F ζ hζ U R P H μG hμG hR realization part v s hs,
          ← MeasureTheory.integral_const_mul dF
            (fun x => ‖(part.core_multiplier.op (jU v)).val x‖ ^ 2),
          ← MeasureTheory.integral_add hcore_int hE_int,
          ← MeasureTheory.integral_const_mul (coefficient F ζ hζ U R P H part)
            (fun x => ‖(part.rho_multiplier.op (jU v)).val x‖ ^ 2)]
        exact MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x =>
            add_nonneg (mul_nonneg ha (sq_nonneg _))
              (mul_nonneg (part.error_nonnegative (qcov x)) (sq_nonneg _)))
          hrho_int hpt_ae
    rw [← ims.mass v, Fintype.sum_option, mul_add, Finset.mul_sum]
    linarith [hcusp_sum, hsum_opt, hims, herr]
  have hjbU : ∀ u : HU, jU (bU u) = BU u := fun u => by
    have h := DFunLike.congr_fun
      (b_U_properties F ζ hζ U R P H μG hμG hR realization).1 u
    simpa using h
  have hife : ∀ u : HU, qU (bU u) = (inner ℂ (BU u) (u - BU u)).re := by
    intro u
    have hvar := hfr.friedrichs.variational
    obtain ⟨hR, h1, h2⟩ := hfr.friedrichs.genuine_inverse
    have hΔeq : ΔU ⟨BU u, hR u⟩ = u - BU u := by
      have h := h1 u
      rw [neg_smul, one_smul, sub_neg_eq_add] at h
      exact eq_sub_of_add_eq h
    obtain ⟨hmem, hform⟩ := (hvar (BU u) (u - BU u)).mp ⟨hR u, hΔeq⟩
    have hv := hform ⟨BU u, hmem⟩
    have hq : qU (bU u) = closedGradientEnergy AU ⟨BU u, hmem⟩ := by
      show ‖closedGradientCoordinate AU (bU u)‖ ^ 2 =
        closedGradientEnergy AU ⟨BU u, hmem⟩
      rw [coord_eq_closure_of_embedding AU (bU u) ⟨BU u, hmem⟩ (hjbU u),
        closedGradientEnergy]
    have hre : (inner ℂ (BU u) (u - BU u)).re =
        closedGradientEnergy AU ⟨BU u, hmem⟩ := by
      rw [← inner_conj_symm (𝕜 := ℂ) (BU u) (u - BU u), Complex.conj_re]
      rw [← hv, closedGradientForm, closedGradientEnergy, inner_self_eq_norm_sq_to_K]
      simp [← Complex.ofReal_pow]
    rw [hq, ← hre]
  refine ⟨remainder F ζ hζ U R P H μG hμG hR realization part mult,
    mult.localized_compact.smul (Real.sqrt (coefficient F ζ hζ U R P H part) : ℂ), fun u => ?_⟩
  simpa only [hjbU u, hife u, hnsq u] using hformbound (bU u)

end DedekindZetaZeroFree.KPContActualCompactRemainderEstimate

namespace DedekindZetaZeroFree

alias kp_cont_actual_compact_remainder_estimate := KPContActualCompactRemainderEstimate.compact_remainder_estimate

end DedekindZetaZeroFree

end
