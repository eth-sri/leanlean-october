module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Cusps.SquarePartitionsOfUnity

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualFormIMSIdentity

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings
open KPContActualSectorTestDifferentialDescent
open KPContActualSquareEndPartition KPContSectorLineL2Isometry

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

abbrev Index := Option (CuspIndex F ζ hζ U R P H)


local notation:max "current_Index" => Index F ζ hζ U R P H


local notation:max "current_SquareEndPartition" => SquareEndPartition F ζ hζ U R P H

def cutoff {T : ℝ} (partition : current_SquareEndPartition T) :
    current_Index → Cutoff F ζ hζ U R P H
  | none => partition.χ₀
  | some c => partition.χ c


local notation:max "current_cutoff" => cutoff F ζ hζ U R P H

def sectorMultiplier {T : ℝ} (partition : current_SquareEndPartition T) :
    (i : current_Index) →
      SectorMultiplier F ζ hζ U R P H (current_cutoff partition i)
  | none => partition.core_multiplier
  | some c => partition.cusp_multiplier c

variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

local notation "D" => KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization

abbrev Q_U := ClosedGradientSpace D

abbrev j_U : Q_U F ζ hζ U R P H μG hμG hR realization →L[ℂ]
    KPContSectorClosedLpSubspace.H F ζ hζ R U := closedGradientEmbedding D

abbrev closedGradient : Q_U F ζ hζ U R P H μG hμG hR realization →L[ℂ]
    KPContActualSectorCotangentL2.V F ζ hζ U R P H := closedGradientCoordinate D

abbrev q_U (v : Q_U F ζ hζ U R P H μG hμG hR realization) : ℝ :=
  ‖closedGradient F ζ hζ U R P H μG hμG hR realization v‖ ^ 2


local notation:max "current_S_U" => S_U F ζ hζ U R P H


local notation:max "current_j_U" => j_U F ζ hζ U R P H

def coreLift (f : current_S_U) :
    Q_U F ζ hζ U R P H μG hμG hR realization :=
  ⟨WithLp.toLp 2 (iota f, (D).closure
      (KPContActualSectorFriedrichsSynthesis.formTest F ζ hζ U R P H μG hμG hR realization f)),
    (D).closure.mem_graph
      (KPContActualSectorFriedrichsSynthesis.formTest F ζ hζ U R P H μG hμG hR realization f)⟩

local notation "Q" => Q_U F ζ hζ U R P H μG hμG hR realization
local notation "jQ" => current_j_U μG hμG hR realization
local notation "∇Q" => closedGradient F ζ hζ U R P H μG hμG hR realization
local notation "qQ" => q_U F ζ hζ U R P H μG hμG hR realization
local notation "lift" => coreLift F ζ hζ U R P H μG hμG hR realization

theorem coreLift_scalar (f : current_S_U) : jQ (lift f) = iota f := rfl

theorem coreLift_gradient (f : current_S_U) : ∇Q (lift f) = j (D_U f) := by
  change (D).closure
    (KPContActualSectorFriedrichsSynthesis.formTest F ζ hζ U R P H μG hμG hR realization f) = _
  have h := LinearPMap.apply_comp_inclusion (D).le_closure
    ⟨iota f, LinearMap.mem_range_self iota f⟩
  exact h.symm.trans (KPTestOperator.descend_image _ _ _ _ f)

theorem coreLift_product (η : Cutoff F ζ hζ U R P H) (f : current_S_U) :
    ∇Q (lift (scalarMultiply η f)) =
      j (cotangentMultiply η (D_U f)) + j (cutoffGradientTimes η f) := by
  rw [coreLift_gradient]
  rw [(kp_cont_actual_sector_test_differential_descent F ζ hζ μG hμG U R hR P H
    realization).differential_product, map_add]

theorem core_line_representative (v : Q) : ∃ s : BorelL2Sections F ζ hζ U R P H,
    sectorLineIsometry F ζ hζ U R P H (jQ v) = mk F ζ hζ U R P H s := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep (sectorLineIsometry F ζ hζ U R P H (jQ v))
  exact ⟨s, hs.symm⟩

theorem cutoff_range {T : ℝ} (partition : current_SquareEndPartition T)
    (i : current_Index) (x : Base F ζ hζ U) :
    0 ≤ (current_cutoff partition i).val x ∧
      (current_cutoff partition i).val x ≤ 1 := by
  cases i with
  | none => exact partition.core_range x
  | some c => exact partition.cusp_range c x

theorem cutoff_square_sum {T : ℝ} (partition : current_SquareEndPartition T)
    (x : Base F ζ hζ U) :
    ∑ i : current_Index, (current_cutoff partition i).val x ^ 2 = 1 := by
  simpa [Fintype.sum_option, cutoff] using partition.square_sum x

theorem cutoff_differential_bound {T : ℝ}
    (partition : current_SquareEndPartition T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : current_Index)
      (a : ActualChart (U := U) (H := H))
      (y : KPContCotangentOverlapRationalBranches.omega a),
      ‖cutoffDifferential (current_cutoff partition i) a y‖ ≤ Real.sqrt C := by
  obtain ⟨C, hC, hb⟩ := partition.error_bounded
  refine ⟨C, hC, fun i a y => ?_⟩
  have hn (η : Cutoff F ζ hζ U R P H) :
      0 ≤ differentialNormSquared F ζ hζ U R P H η
        (KPContCotangentOverlapRationalBranches.q a y.val) := by
    rw [differentialNormSquared_chart F ζ hζ U R P H η a y]
    positivity
  have he := hb (KPContCotangentOverlapRationalBranches.q a y.val)
  have hi : differentialNormSquared F ζ hζ U R P H
      (current_cutoff partition i)
      (KPContCotangentOverlapRationalBranches.q a y.val) ≤ C := by
    cases i with
    | none =>
      change differentialNormSquared F ζ hζ U R P H partition.χ₀ _ ≤ C
      have hs := Finset.sum_nonneg (fun c (_ : c ∈ Finset.univ) => hn (partition.χ c))
      dsimp [collarError] at he
      linarith
    | some c =>
      change differentialNormSquared F ζ hζ U R P H (partition.χ c) _ ≤ C
      have hs := Finset.single_le_sum (fun c (_ : c ∈ Finset.univ) => hn (partition.χ c))
        (Finset.mem_univ c)
      dsimp [collarError] at he
      linarith [hn partition.χ₀]
  rw [differentialNormSquared_chart] at hi
  exact (Real.le_sqrt (norm_nonneg _) hC).mpr hi


local notation:max "current_q" => KPContSectorCoveredQuotientVocabulary.q F ζ hζ U


local notation:max "current_sectorMultiplier" => sectorMultiplier F ζ hζ U R P H

theorem sector_mass {T : ℝ} (partition : current_SquareEndPartition T)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) :
    ∑ i : current_Index,
      ‖(current_sectorMultiplier partition i).op u‖ ^ 2 = ‖u‖ ^ 2 := by
  let M := fun i : current_Index =>
    (current_sectorMultiplier partition i).op
  have hae : ∀ᵐ x ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U,
      ∀ i : current_Index,
        ((M i u).val : KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ U → ℂ) x =
          ((current_cutoff partition i).val
            (current_q x) : ℂ) *
            (u.val : KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ U → ℂ) x := by
    rw [Filter.eventually_all]
    exact fun i => (current_sectorMultiplier partition i).ae_apply u
  have hp : (fun x => ∑ i : current_Index,
      inner ℂ ((M i u).val x) ((M i u).val x)) =ᵐ[
        KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U]
      (fun x => inner ℂ (u.val x) (u.val x)) := by
    filter_upwards [hae] with x hx
    simp only [hx, inner_self_eq_norm_sq_to_K, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow]
    push_cast
    have hs := cutoff_square_sum F ζ hζ U R P H partition
      (current_q x)
    norm_cast
    simp_rw [mul_pow, sq_abs]
    rw [← Finset.sum_mul, hs, one_mul]
  have hc : (∑ i, inner ℂ (M i u).val (M i u).val) = inner ℂ u.val u.val := by
    simp_rw [L2.inner_def]
    rw [← integral_finset_sum Finset.univ (fun i _ => L2.integrable_inner _ _)]
    exact integral_congr_ae hp
  simp only [inner_self_eq_norm_sq_to_K] at hc
  norm_cast at hc

theorem coreLift_eq_graphTestLift (f : current_S_U) :
    lift f = KPContActualFormCutoffClosedProduct.graphTestLift
      F ζ hζ U R P H μG hμG hR realization f := by
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 ℂ _).injective
  apply Prod.ext
  · rfl
  · exact coreLift_gradient F ζ hζ U R P H μG hμG hR realization f

theorem partition_lifts {T : ℝ} (partition : current_SquareEndPartition T) :
    ∃ A : current_Index → Q →L[ℂ] Q,
      (∀ i, (jQ).comp (A i) =
        (current_sectorMultiplier partition i).op.comp jQ) ∧
      ∀ i (f : current_S_U),
        A i (lift f) = lift (scalarMultiply (current_cutoff partition i) f) := by
  obtain ⟨C, hC, hd⟩ := cutoff_differential_bound F ζ hζ U R P H partition
  have hex (i : current_Index) :
      ∃ A : Q →L[ℂ] Q, (jQ).comp A =
        (current_sectorMultiplier partition i).op.comp jQ ∧
        ∀ f : current_S_U,
          A (lift f) = lift (scalarMultiply (current_cutoff partition i) f) := by
    obtain ⟨A, hA, ht⟩ := KPContActualFormCutoffClosedProduct.exists_lift
      F ζ hζ U R P H μG hμG hR realization
      (current_cutoff partition i)
      (current_sectorMultiplier partition i)
      1 (Real.sqrt C) zero_le_one (Real.sqrt_nonneg C)
      (fun x => by rw [abs_of_nonneg (cutoff_range F ζ hζ U R P H partition i x).1];
                   exact (cutoff_range F ζ hζ U R P H partition i x).2)
      (hd i)
    refine ⟨A, hA, fun f => ?_⟩
    simpa only [coreLift_eq_graphTestLift] using ht f
  choose A hA ht using hex
  exact ⟨A, hA, ht⟩


local notation:max "current_collarError" => collarError F ζ hζ U R P H


local notation:max "current_sectionNorm" => KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ U R P H

theorem collar_error_integrable {T : ℝ}
    (partition : current_SquareEndPartition T)
    (s : BorelL2Sections F ζ hζ U R P H) :
    Integrable (fun x => current_collarError partition.χ₀ partition.χ x *
      current_sectionNorm s.val x ^ 2)
      (KPContActualSectorCotangentL2.muU F ζ hζ U R P) := by
  have hm : Measurable (fun x =>
      current_sectionNorm s.val x ^ 2) := by
    have h := ENNReal.measurable_toReal.comp
      (squaredNorm_measurable F ζ hζ U R P H s.val s.property.1)
    simpa only [Function.comp_def, squaredNorm, ENNReal.toReal_ofReal (sq_nonneg _)] using h
  have hi : Integrable (fun x =>
      current_sectionNorm s.val x ^ 2)
      (KPContActualSectorCotangentL2.muU F ζ hζ U R P) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa only [Real.norm_of_nonneg (sq_nonneg _), normIntegral, squaredNorm] using s.property.2
  have hc : Continuous (current_collarError partition.χ₀ partition.χ) := by
    unfold collarError
    apply Continuous.add
    · exact (Classical.choose_spec
        (differentialNormSquared_descends F ζ hζ U R P H partition.χ₀)).1.1
    · apply continuous_finset_sum
      intro c _
      exact (Classical.choose_spec
        (differentialNormSquared_descends F ζ hζ U R P H (partition.χ c))).1.1
  obtain ⟨C, _, hb⟩ := partition.error_bounded
  apply hi.bdd_mul hc.measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (partition.error_nonnegative x)]
    exact hb x)

theorem coreLift_dense : DenseRange (lift) := by
  intro v
  have hv : (jQ v) ∈ (D).closure.domain :=
    (D).closure.mem_domain_of_mem_graph v.property
  obtain ⟨s, hs, hds, _⟩ :=
    (kp_cont_actual_sector_friedrichs_synthesis F ζ hζ μG hμG U R hR P H
      realization).form_core ⟨jQ v, hv⟩
  have hg : (D).closure ⟨jQ v, hv⟩ = ∇Q v :=
    (D).closure.mem_graph_snd_inj ((D).closure.mem_graph ⟨jQ v, hv⟩) v.property rfl
  have ht : Filter.Tendsto (fun n => (lift (s n)).val) Filter.atTop (nhds v.val) := by
    have hp := (WithLp.prod_continuous_toLp 2
      (KPContSectorClosedLpSubspace.H F ζ hζ R U)
      (KPContActualSectorCotangentL2.V F ζ hζ U R P H)).tendsto
        ((jQ v), ∇Q v)
    have hpair := hs.prodMk_nhds (hg ▸ hds)
    have hh := hp.comp hpair
    convert hh using 1
    · funext n
      apply (WithLp.linearEquiv 2 ℂ _).injective
      exact Prod.ext rfl (coreLift_gradient F ζ hζ U R P H μG hμG hR realization (s n))
    · rfl
  have hts : Filter.Tendsto (fun n => lift (s n)) Filter.atTop (nhds v) :=
    tendsto_subtype_rng.mpr ht
  exact isClosed_closure.mem_of_tendsto hts
    (Filter.Eventually.of_forall (fun n => subset_closure ⟨s n, rfl⟩))

theorem finite_norm_expansion {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (c : ι → ℝ) (d : ι → E) (w : E) (z : ℂ)
    (hc : ∑ i, c i ^ 2 = 1) (hd : ∑ i, (c i : ℂ) • d i = 0) :
    ∑ i, ‖(c i : ℂ) • w + z • d i‖ ^ 2 = ‖w‖ ^ 2 + ‖z‖ ^ 2 * ∑ i, ‖d i‖ ^ 2 := by
  have hx : ∑ i, inner ℂ ((c i : ℂ) • w) (z • d i) = 0 := by
    simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    have he : (∑ i, z * ((c i : ℂ) * inner ℂ w (d i))) =
        z * inner ℂ w (∑ i, (c i : ℂ) • d i) := by
      simp only [inner_sum, inner_smul_right, Finset.mul_sum]
    rw [he, hd, inner_zero_right, mul_zero]
  simp_rw [norm_add_sq (𝕜 := ℂ), norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hc]
  have hr : ∑ i, (inner ℂ ((c i : ℂ) • w) (z • d i)).re = 0 := by
    rw [← Complex.re_sum, hx, Complex.zero_re]
  rw [← Finset.mul_sum]
  change 1 * ‖w‖ ^ 2 + 2 * (∑ i, (inner ℂ ((c i : ℂ) • w) (z • d i)).re) +
    ‖z‖ ^ 2 * ∑ i, ‖d i‖ ^ 2 = _
  rw [hr]
  ring

include μG hμG hR realization in

theorem test_weighted_cutoff_gradient_zero {T : ℝ}
    (partition : current_SquareEndPartition T)
    (f : current_S_U) :
    ∑ i : current_Index,
      cotangentMultiply (current_cutoff partition i)
        (cutoffGradientTimes (current_cutoff partition i) f) = 0 := by
  let η := current_cutoff partition
  have hs : ∑ i : current_Index,
      scalarMultiply (η i) (scalarMultiply (η i) f) = f := by
    apply Subtype.ext
    funext a y
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change (∑ i, cutoffLift (η i) a y * (cutoffLift (η i) a y * f.val a y)) = f.val a y
    have hsq := cutoff_square_sum F ζ hζ U R P H partition
      (KPContCotangentOverlapRationalBranches.q a y.val)
    simp only [cutoffLift]
    simp_rw [← mul_assoc, ← pow_two]
    rw [← Finset.sum_mul]
    norm_cast at hsq ⊢
    simpa [η, hsq] using congrArg (fun c : ℝ => (c : ℂ) * f.val a y) hsq
  have hds := congrArg D_U hs
  rw [map_sum] at hds
  have hprod := (kp_cont_actual_sector_test_differential_descent F ζ hζ μG hμG U R hR P H
    realization).differential_product
  simp_rw [hprod] at hds
  apply Subtype.ext
  apply Subtype.ext
  funext a y
  apply PiLp.ext
  intro k
  simp only [Submodule.coe_sum, Submodule.coe_zero, Finset.sum_apply, Pi.zero_apply,
    WithLp.ofLp_sum, Finset.sum_apply, map_zero, PiLp.zero_apply]
  have he := congrArg
    (fun W : T_U F ζ hζ U R P H =>
      KPContActualCotangentMeasurableFamilies.coefficient W.val a y k) hds
  change ∑ i, cutoffLift (η i) a y *
    (f.val a y * cutoffDifferential (η i) a y k) = 0
  simp only [KPContActualCotangentMeasurableFamilies.coefficient, Submodule.coe_sum,
    Submodule.coe_add, Finset.sum_apply, Pi.add_apply, WithLp.ofLp_sum, WithLp.ofLp_add,
    cotangentMultiply, cutoffGradientTimes, scalarMultiply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul] at he
  have hsq : ∑ i, (cutoffLift (η i) a y) ^ 2 = (1 : ℂ) := by
    simp only [cutoffLift]
    norm_cast
    exact cutoff_square_sum F ζ hζ U R P H partition _
  change (∑ i, (cutoffLift (η i) a y *
    (cutoffLift (η i) a y * KPContActualCotangentMeasurableFamilies.coefficient (D_U f).val a y k +
      f.val a y * cutoffDifferential (η i) a y k) +
    (cutoffLift (η i) a y * f.val a y) * cutoffDifferential (η i) a y k)) =
    KPContActualCotangentMeasurableFamilies.coefficient (D_U f).val a y k at he
  have he' : (∑ i, cutoffLift (η i) a y ^ 2 *
      KPContActualCotangentMeasurableFamilies.coefficient (D_U f).val a y k) +
      2 * ∑ i, cutoffLift (η i) a y * (f.val a y * cutoffDifferential (η i) a y k) =
      KPContActualCotangentMeasurableFamilies.coefficient (D_U f).val a y k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    convert he using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← Finset.sum_mul, hsq, one_mul] at he'
  linear_combination (1 / 2 : ℂ) * he'

include μG hμG hR realization in

theorem test_chart_ims {T : ℝ} (partition : current_SquareEndPartition T)
    (f : current_S_U) (a : ActualChart (U := U) (H := H))
    (y : KPContCotangentOverlapRationalBranches.omega a) :
    (∑ i : current_Index,
      ‖KPContActualCotangentMeasurableFamilies.coefficient
        (D_U (scalarMultiply (current_cutoff partition i) f)).val a y‖ ^ 2) =
      ‖KPContActualCotangentMeasurableFamilies.coefficient (D_U f).val a y‖ ^ 2 +
      current_collarError partition.χ₀ partition.χ
        (KPContCotangentOverlapRationalBranches.q a y.val) * ‖f.val a y‖ ^ 2 := by
  let η := current_cutoff partition
  have hd := congrArg
    (fun W : T_U F ζ hζ U R P H =>
      KPContActualCotangentMeasurableFamilies.coefficient W.val a y)
    (test_weighted_cutoff_gradient_zero F ζ hζ U R P H μG hμG hR realization partition f)
  simp only [KPContActualCotangentMeasurableFamilies.coefficient, Submodule.coe_sum,
    Submodule.coe_zero, Finset.sum_apply, Pi.zero_apply, cotangentMultiply,
    cutoffGradientTimes] at hd
  have hx := finite_norm_expansion
    (fun i => (η i).val (KPContCotangentOverlapRationalBranches.q a y.val))
    (fun i => f.val a y • cutoffDifferential (η i) a y)
    (KPContActualCotangentMeasurableFamilies.coefficient (D_U f).val a y)
    1 (cutoff_square_sum F ζ hζ U R P H partition _) hd
  simp only [norm_one, one_pow, one_mul, one_smul, norm_smul, mul_pow] at hx
  simp_rw [(kp_cont_actual_sector_test_differential_descent F ζ hζ μG hμG U R hR P H
    realization).differential_product]
  change (∑ i, ‖cutoffLift (η i) a y •
    KPContActualCotangentMeasurableFamilies.coefficient (D_U f).val a y +
    f.val a y • cutoffDifferential (η i) a y‖ ^ 2) = _
  unfold cutoffLift
  rw [hx, ← Finset.mul_sum]
  have he : current_collarError partition.χ₀ partition.χ
      (KPContCotangentOverlapRationalBranches.q a y.val) =
      ∑ i : current_Index, ‖cutoffDifferential (η i) a y‖ ^ 2 := by
    simp only [Fintype.sum_option, η, cutoff, collarError]
    simp_rw [differentialNormSquared_chart]
  rw [he, mul_comm]

private theorem q_coordinates_actual
    (a : KPContActualCotangentCountableShrinking.ShrunkChart F ζ hζ U R P H)
    (y : a.domain) :
    KPContCotangentOverlapRationalBranches.q a
      (KPContActualCotangentPieceHilbertSum.coordinates a y).val = a.toBase y := by
  have hi : ∀ z : KPCuspGenuineMonodromy.SymmetricSpace F,
      KPContCotangentActualOverlap.labeledA (KPContCotangentActualOverlap.placeEquiv F ζ hζ)
        (KPContCotangentActualOverlap.labeledAInv
          (KPContCotangentActualOverlap.placeEquiv F ζ hζ) z) = z := by
    intro z; funext k
    simp [KPContCotangentActualOverlap.labeledA, KPContCotangentActualOverlap.labeledAInv]
  simp only [KPContActualCotangentCountableShrinking.ShrunkChart.toBase,
    KPContCotangentOverlapRationalBranches.q,
    KPContActualCotangentPieceHilbertSum.coordinates]
  rw [hi]

include μG hμG hR realization in

theorem test_base_ims {T : ℝ} (partition : current_SquareEndPartition T)
    (f : current_S_U) (x : Base F ζ hζ U) :
    (∑ i : current_Index,
      (KPContActualCotangentMeasurableFamilies.normSquare
        (D_U (scalarMultiply (current_cutoff partition i) f)).val x : ℝ)) =
      (KPContActualCotangentMeasurableFamilies.normSquare (D_U f).val x : ℝ) +
      current_collarError partition.χ₀ partition.χ x *
        (scalarPair f f x).re := by
  let cover := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  have hx : x ∈ ⋃ n, (cover.chart n).baseDomain := by
    rw [cover.covers]; exact Set.mem_univ x
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y, hy⟩ := hn
  have hqx : KPContCotangentOverlapRationalBranches.q (cover.chart n)
      (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y).val = x := by
    rw [q_coordinates_actual F ζ hζ U R P H (cover.chart n) y, hy]
  have hsum : (∑ i : current_Index,
      (KPContActualCotangentMeasurableFamilies.normSquare
        (D_U (scalarMultiply (current_cutoff partition i) f)).val x : ℝ)) =
      ∑ i : current_Index,
        ‖KPContActualCotangentMeasurableFamilies.coefficient
          (D_U (scalarMultiply (current_cutoff partition i) f)).val
          (cover.chart n)
          (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← hqx, KPContActualCotangentMeasurableFamilies.normSquare_chart]
    simp
  have hb : (KPContActualCotangentMeasurableFamilies.normSquare (D_U f).val x : ℝ) =
      ‖KPContActualCotangentMeasurableFamilies.coefficient (D_U f).val (cover.chart n)
          (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y)‖ ^ 2 := by
    rw [← hqx, KPContActualCotangentMeasurableFamilies.normSquare_chart]
    simp
  have hs : (scalarPair f f x).re =
      ‖f.val (cover.chart n)
        (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y)‖ ^ 2 := by
    rw [← hqx, (kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H
      realization).scalar_pair_chart f f (cover.chart n)
        (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y)]
    have hz : inner ℂ (f.val (cover.chart n)
          (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y))
        (f.val (cover.chart n)
          (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y)) =
        ((‖f.val (cover.chart n)
          (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y)‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_num
    rw [hz, Complex.ofReal_re]
  rw [hsum, test_chart_ims F ζ hζ U R P H μG hμG hR realization partition f (cover.chart n)
    (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y), ← hb, ← hs]
  rw [← hqx]

private theorem sectionFields_apply_actual
    (s : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H)
    (a : KPContActualCotangentCountableShrinking.ShrunkChart F ζ hζ U R P H)
    (x : KPContCotangentOverlapRationalBranches.omega a) :
    sectionFields s a x = (s a.component).val
      (KPContCotangentActualOverlap.labeledA
        (KPContCotangentActualOverlap.placeEquiv F ζ hζ) x.val) := by
  have hcoe : (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient
      s x.val =
      (KPCuspGenuineMonodromy.chi F ζ hζ
          ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).splitting x.val) : ℂ) *
        (s a.component).val
          ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).kind.representative •
            KPContCotangentActualOverlap.labeledA
              (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).places x.val) := rfl
  rw [sectionFields, hcoe]
  simp [KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
    KPContCotangentActualOverlap.ChartKind.representative]

private theorem measurable_sectionNorm (s : BorelL2Sections F ζ hζ U R P H) :
    Measurable (current_sectionNorm s.val) := by
  have hme : Measurable (fun x =>
      current_sectionNorm s.val x ^ 2) := by
    have h := ENNReal.measurable_toReal.comp
      (squaredNorm_measurable F ζ hζ U R P H s.val s.property.1)
    simpa only [Function.comp_def, squaredNorm, ENNReal.toReal_ofReal (sq_nonneg _)] using h
  have heq : current_sectionNorm s.val =
      fun x => Real.sqrt
        (current_sectionNorm s.val x ^ 2) := by
    funext x
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    obtain ⟨⟨i, w⟩, rfl⟩ := (H.atlas U).components.surjective x
    obtain ⟨z, rfl⟩ := Quotient.exists_rep w
    rw [KPContSectorSmoothFramesSupport.sectionNorm_component]
    exact norm_nonneg _
  rw [heq]; exact hme.sqrt


local notation:max "current_S" => KPContSectorScalarLineAlgebra.S F ζ hζ U R P H


local notation:max "current_scalarRepresentative" => KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H

theorem sectionNorm_ae_eq_of_mk_eq (s t : BorelL2Sections F ζ hζ U R P H)
    (h : mk F ζ hζ U R P H s = mk F ζ hζ U R P H t) :
    current_sectionNorm s.val
      =ᵐ[KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U]
      current_sectionNorm t.val := by
  have hnull := (KPContSectorLineL2Isometry.mk_eq_mk_iff F ζ hζ U R P H s t).mp h
  have hae := (KPContSectorLineL2Isometry.null_iff_scalar_ae_eq F ζ hζ U R P H s t).mp hnull
  have hq : AEMeasurable (current_q)
      (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U) :=
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).aemeasurable
  rw [← KPContSectorFixedPushforwardSupport.map_q_coveredMeasure F ζ hζ R P U]
  apply (ae_map_iff hq (measurableSet_eq_fun (measurable_sectionNorm F ζ hζ U R P H s)
    (measurable_sectionNorm F ζ hζ U R P H t))).mpr
  have hsv : s.val = current_S
      (current_scalarRepresentative s.val) :=
    ((current_S).apply_symm_apply s.val).symm
  have htv : t.val = current_S
      (current_scalarRepresentative t.val) :=
    ((current_S).apply_symm_apply t.val).symm
  filter_upwards [hae] with v hv
  rw [hsv, KPContSectorSmoothFramesSupport.sectionNorm_pullback, htv,
    KPContSectorSmoothFramesSupport.sectionNorm_pullback, hv]

include μG hμG hR realization in

theorem sectorLineIsometry_iota (f : current_S_U) :
    KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ U R P H (iota f) =
      mk F ζ hζ U R P H (borelS F ζ hζ U R P H
        ⟨scalarCovered f, (kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H
            realization).scalar_continuous f |>.measurable,
          KPContActualSectorTestEmbeddings.scalar_memLp f⟩) :=
  (kp_cont_sector_line_l2_isometry F ζ hζ U R P H).forward (iota f)
    ⟨scalarCovered f, (kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H
        realization).scalar_continuous f |>.measurable,
      KPContActualSectorTestEmbeddings.scalar_memLp f⟩
    ((kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H
        realization).scalar_represented f).symm

include μG hμG hR realization in

theorem sectionNorm_scalarSections_sq (f : current_S_U) (x : Base F ζ hζ U) :
    current_sectionNorm (scalarSections f) x ^ 2 =
      (scalarPair f f x).re := by
  let cover := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  have hx : x ∈ ⋃ n, (cover.chart n).baseDomain := by
    rw [cover.covers]; exact Set.mem_univ x
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y, hy⟩ := hn
  have hqx : KPContCotangentOverlapRationalBranches.q (cover.chart n)
      (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y).val = x := by
    rw [q_coordinates_actual F ζ hζ U R P H (cover.chart n) y, hy]
  have hfields : sectionFields (scalarSections f) = f.val :=
    (Classical.choose_spec (scalar_gluing (F := F) (ζ := ζ) (hζ := hζ) (U := U)
      (R := R) (P := P) (H := H) f)).1.2.2
  have hq : KPContCotangentOverlapRationalBranches.q (cover.chart n)
      (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y).val =
      (H.atlas U).components ⟨(cover.chart n).component, Quotient.mk _
        (KPContCotangentActualOverlap.labeledA (KPContCotangentActualOverlap.placeEquiv F ζ hζ)
          (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y).val)⟩ := by
    simp only [KPContCotangentOverlapRationalBranches.q, KPCuspSiegel.projection,
      (H.atlas U).components_formula]
  rw [← hqx, (kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H
    realization).scalar_pair_chart f f (cover.chart n)
      (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y)]
  rw [hq, KPContSectorSmoothFramesSupport.sectionNorm_component,
    ← sectionFields_apply_actual (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P)
      (H := H) (scalarSections f) (cover.chart n)
      (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y),
    congrFun (congrFun hfields (cover.chart n))
      (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y)]
  have hz : inner ℂ (f.val (cover.chart n)
        (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y))
      (f.val (cover.chart n)
        (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y)) =
      ((‖f.val (cover.chart n)
        (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y)‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_num
  rw [hz, Complex.ofReal_re]

include μG hμG hR realization in

theorem test_ims_scalar {T : ℝ} (partition : current_SquareEndPartition T)
    (f : current_S_U) :
    (∑ i : current_Index,
        ‖j (D_U (scalarMultiply (current_cutoff partition i) f))‖ ^ 2) =
      ‖j (D_U f)‖ ^ 2 +
      ∫ x, current_collarError partition.χ₀ partition.χ x *
        (scalarPair f f x).re ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
  have hte := kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H realization
  have hcl2 := kp_cont_actual_sector_cotangent_l2 F ζ hζ μG hμG U R hR P H realization
  have hinte (g : current_S_U) : Integrable (fun x =>
      (KPContActualCotangentMeasurableFamilies.normSquare (D_U g).val x : ℝ))
      (KPContActualSectorCotangentL2.muU F ζ hζ U R P) := by
    have h := hte.cotangent_base_memLp (D_U g)
    refine h.integrable_sq.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Real.sq_sqrt (KPContActualCotangentMeasurableFamilies.normSquare
      (D_U g).val x).coe_nonneg]
  obtain ⟨C, hC, hb⟩ := partition.error_bounded
  have hEc : Continuous (current_collarError partition.χ₀ partition.χ) := by
    unfold collarError
    apply Continuous.add
    · exact (Classical.choose_spec
        (differentialNormSquared_descends F ζ hζ U R P H partition.χ₀)).1.1
    · apply continuous_finset_sum
      intro c _
      exact (Classical.choose_spec
        (differentialNormSquared_descends F ζ hζ U R P H (partition.χ c))).1.1
  have hEbdd : ∀ᵐ x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P,
      ‖collarError F ζ hζ U R P H partition.χ₀ partition.χ x‖ ≤ C :=
    Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (partition.error_nonnegative x)]
      exact hb x)
  have hscal : Integrable (fun x => (scalarPair f f x).re)
      (KPContActualSectorCotangentL2.muU F ζ hζ U R P) :=
    (hte.scalar_pair_integrable f f).re
  have hIntScalar : Integrable (fun x =>
      current_collarError partition.χ₀ partition.χ x * (scalarPair f f x).re)
      (KPContActualSectorCotangentL2.muU F ζ hζ U R P) :=
    hscal.bdd_mul hEc.aestronglyMeasurable hEbdd
  have hWi (i : current_Index) :
      ‖j (D_U (scalarMultiply (current_cutoff partition i) f))‖ ^ 2 =
      ∫ x, (KPContActualCotangentMeasurableFamilies.normSquare
        (D_U (scalarMultiply (current_cutoff partition i) f)).val x : ℝ)
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P :=
    hcl2.norm_integral _
      (KPContActualSectorTestEmbeddings.cotangentSquareFamily
        (D_U (scalarMultiply (current_cutoff partition i) f))) rfl
  have hW : ‖j (D_U f)‖ ^ 2 =
      ∫ x, (KPContActualCotangentMeasurableFamilies.normSquare (D_U f).val x : ℝ)
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P :=
    hcl2.norm_integral _ (KPContActualSectorTestEmbeddings.cotangentSquareFamily (D_U f)) rfl
  have hsum_int : (∫ x, (∑ i : current_Index,
        (KPContActualCotangentMeasurableFamilies.normSquare
          (D_U (scalarMultiply (current_cutoff partition i) f)).val x : ℝ))
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) =
      ∑ i : current_Index, ∫ x,
        (KPContActualCotangentMeasurableFamilies.normSquare
          (D_U (scalarMultiply (current_cutoff partition i) f)).val x : ℝ)
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P :=
    integral_finset_sum _
      (fun i _ => hinte (scalarMultiply (current_cutoff partition i) f))
  have hcongr : (fun x => (∑ i : current_Index,
        (KPContActualCotangentMeasurableFamilies.normSquare
          (D_U (scalarMultiply (current_cutoff partition i) f)).val x : ℝ)))
      =ᵐ[KPContActualSectorCotangentL2.muU F ζ hζ U R P]
      (fun x => (KPContActualCotangentMeasurableFamilies.normSquare (D_U f).val x : ℝ)
        + current_collarError partition.χ₀ partition.χ x * (scalarPair f f x).re) :=
    Filter.Eventually.of_forall
      (fun x => test_base_ims F ζ hζ U R P H μG hμG hR realization partition f x)
  have hsplit : (∫ x, ((KPContActualCotangentMeasurableFamilies.normSquare (D_U f).val x : ℝ)
        + current_collarError partition.χ₀ partition.χ x * (scalarPair f f x).re)
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) =
      (∫ x, (KPContActualCotangentMeasurableFamilies.normSquare (D_U f).val x : ℝ)
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P)
        + ∫ x, current_collarError partition.χ₀ partition.χ x * (scalarPair f f x).re
          ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P :=
    integral_add (hinte f) hIntScalar
  calc (∑ i : current_Index,
        ‖j (D_U (scalarMultiply (current_cutoff partition i) f))‖ ^ 2)
      = ∑ i : current_Index, ∫ x,
          (KPContActualCotangentMeasurableFamilies.normSquare
            (D_U (scalarMultiply (current_cutoff partition i) f)).val x : ℝ)
          ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P :=
        Finset.sum_congr rfl (fun i _ => hWi i)
    _ = ∫ x, (∑ i : current_Index,
          (KPContActualCotangentMeasurableFamilies.normSquare
            (D_U (scalarMultiply (current_cutoff partition i) f)).val x : ℝ))
          ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := hsum_int.symm
    _ = ∫ x, ((KPContActualCotangentMeasurableFamilies.normSquare (D_U f).val x : ℝ)
          + current_collarError partition.χ₀ partition.χ x * (scalarPair f f x).re)
          ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := integral_congr_ae hcongr
    _ = (∫ x, (KPContActualCotangentMeasurableFamilies.normSquare (D_U f).val x : ℝ)
          ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P)
          + ∫ x, current_collarError partition.χ₀ partition.χ x * (scalarPair f f x).re
            ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := hsplit
    _ = ‖j (D_U f)‖ ^ 2 +
          ∫ x, current_collarError partition.χ₀ partition.χ x * (scalarPair f f x).re
            ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by rw [hW]

include μG hμG hR realization in

theorem test_ims {T : ℝ} (partition : current_SquareEndPartition T)
    (f : current_S_U) (s : BorelL2Sections F ζ hζ U R P H)
    (hs : KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ U R P H (iota f) =
      mk F ζ hζ U R P H s) :
    (∑ i : current_Index,
        ‖j (D_U (scalarMultiply (current_cutoff partition i) f))‖ ^ 2) =
      ‖j (D_U f)‖ ^ 2 +
      ∫ x, current_collarError partition.χ₀ partition.χ x *
        current_sectionNorm s.val x ^ 2
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
  rw [test_ims_scalar F ζ hζ U R P H μG hμG hR realization partition f]
  congr 1
  let fB : BorelL2Scalars F ζ hζ U R :=
    ⟨scalarCovered f, (kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H
        realization).scalar_continuous f |>.measurable,
      KPContActualSectorTestEmbeddings.scalar_memLp f⟩
  have hs0val : (borelS F ζ hζ U R P H fB).val = scalarSections f := by
    show current_S fB.val = scalarSections f
    rw [show fB.val = current_scalarRepresentative
        (scalarSections f) from rfl]
    exact (current_S).apply_symm_apply (scalarSections f)
  have hmk : mk F ζ hζ U R P H s = mk F ζ hζ U R P H (borelS F ζ hζ U R P H fB) := by
    rw [← hs, sectorLineIsometry_iota F ζ hζ U R P H μG hμG hR realization f]
  have hsn := sectionNorm_ae_eq_of_mk_eq F ζ hζ U R P H s (borelS F ζ hζ U R P H fB) hmk
  rw [hs0val] at hsn
  apply integral_congr_ae
  filter_upwards [hsn] with x hx
  rw [hx, sectionNorm_scalarSections_sq F ζ hζ U R P H μG hμG hR realization f x]

private theorem lp_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
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

private theorem continuous_weighted_l2 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (E : α → ℝ) (hEmeas : AEStronglyMeasurable E μ) (C : ℝ)
    (hE0 : ∀ᵐ x ∂μ, 0 ≤ E x) (hEbd : ∀ᵐ x ∂μ, E x ≤ C) :
    Continuous (fun w : Lp ℂ 2 μ => ∫ x, E x * ‖w x‖ ^ 2 ∂μ) := by
  have hfmeas : AEStronglyMeasurable (fun x => (Real.sqrt (E x) : ℂ)) μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      hEmeas.aemeasurable.sqrt.aestronglyMeasurable
  have hfbdd : ∀ᵐ x ∂μ, ‖(Real.sqrt (E x) : ℂ)‖ ≤ Real.sqrt C := by
    filter_upwards [hE0, hEbd] with x h0 hb
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt hb
  have hf : MemLp (fun x => (Real.sqrt (E x) : ℂ)) ⊤ μ :=
    memLp_top_of_bound hfmeas (Real.sqrt C) hfbdd
  let fL : Lp ℂ ⊤ μ := hf.toLp (fun x => (Real.sqrt (E x) : ℂ))
  have hfL : ∀ᵐ x ∂μ, fL x = (Real.sqrt (E x) : ℂ) := hf.coeFn_toLp
  have hMcont : Continuous (fun w : Lp ℂ 2 μ => (fL • w : Lp ℂ 2 μ)) := by
    apply LipschitzWith.continuous
    refine LipschitzWith.of_dist_le_mul (K := ‖fL‖₊) (fun w w' => ?_)
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖(fL • w : Lp ℂ 2 μ) - fL • w'‖ = ‖(fL • (w - w') : Lp ℂ 2 μ)‖ := by
          rw [sub_eq_add_neg, ← Lp.smul_neg, ← Lp.add_smul, sub_eq_add_neg]
      _ ≤ ‖fL‖ * ‖w - w'‖ := Lp.norm_smul_le fL (w - w')
  have hkey : ∀ w : Lp ℂ 2 μ, (∫ x, E x * ‖w x‖ ^ 2 ∂μ) = ‖(fL • w : Lp ℂ 2 μ)‖ ^ 2 := by
    intro w
    rw [lp_norm_sq (fL • w : Lp ℂ 2 μ)]
    apply integral_congr_ae
    have hsl : (fL • w : Lp ℂ 2 μ) =ᵐ[μ] (fL : α → ℂ) • (w : α → ℂ) :=
      Lp.coeFn_lpSMul fL w
    filter_upwards [hsl, hfL, hE0] with x hx hfx h0
    simp only [hx, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, hfx, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt h0]
  rw [show (fun w : Lp ℂ 2 μ => ∫ x, E x * ‖w x‖ ^ 2 ∂μ)
      = fun w => ‖(fL • w : Lp ℂ 2 μ)‖ ^ 2 from funext hkey]
  exact hMcont.norm.pow 2

private theorem weighted_integral_eq {T : ℝ}
    (partition : current_SquareEndPartition T)
    (w : Q_U F ζ hζ U R P H μG hμG hR realization)
    (s : BorelL2Sections F ζ hζ U R P H)
    (hs : KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ U R P H
        (current_j_U μG hμG hR realization w) = mk F ζ hζ U R P H s) :
    (∫ x, current_collarError partition.χ₀ partition.χ
        (current_q x) *
        ‖(current_j_U μG hμG hR realization w).val x‖ ^ 2
        ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U) =
      ∫ x, current_collarError partition.χ₀ partition.χ x *
        current_sectionNorm s.val x ^ 2
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
  have hs' : (KPContSectorLineL2Isometry.lineToSector F ζ hζ U R P H).symm
      (current_j_U μG hμG hR realization w) = mk F ζ hζ U R P H s := hs
  have hts : KPContSectorLineL2Isometry.toSector F ζ hζ U R P H s =
      current_j_U μG hμG hR realization w := by
    have h := congrArg (KPContSectorLineL2Isometry.lineToSector F ζ hζ U R P H) hs'
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hval : (current_j_U μG hμG hR realization w).val =
      (KPContSectorLineL2Isometry.representative_memLp F ζ hζ U R P H s).toLp
        (current_scalarRepresentative s.val).val := by
    rw [← hts]; rfl
  have hcoe : (KPContSectorLineL2Isometry.representative_memLp F ζ hζ U R P H s).toLp
        (current_scalarRepresentative s.val).val
      =ᵐ[KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U]
        (current_scalarRepresentative s.val).val :=
    (KPContSectorLineL2Isometry.representative_memLp F ζ hζ U R P H s).coeFn_toLp
  have hstep1 : (∫ x, current_collarError partition.χ₀ partition.χ
        (current_q x) *
        ‖(current_j_U μG hμG hR realization w).val x‖ ^ 2
        ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U) =
      ∫ x, current_collarError partition.χ₀ partition.χ
        (current_q x) *
        ‖(current_scalarRepresentative s.val).val x‖ ^ 2
        ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U := by
    apply integral_congr_ae
    filter_upwards [hcoe] with x hx
    rw [hval, hx]
  rw [hstep1]
  rw [show KPContActualSectorCotangentL2.muU F ζ hζ U R P =
      Measure.map (current_q)
        (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U) from
      (KPContSectorFixedPushforwardSupport.map_q_coveredMeasure F ζ hζ R P U).symm]
  rw [MeasureTheory.integral_map]
  · apply integral_congr_ae
    filter_upwards with x
    have hS : current_S
        (current_scalarRepresentative s.val) = s.val :=
      (current_S).apply_symm_apply s.val
    have hsn : current_sectionNorm s.val
        (current_q x) =
        ‖(current_scalarRepresentative s.val).val x‖ := by
      conv_lhs => rw [← hS]
      exact KPContSectorSmoothFramesSupport.sectionNorm_pullback F ζ hζ U R P H _ x
    rw [hsn]
  · exact (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).aemeasurable
  · have hEc : Continuous (current_collarError partition.χ₀ partition.χ) := by
      unfold collarError
      apply Continuous.add
      · exact continuous_differentialNormSquared F ζ hζ U R P H partition.χ₀
      · apply continuous_finset_sum
        intro c _
        exact continuous_differentialNormSquared F ζ hζ U R P H (partition.χ c)
    have hm : Measurable (fun y => current_collarError partition.χ₀ partition.χ y *
        current_sectionNorm s.val y ^ 2) :=
      hEc.measurable.mul ((measurable_sectionNorm F ζ hζ U R P H s).pow_const 2)
    exact hm.aestronglyMeasurable

include μG hμG hR realization in

theorem ims_identity {T : ℝ} (partition : current_SquareEndPartition T)
    (A : current_Index → Q →L[ℂ] Q)
    (ht : ∀ i (f : current_S_U),
      A i (lift f) = lift (scalarMultiply (current_cutoff partition i) f))
    (v : Q) (s : BorelL2Sections F ζ hζ U R P H)
    (hs : KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ U R P H (jQ v) =
      mk F ζ hζ U R P H s) :
    ∑ i, qQ (A i v) = qQ v +
      ∫ x, current_collarError partition.χ₀ partition.χ x *
        current_sectionNorm s.val x ^ 2
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
  have hval : Continuous (fun w : Q => (jQ w).val) :=
    continuous_subtype_val.comp
      (current_j_U μG hμG hR realization).continuous
  have hEc : Continuous (current_collarError partition.χ₀ partition.χ) := by
    unfold collarError
    apply Continuous.add
    · exact continuous_differentialNormSquared F ζ hζ U R P H partition.χ₀
    · apply continuous_finset_sum
      intro c _
      exact continuous_differentialNormSquared F ζ hζ U R P H (partition.χ c)
  obtain ⟨C, hC, hb⟩ := partition.error_bounded
  have hGcont : Continuous (fun w : Q =>
      ∫ x, current_collarError partition.χ₀ partition.χ
          (current_q x) *
        ‖(jQ w).val x‖ ^ 2
        ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U) := by
    have hq : Continuous (current_q) :=
      KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U
    have hEmeas : AEStronglyMeasurable (fun x =>
        current_collarError partition.χ₀ partition.χ
          (current_q x))
        (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U) :=
      (hEc.comp hq).measurable.aestronglyMeasurable
    have hE0 : ∀ᵐ x ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U,
        0 ≤ current_collarError partition.χ₀ partition.χ
          (current_q x) :=
      Filter.Eventually.of_forall (fun x => partition.error_nonnegative _)
    have hEbd : ∀ᵐ x ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U,
        current_collarError partition.χ₀ partition.χ
          (current_q x) ≤ C :=
      Filter.Eventually.of_forall (fun x => hb _)
    exact (continuous_weighted_l2
      (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U)
      (fun x => current_collarError partition.χ₀ partition.χ
        (current_q x))
      hEmeas C hE0 hEbd).comp hval
  have hFn : Continuous (fun w : Q => ∑ i : current_Index, qQ (A i w)) := by
    apply continuous_finset_sum
    intro i _
    show Continuous (fun w : Q => ‖∇Q (A i w)‖ ^ 2)
    exact (((closedGradient F ζ hζ U R P H μG hμG hR realization).comp
      (A i)).continuous.norm.pow 2)
  have hGn : Continuous (fun w : Q => qQ w +
      ∫ x, current_collarError partition.χ₀ partition.χ
          (current_q x) *
        ‖(jQ w).val x‖ ^ 2
        ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U) := by
    refine ((closedGradient F ζ hζ U R P H μG hμG hR realization).continuous.norm.pow 2).add ?_
    exact hGcont
  have hpt : ∀ f : current_S_U,
      (∑ i : current_Index, qQ (A i (lift f))) = qQ (lift f) +
        ∫ x, current_collarError partition.χ₀ partition.χ
            (current_q x) *
          ‖(jQ (lift f)).val x‖ ^ 2
          ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U := by
    intro f
    let fB : BorelL2Scalars F ζ hζ U R :=
      ⟨scalarCovered f, (kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H
          realization).scalar_continuous f |>.measurable,
        KPContActualSectorTestEmbeddings.scalar_memLp f⟩
    have hiota := sectorLineIsometry_iota F ζ hζ U R P H μG hμG hR realization f
    rw [weighted_integral_eq F ζ hζ U R P H μG hμG hR realization partition
      (lift f) (borelS F ζ hζ U R P H fB) hiota]
    have hL : (∑ i : current_Index, qQ (A i (lift f))) =
        ∑ i : current_Index,
          ‖j (D_U (scalarMultiply (current_cutoff partition i) f))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      show ‖∇Q (A i (lift f))‖ ^ 2 =
        ‖j (D_U (scalarMultiply (current_cutoff partition i) f))‖ ^ 2
      rw [ht i f, coreLift_gradient F ζ hζ U R P H μG hμG hR realization _]
    have hQg : qQ (lift f) = ‖j (D_U f)‖ ^ 2 := by
      show ‖∇Q (lift f)‖ ^ 2 = ‖j (D_U f)‖ ^ 2
      rw [coreLift_gradient F ζ hζ U R P H μG hμG hR realization f]
    rw [hL, hQg]
    exact test_ims F ζ hζ U R P H μG hμG hR realization partition f
      (borelS F ζ hζ U R P H fB) hiota
  have heq := DenseRange.equalizer (coreLift_dense F ζ hζ U R P H μG hμG hR realization)
    hFn hGn (funext hpt)
  rw [congrFun heq v,
    weighted_integral_eq F ζ hζ U R P H μG hμG hR realization partition v s hs]

structure Properties {T : ℝ} (partition : current_SquareEndPartition T) where

  A : current_Index → Q →L[ℂ] Q

  intertwines : ∀ i, (jQ).comp (A i) =
    (current_sectorMultiplier partition i).op.comp jQ

  test_lift : ∀ i (f : current_S_U),
    A i (lift f) = lift (scalarMultiply (current_cutoff partition i) f)

  test_gradient : ∀ f : current_S_U, ∇Q (lift f) = j (D_U f)

  test_product_rule : ∀ i (f : current_S_U),
    ∇Q (A i (lift f)) =
      j (cotangentMultiply (current_cutoff partition i) (D_U f)) +
      j (cutoffGradientTimes (current_cutoff partition i) f)

  mass : ∀ v : Q, ∑ i, ‖jQ (A i v)‖ ^ 2 = ‖jQ v‖ ^ 2

  line_representative : ∀ v : Q, ∃ s : BorelL2Sections F ζ hζ U R P H,
    sectorLineIsometry F ζ hζ U R P H (jQ v) = mk F ζ hζ U R P H s

  ims : ∀ (v : Q) (s : BorelL2Sections F ζ hζ U R P H),
    sectorLineIsometry F ζ hζ U R P H (jQ v) = mk F ζ hζ U R P H s →
    Integrable (fun x => current_collarError partition.χ₀ partition.χ x *
      current_sectionNorm s.val x ^ 2)
      (KPContActualSectorCotangentL2.muU F ζ hζ U R P) ∧
    ∑ i, qQ (A i v) = qQ v + ∫ x,
      current_collarError partition.χ₀ partition.χ x *
        current_sectionNorm s.val x ^ 2
      ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P

end DedekindZetaZeroFree.KPContActualFormIMSIdentity

namespace DedekindZetaZeroFree

theorem kp_cont_actual_form_ims_identity
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (T : ℝ) (partition : KPContActualSquareEndPartition.SquareEndPartition F ζ hζ U R P H T) :
    Nonempty (KPContActualFormIMSIdentity.Properties F ζ hζ U R P H μG hμG hR realization partition) := by
  obtain ⟨A, hA, ht⟩ := KPContActualFormIMSIdentity.partition_lifts
    F ζ hζ U R P H μG hμG hR realization partition
  refine ⟨{
    A := A
    intertwines := hA
    test_lift := ht
    test_gradient := KPContActualFormIMSIdentity.coreLift_gradient
      F ζ hζ U R P H μG hμG hR realization
    test_product_rule := ?_
    mass := ?_
    line_representative := KPContActualFormIMSIdentity.core_line_representative
      F ζ hζ U R P H μG hμG hR realization
    ims := ?_ }⟩
  · intro i f
    rw [ht]
    exact KPContActualFormIMSIdentity.coreLift_product
      F ζ hζ U R P H μG hμG hR realization _ f
  · intro v
    have he (i) := congrArg (fun M => M v) (hA i)
    simp only [ContinuousLinearMap.comp_apply] at he
    simp_rw [he]
    exact
      KPContActualFormIMSIdentity.sector_mass F ζ hζ U R P H partition
        (KPContActualFormIMSIdentity.j_U F ζ hζ U R P H μG hμG hR realization v)
  · intro v s hs
    refine ⟨KPContActualFormIMSIdentity.collar_error_integrable F ζ hζ U R P H partition s, ?_⟩
    exact KPContActualFormIMSIdentity.ims_identity F ζ hζ U R P H μG hμG hR realization
      partition A ht v s hs

end DedekindZetaZeroFree

end
