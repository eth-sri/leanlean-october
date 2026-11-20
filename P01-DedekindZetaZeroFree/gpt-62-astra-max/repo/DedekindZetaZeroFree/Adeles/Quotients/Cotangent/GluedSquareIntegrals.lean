module
public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.HilbertPieceExtraction

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.EquivariantBorelGluing
public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.EquivariantHilbertSum

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal BigOperators
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentGluedPieceIntegral

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualCotangentCountableShrinking KPContActualCotangentBorelRefinement
open KPContActualCotangentExactMeasurableGluing
open KPContActualCotangentPieceHilbertSum
open KPContActualCotangentMeasurableFamilies
open KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

section

variable (cover : CountableCover F ζ hζ U R P H) (f : PieceSequence cover)

def pieceCoefficient (n : ℕ) (y : (cover.chart n).domain) : E F :=
  f.val n (coordinates (cover.chart n) y)

def pieceSquareIntegral (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ y in liftedPiece cover n, ENNReal.ofReal (‖pieceCoefficient cover f n y‖ ^ 2)
    ∂(cover.chart n).liftedMeasure

def RepresentsComponents (u : PieceHilbert cover) : Prop :=
  ∀ n : ℕ, pieceCoefficient cover f n =ᵐ[(cover.chart n).liftedMeasure]
    ((u n).val : (cover.chart n).domain → E F)

end

structure Properties (cover : CountableCover F ζ hζ U R P H) : Prop where
  gluing_squareFinite : ∀ (f : PieceSequence cover) (u : PieceHilbert cover),
    RepresentsComponents cover f u → squareFinite (G cover f)

private alias labeledA_labeledAInv_local := DedekindZetaZeroFree.KPContCotangentActualOverlap.OverlapMetricAndPhase.labeledA_labeledAInv

private alias toBase_eq_q := DedekindZetaZeroFree.KPContActualCotangentPieceExtraction.toBase_eq_q

private lemma lintegral_ofReal_norm_sq_eq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w : Lp (E F) 2 μ) :
    ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ∂μ = ENNReal.ofReal (‖w‖ ^ 2) := by
  have hpoint : ∀ x, ENNReal.ofReal (‖w x‖ ^ 2) = (‖w x‖₊ : ℝ≥0∞) ^ (2 : ℝ) := by
    intro x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
  have hfin : (∫⁻ x, (‖w x‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂μ) < ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
       (by norm_num) (by norm_num) (Lp.eLpNorm_lt_top w)
    rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num] at h
    simpa only [enorm_eq_nnnorm] using h
  have h1 : ‖w‖ ^ 2 = (∫⁻ x, (‖w x‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂μ).toReal := by
    have h0 : ‖w‖ ^ 2 = RCLike.re (inner ℂ w w) := norm_sq_eq_re_inner w
    rw [L2.inner_def, L2.integral_inner_eq_sq_eLpNorm, RCLike.ofReal_re] at h0
    exact h0
  calc _
      = ∫⁻ x, (‖w x‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂μ := lintegral_congr hpoint
    _ = ENNReal.ofReal (‖w‖ ^ 2) := by
        rw [h1, ENNReal.ofReal_toReal hfin.ne]

variable (cover : CountableCover F ζ hζ U R P H)
    (hb : KPContActualCotangentBorelRefinement.Properties cover)
    (hg : KPContActualCotangentExactMeasurableGluing.Properties cover) (f : PieceSequence cover)

include hb hg in
private lemma glued_integral_eq_tsum :
    (∫⁻ x, ENNReal.ofReal ((normSquare (G cover f) x : ℝ))
        ∂(baseMeasure (R := R) (P := P) (U := U))) =
      ∑' n, pieceSquareIntegral cover f n := by
  have hstep : ∀ n, (∫⁻ y in liftedPiece cover n,
      (normSquare (G cover f) ((cover.chart n).toBase y) : ℝ≥0∞)
        ∂(cover.chart n).liftedMeasure) = pieceSquareIntegral cover f n := by
    intro n
    rw [pieceSquareIntegral]
    refine setLIntegral_congr_fun (hb.lifted_measurable n) ?_
    intro y hy
    change (normSquare (G cover f) ((cover.chart n).toBase y) : ℝ≥0∞) =
      ENNReal.ofReal (‖pieceCoefficient cover f n y‖ ^ 2)
    rw [toBase_eq_q cover n y, ← ENNReal.ofReal_coe_nnreal, (hg.normSquare_on_piece f n (coordinates (cover.chart n) y) (by
      rw [← toBase_eq_q cover n y]; exact hy))]
    rfl
  calc ∫⁻ x, ENNReal.ofReal ((normSquare (G cover f) x : ℝ))
        ∂(baseMeasure)
      = ∫⁻ x, (normSquare (G cover f) x : ℝ≥0∞)
        ∂(baseMeasure) :=
        lintegral_congr fun x => ENNReal.ofReal_coe_nnreal
    _ = ∑' n, ∫⁻ y in liftedPiece cover n,
          (normSquare (G cover f) ((cover.chart n).toBase y) : ℝ≥0∞)
            ∂(cover.chart n).liftedMeasure := hb.lintegral_eq_tsum _ ((measurable_normSquare (G cover f)).coe_nnreal_ennreal)
    _ = ∑' n, pieceSquareIntegral cover f n := tsum_congr hstep

include hb hg in
private lemma glued_piece_eq (u : PieceHilbert cover)
    (hf : RepresentsComponents cover f u) (n : ℕ) :
    pieceSquareIntegral cover f n = ENNReal.ofReal (‖u n‖ ^ 2) := by
  have hA : pieceSquareIntegral cover f n
      = ∫⁻ y in liftedPiece cover n,
          ENNReal.ofReal (‖((u n).val : (cover.chart n).domain → E F) y‖ ^ 2)
            ∂(cover.chart n).liftedMeasure := by
    rw [pieceSquareIntegral]
    refine setLIntegral_congr_fun_ae (hb.lifted_measurable n) ?_
    filter_upwards [hf n] with y hy
    intro _
    rw [hy]
  have hsupp : ∀ᵐ y ∂(cover.chart n).liftedMeasure, y ∉ liftedPiece cover n →
      ((u n).val : (cover.chart n).domain → E F) y = 0 :=
    ((KPMeasurableLocalL2.mem_Q_iff (localData (cover.chart n)) (supportedPiece cover n)
      ((u n).val)).mp (u n).property).2
  have hB : (∫⁻ y in liftedPiece cover n,
        ENNReal.ofReal (‖((u n).val : (cover.chart n).domain → E F) y‖ ^ 2)
          ∂(cover.chart n).liftedMeasure)
      = ∫⁻ y, ENNReal.ofReal (‖((u n).val : (cover.chart n).domain → E F) y‖ ^ 2)
          ∂(cover.chart n).liftedMeasure := by
    rw [← lintegral_indicator (hb.lifted_measurable n)]
    refine lintegral_congr_ae ?_
    filter_upwards [hsupp] with y hy
    by_cases hyy : y ∈ liftedPiece cover n
    · rw [Set.indicator_of_mem hyy]
    · rw [Set.indicator_of_notMem hyy, hy hyy]; simp
  have hC : (∫⁻ y, ENNReal.ofReal (‖((u n).val : (cover.chart n).domain → E F) y‖ ^ 2)
          ∂(cover.chart n).liftedMeasure) = ENNReal.ofReal (‖u n‖ ^ 2) := by
    exact (lintegral_ofReal_norm_sq_eq ((cover.chart n).liftedMeasure) ((u n).val))
  exact hA.trans (hB.trans hC)

include hb hg in
private lemma glued_tsum_eq (u : PieceHilbert cover)
    (hf : RepresentsComponents cover f u) :
    (∑' n, pieceSquareIntegral cover f n) = ENNReal.ofReal (‖u‖ ^ 2) := by
  have hsumm : Summable (fun n => ‖u n‖ ^ 2) := by
    simpa using (memℓp_gen_iff (p := 2) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp
      (lp.memℓp u)
  rw [(tsum_congr fun n => glued_piece_eq cover hb hg f u hf n), ← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hsumm,
    ← norm_sq_eq_tsum cover u]

include hb hg in
private lemma glued_tsum_lt_top (u : PieceHilbert cover)
    (hf : RepresentsComponents cover f u) :
    (∑' n, pieceSquareIntegral cover f n) < ⊤ := by
  rw [glued_tsum_eq cover hb hg f u hf]
  exact ENNReal.ofReal_lt_top

end DedekindZetaZeroFree.KPContActualCotangentGluedPieceIntegral

namespace DedekindZetaZeroFree

theorem kp_cont_actual_cotangent_glued_piece_integral
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (cover : KPContActualCotangentCountableShrinking.CountableCover F ζ hζ U R P H) :
    KPContActualCotangentGluedPieceIntegral.Properties cover := by
  classical
  have hb := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover
  have hg := kp_cont_actual_cotangent_exact_measurable_gluing F ζ hζ μG hμG U R hR P H cover
  refine ⟨?_⟩
  · intro f u hf
    unfold KPContActualCotangentMeasurableFamilies.squareFinite
    rw [KPContActualCotangentGluedPieceIntegral.glued_integral_eq_tsum cover hb hg f]
    exact KPContActualCotangentGluedPieceIntegral.glued_tsum_lt_top cover hb hg f u hf

end DedekindZetaZeroFree

end
