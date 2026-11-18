module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryMeasure
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffJets
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierFinite
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometry
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryAffine
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import Mathlib.Algebra.Order.Archimedean.Basic
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackPositivityScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagation
import Mathlib.Algebra.BigOperators.Ring.Finset
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationPhysical
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AdmissibilityAffine
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PairGeometry

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Parabolic Scaling MeasureTheory Set
open scoped ENNReal


/-- The velocity slice of the unit product cutoff. -/
def unitCutoffVelocitySlice {d : ℕ}
    (f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ) (Q : KineticPoint d) : PDE.Vec d → ℝ :=
  fun w => f (Q.time, (Q.position, w))

/-- A source-smooth product cutoff has smooth velocity slices. -/
theorem contDiff_unitCutoffVelocitySlice {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (Q : KineticPoint d) :
    ContDiff ℝ (⊤ : ℕ∞) (unitCutoffVelocitySlice f Q) :=
  hf.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))


/-- The physical backward operator is the exact inverse-square unit jet expression. -/
theorem scaledUnitCutoff_backwardOperator {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (A : FullKineticCoefficient d)
    (P₀ P : KineticPoint d) (R ell : ℝ) :
    backwardOperator A (scaledUnitCutoff f P₀ R ell) P =
      ell * (R ^ 2)⁻¹ *
        (fderiv ℝ f (KineticPoint.equivProd d (kineticAffineInverse P₀ R P))
          (1, ((kineticAffineInverse P₀ R P).velocity, 0)) -
          matrixContraction (fullKineticCoefficientAt A P)
            (sliceHessian (unitCutoffVelocitySlice f (kineticAffineInverse P₀ R P))
              (kineticAffineInverse P₀ R P).velocity))  := by
  have scaledUnitCutoff_velocityHessian (P₀ P : KineticPoint d) (R : ℝ) (ell : ℝ) :
      kineticVelocityHessian (scaledUnitCutoff f P₀ R ell) P =
      (ell * (R ^ 2)⁻¹) • sliceHessian
        (unitCutoffVelocitySlice f (kineticAffineInverse P₀ R P))
        (kineticAffineInverse P₀ R P).velocity := by
    let Q := kineticAffineInverse P₀ R P
    let g := unitCutoffVelocitySlice f Q
    let w₀ := -(R⁻¹ • P₀.velocity)
    have hg : ContDiff ℝ 2 g :=
      (contDiff_unitCutoffVelocitySlice hf Q).of_le (by simp)
    have hmap : ContDiff ℝ 2 (fun w : PDE.Vec d => w₀ + R⁻¹ • w) := by fun_prop
    have heq : (fun w : PDE.Vec d => scaledUnitCutoff f P₀ R ell
        ⟨P.time, P.position, w⟩) = fun w => ell * g (w₀ + R⁻¹ • w) := by
      funext w
      change ell * f ((P.time - P₀.time) / R ^ 2,
        ((R ^ 3)⁻¹ • relativePosition P₀ P, R⁻¹ • (w - P₀.velocity))) =
          ell * f ((P.time - P₀.time) / R ^ 2,
            ((R ^ 3)⁻¹ • relativePosition P₀ P, w₀ + R⁻¹ • w))
      have hv : R⁻¹ • (w - P₀.velocity) = w₀ + R⁻¹ • w := by
        ext i
        simp [w₀]
        ring
      rw [hv]
    have hbase : w₀ + R⁻¹ • P.velocity = Q.velocity := by
      ext i
      simp [w₀, Q, kineticAffineInverse, relativeVelocity]
      ring
    have hgmap : ContDiff ℝ 2 (fun w => g (w₀ + R⁻¹ • w)) := by
      simpa only [Function.comp_def] using hg.comp hmap
    rw [kineticVelocityHessian_eq_sliceHessian, heq,
      sliceHessian_const_mul ell hgmap.contDiffAt,
      sliceHessian_affine (g := g) (y₀ := w₀) (c := R⁻¹) hg.contDiffAt, hbase]
    simp only [smul_smul, inv_pow]
    rfl
  rw [backwardOperator_apply, scaledUnitCutoff_transport hf,
    scaledUnitCutoff_velocityHessian, matrixContraction_smul_right]
  ring



/-- An affine slice Hessian is the restriction of the ambient second derivative. -/
theorem sliceHessian_comp_affine_embedding {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {ι : PDE.Vec d → E} (hιc : ContDiff ℝ 2 ι)
    {J : PDE.Vec d →L[ℝ] E} (hι : ∀ x, HasFDerivAt ι J x)
    (x : PDE.Vec d) (i j : Fin d) :
    sliceHessian (fun w => f (ι w)) x i j =
      fderiv ℝ (fderiv ℝ f) (ι x) (J (PDE.basisVec i)) (J (PDE.basisVec j)) := by
  have hg : ContDiffAt ℝ 2 (fun w => f (ι w)) x := (hf.comp hιc).contDiffAt
  rw [sliceHessian_apply_eq_sndFDeriv hg]
  have hd : ∀ w, DifferentiableAt ℝ f w := hf.differentiable (by norm_num)
  have hfd : ∀ w, fderiv ℝ (fun z => f (ι z)) w = (fderiv ℝ f (ι w)).comp J :=
    fun w => ((hd (ι w)).hasFDerivAt.comp w (hι w)).fderiv
  have hgd := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [← fderiv_clm_apply_const_eval hgd (PDE.basisVec j) (PDE.basisVec i)]
  have hfun : (fun w => fderiv ℝ (fun z => f (ι z)) w (PDE.basisVec j)) =
      fun w => fderiv ℝ f (ι w) (J (PDE.basisVec j)) := by
    funext w
    rw [hfd w]
    rfl
  rw [hfun]
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) (ι x)
  have hh := (hdf.clm_apply (differentiableAt_const (J (PDE.basisVec j)))).hasFDerivAt
  have hc := hh.comp x (hι x)
  rw [show (fun w => fderiv ℝ f (ι w) (J (PDE.basisVec j))) =
    (fun z => fderiv ℝ f z (J (PDE.basisVec j))) ∘ ι from rfl, hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_clm_apply_const_eval hdf]

/-- Unit velocity-Hessian entries are the corresponding ambient coordinate derivatives. -/
theorem unitCutoffVelocitySlice_hessian {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (Q : KineticPoint d) (i j : Fin d) :
    sliceHessian (unitCutoffVelocitySlice f Q) Q.velocity i j =
      fderiv ℝ (fderiv ℝ f) (KineticPoint.equivProd d Q)
        (0, (0, PDE.basisVec i)) (0, (0, PDE.basisVec j)) := by
  let J : PDE.Vec d →L[ℝ] ℝ × (PDE.Vec d × PDE.Vec d) :=
    (0 : PDE.Vec d →L[ℝ] ℝ).prod
      ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ (PDE.Vec d)))
  have hι : ∀ w, HasFDerivAt (fun z : PDE.Vec d => (Q.time, (Q.position, z))) J w :=
    fun w => (hasFDerivAt_const Q.time w).prodMk
      ((hasFDerivAt_const Q.position w).prodMk (hasFDerivAt_id w))
  have h := sliceHessian_comp_affine_embedding (hf.of_le (by simp))
    (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)) hι Q.velocity i j
  change sliceHessian (fun w => f (Q.time, (Q.position, w))) Q.velocity i j =
    fderiv ℝ (fderiv ℝ f) (Q.time, (Q.position, Q.velocity))
      (0, (0, PDE.basisVec i)) (0, (0, PDE.basisVec j))
  simpa only [J, ContinuousLinearMap.prod_apply, zero_apply, ContinuousLinearMap.id_apply,
    id_eq]
    using h

/-- The unit velocity Hessian depends continuously on the physical point. -/
theorem continuous_unitCutoffVelocityHessian {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun Q : KineticPoint d =>
      sliceHessian (unitCutoffVelocitySlice f Q) Q.velocity) := by
  have hc : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (((hf.of_le (show (3 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).continuous
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have h0 := (hc.comp (KineticPoint.homeomorphProd d).continuous).clm_apply
    (continuous_const (y := ((0, (0, PDE.basisVec i)) : ℝ × (PDE.Vec d × PDE.Vec d))))
  have h1 := h0.clm_apply (continuous_const
    (y := ((0, (0, PDE.basisVec j)) : ℝ × (PDE.Vec d × PDE.Vec d))))
  exact h1.congr (fun Q => (unitCutoffVelocitySlice_hessian hf Q i j).symm)

/-- The unit transport derivative depends continuously on the physical point. -/
theorem continuous_unitCutoffTransport {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun Q : KineticPoint d =>
      fderiv ℝ f (KineticPoint.equivProd d Q) (1, (Q.velocity, 0))) := by
  have h0 := ((hf.of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).fderiv_right
    (m := 1) (by norm_num)).continuous.comp (KineticPoint.homeomorphProd d).continuous
  exact h0.clm_apply
    (continuous_const.prodMk (continuous_velocity.prodMk continuous_const))







/-- A bounded localized positive source is controlled by the strict-sublevel volume. -/
theorem localizedSource_norm_le_sublevel_volume {d : ℕ} (A : FullKineticCoefficient d)
    {psi u : KineticPoint d → ℝ} {Q : Set (KineticPoint d)} (hQ : IsOpen Q)
    (hQfinite : volume Q ≠ ⊤) (hpsi : ContinuousOn psi Q) (hu : ContinuousOn u Q)
    (hopm : Measurable (backwardOperator A psi)) (ell B p : ℝ)
    (hB : 0 ≤ B) (hp : 1 ≤ p) (hlevel : ∀ P ∈ Q, psi P ≤ ell)
    (hop : ∀ᵐ P ∂(volume.restrict Q), |backwardOperator A psi P| ≤ B) :
    (eLpNorm (localizedSource A psi u) (ENNReal.ofReal p) (volume.restrict Q)).toReal ≤
      B * (volume ({P | u P < ell} ∩ Q)).toReal ^ (1 / p)  := by
  have localizedSource_aestronglyMeasurable :
      AEStronglyMeasurable (localizedSource A psi u) (volume.restrict Q) := by
    have hE : MeasurableSet (Q ∩ {P | u P < psi P}) := by
      simpa only [Set.preimage, mem_Ioi, Pi.sub_apply, sub_pos] using
        ((hpsi.sub hu).isOpen_inter_preimage hQ (isOpen_Ioi (a := 0))).measurableSet
    have hm : AEStronglyMeasurable
        ((Q ∩ {P | u P < psi P}).indicator
          (fun P => max (backwardOperator A psi P) 0)) volume :=
      ((hopm.max measurable_const).aestronglyMeasurable).indicator hE
    apply hm.restrict.congr
    filter_upwards [ae_restrict_mem hQ.measurableSet] with P hP
    simp only [localizedSource, indicator, mem_inter_iff, mem_ofPred_eq, hP, true_and]
  let E := {P | u P < ell} ∩ Q
  have hE : MeasurableSet E := by
    simpa only [E, Set.preimage, mem_Iio, inter_comm] using
      (hu.isOpen_inter_preimage hQ (isOpen_Iio (a := ell))).measurableSet
  have hm := localizedSource_aestronglyMeasurable
  have hbound : ∀ᵐ P ∂(volume.restrict Q),
      ‖localizedSource A psi u P‖ ≤ ‖E.indicator (fun _ => B) P‖ := by
    filter_upwards [ae_restrict_mem hQ.measurableSet, hop] with P hP hb
    by_cases hs : u P < psi P
    · have hPE : P ∈ E := ⟨hs.trans_le (hlevel P hP), hP⟩
      rw [indicator_of_mem hPE]
      simp only [localizedSource, indicator, mem_ofPred_eq, hs, ite_true, Real.norm_eq_abs,
        abs_of_nonneg hB, abs_of_nonneg (le_max_right (backwardOperator A psi P) 0)]
      exact max_le ((le_abs_self _).trans hb) hB
    · simp only [localizedSource, indicator, mem_ofPred_eq, hs, ite_false, norm_zero]
      exact norm_nonneg _
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hnorm := eLpNorm_mono_ae (p := ENNReal.ofReal p) hm hbound
  rw [eLpNorm_indicator_const hE.nullMeasurableSet
    (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top] at hnorm
  have hmeasure : (volume.restrict Q) E = volume E := by
    rw [Measure.restrict_apply hE, inter_eq_left.mpr inter_subset_right]
  rw [hmeasure, ENNReal.toReal_ofReal hp0.le] at hnorm
  have hEfinite : volume E ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right hQfinite
  have hright : ‖B‖ₑ * volume E ^ (1 / p) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg
      (one_div_nonneg.mpr hp0.le) hEfinite)
  have hreal := ENNReal.toReal_mono hright hnorm
  simpa only [ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hB,
    ENNReal.toReal_ofReal hB, ← ENNReal.toReal_rpow] using hreal




end HypoellipticAleksandrov.KineticAleksandrov.Holder

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
open Set MeasureTheory Covering
open scoped BigOperators


/-- Relative superlevels are measurable without assuming global measurability of u. -/
theorem measurableSet_superlevel_inter {d : ℕ} {O E : Set (KineticPoint d)}
    (hO : IsOpen O) (hE : MeasurableSet E) (hEO : E ⊆ O)
    {u : KineticPoint d → ℝ} (hu : ContinuousOn u O) (ell : ℝ) :
    MeasurableSet ({P | ell ≤ u P} ∩ E) := by
  classical
  let f := O.piecewise u (fun _ => 0)
  have hf : Measurable f := hu.measurable_piecewise continuous_const.continuousOn
    hO.measurableSet
  have heq : {P | ell ≤ u P} ∩ E = {P | ell ≤ f P} ∩ E := by
    ext P
    by_cases hp : P ∈ E
    · have hpo := hEO hp
      simp only [mem_inter_iff, mem_ofPred_eq, hp, and_true, f,
        piecewise_eq_of_mem O u (fun _ => 0) hpo]
    · simp only [mem_inter_iff, hp, and_false]
  rw [heq]
  exact (measurableSet_le measurable_const hf).inter hE

/-- All source level intersections are bounded by their comparison region. -/
theorem superlevel_inter_isBounded {d : ℕ} {E : Set (KineticPoint d)}
    (hE : Bornology.IsBounded E) (u : KineticPoint d → ℝ) (ell : ℝ) :
    Bornology.IsBounded ({P | ell ≤ u P} ∩ E) :=
  hE.subset inter_subset_right

/-- Exact source volume scaling also holds after conversion to real volume. -/
theorem volume_affine_image_toReal {d : ℕ} (P0 : KineticPoint d) {R : ℝ}
    (hR : 0 < R) (E : Set (KineticPoint d)) :
    (volume (kineticAffine P0 R '' E)).toReal = R ^ (4 * d + 2) * (volume E).toReal := by
  rw [volume_kineticAffine_image P0 hR, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_pos hR _).le]



/-- Every bounded kinetic set has a compact coordinate envelope. -/
theorem bounded_kinetic_compact_envelope {d : ℕ} {E : Set (KineticPoint d)}
    (hE : Bornology.IsBounded E) : ∃ K : Set (KineticPoint d), IsCompact K ∧ E ⊆ K := by
  let e := KineticPoint.isometryEquivProd d
  have hb := e.isometry.lipschitzWith.isBounded_image hE
  refine ⟨(KineticPoint.homeomorphProd d).symm '' closure (e '' E),
    hb.isCompact_closure.image (KineticPoint.homeomorphProd d).symm.continuous, ?_⟩
  intro P hP
  exact ⟨e P, subset_closure ⟨P, hP, rfl⟩, e.symm_apply_apply P⟩

/-- A nonzero affine preimage of a bounded kinetic set remains bounded. -/
theorem isBounded_kineticAffine_preimage {d : ℕ} (P0 : KineticPoint d) {R : ℝ}
    (hR : R ≠ 0) {E : Set (KineticPoint d)} (hE : Bornology.IsBounded E) :
    Bornology.IsBounded (kineticAffine P0 R ⁻¹' E) := by
  obtain ⟨K, hK, hEK⟩ := bounded_kinetic_compact_envelope hE
  exact ((kineticAffineHomeomorph P0 R hR).isCompact_preimage.mpr hK).isBounded.subset
    (preimage_mono hEK)

/-- Affine images of bounded kinetic sets have compact coordinate envelopes. -/
theorem isBounded_kineticAffine_image {d : ℕ} (P0 : KineticPoint d) (R : ℝ)
    {E : Set (KineticPoint d)} (hE : Bornology.IsBounded E) :
    Bornology.IsBounded (kineticAffine P0 R '' E) := by
  obtain ⟨K, hK, hEK⟩ := bounded_kinetic_compact_envelope hE
  exact (hK.image (continuous_kineticAffine P0 R)).isBounded.subset (image_mono hEK)

/-- Affine pullbacks of measurable levels are measurable in the same Lebesgue space. -/
theorem measurableSet_kineticAffine_preimage {d : ℕ} (P0 : KineticPoint d) (R : ℝ)
    {E : Set (KineticPoint d)} (hE : MeasurableSet E) :
    MeasurableSet (kineticAffine P0 R ⁻¹' E) :=
  hE.preimage (continuous_kineticAffine P0 R).measurable






/-- The power sum has the shifted recurrence used in the density ladder. -/
theorem ladder_power_sum_succ (q : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), q ^ k) =
      q * (∑ k ∈ Finset.range n, q ^ k) + 1 := by
  rw [Finset.sum_range_succ']
  simp only [pow_succ, pow_zero]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The exact source ladder gives its terminal-level lower bound by numeric induction. -/
theorem density_ladder_numeric {a beta L0 : ℝ} (ha : 0 < a) (e : ℕ → ℝ) (N : ℕ)
    (hzero : beta ≤ e 0) (hstep : ∀ j < N, e j ≤ a * (e (j + 1) + L0)) :
    a⁻¹ ^ N * beta - L0 * (∑ k ∈ Finset.range N, a⁻¹ ^ k) ≤ e N := by
  have hrec : ∀ j < N, a⁻¹ * e j - L0 ≤ e (j + 1) := by
    intro j hj
    have he := mul_le_mul_of_nonneg_left (hstep j hj) (inv_nonneg.mpr ha.le)
    rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] at he
    linarith only [he]
  have hbound : ∀ n, n ≤ N →
      a⁻¹ ^ n * beta - L0 * (∑ k ∈ Finset.range n, a⁻¹ ^ k) ≤ e n := by
    intro n
    induction n with
    | zero => intro _; simpa only [pow_zero, one_mul, Finset.range_zero,
        Finset.sum_empty, mul_zero, sub_zero] using hzero
    | succ n ih =>
      intro hn
      have he := mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hn))
        (inv_nonneg.mpr ha.le)
      have hr := hrec n (Nat.lt_of_succ_le hn)
      rw [ladder_power_sum_succ, pow_succ]
      nlinarith only [he, hr]
  exact hbound N le_rfl

/-- Fixing N first allows the source leakage radius to be chosen strictly positive and small. -/
theorem exists_density_leakage_choice {a eta beta C V : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (_heta1 : eta < 1) (hbeta : 0 < beta) (hC : 0 < C) (hV : 0 < V)
    (m : ℕ) (hm : 0 < m) :
    ∃ N : ℕ, 1 ≤ N ∧ a⁻¹ ^ N * beta > 1 - eta ∧
      ∃ r0 : ℝ, 0 < r0 ∧ r0 < 1 ∧
        (C * (m : ℝ) * r0 ^ 2 / V) * (∑ k ∈ Finset.range N, a⁻¹ ^ k) <
          a⁻¹ ^ N * beta - (1 - eta) := by
  have hq : 1 < a⁻¹ := (one_lt_inv₀ ha).mpr ha1
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((1 - eta) / beta) hq
  let N := n + 1
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hn' : a⁻¹ ^ n ≤ a⁻¹ ^ N := pow_le_pow_right₀ hq.le (Nat.le_succ n)
  have hbig : 1 - eta < a⁻¹ ^ N * beta := by
    exact (div_lt_iff₀ hbeta).mp (hn.trans_le hn')
  let S := ∑ k ∈ Finset.range N, a⁻¹ ^ k
  have hS : 0 < S := Finset.sum_pos (fun k _ => pow_pos (inv_pos.mpr ha) k)
    (Finset.nonempty_range_iff.mpr (by omega))
  let D := (C * (m : ℝ) / V) * S
  have hD : 0 < D := mul_pos (div_pos (mul_pos hC (Nat.cast_pos.mpr hm)) hV) hS
  let gap := a⁻¹ ^ N * beta - (1 - eta)
  have hgap : 0 < gap := sub_pos.mpr hbig
  let r0 := min (1 / 2 : ℝ) (Real.sqrt (gap / (2 * D)))
  have hr0 : 0 < r0 := lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  have hr01 : r0 < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hrsq : r0 ^ 2 ≤ gap / (2 * D) := by
    have he := (sq_le_sq₀ hr0.le (Real.sqrt_nonneg _)).mpr (min_le_right _ _)
    rwa [Real.sq_sqrt (by positivity : 0 ≤ gap / (2 * D))] at he
  have hhalf : D * r0 ^ 2 ≤ gap / 2 := by
    have he := mul_le_mul_of_nonneg_left hrsq hD.le
    apply he.trans_eq
    field_simp
  refine ⟨N, hN, hbig, r0, hr0, hr01, ?_⟩
  have heq : (C * (m : ℝ) * r0 ^ 2 / V) * S = D * r0 ^ 2 := by
    dsimp only [D]
    ring
  rw [heq]
  exact hhalf.trans_lt (by dsimp only [gap] at hgap ⊢; linarith only [hgap])




end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

section



namespace HypoellipticAleksandrov.KineticAleksandrov

open Set MeasureTheory Holder Holder.Growth
open scoped ENNReal MatrixOrder


end HypoellipticAleksandrov.KineticAleksandrov

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

/-- The literal source exponent is positive, at most one, and absorbs the contraction. -/
theorem source_holder_exponent {theta q : ℝ} (ht : 0 < theta) (ht1 : theta < 1)
    (hq : 0 < q) (hq1 : q < 1) :
    let alpha := min 1 (Real.log (1 / q) / Real.log (1 / theta))
    0 < alpha ∧ alpha ≤ 1 ∧ q ≤ theta ^ alpha := by
  have hlt : Real.log theta < 0 := Real.log_neg ht ht1
  have hlq : Real.log q < 0 := Real.log_neg hq hq1
  have hratio : Real.log (1 / q) / Real.log (1 / theta) =
      Real.log q / Real.log theta := by rw [one_div, one_div, Real.log_inv, Real.log_inv]; ring
  dsimp only
  rw [hratio]
  refine ⟨lt_min zero_lt_one (div_pos_of_neg_of_neg hlq hlt), min_le_left _ _, ?_⟩
  apply (Real.le_rpow_iff_log_le hq ht).mpr
  have he := mul_le_mul_of_nonpos_right (min_le_right (1 : ℝ)
    (Real.log q / Real.log theta)) hlt.le
  rw [div_mul_cancel₀ _ hlt.ne] at he
  exact he

/-- A geometric shell bounds the corresponding contraction by the source power multiplier. -/
theorem contraction_power_le_scale_power {theta q alpha x : ℝ}
    (ht : 0 < theta) (hq : 0 ≤ q) (ha : 0 < alpha) (hqa : q ≤ theta ^ alpha)
    (n : ℕ) (hn : theta ^ (n + 1) < x) :
    q ^ n ≤ theta ^ (-alpha) * x ^ alpha := by
  have hs : theta ^ n < x / theta := by
    rw [pow_succ] at hn
    exact (lt_div_iff₀ ht).mpr hn
  calc
    q ^ n ≤ (theta ^ alpha) ^ n := pow_le_pow_left₀ hq hqa n
    _ = (theta ^ n) ^ alpha := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le,
        ← Real.rpow_natCast, ← Real.rpow_mul ht.le, mul_comm alpha (n : ℝ)]
    _ ≤ (x / theta) ^ alpha := Real.rpow_le_rpow (pow_nonneg ht.le n) hs.le ha.le
    _ = theta ^ (-alpha) * x ^ alpha := by
      rw [Real.div_rpow (by linarith only [hn, pow_pos ht (n + 1)]) ht.le,
        Real.rpow_neg ht.le, div_eq_mul_inv, mul_comm]


open Set


end HypoellipticAleksandrov.KineticAleksandrov.Holder

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set MeasureTheory Holder
open scoped ENNReal MatrixOrder

/-- The kinetic Holder theorem, conditional only on its admissibility predicate. -/
theorem kinetic_holder_of_aleksandrov_aux
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p C_A : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 1 ≤ p) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : FullKineticCoefficient d,
        Measurable (fullKineticCoefficientAt A) →
        (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) →
      ∀ (Omega : Set (KineticPoint d)), IsOpen Omega →
      ∀ (u : KineticPoint d → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        IsAdmissibleSolution A Omega p C_A u →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha    := by
  have kinetic_growth_lemma_aux :
      ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧
      ∃ (P_Sigma : KineticPoint d) (r_Sigma : ℝ), 0 < r_Sigma ∧
        closure (backwardCylinder P_Sigma r_Sigma) ⊆
          backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
        ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
          ∃ kappa_beta : ℝ, 0 < kappa_beta ∧
            ∀ A : FullKineticCoefficient d,
              Measurable (fullKineticCoefficientAt A) →
              (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
              (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
                lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P) →
              (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
                fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) →
              ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
              ∀ O : Set (KineticPoint d), IsOpen O →
                closure (backwardCylinder P₀ R) ⊆ O →
              ∀ u : KineticPoint d → ℝ,
                (∀ P ∈ O, 0 ≤ u P) → IsAdmissibleSupersolution A O p C_A u →
                beta * (volume (kineticAffine P₀ R ''
                  backwardCylinder P_Sigma r_Sigma)).toReal ≤
                    (volume ({P | 1 ≤ u P} ∩ (kineticAffine P₀ R ''
                      backwardCylinder P_Sigma r_Sigma))).toReal →
                ∀ P ∈ backwardCylinder P₀ (theta * R), kappa_beta ≤ u P := open Holder.Growth in by
    have exists_growth_parameters :
        ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧
        ∃ (Psigma : KineticPoint d) (rsigma : ℝ), 0 < rsigma ∧
          closure (backwardCylinder Psigma rsigma) ⊆
            backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
          ∀ beta : ℝ, 0 < beta → beta ≤ 1 → ∃ kappa : ℝ, 0 < kappa ∧
            ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
            ∀ (P0 : KineticPoint d) (R : ℝ), 0 < R →
            ∀ O : Set (KineticPoint d), IsOpen O → closure (backwardCylinder P0 R) ⊆ O →
            ∀ u : KineticPoint d → ℝ, (∀ P ∈ O, 0 ≤ u P) →
              IsAdmissibleSupersolution A O p C_A u →
              beta * (volume (kineticAffine P0 R '' backwardCylinder Psigma rsigma)).toReal ≤
                (volume ({P | 1 ≤ u P} ∩
                  kineticAffine P0 R '' backwardCylinder Psigma rsigma)).toReal →
              ∀ P ∈ backwardCylinder P0 (theta * R), kappa ≤ u P := open Covering in by
      have near_full_threshold :
          ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
          ∀ lam : ℝ, 0 < lam → lam ≤ Lam →
          ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
          ∀ (P₀ : KineticPoint d) (R ell : ℝ), 0 < R → 0 ≤ ell →
          ∀ O : Set (KineticPoint d), IsOpen O → closure (backwardCylinder P₀ R) ⊆ O →
          ∀ u : KineticPoint d → ℝ, (∀ P ∈ O, 0 ≤ u P) →
            IsAdmissibleSupersolution A O p C_A u →
            (1 - eta) * (volume (backwardCylinder P₀ R)).toReal ≤
              (volume ({P | ell ≤ u P} ∩ backwardCylinder P₀ R)).toReal →
          ∀ P ∈ kineticAffine P₀ R '' cap d, (3 / 4 : ℝ) * ell ≤ u P := by
        have near_full :
            ∃ C₁ : ℝ, ∀ lam : ℝ, 0 < lam → lam ≤ Lam →
            ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
            ∀ (P₀ : KineticPoint d) (R ell eta : ℝ),
              0 < R → 0 ≤ ell → 0 < eta → eta < 1 →
            ∀ O : Set (KineticPoint d), IsOpen O → closure (backwardCylinder P₀ R) ⊆ O →
            ∀ u : KineticPoint d → ℝ, (∀ P ∈ O, 0 ≤ u P) →
              IsAdmissibleSupersolution A O p C_A u →
              (1 - eta) * (volume (backwardCylinder P₀ R)).toReal ≤
                (volume ({P | ell ≤ u P} ∩ backwardCylinder P₀ R)).toReal →
            ∀ P ∈ kineticAffine P₀ R '' cap d, (1 - C₁ * eta ^ (1 / p)) * ell ≤ u P := by
          have near_full_with_nonneg_constant (d : ℕ) :
              ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ lam : ℝ, 0 < lam → lam ≤ Lam →
              ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
              ∀ (P₀ : KineticPoint d) (R ell eta : ℝ),
                0 < R → 0 ≤ ell → 0 < eta → eta < 1 →
              ∀ O : Set (KineticPoint d), IsOpen O → closure (backwardCylinder P₀ R) ⊆ O →
              ∀ u : KineticPoint d → ℝ, (∀ P ∈ O, 0 ≤ u P) →
                IsAdmissibleSupersolution A O p C_A u →
                (1 - eta) * (volume (backwardCylinder P₀ R)).toReal ≤
                  (volume ({P | ell ≤ u P} ∩ backwardCylinder P₀ R)).toReal →
              ∀ P ∈ kineticAffine P₀ R '' cap d, (1 - C₁ * eta ^ (1 / p)) * ell ≤ u P := by
            have measurable_scaledUnitCutoff_backwardOperator {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {A : FullKineticCoefficient d} (hA : Measurable (fullKineticCoefficientAt A)) (P₀ : KineticPoint d) (R : ℝ) (ell : ℝ) :
                Measurable (backwardOperator A (scaledUnitCutoff f P₀ R ell)) := by
              have hT := ((continuous_unitCutoffTransport hf).comp
                (continuous_kineticAffineInverse P₀ R)).measurable
              have hH := ((continuous_unitCutoffVelocityHessian hf).comp
                (continuous_kineticAffineInverse P₀ R)).measurable
              have hC : Measurable (fun P => matrixContraction (fullKineticCoefficientAt A P)
                  (sliceHessian (unitCutoffVelocitySlice f (kineticAffineInverse P₀ R P))
                    (kineticAffineInverse P₀ R P).velocity)) := by
                unfold matrixContraction
                apply Finset.measurable_sum
                intro i _
                apply Finset.measurable_sum
                intro j _
                exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)).mul
                  ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hH))
              have h := (measurable_const (a := ell * (R ^ 2)⁻¹)).mul (hT.sub hC)
              convert h using 1
              funext P
              exact scaledUnitCutoff_backwardOperator hf A P₀ P R ell
            have exists_scaledUnitCutoff_operator_bound {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
                ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ lam : ℝ, 0 < lam →
                ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
                ∀ (P₀ : KineticPoint d) (R ell : ℝ), 0 < R → 0 ≤ ell →
                ∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
                  |backwardOperator A (scaledUnitCutoff f P₀ R ell) P| ≤ C₀ * ell * (R ^ 2)⁻¹ := by
              have exists_unitCutoffJet_bound :
                  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ Q ∈ closure
                  (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1),
                  ∀ B : PDE.Mat d, (∀ i j, |B i j| ≤ |Lam|) →
                    |fderiv ℝ f (KineticPoint.equivProd d Q) (1, (Q.velocity, 0)) -
                      matrixContraction B (sliceHessian (unitCutoffVelocitySlice f Q) Q.velocity)| ≤ C₀ := by
                have continuous_unitCutoffJet :
                    Continuous (fun z : KineticPoint d × PDE.Mat d =>
                    fderiv ℝ f (KineticPoint.equivProd d z.1) (1, (z.1.velocity, 0)) -
                      matrixContraction z.2 (sliceHessian (unitCutoffVelocitySlice f z.1) z.1.velocity)) := by
                  have hD : Continuous (fun z : KineticPoint d × PDE.Mat d =>
                      fderiv ℝ f (KineticPoint.equivProd d z.1) (1, (z.1.velocity, 0))) :=
                    (continuous_unitCutoffTransport hf).comp continuous_fst
                  apply hD.sub
                  have hH : Continuous (fun z : KineticPoint d × PDE.Mat d =>
                      sliceHessian (unitCutoffVelocitySlice f z.1) z.1.velocity) :=
                    (continuous_unitCutoffVelocityHessian hf).comp continuous_fst
                  unfold matrixContraction
                  apply continuous_finsetSum
                  intro i _
                  apply continuous_finsetSum
                  intro j _
                  exact ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd)).mul
                    ((continuous_apply j).comp ((continuous_apply i).comp hH))
                let K := closure (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)
                let S : Set (PDE.Mat d) := {B | ∀ i j, B i j ∈ Icc (-|Lam|) |Lam|}
                have hK : IsCompact K := isCompact_closure_backwardCylinder _ 1 (by norm_num)
                have hS : IsCompact S :=
                  isCompact_pi_infinite (fun _ => isCompact_pi_infinite (fun _ => isCompact_Icc))
                obtain ⟨M, hM⟩ := (hK.prod hS).exists_bound_of_continuousOn
                  (continuous_unitCutoffJet).continuousOn
                refine ⟨max M 0, le_max_right _ _, fun Q hQ B hB => ?_⟩
                have hBS : B ∈ S := fun i j => abs_le.mp (hB i j)
                exact (show |fderiv ℝ f (KineticPoint.equivProd d Q) (1, (Q.velocity, 0)) -
                  matrixContraction B (sliceHessian (unitCutoffVelocitySlice f Q) Q.velocity)| ≤ M by
                    simpa only [Real.norm_eq_abs] using hM (Q, B) ⟨hQ, hBS⟩).trans (le_max_left _ _)
              obtain ⟨C₀, hC₀, hbound⟩ := exists_unitCutoffJet_bound
              refine ⟨C₀, hC₀, fun lam hlam A hA P₀ R ell hR hell => ?_⟩
              have hQ := isOpen_backwardCylinder P₀ R hR
              filter_upwards [ae_restrict_mem hQ.measurableSet,
                ae_restrict_of_ae hA.2.2.1, ae_restrict_of_ae hA.2.2.2] with P hP hl hu
              have hunit : kineticAffineInverse P₀ R P ∈
                  backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
                apply (kineticAffine_mem_cylinder P₀ _ hR).mp
                simpa only [kineticAffine_apply_inverse P₀ hR.ne' P] using hP
              have hB : ∀ i j, |fullKineticCoefficientAt A P i j| ≤ |Lam| :=
                fun i j =>
                  (HypoellipticAleksandrov.abs_apply_le_of_loewner hlam hl hu i j).trans (le_abs_self Lam)
              have hb := hbound _ (subset_closure hunit) _ hB
              rw [scaledUnitCutoff_backwardOperator hf, abs_mul,
                abs_of_nonneg (mul_nonneg hell (inv_nonneg.mpr (sq_nonneg R)))]
              calc
                _ ≤ ell * (R ^ 2)⁻¹ * C₀ :=
                  mul_le_mul_of_nonneg_left hb (mul_nonneg hell (inv_nonneg.mpr (sq_nonneg R)))
                _ = C₀ * ell * (R ^ 2)⁻¹ := by ring
            have near_full_radius_cancellation {R : ℝ} (hR : 0 < R) :
                R ^ (2 - (4 * (d : ℝ) + 2) / p) * (R ^ 2)⁻¹ *
                (R ^ (4 * d + 2)) ^ (1 / p : ℝ) = 1 := by
              rw [← Real.rpow_natCast R 2, ← Real.rpow_neg hR.le,
                ← Real.rpow_natCast R (4 * d + 2), ← Real.rpow_mul hR.le,
                ← Real.rpow_add hR, ← Real.rpow_add hR]
              have heq : (2 - (4 * (d : ℝ) + 2) / p) + -(2 : ℝ) +
                  ((4 * d + 2 : ℕ) : ℝ) * (1 / p) = 0 := by
                push_cast
                ring
              norm_num only [Nat.cast_ofNat]
              rw [heq, Real.rpow_zero]
            have volume_backwardCylinder_toReal (P₀ : KineticPoint d) {R : ℝ} (hR : 0 < R) :
                (volume (backwardCylinder P₀ R)).toReal =
                R ^ (4 * d + 2) *
                  (volume (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)).toReal := by
              rw [← kineticAffine_image_unitCylinder P₀ hR, volume_kineticAffine_image P₀ hR,
                ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_pos hR _).le]
            obtain ⟨f, hf, hrange, hcap, _, hsupport⟩ := exists_unit_cutoff d
            obtain ⟨C₀, hC₀, hop⟩ := exists_scaledUnitCutoff_operator_bound hf
            let V := (volume (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)).toReal
            let C₁ := max C_A 0 * C₀ * V ^ (1 / p)
            have hV : 0 ≤ V := ENNReal.toReal_nonneg
            have hCA : 0 ≤ max C_A 0 := le_max_right _ _
            refine ⟨C₁, mul_nonneg (mul_nonneg hCA hC₀) (Real.rpow_nonneg hV _), ?_⟩
            intro lam hlam hLam A hA P₀ R ell eta hR hell heta heta1 O hO hQO u hu0 hu hdensity P hP
            let Q := backwardCylinder P₀ R
            let psi := scaledUnitCutoff f P₀ R ell
            have hQU : Q ⊆ O := subset_closure.trans hQO
            have hEll : 0 < lam ∧ lam ≤ Lam := ⟨hlam, hLam⟩
            have hEta : eta ∈ Ioo (0 : ℝ) 1 := ⟨heta, heta1⟩
            have hB : 0 ≤ C₀ * ell * (R ^ 2)⁻¹ :=
              mul_nonneg (mul_nonneg hC₀ hell) (inv_nonneg.mpr (sq_nonneg R))
            have hopQ := hop lam hEll.1 A hA P₀ R ell hR hell
            have hsmooth := scaledUnitCutoff_isSmoothNear hf P₀ R ell (closure Q)
            have hpsi := hsmooth.continuousOn
            have huQ := hu.1.mono hQU
            have hnorm := localizedSource_norm_le_sublevel_volume A
              (isOpen_backwardCylinder P₀ R hR) (volume_backwardCylinder_lt_top P₀ hR).ne
              (hpsi.mono subset_closure) huQ
              (measurable_scaledUnitCutoff_backwardOperator hf hA.1 P₀ R ell)
              ell (C₀ * ell * (R ^ 2)⁻¹) p hB hp
              (fun T _ => (scaledUnitCutoff_bounds hrange P₀ R ell hell T).2) hopQ
            have hdens := near_full_sublevel_volume hO hu.1 P₀ hR hQU ell eta hdensity
            have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
            have hrpow := Real.rpow_le_rpow ENNReal.toReal_nonneg hdens
              (one_div_nonneg.mpr hp0.le)
            have hnorm' := hnorm.trans (mul_le_mul_of_nonneg_left hrpow hB)
            rw [volume_backwardCylinder_toReal P₀ hR,
              Real.mul_rpow hEta.1.le (mul_nonneg (pow_pos hR _).le hV),
              Real.mul_rpow (pow_pos hR _).le hV] at hnorm'
            have hscale := near_full_radius_cancellation hR
            have hmul : max C_A 0 * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
                (eLpNorm (localizedSource A psi u) (ENNReal.ofReal p) (volume.restrict Q)).toReal ≤
                  C₁ * eta ^ (1 / p) * ell := by
              calc
                _ ≤ max C_A 0 * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
                    (C₀ * ell * (R ^ 2)⁻¹ *
                      (eta ^ (1 / p) * ((R ^ (4 * d + 2)) ^ (1 / p) * V ^ (1 / p)))) :=
                  mul_le_mul_of_nonneg_left hnorm' (mul_nonneg hCA (Real.rpow_nonneg hR.le _))
                _ = C₁ * eta ^ (1 / p) * ell := by
                  calc
                    _ = (max C_A 0 * C₀ * V ^ (1 / p)) * eta ^ (1 / p) * ell *
                        (R ^ (2 - (4 * (d : ℝ) + 2) / p) * (R ^ 2)⁻¹ *
                          (R ^ (4 * d + 2)) ^ (1 / p)) := by ring
                    _ = _ := by rw [hscale, mul_one]
            have hboundary : sSup ((fun T => max (psi T - u T) 0) '' kineticBoundary P₀ R) ≤ 0 := by
              apply csSup_le ((kineticBoundary_nonempty P₀ hR).image _)
              rintro _ ⟨T, hT, rfl⟩
              have hz := scaledUnitCutoff_boundary_eq_zero hsupport P₀ hR ell hT
              have hn := hu0 T (hQO hT.1)
              change max (scaledUnitCutoff f P₀ R ell T - u T) 0 ≤ 0
              rw [hz, zero_sub]
              exact max_le (neg_nonpos.mpr hn) le_rfl
            have hPunit : P ∈ Q := by
              obtain ⟨T, hT, rfl⟩ := hP
              exact (kineticAffine_mem_cylinder P₀ T hR).mpr
                ((cap_compact_inside d).2 (subset_closure hT))
            have hbounded := (isCompact_closure_backwardCylinder P₀ R hR).bddAbove_image
              (hpsi.sub (hu.1.mono hQO))
            have hpoint := (le_csSup hbounded (mem_image_of_mem (fun T => psi T - u T)
              (subset_closure hPunit))).trans (hu.nonnegative_constant.2 P₀ R hR hQO psi hsmooth)
            have hplateau : psi P = ell := scaledUnitCutoff_eq_level hcap P₀ hR ell hP
            rw [hplateau] at hpoint
            change ell - u P ≤ _ at hpoint
            have hlast := hpoint.trans (add_le_add hboundary hmul)
            simp only [zero_add] at hlast
            linarith only [hlast]
          cases d with
          | zero => omega
          | succ n =>
            obtain ⟨C₁, _, hC₁⟩ := near_full_with_nonneg_constant (n + 1)
            exact ⟨C₁, hC₁⟩
        obtain ⟨C, hC⟩ := near_full
        let B := max C 0
        let delta := 1 / (4 * (B + 1))
        let eta := min (1 / 2 : ℝ) (delta ^ p)
        have hB : 0 ≤ B := le_max_right _ _
        have hden : 0 < 4 * (B + 1) := by positivity
        have hdelta : 0 < delta := one_div_pos.mpr hden
        have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
        have heta : 0 < eta := lt_min (by norm_num) (Real.rpow_pos_of_pos hdelta _)
        have heta1 : eta < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
        have hroot : eta ^ (1 / p) ≤ delta := by
          calc
            _ ≤ (delta ^ p) ^ (1 / p) := Real.rpow_le_rpow heta.le
              (min_le_right _ _) (one_div_nonneg.mpr hp0.le)
            _ = delta := by rw [← Real.rpow_mul hdelta.le]; simp [hp0.ne']
        have hsmall : B * delta ≤ 1 / 4 := by
          change B * (1 / (4 * (B + 1))) ≤ 1 / 4
          rw [mul_one_div, div_le_iff₀ hden]
          linarith only [hB]
        have hCsmall : C * eta ^ (1 / p) ≤ 1 / 4 :=
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg heta.le _)).trans
            ((mul_le_mul_of_nonneg_left hroot hB).trans hsmall)
        refine ⟨eta, heta, heta1, ?_⟩
        intro lam hlam hLam A hA P₀ R ell hR hell O hO hQO u hu0 hu hdensity P hP
        exact (mul_le_mul_of_nonneg_right (by linarith only [hCsmall]) hell).trans
          (hC lam hlam hLam A hA P₀ R ell eta hR hell heta heta1 O hO hQO u hu0 hu hdensity P hP)
      have exists_joint_growth_parameters (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
          ∃ (eta : ℝ) (m : ℕ) (delta eps : ℝ),
          0 < eta ∧ eta < 1 ∧ 0 < m ∧
          0 < (((m : ℝ) + 1) / (m : ℝ)) * (1 - c * eta) ∧
          (((m : ℝ) + 1) / (m : ℝ)) * (1 - c * eta) < 1 ∧
          0 < delta ∧ delta < 1 ∧ 0 < eps ∧ eps < 1 ∧
          kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps ''
            referenceRegion d m (referenceBound m) ⊆
              backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
          closure (kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps '' samplingCylinder d m) ⊆
            backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
          (∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
            ∀ (P0 : KineticPoint d) (r ell : ℝ), 0 < r → 0 ≤ ell →
            ∀ O : Set (KineticPoint d), IsOpen O → closure (backwardCylinder P0 r) ⊆ O →
            ∀ u : KineticPoint d → ℝ, (∀ Z ∈ O, 0 ≤ u Z) →
              IsAdmissibleSupersolution A O p C_A u →
              (1 - eta) * (volume (backwardCylinder P0 r)).toReal ≤
                (volume ({Z | ell ≤ u Z} ∩ backwardCylinder P0 r)).toReal →
              ∀ Z ∈ kineticAffine P0 r '' cap d, (3 / 4 : ℝ) * ell ≤ u Z) ∧
          (∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
            ∀ (P0 : KineticPoint d) (r ell : ℝ), 0 < r → 0 ≤ ell →
            ∀ O : Set (KineticPoint d), IsOpen O →
              closure (kineticAffine P0 r '' stackComparisonRegion d m) ⊆ O →
            ∀ u : KineticPoint d → ℝ, (∀ Z ∈ O, 0 ≤ u Z) →
              IsAdmissibleSupersolution A O p C_A u →
              (1 - eta) * (volume (backwardCylinder P0 r)).toReal ≤
                (volume ({Z | ell ≤ u Z} ∩ backwardCylinder P0 r)).toReal →
              ∀ Z ∈ forwardStack P0 r m, delta * ell ≤ u Z) := by
        have exists_stack_positivity_constant (m : ℕ) :
            ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
            ∀ (p C_A : ℝ), 1 ≤ p → ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
            ∀ (P0 : KineticPoint d) (r ell : ℝ), 0 < r → 0 ≤ ell →
            ∀ O : Set (KineticPoint d), IsOpen O →
              closure (kineticAffine P0 r '' stackComparisonRegion d m) ⊆ O →
            ∀ u : KineticPoint d → ℝ, (∀ P ∈ O, 0 ≤ u P) →
              IsAdmissibleSupersolution A O p C_A u →
              (∀ Z ∈ kineticAffine P0 r '' cap d, (3 / 4 : ℝ) * ell ≤ u Z) →
              ∀ P ∈ forwardStack P0 r m, delta * ell ≤ u P := by
          let M := (m : ℝ) + 1
          have hM : 0 < M := by dsimp only [M]; positivity
          have hacc : 0 < stackAcceleration m := by unfold stackAcceleration; positivity
          obtain ⟨c, hc, hc1, hprop⟩ := propagation_dimensionless d hd lam Lam
            (1 / (32 * M)) (stackAcceleration m * Real.sqrt M)
            (1 / (1024 * M ^ (3 / 2 : ℝ))) (1 / (16 * Real.sqrt M))
            hlam hLam (by positivity) (by
              apply (div_le_one (by positivity : 0 < 32 * M)).mpr
              dsimp only [M]
              have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
              linarith only [hm]) (by positivity) (by positivity) (by positivity)
          refine ⟨(3 / 4 : ℝ) * c, by positivity, by linarith only [hc1], ?_⟩
          intro p C_A hp A hA P0 r ell hr hell O hO hregion u hnonneg hu hcap P hP
          obtain ⟨x, v, hsk, _, _, hxP, hvP, hTlo, hThi, hcapCorr, hfullCorr⟩ :=
            exists_stack_corridors P0 P hr m hP
          obtain ⟨hscaleTime, hscaleH, hscaleX, hscaleV⟩ := stack_propagation_scaling m hr
          have hT1 : 0 < M * r ^ 2 := mul_pos hM (sq_pos_of_pos hr)
          have hPO : P ∈ O := by
            have hpoint : P ∈ corridor (stackStartTime P0 r) (-(r ^ 2 / 32))
                (P.time - stackStartTime P0 r) (r ^ 3 / (2 * 8 ^ 3)) (r / 16) x v := by
              refine ⟨⟨by linarith only [hTlo, sq_pos_of_pos hr], le_rfl⟩, ?_, ?_⟩
              · rw [hxP, sub_self]
                norm_num [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]
                positivity
              · rw [hvP, sub_self]
                norm_num [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]
                positivity
            exact hregion (subset_closure (hfullCorr hpoint))
          have hprop' := hprop (M * r ^ 2) hT1 p C_A hp A hA O hO
            (stackStartTime P0 r) P hPO
          rw [neg_mul, hscaleTime, hscaleH, hscaleX, hscaleV] at hprop'
          have htlo : r ^ 2 / 32 ≤ P.time - stackStartTime P0 r := by
            linarith only [hTlo, sq_pos_of_pos hr]
          have hbound := hprop' htlo hThi x v (by simpa only [stackAcceleration] using hsk) hxP hvP
            (fun Q hQ => hregion (subset_closure (hfullCorr hQ))) ((3 / 4 : ℝ) * ell)
            (mul_nonneg (by norm_num) hell) u hnonneg hu
            (fun Q hQ ht => hcap Q (hcapCorr ⟨⟨hQ.1.1, sub_nonpos.mpr ht⟩, hQ.2⟩))
          convert hbound using 1
          ring
        have exists_contractive_stack_height {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1) :
            ∃ m : ℕ, 0 < m ∧ 0 < (((m : ℝ)+1)/(m : ℝ))*(1-c*eta) ∧
            (((m : ℝ)+1)/(m : ℝ))*(1-c*eta) < 1 := by
          have density_factor_pos_lt_one :
              0 < 1-c*eta ∧ 1-c*eta < 1 := by
            constructor <;> nlinarith
          obtain ⟨m, hm⟩ := exists_nat_gt ((1-c*eta)/(c*eta))
          have hce : 0 < c*eta := mul_pos hc heta
          have hf := density_factor_pos_lt_one
          have hmpos : 0 < (m : ℝ) := (div_pos hf.1 hce).trans hm
          have hmn : 0 < m := by exact_mod_cast hmpos
          refine ⟨m, hmn, mul_pos (div_pos (by linarith) hmpos) hf.1, ?_⟩
          have hmul := (div_lt_iff₀ hce).mp hm
          have heq : (((m : ℝ)+1)/(m : ℝ))*(1-c*eta) =
              (((m : ℝ)+1)*(1-c*eta))/(m : ℝ) := by ring
          rw [heq]
          apply (div_lt_iff₀ hmpos).mpr
          nlinarith
        obtain ⟨eta, heta, heta1, hnear⟩ := near_full_threshold
        obtain ⟨m, hm, ha, ha1⟩ := exists_contractive_stack_height heta heta1
        obtain ⟨delta, hdelta, hdelta1, hstack⟩ :=
          exists_stack_positivity_constant m
        obtain ⟨eps, heps, heps1, _, _, _, _, hscaled, hsigma⟩ := exists_reference_geometry d m
        refine ⟨eta, m, delta, eps, heta, heta1, hm, ha, ha1, hdelta, hdelta1,
          heps, heps1, hscaled, hsigma, hnear lam hlam hLam, ?_⟩
        intro A hA P0 r ell hr hell O hO hregion u hnonneg hu hdensity
        have hQO : closure (backwardCylinder P0 r) ⊆ O := by
          apply (closure_mono ?_).trans hregion
          rw [← kineticAffine_image_unitCylinder P0 hr]
          apply image_mono
          exact subset_closure.trans (stackComparisonRegion_geometry d m).2.2.1
        exact hstack p C_A hp A hA P0 r ell hr hell O hO hregion u hnonneg hu
          (hnear lam hlam hLam A hA P0 r ell hr hell O hO hQO u hnonneg hu hdensity)
      have exists_affine_ink_spots_constants :
          ∃ c C : ℝ, 0 < c ∧ c < 1 ∧ 0 < C ∧
          ∀ m : ℕ, 0 < m →
          ∀ eta r0 : ℝ, 0 < eta → eta < 1 → 0 < r0 → r0 < 1 →
          ∀ (P0 : KineticPoint d) (R : ℝ), 0 < R →
          ∀ E F : Set (KineticPoint d),
            Bornology.IsBounded E → Bornology.IsBounded F →
            MeasurableSet E → MeasurableSet F → E ⊆ F ∩ backwardCylinder P0 R →
            (∀ (P : KineticPoint d) (r : ℝ), 0 < r →
              backwardCylinder P r ⊆ backwardCylinder P0 R →
              (1 - eta) * (volume (backwardCylinder P r)).toReal ≤
                (volume (E ∩ backwardCylinder P r)).toReal →
              r < r0 * R ∧ forwardStack P r m ⊆ F) →
            (volume E).toReal ≤ (((m : ℝ) + 1) / (m : ℝ)) * (1 - c * eta) *
              ((volume (F ∩ backwardCylinder P0 R)).toReal +
                R ^ (4 * d + 2) * C * (m : ℝ) * r0 ^ 2) := by
        obtain ⟨c, C, hc, hc1, hC, hink⟩ := kinetic_crawling_ink_spots_aux d hd
        refine ⟨c, C, hc, hc1, hC, ?_⟩
        intro m hm eta r0 heta heta1 hr0 hr01 P0 R hR E F hEb hFb hE hF hEF hstack
        let phi := kineticAffine P0 R
        let Ep := phi ⁻¹' E
        let Fp := phi ⁻¹' F
        let Q := backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1
        have hEp : MeasurableSet Ep := measurableSet_kineticAffine_preimage P0 R hE
        have hFp : MeasurableSet Fp := measurableSet_kineticAffine_preimage P0 R hF
        have hEpF : Ep ⊆ Fp ∩ Q := by
          intro P hP
          have hh := hEF hP
          exact ⟨hh.1, (kineticAffine_mem_cylinder P0 P hR).mp hh.2⟩
        have hfactor : 0 < R ^ (4 * d + 2) := pow_pos hR _
        have hphiInj : Function.Injective phi :=
          (kineticAffineHomeomorph P0 R hR.ne').injective
        have hphiF : phi '' Fp = F :=
          (kineticAffineHomeomorph P0 R hR.ne').toEquiv.image_preimage F
        have hphiQ : phi '' Q = backwardCylinder P0 R :=
          kineticAffine_image_unitCylinder P0 hR
        have hphiE : phi '' Ep = E := (kineticAffineHomeomorph P0 R hR.ne').toEquiv.image_preimage E
        have hphiFQ : phi '' (Fp ∩ Q) = F ∩ backwardCylinder P0 R := by
          rw [image_inter hphiInj, hphiF, hphiQ]
        have hlocal (P : KineticPoint d) (r : ℝ) (hr : 0 < r)
            (hsub : backwardCylinder P r ⊆ Q)
            (hdense : (1 - eta) * (volume (backwardCylinder P r)).toReal ≤
              (volume (Ep ∩ backwardCylinder P r)).toReal) :
            r < r0 ∧ forwardStack P r m ⊆ Fp := by
          have himage := kineticAffine_image_cylinder P0 P R r hR hr
          have hsubp : backwardCylinder (phi P) (R * r) ⊆ backwardCylinder P0 R := by
            rw [← himage, ← kineticAffine_image_unitCylinder P0 hR]
            exact image_mono hsub
          have hinter : phi '' (Ep ∩ backwardCylinder P r) =
              E ∩ backwardCylinder (phi P) (R * r) := by
            rw [image_inter hphiInj, hphiE, himage]
          have hdensep : (1 - eta) *
              (volume (backwardCylinder (phi P) (R * r))).toReal ≤
                (volume (E ∩ backwardCylinder (phi P) (R * r))).toReal := by
            rw [← hinter, ← himage, volume_affine_image_toReal P0 hR,
              volume_affine_image_toReal P0 hR]
            nlinarith only [mul_le_mul_of_nonneg_left hdense hfactor.le]
          obtain ⟨hsmall, hforward⟩ := hstack (phi P) (R * r) (mul_pos hR hr) hsubp hdensep
          refine ⟨?_, ?_⟩
          · nlinarith only [hsmall, hR]
          · intro Z hZ
            apply hforward
            rw [← kineticAffine_image_stack P0 P R r hR hr m]
            exact ⟨Z, hZ, rfl⟩
        have hbound := hink m hm eta r0 heta heta1 hr0 hr01 Ep Fp
          (isBounded_kineticAffine_preimage P0 hR.ne' hEb)
          (isBounded_kineticAffine_preimage P0 hR.ne' hFb)
          hEp.nullMeasurableSet hFp.nullMeasurableSet hEpF hlocal
        have hvolE := volume_affine_image_toReal P0 hR Ep
        have hvolF := volume_affine_image_toReal P0 hR (Fp ∩ Q)
        rw [hphiE] at hvolE
        rw [hphiFQ] at hvolF
        rw [hvolE, hvolF]
        nlinarith only [mul_le_mul_of_nonneg_left hbound hfactor.le]
      obtain ⟨c, C, hc, hc1, hC, hink⟩ := exists_affine_ink_spots_constants
      obtain ⟨eta, m, delta, eps, heta, heta1, hm, ha, ha1, hdelt, hdelt1,
        heps, heps1, hscaled, hsigma, hnear, hstack⟩ :=
        exists_joint_growth_parameters c hc hc1
      let a := (((m : ℝ) + 1) / (m : ℝ)) * (1 - c * eta)
      let V := (volume (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)).toReal
      have hV : 0 < V := ENNReal.toReal_pos
        (volume_cylinder_pos_ne_top _ zero_lt_one).1.ne'
        (volume_cylinder_pos_ne_top _ zero_lt_one).2
      refine ⟨eps, heps, heps1,
        kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps (samplingCenter d m),
        eps, heps, ?_, ?_⟩
      · rw [← physical_sampling_image _ heps m]
        exact hsigma
      intro beta hbeta _hbeta1
      obtain ⟨N, hN, _, r0, hr0, hr01, herror⟩ :=
        exists_density_leakage_choice ha ha1 heta1 hbeta hC hV m hm
      obtain ⟨cmac, hcmac, _, hmacro⟩ :=
        exists_physical_macroscopic_cap_constant d hd lam Lam hlam hLam m r0 hr0 hr01
      let kappa := (3 / 4 : ℝ) * cmac * delta ^ N
      refine ⟨kappa, by dsimp only [kappa]; positivity, ?_⟩
      intro A hA P0 R hR O hO hdomain u hnonneg hu hdensity
      let scale := R * eps
      have hscale : 0 < scale := mul_pos hR heps
      let G := kineticAffine P0 scale '' referenceRegion d m (referenceBound m)
      let S := kineticAffine P0 scale (samplingCenter d m)
      let Sigma := backwardCylinder S scale
      have hGO : closure G ⊆ O :=
        buffered_reference_preserves_domain P0 hR m hscaled O hdomain
      have hSigmaO : closure Sigma ⊆ O :=
        (physical_sampling_closure_subset P0 hscale m).trans hGO
      have hSigmaG : Sigma ⊆ G := by
        dsimp only [Sigma, S]
        rw [← physical_sampling_image P0 hscale m]
        exact image_mono (subset_closure.trans
          (sampling_closure_subset_reference d m (referenceBound_large m)))
      have hGb : Bornology.IsBounded G := isBounded_kineticAffine_image P0 scale
        (isBounded_referenceRegion d m (by linarith only [referenceBound_large m]))
      have hGopen : IsOpen G := (kineticAffineHomeomorph P0 scale hscale.ne').isOpenMap _
        (isOpen_referenceRegion d m (referenceBound m))
      have hSigmab : Bornology.IsBounded Sigma :=
        (isCompact_closure_backwardCylinder S scale hscale).isBounded.subset subset_closure
      have hSigmaMeas : MeasurableSet Sigma := (isOpen_cylinder S scale).measurableSet
      let E := fun j : ℕ => {P | delta ^ j ≤ u P} ∩ Sigma
      let F := fun j : ℕ => {P | delta ^ (j + 1) ≤ u P} ∩ G
      have hEMeas (j : ℕ) : MeasurableSet (E j) := measurableSet_superlevel_inter hO
        hSigmaMeas (subset_closure.trans hSigmaO) hu.1 _
      have hFMeas (j : ℕ) : MeasurableSet (F j) := measurableSet_superlevel_inter hO
        hGopen.measurableSet (subset_closure.trans hGO) hu.1 _
      have hEb (j : ℕ) : Bornology.IsBounded (E j) :=
        superlevel_inter_isBounded hSigmab u _
      have hFb (j : ℕ) : Bornology.IsBounded (F j) :=
        superlevel_inter_isBounded hGb u _
      have hdown (j : ℕ) : delta ^ (j + 1) ≤ delta ^ j := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hdelt.le j) hdelt1.le
      have hEF (j : ℕ) : E j ⊆ F j ∩ Sigma := by
        intro P hP
        exact ⟨⟨(hdown j).trans hP.1, hSigmaG hP.2⟩, hP.2⟩
      have hFQ (j : ℕ) : F j ∩ Sigma = E (j + 1) := by
        ext P
        constructor
        · intro hP; exact ⟨hP.1.1, hP.2⟩
        · intro hP; exact ⟨⟨hP.1, hSigmaG hP.2⟩, hP.2⟩
      have hlocalLevel (j : ℕ) (Q : KineticPoint d) (r : ℝ)
          (hsub : backwardCylinder Q r ⊆ Sigma) :
          E j ∩ backwardCylinder Q r = {Z | delta ^ j ≤ u Z} ∩ backwardCylinder Q r := by
        ext Z
        constructor
        · intro hZ; exact ⟨hZ.1.1, hZ.2⟩
        · intro hZ; exact ⟨⟨hZ.1, hsub hZ.2⟩, hZ.2⟩
      have hmacDensity (j : ℕ) (Q : KineticPoint d) (r : ℝ) (hr : 0 < r)
          (hsub : backwardCylinder Q r ⊆ Sigma) (hbig : r0 * scale ≤ r)
          (hden : (1 - eta) * (volume (backwardCylinder Q r)).toReal ≤
            (volume ({Z | delta ^ j ≤ u Z} ∩ backwardCylinder Q r)).toReal) :
          ∀ Z ∈ backwardCylinder P0 scale, (3 / 4 : ℝ) * cmac * delta ^ j ≤ u Z := by
        have hQO : closure (backwardCylinder Q r) ⊆ O := (closure_mono hsub).trans hSigmaO
        have hcap := hnear A hA Q r (delta ^ j) hr (pow_nonneg hdelt.le j)
          O hO hQO u hnonneg hu hden
        have hb := hmacro p C_A hp A hA P0 scale hscale O hO hGO u hnonneg hu
          Q r ((3 / 4 : ℝ) * delta ^ j) hr hbig hsub (by positivity) hcap
        intro Z hZ
        convert hb Z hZ using 1
        ring
      have hSigmaVol : (volume Sigma).toReal = scale ^ (4 * d + 2) * V := by
        dsimp only [Sigma]
        rw [← kineticAffine_image_unitCylinder S hscale, volume_affine_image_toReal S hscale]
      have hSigmaVolPos : 0 < (volume Sigma).toReal := by rw [hSigmaVol]; positivity
      have hphysicalSigma : kineticAffine P0 R ''
          backwardCylinder
            (kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps (samplingCenter d m)) eps = Sigma := by
        rw [← physical_sampling_image _ heps m]
        rw [image_image]
        have hc0 : kineticAffine P0 R ∘ kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps =
            kineticAffine P0 scale := by
          rw [kineticAffine_comp]
          congr 1
          ext i <;> simp [kineticAffine]
        rw [← Function.comp_def, hc0, physical_sampling_image P0 hscale m]
      rw [hphysicalSigma] at hdensity
      have htarget : backwardCylinder P0 (eps * R) = backwardCylinder P0 scale := by
        dsimp only [scale]
        rw [mul_comm eps R]
      rw [htarget]
      by_cases hmac : ∃ j : ℕ, j < N ∧ ∃ (Q : KineticPoint d) (r : ℝ),
          0 < r ∧ backwardCylinder Q r ⊆ Sigma ∧ r0 * scale ≤ r ∧
          (1 - eta) * (volume (backwardCylinder Q r)).toReal ≤
            (volume ({Z | delta ^ j ≤ u Z} ∩ backwardCylinder Q r)).toReal
      · obtain ⟨j, hj, Q, r, hr, hsub, hbig, hden⟩ := hmac
        have hpow : delta ^ N ≤ delta ^ j :=
          pow_le_pow_of_le_one hdelt.le hdelt1.le hj.le
        intro Z hZ
        exact (mul_le_mul_of_nonneg_left hpow (by positivity :
          0 ≤ (3 / 4 : ℝ) * cmac)).trans (hmacDensity j Q r hr hsub hbig hden Z hZ)
      let e := fun j : ℕ => (volume (E j)).toReal / (volume Sigma).toReal
      let L0 := C * (m : ℝ) * r0 ^ 2 / V
      have hzero : beta ≤ e 0 := by
        apply (le_div_iff₀ hSigmaVolPos).mpr
        simpa only [E, pow_zero] using hdensity
      have hstep (j : ℕ) (hj : j < N) : e j ≤ a * (e (j + 1) + L0) := by
        have hcriterion (Q : KineticPoint d) (r : ℝ) (hr : 0 < r)
            (hsub : backwardCylinder Q r ⊆ Sigma)
            (hden : (1 - eta) * (volume (backwardCylinder Q r)).toReal ≤
              (volume (E j ∩ backwardCylinder Q r)).toReal) :
            r < r0 * scale ∧ forwardStack Q r m ⊆ F j := by
          rw [hlocalLevel j Q r hsub] at hden
          have hsmall : r < r0 * scale := by
            by_contra hs
            exact hmac ⟨j, hj, Q, r, hr, hsub, le_of_not_gt hs, hden⟩
          refine ⟨hsmall, ?_⟩
          have hcomp := physical_sampling_comparison_image_subset P0 Q hscale hr m hsub
          have hcompO := (closure_mono hcomp).trans hGO
          have hvis := hstack A hA Q r (delta ^ j) hr (pow_nonneg hdelt.le j)
            O hO hcompO u hnonneg hu hden
          intro Z hZ
          exact ⟨by simpa only [mem_ofPred_eq, pow_succ, mul_comm delta] using hvis Z hZ,
            hcomp (forwardStack_subset_comparison Q hr m hZ)⟩
        have hb := hink m hm eta r0 heta heta1 hr0 hr01 S scale hscale
          (E j) (F j) (hEb j) (hFb j) (hEMeas j) (hFMeas j) (hEF j) hcriterion
        rw [hFQ j] at hb
        apply (div_le_iff₀ hSigmaVolPos).mpr
        have heq : a * (e (j + 1) + L0) * (volume Sigma).toReal =
            a * ((volume (E (j + 1))).toReal + scale ^ (4 * d + 2) * C * (m : ℝ) * r0 ^ 2) := by
          dsimp only [e, L0]
          rw [hSigmaVol]
          field_simp
        rw [heq]
        exact hb
      have hterminal := density_ladder_numeric ha e N hzero hstep
      have hterminalDense : 1 - eta < e N := by linarith only [hterminal, herror]
      have hdenSigma : (1 - eta) * (volume Sigma).toReal ≤
          (volume ({Z | delta ^ N ≤ u Z} ∩ Sigma)).toReal :=
        (le_div_iff₀ hSigmaVolPos).mp hterminalDense.le
      have hbigSigma : r0 * scale ≤ scale :=
        (mul_le_mul_of_nonneg_right hr01.le hscale.le).trans_eq (one_mul scale)
      exact hmacDensity N S scale hscale Subset.rfl hbigSigma hdenSigma
    obtain ⟨theta, ht, ht1, S, r, hr, hS, hbeta⟩ :=
      exists_growth_parameters
    refine ⟨theta, ht, ht1, S, r, hr, hS, ?_⟩
    intro beta hb hb1
    obtain ⟨kappa, hk, hbound⟩ := hbeta beta hb hb1
    refine ⟨kappa, hk, ?_⟩
    intro A hmeas hsym hlo hhi
    exact hbound A ⟨hmeas, hsym, hlo, hhi⟩
  have oscillation_decay :
      ∃ alpha D : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ O : Set (KineticPoint d), IsOpen O →
      ∀ (P0 : KineticPoint d) (R rho : ℝ), 0 < R → 0 < rho → rho ≤ R →
        closure (backwardCylinder P0 R) ⊆ O →
      ∀ u : KineticPoint d → ℝ, IsAdmissibleSolution A O p C_A u →
        oscillationOn u (backwardCylinder P0 rho) ≤
          D * (rho / R) ^ alpha * oscillationOn u (backwardCylinder P0 R) := by
    have oscillation_contraction :
        ∃ theta q : ℝ, 0 < theta ∧ theta < 1 ∧ 0 < q ∧ q < 1 ∧
        ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
        ∀ O : Set (KineticPoint d), IsOpen O →
        ∀ (P0 : KineticPoint d) (R : ℝ), 0 < R →
          closure (backwardCylinder P0 R) ⊆ O →
        ∀ u : KineticPoint d → ℝ, IsAdmissibleSolution A O p C_A u →
          oscillationOn u (backwardCylinder P0 (theta * R)) ≤
            q * oscillationOn u (backwardCylinder P0 R) := open MeasureTheory in by
      have exists_growth_half_upper_bound :
          ∃ (theta : ℝ) (S : KineticPoint d) (r kappa : ℝ),
          0 < theta ∧ theta < 1 ∧ 0 < r ∧ 0 < kappa ∧ kappa ≤ 1 ∧
          closure (backwardCylinder S r) ⊆
            backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
          ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
          ∀ O : Set (KineticPoint d), IsOpen O →
          ∀ (P0 : KineticPoint d) (R : ℝ), 0 < R → closure (backwardCylinder P0 R) ⊆ O →
          ∀ u : KineticPoint d → ℝ, IsAdmissibleSupersolution A O p C_A (fun P => -u P) →
          ∀ b h : ℝ, 0 < h → (∀ P ∈ closure (backwardCylinder P0 R), u P ≤ b) →
            (1 / 2 : ℝ) * (volume (kineticAffine P0 R '' backwardCylinder S r)).toReal ≤
              (volume ({P | u P ≤ b - h} ∩
                kineticAffine P0 R '' backwardCylinder S r)).toReal →
            ∀ P ∈ backwardCylinder P0 (theta * R), u P ≤ b - kappa * h := by
        obtain ⟨theta, ht, ht1, S, r, hr, hS, hbeta⟩ :=
          kinetic_growth_lemma_aux
        obtain ⟨k, hk, hbound⟩ := hbeta (1 / 2) (by norm_num) (by norm_num)
        refine ⟨theta, S, r, min k 1, ht, ht1, hr, lt_min hk (by norm_num),
          min_le_right _ _, hS, ?_⟩
        intro A hA O hO P0 R hR hQ u hu b h hh hupper hdense P hP
        have hcont : ContinuousOn u O := by
          have heq : (-(fun P => -u P)) = u := by funext P; simp only [Pi.neg_apply, neg_neg]
          rw [← heq]
          exact hu.1.neg
        have hlocal : ∀ epsilon : ℝ, 0 < epsilon → u P ≤ b - min k 1 * h + epsilon := by
          intro epsilon hepsilon
          let U := O ∩ {Z | u Z < b + epsilon}
          have hU : IsOpen U := hcont.isOpen_inter_preimage hO isOpen_Iio
          have hQU : closure (backwardCylinder P0 R) ⊆ U := by
            intro Z hZ
            exact ⟨hQ hZ, (hupper Z hZ).trans_lt (by linarith only [hepsilon])⟩
          let w := fun Z => h⁻¹ * (-u Z) + (b + epsilon) / h
          have hw : IsAdmissibleSupersolution A U p C_A w :=
            (admissible_pos_affine hu h⁻¹ ((b + epsilon) / h) (inv_pos.mpr hh)).mono
              inter_subset_left
          have hn : ∀ Z ∈ U, 0 ≤ w Z := by
            intro Z hZ
            dsimp only [w]
            rw [inv_mul_eq_div, ← add_div]
            have hz : u Z < b + epsilon := hZ.2
            exact div_nonneg (by linarith only [hz]) hh.le
          have hlevels : {Z | u Z ≤ b - h} ∩ kineticAffine P0 R '' backwardCylinder S r ⊆
              {Z | 1 ≤ w Z} ∩ kineticAffine P0 R '' backwardCylinder S r := by
            intro Z hZ
            refine ⟨?_, hZ.2⟩
            change 1 ≤ h⁻¹ * (-u Z) + (b + epsilon) / h
            rw [inv_mul_eq_div, ← add_div]
            apply (le_div_iff₀ hh).mpr
            have hz : u Z ≤ b - h := hZ.1
            linarith only [hz, hepsilon]
          have hfinite : volume (kineticAffine P0 R '' backwardCylinder S r) ≠ ⊤ := by
            have hinside : kineticAffine P0 R '' backwardCylinder S r ⊆ backwardCylinder P0 R := by
              rw [← kineticAffine_image_unitCylinder P0 hR]
              exact image_mono (subset_closure.trans hS)
            exact ne_top_of_le_ne_top (Covering.volume_cylinder_pos_ne_top P0 hR).2
              (measure_mono hinside)
          have hdenw : (1 / 2 : ℝ) *
              (volume (kineticAffine P0 R '' backwardCylinder S r)).toReal ≤
                (volume ({Z | 1 ≤ w Z} ∩ kineticAffine P0 R '' backwardCylinder S r)).toReal :=
            hdense.trans (ENNReal.toReal_mono
              (ne_top_of_le_ne_top hfinite (measure_mono inter_subset_right)) (measure_mono hlevels))
          have hkP := hbound A hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 P0 R hR U hU hQU
            w hn hw hdenw P hP
          have hkP' : min k 1 ≤ w P := (min_le_left _ _).trans hkP
          dsimp only [w] at hkP'
          rw [inv_mul_eq_div, ← add_div, le_div_iff₀ hh] at hkP'
          linarith only [hkP']
        apply le_of_forall_pos_le_add
        exact hlocal
      obtain ⟨theta, S, r, kappa, ht, ht1, _hr, hk, hk1, _hS, hupper⟩ :=
        exists_growth_half_upper_bound
      refine ⟨theta, 1 - kappa / 2, ht, ht1, by linarith only [hk1],
        by linarith only [hk], ?_⟩
      intro A hA O hO P0 R hR hQ u hu
      let Q := backwardCylinder P0 R
      let Qsmall := backwardCylinder P0 (theta * R)
      let Sigma := kineticAffine P0 R '' backwardCylinder S r
      have hQc : IsCompact (closure Q) := isCompact_closure_backwardCylinder P0 R hR
      have huc : ContinuousOn u (closure Q) := hu.1.1.mono hQ
      have habc : BddAbove (u '' closure Q) := hQc.bddAbove_image huc
      have hbbc : BddBelow (u '' closure Q) := hQc.bddBelow_image huc
      have hab : BddAbove (u '' Q) := habc.mono (image_mono subset_closure)
      have hbb : BddBelow (u '' Q) := hbbc.mono (image_mono subset_closure)
      have hsub : Qsmall ⊆ Q := backwardCylinder_radius_mono P0 (mul_pos ht hR)
        ((mul_le_mul_of_nonneg_right ht1.le hR.le).trans_eq (one_mul R))
      have hne := backwardCylinder_nonempty P0 (mul_pos ht hR)
      have hosc : 0 ≤ oscillationOn u Q := oscillationOn_nonneg
        (backwardCylinder_nonempty P0 hR) hab hbb
      by_cases hz : oscillationOn u Q = 0
      · have hm := oscillationOn_mono hne hsub hab hbb
        change oscillationOn u Qsmall ≤ (1 - kappa / 2) * oscillationOn u Q
        simpa only [hz, mul_zero] using hm
      have hpos : 0 < oscillationOn u Q := lt_of_le_of_ne hosc (Ne.symm hz)
      let M := sSup (u '' Q)
      let m := sInf (u '' Q)
      let half := oscillationOn u Q / 2
      have hhalf : 0 < half := div_pos hpos (by norm_num)
      have hM (P : KineticPoint d) (hP : P ∈ closure Q) : u P ≤ M :=
        closure_values_le_sup huc hab hP
      have hm (P : KineticPoint d) (hP : P ∈ closure Q) : m ≤ u P :=
        inf_le_closure_values huc hbb hP
      have hmid : M - half = m + half := by
        dsimp only [half, oscillationOn, M, m]
        ring
      rcases half_density_alternative u Sigma (M - half) with hlo | hhi
      · have himproved := hupper A hA O hO P0 R hR hQ u hu.2 M half hhalf hM hlo
        have hb := oscillationOn_le hne
          (fun P hP => hm P (subset_closure (hsub hP))) himproved
        apply hb.trans_eq
        dsimp only [half, oscillationOn, M, m]
        ring
      · have hneg : IsAdmissibleSupersolution A O p C_A (fun P => -(-u P)) := by
          simpa only [neg_neg] using hu.1
        have hupperneg (P : KineticPoint d) (hP : P ∈ closure Q) : -u P ≤ -m :=
          neg_le_neg (hm P hP)
        have hlevels : {P | M - half ≤ u P} = {P | -u P ≤ -m - half} := by
          ext P
          simp only [mem_ofPred_eq]
          rw [hmid]
          constructor <;> intro h <;> linarith only [h]
        rw [hlevels] at hhi
        have himproved := hupper A hA O hO P0 R hR hQ (fun P => -u P)
          hneg (-m) half hhalf hupperneg hhi
        have hb := oscillationOn_le (a := m + kappa * half) (b := M) hne
          (fun P hP => by have hh := himproved P hP; linarith only [hh])
          (fun P hP => hM P (subset_closure (hsub hP)))
        apply hb.trans_eq
        dsimp only [half, oscillationOn, M, m]
        ring
    obtain ⟨theta, q, ht, ht1, hq, hq1, hcontract⟩ :=
      oscillation_contraction
    let alpha := min 1 (Real.log (1 / q) / Real.log (1 / theta))
    obtain ⟨ha, ha1, hqa⟩ := source_holder_exponent ht ht1 hq hq1
    refine ⟨alpha, theta ^ (-alpha), ha, ha1, ?_⟩
    intro A hA O hO P0 R rho hR hrho hrhoR hQ u hu
    have hcompact := isCompact_closure_backwardCylinder P0 R hR
    have hcont := hu.1.1.mono hQ
    have hab := (hcompact.bddAbove_image hcont).mono (image_mono subset_closure)
    have hbb := (hcompact.bddBelow_image hcont).mono (image_mono subset_closure)
    have hosc := oscillationOn_nonneg (backwardCylinder_nonempty P0 hR) hab hbb
    have hrad (n : ℕ) : 0 < theta ^ n * R := mul_pos (pow_pos ht n) hR
    have hrads (n : ℕ) : theta ^ n * R ≤ R :=
      (mul_le_mul_of_nonneg_right (pow_le_one₀ ht.le ht1.le) hR.le).trans_eq (one_mul R)
    have hsub (n : ℕ) := backwardCylinder_radius_mono P0 (hrad n) (hrads n)
    have hiter (n : ℕ) : oscillationOn u (backwardCylinder P0 (theta ^ n * R)) ≤
        q ^ n * oscillationOn u (backwardCylinder P0 R) := by
      induction n with
      | zero => simp only [pow_zero, one_mul, le_refl]
      | succ n ih =>
        have hc := hcontract A hA O hO P0 (theta ^ n * R) (hrad n)
          ((closure_mono (hsub n)).trans hQ) u hu
        have he : theta * (theta ^ n * R) = theta ^ (n + 1) * R := by rw [pow_succ]; ring
        rw [he] at hc
        have hb := hc.trans (mul_le_mul_of_nonneg_left ih hq.le)
        exact hb.trans_eq (by rw [pow_succ]; ring)
    have hx : 0 < rho / R := div_pos hrho hR
    have hx1 : rho / R ≤ 1 := (div_le_one hR).mpr hrhoR
    obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one hx hx1 ht ht1
    have hsmall : rho ≤ theta ^ n * R := (div_le_iff₀ hR).mp hnhi
    have hm := oscillationOn_mono (backwardCylinder_nonempty P0 hrho)
      (backwardCylinder_radius_mono P0 hrho hsmall)
      (hab.mono (image_mono (hsub n))) (hbb.mono (image_mono (hsub n)))
    have hpower := contraction_power_le_scale_power ht hq.le ha hqa n hnlo
    exact (hm.trans (hiter n)).trans (mul_le_mul_of_nonneg_right hpower hosc)
  obtain ⟨alpha, D, ha, ha1, hdecay⟩ := oscillation_decay
  let C := max D 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨alpha, C, ha, ha1, ?_⟩
  intro A hmeas hsym hlo hhi Omega hOmega u _hbounded hu K _hKO hK R0 hR0 hQ
  have hA : FullElliptic lam Lam A := ⟨hmeas, hsym, hlo, hhi⟩
  let E := holderNeighbourhood R0 K
  obtain ⟨hclosed, hcompact⟩ := holder_neighbourhood_compact K hK R0 hR0
  have hEO : closure E ⊆ Omega := by
    rw [hclosed]
    intro Z hZ
    simp only [mem_iUnion] at hZ
    obtain ⟨P, hP, hZ⟩ := hZ
    exact hQ P hP hZ
  have hcont : ContinuousOn u (closure E) := hu.1.1.mono hEO
  have habc : BddAbove (u '' closure E) := hcompact.bddAbove_image hcont
  have hbbc : BddBelow (u '' closure E) := hcompact.bddBelow_image hcont
  have hab : BddAbove (u '' E) := habc.mono (image_mono subset_closure)
  have hbb : BddBelow (u '' E) := hbbc.mono (image_mono subset_closure)
  have hcenter (P : KineticPoint d) (hP : P ∈ K) : P ∈ closure E := by
    rw [hclosed]
    exact mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP,
      Covering.top_mem_closure_cylinder P (by positivity : 0 < 2 * R0)
        (PDE.center_mem_euclideanBall _ (by positivity))⟩⟩
  have hpair (P : KineticPoint d) (hP : P ∈ K) (P' : KineticPoint d) (hP' : P' ∈ K)
      (ht : P.time ≤ P'.time) :
      |u P - u P'| ≤ C * oscillationOn u E * (quasiDistance P P' / R0) ^ alpha := by
    have hne : E.Nonempty := by
      obtain ⟨Z, hZ⟩ := backwardCylinder_nonempty P (by positivity : 0 < 2 * R0)
      exact ⟨Z, mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP, hZ⟩⟩⟩
    have hosc := oscillationOn_nonneg hne hab hbb
    have hosccl : oscillationOn u (closure E) = oscillationOn u E :=
      oscillationOn_closure hne hcompact hcont
    have hdelta := quasiDistance_nonneg P P'
    by_cases hz : quasiDistance P P' = 0
    · have heq := (quasiDistance_eq_zero_iff P P').mp hz
      rw [congrArg u heq, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hC.le hosc)
        (Real.rpow_nonneg (div_nonneg hdelta hR0.le) _)
    have hdpos : 0 < quasiDistance P P' := lt_of_le_of_ne hdelta (Ne.symm hz)
    by_cases hnear : quasiDistance P P' ≤ R0
    · have hR : 0 < 2 * R0 := by positivity
      have hdistR : quasiDistance P P' ≤ 2 * R0 := by linarith only [hnear, hR0]
      obtain ⟨hpcl, hp'cl⟩ := pair_mem_closed_later_cylinder P P' ht hdpos
      have hsmallO : closure (backwardCylinder P' (quasiDistance P P')) ⊆ Omega :=
        (closure_mono (backwardCylinder_radius_mono P' hdpos hdistR)).trans (hQ P' hP')
      have hcsmall := isCompact_closure_backwardCylinder P' _ hdpos
      have hucsmall := hu.1.1.mono hsmallO
      have habsmall := hcsmall.bddAbove_image hucsmall
      have hbbsmall := hcsmall.bddBelow_image hucsmall
      have habdiff := abs_sub_le_oscillationOn habsmall hbbsmall hpcl hp'cl
      rw [oscillationOn_closure (backwardCylinder_nonempty P' hdpos) hcsmall hucsmall]
        at habdiff
      have hd := hdecay A hA Omega hOmega P' (2 * R0) (quasiDistance P P')
        hR hdpos hdistR (hQ P' hP') u hu
      have hbigE : backwardCylinder P' (2 * R0) ⊆ E := fun Z hZ =>
        mem_iUnion.mpr ⟨P', mem_iUnion.mpr ⟨hP', hZ⟩⟩
      have hbigosc := oscillationOn_nonneg (backwardCylinder_nonempty P' hR)
        (hab.mono (image_mono hbigE)) (hbb.mono (image_mono hbigE))
      have hoscmono := oscillationOn_mono (backwardCylinder_nonempty P' hR) hbigE hab hbb
      have hratio : quasiDistance P P' / (2 * R0) ≤ quasiDistance P P' / R0 :=
        div_le_div_of_nonneg_left hdelta hR0 (by linarith only [hR0])
      have hpower := Real.rpow_le_rpow (div_nonneg hdelta hR.le) hratio ha.le
      have hcoeff : D * (quasiDistance P P' / (2 * R0)) ^ alpha ≤
          C * (quasiDistance P P' / R0) ^ alpha :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (div_nonneg hdelta hR.le) _)).trans
          (mul_le_mul_of_nonneg_left hpower hC.le)
      have hb := (habdiff.trans hd).trans
        (mul_le_mul_of_nonneg_right hcoeff hbigosc)
      have hb' := hb.trans (mul_le_mul_of_nonneg_left hoscmono
        (mul_nonneg hC.le (Real.rpow_nonneg (div_nonneg hdelta hR0.le) _)))
      exact hb'.trans_eq (by ring)
    · have hbase := abs_sub_le_oscillationOn habc hbbc (hcenter P hP) (hcenter P' hP')
      rw [hosccl] at hbase
      have hratio : 1 ≤ quasiDistance P P' / R0 :=
        (one_le_div hR0).mpr (le_of_not_ge hnear)
      have hpower : 1 ≤ (quasiDistance P P' / R0) ^ alpha := by
        simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hratio ha.le
      have hCpower : C ≤ C * (quasiDistance P P' / R0) ^ alpha := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower hC.le
      have hcoeff : 1 ≤ C * (quasiDistance P P' / R0) ^ alpha :=
        (le_max_right D 1).trans hCpower
      have hb := mul_le_mul_of_nonneg_right hcoeff hosc
      rw [one_mul] at hb
      exact hbase.trans (hb.trans_eq (by ring))
  intro P hP P' hP'
  rcases le_total P.time P'.time with ht | ht
  · exact hpair P hP P' hP' ht
  · have hb := hpair P' hP' P hP ht
    simpa only [abs_sub_comm, quasiDistance_symm P' P] using hb

end HypoellipticAleksandrov.KineticAleksandrov

end

