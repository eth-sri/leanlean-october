module

public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Radius
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Pushforward
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Elapsed
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierOccupation
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DualityFromBound
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceBound
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierPremises
public import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensityEvolution

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open SectionTwo Scaling MeasureTheory HypoellipticAleksandrov.Parabolic Set HypoellipticAleksandrov ProbabilityTheory
open scoped ENNReal ProbabilityTheory

/-- Measurable pullback is a real-linear map on bounded Borel data. -/
def occupation_borelComap {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) : BoundedBorel β →ₗ[ℝ] BoundedBorel α where
  toFun g := ⟨fun x => g (f x), g.measurable.comp hf, by
    obtain ⟨C, hC, hb⟩ := g.exists_bound
    exact ⟨C, hC, fun x => hb _⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of measurable bounded-Borel pullback. -/
@[simp] theorem occupation_borelComap_apply {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (f : α → β) (hf : Measurable f)
    (g : BoundedBorel β) (x : α) : occupation_borelComap f hf g x = g (f x) := rfl

/-- The whole-space scalar position equivalence at the two corresponding times. -/
def occupation_positionEquiv {d : ℕ} (Φ : KineticAffineScaling d) (t : ℝ) :
    EvolutionPosition (wholeSpace d) (fun _ => (0 : PDE.Vec d)) t ≃ᵐ
      EvolutionPosition (wholeSpace d) (fun _ => (0 : PDE.Vec d)) (Φ.time t) :=
  (wholeSpacePositionEquiv d t).trans
    (Φ.positionHomeo.toMeasurableEquiv.trans (wholeSpacePositionEquiv d (Φ.time t)).symm)

/-- Conjugation of the original scalar operators by their fixed-time position equivalences. -/
def occupation_pushParabolicFamily {d : ℕ} (Φ : KineticAffineScaling d)
    (Q : ParabolicOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d))) :
    ParabolicOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)) :=
  fun σ τ hστ =>
    (occupation_borelComap (occupation_positionEquiv Φ σ)
      (occupation_positionEquiv Φ σ).measurable).comp
      ((Q (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ)).comp
        (occupation_borelComap (occupation_positionEquiv Φ τ).symm
          (occupation_positionEquiv Φ τ).symm.measurable))

/-- The conjugated scalar family inherits the original endpoint identity. -/
theorem occupation_pushParabolicFamily_endpoint {d : ℕ} (Φ : KineticAffineScaling d)
    (Q : ParabolicOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hQ : ∀ σ, Q σ σ le_rfl = LinearMap.id) (σ : ℝ) :
    occupation_pushParabolicFamily Φ Q σ σ le_rfl = LinearMap.id := by
  ext f y
  simp only [occupation_pushParabolicFamily, LinearMap.comp_apply,
    occupation_borelComap_apply]
  rw [hQ]
  exact congrArg f ((occupation_positionEquiv Φ σ).symm_apply_apply y)

/-- The conjugated scalar family preserves positive data. -/
theorem occupation_pushParabolicFamily_positive {d : ℕ} (Φ : KineticAffineScaling d)
    (Q : ParabolicOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hQ : ∀ σ τ hστ f, 0 ≤ f → 0 ≤ Q σ τ hστ f)
    (σ τ : ℝ) (hστ : σ ≤ τ)
    (f : BoundedBorel (EvolutionPosition (wholeSpace d) (fun _ => 0) τ)) (hf : 0 ≤ f) :
    0 ≤ occupation_pushParabolicFamily Φ Q σ τ hστ f := by
  intro y
  have hf0 : 0 ≤ occupation_borelComap (occupation_positionEquiv Φ τ).symm
      (occupation_positionEquiv Φ τ).symm.measurable f := by
    intro x
    exact hf ((occupation_positionEquiv Φ τ).symm x)
  exact hQ (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ) _ hf0
    (occupation_positionEquiv Φ σ y)

/-- The conjugated scalar family retains its sub-Markov contraction. -/
theorem occupation_pushParabolicFamily_contraction {d : ℕ} (Φ : KineticAffineScaling d)
    (Q : ParabolicOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hQ : ∀ σ τ hστ, Q σ τ hστ 1 ≤ 1) (σ τ : ℝ) (hστ : σ ≤ τ) :
    occupation_pushParabolicFamily Φ Q σ τ hστ 1 ≤ 1 := by
  intro y
  exact hQ (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ)
    (occupation_positionEquiv Φ σ y)

/-- The conjugated scalar family retains composition. -/
theorem occupation_pushParabolicFamily_composition {d : ℕ} (Φ : KineticAffineScaling d)
    (Q : ParabolicOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hQ : ∀ σ r τ hσr hrτ, Q σ τ (hσr.trans hrτ) =
      (Q σ r hσr).comp (Q r τ hrτ))
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) :
    occupation_pushParabolicFamily Φ Q σ τ (hσr.trans hrτ) =
      (occupation_pushParabolicFamily Φ Q σ r hσr).comp
        (occupation_pushParabolicFamily Φ Q r τ hrτ) := by
  ext f y
  have hcancel (g : BoundedBorel
      (EvolutionPosition (wholeSpace d) (fun _ => 0) (Φ.time r))) :
      occupation_borelComap (occupation_positionEquiv Φ r).symm
        (occupation_positionEquiv Φ r).symm.measurable
        (occupation_borelComap (occupation_positionEquiv Φ r)
          (occupation_positionEquiv Φ r).measurable g) = g := by
    ext x
    exact congrArg g ((occupation_positionEquiv Φ r).apply_symm_apply x)
  simp only [occupation_pushParabolicFamily, LinearMap.comp_apply,
    occupation_borelComap_apply]
  rw [show Q (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr (hσr.trans hrτ)) =
      (Q (Φ.time σ) (Φ.time r) (Φ.time_le_iff.mpr hσr)).comp
        (Q (Φ.time r) (Φ.time τ) (Φ.time_le_iff.mpr hrτ)) from hQ _ _ _ _ _]
  simp
  rw [hcancel]


/-- The first marginal of the pushed kernel is the inverse velocity affine image. -/
theorem firstMarginal_pushKernel {d : ℕ} (Φ : KineticAffineScaling d)
    {Ω Ω' : Set (PDE.Vec d)} {γ γ' : ℝ → PDE.Vec d}
    (h : Φ.MapsDomain Ω γ Ω' γ') (K : MovingFiberKernel Ω γ)
    (q : EvolutionQuery Ω' γ') :
    (KineticAffineScaling.pushKernel h K).firstMarginal q =
      (K.firstMarginal (KineticAffineScaling.queryMap h q)).map Φ.positionInv := by
  rw [MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply,
    KineticAffineScaling.pushKernel_master_apply,
    Measure.map_map measurable_fst (Φ.ambientEquiv q.1.2.1).symm.measurable]
  rw [MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply,
    Measure.map_map Φ.continuous_positionInv.measurable measurable_fst]
  rfl

/-- Radius transport on a whole-space query starting at scaled time zero. -/
theorem firstMarginal_radius_query {d : ℕ} (σ₀ : ℝ) (r : {r : ℝ // 0 < r})
    (K : MovingFiberKernel (SectionTwo.wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (t : ℝ) (ht : 0 ≤ t) (v : PDE.Vec d) :
    let Φ := KineticAffineScaling.ofRadius σ₀ 0 0 (SectionTwo.identityDrift d) r
    (KineticAffineScaling.pushKernel
      (KineticAffineScaling.mapsDomain_wholeSpace Φ) K).firstMarginal
        (SectionTwo.wholeSpaceQuery 0 t ht v 0) =
      (K.firstMarginal (SectionTwo.wholeSpaceQuery σ₀ (σ₀ + r.1 ^ 2 * t)
        (le_add_of_nonneg_right (mul_nonneg (sq_nonneg r.1) ht)) (r.1 • v) 0)).map
          (fun w => r.1⁻¹ • w) := by
  unfold SectionTwo.wholeSpace at K ⊢
  let Φ := KineticAffineScaling.ofRadius σ₀ 0 0 (SectionTwo.identityDrift d) r
  refine (firstMarginal_pushKernel Φ (KineticAffineScaling.mapsDomain_wholeSpace Φ) K (SectionTwo.wholeSpaceQuery 0 t ht v 0)).trans ?_
  congr 1
  · funext w
    simp [Φ, KineticAffineScaling.positionInv, KineticAffineScaling.ofRadius]
  · congr 1
    apply Subtype.ext
    simp [Φ, KineticAffineScaling.queryMap, KineticAffineScaling.rawQuery,
      KineticAffineScaling.ofRadius, KineticAffineScaling.time,
      KineticAffineScaling.position,
      KineticAffineScaling.transport, SectionTwo.wholeSpaceQuery]

/-- The original parabolic bundle makes the master velocity marginal position independent. -/
theorem firstMarginal_independent_position {d : ℕ} {B : CoefficientField d}
    (K : MovingFiberKernel (SectionTwo.wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hP : SectionTwo.HasParabolicMarginalBundle (SectionTwo.wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z z' : PDE.Vec d) :
    K.firstMarginal (SectionTwo.wholeSpaceQuery σ τ hστ v z) =
      K.firstMarginal (SectionTwo.wholeSpaceQuery σ τ hστ v z') := by
  obtain ⟨_Q, h1, -, -, -, -, -, -, -, -, -⟩ := hP (fun _ _ _ _ => rfl)
  let y : EvolutionPosition (SectionTwo.wholeSpace d) (fun _ => 0) σ :=
    ⟨v, by simp [SectionTwo.movingDomain_wholeSpace]⟩
  have hsame := (h1 σ τ hστ y z).symm.trans (h1 σ τ hστ y z')
  have hh := congrArg
    (Measure.map ((↑) : EvolutionPosition (SectionTwo.wholeSpace d)
      (fun _ => 0) τ → PDE.Vec d)) hsame
  have hz' := MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal K
    MeasurableSet.univ σ τ hστ
    (evolutionStateOfPosition (SectionTwo.wholeSpace d) (fun _ => 0) σ y z')
  exact (MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal K MeasurableSet.univ σ τ hστ (evolutionStateOfPosition (SectionTwo.wholeSpace d) (fun _ => 0) σ y z)).symm.trans (hh.trans hz')

/-- The scaled scalar marginal is conjugate by the fixed-time position equivalences. -/
theorem occupation_parabolicMarginal_conjugate {d : ℕ} {B : CoefficientField d}
    (Φ : KineticAffineScaling d)
    (K : MovingFiberKernel (SectionTwo.wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hP : SectionTwo.HasParabolicMarginalBundle (SectionTwo.wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ)
    (y : EvolutionPosition (SectionTwo.wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ) :
    let Kt := KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace Φ) K
    parabolicMarginalKernel Kt MeasurableSet.univ σ τ hστ y =
      (parabolicMarginalKernel K MeasurableSet.univ (Φ.time σ) (Φ.time τ)
        (Φ.time_le_iff.mpr hστ) (occupation_positionEquiv Φ σ y)).map
          (occupation_positionEquiv Φ τ).symm := by
  apply ((SectionTwo.wholeSpacePositionEquiv d τ).measurableEmbedding).map_injective
  have ht := MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal (KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace Φ) K)
    MeasurableSet.univ σ τ hστ
    (positionStateZero (SectionTwo.wholeSpace d) (fun _ => 0) σ y)
  have hp := firstMarginal_pushKernel Φ (KineticAffineScaling.mapsDomain_wholeSpace Φ)
    K (evolutionQueryOfState (SectionTwo.wholeSpace d) (fun _ => 0) σ τ hστ
      (positionStateZero (SectionTwo.wholeSpace d) (fun _ => 0) σ y))
  have hquery : KineticAffineScaling.queryMap (KineticAffineScaling.mapsDomain_wholeSpace Φ)
      (evolutionQueryOfState (SectionTwo.wholeSpace d) (fun _ => 0) σ τ hστ
        (positionStateZero (SectionTwo.wholeSpace d) (fun _ => 0) σ y)) =
      SectionTwo.wholeSpaceQuery (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ)
        (Φ.position y.1) (Φ.transport σ 0) := by
    apply Subtype.ext
    rfl
  rw [hquery] at hp
  have hp2 := hp.trans (congrArg (Measure.map Φ.positionInv) (firstMarginal_independent_position K hP (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ) (Φ.position y.1) (Φ.transport σ 0) 0))
  have hrhs : Measure.map Subtype.val
      ((parabolicMarginalKernel K MeasurableSet.univ (Φ.time σ) (Φ.time τ)
        (Φ.time_le_iff.mpr hστ) (occupation_positionEquiv Φ σ y)).map
          (occupation_positionEquiv Φ τ).symm) =
      Measure.map Φ.positionInv (Measure.map Subtype.val
        (parabolicMarginalKernel K MeasurableSet.univ (Φ.time σ) (Φ.time τ)
          (Φ.time_le_iff.mpr hστ) (occupation_positionEquiv Φ σ y))) := by
    rw [Measure.map_map measurable_subtype_coe
      (occupation_positionEquiv Φ τ).symm.measurable,
      Measure.map_map Φ.continuous_positionInv.measurable measurable_subtype_coe]
    rfl
  have hh := congrArg (Measure.map Φ.positionInv) (MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal K MeasurableSet.univ (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ) (positionStateZero (SectionTwo.wholeSpace d) (fun _ => 0) (Φ.time σ) (occupation_positionEquiv Φ σ y)))
  exact ht.trans (hp2.trans (hh.symm.trans hrhs.symm))

/-- Position independence survives the constructed affine kernel pushforward. -/
theorem occupation_scaled_firstMarginal_independent {d : ℕ} {B : CoefficientField d}
    (Φ : KineticAffineScaling d)
    (K : MovingFiberKernel (SectionTwo.wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hP : SectionTwo.HasParabolicMarginalBundle (SectionTwo.wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z z' : PDE.Vec d) :
    let Kt := KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace Φ) K
    Kt.firstMarginal (SectionTwo.wholeSpaceQuery σ τ hστ v z) =
      Kt.firstMarginal (SectionTwo.wholeSpaceQuery σ τ hστ v z') := by
  have hq (w : PDE.Vec d) :
      KineticAffineScaling.queryMap (KineticAffineScaling.mapsDomain_wholeSpace Φ)
        (SectionTwo.wholeSpaceQuery σ τ hστ v w) =
      SectionTwo.wholeSpaceQuery (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ)
        (Φ.position v) (Φ.transport σ w) := by
    apply Subtype.ext
    rfl
  have hp := firstMarginal_pushKernel Φ (KineticAffineScaling.mapsDomain_wholeSpace Φ)
    K (SectionTwo.wholeSpaceQuery σ τ hστ v z)
  have hp' := firstMarginal_pushKernel Φ (KineticAffineScaling.mapsDomain_wholeSpace Φ)
    K (SectionTwo.wholeSpaceQuery σ τ hστ v z')
  rw [hq] at hp hp'
  exact hp.trans ((congrArg (Measure.map Φ.positionInv) (firstMarginal_independent_position K hP (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ) (Φ.position v) (Φ.transport σ z) (Φ.transport σ z'))).trans hp'.symm)

/-- Equality of the scaled scalar kernel with the constructed kernel conjugation. -/
theorem occupation_parabolicKernel_conjugate {d : ℕ} {B : CoefficientField d}
    (Φ : KineticAffineScaling d)
    (K : MovingFiberKernel (SectionTwo.wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hP : SectionTwo.HasParabolicMarginalBundle (SectionTwo.wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ) :
    parabolicMarginalKernel
      (KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace Φ) K)
      MeasurableSet.univ σ τ hστ =
    kernelConj (occupation_positionEquiv Φ σ) (occupation_positionEquiv Φ τ)
      (parabolicMarginalKernel K MeasurableSet.univ (Φ.time σ) (Φ.time τ)
        (Φ.time_le_iff.mpr hστ)) := by
  ext y : 1
  exact (occupation_parabolicMarginal_conjugate Φ K hP σ τ hστ y).trans
    (kernelConj_apply (occupation_positionEquiv Φ σ) (occupation_positionEquiv Φ τ)
      (parabolicMarginalKernel K MeasurableSet.univ (Φ.time σ) (Φ.time τ)
        (Φ.time_le_iff.mpr hστ)) y).symm

/-- The ambient scalar marginal is a measurable-query evaluation of the master marginal. -/
theorem occupation_parabolicMarginalAmbient_eq {d : ℕ}
    (K : MovingFiberKernel (SectionTwo.wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (q : ParabolicEvolutionQuery (SectionTwo.wholeSpace d) (fun _ => (0 : PDE.Vec d))) :
    parabolicMarginalAmbientMeasure K MeasurableSet.univ q =
      K.firstMarginal (SectionTwo.wholeSpaceQuery q.1.1 q.1.2.1 q.2.1 q.1.2.2 0) := by
  exact MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal K MeasurableSet.univ
    q.1.1 q.1.2.1 q.2.1
    (positionStateZero (SectionTwo.wholeSpace d) (fun _ => 0) q.1.1 (parabolicQuerySource q))

/-- Joint measurable-set evaluation for every whole-space scalar marginal. -/
theorem occupation_parabolicMarginal_measurable {d : ℕ}
    (K : MovingFiberKernel (SectionTwo.wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (E : Set (PDE.Vec d)) (hE : MeasurableSet E) :
    Measurable (fun q : ParabolicEvolutionQuery (SectionTwo.wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) => parabolicMarginalAmbientMeasure K MeasurableSet.univ q E) := by
  have hq : Measurable (fun q : ParabolicEvolutionQuery (SectionTwo.wholeSpace d)
      (fun _ => 0) =>
      SectionTwo.wholeSpaceQuery q.1.1 q.1.2.1 q.2.1 q.1.2.2 0) := by
    apply Measurable.subtype_mk
    fun_prop
  convert ((ProbabilityTheory.Kernel.measurable_coe K.firstMarginal hE).comp hq) using 1
  funext q
  exact congrArg (fun μ : Measure (PDE.Vec d) => μ E)
    (occupation_parabolicMarginalAmbient_eq K q)


/-- Restricted volume under the parabolic affine change of variables. -/
theorem occupation_map_restrict_parabolicAffine {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d)
    {r : ℝ} (hr : 0 < r) (s : Set (TimeVelocity d)) :
    Measure.map (parabolicAffine t₀ v₀ r) (volume.restrict s) =
      ENNReal.ofReal ((r ^ (d + 2))⁻¹) •
        volume.restrict (parabolicAffine t₀ v₀ r '' s) := by
  have hp : parabolicAffine t₀ v₀ r ⁻¹' (parabolicAffine t₀ v₀ r '' s) = s :=
    preimage_image_eq _ (parabolicAffine_injective hr)
  calc
    _ = (Measure.map (parabolicAffine t₀ v₀ r) volume).restrict
        (parabolicAffine t₀ v₀ r '' s) := by
      have hh := ((parabolicAffine_measurableEmbedding (t₀ := t₀) (v₀ := v₀) hr).restrict_map volume (parabolicAffine t₀ v₀ r '' s)).symm
      simpa only [hp] using hh
    _ = _ := by rw [map_volume_parabolicAffine t₀ v₀ hr, Measure.restrict_smul]

/-- Pullback norm with a scalar prefactor, at every extended exponent. -/
theorem occupation_eLpNorm_pullback {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d)
    {r : ℝ} (hr : 0 < r) (a : ℝ) (g : TimeVelocity d → ℝ)
    (p : ℝ≥0∞) (s : Set (TimeVelocity d)) :
    eLpNorm (fun z => a * g (parabolicAffine t₀ v₀ r z)) p (volume.restrict s) =
      ‖a‖ₑ * (ENNReal.ofReal ((r ^ (d + 2))⁻¹) ^ (1 / p).toReal) *
        eLpNorm g p (volume.restrict (parabolicAffine t₀ v₀ r '' s)) := by
  have hc : ENNReal.ofReal ((r ^ (d + 2))⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (pow_pos hr _))
  change eLpNorm (a • (g ∘ parabolicAffine t₀ v₀ r)) p (volume.restrict s) = _
  rw [eLpNorm_const_smul, ← (parabolicAffine_measurableEmbedding (t₀ := t₀) (v₀ := v₀) hr).eLpNorm_map_measure,
    occupation_map_restrict_parabolicAffine t₀ v₀ hr s,
    eLpNorm_smul_measure_of_ne_zero hc]
  simp [mul_assoc]

/-- Inverse parabolic dilation carries the length-T open slab onto the unit slab. -/
theorem occupation_inverseScaling_image_slab {d : ℕ} {T : ℝ} (hT : 0 < T) :
    parabolicAffine 0 (0 : PDE.Vec d) (Real.sqrt T)⁻¹ ''
      (Ioo (0 : ℝ) T ×ˢ univ) = Ioo (0 : ℝ) 1 ×ˢ univ := by
  have hs := Real.sq_sqrt hT.le
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    change (0 < 0 + (Real.sqrt T)⁻¹ ^ 2 * z.1 ∧
      0 + (Real.sqrt T)⁻¹ ^ 2 * z.1 < 1) ∧ _
    rw [inv_pow, hs]
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · simpa using mul_pos (inv_pos.mpr hT) hz.1.1
    · simpa [inv_mul_eq_div] using (div_lt_one hT).mpr hz.1.2
  · intro hq
    refine ⟨(T * q.1, Real.sqrt T • q.2), ?_, ?_⟩
    · exact ⟨⟨mul_pos hT hq.1.1, by nlinarith only [hq.1.2, hT]⟩, mem_univ _⟩
    · apply Prod.ext
      · change 0 + (Real.sqrt T)⁻¹ ^ 2 * (T * q.1) = q.1
        rw [inv_pow, hs]
        field_simp
        simp
      · ext j
        change 0 + (Real.sqrt T)⁻¹ * (Real.sqrt T * q.2 j) = q.2 j
        field_simp
        simp

/-- The scalar determinant factor is exactly the source time exponent. -/
theorem occupation_scaling_factor {d : ℕ} {T γ : ℝ} (hT : 0 < T) :
    T ^ (-(d : ℝ) / 2) *
      (((Real.sqrt T)⁻¹ ^ (d + 2))⁻¹) ^ (1 / γ) =
        T ^ occupationBeta d γ := by
  rw [inv_pow, inv_inv, ← Real.rpow_natCast, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le, ← Real.rpow_add hT]
  congr 1
  unfold occupationBeta
  push_cast
  ring

/-- The real norm of the constructed scaled density has the exact source factor. -/
theorem occupationLpNorm_scaledDensity {d : ℕ} {T γ : ℝ} (hT : 0 < T)
    (hγ : 0 ≤ γ) (g : TimeVelocity d → ℝ) :
    occupationLpNorm T γ
      (fun q => T ^ (-(d : ℝ) / 2) * g (q.1 / T, (Real.sqrt T)⁻¹ • q.2)) =
        T ^ occupationBeta d γ * occupationLpNorm 1 γ g := by
  have hs := Real.sqrt_pos.mpr hT
  have hf : (fun q =>
      T ^ (-(d : ℝ) / 2) * g (q.1 / T, (Real.sqrt T)⁻¹ • q.2)) =
      fun q => T ^ (-(d : ℝ) / 2) *
        g (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q) := by
    funext q
    congr 2
    apply Prod.ext
    · change q.1 / T = 0 + (Real.sqrt T)⁻¹ ^ 2 * q.1
      rw [inv_pow, (Real.sq_sqrt hT.le)]
      simp [inv_mul_eq_div]
    · simp [parabolicAffine]
  unfold occupationLpNorm
  rw [hf, occupation_eLpNorm_pullback 0 0 (inv_pos.mpr hs),
    occupation_inverseScaling_image_slab hT, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, Real.enorm_of_nonneg (Real.rpow_nonneg hT.le _),
    ENNReal.toReal_ofReal (Real.rpow_nonneg hT.le _),
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (inv_nonneg.mpr hs.le) _)),
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofReal hγ,
    occupation_scaling_factor hT]

/-- Parabolic pullback with a finite prefactor preserves finite extended norms. -/
theorem occupation_memLp_pullback {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d)
    {r : ℝ} (hr : 0 < r) (a : ℝ) (g : TimeVelocity d → ℝ)
    (p : ℝ≥0∞) (s : Set (TimeVelocity d))
    (hg : MemLp g p (volume.restrict (parabolicAffine t₀ v₀ r '' s))) :
    MemLp (fun z => a * g (parabolicAffine t₀ v₀ r z)) p (volume.restrict s) := by
  change eLpNorm _ _ _ < ⊤
  rw [occupation_eLpNorm_pullback t₀ v₀ hr]
  apply ENNReal.mul_lt_top
  · apply ENNReal.mul_lt_top enorm_lt_top
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  · exact hg



/-- Elapsed-time pairing is the ordinary open-interval pairing with the marginal kernel. -/
theorem occupation_rhs_interval {d : ℕ} (K : WholeKernel d) (σ T : ℝ) (hT : 0 < T)
    (ρ : Measure (PDE.Vec d)) (φ : TimeVelocity d → ℝ) :
    (∫ v, ∫ τ : ElapsedTime (ENNReal.ofReal T),
      ∫ w, φ (τ.1, w) ∂K.firstMarginal
        (wholeSpaceQuery σ (σ + τ.1) (le_add_of_nonneg_right τ.2.1.le) v 0)
      ∂elapsedVolume (ENNReal.ofReal T) ∂ρ) =
    ∫ v, (∫ t in Ioo 0 T, ∫ w, φ (t, w) ∂Green.occupationKernel K σ t v) ∂ρ := by
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun v => ?_
  dsimp only
  rw [← (Green.integral_elapsed_finite T hT (fun t => ∫ w, φ (t, w) ∂Green.occupationKernel K σ t v))]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun τ => ?_
  dsimp only
  rw [Green.occupationKernel_of_nonneg K σ τ.1 τ.2.1.le v]



/-- A unit-time density for the constructed pushforward yields the original slab density. -/
theorem isOccupationDensity_scaled {d : ℕ} (K : WholeKernel d) (σ₀ : ℝ)
    {T : ℝ} (hT : 0 < T) (ρ : Measure (PDE.Vec d)) (gt : TimeVelocity d → ℝ)
    (hgt : IsOccupationDensity
      (KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace
        (KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d)
          ⟨Real.sqrt T, Real.sqrt_pos.mpr hT⟩)) K) 0 1
      (ρ.map (fun v => (Real.sqrt T)⁻¹ • v)) gt) :
    IsOccupationDensity K σ₀ T ρ
      (fun q => T ^ (-(d : ℝ) / 2) *
        gt (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q))    := by
  let occupation_scaledTest (φ : BoundedBorel (TimeVelocity d)) : BoundedBorel (TimeVelocity d) :=
    ⟨fun q => φ (parabolicAffine 0 0 (Real.sqrt T) q),
        φ.measurable.comp ((contDiff_infty_parabolicAffine 0 0 (Real.sqrt T)).continuous.measurable),
        by
          obtain ⟨C, hC, hb⟩ := φ.exists_bound
          exact ⟨C, hC, fun q => hb _⟩⟩
  have occupation_rhs_scaled (σ₀ : ℝ) {T : ℝ} (hT : 0 < T) (ρ : Measure (PDE.Vec d)) (φ : TimeVelocity d → ℝ) :
      let r : {r : ℝ // 0 < r} := ⟨Real.sqrt T, Real.sqrt_pos.mpr hT⟩
    let Φ := KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r
    let Kt := KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace Φ) K
    (∫ v, (∫ t in Ioo 0 1,
      ∫ w, φ (parabolicAffine 0 0 (Real.sqrt T) (t, w))
        ∂Green.occupationKernel Kt 0 t v) ∂ρ.map (fun v => (Real.sqrt T)⁻¹ • v)) =
      T⁻¹ * ∫ v, (∫ t in Ioo 0 T,
        ∫ w, φ (t, w) ∂Green.occupationKernel K σ₀ t v) ∂ρ := by
    have occupation_integral_time_dilation (f : ℝ → ℝ) :
        ∫ t in Ioo 0 1, f (T * t) = T⁻¹ * ∫ t in Ioo 0 T, f t := by
      have occupation_map_timeVolume :
          Measure.map (fun t => T * t) (volume.restrict (Ioo 0 1)) =
          ENNReal.ofReal T⁻¹ • volume.restrict (Ioo 0 T) := by
        have he : MeasurableEmbedding (fun t => T * t) :=
          (Homeomorph.mulLeft₀ T hT.ne').measurableEmbedding
        have hp : (fun t : ℝ => T * t) ⁻¹' Ioo 0 T = Ioo 0 1 := by
          ext t
          simp
          constructor
          · intro ht
            exact ⟨(mul_pos_iff_of_pos_left hT).mp ht.1, by nlinarith only [ht.2, hT]⟩
          · intro ht
            exact ⟨mul_pos hT ht.1, by nlinarith only [ht.2, hT]⟩
        calc
          _ = (Measure.map (fun t : ℝ => T * t) volume).restrict (Ioo 0 T) := by
            have hh := (he.restrict_map volume (Ioo 0 T)).symm
            simpa only [hp] using hh
          _ = _ := by
            rw [Real.map_volume_mul_left hT.ne', abs_of_pos (inv_pos.mpr hT),
              Measure.restrict_smul]
      have he : MeasurableEmbedding (fun t => T * t) :=
        (Homeomorph.mulLeft₀ T hT.ne').measurableEmbedding
      rw [← he.integral_map, occupation_map_timeVolume, integral_smul_measure,
        ENNReal.toReal_ofReal (inv_pos.mpr hT).le, smul_eq_mul]
    dsimp only
    let r : {r : ℝ // 0 < r} := ⟨Real.sqrt T, Real.sqrt_pos.mpr hT⟩
    let Φ := KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r
    let Kt := KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace Φ) K
    have hs := (Real.sqrt_pos.mpr hT).ne'
    have hsq := Real.sq_sqrt hT.le
    have he : MeasurableEmbedding (fun v : PDE.Vec d => (Real.sqrt T)⁻¹ • v) :=
      (Homeomorph.smulOfNeZero (Real.sqrt T)⁻¹ (inv_ne_zero hs)).measurableEmbedding
    rw [he.integral_map, ← integral_const_mul]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun v => ?_
    dsimp only
    rw [← occupation_integral_time_dilation]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hkernel := firstMarginal_radius_query σ₀ r K t ht.1.le
      ((Real.sqrt T)⁻¹ • v)
    have hcancel : r.1 • ((Real.sqrt T)⁻¹ • v) = v := by
      rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
    have hKT : Green.occupationKernel Kt 0 t ((Real.sqrt T)⁻¹ • v) =
        (Green.occupationKernel K σ₀ (T * t) v).map
          (fun w => (Real.sqrt T)⁻¹ • w) := by
      rw [Green.occupationKernel_of_nonneg Kt 0 t ht.1.le]
      change (KineticAffineScaling.pushKernel
        (KineticAffineScaling.mapsDomain_wholeSpace Φ) K).firstMarginal _ = _
      dsimp only at hkernel
      rw [hcancel] at hkernel
      have hh := Green.occupationKernel_of_nonneg K σ₀
        (T * t) (mul_nonneg hT.le ht.1.le) v
      simpa [r, hsq, hh] using hkernel
    rw [hKT, he.integral_map]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun w => ?_
    dsimp only
    congr 1
    apply Prod.ext
    · change 0 + (Real.sqrt T) ^ 2 * t = T * t
      rw [hsq, zero_add]
    · change 0 + Real.sqrt T • ((Real.sqrt T)⁻¹ • w) = w
      rw [zero_add, smul_smul, mul_inv_cancel₀ hs, one_smul]
  have occupation_scaledDensity_pairing (φ g : TimeVelocity d → ℝ) :
      ∫ q in Ioo 0 T ×ˢ univ,
      φ q * (T ^ (-(d : ℝ) / 2) *
        g (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q)) =
      T * ∫ q in Ioo 0 1 ×ˢ univ,
        φ (parabolicAffine 0 0 (Real.sqrt T) q) * g q := by
    have occupation_forward_inverse {d : ℕ} (q : TimeVelocity d) :
        parabolicAffine 0 0 (Real.sqrt T)
        (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q) = q := by
      have hs := (Real.sqrt_pos.mpr hT).ne'
      apply Prod.ext
      · change 0 + (Real.sqrt T) ^ 2 * (0 + (Real.sqrt T)⁻¹ ^ 2 * q.1) = q.1
        rw [inv_pow]
        field_simp
        simp
      · ext j
        change 0 + Real.sqrt T * (0 + (Real.sqrt T)⁻¹ * q.2 j) = q.2 j
        field_simp
        simp
    have occupation_integral_scaled_pullback {d : ℕ} (f : TimeVelocity d → ℝ) :
        ∫ q in Ioo 0 T ×ˢ univ,
        T ^ (-(d : ℝ) / 2) * f (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q) =
        T * ∫ q in Ioo 0 1 ×ˢ univ, f q := by
      have occupation_density_jacobian :
          T ^ (-(d : ℝ) / 2) * ((Real.sqrt T)⁻¹ ^ (d + 2))⁻¹ = T := by
        have hh := occupation_scaling_factor (d := d) (γ := 1) hT
        have hb : occupationBeta d 1 = 1 := by unfold occupationBeta; ring
        simpa [Real.rpow_one, hb] using hh
      have hs := Real.sqrt_pos.mpr hT
      rw [integral_const_mul, ← (parabolicAffine_measurableEmbedding (d := d) (t₀ := 0) (v₀ := 0) (inv_pos.mpr hs)).integral_map,
        occupation_map_restrict_parabolicAffine 0 0 (inv_pos.mpr hs),
        occupation_inverseScaling_image_slab hT, integral_smul_measure,
        ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (inv_nonneg.mpr hs.le) _)),
        smul_eq_mul, ← mul_assoc, occupation_density_jacobian]
    have hh := occupation_integral_scaled_pullback
      (fun q => φ (parabolicAffine 0 0 (Real.sqrt T) q) * g q)
    convert hh using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q => by
      dsimp only
      rw [occupation_forward_inverse]
      ring
  refine ⟨measurable_const.mul (hgt.1.comp
    ((contDiff_infty_parabolicAffine 0 0 (Real.sqrt T)⁻¹).continuous.measurable)),
    fun q => mul_nonneg (Real.rpow_nonneg hT.le _) (hgt.2.1 _), ?_⟩
  intro φ
  rw [occupation_scaledDensity_pairing]
  have hh := hgt.2.2 (occupation_scaledTest φ)
  change (∫ q in Ioo 0 1 ×ˢ univ,
    φ (parabolicAffine 0 0 (Real.sqrt T) q) * gt q) = _ at hh
  rw [hh, occupation_rhs_interval _ 0 1 zero_lt_one]
  change T * (∫ v, (∫ t in Ioo 0 1,
    ∫ w, φ (parabolicAffine 0 0 (Real.sqrt T) (t, w)) ∂_) ∂_) = _
  have hm := congrArg (fun a : ℝ => T * a) (occupation_rhs_scaled σ₀ hT ρ φ)
  rw [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul] at hm
  exact hm.trans (occupation_rhs_interval K σ₀ T hT ρ φ).symm



/-- The density characterization is exactly the slab consumer's predicate. -/
theorem isOccupationDensity_iff_slabOccupationDensity {d : ℕ} (K : WholeKernel d)
    (σ₀ T : ℝ) (ρ : Measure (PDE.Vec d)) (g : ℝ × PDE.Vec d → ℝ) :
    IsOccupationDensity K σ₀ T ρ g ↔ Green.SlabOccupationDensity K σ₀ T ρ g := by
  rfl



private theorem pastClosed_wholeSpace {d : ℕ} (τ : ℝ) :
    ParabolicProbe.scalarPastClosedCylinder (wholeSpace d) (fun _ => (0 : PDE.Vec d)) τ =
      {q : TimeVelocity d | q.1 ≤ τ} := by
  ext q
  simp [ParabolicProbe.scalarPastClosedCylinder, movingDomain_wholeSpace, closure_univ]

/-- Classical scalar solutions pull back by the literal source radius scaling. -/
theorem occupation_scalarTerminal_pullback {d : ℕ} (σ₀ τ : ℝ)
    (r : {r : ℝ // 0 < r}) (B : CoefficientField d)
    (F : BoundedBorel (PDE.Vec d)) (V : TimeVelocity d → ℝ)
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) (zIndependentCoefficient B) (σ₀ + r.1 ^ 2 * τ) F V) :
    ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
      (fun _ => (0 : PDE.Vec d))
      (zIndependentCoefficient (scaledCoefficient B σ₀ 0 r)) τ
      (occupation_borelComap (fun v => r.1 • v)
        (continuous_const_smul r.1).measurable F)
      (V ∘ parabolicAffine σ₀ 0 r.1)  := by
  have pastOpen_wholeSpace (τ : ℝ) :
      ParabolicProbe.scalarPastOpenCylinder (wholeSpace d) (fun _ => 0) τ =
      {q : TimeVelocity d | q.1 < τ} := by
    ext q
    simp [ParabolicProbe.scalarPastOpenCylinder, movingDomain_wholeSpace]
  have hmapO : MapsTo (parabolicAffine σ₀ 0 r.1)
      (ParabolicProbe.scalarPastOpenCylinder (wholeSpace d) (fun _ => 0) τ)
      (ParabolicProbe.scalarPastOpenCylinder (wholeSpace d) (fun _ => 0)
        (σ₀ + r.1 ^ 2 * τ)) := by
    intro q hq
    rw [pastOpen_wholeSpace] at hq ⊢
    change σ₀ + r.1 ^ 2 * q.1 < σ₀ + r.1 ^ 2 * τ
    simpa only [add_comm] using
      add_lt_add_left (mul_lt_mul_of_pos_left hq (sq_pos_of_pos r.2)) σ₀
  have hmapC : MapsTo (parabolicAffine σ₀ 0 r.1)
      (ParabolicProbe.scalarPastClosedCylinder (wholeSpace d) (fun _ => 0) τ)
      (ParabolicProbe.scalarPastClosedCylinder (wholeSpace d) (fun _ => 0)
        (σ₀ + r.1 ^ 2 * τ)) := by
    intro q hq
    rw [pastClosed_wholeSpace] at hq ⊢
    change σ₀ + r.1 ^ 2 * q.1 ≤ σ₀ + r.1 ^ 2 * τ
    simpa only [add_comm] using
      add_le_add_left (mul_le_mul_of_nonneg_left hq (sq_nonneg r.1)) σ₀
  have hopen : IsOpen (ParabolicProbe.scalarPastOpenCylinder (wholeSpace d)
      (fun _ => 0) (σ₀ + r.1 ^ 2 * τ)) := by
    rw [pastOpen_wholeSpace]
    exact isOpen_lt continuous_fst continuous_const
  obtain ⟨-, hjet⟩ := KrylovEstimate.scalarC12On_affine_pullback hopen V (isScalarC12On_of_isOpen_contDiffOn_two hopen (hV.2.2.1.of_le (by simp))) σ₀ 0 r.2
  refine ⟨?_, hV.2.1.comp
    (contDiff_infty_parabolicAffine σ₀ 0 r.1).continuous.continuousOn hmapC,
    hV.2.2.1.comp
      ((contDiff_infty_parabolicAffine σ₀ 0 r.1).of_le (by simp)).contDiffOn hmapO,
    ?_, ?_, ?_⟩
  · obtain ⟨C, hC, hb⟩ := hV.1
    exact ⟨C, hC, fun q hq => hb _ (hmapC hq)⟩
  · intro q hq
    obtain ⟨ht, hh⟩ := hjet q (hmapO hq)
    have he := hV.2.2.2.1 (parabolicAffine σ₀ 0 r.1 q) (hmapO hq)
    unfold scalarParabolicOperator at he ⊢
    rw [ht, hh, matrixContraction_smul_right]
    simp [PDE.vecDot] at he ⊢
    change r.1 ^ 2 * scalarTimeDerivative V (parabolicAffine σ₀ 0 r.1 q) +
      r.1 ^ 2 * matrixContraction (B (σ₀ + r.1 ^ 2 * q.1) (0 + r.1 • q.2))
        (scalarSpatialHessian V (parabolicAffine σ₀ 0 r.1 q)) = 0
    change scalarTimeDerivative V (parabolicAffine σ₀ 0 r.1 q) +
      matrixContraction (B (σ₀ + r.1 ^ 2 * q.1) (0 + r.1 • q.2))
        (scalarSpatialHessian V (parabolicAffine σ₀ 0 r.1 q)) = 0 at he
    rw [← mul_add, he, mul_zero]
  · intro q hq
    have hterm : parabolicAffine σ₀ 0 r.1 q ∈
        ParabolicProbe.scalarTerminalClosure (wholeSpace d) (fun _ => 0)
          (σ₀ + r.1 ^ 2 * τ) := by
      exact ⟨by change σ₀ + r.1 ^ 2 * q.1 = _; rw [hq.1],
        by simp [movingDomain_wholeSpace]⟩
    simpa [occupation_borelComap_apply, parabolicAffine] using (hV.2.2.2.2.1 _ hterm)
  · intro q hq
    have hf := hq.2
    simp only [movingDomain_wholeSpace, frontier_univ, mem_empty_iff_false] at hf

/-- Inverse-radius pullback preserves smooth compact scalar terminal data. -/
theorem occupation_scalarDatum_inverse {d : ℕ} (σ₀ τ : ℝ)
    (r : {r : ℝ // 0 < r}) (F : BoundedBorel (PDE.Vec d))
    (hF : ParabolicProbe.IsSmoothCompactScalarTerminalDatum (wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) τ F) :
    ParabolicProbe.IsSmoothCompactScalarTerminalDatum (wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) (σ₀ + r.1 ^ 2 * τ)
      (occupation_borelComap (fun v => r.1⁻¹ • v)
        (continuous_const_smul r.1⁻¹).measurable F) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hF.1.comp (by fun_prop)
  · have hc : HasCompactSupport (F : PDE.Vec d → ℝ) := hF.2.1
    exact hc.comp_homeomorph (Homeomorph.smulOfNeZero r.1⁻¹ (inv_ne_zero r.2.ne'))
  · intro v _
    simp [movingDomain_wholeSpace]

/-- Pulling the inverse datum back by the forward radius recovers the given datum. -/
theorem occupation_scalarDatum_cancel {d : ℕ} (r : {r : ℝ // 0 < r})
    (F : BoundedBorel (PDE.Vec d)) :
    occupation_borelComap (fun v => r.1 • v) (continuous_const_smul r.1).measurable
      (occupation_borelComap (fun v => r.1⁻¹ • v)
        (continuous_const_smul r.1⁻¹).measurable F) = F := by
  ext v
  simp [occupation_borelComap_apply, smul_smul, inv_mul_cancel₀ r.2.ne']

/-- Inverse radius and time origin undo coefficient rescaling. -/
theorem occupation_inverse_scaledCoefficient {d : ℕ} (σ₀ : ℝ)
    (r : {r : ℝ // 0 < r}) (B : CoefficientField d) :
    scaledCoefficient (scaledCoefficient B σ₀ 0 r) (-σ₀ / r.1 ^ 2) 0
      ⟨r.1⁻¹, inv_pos.mpr r.2⟩ = B := by
  funext σ v
  unfold scaledCoefficient
  congr 1
  · dsimp only
    rw [inv_pow]
    field_simp [r.2.ne']
    ring
  · simp [smul_smul, mul_inv_cancel₀ r.2.ne']

/-- The inverse time origin sends the original terminal time back to the scaled one. -/
theorem occupation_inverse_terminalTime (σ₀ τ : ℝ) (r : {r : ℝ // 0 < r}) :
    -σ₀ / r.1 ^ 2 + (r.1⁻¹) ^ 2 * (σ₀ + r.1 ^ 2 * τ) = τ := by
  rw [inv_pow]
  field_simp [r.2.ne']
  ring

/-- An arbitrary scaled classical solution pushes back to the original coefficient. -/
theorem occupation_scalarTerminal_inverse {d : ℕ} (σ₀ τ : ℝ)
    (r : {r : ℝ // 0 < r}) (B : CoefficientField d)
    (F : BoundedBorel (PDE.Vec d)) (W : TimeVelocity d → ℝ)
    (hW : ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
      (fun _ => (0 : PDE.Vec d))
      (zIndependentCoefficient (scaledCoefficient B σ₀ 0 r)) τ F W) :
    ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) (zIndependentCoefficient B) (σ₀ + r.1 ^ 2 * τ)
      (occupation_borelComap (fun v => r.1⁻¹ • v)
        (continuous_const_smul r.1⁻¹).measurable F)
      (W ∘ parabolicAffine (-σ₀ / r.1 ^ 2) 0 r.1⁻¹) := by
  have hW' : ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
      (fun _ => 0)
      (zIndependentCoefficient (scaledCoefficient B σ₀ 0 r))
      (-σ₀ / r.1 ^ 2 + (r.1⁻¹) ^ 2 * (σ₀ + r.1 ^ 2 * τ)) F W := by
    rw [(occupation_inverse_terminalTime σ₀ τ r)]
    exact hW
  have hh := occupation_scalarTerminal_pullback (-σ₀ / r.1 ^ 2)
    (σ₀ + r.1 ^ 2 * τ) ⟨r.1⁻¹, inv_pos.mpr r.2⟩
    (scaledCoefficient B σ₀ 0 r) F W hW'
  rw [occupation_inverse_scaledCoefficient] at hh
  exact hh

/-- Inverse spacetime radius scaling cancels the forward affine map. -/
theorem occupation_inverse_forward {d : ℕ} (σ₀ : ℝ) (r : {r : ℝ // 0 < r})
    (q : TimeVelocity d) :
    parabolicAffine (-σ₀ / r.1 ^ 2) 0 r.1⁻¹ (parabolicAffine σ₀ 0 r.1 q) = q := by
  apply Prod.ext
  · change -σ₀ / r.1 ^ 2 + r.1⁻¹ ^ 2 * (σ₀ + r.1 ^ 2 * q.1) = q.1
    exact occupation_inverse_terminalTime σ₀ q.1 r
  · ext j
    change 0 + r.1⁻¹ * (0 + r.1 * q.2 j) = q.2 j
    simp [← mul_assoc, inv_mul_cancel₀ r.2.ne']

/-- A scalar terminal existence and uniqueness clause transports with the same operator family. -/
theorem occupation_scalarTerminalClause_scale {d : ℕ} (σ₀ : ℝ)
    (r : {r : ℝ // 0 < r}) (B : CoefficientField d)
    (Q : ParabolicOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hQ : ∀ τ F, ParabolicProbe.IsSmoothCompactScalarTerminalDatum (wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) τ F →
      ∃ V : TimeVelocity d → ℝ,
        ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
          (fun _ => (0 : PDE.Vec d)) (zIndependentCoefficient B) τ F V ∧
        (∀ σ hστ y, V (σ, y.1) = Q σ τ hστ (terminalPositionDatum F) y) ∧
        (∀ W : TimeVelocity d → ℝ,
          ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
            (fun _ => (0 : PDE.Vec d)) (zIndependentCoefficient B) τ F W →
          EqOn W V (ParabolicProbe.scalarPastClosedCylinder (wholeSpace d)
            (fun _ => (0 : PDE.Vec d)) τ))) :
    ∀ τ F, ParabolicProbe.IsSmoothCompactScalarTerminalDatum (wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) τ F →
      ∃ V : TimeVelocity d → ℝ,
        ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
          (fun _ => (0 : PDE.Vec d))
          (zIndependentCoefficient (scaledCoefficient B σ₀ 0 r)) τ F V ∧
        (∀ σ hστ y, V (σ, y.1) =
          occupation_pushParabolicFamily
            (KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r) Q σ τ hστ
            (terminalPositionDatum F) y) ∧
        (∀ W : TimeVelocity d → ℝ,
          ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
            (fun _ => (0 : PDE.Vec d))
            (zIndependentCoefficient (scaledCoefficient B σ₀ 0 r)) τ F W →
          EqOn W V (ParabolicProbe.scalarPastClosedCylinder (wholeSpace d)
            (fun _ => (0 : PDE.Vec d)) τ)) := by
  intro τ F hF
  let F0 := occupation_borelComap (fun v => r.1⁻¹ • v)
    (continuous_const_smul r.1⁻¹).measurable F
  obtain ⟨V, hV, hVQ, huniq⟩ := hQ (σ₀ + r.1 ^ 2 * τ) F0
    (occupation_scalarDatum_inverse σ₀ τ r F hF)
  have hVt := occupation_scalarTerminal_pullback σ₀ τ r B F0 V hV
  rw [occupation_scalarDatum_cancel] at hVt
  refine ⟨V ∘ parabolicAffine σ₀ 0 r.1, hVt, ?_, ?_⟩
  · intro σ hστ y
    let Φ := KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r
    have hf : terminalPositionDatum (τ := σ₀ + r.1 ^ 2 * τ) F0 =
        occupation_borelComap (occupation_positionEquiv Φ τ).symm
          (occupation_positionEquiv Φ τ).symm.measurable (terminalPositionDatum F) := by
      ext x
      change F (r.1⁻¹ • x.1) = F (Φ.positionInv x.1)
      simp [Φ, KineticAffineScaling.positionInv, KineticAffineScaling.ofRadius]
    have hh := hVQ (Φ.time σ) (Φ.time_le_iff.mpr hστ) (occupation_positionEquiv Φ σ y)
    rw [hf] at hh
    exact hh
  · intro W hW q hq
    have heq := huniq (W ∘ parabolicAffine (-σ₀ / r.1 ^ 2) 0 r.1⁻¹) (occupation_scalarTerminal_inverse σ₀ τ r B F W hW)
      (show parabolicAffine σ₀ 0 r.1 q ∈
        ParabolicProbe.scalarPastClosedCylinder (wholeSpace d) (fun _ => 0)
          (σ₀ + r.1 ^ 2 * τ) from by
        rw [pastClosed_wholeSpace] at hq ⊢
        change σ₀ + r.1 ^ 2 * q.1 ≤ σ₀ + r.1 ^ 2 * τ
        linarith only [mul_le_mul_of_nonneg_left hq (sq_nonneg r.1)])
    simpa [occupation_inverse_forward] using heq


/-- The given parabolic marginal bundle transports directly to the constructed scaled kernel. -/
theorem occupation_scaled_marginalBundle {d : ℕ} (σ₀ : ℝ)
    (r : {r : ℝ // 0 < r}) {B : CoefficientField d}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient B) K) :
    HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient (scaledCoefficient B σ₀ 0 r))
      (KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace
        (KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r)) K) := by
  intro _hBz
  obtain ⟨Q, -, h2, h3, h4, h5, h6, -, h8, h9, h10⟩ := hP (fun _ _ _ _ => rfl)
  let Φ := KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r
  let Kt := KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace Φ) K
  refine ⟨occupation_pushParabolicFamily Φ Q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ τ hστ y z
    apply (wholeSpacePositionEquiv d τ).measurableEmbedding.map_injective
    have hi := occupation_scaled_firstMarginal_independent Φ K hP σ τ hστ y.1 0 z
    exact (MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal Kt MeasurableSet.univ σ τ hστ (positionStateZero (wholeSpace d) (fun _ => 0) σ y)).trans (hi.trans (MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal Kt MeasurableSet.univ σ τ hστ (evolutionStateOfPosition (wholeSpace d) (fun _ => 0) σ y z)).symm)
  · exact occupation_pushParabolicFamily_endpoint Φ Q h2
  · exact occupation_pushParabolicFamily_positive Φ Q h3
  · exact occupation_pushParabolicFamily_contraction Φ Q h4
  · exact occupation_pushParabolicFamily_composition Φ Q h5
  · intro σ τ hστ y f
    let eσ := occupation_positionEquiv Φ σ
    let eτ := occupation_positionEquiv Φ τ
    have heval := h6 (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ) (eσ y) (occupation_borelComap eτ.symm eτ.symm.measurable f)
    have hc := occupation_parabolicMarginal_conjugate Φ K hP σ τ hστ y
    exact heval.trans ((congrArg (fun μ => ∫ x, f x ∂μ) hc).trans (eτ.symm.measurableEmbedding.integral_map (fun x => f x) (μ := parabolicMarginalKernel K MeasurableSet.univ (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ) (eσ y)))).symm
  · exact occupation_parabolicMarginal_measurable Kt
  · intro σ
    have hc := occupation_parabolicKernel_conjugate Φ K hP σ σ le_rfl
    exact hc.trans ((congrArg (kernelConj (occupation_positionEquiv Φ σ) (occupation_positionEquiv Φ σ)) (h8 (Φ.time σ))).trans (kernelConj_id (occupation_positionEquiv Φ σ)))
  · intro σ s τ hσs hsτ
    exact (occupation_parabolicKernel_conjugate Φ K hP σ τ (hσs.trans hsτ)).trans ((congrArg (kernelConj (occupation_positionEquiv Φ σ) (occupation_positionEquiv Φ τ)) (h9 (Φ.time σ) (Φ.time s) (Φ.time τ) (Φ.time_le_iff.mpr hσs) (Φ.time_le_iff.mpr hsτ))).trans ((kernelConj_comp (occupation_positionEquiv Φ σ) (occupation_positionEquiv Φ s) (occupation_positionEquiv Φ τ) (parabolicMarginalKernel K MeasurableSet.univ (Φ.time σ) (Φ.time s) (Φ.time_le_iff.mpr hσs)) (parabolicMarginalKernel K MeasurableSet.univ (Φ.time s) (Φ.time τ) (Φ.time_le_iff.mpr hsτ))).trans
      (congrArg₂ (fun A B => A ∘ₖ B) (occupation_parabolicKernel_conjugate Φ K hP s τ hsτ).symm (occupation_parabolicKernel_conjugate Φ K hP σ s hσs).symm)))
  · exact occupation_scalarTerminalClause_scale σ₀ r B Q h10

variable {d : ℕ}


/-- The whole-space occupation theorem with all its original premises. -/
theorem occupation
    (hH : HormanderHypoellipticityStatement)
    (hd : 0 < d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ → ℝ,
      (∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d → 0 ≤ C γ) ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ]
        (σ₀ T : ℝ) (_hT : 0 < T),
        ∃ g : TimeVelocity d → ℝ, IsOccupationDensity K σ₀ T ρ g ∧
          ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
            MemLp g (ENNReal.ofReal γ)
              (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) ∧
            occupationLpNorm T γ g ≤
              C γ * (ρ univ).toReal * T ^ occupationBeta d γ   := by
  have occupation_of_duality (hDuality :
    ∃ C : ℝ → ℝ,
      (∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d → 0 ≤ C γ) ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0)
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => 0)
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ],
        ∃ g : TimeVelocity d → ℝ, IsOccupationDensity K 0 1 ρ g ∧
          ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
            MemLp g (ENNReal.ofReal γ)
              (volume.restrict (Ioo 0 1 ×ˢ univ)) ∧
            occupationLpNorm 1 γ g ≤ C γ * (ρ univ).toReal) :
      ∃ C : ℝ → ℝ,
      (∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d → 0 ≤ C γ) ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0)
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => 0)
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ]
        (σ₀ T : ℝ) (_hT : 0 < T),
        ∃ g : TimeVelocity d → ℝ, IsOccupationDensity K σ₀ T ρ g ∧
          ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
            MemLp g (ENNReal.ofReal γ)
              (volume.restrict (Ioo 0 T ×ˢ univ)) ∧
            occupationLpNorm T γ g ≤
              C γ * (ρ univ).toReal * T ^ occupationBeta d γ := by
    have occupation_scaling_of_duality (hDuality :
      ∃ C : ℝ → ℝ,
        (∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d → 0 ≤ C γ) ∧
        ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
          (S : WholeFamily d) (K : WholeKernel d)
          (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0)
            MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
          (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => 0)
            MeasurableSet.univ (zIndependentCoefficient B) K)
          (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ],
          ∃ g : TimeVelocity d → ℝ, IsOccupationDensity K 0 1 ρ g ∧
            ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
              MemLp g (ENNReal.ofReal γ)
                (volume.restrict (Ioo 0 1 ×ˢ univ)) ∧
              occupationLpNorm 1 γ g ≤ C γ * (ρ univ).toReal ) :
        ∃ C : ℝ → ℝ,
        (∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d → 0 ≤ C γ) ∧
        ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
          (S : WholeFamily d) (K : WholeKernel d)
          (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0)
            MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
          (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => 0)
            MeasurableSet.univ (zIndependentCoefficient B) K)
          (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ]
          (σ₀ T : ℝ) (hT : 0 < T),
          let r : {r : ℝ // 0 < r} := ⟨Real.sqrt T, Real.sqrt_pos.2 hT⟩
          let Φ := Scaling.KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r
          let ρtilde := ρ.map (fun v => (Real.sqrt T)⁻¹ • v)
          ∃ (g gtilde : TimeVelocity d → ℝ),
            IsOccupationDensity K σ₀ T ρ g ∧
            IsOccupationDensity (Scaling.KineticAffineScaling.pushKernel (Scaling.KineticAffineScaling.mapsDomain_wholeSpace Φ) K) 0 1 ρtilde gtilde ∧
            (∀ q, g q = T ^ (-(d : ℝ) / 2) *
              gtilde (q.1 / T, (Real.sqrt T)⁻¹ • q.2)) ∧
            ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
              MemLp g (ENNReal.ofReal γ)
                (volume.restrict (Ioo 0 T ×ˢ univ)) ∧
              MemLp gtilde (ENNReal.ofReal γ)
                (volume.restrict (Ioo 0 1 ×ˢ univ)) ∧
              occupationLpNorm T γ g =
                T ^ occupationBeta d γ * occupationLpNorm 1 γ gtilde ∧
              occupationLpNorm T γ g ≤
                C γ * (ρ univ).toReal * T ^ occupationBeta d γ := by
      obtain ⟨C, hC0, hunit⟩ := hDuality
      refine ⟨C, hC0, ?_⟩
      intro B hB S K hreal hP ρ _ σ₀ T hT
      dsimp only
      let r : {r : ℝ // 0 < r} := ⟨Real.sqrt T, Real.sqrt_pos.mpr hT⟩
      let Φ := Scaling.KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r
      let Kt := Scaling.KineticAffineScaling.pushKernel
        (Scaling.KineticAffineScaling.mapsDomain_wholeSpace Φ) K
      let ρt := ρ.map (fun v => (Real.sqrt T)⁻¹ • v)
      obtain ⟨gt, hgt, hnorm⟩ := hunit (scaledCoefficient B σ₀ 0 r) (scaledCoefficient_sectionTwo lam Lam B hB σ₀ 0 r)
        (Scaling.fiberOperator Kt MeasurableSet.univ) Kt (Scaling.realizes_ofRadius_wholeSpace σ₀ 0 0 r hreal) (occupation_scaled_marginalBundle σ₀ r K hP) ρt
      let g := fun q => T ^ (-(d : ℝ) / 2) *
        gt (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q)
      have hg := isOccupationDensity_scaled K σ₀ hT ρ gt hgt
      have hgeq : ∀ q, g q = T ^ (-(d : ℝ) / 2) *
          gt (q.1 / T, (Real.sqrt T)⁻¹ • q.2) := by
        intro q
        dsimp [g]
        congr 2
        apply Prod.ext
        · change 0 + (Real.sqrt T)⁻¹ ^ 2 * q.1 = q.1 / T
          rw [inv_pow, Real.sq_sqrt hT.le]
          simp [inv_mul_eq_div]
        · simp [parabolicAffine]
      refine ⟨g, gt, hg, hgt, hgeq, ?_⟩
      intro γ hγ0 hγ1
      obtain ⟨hmem, hbd⟩ := hnorm γ hγ0 hγ1
      have hmemg : MemLp g (ENNReal.ofReal γ)
          (volume.restrict (Ioo 0 T ×ˢ univ)) := by
        apply occupation_memLp_pullback 0 0 (inv_pos.mpr (Real.sqrt_pos.mpr hT))
        simpa only [occupation_inverseScaling_image_slab hT] using hmem
      have hnormeq : occupationLpNorm T γ g =
          T ^ occupationBeta d γ * occupationLpNorm 1 γ gt := by
        rw [show g = fun q => T ^ (-(d : ℝ) / 2) *
          gt (q.1 / T, (Real.sqrt T)⁻¹ • q.2) from funext hgeq]
        exact occupationLpNorm_scaledDensity hT (zero_le_one.trans hγ0) gt
      have hmass : (ρt univ).toReal = (ρ univ).toReal := by
        have hm : Measurable (fun v : PDE.Vec d => (Real.sqrt T)⁻¹ • v) :=
          (continuous_const_smul (Real.sqrt T)⁻¹).measurable
        change (ρ.map (fun v => (Real.sqrt T)⁻¹ • v) univ).toReal = _
        rw [Measure.map_apply hm MeasurableSet.univ, preimage_univ]
      refine ⟨hmemg, hmem, hnormeq, ?_⟩
      rw [hnormeq]
      rw [hmass] at hbd
      calc
        _ ≤ T ^ occupationBeta d γ * (C γ * (ρ univ).toReal) := (mul_le_mul_of_nonneg_left hbd (Real.rpow_nonneg hT.le (occupationBeta d γ)))
        _ = _ := by ring
    obtain ⟨C, hC0, hscale⟩ := occupation_scaling_of_duality hDuality
    refine ⟨C, hC0, ?_⟩
    intro B hB S K hreal hP ρ _ σ₀ T hT
    obtain ⟨g, gt, hg, -, -, hb⟩ := hscale B hB S K hreal hP ρ σ₀ T hT
    refine ⟨g, hg, ?_⟩
    intro γ hγ0 hγ1
    exact ⟨(hb γ hγ0 hγ1).1, (hb γ hγ0 hγ1).2.2.2⟩
  have occupation_duality :
      ∃ C : ℝ → ℝ,
      (∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d → 0 ≤ C γ) ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0)
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => 0)
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ],
        ∃ g : TimeVelocity d → ℝ, IsOccupationDensity K 0 1 ρ g ∧
          ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
            MemLp g (ENNReal.ofReal γ)
              (volume.restrict (Ioo 0 1 ×ˢ univ)) ∧
            occupationLpNorm 1 γ g ≤ C γ * (ρ univ).toReal := by
    exact occupation_duality_of_whole_space_bound hH hd lam Lam hlam hLam
      (occupation_whole_space_bound hH hd lam Lam hlam hLam)
  exact occupation_of_duality (occupation_duality)

/-- The occupation family, relative to the terminal evolution statement and Hörmander's theorem. -/
theorem parabolicOccupationFamily_holds (hEvol : TerminalEvolutionStatement)
    (hH : HormanderHypoellipticityStatement)
    (hd : 0 < d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    Green.ParabolicOccupationFamily d lam Lam := by
  obtain ⟨C, hC0, hocc⟩ := occupation hH hd lam Lam hlam hLam
  refine ⟨C, ?_⟩
  intro B hB S K hreal
  refine ⟨hC0, ?_⟩
  intro ρ _ σ₀ T hT
  obtain ⟨g, hg, hb⟩ := hocc B hB S K hreal (wholeSpace_marginalBundle_of_evolution hEvol hd hB S K hreal) ρ σ₀ T hT
  refine ⟨g, (isOccupationDensity_iff_slabOccupationDensity K σ₀ T ρ g).mp hg, ?_⟩
  intro γ hγ0 hγ1
  exact hb γ hγ0 hγ1

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

