module

public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Pushforward
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Radius
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingBorel

/-! # First marginal of the constructed affine kernel pushforward -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open MeasureTheory Scaling

variable {d : ℕ} {B : CoefficientField d} (σ₀ : ℝ) (Φ : KineticAffineScaling d)
    (r : {r : ℝ // 0 < r})
    (K : MovingFiberKernel (SectionTwo.wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hP : SectionTwo.HasParabolicMarginalBundle (SectionTwo.wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z z' : PDE.Vec d)

/-- The first marginal of the pushed kernel is the inverse velocity affine image. -/
theorem firstMarginal_pushKernel
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
theorem firstMarginal_radius_query
    (t : ℝ) (ht : 0 ≤ t) (v : PDE.Vec d) :
    let Φ := KineticAffineScaling.ofRadius σ₀ 0 0 (SectionTwo.identityDrift d) r
    (KineticAffineScaling.pushKernel
      (KineticAffineScaling.mapsDomain_wholeSpace Φ) K).firstMarginal
        (SectionTwo.wholeSpaceQuery 0 t ht v 0) =
      (K.firstMarginal (SectionTwo.wholeSpaceQuery σ₀ (σ₀ + r.1 ^ 2 * t)
        (le_add_of_nonneg_right (mul_nonneg (sq_nonneg r.1) ht)) (r.1 • v) 0)).map
          (fun w => r.1⁻¹ • w) := by
  dsimp only
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

include hP in
/-- The original parabolic bundle makes the master velocity marginal position independent. -/
theorem firstMarginal_independent_position :
    K.firstMarginal (SectionTwo.wholeSpaceQuery σ τ hστ v z) =
      K.firstMarginal (SectionTwo.wholeSpaceQuery σ τ hστ v z') := by
  obtain ⟨_Q, h1, -, -, -, -, -, -, -, -, -⟩ := hP (fun _ _ _ _ => rfl)
  let y : EvolutionPosition (SectionTwo.wholeSpace d) (fun _ => 0) σ :=
    ⟨v, by simp [SectionTwo.movingDomain_wholeSpace]⟩
  have hh := congrArg
    (Measure.map ((↑) : EvolutionPosition (SectionTwo.wholeSpace d)
      (fun _ => 0) τ → PDE.Vec d)) ((h1 σ τ hστ y z).symm.trans (h1 σ τ hστ y z'))
  exact (MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal K MeasurableSet.univ σ τ hστ (evolutionStateOfPosition (SectionTwo.wholeSpace d) (fun _ => 0) σ y z)).symm.trans (hh.trans (MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal K MeasurableSet.univ σ τ hστ (evolutionStateOfPosition (SectionTwo.wholeSpace d) (fun _ => 0) σ y z')))

include hP in
/-- The scaled scalar marginal is conjugate by the fixed-time position equivalences. -/
theorem occupation_parabolicMarginal_conjugate
    (y : EvolutionPosition (SectionTwo.wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ) :
    let Kt := KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace Φ) K
    parabolicMarginalKernel Kt MeasurableSet.univ σ τ hστ y =
      (parabolicMarginalKernel K MeasurableSet.univ (Φ.time σ) (Φ.time τ)
        (Φ.time_le_iff.mpr hστ) (occupation_positionEquiv Φ σ y)).map
          (occupation_positionEquiv Φ τ).symm := by
  dsimp only
  let Kt := KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace Φ) K
  apply ((SectionTwo.wholeSpacePositionEquiv d τ).measurableEmbedding).map_injective
  have ho := MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal K
    MeasurableSet.univ (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ)
    (positionStateZero (SectionTwo.wholeSpace d) (fun _ => 0) (Φ.time σ)
      (occupation_positionEquiv Φ σ y))
  have hp := firstMarginal_pushKernel Φ (KineticAffineScaling.mapsDomain_wholeSpace Φ)
    K (evolutionQueryOfState (SectionTwo.wholeSpace d) (fun _ => 0) σ τ hστ
      (positionStateZero (SectionTwo.wholeSpace d) (fun _ => 0) σ y))
  have hquery : KineticAffineScaling.queryMap (KineticAffineScaling.mapsDomain_wholeSpace Φ)
      (evolutionQueryOfState (SectionTwo.wholeSpace d) (fun _ => 0) σ τ hστ
        (positionStateZero (SectionTwo.wholeSpace d) (fun _ => 0) σ y)) =
      SectionTwo.wholeSpaceQuery (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ)
        (Φ.position y.1) (Φ.transport σ 0) := by
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
  exact (MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal Kt MeasurableSet.univ σ τ hστ (positionStateZero (SectionTwo.wholeSpace d) (fun _ => 0) σ y)).trans (hp2.trans ((congrArg (Measure.map Φ.positionInv) ho).symm.trans hrhs.symm))

include hP in
/-- Position independence survives the constructed affine kernel pushforward. -/
theorem occupation_scaled_firstMarginal_independent :
    let Kt := KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace Φ) K
    Kt.firstMarginal (SectionTwo.wholeSpaceQuery σ τ hστ v z) =
      Kt.firstMarginal (SectionTwo.wholeSpaceQuery σ τ hστ v z') := by
  have hq (w : PDE.Vec d) :
      KineticAffineScaling.queryMap (KineticAffineScaling.mapsDomain_wholeSpace Φ)
        (SectionTwo.wholeSpaceQuery σ τ hστ v w) =
      SectionTwo.wholeSpaceQuery (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ)
        (Φ.position v) (Φ.transport σ w) := by
    rfl
  have hp := firstMarginal_pushKernel Φ (KineticAffineScaling.mapsDomain_wholeSpace Φ)
    K (SectionTwo.wholeSpaceQuery σ τ hστ v z)
  have hp' := firstMarginal_pushKernel Φ (KineticAffineScaling.mapsDomain_wholeSpace Φ)
    K (SectionTwo.wholeSpaceQuery σ τ hστ v z')
  rw [hq] at hp hp'
  exact hp.trans ((congrArg (Measure.map Φ.positionInv) (firstMarginal_independent_position K hP (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ) (Φ.position v) (Φ.transport σ z) (Φ.transport σ z'))).trans hp'.symm)

include hP in
/-- Equality of the scaled scalar kernel with the constructed kernel conjugation. -/
theorem occupation_parabolicKernel_conjugate :
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
theorem occupation_parabolicMarginalAmbient_eq
    (q : ParabolicEvolutionQuery (SectionTwo.wholeSpace d) (fun _ => (0 : PDE.Vec d))) :
    parabolicMarginalAmbientMeasure K MeasurableSet.univ q =
      K.firstMarginal (SectionTwo.wholeSpaceQuery q.1.1 q.1.2.1 q.2.1 q.1.2.2 0) := by
  apply MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal

/-- Joint measurable-set evaluation for every whole-space scalar marginal. -/
theorem occupation_parabolicMarginal_measurable
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

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
