module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.GeometryAPI
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Order.Compact
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonBoundary
import Mathlib.Topology.Order.OrderClosed

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology

/-- The position differential encoded by the existing classical gradient. -/
def comparisonPositionDifferential {d : ℕ} (u : KineticPoint d → ℝ)
    (P : KineticPoint d) : PDE.Vec d →L[ℝ] ℝ :=
  ∑ i : Fin d, kineticPositionGradient u P i • ContinuousLinearMap.proj i

/-- The encoded differential agrees with the actual position-slice differential. -/
theorem comparisonPositionDifferential_eq_fderiv {d : ℕ}
    (u : KineticPoint d → ℝ) (P : KineticPoint d) :
    comparisonPositionDifferential u P =
      fderiv ℝ (fun x => u ⟨P.time,x,P.velocity⟩) P.position := by
  ext v
  rw [PDE.fderiv_apply_eq_vecDot_classicalGradient]
  simp [comparisonPositionDifferential, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, kineticPositionGradient, PDE.vecDot]


/-- Continuous partial derivatives give the derivative along physical free transport. -/
theorem hasDerivAt_freeTransport {d : ℕ} {D : Set (KineticPoint d)}
    (hD : IsOpen D) {u : KineticPoint d → ℝ} (hu : IsKineticC112On u D)
    {P : KineticPoint d} (hP : P ∈ D) :
    HasDerivAt (fun r : ℝ => u ⟨P.time + r,P.position + r • P.velocity,P.velocity⟩)
      (kineticTimeDerivative u P + PDE.vecDot P.velocity (kineticPositionGradient u P)) 0  := by
  have continuousOn_comparisonPositionDifferential :
      ContinuousOn (comparisonPositionDifferential u) D := by
    unfold comparisonPositionDifferential
    apply continuousOn_finsetSum
    intro i _
    exact ((continuous_apply i).comp_continuousOn
      hu.continuousOn_kineticPositionGradient).smul continuousOn_const
  let ι : ℝ × PDE.Vec d → KineticPoint d := fun z => ⟨z.1,z.2,P.velocity⟩
  have hι : Continuous ι :=
    KineticPoint.continuous_mk continuous_fst continuous_snd continuous_const
  have hev : ∀ᶠ z in 𝓝 (P.time,P.position), ι z ∈ D :=
    hι.continuousAt (hD.mem_nhds hP)
  let f : ℝ → PDE.Vec d → ℝ := fun s x => u ⟨s,x,P.velocity⟩
  let ft : ℝ → PDE.Vec d → ℝ →L[ℝ] ℝ := fun s x =>
    ContinuousLinearMap.toSpanSingleton ℝ (kineticTimeDerivative u ⟨s,x,P.velocity⟩)
  let fx : ℝ → PDE.Vec d → PDE.Vec d →L[ℝ] ℝ := fun s x =>
    comparisonPositionDifferential u ⟨s,x,P.velocity⟩
  have ht : ∀ᶠ z in 𝓝 (P.time,P.position), HasFDerivAt (f · z.2) (ft z.1 z.2) z.1 := by
    filter_upwards [hev] with z hz
    exact (hu.timeSlice_differentiableAt hz).hasDerivAt.hasFDerivAt
  have hx : ∀ᶠ z in 𝓝 (P.time,P.position), HasFDerivAt (f z.1 ·) (fx z.1 z.2) z.2 := by
    filter_upwards [hev] with z hz
    dsimp only [fx]
    rw [comparisonPositionDifferential_eq_fderiv]
    exact (hu.positionSlice_contDiffAt hz).differentiableAt (by norm_num) |>.hasFDerivAt
  have hiP : ι (P.time,P.position) = P := by cases P; rfl
  have hct : ContinuousAt (fun z => ft z.1 z.2) (P.time,P.position) := by
    have hc : ContinuousAt (kineticTimeDerivative u) (ι (P.time,P.position)) := by
      rw [hiP]
      exact hu.continuousOn_kineticTimeDerivative.continuousAt (hD.mem_nhds hP)
    have hcι : ContinuousAt (kineticTimeDerivative u ∘ ι) (P.time,P.position) :=
      hc.comp hι.continuousAt
    exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.continuousAt.comp
      hcι
  have hcx : ContinuousAt (fun z => fx z.1 z.2) (P.time,P.position) := by
    have hc : ContinuousAt (comparisonPositionDifferential u) (ι (P.time,P.position)) := by
      rw [hiP]
      exact (continuousOn_comparisonPositionDifferential).continuousAt (hD.mem_nhds hP)
    exact hc.comp hι.continuousAt
  have hline : HasDerivAt (fun r => (P.time + r,P.position + r • P.velocity))
      (1,P.velocity) 0 := by
    simpa using
      ((hasDerivAt_id 0).const_add P.time).prodMk
        (((hasDerivAt_id 0).smul_const P.velocity).const_add P.position)
  have hj' := ((hasStrictFDerivAt_uncurry_coprod (f := f) (f₁ := ft) (f₂ := fx) (u := (P.time,P.position)) ht hx hct hcx).hasFDerivAt)
  rw [show (P.time,P.position) =
    (P.time + 0,P.position + (0 : ℝ) • P.velocity) by simp] at hj'
  convert (hj'.comp_hasDerivAt 0 hline) using 1
  · rfl
  · simp [Function.HasUncurry.uncurry, ContinuousLinearMap.coprod_apply, ft, fx, ContinuousLinearMap.toSpanSingleton_apply]
    rw [comparisonPositionDifferential_eq_fderiv,
      PDE.fderiv_apply_eq_vecDot_classicalGradient, PDE.vecDot_comm]
    rfl


/-- A vector with strictly inward normal component stays in the closed ball for short time. -/
theorem comparison_inward_segment {d : ℕ} (Y V : PDE.Vec d) (r : ℝ)
    (hY : PDE.vecNormSq Y ≤ r ^ 2)
    (hin : ¬ (PDE.vecNormSq Y = r ^ 2 ∧ 0 ≤ PDE.vecDot V Y)) :
    ∃ η : ℝ, 0 < η ∧ ∀ h : ℝ, 0 ≤ h → h < η →
      PDE.vecNormSq (Y + h • V) ≤ r ^ 2 := by
  by_cases hstrict : PDE.vecNormSq Y < r ^ 2
  · have hc : Continuous (fun h : ℝ => PDE.vecNormSq (Y + h • V)) :=
      PDE.continuous_vecNormSq.comp (continuous_const.add (continuous_id.smul continuous_const))
    have he : ∀ᶠ h in 𝓝 (0 : ℝ), PDE.vecNormSq (Y + h • V) < r ^ 2 := by
      apply hc.continuousAt.eventually_lt continuousAt_const
      simpa using hstrict
    obtain ⟨η,hη,he⟩ := Metric.eventually_nhds_iff.mp he
    refine ⟨η,hη,fun h hh hhη => (he ?_).le⟩
    simpa [Real.dist_eq, abs_of_nonneg hh] using hhη
  · have heq : PDE.vecNormSq Y = r ^ 2 := le_antisymm hY (le_of_not_gt hstrict)
    have hdot := lt_of_not_ge (fun h => hin ⟨heq,h⟩)
    have hnorm := PDE.vecNormSq_nonneg V
    have hden : 0 < PDE.vecNormSq V + 1 := by positivity
    refine ⟨-PDE.vecDot V Y / (PDE.vecNormSq V + 1), div_pos (neg_pos.mpr hdot) hden,?_⟩
    intro h hh hhη
    have hb :=
      (lt_div_iff₀ hden).mp hhη
    have hm : h * (2 * PDE.vecDot V Y + h * PDE.vecNormSq V) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hh (by linarith)
    have hd : PDE.vecDot Y (h • V) = h * PDE.vecDot V Y := by
      simp [PDE.vecDot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [PDE.vecNormSq_add_expand, PDE.vecNormSq_smul, hd, heq]
    nlinarith only [hm]




/-- At a non-exit closed-cylinder maximum, transport plus diffusion is nonpositive.
Only the source anisotropic regularity on an open neighbourhood is used. -/
theorem comparison_operator_nonpos_at_max {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    {D : Set (KineticPoint d)} (hD : IsOpen D)
    (hQD : closure (forwardCylinder Z₀ R hR) ⊆ D)
    {u : KineticPoint d → ℝ} (hu : IsKineticC112On u D)
    (A : FullKineticCoefficient d) {P : KineticPoint d}
    (hP : P ∈ closure (forwardCylinder Z₀ R hR))
    (hnot : P ∉ exitBoundary Z₀ R hR)
    (hmax : IsMaxOn u (closure (forwardCylinder Z₀ R hR)) P)
    (hA : (A P.time P.position P.velocity).PosSemidef) :
    forwardKineticOperator A u P ≤ 0   := by
  have comparison_velocity_interior (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) {P : KineticPoint d} (hP : P ∈ closure (forwardCylinder Z₀ R hR)) (hnot : P ∉ exitBoundary Z₀ R hR) :
      P.velocity ∈ PDE.euclideanBall Z₀.velocity R := by
    have hb := (closure_forwardCylinder_bounds Z₀ R hR hP).2.2
    change PDE.vecNormSq (P.velocity - Z₀.velocity - 0) ≤ R ^ 2 at hb
    simp at hb
    apply lt_of_le_of_ne hb
    intro heq
    apply hnot ((mem_exitBoundary_iff Z₀ P R hR).2 ⟨hP,Or.inr (Or.inl ?_)⟩)
    exact heq
  have comparison_freeTransport_stays (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) {P : KineticPoint d} (hP : P ∈ closure (forwardCylinder Z₀ R hR)) (hnot : P ∉ exitBoundary Z₀ R hR) :
      ∃ η : ℝ, 0 < η ∧ ∀ h : ℝ, 0 ≤ h → h < η →
      (⟨P.time + h,P.position + h • P.velocity,P.velocity⟩ : KineticPoint d) ∈
        closure (forwardCylinder Z₀ R hR) := by
    have hb := closure_forwardCylinder_bounds Z₀ R hR hP
    rcases hb with ⟨⟨ht0,ht1⟩,hx,hv⟩
    change Z₀.time ≤ P.time at ht0
    change P.time ≤ Z₀.time + R ^ 2 at ht1
    have htime : P.time < Z₀.time + R ^ 2 := by
      apply lt_of_le_of_ne ht1
      intro heq
      exact hnot ((mem_exitBoundary_iff Z₀ P R hR).2 ⟨hP,Or.inl heq⟩)
    have hin : ¬ (PDE.vecNormSq (relativePosition Z₀ P) = (R ^ 3) ^ 2 ∧
        0 ≤ PDE.vecDot (relativeVelocity Z₀ P) (relativePosition Z₀ P)) := by
      intro hh
      apply hnot ((mem_exitBoundary_iff Z₀ P R hR).2 ⟨hP,Or.inr (Or.inr ?_)⟩)
      refine ⟨?_,hh.2⟩
      simpa [PDE.euclideanSphere, PDE.euclideanSqDist, relativeHomeomorph] using hh.1
    have hx' : PDE.vecNormSq (relativePosition Z₀ P) ≤ (R ^ 3) ^ 2 := by
      change PDE.vecNormSq (relativePosition Z₀ P - 0) ≤ (R ^ 3) ^ 2 at hx
      simpa using hx
    obtain ⟨r,hr,hstay⟩ := comparison_inward_segment _ _ _ hx' hin
    refine ⟨min r (Z₀.time + R ^ 2 - P.time), lt_min hr (sub_pos.mpr htime),?_⟩
    intro h hh hη
    rw [comparison_closure_forwardCylinder_eq]
    change (Z₀.time ≤ P.time + h ∧ P.time + h ≤ Z₀.time + R ^ 2) ∧
      relativePosition Z₀ ⟨P.time + h,P.position + h • P.velocity,P.velocity⟩ ∈
        PDE.euclideanClosedBall 0 (R ^ 3) ∧
      relativeVelocity Z₀ ⟨P.time + h,P.position + h • P.velocity,P.velocity⟩ ∈
        PDE.euclideanClosedBall 0 R
    refine ⟨⟨by linarith,by have := lt_of_lt_of_le hη (min_le_right _ _); linarith⟩,?_,hv⟩
    have heq : relativePosition Z₀ ⟨P.time + h,P.position + h • P.velocity,P.velocity⟩ =
        relativePosition Z₀ P + h • relativeVelocity Z₀ P := by
      ext i
      simp [relativePosition, relativeVelocity]
      ring
    rw [heq]
    simpa [PDE.euclideanClosedBall, PDE.euclideanSqDist, relativeHomeomorph] using
      hstay h hh (lt_of_lt_of_le hη (min_le_left _ _))
  have htransport := hasDerivAt_freeTransport hD hu (hQD hP)
  obtain ⟨η,hη,hstay⟩ := comparison_freeTransport_stays Z₀ R hR hP hnot
  have hmaxTransport : ∀ᶠ h in 𝓝 0, 0 ≤ h →
      u ⟨P.time + h,P.position + h • P.velocity,P.velocity⟩ ≤
        u ⟨P.time + 0,P.position + (0 : ℝ) • P.velocity,P.velocity⟩ := by
    filter_upwards [Iio_mem_nhds hη] with h hh hhn
    simpa using hmax (hstay h hhn hh)
  have ht := deriv_nonpos_of_future_localMax htransport.differentiableAt hmaxTransport
  rw [htransport.deriv] at ht
  have hv : IsLocalMax (fun v => u ⟨P.time,P.position,v⟩) P.velocity := by
    filter_upwards [(PDE.isOpen_euclideanBall Z₀.velocity R).mem_nhds (comparison_velocity_interior Z₀ R hR hP hnot)] with v hv
    apply hmax
    rw [comparison_closure_forwardCylinder_eq]
    have hb := closure_forwardCylinder_bounds Z₀ R hR hP
    change (Z₀.time ≤ P.time ∧ P.time ≤ Z₀.time + R ^ 2) ∧
      relativePosition Z₀ P ∈ PDE.euclideanClosedBall 0 (R ^ 3) ∧
      v - Z₀.velocity ∈ PDE.euclideanClosedBall 0 R
    refine ⟨hb.1,hb.2.1,?_⟩
    simpa [PDE.euclideanClosedBall, PDE.euclideanSqDist] using (PDE.euclideanBall_subset_euclideanClosedBall _ _ hv)
  rw [forwardKineticOperator_apply, kineticVelocityHessian_eq_sliceHessian]
  exact add_nonpos ht (matrixContraction_sliceHessian_nonpos_of_localMax (hu.velocitySlice_contDiffAt (hQD hP)) hv hA)

/-- A positive maximum of a strict subsolution is on the exit boundary. -/
theorem comparison_inner_maximum_exclusion {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    {D : Set (KineticPoint d)} (hD : IsOpen D)
    (hQD : closure (forwardCylinder Z₀ R hR) ⊆ D)
    {u : KineticPoint d → ℝ} (hu : IsKineticC112On u D)
    (A : FullKineticCoefficient d)
    (hA : ∀ P ∈ D, (A P.time P.position P.velocity).PosSemidef)
    (hstrict : ∀ P ∈ D, 0 < u P → 0 < forwardKineticOperator A u P)
    {P : KineticPoint d} (hP : P ∈ closure (forwardCylinder Z₀ R hR))
    (hmax : IsMaxOn u (closure (forwardCylinder Z₀ R hR)) P) (hpos : 0 < u P) :
    P ∈ exitBoundary Z₀ R hR := by
  by_contra hnot
  exact (not_le.mpr (hstrict P (hQD hP) hpos))
    (comparison_operator_nonpos_at_max Z₀ R hR hD hQD hu A hP hnot hmax (hA P (hQD hP)))


/-- The terminal-time affine function has unit time derivative and zero spatial derivatives. -/
theorem comparison_time_sub_formulas {d : ℕ} (T : ℝ) (P : KineticPoint d) :
    kineticTimeDerivative (fun Q : KineticPoint d => Q.time - T) P = 1 ∧
    kineticPositionGradient (fun Q : KineticPoint d => Q.time - T) P = 0 ∧
    kineticVelocityGradient (fun Q : KineticPoint d => Q.time - T) P = 0 ∧
    kineticVelocityHessian (fun Q : KineticPoint d => Q.time - T) P = 0 := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [kineticTimeDerivative]
    simp
  · ext i
    simp [kineticPositionGradient, PDE.classicalGradient]
  · ext i
    simp [kineticVelocityGradient, PDE.classicalGradient]
  · have hg : (fun v =>
        PDE.classicalGradient (fun _ : PDE.Vec d => P.time - T) v) = fun _ => 0 := by
      funext v
      ext i
      simp [PDE.classicalGradient]
    unfold kineticVelocityHessian
    rw [hg]
    ext i j
    simp

/-- The time-affine function is in the source classical class on every set. -/
theorem comparison_regular_time_sub {d : ℕ} (T : ℝ) (D : Set (KineticPoint d)) :
    IsKineticC112On (fun Q : KineticPoint d => Q.time - T) D := by
  refine ⟨(continuous_time.sub continuous_const).continuousOn,
    fun _ _ => differentiableAt_id.sub_const T,
    fun P _ => (show ContDiffAt ℝ 1 (fun _ => P.time - T) P.position from
      contDiffAt_const),
    fun P _ => (show ContDiffAt ℝ 2 (fun _ => P.time - T) P.velocity from
      contDiffAt_const),?_,?_,?_,?_⟩
  · have h : kineticTimeDerivative (fun Q : KineticPoint d => Q.time - T) =
        fun _ => 1 := funext fun P => (comparison_time_sub_formulas T P).1
    rw [h]
    exact continuousOn_const
  · have h : kineticPositionGradient (fun Q : KineticPoint d => Q.time - T) =
        fun _ => 0 := funext fun P => (comparison_time_sub_formulas T P).2.1
    rw [h]
    exact continuousOn_const
  · have h : kineticVelocityGradient (fun Q : KineticPoint d => Q.time - T) =
        fun _ => 0 := funext fun P => (comparison_time_sub_formulas T P).2.2.1
    rw [h]
    exact continuousOn_const
  · have h : kineticVelocityHessian (fun Q : KineticPoint d => Q.time - T) =
        fun _ => 0 := funext fun P => (comparison_time_sub_formulas T P).2.2.2
    rw [h]
    exact continuousOn_const

/-- The forward operator of the terminal-time affine function equals one. -/
theorem comparison_forwardOperator_time_sub {d : ℕ}
    (A : FullKineticCoefficient d) (T : ℝ) (P : KineticPoint d) :
    forwardKineticOperator A (fun Q : KineticPoint d => Q.time - T) P = 1 := by
  obtain ⟨ht,hx,_,hv⟩ := comparison_time_sub_formulas T P
  rw [forwardKineticOperator_apply,ht,hx,hv]
  simp [PDE.vecDot, HypoellipticAleksandrov.matrixContraction]

/-- The exact source tilt preserves regularity and is a strict subsolution at positive points. -/
theorem comparison_strictification {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (A : FullKineticCoefficient d) (u : KineticPoint d → ℝ)
    (hu : IsKineticC112On u (forwardCylinder Z₀ R hR))
    (hsub : ∀ P ∈ forwardCylinder Z₀ R hR, 0 < u P →
      0 ≤ forwardKineticOperator A u P) (ε : ℝ) (hε : 0 < ε) :
    let w := fun P : KineticPoint d => u P + ε * (P.time - Z₀.time - R ^ 2)
    (∀ P ∈ closure (forwardCylinder Z₀ R hR), w P ≤ u P) ∧
      IsKineticC112On w (forwardCylinder Z₀ R hR) ∧
      (∀ P ∈ forwardCylinder Z₀ R hR, 0 < w P →
        ε ≤ forwardKineticOperator A w P) := by
  let T := Z₀.time + R ^ 2
  dsimp only
  simp only [sub_sub]
  have ht := comparison_regular_time_sub (d := d) T (forwardCylinder Z₀ R hR)
  have hle : ∀ P ∈ closure (forwardCylinder Z₀ R hR),
      u P + ε * (P.time - T) ≤ u P := by
    intro P hP
    have hp := (closure_forwardCylinder_bounds Z₀ R hR hP).1.2
    change P.time ≤ T at hp
    linarith only [(mul_nonpos_of_nonneg_of_nonpos hε.le (sub_nonpos.mpr hp))]
  refine ⟨hle,comparison_regular_add hu (comparison_regular_const_mul ht ε),?_⟩
  intro P hP hpos
  rw [comparison_forwardOperator_add hu (comparison_regular_const_mul ht ε) A hP,
    comparison_forwardOperator_const_mul ht ε A hP,comparison_forwardOperator_time_sub,mul_one]
  have hs := hsub P hP (lt_of_lt_of_le hpos (hle P (subset_closure hP)))
  linarith only [hs]


/-- The terminal face supplies an exit-boundary point for every positive-radius cylinder. -/
theorem comparison_exitBoundary_nonempty {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    (exitBoundary Z₀ R hR).Nonempty := by
  let P : KineticPoint d := ⟨Z₀.time + R ^ 2,Z₀.position + R ^ 2 • Z₀.velocity,Z₀.velocity⟩
  refine ⟨P,(mem_exitBoundary_iff Z₀ P R hR).2 ⟨?_,Or.inl rfl⟩⟩
  rw [comparison_closure_forwardCylinder_eq]
  have hx : relativePosition Z₀ P = 0 := by
    ext i
    simp only [relativePosition,P,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,Pi.zero_apply,smul_eq_mul]
    ring
  change (Z₀.time ≤ Z₀.time + R ^ 2 ∧ Z₀.time + R ^ 2 ≤ Z₀.time + R ^ 2) ∧
    relativePosition Z₀ P ∈ PDE.euclideanClosedBall 0 (R ^ 3) ∧
    relativeVelocity Z₀ P ∈ PDE.euclideanClosedBall 0 R
  rw [hx]
  simp [P,relativeVelocity,PDE.euclideanClosedBall,PDE.euclideanSqDist,
    PDE.vecNormSq,PDE.vecDot,sq_nonneg]

/-- A scalar boundary bound propagates for a strict subsolution on a compact cylinder. -/
theorem comparison_strict_compact_bound {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    {D : Set (KineticPoint d)} (hD : IsOpen D)
    (hQD : closure (forwardCylinder Z₀ R hR) ⊆ D)
    {u : KineticPoint d → ℝ} (hu : IsKineticC112On u D)
    (A : FullKineticCoefficient d)
    (hA : ∀ P ∈ D, (A P.time P.position P.velocity).PosSemidef)
    (hstrict : ∀ P ∈ D, 0 < u P → 0 < forwardKineticOperator A u P)
    (M : ℝ) (hM : 0 ≤ M) (hboundary : ∀ P ∈ exitBoundary Z₀ R hR, u P ≤ M) :
    ∀ P ∈ closure (forwardCylinder Z₀ R hR), u P ≤ M := by
  intro P hP
  by_contra hn
  have hpos := not_le.mp hn
  obtain ⟨p,hp,hmax⟩ := (isCompact_closure_forwardCylinder Z₀ R hR).exists_isMaxOn
    ⟨P,hP⟩ (hu.continuousOn.mono hQD)
  have hpexit := comparison_inner_maximum_exclusion Z₀ R hR hD hQD hu A hA hstrict hp hmax (lt_of_le_of_lt hM (lt_of_lt_of_le hpos (hmax hP)))
  exact (not_le.mpr hpos) ((hmax hP).trans (hboundary p hpexit))

/-- Retractions and exhaustion pass a strict comparison bound to the original closure. -/
theorem comparison_boundary_limit {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (A : FullKineticCoefficient d) (u : KineticPoint d → ℝ)
    (hA : ∀ P ∈ forwardCylinder Z₀ R hR, (A P.time P.position P.velocity).PosSemidef)
    (hcont : ContinuousOn u (closure (forwardCylinder Z₀ R hR)))
    (hreg : IsKineticC112On u (forwardCylinder Z₀ R hR))
    (hstrict : ∀ P ∈ forwardCylinder Z₀ R hR, 0 < u P →
      0 < forwardKineticOperator A u P)
    (M : ℝ) (hM : 0 ≤ M) (hboundary : ∀ P ∈ exitBoundary Z₀ R hR, u P ≤ M) :
    ∀ P ∈ closure (forwardCylinder Z₀ R hR), u P ≤ M := by
  have hb : sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) ≤ M := by
    apply csSup_le ((comparison_exitBoundary_nonempty Z₀ R hR).image _)
    rintro _ ⟨P,hP,rfl⟩
    exact max_le (hboundary P hP) hM
  have hinterior : ∀ P ∈ forwardCylinder Z₀ R hR, u P ≤ M := by
    intro P hP
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨η,hη,hbound⟩ := comparison_exit_boundary_approx Z₀ R hR u hcont hε
    obtain ⟨τ,hτ,hexhaust⟩ := innerCylinder_exhaustion Z₀ R hR P hP
    let δ := min (R ^ 2 / 4) (min η τ / 2)
    have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
    have hδlt : δ < R ^ 2 / 2 := by
      have h := min_le_left (R ^ 2 / 4) (min η τ / 2)
      dsimp only [δ]
      nlinarith [sq_pos_of_pos hR]
    have hδη : δ < η := by
      have h1 : δ ≤ min η τ / 2 := min_le_right _ _
      have h2 := min_le_left η τ
      linarith only [h1,h2,hη]
    have hδτ : δ < τ := by
      have h1 : δ ≤ min η τ / 2 := min_le_right _ _
      linarith only [h1,(min_le_right η τ),hτ]
    obtain ⟨hr,heq⟩ := innerCylinder_eq_forwardCylinder Z₀ R hR δ hδ0 hδlt
    obtain ⟨hr',heqB⟩ := innerExitBoundary_eq_exitBoundary Z₀ R hR δ hδ0 hδlt
    have hQD : closure (forwardCylinder (innerCentre Z₀ δ)
        (innerRatio R hR δ hδ0 hδlt * R) hr) ⊆ forwardCylinder Z₀ R hR := by
      rw [← heq]
      exact closure_innerCylinder_subset Z₀ R hR δ hδ0 hδlt
    have hPinner := hexhaust δ hδ0 hδlt hδτ
    rw [heq] at hPinner
    apply comparison_strict_compact_bound (innerCentre Z₀ δ) _ hr
      (isOpen_forwardCylinder Z₀ R hR) hQD hreg A hA hstrict (M + ε)
      (by linarith only [hM,hε]) ?_ P (subset_closure hPinner)
    intro p hp
    have hpB : p ∈ innerExitBoundary Z₀ R hR δ hδ0 hδlt := by
      rw [heqB]
      exact hp
    exact (le_max_left (u p) 0).trans ((hbound δ hδ0 hδlt hδη p hpB).trans
      (by linarith only [hb]))
  exact le_on_closure hinterior hcont continuousOn_const

/-- The source kinetic comparison principle with pointwise positive semidefinite coefficients. -/
theorem kinetic_comparison {d : ℕ} (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (A : FullKineticCoefficient d) (u : KineticPoint d → ℝ)
    (hA : ∀ P ∈ forwardCylinder Z₀ R hR, (A P.time P.position P.velocity).PosSemidef)
    (hcont : ContinuousOn u (closure (forwardCylinder Z₀ R hR)))
    (hreg : IsKineticC112On u (forwardCylinder Z₀ R hR))
    (hsub : ∀ P ∈ forwardCylinder Z₀ R hR, 0 < u P →
      0 ≤ forwardKineticOperator A u P) :
    ∀ P ∈ closure (forwardCylinder Z₀ R hR), u P ≤
      sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) := by
  let M := sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR)
  have hbd : BddAbove ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) :=
    ((isCompact_closure_forwardCylinder Z₀ R hR).bddAbove_image
      (hcont.sup continuousOn_const)).mono (image_mono (fun _ h => h.1))
  have hM : 0 ≤ M := by
    obtain ⟨p,hp⟩ := comparison_exitBoundary_nonempty Z₀ R hR
    exact (le_max_right (u p) 0).trans (le_csSup hbd (mem_image_of_mem _ hp))
  intro P hP
  apply le_of_forall_pos_le_add
  intro ε hε
  let e := ε / (R ^ 2 + 1)
  have he : 0 < e := div_pos hε (by positivity)
  obtain ⟨hle,hregular,hstrict⟩ := comparison_strictification Z₀ R hR A u hreg hsub e he
  have hc : ContinuousOn (fun p => u p + e * (p.time - Z₀.time - R ^ 2))
      (closure (forwardCylinder Z₀ R hR)) :=
    hcont.add (continuous_const.mul
      ((continuous_time.sub continuous_const).sub continuous_const)).continuousOn
  have hbound := comparison_boundary_limit Z₀ R hR A _ hA hc hregular
    (fun p hp hpos => lt_of_lt_of_le he (hstrict p hp hpos)) M hM
    (fun p hp => (hle p hp.1).trans ((le_max_left (u p) 0).trans
      (le_csSup hbd (mem_image_of_mem _ hp)))) P hP
  have ht := (closure_forwardCylinder_bounds Z₀ R hR hP).1.1
  change Z₀.time ≤ P.time at ht
  have herr : e * R ^ 2 ≤ ε := by
    dsimp only [e]
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    nlinarith only [hε.le]
  change u P + e * (P.time - Z₀.time - R ^ 2) ≤ M at hbound
  nlinarith only [hbound,ht,he.le,herr]

end HypoellipticAleksandrov.KineticAleksandrov

