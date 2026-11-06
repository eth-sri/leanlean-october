module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationSource
public import PDEFoundation.Calculus.RegularityOrder


/-! # Position cutoffs for solutions defined only on a kinetic cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Filter Parabolic
open scoped Topology

variable {d : ℕ}

variable (Z₀ : KineticPoint d)

variable (χ : PDE.ScalarField d)

/-- The position cutoff uses the cylinder's actual free-transport frame. -/
def localPositionCutoff
    (P : KineticPoint d) : ℝ := χ (relativePosition Z₀ P)

/-- The local solution multiplied by a position cutoff, with no extension assumption. -/
def localCutoffSolution
    (u : HypoellipticAleksandrov.KineticScalarField d) (P : KineticPoint d) : ℝ := localPositionCutoff Z₀ χ P * u P

/-- Free-transport relative position is smooth on the physical product carrier. -/
theorem contDiff_relativePosition_native   :
    ContDiff ℝ PDE.smoothOrder
      (relativePosition Z₀ ∘ (KineticPoint.equivProd d).symm) :=
  (contDiff_snd.fst.sub contDiff_const).sub
    ((contDiff_fst.sub contDiff_const).smul contDiff_const)

/-- A smooth position cutoff is smooth in physical product coordinates. -/
theorem contDiff_localPositionCutoff
    {χ : PDE.ScalarField d} (hχ : ContDiff ℝ PDE.smoothOrder χ) :
    ContDiff ℝ PDE.smoothOrder
      (localPositionCutoff Z₀ χ ∘ (KineticPoint.equivProd d).symm) :=
  hχ.comp (contDiff_relativePosition_native Z₀)

/-- Strict position membership and closed velocity membership give outer closure membership. -/
theorem local_closed_strip_mem_outer  (Z₀ Q : KineticPoint d)
    {R a T : ℝ} (hR : 0 < R) (ha : Z₀.time ≤ a) (hT : T ≤ Z₀.time + R ^ 2)
    (hQ : Q ∈ localClosedStrip a T Z₀.velocity R)
    (hx : relativePosition Z₀ Q ∈ PDE.euclideanBall 0 (R ^ 3)) :
    Q ∈ closure (forwardCylinder Z₀ R hR) := by
  rw [comparison_closure_forwardCylinder_eq]
  refine ⟨⟨ha.trans hQ.1, hQ.2.1.trans hT⟩,
    PDE.euclideanBall_subset_euclideanClosedBall _ _ hx, ?_⟩
  change PDE.vecNormSq (Q.velocity - Z₀.velocity - 0) ≤ R ^ 2
  have hv := (closure_minimal (PDE.euclideanBall_subset_euclideanClosedBall _ _)
    (PDE.isClosed_euclideanClosedBall Z₀.velocity R)) hQ.2.2
  change PDE.vecNormSq (Q.velocity - Z₀.velocity) ≤ R ^ 2 at hv
  simpa only [sub_zero] using hv

variable (Z₀ : KineticPoint d) {R a T : ℝ} (hR : 0 < R)

/-- The cutoff solution is smooth inside the whole velocity strip. -/
theorem localCutoffSolution_contDiffOn   (ha : Z₀.time < a) (hT : T < Z₀.time + R ^ 2)
    (u : HypoellipticAleksandrov.KineticScalarField d)
    (hu : ContDiffOn ℝ PDE.smoothOrder (u ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' forwardCylinder Z₀ R hR))
    (χ : PDE.ScalarField d) (hχ : ContDiff ℝ PDE.smoothOrder χ)
    (hs : tsupport χ ⊆ PDE.euclideanBall 0 (R ^ 3)) :
    ContDiffOn ℝ PDE.smoothOrder
      (localCutoffSolution Z₀ χ u ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' localStrip a T Z₀.velocity R) := by
  rintro q ⟨P, hP, rfl⟩
  by_cases hx : relativePosition Z₀ P ∈ tsupport χ
  ·

    exact ((contDiff_localPositionCutoff Z₀ hχ).contDiffAt.mul
      (hu.contDiffAt (((KineticPoint.homeomorphProd d).isOpenMap _ (isOpen_forwardCylinder Z₀ R hR)).mem_nhds ⟨P, (⟨ha.trans hP.1, hP.2.1.trans hT, hP.2.2, hs hx⟩), rfl⟩))).contDiffWithinAt
  ·
    have hrel := (contDiff_relativePosition_native Z₀).continuous.continuousAt
      (x := (KineticPoint.equivProd d) P)

    exact (contDiffAt_const.congr_of_eventuallyEq (by
        filter_upwards [hrel.eventually (notMem_tsupport_iff_eventuallyEq.mp hx)] with q hq
        change χ (relativePosition Z₀ ((KineticPoint.equivProd d).symm q)) *
          u ((KineticPoint.equivProd d).symm q) = 0
        change χ (relativePosition Z₀ ((KineticPoint.equivProd d).symm q)) = 0 at hq
        rw [hq, zero_mul])).contDiffWithinAt

/-- The original closed-cylinder continuity gives closed-strip continuity after cutoff. -/
theorem localCutoffSolution_continuousOn   (ha : Z₀.time ≤ a) (hT : T ≤ Z₀.time + R ^ 2)
    (u : HypoellipticAleksandrov.KineticScalarField d)
    (hu : ContinuousOn u (closure (forwardCylinder Z₀ R hR)))
    (χ : PDE.ScalarField d) (hχ : Continuous χ)
    (hs : tsupport χ ⊆ PDE.euclideanBall 0 (R ^ 3)) :
    ContinuousOn (localCutoffSolution Z₀ χ u) (localClosedStrip a T Z₀.velocity R) := by
  have hrel : Continuous (relativePosition Z₀) :=
    (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  intro P hP
  by_cases hx : relativePosition Z₀ P ∈ tsupport χ
  ·

    exact (hχ.comp hrel).continuousAt.continuousWithinAt.mul
      ((hu P (local_closed_strip_mem_outer Z₀ P hR ha hT hP (hs hx))).mono_of_mem_nhdsWithin (by
          have hpos := hrel.continuousAt.preimage_mem_nhds
            ((PDE.isOpen_euclideanBall 0 (R ^ 3)).mem_nhds (hs hx))
          apply mem_of_superset (inter_mem (mem_nhdsWithin_of_mem_nhds hpos)
            self_mem_nhdsWithin)
          intro Q hQ
          exact local_closed_strip_mem_outer Z₀ Q hR ha hT hQ.2 hQ.1))
  ·

    exact (continuousAt_const.congr_of_eventuallyEq (by
        filter_upwards [hrel.continuousAt.eventually (notMem_tsupport_iff_eventuallyEq.mp hx)] with Q hQ
        change χ (relativePosition Z₀ Q) * u Q = 0
        change χ (relativePosition Z₀ Q) = 0 at hQ
        rw [hQ, zero_mul])).continuousWithinAt

/-- A cutoff with zero position germ has zero classical operator, even for arbitrary data. -/
theorem localCutoffSolution_operator_zero  (Z₀ P : KineticPoint d)
    (A : FullKineticCoefficient d) (χ : PDE.ScalarField d) (u : HypoellipticAleksandrov.KineticScalarField d)
    (hx : relativePosition Z₀ P ∉ tsupport χ) :
    forwardKineticOperator A (localCutoffSolution Z₀ χ u) P = 0 := by
  let sharedTerm_ce403832c0 := ((fun x => localCutoffSolution Z₀ χ u ⟨P.time, x, P.velocity⟩))
  have he  :=
    notMem_tsupport_iff_eventuallyEq.mp hx


  have hpos : sharedTerm_ce403832c0 =ᶠ[
      𝓝 P.position] (fun _ => (0 )) := by

    filter_upwards [((continuous_id.sub continuous_const).sub continuous_const).continuousAt.eventually he] with x hx'
    change χ (x - Z₀.position - (P.time - Z₀.time) • Z₀.velocity) = 0 at hx'
    change χ (x - Z₀.position - (P.time - Z₀.time) • Z₀.velocity) *
      u ⟨P.time, x, P.velocity⟩ = 0
    rw [hx', zero_mul]

  have hg : kineticPositionGradient (localCutoffSolution Z₀ χ u) P = 0 := by
    ext i
    change fderiv ℝ sharedTerm_ce403832c0
      P.position (PDE.basisVec i) = 0
    rw [hpos.fderiv_eq]
    exact congrArg (fun L : PDE.Vec d →L[ℝ] ℝ => L (PDE.basisVec i))
      (hasFDerivAt_const (0 : ℝ) P.position).fderiv
  have hvel : (fun v => localCutoffSolution Z₀ χ u ⟨P.time, P.position, v⟩) =
      (fun _ => (0 : ℝ)) := by
    funext v
    change χ (relativePosition Z₀ P) * u ⟨P.time, P.position, v⟩ = 0
    rw [(image_eq_zero_of_notMem_tsupport hx), zero_mul]
  have hh : kineticVelocityHessian (localCutoffSolution Z₀ χ u) P = 0 := by
    rw [kineticVelocityHessian_eq_sliceHessian, hvel]
    have hgrad : (fun y : PDE.Vec d => PDE.classicalGradient (fun _ => (0 )) y) =
        (fun _ => (0 : PDE.Vec d)) := by
      funext y
      ext k
      rw [PDE.classicalGradient_apply, fderiv_const_apply]
      rfl
    ext i j
    change fderiv ℝ (fun y => PDE.classicalGradient (fun _ => (0 )) y)
      P.velocity (PDE.basisVec i) j = 0
    rw [hgrad, fderiv_const_apply]
    rfl
  rw [forwardKineticOperator_apply, (show kineticTimeDerivative (localCutoffSolution Z₀ χ u) P = 0 from (show (fun t => localCutoffSolution Z₀ χ u ⟨t, P.position, P.velocity⟩) =ᶠ[
      𝓝 P.time] (fun _ => (0 )) by

      filter_upwards [(show Continuous (fun t  => P.position - Z₀.position -
          (t - Z₀.time) • Z₀.velocity) from continuous_const.sub ((continuous_id.sub continuous_const).smul continuous_const)).continuousAt.eventually he] with t ht
      change χ (P.position - Z₀.position - (t - Z₀.time) • Z₀.velocity) = 0 at ht
      change χ (P.position - Z₀.position - (t - Z₀.time) • Z₀.velocity) *
        u ⟨t, P.position, P.velocity⟩ = 0
      rw [ht, zero_mul]).deriv_eq.trans (deriv_const _ _)), hg, hh]
  simp only [PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    matrixContraction, add_zero, Matrix.zero_apply]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
