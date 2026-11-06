module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonFaces
import Mathlib.Topology.Order.Compact
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.GeometryAPI
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry
import Mathlib.Tactic.FieldSimp

/-! # The classical operator at a closed-cylinder maximum outside the exit faces -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology

/- The velocity of a non-exit point is strictly inside the velocity ball. -/
theorem comparison_inner_maximum_exclusion {d }
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    {D } (hD : IsOpen D)
    (hQD : closure (forwardCylinder Z₀ R hR) ⊆ D)
    {u } (hu : IsKineticC112On u D)
    (A : FullKineticCoefficient d)
    (hA : ∀ P ∈ D, (A P.time P.position P.velocity).PosSemidef)
    (hstrict : ∀ P ∈ D, 0 < u P → 0 < forwardKineticOperator A u P)
    {P } (hP : P ∈ closure (forwardCylinder Z₀ R hR))
    (hmax : IsMaxOn u (closure (forwardCylinder Z₀ R hR)) P) (hpos : 0 < u P) :
    P ∈ exitBoundary Z₀ R hR := by
  by_contra hnot
  have _h_inl_16 : forwardKineticOperator A u P ≤ 0 := by
    have hA := (hA P (hQD hP))
    have htransport : HasDerivAt (fun r : ℝ => u ⟨P.time + r,P.position + r • P.velocity,P.velocity⟩)
        (kineticTimeDerivative u P + PDE.vecDot P.velocity (kineticPositionGradient u P)) 0 := by
      have hP := (hQD hP)
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
      have hct : ContinuousAt (fun z : ℝ × PDE.Vec d => ft z.1 z.2) (P.time,P.position) := by
        have hc : ContinuousAt (kineticTimeDerivative u) (ι (P.time,P.position)) := by
          rw [hiP]
          exact hu.continuousOn_kineticTimeDerivative.continuousAt (hD.mem_nhds hP)
        have hcι :=
          hc.comp hι.continuousAt
        exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.continuousAt.comp
          hcι
      have hcx : ContinuousAt (fun z : ℝ × PDE.Vec d => fx z.1 z.2) (P.time,P.position) := by
        have hc : ContinuousAt (comparisonPositionDifferential u) (ι (P.time,P.position)) := by
          rw [hiP]
          have _h_xinl_0 : ContinuousOn (comparisonPositionDifferential u) D := by
              unfold comparisonPositionDifferential
              apply continuousOn_finsetSum
              intro i _
              exact ((continuous_apply i).comp_continuousOn
                hu.continuousOn_kineticPositionGradient).smul continuousOn_const


          exact _h_xinl_0.continuousAt (hD.mem_nhds hP)
        change ContinuousAt (comparisonPositionDifferential u ∘ ι) (P.time,P.position)
        exact hc.comp hι.continuousAt
      have hj := (hasStrictFDerivAt_uncurry_coprod (f := f) (f₁ := ft) (f₂ := fx)
        (u := (P.time,P.position)) ht hx hct hcx).hasFDerivAt
      have hline : HasDerivAt (fun r : ℝ => (P.time + r,P.position + r • P.velocity))
          (1,P.velocity) 0 := by
        simpa only [one_smul, id_eq] using
          ((hasDerivAt_id 0).const_add P.time).prodMk
            (((hasDerivAt_id 0).smul_const P.velocity).const_add P.position)
      have hj' := hj
      rw [show (P.time,P.position) =
        (P.time + 0,P.position + (0 : ℝ) • P.velocity) by simp only [add_zero,zero_smul]] at hj'
      have hc := hj'.comp_hasDerivAt 0 hline
      convert hc using 1
      · rfl
      · simp only [Function.HasUncurry.uncurry,id_eq,add_zero,zero_smul,
          ContinuousLinearMap.coprod_apply,
          ft,fx,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
        rw [comparisonPositionDifferential_eq_fderiv,
          PDE.fderiv_apply_eq_vecDot_classicalGradient, PDE.vecDot_comm]
        rfl
    obtain ⟨η,hη,hstay⟩ : ∃ η : ℝ, 0 < η ∧ ∀ h : ℝ, 0 ≤ h → h < η →
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
        simpa only [PDE.euclideanSphere, PDE.euclideanSqDist, mem_ofPred_eq,
          relativeHomeomorph, sub_zero] using hh.1
      have hx' : PDE.vecNormSq (relativePosition Z₀ P) ≤ (R ^ 3) ^ 2 := by
        change PDE.vecNormSq (relativePosition Z₀ P - 0) ≤ (R ^ 3) ^ 2 at hx
        simpa only [sub_zero] using hx
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
        simp only [relativePosition, relativeVelocity, Pi.add_apply, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul]
        ring
      rw [heq]
      simpa only [PDE.euclideanClosedBall, PDE.euclideanSqDist, mem_ofPred_eq,
          relativeHomeomorph, sub_zero] using
        hstay h hh (lt_of_lt_of_le hη (min_le_left _ _))
    have hmaxTransport : ∀ᶠ h in 𝓝 (0 : ℝ), 0 ≤ h →
        u ⟨P.time + h,P.position + h • P.velocity,P.velocity⟩ ≤
          u ⟨P.time + 0,P.position + (0 : ℝ) • P.velocity,P.velocity⟩ := by
      filter_upwards [Iio_mem_nhds hη] with h hh hhn
      simpa only [mem_ofPred_eq,add_zero,zero_smul] using hmax (hstay h hhn hh)
    have ht := deriv_nonpos_of_future_localMax htransport.differentiableAt hmaxTransport
    rw [htransport.deriv] at ht
    have hv : IsLocalMax (fun v => u ⟨P.time,P.position,v⟩) P.velocity := by
      have hpv : P.velocity ∈ PDE.euclideanBall Z₀.velocity R := by
          have hb := (closure_forwardCylinder_bounds Z₀ R hR hP).2.2
          change PDE.vecNormSq (P.velocity - Z₀.velocity - 0) ≤ R ^ 2 at hb
          simp only [sub_zero] at hb
          change PDE.vecNormSq (P.velocity - Z₀.velocity) < R ^ 2
          apply lt_of_le_of_ne hb
          intro heq
          apply hnot ((mem_exitBoundary_iff Z₀ P R hR).2 ⟨hP,Or.inr (Or.inl ?_)⟩)
          exact heq



      filter_upwards [(PDE.isOpen_euclideanBall Z₀.velocity R).mem_nhds hpv] with v hv
      apply hmax
      rw [comparison_closure_forwardCylinder_eq]
      have hb := closure_forwardCylinder_bounds Z₀ R hR hP
      change (Z₀.time ≤ P.time ∧ P.time ≤ Z₀.time + R ^ 2) ∧
        relativePosition Z₀ P ∈ PDE.euclideanClosedBall 0 (R ^ 3) ∧
        v - Z₀.velocity ∈ PDE.euclideanClosedBall 0 R
      refine ⟨hb.1,hb.2.1,?_⟩
      simpa only [PDE.euclideanClosedBall, PDE.euclideanSqDist, mem_ofPred_eq, sub_zero] using (PDE.euclideanBall_subset_euclideanClosedBall _ _ hv)
    have hdiff := matrixContraction_sliceHessian_nonpos_of_localMax
      (hu.velocitySlice_contDiffAt (hQD hP)) hv hA
    rw [forwardKineticOperator_apply, kineticVelocityHessian_eq_sliceHessian]
    exact add_nonpos ht hdiff
  exact (not_le.mpr (hstrict P (hQD hP) hpos))
    _h_inl_16

end HypoellipticAleksandrov.KineticAleksandrov
