module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSourceProfile

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffProfileChain
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningProfile
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyWeakCoordinates
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffProfileSobolev
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffSecondBounds
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffWeak
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffWeakSecond
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.MetricSpace.ProperSpace
import PDEFoundation.Sobolev.W1p.Smooth

/-! # Global compact-test identities for the explicit cutoff jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory
open Set
open scoped ENNReal

/- The literal cutoff value before the fixed collar extension, in packed coordinates. -/
def spatialPackedCutoffValue {d alpha} (h : CounterProfileStatement d alpha)
    (r mu R t : ℝ) (x : PDE.Vec (d + d)) : ℝ :=
  timeCutoffTheta (selectedFlatProfile h r (spatialCoordinateCLE d x) -
    spatialPackedBarrier d mu R t x)

/- The first chain-rule representative, including the derivative of the barrier. -/
def spatialPackedCutoffGradient {d alpha} (h : CounterProfileStatement d alpha)
    (r mu R t : ℝ) (x : PDE.Vec (d + d)) (i : Fin (d + d)) : ℝ :=
  deriv timeCutoffTheta (selectedFlatProfile h r (spatialCoordinateCLE d x) -
    spatialPackedBarrier d mu R t x) *
    (spatialPackedGradient (flatProfilePositionJet h r) (flatProfileVelocityJet h r) x i -
      PDE.classicalGradient (spatialPackedBarrier d mu R t) x i)

/- The velocity Hessian representative includes the favorable convexity term. -/
def spatialPackedCutoffVelocityHessian {d alpha}
    (h : CounterProfileStatement d alpha) (r mu R t : ℝ)
    (x : PDE.Vec (d + d)) (i k : Fin d) : ℝ :=
  let s := selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x
  let g := fun j => flatProfileVelocityJet h r (spatialCoordinateCLE d x) j -
    PDE.classicalGradient (spatialPackedBarrier d mu R t) x (Fin.natAdd d j)
  deriv timeCutoffTheta s *
    (flatProfileHessian h r (spatialCoordinateCLE d x) i k -
      PDE.classicalGradient
        (fun y => PDE.classicalGradient (spatialPackedBarrier d mu R t) y (Fin.natAdd d k))
        x (Fin.natAdd d i)) +
    deriv (deriv timeCutoffTheta) s * g i * g k

/- The actual first cutoff jets satisfy global compact-test identities. -/
theorem spatialPackedCutoff_weak_first_of_profile
    {d } (hd : 1 ≤ d) {alpha } (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (mu R t : ℝ) (i : Fin (d + d)) (test : PDE.Vec (d + d) → ℝ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) test) (hs : HasCompactSupport test) :
    (∫ x, spatialPackedCutoffValue h r mu R t x * fderiv ℝ test x (PDE.basisVec i)) =
      -(∫ x, spatialPackedCutoffGradient h r mu R t x i * test x) := by
  apply weakPartial_global_of_locals i _ _ _ test ht hs
  intro D hD
  exact weakGradient_timeCutoffProfile_of_flatProfile_source
    flatProfile_source hd ha ha1 h r hr hD mu R t i

/- The proved flattened-profile theorem discharges the complete source interface. -/
theorem spatialPackedCutoff_velocityJet_weak_of_profile
    {d } (hd : 1 ≤ d) {alpha } (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (mu R t : ℝ) (i k : Fin d) (test : PDE.Vec (d + d) → ℝ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) test) (hs : HasCompactSupport test) :
    (∫ x, spatialPackedCutoffGradient h r mu R t x (Fin.natAdd d k) *
      fderiv ℝ test x (PDE.basisVec (Fin.natAdd d i))) =
      -(∫ x, spatialPackedCutoffVelocityHessian h r mu R t x i k * test x) := by
  apply weakPartial_global_of_locals (Fin.natAdd d i) _ _ _ test ht hs
  intro D hD
  have _h_xinl_0 :
      let u := fun x => selectedFlatProfile h r (spatialCoordinateCLE d x)
          let B := spatialPackedBarrier d mu R t
          let gv := fun x j => flatProfileVelocityJet h r (spatialCoordinateCLE d x) j -
            PDE.classicalGradient B x (Fin.natAdd d j)
          PDE.HasWeakPartialDerivOn D (Fin.natAdd d i)
            (fun x => deriv timeCutoffTheta (u x - B x) * gv x k)
            (fun x => deriv timeCutoffTheta (u x - B x) *
              (flatProfileHessian h r (spatialCoordinateCLE d x) i k -
                PDE.classicalGradient
                  (fun y => PDE.classicalGradient B y (Fin.natAdd d k)) x (Fin.natAdd d i)) +
              deriv (deriv timeCutoffTheta) (u x - B x) * gv x i * gv x k) := by
    let u := flatProfileW1p_of_flatProfile_source flatProfile_source hd ha ha1 h r hr hD
    have hw : PDE.HasWeakPartialDerivOn D (Fin.natAdd d i)
        (fun x => u.grad x (Fin.natAdd d k))
        (fun x => flatProfileHessian h r (spatialCoordinateCLE d x) i k) := by
      have _h_xinl_0 : PDE.HasWeakPartialDerivOn D (Fin.natAdd d i) (fun x => flatProfileVelocityJet h r (spatialCoordinateCLE d x) k) (fun x => flatProfileHessian h r (spatialCoordinateCLE d x) i k) := by
        obtain ⟨_, _, _, _, _, _, _, _, _, hw, _, _⟩ := flatProfile_source hd ha ha1 h r hr
        apply weakPartial_on_of_global
        intro test ht hs
        apply weak_directional_spatialCoordinate (fun q => flatProfileVelocityJet h r q k)
          (fun q => flatProfileHessian h r q i k) (0, PDE.basisVec i)
          (PDE.basisVec (Fin.natAdd d i)) (spatialCoordinate_basis_velocity i) _ test ht hs
        intro test ht hs
        apply weak_first_jet_of_second (selectedFlatProfile h r) _ _
          (0, PDE.basisVec k) (0, PDE.basisVec i) _ _ test ht hs
        · intro test ht hs
          exact (hw test (ht.of_le (by simp)) hs).2.1 k
        · intro test ht hs
          have he := (hw test (ht.of_le (by simp)) hs).2.2 i k
          simpa only [dvv, dv, PDE.basisVec,
            smooth_test_second_swap test (ht.of_le (by simp))] using! he
      simpa only [u, flatProfileW1p_of_flatProfile_source, spatialPackedGradient, Fin.addCases_right] using! _h_xinl_0
    have hm : PDE.MemLpOn D 2 (fun x => flatProfileHessian h r (spatialCoordinateCLE d x) i k) := by
      let p := 2
      obtain ⟨_, _, _, hm, hb, _, _, _, _, _, _, _⟩ := flatProfile_source hd ha ha1 h r hr
      apply memLp_spatialCoordinate_of_compact_bound hD _ (hm i k)
      intro K hK
      obtain ⟨M, _, hM⟩ := hb K hK
      exact ⟨M, fun q hq => by simpa only [Real.norm_eq_abs] using (hM q hq).2.2 i k⟩
    obtain ⟨M, hM, hb⟩ := timeCutoffTheta_deriv2_abs_bound
    have he := weakSecond_cutoff_sub_smooth hD u (spatialPackedBarrier d mu R t)
      (contDiff_spatialPackedBarrier d mu R t) (Fin.natAdd d i) (Fin.natAdd d k)
      _ hm hw timeCutoffTheta (contDiff_timeCutoffTheta.of_le (by simp)) M hM.le hb
    simpa only [u, flatProfileW1p_of_flatProfile_source, spatialPackedGradient,
      Fin.addCases_right] using! he
  simpa only [spatialPackedCutoffGradient, spatialPackedCutoffVelocityHessian, spatialPackedGradient, Fin.addCases_right] using! _h_xinl_0

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
