module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationGreen
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ConeSupport
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ConeSupportTransition
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationBounds

/-! # Exit representation for a solution defined only on its kinetic cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter MeasureTheory Parabolic SectionTwo
open TheoremA
open scoped Topology

/- The actual velocity-ball exit measure represents the source's local solution class. -/
theorem local_cone_representation
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d } (hd : 1 ≤ d) {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R } (hR : 0 < R)
    (Z₀ : KineticPoint d) (U : KineticPoint d → ℝ)
    (hUc : ContinuousOn U (closure (forwardCylinder Z₀ R hR)))
    (hUs : IsKineticC112On U (forwardCylinder Z₀ R hR))
    (hUe : ∀ Q ∈ forwardCylinder Z₀ R hR,
      forwardKineticOperator (ofTimeVelocityCoefficient B) U Q = 0)
    (P : LocalBallStart v₀ R) (hPv : v₀ = Z₀.velocity)
    (hP : P.1 ∈ forwardCylinder Z₀ (3 * R / 4) (by positivity))
    (T : {t : ℝ // P.1.time < t}) (hT : T.1 - P.1.time = R ^ 2 / 8) :
    U P.1 = ∫ Q, U Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T := by
  subst v₀
  obtain ⟨χ, hχ, _hχcompact, hs, _hχb, hχone⟩ : ∃ χ : PDE.Vec (d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ PDE.euclideanBall 0 (R ^ 3) ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      ∀ x ∈ PDE.euclideanClosedBall 0 ((3 / 4 : ℝ) * R ^ 3), χ x = 1 := by
    let d := (d)
    apply exists_smooth_bump_of_isCompact_subset_isOpen
      (PDE.isCompact_euclideanClosedBall 0 (by positivity))
      (PDE.isOpen_euclideanBall 0 (R ^ 3))
    exact PDE.euclideanClosedBall_subset_euclideanBall (by positivity)
      (by nlinarith only [pow_pos hR 3])
  let V := localCutoffSolution Z₀ χ U
  let F := (localStrip P.1.time T.1 Z₀.velocity R).indicator
    (fun Q => localCutoffTransport Z₀ χ Q * U Q)
  have ha := hP.1
  have htop : T.1 < Z₀.time + R ^ 2 := by
    have hpt := hP.2.1
    nlinarith only [hpt, hT, sq_pos_of_pos hR]
  have hrel : Continuous (relativePosition Z₀) :=
    (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  have hVc := localCutoffSolution_continuousOn Z₀ hR ha.le htop.le U hUc χ hχ.continuous hs
  have hUb := localRepresentation_supported_mul_bounded Z₀ hR ha.le htop.le U hUc χ hs
    (localPositionCutoff Z₀ χ) (hχ.continuous.comp hrel)
    (fun Q hx => by
      change χ (relativePosition Z₀ Q) = 0
      exact image_eq_zero_of_notMem_tsupport hx)
  obtain ⟨L, _hL, hVb⟩ := hUb
  have hsm := mass_classical_homogeneous_smooth hH B hB
    (isOpen_forwardCylinder Z₀ R hR) U hUs hUe
  have hVs := localCutoffSolution_contDiffOn Z₀ hR ha htop U hsm χ hχ hs
  have hVr :=
    TheoremA.isKineticC112On_of_contDiffOn (isOpen_localStrip P.1.time T.1 Z₀.velocity R)
      (boundary_physical_smooth_to_native hVs)
  have hfc := localRepresentation_supported_mul_continuousOn Z₀ hR ha.le htop.le U hUc
    χ hs (localCutoffTransport Z₀ χ) (continuous_localCutoffTransport Z₀ hχ)
    (fun Q hx => localCutoffTransport_zero Z₀ Q χ hx)
  have hFm : Measurable F := localRepresentation_indicator_measurable _ _ _ _ _
    (hfc.mono (localStrip_subset_closed P.1.time T.1 Z₀.velocity R))
  obtain ⟨M, hM, hFb⟩ := localRepresentation_supported_mul_bounded Z₀ hR ha.le htop.le
    U hUc χ hs (localCutoffTransport Z₀ χ) (continuous_localCutoffTransport Z₀ hχ)
    (fun Q hx => localCutoffTransport_zero Z₀ Q χ hx)
  have hFe : ∀ Q ∈ localStrip P.1.time T.1 Z₀.velocity R,
      forwardKineticOperator (ofTimeVelocityCoefficient B) V Q = F Q := by
    intro Q hQ
    change forwardKineticOperator (ofTimeVelocityCoefficient B)
      (localCutoffSolution Z₀ χ U) Q =
      (localStrip P.1.time T.1 Z₀.velocity R).indicator
        (fun Q => localCutoffTransport Z₀ χ Q * U Q) Q
    rw [indicator_of_mem hQ]
    by_cases hx : relativePosition Z₀ Q ∈ tsupport χ
    · have houter : Q ∈ forwardCylinder Z₀ R hR :=
        ⟨ha.trans hQ.1, hQ.2.1.trans htop, hQ.2.2, hs hx⟩
      rw [localCutoffSolution_operator Z₀ _ hχ hUs houter, hUe Q houter,
        mul_zero, zero_add]
    · rw [localCutoffSolution_operator_zero Z₀ Q _ χ U hx,
        localCutoffTransport_zero Z₀ Q χ hx, zero_mul]
  have hFbound : ∀ Q ∈ localStrip P.1.time T.1 Z₀.velocity R, |F Q| ≤ M := by
    intro Q hQ
    change |(localStrip P.1.time T.1 Z₀.velocity R).indicator
      (fun Q => localCutoffTransport Z₀ χ Q * U Q) Q| ≤ M
    rw [indicator_of_mem hQ]
    exact hFb Q (localStrip_subset_closed _ _ _ _ hQ)
  have hid := localRepresentation_bounded_source_formula hH hLE hd hlam hLam B hB
    Z₀.velocity hR P T V hVr hVc ⟨L, hVb⟩ F hFm hFe M hM hFbound
  have hz : ballSourcePotential hH hLE hd hlam hLam B hB Z₀.velocity hR P.1.time T.1
      ((localStrip P.1.time T.1 Z₀.velocity R).indicator
        (fun Q => localCutoffTransport Z₀ χ Q * U Q)) P.1 = 0 := by
    classical
    unfold ballSourcePotential duhamelPotential
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro r hr
    have hvalid : (sectionTwoPoint P.1).time ≤ r ∧
        (sectionTwoPoint P.1).position ∈
          movingDomain (PDE.euclideanBall Z₀.velocity R) (fun _ => 0)
            (sectionTwoPoint P.1).time := by
      exact ⟨hr.1.le, (movingDomain_ball_zero _ _ _).symm ▸ P.2⟩
    rw [duhamelIntegrand, dite_eq_left hvalid]
    change (∫ w, (localStrip P.1.time T.1 Z₀.velocity R).indicator
      ((localStrip P.1.time T.1 Z₀.velocity R).indicator
        (fun Q => localCutoffTransport Z₀ χ Q * U Q))
          (⟨r, w.2, w.1⟩ : KineticPoint d)
      ∂ballTransition hH hLE hd hlam hLam B hB Z₀.velocity hR P ⟨r, hr.1⟩) = 0
    apply integral_eq_zero_of_ae
    filter_upwards [ballTransition_cone hH hLE hd hlam hLam B hB Z₀.velocity hR
      P ⟨r, hr.1⟩] with w hw
    have ht : r ≤ P.1.time + R ^ 2 / 8 := by linarith only [hr.2, hT]
    have hx := local_cone_cutoff_mem Z₀ P.1 ⟨r, w.2, w.1⟩ hR hP hr.1.le ht hw
    have hz := localCutoffTransport_zero_of_one Z₀ ⟨r, w.2, w.1⟩ χ hχone hx
    by_cases hmem : (⟨r, w.2, w.1⟩ : KineticPoint d) ∈
        localStrip P.1.time T.1 Z₀.velocity R
    · rw [indicator_of_mem hmem, indicator_of_mem hmem, hz, zero_mul]
      rfl
    · rw [indicator_of_notMem hmem]
      rfl
  change V P.1 + ballSourcePotential hH hLE hd hlam hLam B hB Z₀.velocity hR
    P.1.time T.1 F P.1 = _ at hid
  rw [hz, add_zero] at hid
  have hstart : V P.1 = U P.1 := by
    have hx := local_cone_cutoff_mem Z₀ P.1 P.1 hR hP le_rfl
      (by nlinarith only [sq_nonneg R]) (by
        have hz : PDE.vecEuclideanNorm (0 : PDE.Vec d) = 0 :=
          PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl
        simp only [sub_self, zero_smul, hz, mul_zero]
        exact le_rfl)
    change χ (relativePosition Z₀ P.1) * U P.1 = U P.1
    rw [hχone _ (PDE.euclideanBall_subset_euclideanClosedBall _ _ hx), one_mul]
  rw [hstart] at hid
  refine hid.trans (integral_congr_ae ?_)
  filter_upwards [ballExitRaw_cone hH hLE hd hlam hLam B hB Z₀.velocity hR P T]
    with Q hQ
  have ht : Q.time ≤ P.1.time + R ^ 2 / 8 := by linarith only [hQ.2.1, hT]
  have hx := local_cone_cutoff_mem Z₀ P.1 Q hR hP hQ.1 ht hQ.2.2
  change χ (relativePosition Z₀ Q) * U Q = U Q
  rw [hχone _ (PDE.euclideanBall_subset_euclideanClosedBall _ _ hx), one_mul]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
