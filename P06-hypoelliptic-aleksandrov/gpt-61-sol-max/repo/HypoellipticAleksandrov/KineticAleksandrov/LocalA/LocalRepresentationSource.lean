module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationWeak
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentation
public import PDEFoundation.Calculus.RegularityOrder


/-! # Correction of bounded classical residuals by the actual signed source potential -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo Evolution TheoremA

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

omit hH hLE hd hlam hLam B hB v₀ hR in
/-- The packed physical domain is precisely the swapped native domain. -/
theorem localRepresentation_native_domain (D : Set (KineticPoint d)) :
    massPhysicalPoint ⁻¹' D = evolutionHomeomorph d ⁻¹' (sectionTwoPoint '' D) := by
  ext x
  constructor
  · intro hx
    exact ⟨_, hx, rfl⟩
  · rintro ⟨P, hP, hEq⟩
    have hp : massPhysicalPoint x = P := congrArg sectionTwoPoint hEq.symm
    change massPhysicalPoint x ∈ D
    rw [hp]
    exact hP

/-- A bounded classical residual is canceled by its literal signed source potential. -/
theorem localRepresentation_source_correction
    (a T : ℝ) (haT : a < T) (u : HypoellipticAleksandrov.KineticScalarField d)
    (hu : IsKineticC112On u (localStrip a T v₀ R))
    (hc : ContinuousOn u (localClosedStrip a T v₀ R))
    (F : HypoellipticAleksandrov.KineticScalarField d) (hF : Measurable F)
    (he : ∀ P ∈ localStrip a T v₀ R,
      forwardKineticOperator (ofTimeVelocityCoefficient B) u P = F P)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ P ∈ localStrip a T v₀ R, |F P| ≤ M) :
    let E := fun P => u P + ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T F P
    ContDiffOn ℝ PDE.smoothOrder (E ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' localStrip a T v₀ R) ∧
    (∀ P ∈ localStrip a T v₀ R,
      forwardKineticOperator (ofTimeVelocityCoefficient B) E P = 0) ∧
    ContinuousOn E (localClosedStrip a T v₀ R) ∧
    EqOn E u (localTrace a T v₀ R) := by
  dsimp only
  let D := localStrip a T v₀ R
  let D' := sectionTwoPoint '' D
  let W := ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T F
  let E := fun P => u P + W P
  have hD : IsOpen D := isOpen_localStrip a T v₀ R
  have hD' : IsOpen D' := (sectionTwoHomeomorph d).isOpenMap _ hD
  obtain ⟨hWc, hWtr, _hWb⟩ := ballSourcePotential_bounded_traces hH hLE hd hlam hLam
    B hB v₀ hR a T M haT hM F hF hb
  have hw := ballSourcePotential_weak hH hLE hd hlam hLam B hB v₀ hR a T haT
    F hF ⟨M, hb⟩
  have hwn := (isWeakTransportedSolution_comp_iff _ _ _ _ _).2 hw
  rw [← localRepresentation_native_domain D] at hwn
  change IsWeakTransportedSolution (zIndependentCoefficient B) (identityDrift d)
    (massPhysicalPoint ⁻¹' D) (W ∘ massPhysicalPoint)
    (fun x => -F (massPhysicalPoint x)) at hwn
  have hun := localRepresentation_classical_weak B hB hD u hu

  have hcancel := localRepresentation_weak_cancel _
    _ (sectionTwoCoefficient_fullBounds lam Lam B hB).1
    (identityDrift_smooth d) _
    _ _ _ (by
        refine ⟨hun.1, ?_⟩
        intro ψ hψ hcompact hs
        exact (hun.2 ψ hψ hcompact hs).trans
          (setIntegral_congr_fun (hD.preimage continuous_massPhysicalPoint).measurableSet
            (fun x hx => by simp only [Function.comp_apply, he _ hx]))) hwn
  rw [localRepresentation_native_domain D] at hcancel
  have hEk : IsKineticWeakTransportedSolution (zIndependentCoefficient B) (identityDrift d)
      D' (E ∘ sectionTwoPoint) (fun _ => 0) :=
    (isWeakTransportedSolution_comp_iff _ _ _ _ _).1 hcancel
  have hEc : ContinuousOn E (localClosedStrip a T v₀ R) := hc.add hWc
  have hEsc : ContinuousOn (E ∘ sectionTwoPoint) D' :=
    (hEc.mono (localStrip_subset_closed a T v₀ R)).comp
      (continuous_sectionTwoPoint d).continuousOn (by
        rintro Q ⟨P, hP, rfl⟩
        exact hP)
  obtain ⟨hEsn, hEon⟩ := boundary_continuous_weak_smooth hH B hB D' hD'
    _ _ hEsc hEk contDiffOn_const

  refine ⟨(boundary_native_smooth_to_physical D E hEsn), ?_, hEc, ?_⟩
  · intro P hP
    let x := (evolutionHomeomorph d).symm (sectionTwoPoint P)
    have hx : x ∈ evolutionHomeomorph d ⁻¹' D' := by
      change evolutionHomeomorph d x ∈ D'
      rw [Homeomorph.apply_symm_apply]
      exact ⟨P, hP, rfl⟩
    have h := hEon x hx
    have hs : ContDiffAt ℝ 2 ((E ∘ sectionTwoPoint) ∘ evolutionHomeomorph d) x :=
      (hEsn.contDiffAt
        ((hD'.preimage (evolutionHomeomorph d).continuous).mem_nhds hx)).of_le (by simp)
    rw [transportedOperator_comp hs] at h
    dsimp only [x] at h
    rw [Homeomorph.apply_symm_apply] at h
    rw [forwardKineticOperator_eq_lop_identity B E]
    exact h
  · intro P hP
    change u P + W P = u P
    exact congrArg (fun t => u P + t) (hWtr P hP) |>.trans (add_zero _)

/-- The exit formula for bounded classical solutions with a bounded measurable residual. -/
theorem localRepresentation_bounded_source_formula
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (u : HypoellipticAleksandrov.KineticScalarField d)
    (hu : IsKineticC112On u (localStrip P.1.time T.1 v₀ R))
    (hc : ContinuousOn u (localClosedStrip P.1.time T.1 v₀ R))
    (hub : ∃ L : ℝ, ∀ Q ∈ localClosedStrip P.1.time T.1 v₀ R, |u Q| ≤ L)
    (F : HypoellipticAleksandrov.KineticScalarField d) (hF : Measurable F)
    (he : ∀ Q ∈ localStrip P.1.time T.1 v₀ R,
      forwardKineticOperator (ofTimeVelocityCoefficient B) u Q = F Q)
    (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ Q ∈ localStrip P.1.time T.1 v₀ R, |F Q| ≤ M) :
    u P.1 + ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR P.1.time T.1 F P.1 =
      ∫ Q, u Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T := by
  let sharedTerm_91bb3e3983 := (M * (T.1 - P.1.time))
  let W := ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR P.1.time T.1 F
  let E := fun Q => u Q + W Q
  obtain ⟨hEs, hEe, hEc, hEtr⟩ := localRepresentation_source_correction
    hH hLE hd hlam hLam B hB v₀ hR P.1.time T.1 T.2 u hu hc F hF he M hM hb
  obtain ⟨hWc, _hWtr, hWb⟩ := ballSourcePotential_bounded_traces hH hLE hd hlam hLam
    B hB v₀ hR P.1.time T.1 M T.2 hM F hF hb

  obtain ⟨L, hL⟩ := hub

  have hEr : IsKineticC112On E (localStrip P.1.time T.1 v₀ R) :=
    isKineticC112On_of_contDiffOn (isOpen_localStrip P.1.time T.1 v₀ R)
      (boundary_physical_smooth_to_native hEs)
  have hid := ballExit_represents hH hLE hd hlam hLam B hB v₀ hR P T E hEc hEr (by
      refine ⟨L + sharedTerm_91bb3e3983, fun Q hQ => ?_⟩
      exact (abs_add_le (u Q) (W Q)).trans (add_le_add (hL Q hQ) ((show ∀ Q ∈ localClosedStrip P.1.time T.1 v₀ R,
      |W Q| ≤ sharedTerm_91bb3e3983 by

          have hcl := le_on_closure (by
              intro Q hQ
              exact (hWb Q hQ).trans (mul_le_mul_of_nonneg_left
                ((min_le_left _ _).trans (sub_le_sub_left hQ.1.le T.1)) hM))
            (by rw [closure_localStrip T.2]; exact hWc.abs) continuousOn_const
          intro Q hQ
          exact hcl (by rwa [closure_localStrip T.2])) Q hQ))) hEe
  refine hid.trans (integral_congr_ae ?_)
  filter_upwards [ballExitRaw_ae_trace hH hLE hd hlam hLam B hB v₀ hR P T] with Q hQ
  exact hEtr hQ

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
