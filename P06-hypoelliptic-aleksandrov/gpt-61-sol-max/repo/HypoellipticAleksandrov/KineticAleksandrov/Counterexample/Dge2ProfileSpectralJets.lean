module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileSigns
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCutoffCompact
public import PDEFoundation.Calculus.RegularityOrder


/-! # Spectral sign and continuity interfaces discharged by the actual profile -/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Scalar directional evaluation of the local slice second derivative. -/
theorem secondDirectional_eq_at {d : ℕ} (F : PDE.Vec d → ℝ) (y w u : PDE.Vec d)
    (hF : ContDiffAt ℝ PDE.smoothOrder F y) :
    fderiv ℝ (fun z => fderiv ℝ F z w) y u = fderiv ℝ (fderiv ℝ F) y u w := by

  rw [fderiv_clm_apply ((hF.fderiv_right (m := PDE.smoothOrder) (by simp)).differentiableAt (by simp)) (differentiableAt_const w)]
  simp

variable {d : ℕ} (H : XV d → ℝ)

/-- The native velocity matrix represents the literal full velocity quadratic jet. -/
theorem dvv_quadratic_eq  (q : XV d) (w : PDE.Vec d)
    (hH : ContDiffAt ℝ PDE.smoothOrder H q) :
    dotProduct w ((dvv H q).mulVec w) = fullVelocityQuadratic H q w := by
  let F := fun v => H (q.1, v)
  have hF : ContDiffAt ℝ PDE.smoothOrder F q.2 :=
    hH.comp q.2 (contDiffAt_const.prodMk contDiffAt_id)
  have heq : dvv H q = fun i k => fderiv ℝ (fderiv ℝ F) q.2
      (Pi.single i 1) (Pi.single k 1) := by
    ext i k
    change fderiv ℝ (fun z => fderiv ℝ H z (0, Pi.single k 1))
      (q.1, q.2) (0, Pi.single i 1) = _
    rw [full_velocity_hessian_eq_slice H q.1 q.2 _ _ hH]
    exact secondDirectional_eq_at F q.2 _ _ hF
  rw [heq, dotProduct_matrix_of_bilinear]
  unfold fullVelocityQuadratic
  rw [show q = (q.1, q.2) from rfl, full_velocity_hessian_eq_slice H q.1 q.2 w w hH]
  exact (secondDirectional_eq_at F q.2 w w hF).symm

section
variable (hH : ContDiffOn ℝ PDE.smoothOrder H ({0}ᶜ))

include hH
/-- The velocity Hessian matrix of a smooth punctured profile is continuous off the origin. -/
theorem continuousOn_dvv_off_origin
     : ContinuousOn (dvv H) ({0}ᶜ) := by
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl

  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro k

  exact (((hH.fderiv_of_isOpen hopen (m := PDE.smoothOrder) (by simp)).clm_apply (contDiffOn_const (c := ((0, Pi.single k 1) : XV d)))).continuousOn_fderiv_of_isOpen hopen (by simp)).clm_apply
    (continuousOn_const )

/-- The classical full transport scalar is continuous off the origin. -/
theorem continuousOn_transport_off_origin
     :
    ContinuousOn (fun q => PDE.vecDot q.2 (dx H q)) ({0}ᶜ) := by


  have hh := (hH.continuousOn_fderiv_of_isOpen isClosed_singleton.isOpen_compl (by simp)).clm_apply (show Continuous (fun q : XV d => (q.2, (0 : PDE.Vec d))) by fun_prop).continuousOn
  simpa only [transport_eq_direction] using hh
end


/-- The actual full profile discharges the spectral solver's sign conditions off the origin. -/
theorem exists_geometricProfile_spectral_signs (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C₀ sigma R : ℝ, 0 < C₀ ∧ 0 < sigma ∧ 2 < R ∧ ∀ q : XV d, q ≠ 0 →
      let H : XV d → ℝ := geometricProfile alpha C₀ sigma R
      (dvv H q).IsHermitian ∧ 0 < positiveSpectralMass (dvv H q) ∧
        (negativeSpectralMass (dvv H q) = 0 → 0 < PDE.vecDot q.2 (dx H q)) := by
  obtain ⟨C₀, sigma, R, hC₀, hsigma, hR2, hsign⟩ :=
    exists_geometricProfile_sign_parameters d hd alpha ha ha1

  refine ⟨C₀, sigma, R, hC₀, hsigma, hR2, ?_⟩
  intro q hq
  let H : XV d → ℝ := geometricProfile alpha C₀ sigma R

  have hH := (geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma (lt_trans (by norm_num) hR2)).contDiffAt
    (isClosed_singleton.isOpen_compl.mem_nhds hq)
  have hherm := dvv_isHermitian H q hH
  obtain ⟨⟨w, hw⟩, hneg⟩ := hsign q hq

  refine ⟨hherm, (by
      apply positiveSpectralMass_pos_of_direction _ hherm w
      rwa [dvv_quadratic_eq H q w hH]), ?_⟩
  intro hzero
  rcases hneg with ⟨u, hu⟩ | hb
  · have hmn : 0 < negativeSpectralMass (dvv H q) := by
      apply negativeSpectralMass_pos_of_direction _ hherm u
      rwa [dvv_quadratic_eq H q u hH]
    rw [hzero] at hmn
    exact hmn.false.elim
  · exact hb

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
