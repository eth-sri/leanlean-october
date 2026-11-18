module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Spectral
public import Mathlib.Analysis.Matrix.Spectrum
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SignsCutoff
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileJets
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCompact

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
section
open scoped MatrixOrder Matrix.Norms.L2Operator


/-- Positive spectral mass is a sum of nonnegative scalar positive parts. -/
theorem positiveSpectralMass_eq_sum {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian) :
    positiveSpectralMass M = ∑ i, max 0 (hM.eigenvalues i)  := by
  have trace_cfc_eq_sum (f : ℝ → ℝ) :
      (cfc f M).trace = ∑ i, f (hM.eigenvalues i) := by
    rw [hM.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
      Matrix.trace_mul_cycle]
    simp [Matrix.trace_diagonal, Function.comp_def]
  exact trace_cfc_eq_sum _

/-- Every Hermitian matrix has nonnegative positive spectral mass. -/
theorem positiveSpectralMass_nonneg {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian) :
    0 ≤ positiveSpectralMass M := by
  rw [positiveSpectralMass_eq_sum M hM]
  exact Finset.sum_nonneg (fun _ _ => le_max_left _ _)


/-- A positive quadratic-form direction gives strictly positive positive spectral mass. -/
theorem positiveSpectralMass_pos_of_direction {d : ℕ} (M : PDE.Mat d)
    (hM : M.IsHermitian) (w : PDE.Vec d) (hw : 0 < dotProduct w (M.mulVec w)) :
    0 < positiveSpectralMass M  := by
  have quadratic_nonpos_of_positiveSpectralMass_zero (hm : positiveSpectralMass M = 0) :
      dotProduct w (M.mulVec w) ≤ 0 := by
    have hs : ∀ i, hM.eigenvalues i ≤ 0 := by
      rw [positiveSpectralMass_eq_sum M hM] at hm
      intro i
      have hh := ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => le_max_left 0 (hM.eigenvalues i))).mp hm) i (Finset.mem_univ i)
      exact (le_max_right 0 _).trans (le_of_eq hh)
    have hnonpos : M ≤ 0 := by
      conv_lhs => rw [← cfc_id ℝ M hM.isSelfAdjoint]
      rw [← map_zero (algebraMap ℝ (PDE.Mat d))]
      apply cfc_le_algebraMap (id : ℝ → ℝ) 0 M

      intro t ht
      obtain ⟨i, rfl⟩ := hM.spectrum_real_eq_range_eigenvalues ▸ ht
      exact hs i
    have hh := (Matrix.nonneg_iff_posSemidef.mp (neg_nonneg.mpr hnonpos)).dotProduct_mulVec_nonneg w
    have hh' : 0 ≤ -dotProduct w (M.mulVec w) := by
      simpa only [Matrix.neg_mulVec, dotProduct_neg, star_trivial] using hh
    exact neg_nonneg.mp hh'
  apply lt_of_le_of_ne (positiveSpectralMass_nonneg M hM)
  intro hh
  exact (quadratic_nonpos_of_positiveSpectralMass_zero hh.symm).not_gt hw

/-- A negative quadratic-form direction gives strictly positive negative spectral mass. -/
theorem negativeSpectralMass_pos_of_direction {d : ℕ} (M : PDE.Mat d)
    (hM : M.IsHermitian) (w : PDE.Vec d) (hw : dotProduct w (M.mulVec w) < 0) :
    0 < negativeSpectralMass M := by
  apply positiveSpectralMass_pos_of_direction (-M) hM.neg w
  simpa only [Matrix.neg_mulVec, dotProduct_neg] using neg_pos.mpr hw

end

/-- A bilinear continuous derivative is the quadratic form of its native coordinate matrix. -/
theorem dotProduct_matrix_of_bilinear {d : ℕ}
    (B : PDE.Vec d →L[ℝ] PDE.Vec d →L[ℝ] ℝ) (w : PDE.Vec d) :
    dotProduct w (Matrix.mulVec (fun i k => B (Pi.single i 1) (Pi.single k 1)) w) = B w w := by
  have heq : w = ∑ i : Fin d, w i • Pi.single i 1 := by
    ext k
    simp [Pi.single_apply]
  conv_rhs => rw [heq]
  simp
  simp [dotProduct, Matrix.mulVec, sum_apply, smul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring


/-- The full-product velocity quadratic second jet. -/
def fullVelocityQuadratic {d : ℕ} (H : XV d → ℝ) (q : XV d) (w : PDE.Vec d) : ℝ :=
  fderiv ℝ (fun z => fderiv ℝ H z (0, w)) q (0, w)

/-- The profile's full velocity Hessian has the source cutoff prefactor at nonzero position. -/
theorem geometricProfile_quadratic_nonzero_position {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (q : XV d) (hx : q.1 ≠ 0) (w : PDE.Vec d) :
    fullVelocityQuadratic (geometricProfile alpha C₀ sigma R) q w =
      Real.rpow (PDE.vecEuclideanNorm q.1) ((alpha - 2) / 3) *
        cutoffHessian alpha C₀ sigma R (normalizedVelocity q.1 q.2) (positionDirection q.1) w := by
  have hq : q ≠ 0 := fun h => hx (congrArg Prod.fst h)
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hH := (geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma hR).contDiffAt
    (hopen.mem_nhds hq)
  have heq : (fun v => geometricProfile alpha C₀ sigma R (q.1, v)) =
      (fun v => homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) q.1 v) := by
    funext v
    simp only [geometricProfile, ite_eq_right hx]
  unfold fullVelocityQuadratic
  rw [show q = (q.1, q.2) from rfl,
    full_velocity_hessian_eq_slice _ q.1 q.2 w w hH, heq]
  exact homogeneousAnsatz_velocity_hessian alpha C₀ sigma R hsigma hR q.1 q.2 w w hx

/-- The full profile transport has the same source prefactor at nonzero position. -/
theorem geometricProfile_transport_nonzero_position {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (q : XV d) (hx : q.1 ≠ 0) :
    PDE.vecDot q.2 (dx (geometricProfile alpha C₀ sigma R) q) =
      Real.rpow (PDE.vecEuclideanNorm q.1) ((alpha - 2) / 3) *
        ansatzTransport alpha (cutoffProfile alpha C₀ sigma R)
          (normalizedVelocity q.1 q.2) (positionDirection q.1) := by
  have hq : q ≠ 0 := fun h => hx (congrArg Prod.fst h)
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hH := (geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma hR).contDiffAt
    (hopen.mem_nhds hq)
  rw [transport_eq_direction, ← fderiv_position_slice _ q.1 q.2 q.2
    (hH.differentiableAt (by simp))]
  have heq : (fun x => geometricProfile alpha C₀ sigma R (x, q.2)) =ᶠ[nhds q.1]
      (fun x => homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) x q.2) := by
    filter_upwards [continuous_id.continuousAt.eventually_ne hx] with x hx'
    change x ≠ 0 at hx'
    simp only [geometricProfile, ite_eq_right hx']
  rw [heq.fderiv_eq (𝕜 := ℝ)]
  apply homogeneousAnsatz_transport alpha _ q.1 q.2 hx
  exact (contDiff_cutoffProfile alpha C₀ sigma R hsigma hR).differentiable
    (by simp) (normalizedVelocity q.1 q.2, positionDirection q.1)

/-- The full velocity Hessian at zero position is the exact radial Hessian. -/
theorem geometricProfile_quadratic_zero_position {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (v w : PDE.Vec d) (hv : v ≠ 0) :
    fullVelocityQuadratic (geometricProfile alpha C₀ sigma R) (0, v) w =
      radialHessianForm alpha v w w := by
  have hq : ((0, v) : XV d) ≠ 0 := fun h => hv (congrArg Prod.snd h)
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hH := (geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma hR).contDiffAt
    (hopen.mem_nhds hq)
  have heq : (fun a => geometricProfile alpha C₀ sigma R ((0 : PDE.Vec d), a)) =
      radialProfile alpha := by
    funext a
    simp [geometricProfile]
  unfold fullVelocityQuadratic
  rw [full_velocity_hessian_eq_slice _ 0 v w w hH, heq]
  exact radialProfile_hessian alpha v w w hv


section
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Joint finite bounds for the canonical spectral weights imply matrix bounds. -/
theorem spectralTraceMatrix_uniform_bounds {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian)
    (b cminus lower upper : ℝ)
    (hlo : lower ≤ (b + cminus * negativeSpectralMass M) / positiveSpectralMass M)
    (hhi : (b + cminus * negativeSpectralMass M) / positiveSpectralMass M ≤ upper) :
    min 1 (min lower cminus) • (1 : PDE.Mat d) ≤ spectralTraceMatrix M b cminus ∧
      spectralTraceMatrix M b cminus ≤ max 1 (max upper cminus) • (1 : PDE.Mat d) := by
  rw [spectralTraceMatrix_eq_cfc M hM]
  have hcont : ContinuousOn (weightedSpectralSelector
      ((b + cminus * negativeSpectralMass M) / positiveSpectralMass M) cminus)
      (spectrum ℝ M) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  constructor
  · rw [← Algebra.algebraMap_eq_smul_one]
    apply algebraMap_le_cfc _ _ M
    intro t _
    unfold weightedSpectralSelector
    split_ifs
    · exact ((min_le_right _ _).trans (min_le_left _ _)).trans hlo
    · exact (min_le_right _ _).trans (min_le_right _ _)
    · exact min_le_left _ _
  · rw [← Algebra.algebraMap_eq_smul_one]
    apply cfc_le_algebraMap _ _ M
    intro t _
    unfold weightedSpectralSelector
    split_ifs
    · exact hhi.trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (le_max_right _ _).trans (le_max_right _ _)
    · exact le_max_left _ _

end

/-- Scalar directional evaluation of the local slice second derivative. -/
theorem secondDirectional_eq_at {d : ℕ} (F : PDE.Vec d → ℝ) (y w u : PDE.Vec d)
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F y) :
    fderiv ℝ (fun z => fderiv ℝ F z w) y u = fderiv ℝ (fderiv ℝ F) y u w := by
  have hd := (hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

/-- The native velocity matrix represents the literal full velocity quadratic jet. -/
theorem dvv_quadratic_eq {d : ℕ} (H : XV d → ℝ) (q : XV d) (w : PDE.Vec d)
    (hH : ContDiffAt ℝ (⊤ : ℕ∞) H q) :
    dotProduct w ((dvv H q).mulVec w) = fullVelocityQuadratic H q w := by
  let F := fun v => H (q.1, v)
  have hF :=
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

/-- The velocity Hessian matrix of a smooth punctured profile is continuous off the origin. -/
theorem continuousOn_dvv_off_origin {d : ℕ} (H : XV d → ℝ)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ)) : ContinuousOn (dvv H) ({0}ᶜ) := by
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro k
  have hscalar := (hH.fderiv_of_isOpen hopen (m := (⊤ : ℕ∞)) (by simp)).clm_apply (contDiffOn_const (c := ((0, Pi.single k 1) : XV d)))
  exact (hscalar.continuousOn_fderiv_of_isOpen hopen (by simp)).clm_apply
    (continuousOn_const)

/-- The classical full transport scalar is continuous off the origin. -/
theorem continuousOn_transport_off_origin {d : ℕ} (H : XV d → ℝ)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ)) :
    ContinuousOn (fun q => PDE.vecDot q.2 (dx H q)) ({0}ᶜ) := by
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hc : Continuous (fun q : XV d => (q.2, (0 : PDE.Vec d))) := by fun_prop
  simpa only [transport_eq_direction] using ((hH.continuousOn_fderiv_of_isOpen hopen (by simp)).clm_apply hc.continuousOn)

/-- The actual full profile discharges the spectral solver's sign conditions off the origin. -/
theorem exists_geometricProfile_spectral_signs (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C₀ sigma R : ℝ, 0 < C₀ ∧ 0 < sigma ∧ 2 < R ∧ ∀ q : XV d, q ≠ 0 →
      let H : XV d → ℝ := geometricProfile alpha C₀ sigma R
      (dvv H q).IsHermitian ∧ 0 < positiveSpectralMass (dvv H q) ∧
        (negativeSpectralMass (dvv H q) = 0 → 0 < PDE.vecDot q.2 (dx H q))  := by
  have exists_geometricProfile_sign_parameters :
      ∃ C₀ sigma R : ℝ, 0 < C₀ ∧ 0 < sigma ∧ 2 < R ∧
      ∀ q : XV d, q ≠ 0 →
        (∃ w, 0 < fullVelocityQuadratic (geometricProfile alpha C₀ sigma R) q w) ∧
        ((∃ w, fullVelocityQuadratic (geometricProfile alpha C₀ sigma R) q w < 0) ∨
          0 < PDE.vecDot q.2 (dx (geometricProfile alpha C₀ sigma R) q)) := by
    obtain ⟨C₀, sigma, R, hC₀, hsigma, hR2, hsign⟩ :=
      exists_cutoff_sign_parameters d hd alpha ha ha1
    have hR : 0 < R := lt_trans (by norm_num) hR2
    refine ⟨C₀, sigma, R, hC₀, hsigma, hR2, ?_⟩
    intro q hq
    by_cases hx : q.1 = 0
    · have hv : q.2 ≠ 0 := fun hv => hq (Prod.ext hx hv)
      obtain ⟨w, hw⟩ := radialHessian_positive_direction d hd alpha ha q.2 hv
      refine ⟨⟨w, ?_⟩, Or.inl ⟨q.2, ?_⟩⟩
      · rw [show q = (0, q.2) from Prod.ext hx rfl,
          geometricProfile_quadratic_zero_position alpha C₀ sigma R hsigma hR q.2 w hv]
        exact hw
      · rw [show q = (0, q.2) from Prod.ext hx rfl,
          geometricProfile_quadratic_zero_position alpha C₀ sigma R hsigma hR q.2 q.2 hv]
        exact radialHessian_radial_neg alpha ha ha1 q.2 hv
    · have hr : 0 < Real.rpow (PDE.vecEuclideanNorm q.1) ((alpha - 2) / 3) :=
        Real.rpow_pos_of_pos (PDE.vecEuclideanNorm_pos_iff.mpr hx) _
      obtain ⟨⟨w, hw⟩, hneg⟩ := hsign (normalizedVelocity q.1 q.2) (positionDirection q.1)
        (positionDirection_normSq q.1 hx)
      refine ⟨⟨w, ?_⟩, ?_⟩
      · rw [geometricProfile_quadratic_nonzero_position alpha C₀ sigma R hsigma hR q hx]
        exact mul_pos hr hw
      · rcases hneg with ⟨u, hu⟩ | hb
        · left
          refine ⟨u, ?_⟩
          rw [geometricProfile_quadratic_nonzero_position alpha C₀ sigma R hsigma hR q hx]
          exact mul_neg_of_pos_of_neg hr hu
        · right
          rw [geometricProfile_transport_nonzero_position alpha C₀ sigma R hsigma hR q hx]
          exact mul_pos hr (lt_of_lt_of_le zero_lt_one hb)
  obtain ⟨C₀, sigma, R, hC₀, hsigma, hR2, hsign⟩ :=
    exists_geometricProfile_sign_parameters
  have hR : 0 < R := lt_trans (by norm_num) hR2
  refine ⟨C₀, sigma, R, hC₀, hsigma, hR2, ?_⟩
  intro q hq
  let H : XV d → ℝ := geometricProfile alpha C₀ sigma R
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hH := (geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma hR).contDiffAt
    (hopen.mem_nhds hq)
  have hherm := dvv_isHermitian H q hH
  obtain ⟨⟨w, hw⟩, hneg⟩ := hsign q hq
  have hpos : 0 < positiveSpectralMass (dvv H q) := by
    apply positiveSpectralMass_pos_of_direction _ hherm w
    rwa [dvv_quadratic_eq H q w hH]
  refine ⟨hherm, hpos, ?_⟩
  intro hzero
  rcases hneg with ⟨u, hu⟩ | hb
  · have hmn : 0 < negativeSpectralMass (dvv H q) := by
      apply negativeSpectralMass_pos_of_direction _ hherm u
      rwa [dvv_quadratic_eq H q u hH]
    rw [hzero] at hmn
    exact hmn.false.elim
  · exact hb

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

