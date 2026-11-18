module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSourceProfile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoff
import Mathlib.Analysis.Calculus.FDeriv.Prod
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.BarrierPackedJets
import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ExtensionGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeRegularityCompact
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.DenselyOrdered

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped MatrixOrder

/-- Position slice derivatives equal the product selectors at a differentiability point. -/
theorem dx_eq_classicalGradient_at {d : ℕ} (f : XV d → ℝ) (q : XV d)
    (hf : DifferentiableAt ℝ f q) :
    dx f q = PDE.classicalGradient (fun x => f (x, q.2)) q.1 := by
  funext i
  unfold dx PDE.classicalGradient PDE.basisVec
  rw [fderiv_fun_comp q.1 hf
    (differentiableAt_id.prodMk (differentiableAt_const q.2))]
  have hinj := DifferentiableAt.fderiv_prodMk
    (differentiableAt_id (𝕜 := ℝ) (x := q.1)) (differentiableAt_const q.2)
  simp at hinj
  rw [hinj]
  simp

/-- Velocity slice derivatives equal the product selectors at a differentiability point. -/
theorem dv_eq_classicalGradient_at {d : ℕ} (f : XV d → ℝ) (q : XV d)
    (hf : DifferentiableAt ℝ f q) :
    dv f q = PDE.classicalGradient (fun v => f (q.1, v)) q.2 := by
  funext i
  unfold dv PDE.classicalGradient PDE.basisVec
  rw [fderiv_fun_comp q.2 hf
    ((differentiableAt_const q.1).prodMk differentiableAt_id)]
  have hinj := DifferentiableAt.fderiv_prodMk (differentiableAt_const q.1)
    (differentiableAt_id (𝕜 := ℝ) (x := q.2))
  simp at hinj
  rw [hinj]
  simp

/-- Second velocity slice derivatives agree with product selectors at a C2 point. -/
theorem dvv_eq_sliceHessian_at {d : ℕ} (f : XV d → ℝ) (q : XV d)
    (hf : ContDiffAt ℝ 2 f q) :
    dvv f q = Parabolic.kineticVelocityHessian (fun P => f (P.position, P.velocity))
      ⟨0, q.1, q.2⟩ := by
  have hloc : (fun v => PDE.classicalGradient (fun w => f (q.1, w)) v) =ᶠ[nhds q.2]
      (fun v => dv f (q.1, v)) := by
    have hc : ContinuousAt (fun v => (q.1, v)) q.2 :=
      continuousAt_const.prodMk continuousAt_id
    filter_upwards [hc.eventually (hf.eventually (by norm_num))] with v hv
    exact (dv_eq_classicalGradient_at f (q.1, v)
      (hv.differentiableAt (by norm_num))).symm
  funext i k
  unfold Parabolic.kineticVelocityHessian
  rw [hloc.fderiv_eq]
  have hdv : DifferentiableAt ℝ (dv f) q := by
    have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    apply differentiableAt_pi.mpr
    intro j
    exact (hd.clm_apply (differentiableAt_const (0, Pi.single j 1)))
  unfold dvv PDE.basisVec
  rw [fderiv_apply hdv k, fderiv_fun_comp q.2 hdv
    ((differentiableAt_const q.1).prodMk differentiableAt_id)]
  have hinj := DifferentiableAt.fderiv_prodMk (differentiableAt_const q.1)
    (differentiableAt_id (𝕜 := ℝ) (x := q.2))
  simp at hinj
  rw [hinj]
  simp


/-- Contraction of the full positive second-chain representative. -/
theorem contraction_cutoff_identity {d : ℕ} (A B : PDE.Mat d)
    (w : PDE.Vec d) (s t : ℝ) :
    matrixContraction A (fun i k => s * B i k + t * w i * w k) =
      s * matrixContraction A B + t * PDE.vecDot (A.mulVec w) w := by
  simpa using
    contraction_flattening_identity A B w (-s) (-t)

/-- Contraction distributes over an entrywise difference. -/
theorem contraction_sub_right {d : ℕ} (A B C : PDE.Mat d) :
    matrixContraction A (fun i k => B i k - C i k) =
      matrixContraction A B - matrixContraction A C := by
  simp only [matrixContraction, mul_sub, Finset.sum_sub_distrib]

/-- The cutoff source representative uses the actual first and second weak jets.
The time derivative of the stationary profile vanishes. -/
def timeCutoffSourceRepresentative {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) (P : KineticPoint d) : ℝ :=
  let q := (P.position, P.velocity)
  let s := selectedFlatProfile h r q - barrier mu R P
  let w := flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R) P
  (-(deriv timeCutoffTheta s) * kineticTimeDerivative (barrier mu R) P) +
    PDE.vecDot P.velocity (fun i => deriv timeCutoffTheta s * flatProfilePositionJet h r q i) -
    matrixContraction (profileMatrix h q) (fun i k =>
      deriv timeCutoffTheta s *
        (flatProfileHessian h r q i k - kineticVelocityHessian (barrier mu R) P i k) +
      deriv (deriv timeCutoffTheta) s * w i * w k)


/-- The actual selected stationary source is nonnegative almost everywhere. -/
theorem flatSource_nonneg_ae_of_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ q ∂volume, 0 ≤ flatSource (profileMatrix h) (profileFunction h)
      flatteningPsi alpha r q := by
  obtain ⟨hlam, _, _, _, _, hA, _⟩ := selectedProfile_spec h
  filter_upwards [flatSource_ae_eq_jet_of_profile h r] with q hq
  rw [hq]
  unfold flatSourceWithJet
  exact mul_nonneg
    (mul_nonneg (Real.rpow_pos_of_pos hr _).le (flatteningPsi_deriv2_nonneg _))
    (quadratic_nonneg_of_loewner _ hlam.le _ (hA q).1 _)

/-- The favorable convexity term and barrier sign bound the weak source by the shell source. -/
theorem timeCutoff_source_le_of_profile {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (R : ℝ) (hR : 0 < R) (t : ℝ) :
    ∀ᵐ q ∂volume,
      timeCutoffSourceRepresentative h r ((d : ℝ) * profileLowerEllipticity h / R ^ 2) R
        ⟨t, q.1, q.2⟩ ≤
        flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q  := by
  have timeCutoff_source_identity_of_profile (mu : ℝ) :
      ∀ᵐ q ∂volume,
      timeCutoffSourceRepresentative h r mu R ⟨t, q.1, q.2⟩ =
        deriv timeCutoffTheta (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩) *
          (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q -
            backwardOperator (fun _t x v => profileMatrix h (x, v))
              (barrier mu R) ⟨t, q.1, q.2⟩) -
        deriv (deriv timeCutoffTheta)
          (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩) *
          PDE.vecDot ((profileMatrix h q).mulVec
            (flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R)
              ⟨t, q.1, q.2⟩))
            (flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R)
              ⟨t, q.1, q.2⟩) := by
    filter_upwards [flatProfile_representatives_source h r] with q hq
    unfold timeCutoffSourceRepresentative
    have he := contraction_cutoff_identity (profileMatrix h q)
      (fun i k => flatProfileHessian h r q i k -
        kineticVelocityHessian (barrier mu R) ⟨t, q.1, q.2⟩ i k)
      (flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R) ⟨t, q.1, q.2⟩)
      (deriv timeCutoffTheta (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩))
      (deriv (deriv timeCutoffTheta)
        (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩))
    simp only [Pi.sub_apply, Prod.mk.eta] at he ⊢
    rw [he, contraction_sub_right]
    rw [backwardOperator_apply, barrier_positionGradient]
    simp [PDE.vecDot, fullKineticCoefficientAt_apply] at hq ⊢
    have hdot (a : ℝ) :
        (∑ i, q.2 i * (a * flatProfilePositionJet h r q i)) =
          a * ∑ i, q.2 i * flatProfilePositionJet h r q i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hdot, ← hq]
    ring
  obtain ⟨hlam, _, _, _, _, hA, _⟩ := selectedProfile_spec h
  let mu := (d : ℝ) * profileLowerEllipticity h / R ^ 2
  filter_upwards [timeCutoff_source_identity_of_profile mu,
    flatSource_nonneg_ae_of_profile h r hr] with q he hf
  rw [he]
  have htheta := timeCutoffTheta_deriv_bounds
    (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩)
  have hterm := mul_nonneg (timeCutoffTheta_deriv2_nonneg
    (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩)) (quadratic_nonneg_of_loewner _ hlam.le _ (hA q).1 (flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R) ⟨t, q.1, q.2⟩))
  have hfirst := mul_le_mul_of_nonneg_left (sub_le_self
    (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q) (barrier_operator_nonneg hd (profileMatrix h) (profileLowerEllipticity h) R hlam hR (fun y => (hA y).1) ⟨t, q.1, q.2⟩)) htheta.1
  exact (sub_le_self _ hterm).trans (hfirst.trans (mul_le_of_le_one_left hf htheta.2))


/-- The native spatial slice of the barrier is smooth at every finite order. -/
theorem contDiff_nativeBarrier (d : ℕ) (mu R t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : XV d => barrier mu R ⟨t, q.1, q.2⟩) := by
  simpa only [barrier] using!
    (contDiff_const).mul ((contDiff_const (c := 2)).sub
      ((PDE.contDiff_vecNormSq.comp contDiff_snd).div_const (R ^ 2)))

/-- The cutoff's time derivative differentiates only the explicit exponential barrier. -/
theorem timeCutoffProfile_timeDerivative {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) (P : KineticPoint d) :
    kineticTimeDerivative (timeCutoffProfile (profileFunction h) alpha r mu R) P =
      -deriv timeCutoffTheta (selectedFlatProfile h r (P.position, P.velocity) -
        barrier mu R P) * kineticTimeDerivative (barrier mu R) P := by
  have hb := (((hasDerivAt_id P.time).const_mul (-mu)).exp).mul_const
    (2 - PDE.vecNormSq P.velocity / R ^ 2)
  have hi := hb.const_sub (selectedFlatProfile h r (P.position, P.velocity))
  have ht : DifferentiableAt ℝ timeCutoffTheta
      (selectedFlatProfile h r (P.position, P.velocity) - barrier mu R P) :=
    (contDiff_timeCutoffTheta.differentiable (by simp)).differentiableAt
  have he := ht.hasDerivAt.comp P.time hi
  change HasDerivAt
    (fun s => timeCutoffProfile (profileFunction h) alpha r mu R
      ⟨s, P.position, P.velocity⟩) _ P.time at he
  change deriv (fun s => timeCutoffProfile (profileFunction h) alpha r mu R
    ⟨s, P.position, P.velocity⟩) P.time = _
  rw [he.deriv, barrier_timeDerivative]
  simp only [selectedFlatProfile, barrier, id_eq, mul_one]
  ring



/-- On the profile domain the negative-time splice equals the raw cutoff at every time. -/
theorem zeroExtendedProfile_eq_raw_on_profile {d : ℕ} (H : XV d → ℝ)
    (alpha r mu R : ℝ) (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R)
    (hvel : ∀ q, H q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2)
    (P : KineticPoint d) (hq : H (P.position, P.velocity) < 1) :
    zeroExtendedProfile H alpha r mu R P = timeCutoffProfile H alpha r mu R P  := by
  have timeCutoffProfile_eq_zero_of_nonpos_time (ht : P.time ≤ 0) (hv : PDE.vecNormSq P.velocity < R ^ 2) :
      timeCutoffProfile H alpha r mu R P = 0 := by
    have hb : 1 < 2 - PDE.vecNormSq P.velocity / R ^ 2 := by
      have he := (div_lt_one (sq_pos_of_pos hR)).mpr hv
      linarith
    have hbar : 1 ≤ barrier mu R P := by
      unfold barrier
      exact (Real.one_le_exp_iff.mpr (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hmu.le) ht)).trans (le_mul_of_one_le_right (Real.exp_pos _).le hb.le)
    unfold timeCutoffProfile
    apply timeCutoffTheta_eq_zero
    exact sub_nonpos.mpr ((flatProfile_le_one H alpha r hr _).trans hbar)
  by_cases ht : 0 < P.time
  · simp [zeroExtendedProfile, ht, hq, and_self]
  · rw [zeroExtendedProfile_eq_zero_of_time H alpha r mu R P (not_lt.mp ht)]
    exact (timeCutoffProfile_eq_zero_of_nonpos_time
      (not_lt.mp ht) (hvel _ hq.le)).symm


/-- Spatial smoothing of the actual zero extension is globally jointly smooth.
The integration carrier is the fixed compact profile domain; no time smoothing is used. -/
theorem spatial_zeroExtendedProfile_contDiff_of_profile {d : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha)
    (r mu R : ℝ) (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2)
    (phi : ContDiffBump (0 : XV d)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × XV d => spatialMollify phi
      (fun y => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨z.1, y.1, y.2⟩) z.2) := by
  let K : Set (XV d) := {q | profileFunction h q ≤ 1}
  let Omega : Set (XV d) := {q | profileFunction h q < 1}
  have hK := isCompact_profile_unit_sublevel ha h
  have hOmega : MeasurableSet Omega := (isOpen_lt ((selectedProfile_spec h).2.2.2.2.2.2.1) continuous_const).measurableSet
  have hOK : Omega ⊆ K := by
    intro q hq
    change profileFunction h q ≤ 1
    exact le_of_lt hq
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let nu : Measure K := Measure.comap Subtype.val (volume.restrict Omega)
  have : IsFiniteMeasureOnCompacts nu := IsFiniteMeasureOnCompacts.comap'
    (volume.restrict Omega) continuous_subtype_val
    (MeasurableEmbedding.subtype_coe hK.measurableSet)
  have : IsFiniteMeasure nu := inferInstance
  have he : (fun z => spatialMollify phi
      (fun y => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨z.1, y.1, y.2⟩) z.2) =
      (fun z : ℝ × XV d => ∫ y : K, phi.normed volume (z.2 - y) * timeCutoffTheta
        (selectedFlatProfile h r y - Real.exp (-mu * z.1) *
          (2 - PDE.vecNormSq (y : XV d).2 / R ^ 2)) ∂nu) := by
    funext z
    rw [spatialMollify, convolution_lsmul_swap]
    simp only [smul_eq_mul]
    rw [integral_subtype_comap hK.measurableSet (fun y =>
      phi.normed volume (z.2 - y) * timeCutoffTheta
        (selectedFlatProfile h r y - Real.exp (-mu * z.1) *
          (2 - PDE.vecNormSq y.2 / R ^ 2)))]
    rw [Measure.restrict_restrict hK.measurableSet, inter_eq_right.mpr hOK]
    rw [← integral_indicator hOmega]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ Omega
    · rw [indicator_of_mem hy,
        zeroExtendedProfile_eq_raw_on_profile _ alpha r mu R hr hmu hR hvel ⟨z.1, y.1, y.2⟩ hy]
      rfl
    · rw [indicator_of_notMem hy,
        zeroExtendedProfile_eq_zero_of_profile _ alpha r mu R ⟨z.1, y.1, y.2⟩ (not_lt.mp hy),
        mul_zero]
  rw [he]
  exact compact_cutoff_mollification_contDiff nu (fun y => (y : XV d)) continuous_subtype_val (fun y => selectedFlatProfile h r y) ((continuous_selectedFlatProfile h r).comp continuous_subtype_val) phi mu R


/-- For each time, the actual zero extension is continuous across the profile boundary. -/
theorem continuous_zeroExtendedProfile_spatial_of_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) (hr : 0 < r)
    (hmu : 0 < mu) (hR : 0 < R) (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2) (t : ℝ) :
    Continuous (fun q : XV d =>
      zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, q.1, q.2⟩) := by
  let Omega : Set (XV d) := {q | profileFunction h q < 1}
  have he : (fun q =>
      zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, q.1, q.2⟩) =
      Omega.piecewise (fun q => timeCutoffProfile (profileFunction h) alpha r mu R
        ⟨t, q.1, q.2⟩) (fun _ => 0) := by
    funext q
    by_cases hq : q ∈ Omega
    · rw [piecewise_eq_of_mem Omega _ _ hq]
      exact zeroExtendedProfile_eq_raw_on_profile _ alpha r mu R hr hmu hR hvel _ hq
    · rw [piecewise_eq_of_notMem Omega _ _ hq]
      exact zeroExtendedProfile_eq_zero_of_profile _ alpha r mu R _ (not_lt.mp hq)
  rw [he]
  apply Continuous.piecewise ?_ ?_ continuous_const
  · intro q hq
    have hb := ((selectedProfile_spec h).2.2.2.2.2.2.1).frontier_preimage_subset (Iio 1) hq
    have hq1 : profileFunction h q = 1 := by
      simpa using hb
    have hpos : 0 < barrier mu R ⟨t, q.1, q.2⟩ := by
      have hv1 := (div_lt_one (sq_pos_of_pos hR)).mpr (hvel q hq1.le)
      unfold barrier
      exact mul_pos (Real.exp_pos _) (by linarith)
    unfold timeCutoffProfile
    rw [(flatProfile_eq_one_sub (profileFunction h) alpha r hr q (hscale.trans hq1.ge)), hq1, sub_self]
    exact timeCutoffTheta_eq_zero _ (by linarith)
  · simpa using!
      contDiff_timeCutoffTheta.continuous.comp
        ((continuous_selectedFlatProfile h r).sub
          (contDiff_nativeBarrier d mu R t).continuous)

/-- The fixed compact unit profile sublevel contains the support at every time. -/
theorem zeroExtendedProfile_tsupport_subset {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R t : ℝ) :
    tsupport (fun q : XV d =>
      zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, q.1, q.2⟩) ⊆
      {q | profileFunction h q ≤ 1} := by
  apply closure_minimal ?_ (isClosed_le ((selectedProfile_spec h).2.2.2.2.2.2.1) continuous_const)
  intro q hq
  by_contra hn
  exact hq (zeroExtendedProfile_eq_zero_of_profile _ alpha r mu R _ (not_le.mp hn).le)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

