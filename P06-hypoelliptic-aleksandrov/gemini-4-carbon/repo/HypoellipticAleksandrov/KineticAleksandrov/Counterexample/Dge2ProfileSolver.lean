module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileSpectralJets
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Spectral
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Punctured homogeneity is sufficient for the exact velocity derivative scaling. -/
theorem punctured_homogeneous_velocity_jet {d : ℕ} (beta : ℝ) (F : XV d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) F ({0}ᶜ))
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, q ≠ 0 →
      F (dilate r q) = Real.rpow r beta * F q)
    (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) (w : PDE.Vec d) :
    fderiv ℝ F (dilate r q) (0, w) = Real.rpow r (beta - 1) * fderiv ℝ F q (0, w) := by
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hqd := (hsmooth.contDiffAt (hopen.mem_nhds hq)).differentiableAt (by simp)
  have hrqd := (hsmooth.contDiffAt
    (hopen.mem_nhds (dilate_ne_zero r hr q hq))).differentiableAt (by simp)
  have hd : HasFDerivAt (dilate (d := d) r)
      ((r ^ 3 • ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d)).prod
        (r • ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d))) q :=
    (hasFDerivAt_fst.const_smul (r ^ 3)).prodMk (hasFDerivAt_snd.const_smul r)
  have hh := hrqd.hasFDerivAt.comp q hd
  have hother : HasFDerivAt (fun z => F (dilate r z)) (Real.rpow r beta • fderiv ℝ F q) q := by
    apply (hqd.hasFDerivAt.const_mul (Real.rpow r beta)).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hq] with z hz
    exact hhom r hr z hz
  have heq := congrArg (fun L => L (0, w)) (hh.unique hother)
  have hsmul : (0, r • w) = r • ((0, w) : XV d) := by simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_zero, smul_eq_mul] at heq
  rw [hsmul, map_smul, smul_eq_mul] at heq
  have hpower : Real.rpow r (beta - 1) = Real.rpow r beta / r := by
    simp
    rw [Real.rpow_sub hr, Real.rpow_one]
  rw [hpower, div_mul_eq_mul_div]
  apply (eq_div_iff hr.ne').mpr
  simpa only [mul_comm] using heq




section
open Filter Topology
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Ramp functional calculus is continuous on a set supporting a Hermitian field. -/
theorem continuousOn_spectralRamp {X : Type*} [TopologicalSpace X] {d : ℕ}
    (M : X → PDE.Mat d) (S : Set X) (hM : ContinuousOn M S)
    (hherm : ∀ x ∈ S, (M x).IsHermitian) (n : ℕ) :
    ContinuousOn (fun x => cfc (positiveSpectralRamp n) (M x)) S := by
  rw [continuousOn_iff_continuous_domRestrict] at hM ⊢
  exact continuous_spectralRamp (fun x : S => M x) hM (fun x => hherm x x.property) n

/-- Continuous positive-part calculus is continuous on any Hermitian field domain. -/
theorem continuousOn_positiveSpectralMass {X : Type*} [TopologicalSpace X] {d : ℕ}
    (M : X → PDE.Mat d) (S : Set X) (hM : ContinuousOn M S)
    (hherm : ∀ x ∈ S, (M x).IsHermitian) :
    ContinuousOn (fun x => positiveSpectralMass (M x)) S := by
  rw [continuousOn_iff_continuous_domRestrict] at hM ⊢
  exact continuous_positiveSpectralMass (fun x : S => M x) hM (fun x => hherm x x.property)

/-- Positive spectral projections of punctured continuous Hermitian fields are measurable. -/
theorem measurable_positiveSpectralProjection_punctured {d : ℕ}
    (M : PDE.Vec d × PDE.Vec d → PDE.Mat d) (hM : ContinuousOn M ({0}ᶜ))
    (hherm : ∀ q, (M q).IsHermitian) :
    Measurable (fun q => positiveSpectralProjection (M q)) := by
  apply measurable_of_tendsto_metrizable
    (fun n => measurable_of_continuousOn_compl_singleton 0
      (continuousOn_spectralRamp M _ hM (fun q _ => hherm q) n))
  apply tendsto_pi_nhds.mpr
  intro q
  have heq : (fun n : ℕ => cfc (positiveSpectralRamp n) (M q)) =ᶠ[atTop]
      (fun _ => positiveSpectralProjection (M q)) := spectralRamp_eventually (M q) (hherm q)
  exact tendsto_const_nhds.congr' heq.symm

/-- Entries of the canonical trace solver are measurable for punctured continuous data. -/
theorem measurable_spectralTraceMatrix_punctured {d : ℕ}
    (M : PDE.Vec d × PDE.Vec d → PDE.Mat d) (hM : ContinuousOn M ({0}ᶜ))
    (hherm : ∀ q, (M q).IsHermitian) (b : PDE.Vec d × PDE.Vec d → ℝ)
    (hb : Measurable b) (cminus : ℝ) (i k : Fin d) :
    Measurable (fun q => spectralTraceMatrix (M q) (b q) cminus i k) := by
  have hproj := (measurable_positiveSpectralProjection_punctured M hM hherm).eval_matrix
    (i := i) (j := k)
  have hneg := (measurable_positiveSpectralProjection_punctured (fun q => -M q) hM.neg
    (fun q => (hherm q).neg)).eval_matrix (i := i) (j := k)
  have hw : Measurable (fun q =>
      (b q + cminus * negativeSpectralMass (M q)) / positiveSpectralMass (M q)) :=
    (hb.add (measurable_const.mul (measurable_of_continuousOn_compl_singleton 0 (continuousOn_positiveSpectralMass (fun q => -M q) _ hM.neg (fun q _ => (hherm q).neg))))).div (measurable_of_continuousOn_compl_singleton 0 (continuousOn_positiveSpectralMass M _ hM (fun q _ => hherm q)))
  unfold spectralTraceMatrix zeroSpectralProjection
  simp
  exact ((hw.mul hproj).add (measurable_const.mul hneg)).add
    ((measurable_const.sub hproj).sub hneg)

end
section
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- The positive kinetic dilation carrying every nonzero point to the unit gauge shell. -/
def normalizeGauge {d : ℕ} (q : XV d) : XV d := dilate (rho q)⁻¹ q

/-- A nonzero point normalizes to the unit gauge shell. -/
theorem rho_normalizeGauge {d : ℕ} (q : XV d) (hq : q ≠ 0) : rho (normalizeGauge q) = 1 := by
  have hr := (rho_nonneg q).lt_of_ne' ((rho_eq_zero_iff q).not.mpr hq)
  rw [normalizeGauge, rho_dilate _ (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']

/-- Gauge normalization preserves nonzero points. -/
theorem normalizeGauge_ne_zero {d : ℕ} (q : XV d) (hq : q ≠ 0) : normalizeGauge q ≠ 0 := by
  intro hz
  have hh := rho_normalizeGauge q hq
  simp [hz] at hh

/-- Positive dilation by the gauge recovers the original nonzero point. -/
theorem dilate_normalizeGauge {d : ℕ} (q : XV d) (hq : q ≠ 0) :
    dilate (rho q) (normalizeGauge q) = q := by
  rw [normalizeGauge, dilate_mul, mul_inv_cancel₀ ((rho_eq_zero_iff q).not.mpr hq), dilate_one]


/-- The normalized velocity Hessian, assigned the identity at the joint origin. -/
def normalizedProfileMatrix {d : ℕ} (H : XV d → ℝ) (q : XV d) : PDE.Mat d :=
  if q = 0 then 1 else dvv H (normalizeGauge q)

/-- The normalized transport scalar, assigned one at the joint origin. -/
def normalizedProfileTransport {d : ℕ} (H : XV d → ℝ) (q : XV d) : ℝ :=
  if q = 0 then 1 else PDE.vecDot (normalizeGauge q).2 (dx H (normalizeGauge q))



/-- The normalized Hessian field is Hermitian everywhere, including its assigned origin value. -/
theorem normalizedProfileMatrix_isHermitian {d : ℕ} (H : XV d → ℝ)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ)) (q : XV d) :
    (normalizedProfileMatrix H q).IsHermitian := by
  by_cases hq : q = 0
  · simp only [normalizedProfileMatrix, hq, ite_true]
    exact Matrix.isHermitian_one
  · rw [normalizedProfileMatrix, ite_eq_right hq]
    have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
    exact dvv_isHermitian H _ (hH.contDiffAt (hopen.mem_nhds (normalizeGauge_ne_zero q hq)))

/-- The source canonical spectral matrix on normalized jets, with identity at the origin. -/
def homogeneousSpectralMatrix {d : ℕ} (H : XV d → ℝ) (cminus : ℝ) (q : XV d) : PDE.Mat d :=
  if q = 0 then 1 else
    spectralTraceMatrix (normalizedProfileMatrix H q) (normalizedProfileTransport H q) cminus

/-- The globally extended canonical matrix has measurable entries. -/
theorem measurable_homogeneousSpectralMatrix {d : ℕ} (H : XV d → ℝ)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ)) (cminus : ℝ) (i k : Fin d) :
    Measurable (fun q => homogeneousSpectralMatrix H cminus q i k)    := by
  have continuousOn_normalizeGauge :
      ContinuousOn (normalizeGauge (d := d)) ({0}ᶜ) := by
    have hi := (continuous_rho d).continuousOn.inv₀ (fun q hq => (rho_eq_zero_iff q).not.mpr hq)
    exact (hi.pow 3 |>.smul continuous_fst.continuousOn).prodMk
      (hi.smul continuous_snd.continuousOn)
  have continuousOn_normalizedProfileTransport :
      ContinuousOn (normalizedProfileTransport H) ({0}ᶜ) := by
    apply ((continuousOn_transport_off_origin H hH).comp (continuousOn_normalizeGauge)
      (fun q hq => normalizeGauge_ne_zero q hq)).congr
    intro q hq
    change q ≠ 0 at hq
    simp [normalizedProfileTransport, ite_eq_right hq]
  have continuousOn_normalizedProfileMatrix :
      ContinuousOn (normalizedProfileMatrix H) ({0}ᶜ) := by
    apply ((continuousOn_dvv_off_origin H hH).comp (continuousOn_normalizeGauge)
      (fun q hq => normalizeGauge_ne_zero q hq)).congr
    intro q hq
    change q ≠ 0 at hq
    simp [normalizedProfileMatrix, ite_eq_right hq]
  classical
  have hm := measurable_spectralTraceMatrix_punctured (normalizedProfileMatrix H)
    (continuousOn_normalizedProfileMatrix) (normalizedProfileMatrix_isHermitian H hH)
    (normalizedProfileTransport H) (measurable_of_continuousOn_compl_singleton 0 (continuousOn_normalizedProfileTransport)) cminus i k
  have hh : Measurable (fun q : XV d => if q ∈ ({0} : Set (XV d)) then
      (1 : PDE.Mat d) i k else spectralTraceMatrix (normalizedProfileMatrix H q)
        (normalizedProfileTransport H q) cminus i k) :=
    (measurable_const (a := (1 : PDE.Mat d) i k)).ite (measurableSet_singleton 0) hm
  convert hh using 1
  funext q
  simp [homogeneousSpectralMatrix]
  split_ifs <;> rfl

/-- Scalar identity matrices are ordered according to their scalar weights. -/
theorem scalar_identity_le {d : ℕ} (a b : ℝ) (hab : a ≤ b) :
    a • (1 : PDE.Mat d) ≤ b • (1 : PDE.Mat d) := by
  rw [Matrix.le_iff, ← sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hab)

end
open scoped MatrixOrder Matrix.Norms.L2Operator


/-- The geometric profile has a global measurable elliptic matrix solving its pointwise PDE. -/
theorem exists_geometricProfile_elliptic_solver (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C₀ sigma R lam Lam : ℝ, ∃ A : XV d → PDE.Mat d,
      0 < C₀ ∧ 0 < sigma ∧ 2 < R ∧ 0 < lam ∧ lam ≤ Lam ∧
      (∀ i k, Measurable (fun q => A q i k)) ∧
      (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
      (∀ q, q ≠ 0 → matrixContraction (A q) (dvv (geometricProfile alpha C₀ sigma R) q) =
        PDE.vecDot q.2 (dx (geometricProfile alpha C₀ sigma R) q))     := by
  have homogeneous_position_jet {d : ℕ} (H : XV d → ℝ) (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ)) (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) (w : PDE.Vec d) :
      fderiv ℝ H (dilate r q) (w, 0) = Real.rpow r (alpha - 3) * fderiv ℝ H q (w, 0) := by
    have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
    have hqd := (hsmooth.contDiffAt (hopen.mem_nhds hq)).differentiableAt (by simp)
    have hrqd := (hsmooth.contDiffAt
      (hopen.mem_nhds (dilate_ne_zero r hr q hq))).differentiableAt (by simp)
    have hd : HasFDerivAt (dilate (d := d) r)
        ((r ^ 3 • ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d)).prod
          (r • ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d))) q :=
      (hasFDerivAt_fst.const_smul (r ^ 3)).prodMk (hasFDerivAt_snd.const_smul r)
    have hh := hrqd.hasFDerivAt.comp q hd
    have hother : HasFDerivAt (fun z => H (dilate r z)) (Real.rpow r alpha • fderiv ℝ H q) q := by
      convert hqd.hasFDerivAt.const_mul (Real.rpow r alpha) using 1
      funext z
      exact hhom r hr z
    have heq := congrArg (fun L => L (w, 0)) (hh.unique hother)
    have hsmul : (r ^ 3 • w, 0) = r ^ 3 • ((w, 0) : XV d) := by simp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_zero, smul_eq_mul] at heq
    rw [hsmul, map_smul, smul_eq_mul] at heq
    have hpower : Real.rpow r (alpha - 3) = Real.rpow r alpha / r ^ 3 := by
      simp
      rw [Real.rpow_sub hr]
      norm_num
    rw [hpower, div_mul_eq_mul_div]
    apply (eq_div_iff (pow_ne_zero 3 hr.ne')).mpr
    simpa only [mul_comm] using heq
  have homogeneous_transport {d : ℕ} (H : XV d → ℝ) (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ)) (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) :
      PDE.vecDot (dilate r q).2 (dx H (dilate r q)) =
      Real.rpow r (alpha - 2) * PDE.vecDot q.2 (dx H q) := by
    rw [transport_eq_direction, transport_eq_direction]
    have hdir : ((dilate r q).2, 0) = r • ((q.2, 0) : XV d) := by
      simp [dilate, Prod.smul_mk]
    rw [hdir, map_smul, smul_eq_mul, homogeneous_position_jet H hsmooth hhom r hr q hq]
    have hp : r * Real.rpow r (alpha - 3) = Real.rpow r (alpha - 2) := by
      simp only [Real.rpow_eq_pow]
      conv_lhs => lhs; rw [← Real.rpow_one r]
      rw [← Real.rpow_add hr]
      congr 1
      ring
    rw [← mul_assoc, hp]
  have homogeneous_dvv {d : ℕ} (H : XV d → ℝ) (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ)) (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) :
      dvv H (dilate r q) = Real.rpow r (alpha - 2) • dvv H q := by
    have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
    ext i k
    let F := fun z => fderiv ℝ H z (0, Pi.single k 1)
    have hF : ContDiffOn ℝ (⊤ : ℕ∞) F ({0}ᶜ) :=
      (hsmooth.fderiv_of_isOpen hopen (m := (⊤ : ℕ∞)) (by simp)).clm_apply
        (contDiffOn_const (c := ((0, Pi.single k 1) : XV d)))
    have hhomF : ∀ s : ℝ, 0 < s → ∀ z, z ≠ 0 →
        F (dilate s z) = Real.rpow s (alpha - 1) * F z :=
      fun s hs z hz => homogeneous_velocity_jet alpha H hsmooth hhom s hs z hz _
    have hh := punctured_homogeneous_velocity_jet (alpha - 1) F hF hhomF r hr q hq
      (Pi.single i 1)
    have hexp : alpha - 1 - 1 = alpha - 2 := by ring
    simpa [dvv, dv, Matrix.smul_apply, hexp] using hh
  have exists_spectral_weights_of_homogeneous_profile {d : ℕ} (H : XV d → ℝ) (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ)) (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) (hpos : ∀ q, q ≠ 0 → 0 < positiveSpectralMass (dvv H q)) (hzero : ∀ q, q ≠ 0 → negativeSpectralMass (dvv H q) = 0 →
      0 < PDE.vecDot q.2 (dx H q)) :
      ∃ cminus lam Lam : ℝ, 1 ≤ cminus ∧ 0 < lam ∧ lam ≤ 1 ∧ 1 ≤ Lam ∧
      (∀ q, lam • 1 ≤ homogeneousSpectralMatrix H cminus q ∧
        homogeneousSpectralMatrix H cminus q ≤ Lam • 1) ∧
      (∀ q, q ≠ 0 → matrixContraction (homogeneousSpectralMatrix H cminus q) (dvv H q) =
        PDE.vecDot q.2 (dx H q)) := by
    let K : Set (XV d) := {q | rho q = 1}
    let M := dvv H
    let b := fun q : XV d => PDE.vecDot q.2 (dx H q)
    have hKnz : ∀ q ∈ K, q ≠ 0 := by
      intro q hq hz
      have hh : rho q = 1 := hq
      simp [hz] at hh
    have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
    have hherm : ∀ q, q ≠ 0 → (M q).IsHermitian :=
      fun q hq => dvv_isHermitian H q (hsmooth.contDiffAt (hopen.mem_nhds hq))
    have hMc : ContinuousOn M K := (continuousOn_dvv_off_origin H hsmooth).mono
      (fun q hq => hKnz q hq)
    have hbc : ContinuousOn b K := (continuousOn_transport_off_origin H hsmooth).mono
      (fun q hq => hKnz q hq)
    have hmp : ContinuousOn (fun q => positiveSpectralMass (M q)) K :=
      continuousOn_positiveSpectralMass M K hMc (fun q hq => hherm q (hKnz q hq))
    have hmn : ContinuousOn (fun q => negativeSpectralMass (M q)) K :=
      continuousOn_positiveSpectralMass (fun q => -M q) K hMc.neg
        (fun q hq => (hherm q (hKnz q hq)).neg)
    have hm0 : ∀ q ∈ K, 0 ≤ negativeSpectralMass (M q) :=
      fun q hq => positiveSpectralMass_nonneg (-M q) (hherm q (hKnz q hq)).neg
    obtain ⟨cminus, hcminus, hnum⟩ := exists_spectral_weight_on_compact K
      (isCompact_unitGaugeShell d) b (fun q => negativeSpectralMass (M q)) hbc hmn hm0
      (fun q hq => hzero q (hKnz q hq))
    let w := fun q => (b q + cminus * negativeSpectralMass (M q)) / positiveSpectralMass (M q)
    have hwc : ContinuousOn w K :=
      (hbc.add (continuousOn_const.mul hmn)).div hmp
        (fun q hq => (hpos q (hKnz q hq)).ne')
    obtain ⟨lower, upper, hlo, _, hweights⟩ := exists_positive_bounds_on_compact K
      (isCompact_unitGaugeShell d) w hwc
      (fun q hq => div_pos (hnum q hq) (hpos q (hKnz q hq)))
    let lam := min 1 (min lower cminus)
    let Lam := max 1 (max upper cminus)
    have hlam : 0 < lam := lt_min zero_lt_one
      (lt_min hlo (lt_of_lt_of_le zero_lt_one hcminus))
    have hlam1 : lam ≤ 1 := min_le_left _ _
    have hLam1 : 1 ≤ Lam := le_max_left _ _
    have hbound : ∀ q ∈ K, lam • 1 ≤ spectralTraceMatrix (M q) (b q) cminus ∧
        spectralTraceMatrix (M q) (b q) cminus ≤ Lam • 1 := by
      intro q hq
      exact spectralTraceMatrix_uniform_bounds (M q) (hherm q (hKnz q hq)) (b q) cminus
        lower upper (hweights q hq).1 (hweights q hq).2
    refine ⟨cminus, lam, Lam, hcminus, hlam, hlam1, hLam1, ?_, ?_⟩
    · intro q
      by_cases hq : q = 0
      · rw [homogeneousSpectralMatrix, ite_eq_left hq]
        simpa using
          And.intro (scalar_identity_le (d := d) lam 1 hlam1)
            (scalar_identity_le (d := d) 1 Lam hLam1)
      · have hp : normalizeGauge q ∈ K := rho_normalizeGauge q hq
        rw [homogeneousSpectralMatrix, ite_eq_right hq, normalizedProfileMatrix,
          ite_eq_right hq, normalizedProfileTransport, ite_eq_right hq]
        exact hbound (normalizeGauge q) hp
    · intro q hq
      have hr : 0 < rho q := (rho_nonneg q).lt_of_ne' ((rho_eq_zero_iff q).not.mpr hq)
      let p := normalizeGauge q
      have hpnz : p ≠ 0 := normalizeGauge_ne_zero q hq
      have hMscale := homogeneous_dvv H hsmooth hhom (rho q) hr p hpnz
      have hbscale := homogeneous_transport H hsmooth hhom (rho q) hr p hpnz
      rw [dilate_normalizeGauge q hq] at hMscale hbscale
      rw [homogeneousSpectralMatrix, ite_eq_right hq, normalizedProfileMatrix,
        ite_eq_right hq, normalizedProfileTransport, ite_eq_right hq, hMscale,
        matrixContraction_smul_right,
        spectral_trace_solver _ (hherm p hpnz) _ _ (hpos p hpnz).ne']
      exact hbscale.symm
  obtain ⟨C₀, sigma, R, hC₀, hsigma, hR2, hsign⟩ :=
    exists_geometricProfile_spectral_signs d hd alpha ha ha1
  have hR : 0 < R := lt_trans (by norm_num) hR2
  let H : XV d → ℝ := geometricProfile alpha C₀ sigma R
  have hH := geometricProfile_smooth_off_origin (d := d) alpha C₀ sigma R hsigma hR
  have hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q :=
    fun r hr q => geometricProfile_homogeneous alpha C₀ sigma R r hr q
  obtain ⟨cminus, lam, Lam, _, hlam, hlam1, hLam1, hbounds, hsolve⟩ :=
    exists_spectral_weights_of_homogeneous_profile H hH hhom
      (fun q hq => (hsign q hq).2.1) (fun q hq => (hsign q hq).2.2)
  refine ⟨C₀, sigma, R, lam, Lam, homogeneousSpectralMatrix H cminus,
    hC₀, hsigma, hR2, hlam, hlam1.trans hLam1, ?_, hbounds, hsolve⟩
  exact fun i k => measurable_homogeneousSpectralMatrix H hH cminus i k

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

