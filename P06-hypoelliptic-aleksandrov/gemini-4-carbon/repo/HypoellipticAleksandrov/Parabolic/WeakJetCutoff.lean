module

public import HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import HypoellipticAleksandrov.Parabolic.LocalGluing

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic
open Filter MeasureTheory Function Set
open scoped ENNReal Topology ContDiff


private theorem integrable_restrict_mul_of_locallyIntegrableOn
    {d : ℕ} {U : Set (TimeVelocity d)} {f g : TimeVelocity d → ℝ}
    (hf : LocallyIntegrableOn f U volume) (hg : Continuous g)
    (hgCompact : HasCompactSupport g) (hgSub : tsupport g ⊆ U) :
    Integrable (fun z => f z * g z) (timeVelocityVolumeOn U) := by
  have hfgK : IntegrableOn (fun z => f z * g z) (tsupport g) volume := by
    simpa using
      (hf.integrableOn_compact_subset hgSub hgCompact.isCompact).smul_continuousOn hg.continuousOn hgCompact.isCompact
  have hsupport : Function.support (fun z => f z * g z) ⊆ tsupport g := by
    intro z hz
    exact tsupport_mul_subset_right (subset_closure hz)
  exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hfgK |>.restrict

private theorem weak_product_rule
    {d : ℕ} {U : Set (TimeVelocity d)}
    {u du b : TimeVelocity d → ℝ}
    {D : (TimeVelocity d → ℝ) → TimeVelocity d → ℝ}
    (hu : ∀ φ : TimeVelocity d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z in U, u z * D φ z ∂volume) = -∫ z in U, du z * φ z ∂volume)
    (hDmul : ∀ (f g : TimeVelocity d → ℝ), ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) g → ∀ z, D (f * g) z = f z * D g z + g z * D f z)
    (hDcont : ∀ f : TimeVelocity d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      Continuous (D f))
    (hDcompact : ∀ f : TimeVelocity d → ℝ, HasCompactSupport f →
      HasCompactSupport (D f))
    (hDtsupport : ∀ f : TimeVelocity d → ℝ, tsupport (D f) ⊆ tsupport f)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduLoc : LocallyIntegrableOn du U volume) :
    ∀ φ : TimeVelocity d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z in U, (b z * u z) * D φ z ∂volume) =
        -∫ z in U, (b z * du z + u z * D b z) * φ z ∂volume := by
  intro φ hφ hφCompact hφSub
  let μU : Measure (TimeVelocity d) := timeVelocityVolumeOn U
  let dφ : TimeVelocity d → ℝ := D φ
  let db := D b
  let φb : TimeVelocity d → ℝ := b * φ
  have hbCont := hb.continuous
  have hφCont : Continuous φ := hφ.continuous
  have hdφCont : Continuous dφ := hDcont φ hφ
  have hdφCompact : HasCompactSupport dφ := hDcompact φ hφCompact
  have hdφSub : tsupport dφ ⊆ U := (hDtsupport φ).trans hφSub
  have hφbSmooth : ContDiff ℝ (⊤ : ℕ∞) φb := hb.mul hφ
  have hφbCompact : HasCompactSupport φb := by
    simpa using hφCompact.mul_left
  have hdφbCont : Continuous (D φb) := hDcont φb hφbSmooth
  have hdφbCompact : HasCompactSupport (D φb) := hDcompact φb hφbCompact
  have hφbSub : tsupport φb ⊆ U :=
    (tsupport_mul_subset_right).trans hφSub
  have hdφbSub : tsupport (D φb) ⊆ U := (hDtsupport φb).trans hφbSub
  have huWeak :
      (∫ z, u z * D φb z ∂μU) = -∫ z, du z * φb z ∂μU := by
    simpa using hu φb hφbSmooth hφbCompact hφbSub
  have hbdφCont : Continuous (fun z => b z * dφ z) := hbCont.mul hdφCont
  have hbdφCompact : HasCompactSupport (fun z => b z * dφ z) := by
    simpa only [Pi.mul_def] using hdφCompact.mul_left
  have hbdφSub : tsupport (fun z => b z * dφ z) ⊆ U :=
    (tsupport_mul_subset_right.trans hdφSub)
  have hφdbCont : Continuous (fun z => φ z * db z) := hφCont.mul (hDcont b hb)
  have hφdbCompact : HasCompactSupport (fun z => φ z * db z) := by
    simpa only [Pi.mul_def] using hφCompact.mul_right
  have hφdbSub : tsupport (fun z => φ z * db z) ⊆ U :=
    tsupport_mul_subset_left.trans hφSub
  have huBdφ : Integrable (fun z => u z * (b z * dφ z)) μU := by
    simpa using
      integrable_restrict_mul_of_locallyIntegrableOn huLoc hbdφCont hbdφCompact hbdφSub
  have huφdb : Integrable (fun z => u z * (φ z * db z)) μU := by
    simpa using
      integrable_restrict_mul_of_locallyIntegrableOn huLoc hφdbCont hφdbCompact hφdbSub
  have huDφb : Integrable (fun z => u z * D φb z) μU := by
    simpa using
      integrable_restrict_mul_of_locallyIntegrableOn huLoc hdφbCont hdφbCompact hdφbSub
  have hduφb : Integrable (fun z => du z * φb z) μU := by
    simpa only [μU, φb] using
      integrable_restrict_mul_of_locallyIntegrableOn hduLoc
        (hbCont.mul hφCont) hφbCompact hφbSub
  have huDbφ : Integrable (fun z => (u z * db z) * φ z) μU := by
    simpa only [μU, mul_assoc, mul_left_comm, mul_comm] using
      integrable_restrict_mul_of_locallyIntegrableOn huLoc hφdbCont hφdbCompact hφdbSub
  have hproduct : ∀ z, D φb z = b z * dφ z + φ z * db z := by
    intro z
    simpa using hDmul b φ hb hφ z
  have hleft :
      (∫ z, (b z * u z) * dφ z ∂μU) =
        ∫ z, u z * (b z * dφ z) ∂μU := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by ring
  have hsplit :
      (∫ z, u z * (b z * dφ z) ∂μU) =
        (∫ z, u z * D φb z ∂μU) - ∫ z, u z * (φ z * db z) ∂μU := by
    calc
      (∫ z, u z * (b z * dφ z) ∂μU) =
          ∫ z, u z * D φb z - u z * (φ z * db z) ∂μU := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          change u z * (b z * dφ z) =
            u z * D φb z - u z * (φ z * db z)
          rw [hproduct z]
          ring
      _ = (∫ z, u z * D φb z ∂μU) - ∫ z, u z * (φ z * db z) ∂μU := by
        rw [integral_sub huDφb huφdb]
  have hright :
      -(∫ z, du z * φb z ∂μU) - ∫ z, u z * (φ z * db z) ∂μU =
        -∫ z, (b z * du z + u z * db z) * φ z ∂μU := by
    have hsum :
        (∫ z, (b z * du z + u z * db z) * φ z ∂μU) =
          (∫ z, du z * φb z ∂μU) + ∫ z, (u z * db z) * φ z ∂μU := by
      calc
        (∫ z, (b z * du z + u z * db z) * φ z ∂μU) =
            ∫ z, du z * φb z + (u z * db z) * φ z ∂μU := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z => by
            simp [φb]
            ring
        _ = (∫ z, du z * φb z ∂μU) + ∫ z, (u z * db z) * φ z ∂μU := by
          rw [integral_add hduφb huDbφ]
    have huTerm :
        (∫ z, u z * (φ z * db z) ∂μU) =
          ∫ z, (u z * db z) * φ z ∂μU := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    rw [huTerm, hsum]
    ring
  calc
    (∫ z, (b z * u z) * dφ z ∂μU) =
        ∫ z, u z * (b z * dφ z) ∂μU := hleft
    _ = (∫ z, u z * D φb z ∂μU) - ∫ z, u z * (φ z * db z) ∂μU := hsplit
    _ = -(∫ z, du z * φb z ∂μU) - ∫ z, u z * (φ z * db z) ∂μU := by rw [huWeak]
    _ = -∫ z, (b z * du z + u z * db z) * φ z ∂μU := hright

private theorem timeDerivative_mul
    {d : ℕ} (f g : TimeVelocity d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : TimeVelocity d) :
    timeDerivative (f * g) z = f z * timeDerivative g z + g z * timeDerivative f z := by
  unfold timeDerivative
  rw [fderiv_mul (hf.contDiffAt.differentiableAt (by simp))
    (hg.contDiffAt.differentiableAt (by simp))]
  simp

private theorem timeDerivative_continuous {d : ℕ} {f : TimeVelocity d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (timeDerivative f) := by
  unfold timeDerivative
  simpa using (hf.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem timeDerivative_compact {d : ℕ} {f : TimeVelocity d → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (timeDerivative f) := by
  unfold timeDerivative
  simpa using hf.fderiv_apply (𝕜 := ℝ) ((1, 0) : TimeVelocity d)


private theorem velocityGradient_mul {d : ℕ} {i : Fin d}
    (f g : TimeVelocity d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : TimeVelocity d) :
    velocityGradient (f * g) z i =
      f z * velocityGradient g z i + g z * velocityGradient f z i := by
  unfold velocityGradient
  rw [fderiv_mul (hf.contDiffAt.differentiableAt (by simp))
    (hg.contDiffAt.differentiableAt (by simp))]
  simp [ContinuousLinearMap.smul_apply]

private theorem velocityGradient_continuous {d : ℕ} {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (fun z => velocityGradient f z i) := by
  unfold velocityGradient
  simpa using (hf.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem velocityGradient_compact {d : ℕ} {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : HasCompactSupport f) : HasCompactSupport (fun z => velocityGradient f z i) := by
  unfold velocityGradient
  simpa using hf.fderiv_apply (𝕜 := ℝ) ((0, Pi.single i 1) : TimeVelocity d)

private theorem velocityGradient_tsupport {d : ℕ} {i : Fin d} (f : TimeVelocity d → ℝ) :
    tsupport (fun z => velocityGradient f z i) ⊆ tsupport f := by
  unfold velocityGradient
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

namespace HasWeakTimeDerivOn

/-- Smooth scalar multiplication obeys the raw weak time-derivative product rule. -/
theorem mul_contDiff {d : ℕ} {U : Set (TimeVelocity d)} {u du b : TimeVelocity d → ℝ}
    (hu : HasWeakTimeDerivOn U u du) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduLoc : LocallyIntegrableOn du U volume) :
    HasWeakTimeDerivOn U (fun z => b z * u z)
      (fun z => b z * du z + u z * timeDerivative b z)  := by
  have timeDerivative_tsupport {d : ℕ} (f : TimeVelocity d → ℝ) :
      tsupport (timeDerivative f) ⊆ tsupport f := by
    unfold timeDerivative
    refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
    intro z hz
    rw [Function.mem_support] at hz ⊢
    intro hzero
    apply hz
    simp [hzero]
  exact weak_product_rule hu timeDerivative_mul
    (fun f hf => timeDerivative_continuous hf)
    (fun f hf => timeDerivative_compact hf) timeDerivative_tsupport hb huLoc hduLoc

end HasWeakTimeDerivOn

namespace HasWeakVelocityPartialDerivOn

/-- Smooth scalar multiplication obeys the raw weak velocity product rule. -/
theorem mul_contDiff {d : ℕ} {U : Set (TimeVelocity d)} {i : Fin d}
    {u dui b : TimeVelocity d → ℝ}
    (hu : HasWeakVelocityPartialDerivOn U i u dui) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduiLoc : LocallyIntegrableOn dui U volume) :
    HasWeakVelocityPartialDerivOn U i (fun z => b z * u z)
      (fun z => b z * dui z + u z * velocityGradient b z i) := by
  exact weak_product_rule hu
    (fun f g hf hg z => velocityGradient_mul f g hf hg z)
    (fun f hf => velocityGradient_continuous hf)
    (fun f hf => velocityGradient_compact hf) velocityGradient_tsupport hb huLoc hduiLoc

end HasWeakVelocityPartialDerivOn

private theorem velocityGradient_contDiff {d : ℕ} {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => velocityGradient f z i) := by
  unfold velocityGradient
  exact (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

private theorem velocityHessian_continuous {d : ℕ} {f : TimeVelocity d → ℝ}
    {i j : Fin d} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun z => velocityHessian f z i j) := by
  unfold velocityHessian
  simpa using (((contDiff_infty_iff_fderiv.mp hf).2).continuous_fderiv (by simp)).clm_apply continuous_const |>.clm_apply
    continuous_const

private theorem velocityHessian_compact {d : ℕ} {f : TimeVelocity d → ℝ}
    {i j : Fin d} (hf : HasCompactSupport f) :
    HasCompactSupport (fun z => velocityHessian f z i j) := by
  unfold velocityHessian
  have hsecond := (hf.fderiv ℝ).fderiv ℝ
  simpa only [Function.comp_def] using hsecond.comp_left
    (g := fun H =>
      H ((0, Pi.single i 1) : TimeVelocity d) ((0, Pi.single j 1) : TimeVelocity d)) rfl

private theorem velocityGradient_velocityGradient {d : ℕ} {b : TimeVelocity d → ℝ}
    {i j : Fin d} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (z : TimeVelocity d) :
    velocityGradient (fun y => velocityGradient b y i) z j =
      HypoellipticAleksandrov.Parabolic.velocityHessian b z i j := by
  have hgradDiff : DifferentiableAt ℝ (fderiv ℝ b) z :=
    ((contDiff_infty_iff_fderiv.mp hb).2).contDiffAt.differentiableAt (by simp)
  have hraw : velocityGradient (fun y => velocityGradient b y i) z j =
      HypoellipticAleksandrov.Parabolic.velocityHessian b z j i := by
    unfold velocityGradient HypoellipticAleksandrov.Parabolic.velocityHessian
    rw [fderiv_clm_apply hgradDiff (differentiableAt_const _)]
    have hconst : fderiv ℝ (fun _ =>
        ((0, Pi.single i 1) : TimeVelocity d)) z = 0 :=
      (hasFDerivAt_const ((0, Pi.single i 1) : TimeVelocity d) z).fderiv
    rw [hconst]
    simp
  exact hraw.trans ((velocityHessian_isSymm (hb.of_le (by exact WithTop.coe_le_coe.mpr le_top)) z).apply i j)

namespace ParabolicW12Function

/-- Multiply a raw parabolic weak jet by a globally smooth compactly supported scalar. -/
noncomputable def mulContDiffHasCompactSupport {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞}
    (w : ParabolicW12Function d U p) (hp : 1 ≤ p) {b : TimeVelocity d → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbCompact : HasCompactSupport b) :
    ParabolicW12Function d U p where
  toFun := fun z => b z * w.toFun z
  timeDeriv := fun z => b z * w.timeDeriv z + w.toFun z * timeDerivative b z
  velocityGrad := fun z i => b z * w.velocityGrad z i + w.toFun z * velocityGradient b z i
  velocityHessian := fun z i j =>
    b z * w.velocityHessian z i j + velocityGradient b z j * w.velocityGrad z i +
      w.velocityGrad z j * velocityGradient b z i + w.toFun z *
        HypoellipticAleksandrov.Parabolic.velocityHessian b z i j
  memLp := by
    have hbTop : ParabolicMemLpOn U ∞ b :=
      (hb.continuous.memLp_of_hasCompactSupport hbCompact).restrict U
    simpa only [mul_comm] using w.memLp.mul' hbTop
  timeDeriv_memLp := by
    have hbTop : ParabolicMemLpOn U ∞ b :=
      (hb.continuous.memLp_of_hasCompactSupport hbCompact).restrict U
    have hdbTop : ParabolicMemLpOn U ∞ (timeDerivative b) :=
      ((timeDerivative_continuous hb).memLp_of_hasCompactSupport
        (timeDerivative_compact hbCompact)).restrict U
    exact (by
      have hfirst : ParabolicMemLpOn U p (fun z => b z * w.timeDeriv z) :=
        by simpa only [mul_comm] using w.timeDeriv_memLp.mul' hbTop
      have hsecond : ParabolicMemLpOn U p (fun z => w.toFun z * timeDerivative b z) :=
        by simpa only [mul_comm] using w.memLp.mul' hdbTop
      exact hfirst.add hsecond)
  velocityGrad_memLp := by
    intro i
    have hbTop : ParabolicMemLpOn U ∞ b :=
      (hb.continuous.memLp_of_hasCompactSupport hbCompact).restrict U
    have hdbTop : ParabolicMemLpOn U ∞ (fun z => velocityGradient b z i) :=
      ((velocityGradient_continuous hb).memLp_of_hasCompactSupport
        (velocityGradient_compact hbCompact)).restrict U
    have hfirst : ParabolicMemLpOn U p (fun z => b z * w.velocityGrad z i) :=
      by simpa only [mul_comm] using (w.velocityGrad_memLp i).mul' hbTop
    have hsecond : ParabolicMemLpOn U p
        (fun z => w.toFun z * velocityGradient b z i) :=
      by simpa only [mul_comm] using w.memLp.mul' hdbTop
    exact hfirst.add hsecond
  velocityHessian_memLp := by
    intro i j
    have hbTop : ParabolicMemLpOn U ∞ b :=
      (hb.continuous.memLp_of_hasCompactSupport hbCompact).restrict U
    have hdbiTop : ParabolicMemLpOn U ∞ (fun z => velocityGradient b z i) :=
      ((velocityGradient_continuous hb).memLp_of_hasCompactSupport
        (velocityGradient_compact hbCompact)).restrict U
    have hdbjTop : ParabolicMemLpOn U ∞ (fun z => velocityGradient b z j) :=
      ((velocityGradient_continuous hb).memLp_of_hasCompactSupport
        (velocityGradient_compact hbCompact)).restrict U
    have hddbijTop : ParabolicMemLpOn U ∞
        (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian b z i j) :=
      ((velocityHessian_continuous hb).memLp_of_hasCompactSupport
        (velocityHessian_compact hbCompact)).restrict U
    have hfirst : ParabolicMemLpOn U p (fun z => b z * w.velocityHessian z i j) :=
      by simpa only [mul_comm] using (w.velocityHessian_memLp i j).mul' hbTop
    have hsecond : ParabolicMemLpOn U p
        (fun z => velocityGradient b z j * w.velocityGrad z i) :=
      by simpa only [mul_comm] using (w.velocityGrad_memLp i).mul' hdbjTop
    have hthird : ParabolicMemLpOn U p
        (fun z => w.velocityGrad z j * velocityGradient b z i) :=
      by simpa only [mul_comm] using (w.velocityGrad_memLp j).mul' hdbiTop
    have hfourth : ParabolicMemLpOn U p
        (fun z => w.toFun z * HypoellipticAleksandrov.Parabolic.velocityHessian b z i j) :=
      by simpa only [mul_comm] using w.memLp.mul' hddbijTop
    exact ((hfirst.add hsecond).add hthird).add hfourth
  hasWeakTimeDeriv := by
    exact w.hasWeakTimeDeriv.mul_contDiff hb
      (w.memLp.locallyIntegrableOn hp) (w.timeDeriv_memLp.locallyIntegrableOn hp)
  hasWeakVelocityPartialDeriv := by
    intro i
    exact (w.hasWeakVelocityPartialDeriv i).mul_contDiff hb
      (w.memLp.locallyIntegrableOn hp) ((w.velocityGrad_memLp i).locallyIntegrableOn hp)
  hasWeakVelocitySecondPartialDeriv := by
    intro i j
    let dbi : TimeVelocity d → ℝ := fun z => velocityGradient b z i
    have hdbi : ContDiff ℝ (⊤ : ℕ∞) dbi := velocityGradient_contDiff hb
    have hfirst := (w.hasWeakVelocitySecondPartialDeriv i j).mul_contDiff hb
      ((w.velocityGrad_memLp i).locallyIntegrableOn hp)
      ((w.velocityHessian_memLp i j).locallyIntegrableOn hp)
    have hsecond := (w.hasWeakVelocityPartialDeriv j).mul_contDiff hdbi
      (w.memLp.locallyIntegrableOn hp)
      ((w.velocityGrad_memLp j).locallyIntegrableOn hp)
    have hbTop : ParabolicMemLpOn U ∞ b :=
      (hb.continuous.memLp_of_hasCompactSupport hbCompact).restrict U
    have hdbiTop : ParabolicMemLpOn U ∞ dbi := by
      simpa only [dbi] using
        ((velocityGradient_continuous (i := i) hb).memLp_of_hasCompactSupport
          (velocityGradient_compact (i := i) hbCompact)).restrict U
    have hdbjTop : ParabolicMemLpOn U ∞ (fun z => velocityGradient b z j) :=
      ((velocityGradient_continuous (i := j) hb).memLp_of_hasCompactSupport
        (velocityGradient_compact (i := j) hbCompact)).restrict U
    have hddTop : ParabolicMemLpOn U ∞
        (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian b z i j) :=
      ((velocityHessian_continuous (i := i) (j := j) hb).memLp_of_hasCompactSupport
        (velocityHessian_compact (i := i) (j := j) hbCompact)).restrict U
    have hleftValue : ParabolicMemLpOn U p (fun z => b z * w.velocityGrad z i) :=
      by simpa only [mul_comm] using (w.velocityGrad_memLp i).mul' hbTop
    have hleftDeriv : ParabolicMemLpOn U p
        (fun z => b z * w.velocityHessian z i j + w.velocityGrad z i * velocityGradient b z j) := by
      have hA : ParabolicMemLpOn U p (fun z => b z * w.velocityHessian z i j) :=
        by simpa only [mul_comm] using (w.velocityHessian_memLp i j).mul' hbTop
      have hB : ParabolicMemLpOn U p (fun z => w.velocityGrad z i * velocityGradient b z j) :=
        by simpa only [mul_comm] using (w.velocityGrad_memLp i).mul' hdbjTop
      exact hA.add hB
    have hrightValue : ParabolicMemLpOn U p (fun z => dbi z * w.toFun z) :=
      by simpa only [mul_comm] using w.memLp.mul' hdbiTop
    have hrightDeriv : ParabolicMemLpOn U p
        (fun z => dbi z * w.velocityGrad z j + w.toFun z * velocityGradient dbi z j) := by
      have hA : ParabolicMemLpOn U p (fun z => dbi z * w.velocityGrad z j) :=
        by simpa only [mul_comm] using (w.velocityGrad_memLp j).mul' hdbiTop
      have hB : ParabolicMemLpOn U p
          (fun z => w.toFun z * velocityGradient dbi z j) := by
        have hEq : (fun z => velocityGradient dbi z j) =
            fun z => HypoellipticAleksandrov.Parabolic.velocityHessian b z i j := by
          funext z
          simpa only [dbi] using velocityGradient_velocityGradient hb z
        change ParabolicMemLpOn U p
          (fun z => w.toFun z * (fun z => velocityGradient dbi z j) z)
        rw [hEq]
        simpa only [mul_comm] using (w.memLp.mul' (r := p) hddTop)
      exact hA.add hB
    have hsum := hfirst.add hsecond
      (hleftValue.locallyIntegrableOn hp) (hleftDeriv.locallyIntegrableOn hp)
      (hrightValue.locallyIntegrableOn hp) (hrightDeriv.locallyIntegrableOn hp)
    convert hsum using 1 <;> funext z
    · simp only [dbi]
      ring
    · rw [show velocityGradient dbi z j =
        HypoellipticAleksandrov.Parabolic.velocityHessian b z i j by
          simpa only [dbi] using velocityGradient_velocityGradient hb z]
      simp only [dbi]
      ring

@[simp] theorem mulContDiffHasCompactSupport_toFun {d : ℕ} {U : Set (TimeVelocity d)}
    {p : ℝ≥0∞} (w : ParabolicW12Function d U p) (hp : 1 ≤ p)
    {b : TimeVelocity d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b) :
    (w.mulContDiffHasCompactSupport hp hb hbCompact).toFun = fun z => b z * w.toFun z := rfl

@[simp] theorem mulContDiffHasCompactSupport_timeDeriv {d : ℕ} {U : Set (TimeVelocity d)}
    {p : ℝ≥0∞} (w : ParabolicW12Function d U p) (hp : 1 ≤ p)
    {b : TimeVelocity d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b) :
    (w.mulContDiffHasCompactSupport hp hb hbCompact).timeDeriv =
      fun z => b z * w.timeDeriv z + w.toFun z * timeDerivative b z := rfl

@[simp] theorem mulContDiffHasCompactSupport_velocityGrad {d : ℕ} {U : Set (TimeVelocity d)}
    {p : ℝ≥0∞} (w : ParabolicW12Function d U p) (hp : 1 ≤ p)
    {b : TimeVelocity d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b) :
    (w.mulContDiffHasCompactSupport hp hb hbCompact).velocityGrad =
      fun z i => b z * w.velocityGrad z i + w.toFun z * velocityGradient b z i := rfl

@[simp] theorem mulContDiffHasCompactSupport_velocityHessian {d : ℕ} {U : Set (TimeVelocity d)}
    {p : ℝ≥0∞} (w : ParabolicW12Function d U p) (hp : 1 ≤ p)
    {b : TimeVelocity d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b) :
    (w.mulContDiffHasCompactSupport hp hb hbCompact).velocityHessian =
      fun z i j => b z * w.velocityHessian z i j + velocityGradient b z j * w.velocityGrad z i +
        w.velocityGrad z j * velocityGradient b z i + w.toFun z *
          HypoellipticAleksandrov.Parabolic.velocityHessian b z i j := rfl

end ParabolicW12Function



/-- A relatively compact smooth cutoff localizes a selected weak jet while
preserving all four selected representatives near the plateau compact set. -/
theorem exists_smooth_compact_cutoff_mul_eventuallyEq_jet
    {d : ℕ} {K V : Set (TimeVelocity d)} {p : ℝ≥0∞}
    (hK : IsCompact K) (hV : IsOpen V)
    (hVCompact : IsCompact (closure V)) (hKV : K ⊆ V)
    (w : ParabolicW12Function d V p) (hp : 1 ≤ p) :
    ∃ (b : TimeVelocity d → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
        (hbCompact : HasCompactSupport b),
      (∀ᶠ z in 𝓝ˢ K, b z = 1) ∧
      tsupport b ⊆ V ∧
      (w.mulContDiffHasCompactSupport hp hb hbCompact).toFun
        =ᶠ[𝓝ˢ K] w.toFun ∧
      (w.mulContDiffHasCompactSupport hp hb hbCompact).timeDeriv
        =ᶠ[𝓝ˢ K] w.timeDeriv ∧
      (w.mulContDiffHasCompactSupport hp hb hbCompact).velocityGrad
        =ᶠ[𝓝ˢ K] w.velocityGrad ∧
      (w.mulContDiffHasCompactSupport hp hb hbCompact).velocityHessian
        =ᶠ[𝓝ˢ K] w.velocityHessian  := by
  have hasCompactSupport_of_tsupport_subset_of_isCompact_closure {V : Set (TimeVelocity d)} {b : TimeVelocity d → ℝ} (hbV : tsupport b ⊆ V) (hVCompact : IsCompact (closure V)) :
      HasCompactSupport b := by
    exact IsCompact.of_isClosed_subset hVCompact (isClosed_tsupport (f := b))
      (hbV.trans subset_closure)
  obtain ⟨b, hb, hbOne, hbV⟩ := exists_smooth_cutoff_tsupport_subset hK hV hKV
  obtain ⟨O, hOOpen, hKO, hbO⟩ := eventually_nhdsSet_iff_exists.mp hbOne
  refine ⟨b, hb, (hasCompactSupport_of_tsupport_subset_of_isCompact_closure hbV hVCompact), hbOne, hbV, cutoff_mul_eventuallyEq hbOne, ?_, ?_, ?_⟩
  · filter_upwards [hOOpen.mem_nhdsSet.mpr hKO] with z hzO
    have hbz : b =ᶠ[𝓝 z] fun _ => 1 :=
      (show ∀ᶠ y in 𝓝 z, y ∈ O from hOOpen.mem_nhds hzO).mono
        fun y hy => hbO y hy
    have hdb : timeDerivative b z = 0 := by
      unfold timeDerivative
      rw [hbz.fderiv_eq]
      simp
    simp [hdb, hbO z hzO]
  · filter_upwards [hOOpen.mem_nhdsSet.mpr hKO] with z hzO
    have hbz : b =ᶠ[𝓝 z] fun _ => 1 :=
      (show ∀ᶠ y in 𝓝 z, y ∈ O from hOOpen.mem_nhds hzO).mono
        fun y hy => hbO y hy
    have hgrad : velocityGradient b z = 0 := by
      funext i
      unfold velocityGradient
      rw [hbz.fderiv_eq]
      simp
    simp [hgrad, hbO z hzO]
  · filter_upwards [hOOpen.mem_nhdsSet.mpr hKO] with z hzO
    have hbz : b =ᶠ[𝓝 z] fun _ => 1 :=
      (show ∀ᶠ y in 𝓝 z, y ∈ O from hOOpen.mem_nhds hzO).mono
        fun y hy => hbO y hy
    have hhess : velocityHessian b z = 0 := by
      ext i j
      unfold velocityHessian
      rw [hbz.fderiv.fderiv_eq, fderiv_fun_const]
      simp
    have hgrad : velocityGradient b z = 0 := by
      funext i
      unfold velocityGradient
      rw [hbz.fderiv_eq]
      simp
    simp [hgrad, hhess, hbO z hzO]
    funext i j
    rfl

end HypoellipticAleksandrov.Parabolic

