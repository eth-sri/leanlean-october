module

public import HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Linarith
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
public import PDEFoundation.Calculus.RegularityOrder


open private HypoellipticAleksandrov.Parabolic.integrable_restrict_mul_of_locallyIntegrableOn from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
open private HypoellipticAleksandrov.Parabolic.velocityGradient_tsupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
open private HypoellipticAleksandrov.Parabolic.timeDerivative_tsupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_contDiff_infty from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
open private HypoellipticAleksandrov.Parabolic.velocityGradient_continuous from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
open private HypoellipticAleksandrov.Parabolic.timeDerivative_continuous from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
open private HypoellipticAleksandrov.Parabolic.timeDerivative_compact from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra


/-!
# Smooth compact multipliers for parabolic weak jets

This file records raw distributional product rules on time--velocity space and
uses them to multiply a selected `ParabolicW12Function` jet by a smooth,
compactly supported scalar.  The stored velocity Hessian remains ordered: its
`(i,j)` entry differentiates the selected `i`-gradient in direction `j`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

variable {U : HypoellipticAleksandrov.Parabolic.Region d}




private theorem weak_product_rule

    {u du b : HypoellipticAleksandrov.Parabolic.ScalarField d}
    {D : (HypoellipticAleksandrov.Parabolic.ScalarField d) → HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : ∀ φ : HypoellipticAleksandrov.Parabolic.ScalarField d, ContDiff ℝ PDE.smoothOrder φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z in U, u z * D φ z) = -∫ z in U, du z * φ z)
    (hDmul : ∀ (f g : HypoellipticAleksandrov.Parabolic.ScalarField d), ContDiff ℝ PDE.smoothOrder f →
      ContDiff ℝ PDE.smoothOrder g → ∀ z, D (f * g) z = f z * D g z + g z * D f z)
    (hDcont : ∀ f : HypoellipticAleksandrov.Parabolic.ScalarField d, ContDiff ℝ PDE.smoothOrder f →
      Continuous (D f))
    (hDcompact : ∀ f : HypoellipticAleksandrov.Parabolic.ScalarField d, HasCompactSupport f →
      HasCompactSupport (D f))
    (hDtsupport : ∀ f : HypoellipticAleksandrov.Parabolic.ScalarField d, tsupport (D f) ⊆ tsupport f)
    (hb : ContDiff ℝ PDE.smoothOrder b)
    (huLoc : LocallyIntegrableOn u U )
    (hduLoc : LocallyIntegrableOn du U ) :
    ∀ φ : HypoellipticAleksandrov.Parabolic.ScalarField d, ContDiff ℝ PDE.smoothOrder φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z in U, (b z * u z) * D φ z) =
        -∫ z in U, (b z * du z + u z * D b z) * φ z := by
  intro φ hφ hφCompact hφSub
  let μU  := timeVelocityVolumeOn U
  let dφ  := D φ
  let db  := D b
  let φb  := b * φ

  have hφCont : Continuous φ := hφ.continuous




  have hφbSmooth : ContDiff ℝ PDE.smoothOrder φb := hb.mul hφ
  have hφbCompact : HasCompactSupport φb := by
    exact hφCompact.mul_left


  have hφbSub : tsupport φb ⊆ U :=
    (tsupport_mul_subset_right (f := b) (g := φ)).trans hφSub

  have huWeak :
      (∫ z, u z * D φb z ∂μU) = -∫ z, du z * φb z ∂μU := by
    exact hu φb hφbSmooth hφbCompact hφbSub



  have hφdbCont : Continuous (fun z => φ z * db z) := hφCont.mul (hDcont b hb)
  have hφdbCompact : HasCompactSupport (fun z => φ z * db z) := by
    exact hφCompact.mul_right
  have hφdbSub : tsupport (fun z => φ z * db z) ⊆ U :=
    tsupport_mul_subset_left.trans hφSub





  have hproduct : ∀ z, D φb z = b z * dφ z + φ z * db z := by
    intro z
    exact hDmul b φ hb hφ z
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
        rw [integral_sub (_root_.HypoellipticAleksandrov.Parabolic.integrable_restrict_mul_of_locallyIntegrableOn huLoc (hDcont φb hφbSmooth) (hDcompact φb hφbCompact) ((hDtsupport φb).trans hφbSub)) (_root_.HypoellipticAleksandrov.Parabolic.integrable_restrict_mul_of_locallyIntegrableOn huLoc hφdbCont hφdbCompact hφdbSub)]
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
            simp only [φb, Pi.mul_apply]
            ring
        _ = (∫ z, du z * φb z ∂μU) + ∫ z, (u z * db z) * φ z ∂μU := by
          rw [integral_add (_root_.HypoellipticAleksandrov.Parabolic.integrable_restrict_mul_of_locallyIntegrableOn hduLoc
                  (hb.continuous.mul hφCont) hφbCompact hφbSub) (by
              simpa only [μU, mul_comm, mul_left_comm] using
                _root_.HypoellipticAleksandrov.Parabolic.integrable_restrict_mul_of_locallyIntegrableOn huLoc hφdbCont hφdbCompact hφdbSub)]
    have huTerm :
        (∫ z, u z * (φ z * db z) ∂μU) =
          ∫ z, (u z * db z) * φ z ∂μU := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    rw [huTerm, hsum]
    ring
  linarith

private theorem timeDerivative_mul
     (f g : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ContDiff ℝ PDE.smoothOrder f) (hg : ContDiff ℝ PDE.smoothOrder g) (z : TimeVelocity d) :
    timeDerivative (f * g) z = f z * timeDerivative g z + g z * timeDerivative f z := by
  unfold timeDerivative
  rw [fderiv_mul (hf.contDiffAt.differentiableAt (by simp))
    (hg.contDiffAt.differentiableAt (by simp))]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]









private theorem velocityGradient_mul  {i : Fin d}
    (f g : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ContDiff ℝ PDE.smoothOrder f) (hg : ContDiff ℝ PDE.smoothOrder g) (z : TimeVelocity d) :
    velocityGradient (f * g) z i =
      f z * velocityGradient g z i + g z * velocityGradient f z i := by
  unfold velocityGradient
  rw [fderiv_mul (hf.contDiffAt.differentiableAt (by simp))
    (hg.contDiffAt.differentiableAt (by simp))]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]









namespace HasWeakTimeDerivOn

/-- Smooth scalar multiplication obeys the raw weak time-derivative product rule. -/
theorem mul_contDiff {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} {u du b : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : HasWeakTimeDerivOn U u du) (hb : ContDiff ℝ PDE.smoothOrder b)
    (huLoc : LocallyIntegrableOn u U )
    (hduLoc : LocallyIntegrableOn du U ) :
    HasWeakTimeDerivOn U (fun z => b z * u z)
      (fun z => b z * du z + u z * timeDerivative b z) := weak_product_rule hu timeDerivative_mul
    (fun f hf => _root_.HypoellipticAleksandrov.Parabolic.timeDerivative_continuous hf)
    (fun f hf => _root_.HypoellipticAleksandrov.Parabolic.timeDerivative_compact hf) _root_.HypoellipticAleksandrov.Parabolic.timeDerivative_tsupport hb huLoc hduLoc

end HasWeakTimeDerivOn

namespace HasWeakVelocityPartialDerivOn

/-- Smooth scalar multiplication obeys the raw weak velocity product rule. -/
theorem mul_contDiff {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} {i : Fin d}
    {u dui b : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : HasWeakVelocityPartialDerivOn U i u dui) (hb : ContDiff ℝ PDE.smoothOrder b)
    (huLoc : LocallyIntegrableOn u U )
    (hduiLoc : LocallyIntegrableOn dui U ) :
    HasWeakVelocityPartialDerivOn U i (fun z => b z * u z)
      (fun z => b z * dui z + u z * velocityGradient b z i) := weak_product_rule hu
    (velocityGradient_mul)
    (fun f hf => _root_.HypoellipticAleksandrov.Parabolic.velocityGradient_continuous hf)
    (fun f hf => _root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport hf) _root_.HypoellipticAleksandrov.Parabolic.velocityGradient_tsupport hb huLoc hduiLoc

end HasWeakVelocityPartialDerivOn

variable {d : ℕ}

variable {f : HypoellipticAleksandrov.Parabolic.ScalarField d}




variable {i j : Fin d}

private theorem velocityHessian_continuous
     (hf : ContDiff ℝ PDE.smoothOrder f) :
    Continuous (fun z => velocityHessian f z i j) := by
  unfold velocityHessian

  simpa using (((contDiff_infty_iff_fderiv.mp hf).2).continuous_fderiv (by simp)).clm_apply continuous_const |>.clm_apply
    continuous_const

private theorem velocityHessian_compact
     (hf : HasCompactSupport f) :
    HasCompactSupport (fun z => velocityHessian f z i j) := by
  unfold velocityHessian


  simpa only [Function.comp_def] using ((hf.fderiv ℝ).fderiv ℝ).comp_left
    (g := fun H : TimeVelocity d →L[ℝ] TimeVelocity d →L[ℝ] ℝ =>
      H ((0, Pi.single i 1) ) ((0, Pi.single j 1) )) rfl

private theorem velocityGradient_velocityGradient  {b : HypoellipticAleksandrov.Parabolic.ScalarField d}
    {i j : Fin d} (hb : ContDiff ℝ PDE.smoothOrder b) (z : TimeVelocity d) :
    velocityGradient (fun y => velocityGradient b y i) z j =
      HypoellipticAleksandrov.Parabolic.velocityHessian b z i j := by
  let sharedTerm_aee9fc69cd := (((0, Pi.single i 1) : TimeVelocity d))



  have hsymm := velocityHessian_isSymm
    (hb.of_le (by
      simp_all)) z
  exact (show velocityGradient (fun y => velocityGradient b y i) z j =
      HypoellipticAleksandrov.Parabolic.velocityHessian b z j i by
      unfold velocityGradient HypoellipticAleksandrov.Parabolic.velocityHessian
      rw [fderiv_clm_apply (((contDiff_infty_iff_fderiv.mp hb).2).contDiffAt.differentiableAt (by simp)) (differentiableAt_const _)]

      rw [((hasFDerivAt_const sharedTerm_aee9fc69cd z).fderiv)]
      simp).trans (hsymm.apply i j)

namespace ParabolicW12Function

/-- Multiply a raw parabolic weak jet by a globally smooth compactly supported scalar. -/
def mulContDiffHasCompactSupport {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} {p : ℝ≥0∞}
    (w : ParabolicW12Function d U p) (hp : 1 ≤ p) {b : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hb : ContDiff ℝ PDE.smoothOrder b) (hbCompact : HasCompactSupport b) :
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
      ((_root_.HypoellipticAleksandrov.Parabolic.timeDerivative_continuous hb).memLp_of_hasCompactSupport
        (_root_.HypoellipticAleksandrov.Parabolic.timeDerivative_compact hbCompact)).restrict U
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
      ((_root_.HypoellipticAleksandrov.Parabolic.velocityGradient_continuous hb).memLp_of_hasCompactSupport
        (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport hbCompact)).restrict U
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
      ((_root_.HypoellipticAleksandrov.Parabolic.velocityGradient_continuous hb).memLp_of_hasCompactSupport
        (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport hbCompact)).restrict U
    have hdbjTop : ParabolicMemLpOn U ∞ (fun z => velocityGradient b z j) :=
      ((_root_.HypoellipticAleksandrov.Parabolic.velocityGradient_continuous hb).memLp_of_hasCompactSupport
        (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport hbCompact)).restrict U
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
  hasWeakTimeDeriv := w.hasWeakTimeDeriv.mul_contDiff hb
      (w.memLp.locallyIntegrableOn hp) (w.timeDeriv_memLp.locallyIntegrableOn hp)
  hasWeakVelocityPartialDeriv := by
    intro i
    exact (w.hasWeakVelocityPartialDeriv i).mul_contDiff hb
      (w.memLp.locallyIntegrableOn hp) ((w.velocityGrad_memLp i).locallyIntegrableOn hp)
  hasWeakVelocitySecondPartialDeriv := by
    intro i j
    let dbi  := fun z => velocityGradient b z i
    have hdbi : ContDiff ℝ PDE.smoothOrder dbi := _root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_contDiff_infty hb
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
        ((_root_.HypoellipticAleksandrov.Parabolic.velocityGradient_continuous (i := i) hb).memLp_of_hasCompactSupport
          (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport  hbCompact)).restrict U
    have hdbjTop : ParabolicMemLpOn U ∞ (fun z => velocityGradient b z j) :=
      ((_root_.HypoellipticAleksandrov.Parabolic.velocityGradient_continuous (i := j) hb).memLp_of_hasCompactSupport
        (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport  hbCompact)).restrict U
    have hddTop : ParabolicMemLpOn U ∞
        (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian b z i j) :=
      ((velocityHessian_continuous (i := i) (j := j) hb).memLp_of_hasCompactSupport
        (velocityHessian_compact   hbCompact)).restrict U
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
          exact velocityGradient_velocityGradient hb z
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
          exact velocityGradient_velocityGradient hb z]
      simp only [dbi]
      ring

variable {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} {p : ℝ≥0∞} (w : ParabolicW12Function d U p) (hp : 1 ≤ p) {b : HypoellipticAleksandrov.Parabolic.ScalarField d} (hb : ContDiff ℝ PDE.smoothOrder b) (hbCompact : HasCompactSupport b)

@[simp] theorem mulContDiffHasCompactSupport_toFun  :
    (w.mulContDiffHasCompactSupport hp hb hbCompact).toFun = fun z => b z * w.toFun z := rfl

@[simp] theorem mulContDiffHasCompactSupport_timeDeriv  :
    (w.mulContDiffHasCompactSupport hp hb hbCompact).timeDeriv =
      fun z => b z * w.timeDeriv z + w.toFun z * timeDerivative b z := rfl

@[simp] theorem mulContDiffHasCompactSupport_velocityGrad  :
    (w.mulContDiffHasCompactSupport hp hb hbCompact).velocityGrad =
      fun z i => b z * w.velocityGrad z i + w.toFun z * velocityGradient b z i := rfl

@[simp] theorem mulContDiffHasCompactSupport_velocityHessian  :
    (w.mulContDiffHasCompactSupport hp hb hbCompact).velocityHessian =
      fun z i j => b z * w.velocityHessian z i j + velocityGradient b z j * w.velocityGrad z i +
        w.velocityGrad z j * velocityGradient b z i + w.toFun z *
          HypoellipticAleksandrov.Parabolic.velocityHessian b z i j := rfl

end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
