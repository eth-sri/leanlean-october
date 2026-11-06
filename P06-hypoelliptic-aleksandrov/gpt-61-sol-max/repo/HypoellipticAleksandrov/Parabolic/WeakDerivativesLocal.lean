module

public import HypoellipticAleksandrov.Parabolic.WeakDerivatives

/-!
# Elementary locality for weak time--velocity derivatives

This module transports the raw weak-derivative predicates across restricted
domains and restricted-volume almost-everywhere representative changes.  It
also packages the corresponding local representative predicate.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace ParabolicMemLpOn

/-- Restricted `L^p` membership is monotone under domain restriction. -/
theorem mono {d : ℕ} {U V : HypoellipticAleksandrov.Parabolic.Region d} {p : ℝ≥0∞}
    {f : HypoellipticAleksandrov.Parabolic.ScalarField d} (hf : ParabolicMemLpOn U p f) (hVU : V ⊆ U) :
    ParabolicMemLpOn V p f :=
  hf.mono_measure (Measure.restrict_mono_set volume hVU)

end ParabolicMemLpOn

namespace HasWeakTimeDerivOn

/-- Change only the value representative in a weak time-derivative identity. -/
theorem congr_value_ae {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d}
    {u v du : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : HasWeakTimeDerivOn U u du)
    (huv : u =ᵐ[timeVelocityVolumeOn U] v) :
    HasWeakTimeDerivOn U v du := by
  intro φ hφSmooth hφCompact hφSupport
  calc
    ∫ z in U, v z * timeDerivative φ z =
        ∫ z in U, u z * timeDerivative φ z := by
      apply integral_congr_ae
      filter_upwards [huv] with z hz
      rw [hz]
    _ = -∫ z in U, du z * φ z := hu φ hφSmooth hφCompact hφSupport

variable {d : ℕ}

/-- Change both representatives in a weak time-derivative identity. -/
theorem congr_ae  {U : HypoellipticAleksandrov.Parabolic.Region d}
    {u v du dv : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : HasWeakTimeDerivOn U u du)
    (huv : u =ᵐ[timeVelocityVolumeOn U] v)
    (hdudv : du =ᵐ[timeVelocityVolumeOn U] dv) :
    HasWeakTimeDerivOn U v dv := by
  intro φ hφSmooth hφCompact hφSupport

  calc
    ∫ z in U, v z * timeDerivative φ z =
        -∫ z in U, du z * φ z :=
      (hu.congr_value_ae huv) φ hφSmooth hφCompact hφSupport
    _ = -∫ z in U, dv z * φ z := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hdudv] with z hz
      rw [hz]

/-- Restrict a raw weak time-derivative identity to any smaller set. -/
theorem restrict  {U V : HypoellipticAleksandrov.Parabolic.Region d}
    {u du : HypoellipticAleksandrov.Parabolic.ScalarField d} (hu : HasWeakTimeDerivOn U u du)
    (hVU : V ⊆ U) : HasWeakTimeDerivOn V u du := by
  intro φ hφSmooth hφCompact hφSupport

  have hValueZero : ∀ z, z ∉ V → u z * timeDerivative φ z = 0 := by
    intro z hz
    have hφEq  :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem
          (fun hzs => hz (hφSupport hzs)) |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    unfold timeDerivative
    rw [Filter.EventuallyEq.fderiv_eq hφEq]
    simp
  have hDerivZero : ∀ z, z ∉ V → du z * φ z = 0 := by
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport (fun hzs => hz (hφSupport hzs))]


  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hValueZero,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hDerivZero,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => hValueZero z (fun hzV => hz (hVU hzV))),
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => hDerivZero z (fun hzV => hz (hVU hzV))),
    (hu φ hφSmooth hφCompact (hφSupport.trans hVU))]

end HasWeakTimeDerivOn

namespace HasWeakVelocityPartialDerivOn

/-- Change only the value representative in a weak velocity-derivative identity. -/
theorem congr_value_ae {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} {i : Fin d}
    {u v dui : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (huv : u =ᵐ[timeVelocityVolumeOn U] v) :
    HasWeakVelocityPartialDerivOn U i v dui := by
  intro φ hφSmooth hφCompact hφSupport
  calc
    ∫ z in U, v z * velocityGradient φ z i =
        ∫ z in U, u z * velocityGradient φ z i := by
      apply integral_congr_ae
      filter_upwards [huv] with z hz
      rw [hz]
    _ = -∫ z in U, dui z * φ z := hu φ hφSmooth hφCompact hφSupport

variable {d : ℕ}

/-- Change both representatives in a weak velocity-derivative identity. -/
theorem congr_ae  {U : HypoellipticAleksandrov.Parabolic.Region d} {i : Fin d}
    {u v dui dvi : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (huv : u =ᵐ[timeVelocityVolumeOn U] v)
    (hduidvi : dui =ᵐ[timeVelocityVolumeOn U] dvi) :
    HasWeakVelocityPartialDerivOn U i v dvi := by
  intro φ hφSmooth hφCompact hφSupport

  calc
    ∫ z in U, v z * velocityGradient φ z i =
        -∫ z in U, dui z * φ z :=
      (hu.congr_value_ae huv) φ hφSmooth hφCompact hφSupport
    _ = -∫ z in U, dvi z * φ z := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hduidvi] with z hz
      rw [hz]

/-- Restrict a raw weak velocity-derivative identity to any smaller set. -/
theorem restrict  {U V : HypoellipticAleksandrov.Parabolic.Region d} {i : Fin d}
    {u dui : HypoellipticAleksandrov.Parabolic.ScalarField d} (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (hVU : V ⊆ U) : HasWeakVelocityPartialDerivOn V i u dui := by
  intro φ hφSmooth hφCompact hφSupport

  have hValueZero : ∀ z, z ∉ V → u z * velocityGradient φ z i = 0 := by
    intro z hz
    have hφEq  :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem
          (fun hzs => hz (hφSupport hzs)) |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    unfold velocityGradient
    rw [Filter.EventuallyEq.fderiv_eq hφEq]
    simp
  have hDerivZero : ∀ z, z ∉ V → dui z * φ z = 0 := by
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport (fun hzs => hz (hφSupport hzs))]


  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hValueZero,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hDerivZero,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => hValueZero z (fun hzV => hz (hVU hzV))),
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => hDerivZero z (fun hzV => hz (hVU hzV))),
    (hu φ hφSmooth hφCompact (hφSupport.trans hVU))]

end HasWeakVelocityPartialDerivOn

namespace ParabolicW12Function

/-- Keep the selected jet representatives while restricting their domain. -/
def restrict {d : ℕ} {U V : HypoellipticAleksandrov.Parabolic.Region d} {p : ℝ≥0∞}
    (w : ParabolicW12Function d U p) (hVU : V ⊆ U) :
    ParabolicW12Function d V p where
  toFun := w.toFun
  timeDeriv := w.timeDeriv
  velocityGrad := w.velocityGrad
  velocityHessian := w.velocityHessian
  memLp := w.memLp.mono hVU
  timeDeriv_memLp := w.timeDeriv_memLp.mono hVU
  velocityGrad_memLp := fun i => (w.velocityGrad_memLp i).mono hVU
  velocityHessian_memLp := fun i j => (w.velocityHessian_memLp i j).mono hVU
  hasWeakTimeDeriv := w.hasWeakTimeDeriv.restrict hVU
  hasWeakVelocityPartialDeriv := fun i =>
    (w.hasWeakVelocityPartialDeriv i).restrict hVU
  hasWeakVelocitySecondPartialDeriv := fun i j =>
    (w.hasWeakVelocitySecondPartialDeriv i j).restrict hVU

end ParabolicW12Function

/-- Local anisotropic weak `W^{1,2,p}` membership, formulated through
compactly-contained open representative witnesses. -/
def ParabolicW12Loc {d : ℕ} (U : HypoellipticAleksandrov.Parabolic.Region d) (p : ℝ≥0∞)
    (u : HypoellipticAleksandrov.Parabolic.ScalarField d) : Prop :=
  ∀ V : HypoellipticAleksandrov.Parabolic.Region d, IsOpen V → IsCompact (closure V) → closure V ⊆ U →
    ∃ w : ParabolicW12Function d V p, w.toFun =ᵐ[timeVelocityVolumeOn V] u



namespace ParabolicW12Loc

/-- Extract the compactly-contained jet witness in the local predicate. -/
theorem exists_parabolicW12Function {d : ℕ} {U V : HypoellipticAleksandrov.Parabolic.Region d}
    {p : ℝ≥0∞} {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : ParabolicW12Loc U p u) (hVOpen : IsOpen V)
    (hVCompact : IsCompact (closure V)) (hVU : closure V ⊆ U) :
    ∃ w : ParabolicW12Function d V p, w.toFun =ᵐ[timeVelocityVolumeOn V] u :=
  hu V hVOpen hVCompact hVU

end ParabolicW12Loc

end HypoellipticAleksandrov.Parabolic
