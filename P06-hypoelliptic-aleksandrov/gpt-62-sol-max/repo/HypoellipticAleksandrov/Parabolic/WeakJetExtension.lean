module

public import HypoellipticAleksandrov.Parabolic.WeakJetCutoff

/-!
# Global extension of cutoff-selected parabolic weak jets

This module transports all selected representatives of a compactly cutoff
local weak jet to the full time--velocity space.  The transport uses the
actual support of every product representative; it is not a generic extension
operator.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Function MeasureTheory Set
open scoped ContDiff ENNReal Topology

section
variable {d : ℕ}

theorem velocityHessian_tsupport {i j : Fin d}
    (f : TimeVelocity d → ℝ) :
    tsupport (fun z => velocityHessian f z i j) ⊆ tsupport f := by
  refine closure_minimal ?_ (isClosed_tsupport (f := f))
  intro z hz
  rw [Function.mem_support] at hz
  by_contra hzero
  have hzero' : f =ᶠ[𝓝 z] fun _ : TimeVelocity d => (0 : ℝ) :=
    notMem_tsupport_iff_eventuallyEq.mp hzero
  apply hz
  unfold velocityHessian
  rw [hzero'.fderiv.fderiv_eq, fderiv_fun_const]
  simp

/-- Support localization for extension to the full spacetime carrier. -/
theorem tsupport_mul_timeDeriv_subset
    (b u du : TimeVelocity d → ℝ) :
    tsupport (fun z => b z * du z + u z * timeDerivative b z) ⊆ tsupport b := by
  refine (tsupport_add _ _).trans (union_subset ?_ ?_)
  · exact tsupport_mul_subset_left
  · exact (tsupport_mul_subset_right (f := u) (g := timeDerivative b)).trans
      (timeDerivative_tsupport b)

/-- Support localization for extension to the full spacetime carrier. -/
theorem tsupport_mul_velocityGrad_subset {i : Fin d}
    (b u dui : TimeVelocity d → ℝ) :
    tsupport (fun z => b z * dui z + u z * velocityGradient b z i) ⊆ tsupport b := by
  refine (tsupport_add _ _).trans (union_subset ?_ ?_)
  · exact tsupport_mul_subset_left
  · exact (tsupport_mul_subset_right (f := u) (g := fun z => velocityGradient b z i)).trans
      (velocityGradient_tsupport b)

/-- Support localization for extension to the full spacetime carrier. -/
theorem tsupport_mul_velocityHessian_subset {i j : Fin d}
    (b u dui duj duij : TimeVelocity d → ℝ) :
    tsupport (fun z => b z * duij z + velocityGradient b z j * dui z +
      duj z * velocityGradient b z i + u z * velocityHessian b z i j) ⊆ tsupport b := by
  refine (tsupport_add _ _).trans (union_subset ?_ ?_)
  refine (tsupport_add _ _).trans (union_subset ?_ ?_)
  refine (tsupport_add _ _).trans (union_subset ?_ ?_)
  · exact tsupport_mul_subset_left
  · exact (tsupport_mul_subset_left (f := fun z => velocityGradient b z j) (g := dui)).trans
      (velocityGradient_tsupport b)
  · exact (tsupport_mul_subset_right (f := duj) (g := fun z => velocityGradient b z i)).trans
      (velocityGradient_tsupport b)
  · exact (tsupport_mul_subset_right (f := u) (g := fun z => velocityHessian b z i j)).trans
      (velocityHessian_tsupport b)

/-- Support localization for extension to the full spacetime carrier. -/
theorem parabolicMemLpOn_univ_of_support_subset {U : Set (TimeVelocity d)} {p : ℝ≥0∞}
    {f : TimeVelocity d → ℝ}
    (hU : MeasurableSet U) (hf : ParabolicMemLpOn U p f)
    (hsupp : Function.support f ⊆ U) :
    ParabolicMemLpOn Set.univ p f := by
  have hindicator := Set.indicator_eq_self.mpr hsupp
  change MemLp f p ((volume : Measure (TimeVelocity d)).restrict Set.univ)
  rw [← hindicator, memLp_indicator_iff_restrict hU]
  simpa only [Measure.restrict_univ] using hf

end

section
variable {d : ℕ} {U K : Set (TimeVelocity d)}

/-- A cutoff equal to one near both supports preserves the weak directional identity. -/
private theorem weak_directional_univ {u du : TimeVelocity d → ℝ}
    (e : TimeVelocity d) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hu : ∀ φ : TimeVelocity d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      (∫ z in U, u z * fderiv ℝ φ z e) = -∫ z in U, du z * φ z)
    (huK : tsupport u ⊆ K) (hduK : tsupport du ⊆ K)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (∫ z, u z * fderiv ℝ φ z e) = -∫ z, du z * φ z := by
  obtain ⟨a, ha, haOne, haU⟩ := exists_smooth_cutoff_tsupport_subset hK hU hKU
  have hEq {z} (hz : z ∈ K) : a * φ =ᶠ[𝓝 z] φ :=
    (cutoff_mul_eventuallyEq haOne).filter_mono (nhds_le_nhdsSet hz)
  have hI (f : TimeVelocity d → ℝ) (hf : tsupport f ⊆ K)
      (g g' : TimeVelocity d → ℝ) (hgg : EqOn g g' K) :
      (∫ z, f z * g z) = ∫ z in U, f z * g' z := by
    have hz0 {z} (hz : z ∉ K) : f z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hz (hf ht))
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)
      (f := fun z => f z * g z) (fun z hz => by rw [hz0 fun h => hz (hKU h), zero_mul])]
    apply setIntegral_congr_fun hU.measurableSet
    intro z _
    change f z * g z = f z * g' z
    by_cases hz : z ∈ K
    · rw [hgg hz]
    · simp [hz0 hz]
  rw [hI u huK (fun z => fderiv ℝ φ z e) (fun z => fderiv ℝ (a * φ) z e)
    (fun _ hz => congrArg (fun A : TimeVelocity d →L[ℝ] ℝ => A e) (hEq hz).fderiv_eq.symm),
    hI du hduK φ (a * φ) (fun _ hz => (hEq hz).eq_of_nhds.symm)]
  exact hu (a * φ) (ha.mul hφ) hc.mul_left (tsupport_mul_subset_left.trans haU)

theorem HasWeakTimeDerivOn.univ_of_compact_tsupport_subset {u du : TimeVelocity d → ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hu : HasWeakTimeDerivOn U u du)
    (huK : tsupport u ⊆ K) (hduK : tsupport du ⊆ K) :
    HasWeakTimeDerivOn Set.univ u du := by
  intro φ hφ hc _
  simpa only [Measure.restrict_univ, timeDerivative] using weak_directional_univ (1, 0) hU hK hKU hu huK hduK φ hφ hc

theorem HasWeakVelocityPartialDerivOn.univ_of_compact_tsupport_subset {i : Fin d}
    {u dui : TimeVelocity d → ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (huK : tsupport u ⊆ K) (hduiK : tsupport dui ⊆ K) :
    HasWeakVelocityPartialDerivOn Set.univ i u dui := by
  intro φ hφ hc _
  simpa only [Measure.restrict_univ, velocityGradient] using
    weak_directional_univ (0, Pi.single i 1) hU hK hKU hu huK hduiK φ hφ hc

end

namespace ParabolicW12Function

/-- A selected weak jet multiplied by an actual smooth compact cutoff supported
in its open domain is a global selected weak jet. -/
noncomputable def mulContDiffHasCompactSupport_univ
    {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞}
    (w : ParabolicW12Function d U p) (hp : 1 ≤ p)
    {b : TimeVelocity d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b) (hU : IsOpen U)
    (hbU : tsupport b ⊆ U) :
    ParabolicW12Function d Set.univ p := by
  let jet := w.mulContDiffHasCompactSupport hp hb hbCompact
  have hKCompact : IsCompact (tsupport b) := hbCompact
  have hvalueK : tsupport jet.toFun ⊆ tsupport b := by
    simpa only [jet, mulContDiffHasCompactSupport_toFun] using
      (tsupport_mul_subset_left (f := b) (g := w.toFun))
  have htimeK : tsupport jet.timeDeriv ⊆ tsupport b := by
    simpa only [jet, mulContDiffHasCompactSupport_timeDeriv] using
      (tsupport_mul_timeDeriv_subset b w.toFun w.timeDeriv)
  have hgradK : ∀ i : Fin d, tsupport (fun z => jet.velocityGrad z i) ⊆ tsupport b := by
    intro i
    simpa only [jet, mulContDiffHasCompactSupport_velocityGrad] using
      (tsupport_mul_velocityGrad_subset (i := i) b w.toFun (fun z => w.velocityGrad z i))
  have hhessianK : ∀ i j : Fin d,
      tsupport (fun z => jet.velocityHessian z i j) ⊆ tsupport b := by
    intro i j
    simpa only [jet, mulContDiffHasCompactSupport_velocityHessian] using
      (tsupport_mul_velocityHessian_subset (i := i) (j := j) b w.toFun
        (fun z => w.velocityGrad z i) (fun z => w.velocityGrad z j)
        (fun z => w.velocityHessian z i j))
  refine
    { toFun := jet.toFun
      timeDeriv := jet.timeDeriv
      velocityGrad := jet.velocityGrad
      velocityHessian := jet.velocityHessian
      memLp := parabolicMemLpOn_univ_of_support_subset hU.measurableSet jet.memLp
        (subset_closure.trans (hvalueK.trans hbU))
      timeDeriv_memLp := parabolicMemLpOn_univ_of_support_subset hU.measurableSet
        jet.timeDeriv_memLp (subset_closure.trans (htimeK.trans hbU))
      velocityGrad_memLp := fun i => parabolicMemLpOn_univ_of_support_subset hU.measurableSet
        (jet.velocityGrad_memLp i)
          (subset_closure.trans ((hgradK i).trans hbU))
      velocityHessian_memLp := fun i j =>
        parabolicMemLpOn_univ_of_support_subset hU.measurableSet
          (jet.velocityHessian_memLp i j)
          (subset_closure.trans ((hhessianK i j).trans hbU))
      hasWeakTimeDeriv := HasWeakTimeDerivOn.univ_of_compact_tsupport_subset hU hKCompact hbU
        jet.hasWeakTimeDeriv hvalueK htimeK
      hasWeakVelocityPartialDeriv := fun i =>
        HasWeakVelocityPartialDerivOn.univ_of_compact_tsupport_subset hU hKCompact hbU
          (jet.hasWeakVelocityPartialDeriv i) hvalueK (hgradK i)
      hasWeakVelocitySecondPartialDeriv := fun i j =>
        HasWeakVelocityPartialDerivOn.univ_of_compact_tsupport_subset hU hKCompact hbU
          (jet.hasWeakVelocitySecondPartialDeriv i j) (hgradK i) (hhessianK i j) }

section
variable {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞} (w : ParabolicW12Function d U p) (hp : 1 ≤ p)
  {b : TimeVelocity d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbCompact : HasCompactSupport b)
  (hU : IsOpen U) (hbU : tsupport b ⊆ U)

/-- Value representative of the global cutoff-product jet. -/
@[simp] theorem mulContDiffHasCompactSupport_univ_toFun :
    (w.mulContDiffHasCompactSupport_univ hp hb hbCompact hU hbU).toFun =
      fun z => b z * w.toFun z := rfl

/-- Time-derivative representative of the global cutoff-product jet. -/
@[simp] theorem mulContDiffHasCompactSupport_univ_timeDeriv :
    (w.mulContDiffHasCompactSupport_univ hp hb hbCompact hU hbU).timeDeriv =
      fun z => b z * w.timeDeriv z + w.toFun z * timeDerivative b z := rfl

/-- Velocity-gradient representative of the global cutoff-product jet. -/
@[simp] theorem mulContDiffHasCompactSupport_univ_velocityGrad :
    (w.mulContDiffHasCompactSupport_univ hp hb hbCompact hU hbU).velocityGrad =
      fun z i => b z * w.velocityGrad z i + w.toFun z * velocityGradient b z i := rfl

/-- Ordered velocity-Hessian representative of the global cutoff-product jet. -/
@[simp] theorem mulContDiffHasCompactSupport_univ_velocityHessian :
    (w.mulContDiffHasCompactSupport_univ hp hb hbCompact hU hbU).velocityHessian =
      fun z i j => b z * w.velocityHessian z i j + velocityGradient b z j * w.velocityGrad z i +
        w.velocityGrad z j * velocityGradient b z i + w.toFun z *
          HypoellipticAleksandrov.Parabolic.velocityHessian b z i j := rfl

end

end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
