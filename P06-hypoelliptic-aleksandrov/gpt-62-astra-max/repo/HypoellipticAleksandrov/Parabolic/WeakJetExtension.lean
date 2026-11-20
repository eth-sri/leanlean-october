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
variable {d : ℕ} {U K : Set (TimeVelocity d)} {i : Fin d} (f : TimeVelocity d → ℝ)

private theorem timeDerivative_tsupport :
    tsupport (timeDerivative f) ⊆ tsupport f := by
  unfold timeDerivative
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

private theorem velocityGradient_tsupport :
    tsupport (fun z => velocityGradient f z i) ⊆ tsupport f := by
  unfold velocityGradient
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

private theorem velocityHessian_tsupport {i j : Fin d}
    (f : TimeVelocity d → ℝ) :
    tsupport (fun z => velocityHessian f z i j) ⊆ tsupport f := by
  refine closure_minimal ?_ (isClosed_tsupport (f := f))
  intro z hz
  rw [Function.mem_support] at hz
  by_contra hzero
  have hzero' : f =ᶠ[𝓝 z] fun _ : TimeVelocity d => 0 :=
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
theorem tsupport_mul_velocityGrad_subset
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
  change MemLp f p (volume.restrict Set.univ)
  rw [← hindicator, memLp_indicator_iff_restrict hU]
  simpa using hf

/-- Support localization for extension to the full spacetime carrier. -/
theorem HasWeakTimeDerivOn.univ_of_compact_tsupport_subset {u du : TimeVelocity d → ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hu : HasWeakTimeDerivOn U u du)
    (huK : tsupport u ⊆ K) (hduK : tsupport du ⊆ K) :
    HasWeakTimeDerivOn Set.univ u du := by
  intro φ hφ hφCompact _
  obtain ⟨a, ha, haOne, haU⟩ := exists_smooth_cutoff_tsupport_subset hK hU hKU
  obtain ⟨O, hOOpen, hKO, haO⟩ := eventually_nhdsSet_iff_exists.mp haOne
  have haφCompact : HasCompactSupport (a * φ) := by
    exact hφCompact.mul_left (f := a)
  have hlocal := hu (a * φ) (ha.mul hφ) haφCompact ((tsupport_mul_subset_left (f := a) (g := φ)).trans haU)
  have hleft : EqOn (fun z => u z * timeDerivative φ z)
      (fun z => u z * timeDerivative (a * φ) z) U := by
    intro z hzU
    by_cases hzK : z ∈ K
    · have hza : a * φ =ᶠ[𝓝 z] φ := by
        filter_upwards [hOOpen.mem_nhds (hKO hzK)] with y hy
        simp [haO y hy]
      have hderiv : timeDerivative (a * φ) z = timeDerivative φ z := by
        unfold timeDerivative
        rw [hza.fderiv_eq]
      apply_rules [congrArg]
    · simp [(image_eq_zero_of_notMem_tsupport (fun htz => hzK (huK htz)))]
  have hright : EqOn (fun z => du z * φ z) (fun z => du z * (a * φ) z) U := by
    intro z hzU
    by_cases hzK : z ∈ K
    · have hza : a * φ =ᶠ[𝓝 z] φ := by
        filter_upwards [hOOpen.mem_nhds (hKO hzK)] with y hy
        simp [haO y hy]
      exact congrArg (fun r => du z * r) hza.eq_of_nhds.symm
    · simp [(image_eq_zero_of_notMem_tsupport (fun htz => hzK (hduK htz)))]
  have hvalueZero : ∀ z, z ∉ U → u z * timeDerivative φ z = 0 := by
    intro z hzU
    simp [(image_eq_zero_of_notMem_tsupport (fun htz => hzU (hKU (huK htz))))]
  have hderivZero : ∀ z, z ∉ U → du z * φ z = 0 := by
    intro z hzU
    simp [(image_eq_zero_of_notMem_tsupport (fun htz => hzU (hKU (hduK htz))))]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvalueZero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hderivZero,
    setIntegral_congr_fun hU.measurableSet hleft,
    setIntegral_congr_fun hU.measurableSet hright]
  simpa using hlocal

/-- Support localization for extension to the full spacetime carrier. -/
theorem HasWeakVelocityPartialDerivOn.univ_of_compact_tsupport_subset
    {u dui : TimeVelocity d → ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (huK : tsupport u ⊆ K) (hduiK : tsupport dui ⊆ K) :
    HasWeakVelocityPartialDerivOn Set.univ i u dui := by
  intro φ hφ hφCompact _
  obtain ⟨a, ha, haOne, haU⟩ := exists_smooth_cutoff_tsupport_subset hK hU hKU
  obtain ⟨O, hOOpen, hKO, haO⟩ := eventually_nhdsSet_iff_exists.mp haOne
  have haφCompact : HasCompactSupport (a * φ) := by
    exact hφCompact.mul_left (f := a)
  have hlocal := hu (a * φ) (ha.mul hφ) haφCompact ((tsupport_mul_subset_left (f := a) (g := φ)).trans haU)
  have hleft : EqOn (fun z => u z * velocityGradient φ z i)
      (fun z => u z * velocityGradient (a * φ) z i) U := by
    intro z hzU
    by_cases hzK : z ∈ K
    · have hza : a * φ =ᶠ[𝓝 z] φ := by
        filter_upwards [hOOpen.mem_nhds (hKO hzK)] with y hy
        simp [haO y hy]
      have hderiv : velocityGradient (a * φ) z i = velocityGradient φ z i := by
        unfold velocityGradient
        rw [hza.fderiv_eq]
      apply_rules [congrArg]
    · simp [(image_eq_zero_of_notMem_tsupport (fun htz => hzK (huK htz)))]
  have hright : EqOn (fun z => dui z * φ z) (fun z => dui z * (a * φ) z) U := by
    intro z hzU
    by_cases hzK : z ∈ K
    · have hza : a * φ =ᶠ[𝓝 z] φ := by
        filter_upwards [hOOpen.mem_nhds (hKO hzK)] with y hy
        simp [haO y hy]
      exact congrArg (fun r => dui z * r) hza.eq_of_nhds.symm
    · simp [(image_eq_zero_of_notMem_tsupport (fun htz => hzK (hduiK htz)))]
  have hvalueZero : ∀ z, z ∉ U → u z * velocityGradient φ z i = 0 := by
    intro z hzU
    simp [(image_eq_zero_of_notMem_tsupport (fun htz => hzU (hKU (huK htz))))]
  have hderivZero : ∀ z, z ∉ U → dui z * φ z = 0 := by
    intro z hzU
    simp [(image_eq_zero_of_notMem_tsupport (fun htz => hzU (hKU (hduiK htz))))]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvalueZero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hderivZero,
    setIntegral_congr_fun hU.measurableSet hleft,
    setIntegral_congr_fun hU.measurableSet hright]
  simpa using hlocal

end

namespace ParabolicW12Function

variable {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞} (w : ParabolicW12Function d U p)
    (hp : 1 ≤ p) {b : TimeVelocity d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b) (hU : IsOpen U) (hbU : tsupport b ⊆ U)

include w hp hb hbCompact hU hbU in
/-- A selected weak jet multiplied by an actual smooth compact cutoff supported
in its open domain is a global selected weak jet. -/
noncomputable def mulContDiffHasCompactSupport_univ :
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

end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
