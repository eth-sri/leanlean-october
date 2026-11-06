module

public import HypoellipticAleksandrov.Parabolic.WeakJetCutoff
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder



open private HypoellipticAleksandrov.Parabolic.velocityGradient_tsupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
open private HypoellipticAleksandrov.Parabolic.timeDerivative_tsupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra


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

variable {d : ℕ}







private theorem velocityHessian_tsupport  {i j : Fin d}
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    tsupport (fun z => velocityHessian f z i j) ⊆ tsupport f := by
  refine closure_minimal ?_ (isClosed_tsupport (f := f))
  intro z hz
  rw [Function.mem_support] at hz
  by_contra hzero
  have hzero' : f =ᶠ[𝓝 z] fun _  => (0 ) :=
    notMem_tsupport_iff_eventuallyEq.mp hzero
  apply hz
  unfold velocityHessian
  rw [hzero'.fderiv.fderiv_eq, fderiv_fun_const]
  simp

/-- Support localization for extension to the full spacetime carrier. -/
theorem tsupport_mul_timeDeriv_subset
    (b u du : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    tsupport (fun z => b z * du z + u z * timeDerivative b z) ⊆ tsupport b := by
  refine (tsupport_add _ _).trans (union_subset ?_ ?_)
  · exact tsupport_mul_subset_left
  · exact (tsupport_mul_subset_right (f := u) (g := timeDerivative b)).trans
      (_root_.HypoellipticAleksandrov.Parabolic.timeDerivative_tsupport b)

/-- Support localization for extension to the full spacetime carrier. -/
theorem tsupport_mul_velocityGrad_subset  {i : Fin d}
    (b u dui : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    tsupport (fun z => b z * dui z + u z * velocityGradient b z i) ⊆ tsupport b := (LE.le.trans (tsupport_add (fun z => b z * dui z) fun z => u z * velocityGradient b z i)
  (union_subset tsupport_mul_subset_left (LE.le.trans tsupport_mul_subset_right (velocityGradient_tsupport b))))

/-- Support localization for extension to the full spacetime carrier. -/
theorem tsupport_mul_velocityHessian_subset  {i j : Fin d}
    (b u dui duj duij : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    tsupport (fun z => b z * duij z + velocityGradient b z j * dui z +
      duj z * velocityGradient b z i + u z * velocityHessian b z i j) ⊆ tsupport b := by
  refine (tsupport_add _ _).trans (union_subset ?_ ?_)
  refine (tsupport_add _ _).trans (union_subset ?_ ?_)
  refine (tsupport_add _ _).trans (union_subset ?_ ?_)
  · exact tsupport_mul_subset_left
  · exact (tsupport_mul_subset_left (f := fun z => velocityGradient b z j) (g := dui)).trans
      (_root_.HypoellipticAleksandrov.Parabolic.velocityGradient_tsupport b)
  · exact (tsupport_mul_subset_right (f := duj) (g := fun z => velocityGradient b z i)).trans
      (_root_.HypoellipticAleksandrov.Parabolic.velocityGradient_tsupport b)
  · exact (tsupport_mul_subset_right (f := u) (g := fun z => velocityHessian b z i j)).trans
      (velocityHessian_tsupport b)

/-- Support localization for extension to the full spacetime carrier. -/
theorem parabolicMemLpOn_univ_of_support_subset
     {U : HypoellipticAleksandrov.Parabolic.Region d} {p : ℝ≥0∞}
    {f : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hU : MeasurableSet U) (hf : ParabolicMemLpOn U p f)
    (hsupp : Function.support f ⊆ U) :
    ParabolicMemLpOn Set.univ p f := by

  change MemLp f p ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict Set.univ)
  rw [← (Set.indicator_eq_self.mpr hsupp), memLp_indicator_iff_restrict hU]
  simpa only [Measure.restrict_univ] using hf

variable {U K : HypoellipticAleksandrov.Parabolic.Region d}

/-- Support localization for extension to the full spacetime carrier. -/
theorem HasWeakTimeDerivOn.univ_of_compact_tsupport_subset
      {u du : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hu : HasWeakTimeDerivOn U u du)
    (huK : tsupport u ⊆ K) (hduK : tsupport du ⊆ K) :
    HasWeakTimeDerivOn Set.univ u du := by
  intro φ hφ hφCompact _
  obtain ⟨a, ha, haOne, haU⟩ := exists_smooth_cutoff_tsupport_subset hK hU hKU
  obtain ⟨O, hOOpen, hKO, haO⟩ := eventually_nhdsSet_iff_exists.mp haOne
  have haφ : ContDiff ℝ PDE.smoothOrder (a * φ) := ha.mul hφ
  have haφCompact : HasCompactSupport (a * φ) := by
    exact hφCompact.mul_left
  have haφU : tsupport (a * φ) ⊆ U :=
    (tsupport_mul_subset_left (f := a) (g := φ)).trans haU





  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (show ∀ z, z ∉ U → u z * timeDerivative φ z = 0 by
      intro z hzU

      simp [(image_eq_zero_of_notMem_tsupport (fun htz => hzU (hKU (huK htz))))]),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (show ∀ z, z ∉ U → du z * φ z = 0 by
        intro z hzU

        simp [(image_eq_zero_of_notMem_tsupport (fun htz => hzU (hKU (hduK htz))))]),
    setIntegral_congr_fun hU.measurableSet (show EqOn (fun z => u z * timeDerivative φ z)
      (fun z => u z * timeDerivative (a * φ) z) U by
        intro z hzU
        by_cases hzK : z ∈ K
        · have hza : a * φ =ᶠ[𝓝 z] φ := by
            filter_upwards [hOOpen.mem_nhds (hKO hzK)] with y hy
            simp only [Pi.mul_apply, haO y hy, one_mul]

          exact congrArg (fun r => u z * r) (show timeDerivative (a * φ) z = timeDerivative φ z by
              unfold timeDerivative
              rw [hza.fderiv_eq]).symm
        · have huzero  :=
            image_eq_zero_of_notMem_tsupport (fun htz => hzK (huK htz))
          simp [huzero]),
    setIntegral_congr_fun hU.measurableSet (show EqOn (fun z => du z * φ z) (fun z => du z * (a * φ) z) U by
        intro z hzU
        by_cases hzK : z ∈ K
        ·
          exact congrArg (fun r => du z * r) (show a * φ =ᶠ[𝓝 z] φ by
              filter_upwards [hOOpen.mem_nhds (hKO hzK)] with y hy
              simp only [Pi.mul_apply, haO y hy, one_mul]).eq_of_nhds.symm
        · have hduzero  :=
            image_eq_zero_of_notMem_tsupport (fun htz => hzK (hduK htz))
          simp [hduzero])]
  simpa only [Measure.restrict_univ] using (hu (a * φ) haφ haφCompact haφU)

/-- Support localization for extension to the full spacetime carrier. -/
theorem HasWeakVelocityPartialDerivOn.univ_of_compact_tsupport_subset
      {i : Fin d}
    {u dui : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (huK : tsupport u ⊆ K) (hduiK : tsupport dui ⊆ K) :
    HasWeakVelocityPartialDerivOn Set.univ i u dui := by
  intro φ hφ hφCompact _
  obtain ⟨a, ha, haOne, haU⟩ := exists_smooth_cutoff_tsupport_subset hK hU hKU
  obtain ⟨O, hOOpen, hKO, haO⟩ := eventually_nhdsSet_iff_exists.mp haOne
  have haφ : ContDiff ℝ PDE.smoothOrder (a * φ) := ha.mul hφ
  have haφCompact : HasCompactSupport (a * φ) := by
    exact hφCompact.mul_left
  have haφU : tsupport (a * φ) ⊆ U :=
    (tsupport_mul_subset_left (f := a) (g := φ)).trans haU





  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (show ∀ z, z ∉ U → u z * velocityGradient φ z i = 0 by
      intro z hzU

      simp [(image_eq_zero_of_notMem_tsupport (fun htz => hzU (hKU (huK htz))))]),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (show ∀ z, z ∉ U → dui z * φ z = 0 by
        intro z hzU

        simp [(image_eq_zero_of_notMem_tsupport (fun htz => hzU (hKU (hduiK htz))))]),
    setIntegral_congr_fun hU.measurableSet (show EqOn (fun z => u z * velocityGradient φ z i)
      (fun z => u z * velocityGradient (a * φ) z i) U by
        intro z hzU
        by_cases hzK : z ∈ K
        · have hza : a * φ =ᶠ[𝓝 z] φ := by
            filter_upwards [hOOpen.mem_nhds (hKO hzK)] with y hy
            simp only [Pi.mul_apply, haO y hy, one_mul]

          exact congrArg (fun r => u z * r) (show velocityGradient (a * φ) z i = velocityGradient φ z i by
              unfold velocityGradient
              rw [hza.fderiv_eq]).symm
        · have huzero  :=
            image_eq_zero_of_notMem_tsupport (fun htz => hzK (huK htz))
          simp [huzero]),
    setIntegral_congr_fun hU.measurableSet (show EqOn (fun z => dui z * φ z) (fun z => dui z * (a * φ) z) U by
        intro z hzU
        by_cases hzK : z ∈ K
        ·
          exact congrArg (fun r => dui z * r) (show a * φ =ᶠ[𝓝 z] φ by
              filter_upwards [hOOpen.mem_nhds (hKO hzK)] with y hy
              simp only [Pi.mul_apply, haO y hy, one_mul]).eq_of_nhds.symm
        · have hduizero  :=
            image_eq_zero_of_notMem_tsupport (fun htz => hzK (hduiK htz))
          simp [hduizero])]
  simpa only [Measure.restrict_univ] using (hu (a * φ) haφ haφCompact haφU)

namespace ParabolicW12Function

/-- A selected weak jet multiplied by an actual smooth compact cutoff supported
in its open domain is a global selected weak jet. -/
def mulContDiffHasCompactSupport_univ
    {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} {p : ℝ≥0∞}
    (w : ParabolicW12Function d U p) (hp : 1 ≤ p)
    {b : HypoellipticAleksandrov.Parabolic.ScalarField d} (hb : ContDiff ℝ PDE.smoothOrder b)
    (hbCompact : HasCompactSupport b) (hU : IsOpen U)
    (hbU : tsupport b ⊆ U) :
    ParabolicW12Function d Set.univ p := by
  let jet := w.mulContDiffHasCompactSupport hp hb hbCompact
  have hKCompact : IsCompact (tsupport b) := hbCompact
  have hvalueK : tsupport jet.toFun ⊆ tsupport b := by
    exact (tsupport_mul_subset_left  )
  have htimeK : tsupport jet.timeDeriv ⊆ tsupport b := by
    exact (tsupport_mul_timeDeriv_subset b w.toFun w.timeDeriv)
  have hgradK : ∀ i : Fin d, tsupport (fun z => jet.velocityGrad z i) ⊆ tsupport b := by
    intro i
    exact (tsupport_mul_velocityGrad_subset  b w.toFun (fun z => w.velocityGrad z i))
  have hhessianK : ∀ i j : Fin d,
      tsupport (fun z => jet.velocityHessian z i j) ⊆ tsupport b := by
    intro i j
    exact (tsupport_mul_velocityHessian_subset   b w.toFun
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

variable {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} {p : ℝ≥0∞} (w : ParabolicW12Function d U p) (hp : 1 ≤ p) {b : HypoellipticAleksandrov.Parabolic.ScalarField d} (hb : ContDiff ℝ PDE.smoothOrder b) (hbCompact : HasCompactSupport b) (hU : IsOpen U) (hbU : tsupport b ⊆ U)









end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
