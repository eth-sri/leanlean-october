module

public import HypoellipticAleksandrov.Parabolic.LocalGluing
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Compact cutoff localization for selected parabolic weak jets

This module combines the smooth cutoff construction with the compactly
supported weak-jet product and records locality of every selected jet component
on the cutoff plateau.
-/

 public section



open Filter Set
open scoped ContDiff ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

/-- A cutoff supported in a relatively compact set has compact support. -/
theorem hasCompactSupport_of_tsupport_subset_of_isCompact_closure
    {d : ℕ} {V : HypoellipticAleksandrov.Parabolic.Region d} {b : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hbV : tsupport b ⊆ V) (hVCompact : IsCompact (closure V)) :
    HasCompactSupport b := (id (IsCompact.of_isClosed_subset hVCompact (isClosed_tsupport b) (LE.le.trans hbV subset_closure)))

/-- A relatively compact smooth cutoff localizes a selected weak jet while
preserving all four selected representatives near the plateau compact set. -/
theorem exists_smooth_compact_cutoff_mul_eventuallyEq_jet
    {d : ℕ} {K V : HypoellipticAleksandrov.Parabolic.Region d} {p : ℝ≥0∞}
    (hK : IsCompact K) (hV : IsOpen V)
    (hVCompact : IsCompact (closure V)) (hKV : K ⊆ V)
    (w : ParabolicW12Function d V p) (hp : 1 ≤ p) :
    ∃ (b : HypoellipticAleksandrov.Parabolic.ScalarField d) (hb : ContDiff ℝ PDE.smoothOrder b)
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
        =ᶠ[𝓝ˢ K] w.velocityHessian := by
  obtain ⟨b, hb, hbOne, hbV⟩ := exists_smooth_cutoff_tsupport_subset hK hV hKV

  obtain ⟨O, hOOpen, hKO, hbO⟩ := eventually_nhdsSet_iff_exists.mp hbOne
  refine ⟨b, hb, (hasCompactSupport_of_tsupport_subset_of_isCompact_closure hbV hVCompact), hbOne, hbV, cutoff_mul_eventuallyEq hbOne, ?_, ?_, ?_⟩
  · filter_upwards [hOOpen.mem_nhdsSet.mpr hKO] with z hzO
    have hbz : b =ᶠ[𝓝 z] fun _  => (1 ) :=
      (show ∀ᶠ y in 𝓝 z, y ∈ O from hOOpen.mem_nhds hzO).mono
        fun y hy => hbO y hy
    have hdb : timeDerivative b z = 0 := by
      unfold timeDerivative
      rw [hbz.fderiv_eq]
      simp
    simp [hdb, hbO z hzO]
  · filter_upwards [hOOpen.mem_nhdsSet.mpr hKO] with z hzO
    have hbz : b =ᶠ[𝓝 z] fun _  => (1 ) :=
      (show ∀ᶠ y in 𝓝 z, y ∈ O from hOOpen.mem_nhds hzO).mono
        fun y hy => hbO y hy
    have hgrad : velocityGradient b z = 0 := by
      funext i
      unfold velocityGradient
      rw [hbz.fderiv_eq]
      simp
    simp [hgrad, hbO z hzO]
  · filter_upwards [hOOpen.mem_nhdsSet.mpr hKO] with z hzO
    have hbz : b =ᶠ[𝓝 z] fun _  => (1 ) :=
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
