module

public import HypoellipticAleksandrov.Parabolic.Scaling
public import HypoellipticAleksandrov.Parabolic.LocalHarnackGeometry
import HypoellipticAleksandrov.Parabolic.ForwardPropagationGeometry
import HypoellipticAleksandrov.Parabolic.PeakSelection

/-!
# Endpoint continuity for the local parabolic Harnack box

This module transports closed-box scalar continuity through the normalized
parabolic affine map and records the resulting terminal-face limit.
-/

@[expose] public section

open Filter Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/- Continuity within the normalized closed Harnack box gives the terminal-face
limit along the interior-time approximation. -/
theorem ContinuousOn.tendsto_localHarnackTerminalApprox
    {d : ℕ} {q : TimeVelocity d → ℝ} {v : PDE.Vec d}
    (hq : ContinuousOn q (parabolicClosedBox 2 2 0 0))
    (hv : v ∈ velocityCube (0 : PDE.Vec d) 1) :
    Tendsto (fun j : ℕ => q (localHarnackTerminalApprox j, v)) atTop
      (_root_.nhds (q (8, v))) := by
  let K : Set (TimeVelocity d) := parabolicClosedBox 2 2 0 0
  let zj : ℕ → TimeVelocity d := fun j => (localHarnackTerminalApprox j, v)
  have hzj : Tendsto zj atTop (_root_.nhds (8, v)) := by
    exact HypoellipticAleksandrov.Parabolic.tendsto_localHarnackTerminalApprox.prodMk_nhds
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => v) atTop (_root_.nhds v))
  have hzjMem : ∀ j : ℕ, zj j ∈ K := by
    intro j
    have hj := localHarnackTerminalApprox_mem_normalizedOpenBox (v := v) j hv
    rw [mem_parabolicBox_iff] at hj
    rw [mem_parabolicClosedBox_iff]
    exact ⟨hj.1.le, hj.2.1.le, fun i => (hj.2.2 i).le⟩
  have hzjWithin :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within zj hzj
      (Eventually.of_forall hzjMem)
  have hterminal : (8, v) ∈ parabolicClosedBox 2 2 0 0 := by
      rw [mem_parabolicClosedBox_iff]
      refine ⟨by norm_num, by norm_num, ?_⟩
      intro i
      simpa only [Pi.zero_apply, sub_zero] using (hv i).le.trans (by norm_num : (1 : ℝ) ≤ 2)

    /- Translating the selected elapsed time recovers the terminal approximation. -/
  simpa only [Function.comp_def, zj] using
    (hq (8, v) hterminal).tendsto.comp hzjWithin

end

end HypoellipticAleksandrov.Parabolic
