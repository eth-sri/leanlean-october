module

public import HypoellipticAleksandrov.Parabolic.Scaling
public import HypoellipticAleksandrov.Parabolic.LocalHarnackGeometry

/-!
# Endpoint continuity for the local parabolic Harnack box

This module transports closed-box scalar continuity through the normalized
parabolic affine map and records the resulting terminal-face limit.
-/

 public section

open Filter Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- Continuity within the normalized closed Harnack box gives the terminal-face
limit along the interior-time approximation. -/
theorem ContinuousOn.tendsto_localHarnackTerminalApprox
    {d : ℕ} {q : HypoellipticAleksandrov.Parabolic.ScalarField d} {v : PDE.Vec d}
    (hq : ContinuousOn q (parabolicClosedBox 2 2 0 0))
    (hv : v ∈ velocityCube (0 : PDE.Vec d) 1) :
    Tendsto (fun j  => q (localHarnackTerminalApprox j, v)) atTop
      (_root_.nhds (q (8, v))) := by


  have hzj  := HypoellipticAleksandrov.Parabolic.tendsto_localHarnackTerminalApprox.prodMk_nhds
      (tendsto_const_nhds (x := v))

  have hzjWithin  :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (fun j => (localHarnackTerminalApprox j, v)) hzj
      (Eventually.of_forall (by
          intro j
          have hj := localHarnackTerminalApprox_mem_normalizedOpenBox  j hv
          rw [mem_parabolicBox_iff] at hj
          rw [mem_parabolicClosedBox_iff]
          exact ⟨hj.1.le, hj.2.1.le, fun i => (hj.2.2 i).le⟩))

  exact (hq (8, v) (normalized_terminal_target_mem_normalizedClosedBox hv)).tendsto.comp hzjWithin

end

end HypoellipticAleksandrov.Parabolic
