/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.RiemannMapping
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.MeanValue

public section

open Set Filter Metric Function
open scoped Topology

namespace BergmanWeakType

/-- A regular holomorphic change of coordinates between planar domains. -/
structure Chart (U V : Set ℂ) (φ : ℂ → ℂ) : Prop where
  src : IsOpen U
  dst : IsOpen V
  bij : BijOn φ U V
  reg : Complex.RegularOn φ U

namespace Chart
variable {U V : Set ℂ} {φ : ℂ → ℂ} (h : Chart U V φ)

include h

theorem inverse_deriv {z : ℂ} (hz : z ∈ U) :
    deriv (invFunOn φ U) (φ z) = (deriv φ z)⁻¹ :=
  ((h.reg.diff.analyticAt (h.src.mem_nhds hz)).hasStrictDerivAt.to_local_left_inverse (h.reg z hz)
    ((h.src.eventually_mem hz).mono fun _ hw ↦ h.bij.invOn_invFunOn.1 hw)).hasDerivAt.deriv

theorem symm : Chart V U (invFunOn φ U) := by
  refine ⟨h.dst, h.src, h.bij.symm h.bij.invOn_invFunOn.symm, fun w hw ↦ ?_⟩
  obtain ⟨z, hz, rfl⟩ := h.bij.surjOn hw
  rw [h.inverse_deriv hz]; exact inv_ne_zero (h.reg z hz)

end Chart

/-- Riemann disk coordinates for a bounded simply connected domain. -/
theorem exists_chart {U : Set ℂ} (hU : IsOpen U) (hc : IsSimplyConnected U) (hb : Bornology.IsBounded U) :
    ∃ φ, Chart disk U φ := by
  obtain ⟨z, hz⟩ := hc.nonempty
  obtain ⟨ψ, reg, bij⟩ := Complex.exists_regular_bijOn_disk hU hc hb hz
  exact ⟨_, (show Chart U disk ψ from ⟨hU, isOpen_ball, bij, reg⟩).symm⟩

end BergmanWeakType
