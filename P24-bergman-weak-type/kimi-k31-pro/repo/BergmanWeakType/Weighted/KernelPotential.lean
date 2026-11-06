/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.KernelPDE
public import BergmanWeakType.Weighted.CompactIntegral
public import Mathlib.Topology.Order.Basic

/-! # Differential equations for positive kernel integrals

The source is allowed to be any compactly supported measure in the closed disk. This includes
both weighted area potentials and the circular boundary normalizer.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BergmanWeakType.Weighted

def powerKernelX (q a b x y : ℝ) : ℝ :=
  2 * q * ((a ^ 2 + b ^ 2) * x - a) * powerKernel (q - 1) a b x y

def powerKernelXX (q a b x y : ℝ) : ℝ :=
  2 * q * (a ^ 2 + b ^ 2) * powerKernel (q - 1) a b x y +
    4 * q * (q - 1) * ((a ^ 2 + b ^ 2) * x - a) ^ 2 * powerKernel (q - 2) a b x y

theorem powerKernelX_hasDerivAt (q a b x y : ℝ) (hd : 0 < denominator a b x y) :
    HasDerivAt (fun u ↦ powerKernelX q a b u y) (powerKernelXX q a b x y) x := by
  apply (powerKernel_hasDerivAt_deriv_x q a b x y hd).congr_of_eventuallyEq
  have hpos : ∀ᶠ u in nhds x, 0 < denominator a b u y :=
    (denominator_hasDerivAt_x a b x y).continuousAt.eventually (lt_mem_nhds hd)
  exact hpos.mono fun u hu ↦ (powerKernel_deriv_x q a b u y hu).symm

theorem exists_coordinate_interval {x y : ℝ} (hxy : x ^ 2 + y ^ 2 < 1) :
    ∃ S : Set ℝ, IsCompact S ∧ S ∈ nhds x ∧ ∀ u ∈ S, u ^ 2 + y ^ 2 < 1 := by
  have hn : {u : ℝ | u ^ 2 + y ^ 2 < 1} ∈ nhds x :=
    ((continuous_id.pow 2).add_const (y ^ 2)).continuousAt.eventually (gt_mem_nhds hxy)
  obtain ⟨l, r, _, hmem, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds hn
  exact ⟨Icc l r, isCompact_Icc, hmem, hsub⟩

end BergmanWeakType.Weighted
