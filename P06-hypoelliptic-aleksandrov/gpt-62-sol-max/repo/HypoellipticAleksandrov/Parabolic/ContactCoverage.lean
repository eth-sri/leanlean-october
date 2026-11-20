module

public import HypoellipticAleksandrov.Parabolic.ContactMap
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# First-contact coverage for the parabolic normal map

This module proves wedge coverage for the parabolic normal map by choosing
the least time in a compact nonnegative affine-comparison superlevel set.  No
global maximizer of the solution is assumed.  All velocity balls are the
project's explicit Euclidean balls.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Set
open scoped Topology

/-- Every wedge parameter is attained by the parabolic normal map at a genuine
first-contact point in the parabolic sign set. -/
theorem slopeInterceptWedge_subset_image_parabolicSignSet
    {d : ℕ} {T : ℝ} {y₀ : PDE.Vec d} {u : TimeVelocity d → ℝ}
    (hu : ContDiff ℝ 2 u) (hT : 0 < T)
    (hboundary : ∀ z ∈ forwardParabolicBoundary T y₀, u z ≤ 0)
    {zStar : TimeVelocity d}
    (hzStar : zStar ∈ closedParabolicCylinder T y₀)
    (hzPositive : 0 < u zStar) :
    slopeInterceptWedge d (u zStar) ⊆
      parabolicNormalMap u y₀ '' parabolicSignSet T y₀ u := by
  rintro ⟨h, p⟩ hpWedge
  rcases mem_slopeInterceptWedge_iff.mp hpWedge with ⟨hhLower, hhUpper, hp⟩
  let M : ℝ := u zStar
  have hM : 0 < M := hzPositive
  have hTnonneg : 0 ≤ T := hT.le
  let ell : PDE.Vec d → ℝ := affineVelocity y₀ h p
  let g : TimeVelocity d → ℝ := fun z => u z - ell z.2
  have hell (v : PDE.Vec d) (hv : v ∈ PDE.euclideanClosedBall y₀ 1) :
      0 < ell v ∧ ell v < M :=
    affineVelocity_bounds_of_wedge hM (R := 1) zero_lt_one hhLower hhUpper
      (by simpa using hp)
      ((PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).mp hv)
  have hellPos : ∀ v ∈ PDE.euclideanClosedBall y₀ 1, 0 < ell v := fun v hv => (hell v hv).1
  have hzStarClosed := (mem_closedParabolicCylinder_iff.mp hzStar).2.2
  have hgStar : 0 < g zStar := sub_pos.mpr (hell _ hzStarClosed).2
  have hgCont : Continuous g := by
    have hellDiff : ContDiff ℝ 2 (fun z : TimeVelocity d => ell z.2) := by
      unfold ell affineVelocity PDE.vecDot
      fun_prop
    exact hu.continuous.sub hellDiff.continuous
  let S : Set (TimeVelocity d) :=
    closedParabolicCylinder zStar.1 y₀ ∩ {z | 0 ≤ g z}
  have hzStarS : zStar ∈ S := by
    refine ⟨?_, hgStar.le⟩
    rw [mem_closedParabolicCylinder_iff]
    exact ⟨(mem_closedParabolicCylinder_iff.mp hzStar).1,
      le_rfl, hzStarClosed⟩
  have hSCompact : IsCompact S := by
    exact (isCompact_closedParabolicCylinder zStar.1 y₀).inter_right
      (isClosed_Ici.preimage hgCont)
  rcases hSCompact.exists_isMinOn ⟨zStar, hzStarS⟩ continuous_fst.continuousOn with
      ⟨zc, hzcS, hzcMin⟩
  have hzcClosed : zc ∈ closedParabolicCylinder zStar.1 y₀ := hzcS.1
  have hzcNonneg : 0 ≤ g zc := hzcS.2
  have hzcVelClosed : zc.2 ∈ PDE.euclideanClosedBall y₀ 1 :=
    (mem_closedParabolicCylinder_iff.mp hzcClosed).2.2
  have hgAtZero : g (0, zc.2) < 0 := by
    have hell : 0 < ell zc.2 := hellPos zc.2 hzcVelClosed
    have hbd : u (0, zc.2) ≤ 0 := hboundary (0, zc.2) (by
      rw [mem_forwardParabolicBoundary_iff]
      exact Or.inl ⟨rfl, hzcVelClosed⟩)
    change u (0, zc.2) - ell zc.2 < 0
    linarith
  have htcPos : 0 < zc.1 := by
    have htcNonneg : 0 ≤ zc.1 := (mem_closedParabolicCylinder_iff.mp hzcClosed).1
    by_contra hnot
    have hzero : zc.1 = 0 := le_antisymm (not_lt.mp hnot) htcNonneg
    have hzcEq : zc = (0, zc.2) := Prod.ext hzero rfl
    rw [hzcEq] at hzcNonneg
    linarith
  have hgcZero : g zc = 0 := by
    apply le_antisymm ?_ hzcNonneg
    by_contra hneg
    have hgcPos : 0 < g zc := lt_of_not_ge hneg
    let f : ℝ → ℝ := fun t => g (t, zc.2)
    have hfCont : Continuous f := hgCont.comp (continuous_id.prodMk continuous_const)
    rcases zero_between_of_continuousOn_of_neg_pos htcPos hfCont.continuousOn (by simpa [f] using hgAtZero)
      (by simpa [f] using hgcPos) with ⟨s, hs, hfs⟩
    have hsS : (s, zc.2) ∈ S := by
      refine ⟨?_, ?_⟩
      rw [mem_closedParabolicCylinder_iff]
      exact ⟨hs.1.le,
        hs.2.le.trans (mem_closedParabolicCylinder_iff.mp hzcClosed).2.1,
        hzcVelClosed⟩
      simpa [f] using hfs.ge
    have := hzcMin hsS
    change zc.1 ≤ s at this
    exact (not_lt_of_ge this) hs.2
  have htcLtStar : zc.1 < zStar.1 := by
    have hztPos : 0 < zStar.1 := by
      rcases mem_closedParabolicCylinder_iff.mp hzStar with ⟨ht0, htT, hv⟩
      by_contra hnot
      have htzero : zStar.1 = 0 := le_antisymm (not_lt.mp hnot) ht0
      have hbd : u zStar ≤ 0 := hboundary zStar (by
        rw [mem_forwardParabolicBoundary_iff]
        exact Or.inl ⟨htzero, hv⟩)
      linarith
    let f : ℝ → ℝ := fun t => g (t, zStar.2)
    have hfCont : Continuous f := hgCont.comp (continuous_id.prodMk continuous_const)
    have hfZeroNeg : f 0 < 0 := by
      have hell : 0 < ell zStar.2 := hellPos zStar.2 hzStarClosed
      have hbd : u (0, zStar.2) ≤ 0 := hboundary (0, zStar.2) (by
        rw [mem_forwardParabolicBoundary_iff]
        exact Or.inl ⟨rfl, hzStarClosed⟩)
      change u (0, zStar.2) - ell zStar.2 < 0
      linarith
    rcases zero_between_of_continuousOn_of_neg_pos hztPos hfCont.continuousOn hfZeroNeg
      (by simpa [f] using hgStar) with ⟨s, hs, hfs⟩
    have hsS : (s, zStar.2) ∈ S := by
      refine ⟨?_, ?_⟩
      rw [mem_closedParabolicCylinder_iff]
      exact ⟨hs.1.le, hs.2.le, hzStarClosed⟩
      simpa [f] using hfs.ge
    have hmin := hzcMin hsS
    change zc.1 ≤ s at hmin
    exact lt_of_le_of_lt hmin hs.2
  have hspatialNonpos : ∀ v ∈ PDE.euclideanClosedBall y₀ 1, g (zc.1, v) ≤ 0 := by
    intro v hv
    by_contra hnot
    have hpos : 0 < g (zc.1, v) := lt_of_not_ge hnot
    let f : ℝ → ℝ := fun t => g (t, v)
    have hfCont : Continuous f := hgCont.comp (continuous_id.prodMk continuous_const)
    have hfZeroNeg : f 0 < 0 := by
      have hell : 0 < ell v := hellPos v hv
      have hbd : u (0, v) ≤ 0 := hboundary (0, v) (by
        rw [mem_forwardParabolicBoundary_iff]
        exact Or.inl ⟨rfl, hv⟩)
      change u (0, v) - ell v < 0
      linarith
    rcases zero_between_of_continuousOn_of_neg_pos htcPos hfCont.continuousOn hfZeroNeg
      (by simpa [f] using hpos) with ⟨s, hs, hfs⟩
    have hsS : (s, v) ∈ S := by
      refine ⟨?_, ?_⟩
      rw [mem_closedParabolicCylinder_iff]
      exact ⟨hs.1.le,
        hs.2.le.trans (mem_closedParabolicCylinder_iff.mp hzcClosed).2.1, hv⟩
      simpa [f] using hfs.ge
    have hmin := hzcMin hsS
    change zc.1 ≤ s at hmin
    exact (not_lt_of_ge hmin) hs.2
  have hzcTimeUpperStar : zc.1 ≤ zStar.1 :=
    (mem_closedParabolicCylinder_iff.mp hzcClosed).2.1
  have hzStarTimeUpper : zStar.1 ≤ T :=
    (mem_closedParabolicCylinder_iff.mp hzStar).2.1
  have hzcTimeUpper : zc.1 ≤ T := by
    nlinarith [hzcTimeUpperStar, hzStarTimeUpper, hTnonneg]
  have hzcVelOpen : zc.2 ∈ PDE.euclideanBall y₀ 1 := by
    by_contra hnot
    have hsphere : zc.2 ∈ PDE.euclideanSphere y₀ 1 := by
      change PDE.euclideanSqDist zc.2 y₀ = 1 ^ 2
      change PDE.euclideanSqDist zc.2 y₀ ≤ 1 ^ 2 at hzcVelClosed
      exact le_antisymm hzcVelClosed (not_lt.mp (by simpa [PDE.euclideanBall] using hnot))
    have hbd : u zc ≤ 0 := hboundary zc (by
      rw [mem_forwardParabolicBoundary_iff]
      exact Or.inr ⟨htcPos.le, hzcTimeUpper, hsphere⟩)
    have hell : 0 < ell zc.2 := hellPos zc.2 hzcVelClosed
    change u zc - ell zc.2 = 0 at hgcZero
    linarith
  have hzcInterior : zc ∈ parabolicInterior T y₀ := by
    rw [mem_parabolicInterior_iff]
    exact ⟨htcPos, htcLtStar.trans_le hzStarTimeUpper,
      hzcVelOpen⟩
  have huzcPos : 0 < u zc := by
    have hell : 0 < ell zc.2 := hellPos zc.2 hzcVelClosed
    change u zc - ell zc.2 = 0 at hgcZero
    linarith
  have hspatialLocalMax : IsLocalMax
      (fun v : PDE.Vec d => u (zc.1, v) - ell v) zc.2 := by
    rw [IsLocalMax]
    have hopen : PDE.euclideanBall y₀ 1 ∈ 𝓝 zc.2 :=
      PDE.isOpen_euclideanBall y₀ 1 |>.mem_nhds hzcVelOpen
    filter_upwards [hopen] with v hv
    change g (zc.1, v) ≤ g zc
    rw [hgcZero]
    exact hspatialNonpos v (PDE.euclideanBall_subset_euclideanClosedBall y₀ 1 hv)
  have hhess : (-velocityHessian u zc).PosSemidef :=
    neg_velocityHessian_posSemidef_of_spatial_localMax_affineContact_of_contDiffAt hu.contDiffAt hspatialLocalMax
  have htimeMax : IsLocalMaxOn
      (fun t : ℝ => u (t, zc.2) - ell zc.2) (Set.Iic zc.1) zc.1 := by
    rw [IsLocalMaxOn]
    filter_upwards [(eventually_gt_nhds htcPos).filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with t ht htIic
    change g (t, zc.2) ≤ g zc
    rw [hgcZero]
    exact nonpos_at_or_before_firstContact hzcMin hgcZero htIic
      (mem_closedParabolicCylinder_iff.mpr ⟨ht.le, htIic.trans (mem_closedParabolicCylinder_iff.mp hzcClosed).2.1, hzcVelClosed⟩)
  have hdu := hu.differentiable (by norm_num) zc
  exact ⟨zc, ⟨hzcInterior, huzcPos, timeDerivative_nonneg_of_localMaxOn_past hdu htimeMax, hhess⟩,
    parabolicNormalMap_eq_of_affineContact hdu (sub_eq_zero.mp hgcZero) hspatialLocalMax⟩

end HypoellipticAleksandrov.Parabolic
