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


namespace HypoellipticAleksandrov.Parabolic

open Filter Set
open scoped Topology

private theorem zero_between_of_continuous_of_neg_pos
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hf : Continuous f)
    (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ c ∈ Set.Ioo a b, f c = 0 := by
  have hab' : a ≤ b := hab.le
  have hzero : (0) ∈ Set.Icc (f a) (f b) := ⟨hfa.le, hfb.le⟩
  rcases intermediate_value_Icc hab' hf.continuousOn hzero with ⟨c, hc, hfc⟩
  refine ⟨c, ?_, hfc⟩
  refine ⟨?_, ?_⟩
  · by_contra hca
    have hca' : c = a := le_antisymm (not_lt.mp hca) hc.1
    rw [hca'] at hfc
    linarith
  · by_contra hcb
    have hcb' : c = b := le_antisymm hc.2 (not_lt.mp hcb)
    rw [hcb'] at hfc
    linarith

variable {d : ℕ} {M h : ℝ} {y₀ p v : PDE.Vec d} {u : TimeVelocity d → ℝ}

private theorem affineVelocity_pos_on_closedBall
    
    (hM : 0 < M) (hh : M / 2 < h)
    (hp : p ∈ PDE.euclideanBall (0 : PDE.Vec d) (M / 4))
    (hv : v ∈ PDE.euclideanClosedBall y₀ 1) :
    0 < affineVelocity y₀ h p v := by
  have hpNorm : PDE.vecEuclideanNorm p < M / 4 := by
    simpa using
      (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (x₀ := (0))
        (x := p) (R := M / 4) (by linarith)).mp hp
  have hvNorm : PDE.vecEuclideanNorm (v - y₀) ≤ 1 := by
    simpa using
      (PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (x₀ := y₀) (x := v) (R := 1) (by norm_num)).mp hv
  have hprod : PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm (v - y₀) < M / 4 := by
    calc
      PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm _ ≤
          PDE.vecEuclideanNorm p * 1 :=
        mul_le_mul_of_nonneg_left hvNorm (PDE.vecEuclideanNorm_nonneg p)
      _ < M / 4 := by simpa using hpNorm
  have hdotAbs : |PDE.vecDot p _| < M / 4 :=
    (PDE.abs_vecDot_le_vecEuclideanNorm_mul p _).trans_lt hprod
  have hdot : -(M / 4) < PDE.vecDot p (v - y₀) := by
    nlinarith [neg_abs_le (PDE.vecDot p (v - y₀))]
  rw [affineVelocity_apply]
  linarith

private theorem affineVelocity_lt_of_wedge_at_closedBall
    
    (hM : 0 < M) (hh : h < 3 * M / 4)
    (hp : p ∈ PDE.euclideanBall (0 : PDE.Vec d) (M / 4))
    (hv : v ∈ PDE.euclideanClosedBall y₀ 1) :
    affineVelocity y₀ h p v < M := by
  have hpNorm : PDE.vecEuclideanNorm p < M / 4 := by
    simpa using
      (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (x₀ := (0))
        (x := p) (R := M / 4) (by linarith)).mp hp
  have hvNorm : PDE.vecEuclideanNorm (v - y₀) ≤ 1 := by
    simpa using
      (PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (x₀ := y₀) (x := v) (R := 1) (by norm_num)).mp hv
  have hprod : PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm (v - y₀) < M / 4 := by
    calc
      PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm _ ≤
          PDE.vecEuclideanNorm p * 1 :=
        mul_le_mul_of_nonneg_left hvNorm (PDE.vecEuclideanNorm_nonneg p)
      _ < M / 4 := by simpa using hpNorm
  have hdot : PDE.vecDot p _ < M / 4 :=
    lt_of_le_of_lt (le_abs_self _)
      ((PDE.abs_vecDot_le_vecEuclideanNorm_mul p _).trans_lt hprod)
  rw [affineVelocity_apply]
  linarith

private theorem affineVelocity_line_deriv
     (y₀ : PDE.Vec d) (h : ℝ) (p v : PDE.Vec d) (i : Fin d) :
    HasDerivAt
      (fun r : ℝ => affineVelocity y₀ h p
        (v + r • ((Pi.single i (1 : ℝ)) : PDE.Vec d)))
      (p i) 0 := by
  let e : PDE.Vec d := Pi.single i 1
  have hfun :
      (fun r : ℝ => affineVelocity y₀ h p (v + r • e)) =
        fun r => affineVelocity y₀ h p v + r * p i := by
    classical
    funext r
    have hsingle : (∑ x : Fin d,
        p x * r * e x) = r * p i := by
      dsimp [e]
      rw [Fintype.sum_eq_single i]
      · simp
        ring
      · intro x hxi
        simp [hxi]
    unfold affineVelocity PDE.vecDot
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have hsplit :
        h + (∑ x, p x * (v x + r * e x - y₀ x)) =
          h + (∑ x, p x * (v x - y₀ x)) +
            (∑ x, p x * r * e x) := by
      calc
        h + (∑ x, p x * (v x + r * e x - y₀ x)) =
            h + (∑ x, (p x * (v x - y₀ x) + p x * r * e x)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = h + (∑ x, p x * (v x - y₀ x)) + (∑ x, p x * r * e x) := by
          rw [Finset.sum_add_distrib]
          ring
    rw [hsplit, hsingle]
  rw [hfun]
  simpa only [one_mul] using
    ((hasDerivAt_id' (𝕜 := ℝ) 0).mul_const _).const_add
      _

private theorem time_slice_hasDerivAt
     (hu : ContDiff ℝ 2 u)
    (z : TimeVelocity d) :
    HasDerivAt (fun t : ℝ => u (t, z.2)) (timeDerivative u z) z.1 := by
  have huDiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hline : HasDerivAt (fun t : ℝ => (t, z.2)) ((1, 0)) z.1 := by
    exact
      ((hasDerivAt_id' (𝕜 := ℝ) z.1).prodMk
        (hasDerivAt_const (x := z.1) (c := z.2)))
  simpa only [timeDerivative, Function.comp_def] using
    (huDiff z).hasFDerivAt.comp_hasDerivAt z.1 hline

private theorem velocity_slice_hasDerivAt
     (hu : ContDiff ℝ 2 u)
    (z : TimeVelocity d) (i : Fin d) :
    HasDerivAt
      (fun r : ℝ => u (z.1,
        z.2 + r • ((Pi.single i (1 : ℝ)) : PDE.Vec d)))
      (velocityGradient u z i) 0 := by
  have huDiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hvline : HasDerivAt
      (fun r : ℝ => z.2 + r • ((Pi.single i (1)) : PDE.Vec d))
      (Pi.single i (1 : ℝ)) 0 := by
    simpa using
      ((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const
        _).const_add z.2
  have hline : HasDerivAt
      (fun r : ℝ => (z.1,
        z.2 + r • (Pi.single i (1 : ℝ))))
      (((0), (Pi.single i (1 : ℝ))) : TimeVelocity d) 0 := ((hasDerivAt_const (x := (0 : ℝ)) (c := z.1)).prodMk hvline)
  have huAt := (huDiff (z.1,
    z.2 + (0 : ℝ) • (Pi.single i (1 : ℝ)))).hasFDerivAt
  have hcomp := huAt.comp_hasDerivAt 0 hline
  simpa [velocityGradient, Function.comp_def] using hcomp

/-- Every wedge parameter is attained by the parabolic normal map at a genuine
first-contact point in the parabolic sign set. -/
theorem slopeInterceptWedge_subset_image_parabolicSignSet
     {T : ℝ} {y₀ : PDE.Vec d} {u : TimeVelocity d → ℝ}
    (hu : ContDiff ℝ 2 u) (hT : 0 < T)
    (hboundary : ∀ z ∈ forwardParabolicBoundary T y₀, u z ≤ 0)
    {zStar : TimeVelocity d}
    (hzStar : zStar ∈ closedParabolicCylinder T y₀)
    (hzPositive : 0 < u zStar) :
    slopeInterceptWedge d (u zStar) ⊆
      parabolicNormalMap u y₀ '' parabolicSignSet T y₀ u := by
  rintro ⟨h, p⟩ hpWedge
  rcases mem_slopeInterceptWedge_iff.mp hpWedge with ⟨hhLower, hhUpper, hp⟩
  let M  := u zStar
  have hM : 0 < M := hzPositive
  have hTnonneg : 0 ≤ T := hT.le
  have hhLower' : M / 2 < h := hhLower
  have hhUpper' : h < 3 * M / 4 := hhUpper
  have hp' : p ∈ PDE.euclideanBall _ (M / 4) := hp
  let ell  := affineVelocity y₀ h p
  let g  := fun z => u z - ell z.2
  have hellPos : ∀ v ∈ PDE.euclideanClosedBall y₀ 1, 0 < ell v := by
    intro v hv
    exact affineVelocity_pos_on_closedBall hM hhLower' hp' hv
  have hzStarClosed  :=
    (mem_closedParabolicCylinder_iff.mp hzStar).2.2
  have hgStar : 0 < g zStar := by
    have hellLt : ell zStar.2 < M :=
      affineVelocity_lt_of_wedge_at_closedBall hM hhUpper' hp' hzStarClosed
    change 0 < u zStar - ell zStar.2
    dsimp [M] at hellLt
    linarith
  have hgCont : Continuous g := by
    have hellDiff : ContDiff ℝ 2 (fun z : TimeVelocity d => ell z.2) := by
      unfold ell affineVelocity PDE.vecDot
      fun_prop
    exact hu.continuous.sub hellDiff.continuous
  let S  :=
    closedParabolicCylinder zStar.1 y₀ ∩ {z | 0 ≤ g z}
  have hzStarS : zStar ∈ S := by
    refine ⟨?_, hgStar.le⟩
    rw [mem_closedParabolicCylinder_iff]
    exact ⟨(mem_closedParabolicCylinder_iff.mp hzStar).1,
      le_rfl, hzStarClosed⟩
  have hSCompact : IsCompact S := (isCompact_closedParabolicCylinder zStar.1 y₀).inter_right
      (isClosed_Ici.preimage hgCont)
  rcases hSCompact.exists_isMinOn ⟨zStar, hzStarS⟩ continuous_fst.continuousOn with
      ⟨zc, hzcS, hzcMin⟩
  have hzcClosed  := hzcS.1
  have hzcNonneg : 0 ≤ g zc := hzcS.2
  have hzcVelClosed  :=
    (mem_closedParabolicCylinder_iff.mp hzcClosed).2.2
  have hgAtZero : g (0, zc.2) < 0 := by
    have hell  := hellPos zc.2 hzcVelClosed
    have hbd : u _ ≤ 0 := hboundary _ (by
      rw [mem_forwardParabolicBoundary_iff]
      exact Or.inl ⟨rfl, hzcVelClosed⟩)
    change u _ - ell zc.2 < 0
    linarith
  have htcPos : 0 < zc.1 := by
    have htcNonneg  := (mem_closedParabolicCylinder_iff.mp hzcClosed).1
    by_contra hnot
    have hzero  := le_antisymm (not_lt.mp hnot) htcNonneg
    have hzcEq : zc = (0, zc.2) := Prod.ext hzero rfl
    rw [hzcEq] at hzcNonneg
    linarith
  have hgcZero : g zc = 0 := by
    apply le_antisymm ?_ hzcNonneg
    by_contra hneg
    have hgcPos : 0 < g zc := lt_of_not_ge hneg
    let f  := fun t => g (t, zc.2)
    have hfCont : Continuous f := hgCont.comp (continuous_id.prodMk continuous_const)
    rcases zero_between_of_continuous_of_neg_pos htcPos hfCont (by simpa [f] using hgAtZero)
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
      have htzero  := le_antisymm (not_lt.mp hnot) ht0
      have hbd : u zStar ≤ 0 := hboundary zStar (by
        rw [mem_forwardParabolicBoundary_iff]
        exact Or.inl ⟨htzero, hv⟩)
      linarith
    let f  := fun t => g (t, zStar.2)
    have hfCont : Continuous f := hgCont.comp (continuous_id.prodMk continuous_const)
    have hfZeroNeg : f 0 < 0 := by
      have hell  := hellPos zStar.2 hzStarClosed
      have hbd : u _ ≤ 0 := hboundary _ (by
        rw [mem_forwardParabolicBoundary_iff]
        exact Or.inl ⟨rfl, hzStarClosed⟩)
      change u _ - ell zStar.2 < 0
      linarith
    rcases zero_between_of_continuous_of_neg_pos hztPos hfCont hfZeroNeg
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
    have hpos : 0 < g _ := lt_of_not_ge hnot
    let f  := fun t => g (t, v)
    have hfCont : Continuous f := hgCont.comp (continuous_id.prodMk continuous_const)
    have hfZeroNeg : f 0 < 0 := by
      have hell  := hellPos v hv
      have hbd : u _ ≤ 0 := hboundary _ (by
        rw [mem_forwardParabolicBoundary_iff]
        exact Or.inl ⟨rfl, hv⟩)
      change u _ - ell v < 0
      linarith
    rcases zero_between_of_continuous_of_neg_pos htcPos hfCont hfZeroNeg
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
  have hzcTimeUpperStar  :=
    (mem_closedParabolicCylinder_iff.mp hzcClosed).2.1
  have hzStarTimeUpper  :=
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
    have hell  := hellPos zc.2 hzcVelClosed
    change u zc - ell zc.2 = 0 at hgcZero
    linarith
  have hzcInterior : zc ∈ parabolicInterior T y₀ := by
    rw [mem_parabolicInterior_iff]
    exact ⟨htcPos, htcLtStar.trans_le hzStarTimeUpper,
      hzcVelOpen⟩
  have huzcPos : 0 < u zc := by
    have hell  := hellPos zc.2 hzcVelClosed
    change u zc - ell zc.2 = 0 at hgcZero
    linarith
  have hspatialLocalMax : IsLocalMax
      (fun v : PDE.Vec d => u (zc.1, v) - ell v) zc.2 := by
    rw [IsLocalMax]
    have hopen  :=
      PDE.isOpen_euclideanBall y₀ 1 |>.mem_nhds hzcVelOpen
    filter_upwards [hopen] with v hv
    change g _ ≤ g zc
    rw [hgcZero]
    exact hspatialNonpos v (PDE.euclideanBall_subset_euclideanClosedBall y₀ 1 hv)
  have hgrad : velocityGradient u zc = p := by
    ext i
    let q : PDE.Vec d := Pi.single i 1
    let line : ℝ → PDE.Vec d := fun r => zc.2 + r • q
    have hlineCont : ContinuousAt line 0 := (((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const q).const_add zc.2).continuousAt
    have hmaxLine : IsLocalMax
        (fun r : ℝ => u (zc.1, line r) - ell (line r)) 0 := by
      have hmaxAtLine : IsLocalMax
          (fun v : PDE.Vec d => u (zc.1, v) - ell v) (line 0) := by
        simpa [line, q] using hspatialLocalMax
      exact hmaxAtLine.comp_continuous hlineCont
    have huLine := velocity_slice_hasDerivAt hu zc i
    have hellLine := affineVelocity_line_deriv y₀ h p zc.2 i
    have hderiv : HasDerivAt
        (fun r : ℝ => u (zc.1,
          zc.2 + r • (Pi.single i (1 : ℝ))) -
          ell (zc.2 + r • (Pi.single i (1 : ℝ))))
        (velocityGradient u zc i - p i) 0 := huLine.sub hellLine
    have hzero := hmaxLine.hasDerivAt_eq_zero (by simpa [line, q] using hderiv)
    exact sub_eq_zero.mp (by simpa using hzero)
  have hcontact : IsLocalMax
      (fun v : PDE.Vec d => u (zc.1, v) -
        (u zc + PDE.vecDot p (v - zc.2))) zc.2 := by
    have hrewrite :
        (fun v : PDE.Vec d => u (zc.1, v) - ell v) =
          fun v : PDE.Vec d => u (zc.1, v) -
            (u zc + PDE.vecDot p (v - zc.2)) := by
      funext v
      change u _ - (h + PDE.vecDot p _) =
        u _ - (u zc + PDE.vecDot p _)
      have hgcZero' := hgcZero
      change u zc - (h + PDE.vecDot p _) = 0 at hgcZero'
      unfold PDE.vecDot at hgcZero' ⊢
      have hsum : (∑ x, p x * (v - y₀) x) =
          (∑ x, p x * (zc.2 - y₀) x) + ∑ x, p x * (v - zc.2) x := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Pi.sub_apply]
        ring
      rw [hsum]
      linarith
    rw [← hrewrite]
    exact hspatialLocalMax
  have hhess  :=
    neg_velocityHessian_posSemidef_of_spatial_localMax_affineContact hu hcontact
  have htimeMax : IsLocalMaxOn
      (fun t : ℝ => u (t, zc.2) - ell zc.2) (Set.Iic zc.1) zc.1 := by
    rw [IsLocalMaxOn]
    filter_upwards [(eventually_gt_nhds htcPos).filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with t ht htIic
    have htime : g (t, zc.2) ≤ 0 := by
      by_contra hnot
      have hpos : 0 < g _ := lt_of_not_ge hnot
      let f  := fun s => g (s, zc.2)
      have hfCont : Continuous f := hgCont.comp (continuous_id.prodMk continuous_const)
      have hfZeroNeg : f 0 < 0 := by simpa [f] using hgAtZero
      rcases zero_between_of_continuous_of_neg_pos ht hfCont hfZeroNeg
        (by simpa [f] using hpos) with ⟨s, hs, hfs⟩
      have hsS : (s, zc.2) ∈ S := by
        refine ⟨?_, ?_⟩
        rw [mem_closedParabolicCylinder_iff]
        exact ⟨hs.1.le,
          hs.2.le.trans (htIic.trans
            (mem_closedParabolicCylinder_iff.mp hzcClosed).2.1),
          hzcVelClosed⟩
        simpa [f] using hfs.ge
      have hmin := hzcMin hsS
      change zc.1 ≤ s at hmin
      exact (lt_irrefl zc.1) (hmin.trans_lt (hs.2.trans_le htIic))
    change u _ - ell zc.2 ≤ u zc - ell zc.2
    change g _ ≤ g zc
    rw [hgcZero]
    exact htime
  have htimeDeriv : HasDerivAt
      (fun t : ℝ => u _ - ell zc.2) _ zc.1 :=
    (time_slice_hasDerivAt hu zc).sub_const (ell zc.2)
  have hminusOne : (-1) ∈ posTangentConeAt (Set.Iic zc.1) zc.1 := by
    have hsegment : segment ℝ zc.1 (zc.1 - 1) ⊆ Set.Iic zc.1 := by
      intro s hs
      rw [segment_symm] at hs
      exact (segment_subset_Icc (sub_le_self _ (by norm_num)) hs).2
    simpa using sub_mem_posTangentConeAt_of_segment_subset hsegment
  have htimeNonneg : 0 ≤ timeDerivative u zc := by
    have hnonpos := htimeMax.hasFDerivWithinAt_nonpos htimeDeriv.hasDerivWithinAt hminusOne
    have hneg : -timeDerivative u zc ≤ 0 := by simpa using hnonpos
    linarith
  have hsign : zc ∈ parabolicSignSet T y₀ u := ⟨hzcInterior, huzcPos, htimeNonneg, hhess⟩
  refine ⟨zc, hsign, ?_⟩
  rw [parabolicNormalMap_apply]
  apply Prod.ext
  · change u zc - PDE.vecDot (velocityGradient u zc) (zc.2 - y₀) = h
    rw [hgrad]
    change u zc - ell zc.2 = 0 at hgcZero
    change u zc - (h + PDE.vecDot p (zc.2 - y₀)) = 0 at hgcZero
    linarith
  · exact hgrad

end HypoellipticAleksandrov.Parabolic
