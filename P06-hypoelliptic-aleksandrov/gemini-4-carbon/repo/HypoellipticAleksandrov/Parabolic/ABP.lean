module

public import HypoellipticAleksandrov.Parabolic.ContactMap
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.Parabolic.AreaFormula
public import PDEFoundation.Measure.LpPower
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Tactic.FieldSimp

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic
open Filter Set MeasureTheory
open scoped Topology ENNReal MatrixOrder


private theorem zero_between_of_continuous_of_neg_pos
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hf : Continuous f)
    (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ c ∈ Set.Ioo a b, f c = 0 := by
  have hab' := hab.le
  have hzero : 0 ∈ Set.Icc (f a) (f b) := by
    exact ⟨hfa.le, hfb.le⟩
  rcases intermediate_value_Icc hab' hf.continuousOn hzero with ⟨c, hc, hfc⟩
  refine ⟨c, ?_, hfc⟩
  refine ⟨?_, ?_⟩
  · by_contra hca
    have hca' := le_antisymm (not_lt.mp hca) hc.1
    rw [hca'] at hfc
    linarith
  · by_contra hcb
    have hcb' := le_antisymm hc.2 (not_lt.mp hcb)
    rw [hcb'] at hfc
    linarith

private theorem affineVelocity_pos_on_closedBall
    {d : ℕ} {M h : ℝ} {y₀ p v : PDE.Vec d}
    (hM : 0 < M) (hh : M / 2 < h)
    (hp : p ∈ PDE.euclideanBall (0 : PDE.Vec d) (M / 4))
    (hv : v ∈ PDE.euclideanClosedBall y₀ 1) :
    0 < affineVelocity y₀ h p v := by
  have hpNorm : PDE.vecEuclideanNorm p < M / 4 := by
    simpa using
      (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (x₀ := 0)
        (x := p) (R := M / 4) (by linarith)).mp hp
  have hvNorm : PDE.vecEuclideanNorm (v - y₀) ≤ 1 := by
    simpa using
      (PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (x₀ := y₀) (x := v) (R := 1) (by norm_num)).mp hv
  have hprod : PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm (v - y₀) < M / 4 := by
    calc
      PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm (v - y₀) ≤
          PDE.vecEuclideanNorm p * 1 :=
        mul_le_mul_of_nonneg_left hvNorm (PDE.vecEuclideanNorm_nonneg p)
      _ < M / 4 := by simpa using hpNorm
  have hdotAbs :=
    (PDE.abs_vecDot_le_vecEuclideanNorm_mul p (v - y₀)).trans_lt hprod
  have hdot : -(M / 4) < PDE.vecDot p (v - y₀) := by
    nlinarith [neg_abs_le (PDE.vecDot p (v - y₀))]
  rw [affineVelocity_apply]
  linarith

private theorem affineVelocity_lt_of_wedge_at_closedBall
    {d : ℕ} {M h : ℝ} {y₀ p v : PDE.Vec d}
    (hM : 0 < M) (hh : h < 3 * M / 4)
    (hp : p ∈ PDE.euclideanBall (0 : PDE.Vec d) (M / 4))
    (hv : v ∈ PDE.euclideanClosedBall y₀ 1) :
    affineVelocity y₀ h p v < M := by
  have hpNorm : PDE.vecEuclideanNorm p < M / 4 := by
    simpa using
      (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (x₀ := 0)
        (x := p) (R := M / 4) (by linarith)).mp hp
  have hvNorm : PDE.vecEuclideanNorm (v - y₀) ≤ 1 := by
    simpa using
      (PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (x₀ := y₀) (x := v) (R := 1) (by norm_num)).mp hv
  have hprod : PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm (v - y₀) < M / 4 := by
    calc
      PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm (v - y₀) ≤
          PDE.vecEuclideanNorm p * 1 :=
        mul_le_mul_of_nonneg_left hvNorm (PDE.vecEuclideanNorm_nonneg p)
      _ < M / 4 := by simpa using hpNorm
  have hdot :=
    lt_of_le_of_lt (le_abs_self _)
      ((PDE.abs_vecDot_le_vecEuclideanNorm_mul p (v - y₀)).trans_lt hprod)
  rw [affineVelocity_apply]
  linarith

private theorem affineVelocity_line_deriv
    {d : ℕ} (y₀ : PDE.Vec d) (h : ℝ) (p v : PDE.Vec d) (i : Fin d) :
    HasDerivAt
      (fun r : ℝ => affineVelocity y₀ h p
        (v + r • ((Pi.single i (1 : ℝ)) : PDE.Vec d)))
      (p i) 0 := by
  let e : PDE.Vec d := Pi.single i 1
  change HasDerivAt (fun r => affineVelocity y₀ h p (v + r • e)) (p i) 0
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
    simp
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
  simpa using
    ((hasDerivAt_id' (𝕜 := ℝ) 0).mul_const (p i)).const_add
      (affineVelocity y₀ h p v)

private theorem time_slice_hasDerivAt
    {d : ℕ} {u : TimeVelocity d → ℝ} (hu : ContDiff ℝ 2 u)
    (z : TimeVelocity d) :
    HasDerivAt (fun t : ℝ => u (t, z.2)) (timeDerivative u z) z.1 := by
  have hline : HasDerivAt (fun t : ℝ => (t, z.2)) ((1, 0) : TimeVelocity d) z.1 := by
    exact
      ((hasDerivAt_id' (𝕜 := ℝ) z.1).prodMk
        (hasDerivAt_const (x := z.1) (c := z.2)))
  simpa only [timeDerivative, Function.comp_def] using
    ((hu.differentiable (by norm_num)) z).hasFDerivAt.comp_hasDerivAt z.1 hline

private theorem velocity_slice_hasDerivAt
    {d : ℕ} {u : TimeVelocity d → ℝ} (hu : ContDiff ℝ 2 u)
    (z : TimeVelocity d) (i : Fin d) :
    HasDerivAt
      (fun r : ℝ => u (z.1,
        z.2 + r • ((Pi.single i (1 : ℝ)) : PDE.Vec d)))
      (velocityGradient u z i) 0 := by
  have hvline : HasDerivAt
      (fun r : ℝ => z.2 + r • ((Pi.single i 1) : PDE.Vec d))
      ((Pi.single i 1) : PDE.Vec d) 0 := by
    simpa using
      ((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const
        ((Pi.single i 1) : PDE.Vec d)).const_add z.2
  have hline : HasDerivAt
      (fun r : ℝ => (z.1,
        z.2 + r • ((Pi.single i 1) : PDE.Vec d)))
      ((0, ((Pi.single i 1) : PDE.Vec d)) : TimeVelocity d) 0 := by
    exact ((hasDerivAt_const (x := (0 : ℝ)) (c := z.1)).prodMk hvline)
  have huAt := ((hu.differentiable (by norm_num)) (z.1,
    z.2 + (0 : ℝ) • ((Pi.single i 1) : PDE.Vec d))).hasFDerivAt
  simpa [velocityGradient, Function.comp_def] using (huAt.comp_hasDerivAt 0 hline)

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
  have hM := hzPositive
  have hhLower' := hhLower
  have hhUpper' := hhUpper
  have hp' := hp
  let ell := affineVelocity y₀ h p
  let g : TimeVelocity d → ℝ := fun z => u z - ell z.2
  have hellPos : ∀ v ∈ PDE.euclideanClosedBall y₀ 1, 0 < ell v := by
    intro v hv
    exact affineVelocity_pos_on_closedBall hM hhLower' hp' hv
  have hzStarClosed :=
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
  let S :=
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
  have hzcClosed := hzcS.1
  have hzcNonneg : 0 ≤ g zc := hzcS.2
  have hzcVelClosed :=
    (mem_closedParabolicCylinder_iff.mp hzcClosed).2.2
  have hgAtZero : g (0, zc.2) < 0 := by
    have hell := hellPos zc.2 hzcVelClosed
    have hbd := hboundary (0, zc.2) (by
      rw [mem_forwardParabolicBoundary_iff]
      exact Or.inl ⟨rfl, hzcVelClosed⟩)
    change u (0, zc.2) - ell zc.2 < 0
    linarith
  have htcPos : 0 < zc.1 := by
    have htcNonneg := (mem_closedParabolicCylinder_iff.mp hzcClosed).1
    by_contra hnot
    have hzero := le_antisymm (not_lt.mp hnot) htcNonneg
    have hzcEq : zc = (0, zc.2) := Prod.ext hzero rfl
    rw [hzcEq] at hzcNonneg
    linarith
  have hgcZero : g zc = 0 := by
    apply le_antisymm ?_ hzcNonneg
    by_contra hneg
    have hgcPos := lt_of_not_ge hneg
    let f : ℝ → ℝ := fun t => g (t, zc.2)
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
      have htzero := le_antisymm (not_lt.mp hnot) ht0
      have hbd := hboundary zStar (by
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
  have hzcTimeUpperStar : zc.1 ≤ zStar.1 :=
    (mem_closedParabolicCylinder_iff.mp hzcClosed).2.1
  have hzStarTimeUpper : zStar.1 ≤ T :=
    (mem_closedParabolicCylinder_iff.mp hzStar).2.1
  have hzcTimeUpper : zc.1 ≤ T := by
    nlinarith [hzcTimeUpperStar, hzStarTimeUpper, hT.le]
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
  have hgrad : velocityGradient u zc = p := by
    ext i
    let q : PDE.Vec d := Pi.single i 1
    let line : ℝ → PDE.Vec d := fun r => zc.2 + r • q
    have hlineCont : ContinuousAt line 0 := by
      exact (((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const q).const_add zc.2).continuousAt
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
          zc.2 + r • ((Pi.single i 1) : PDE.Vec d)) -
          ell (zc.2 + r • ((Pi.single i 1) : PDE.Vec d)))
        (velocityGradient u zc i - p i) 0 := by
      exact huLine.sub hellLine
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
      change u (zc.1, v) - (h + PDE.vecDot p (v - y₀)) =
        u (zc.1, v) - (u zc + PDE.vecDot p (v - zc.2))
      have hgcZero' := hgcZero
      change u zc - (h + PDE.vecDot p (zc.2 - y₀)) = 0 at hgcZero'
      unfold PDE.vecDot at hgcZero' ⊢
      have hsum : (∑ x, p x * (v - y₀) x) =
          (∑ x, p x * (zc.2 - y₀) x) + ∑ x, p x * (v - zc.2) x := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        simp
        ring
      rw [hsum]
      linarith
    rw [← hrewrite]
    exact hspatialLocalMax
  have hhess : (-velocityHessian u zc).PosSemidef :=
    neg_velocityHessian_posSemidef_of_spatial_localMax_affineContact hu hcontact
  have htimeMax : IsLocalMaxOn
      (fun t : ℝ => u (t, zc.2) - ell zc.2) (Set.Iic zc.1) zc.1 := by
    rw [IsLocalMaxOn]
    filter_upwards [(eventually_gt_nhds htcPos).filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with t ht htIic
    have htime : g (t, zc.2) ≤ 0 := by
      by_contra hnot
      have hpos : 0 < g (t, zc.2) := lt_of_not_ge hnot
      let f : ℝ → ℝ := fun s => g (s, zc.2)
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
    change u (t, zc.2) - ell zc.2 ≤ u zc - ell zc.2
    change g (t, zc.2) ≤ g zc
    rw [hgcZero]
    exact htime
  have htimeDeriv : HasDerivAt
      (fun t : ℝ => u (t, zc.2) - ell zc.2) (timeDerivative u zc) zc.1 :=
    (time_slice_hasDerivAt hu zc).sub_const (ell zc.2)
  have hminusOne : (-1 : ℝ) ∈ posTangentConeAt (Set.Iic zc.1) zc.1 := by
    have hsegment : segment ℝ zc.1 (zc.1 - 1) ⊆ Set.Iic zc.1 := by
      intro s hs
      rw [segment_symm] at hs
      exact (segment_subset_Icc (sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)) hs).2
    simpa using sub_mem_posTangentConeAt_of_segment_subset hsegment
  have htimeNonneg : 0 ≤ timeDerivative u zc := by
    have hnonpos := htimeMax.hasFDerivWithinAt_nonpos htimeDeriv.hasDerivWithinAt hminusOne
    have hneg : -timeDerivative u zc ≤ 0 := by simpa using hnonpos
    linarith
  have hsign : zc ∈ parabolicSignSet T y₀ u := by
    exact ⟨hzcInterior, huzcPos, htimeNonneg, hhess⟩
  refine ⟨zc, hsign, ?_⟩
  rw [parabolicNormalMap_apply]
  apply Prod.ext
  · change u zc - PDE.vecDot (velocityGradient u zc) (zc.2 - y₀) = h
    rw [hgrad]
    change u zc - ell zc.2 = 0 at hgcZero
    change u zc - (h + PDE.vecDot p (zc.2 - y₀)) = 0 at hgcZero
    linarith
  · exact hgrad



private def weightedDensity {d : ℕ} (A : CoefficientField d)
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d) : ℝ :=
  (max (f z) 0) ^ (d + 1) / (coefficientAt A z).det

private theorem continuousOn_weightedDensity {d : ℕ} (A : CoefficientField d)
    (f : TimeVelocity d → ℝ) (hAcont : IsContinuousCoefficient A)
    (hfcont : Continuous f) {T : ℝ} {y₀ : PDE.Vec d}
    (hA : ∀ z ∈ closedParabolicCylinder T y₀, (coefficientAt A z).PosDef) :
    ContinuousOn (weightedDensity A f) (closedParabolicCylinder T y₀) := by
  unfold weightedDensity
  refine ((hfcont.max continuous_const).pow _).continuousOn.div
    hAcont.matrix_det.continuousOn ?_
  intro z hz
  exact (hA z hz).det_pos.ne'

private theorem weightedDensity_nonneg {d : ℕ} (A : CoefficientField d)
    (f : TimeVelocity d → ℝ) {T : ℝ} {y₀ : PDE.Vec d}
    (hA : ∀ z ∈ closedParabolicCylinder T y₀, (coefficientAt A z).PosDef)
    {z : TimeVelocity d} (hz : z ∈ closedParabolicCylinder T y₀) :
    0 ≤ weightedDensity A f z := by
  unfold weightedDensity
  exact div_nonneg (pow_nonneg (le_max_right _ _) _) (hA z hz).det_pos.le

private theorem integrableOn_weightedDensity {d : ℕ} (A : CoefficientField d)
    (f : TimeVelocity d → ℝ) (hAcont : IsContinuousCoefficient A)
    (hfcont : Continuous f) {T : ℝ} {y₀ : PDE.Vec d}
    (hA : ∀ z ∈ closedParabolicCylinder T y₀, (coefficientAt A z).PosDef) :
    IntegrableOn (weightedDensity A f) (closedParabolicCylinder T y₀) volume :=
  (continuousOn_weightedDensity A f hAcont hfcont hA).integrableOn_compact
    (isCompact_closedParabolicCylinder T y₀)

private theorem integrableOn_weightedDensity_interior {d : ℕ} (A : CoefficientField d)
    (f : TimeVelocity d → ℝ) (hAcont : IsContinuousCoefficient A)
    (hfcont : Continuous f) {T : ℝ} {y₀ : PDE.Vec d}
    (hA : ∀ z ∈ closedParabolicCylinder T y₀, (coefficientAt A z).PosDef) :
    IntegrableOn (weightedDensity A f) (parabolicInterior T y₀) volume :=
  (integrableOn_weightedDensity A f hAcont hfcont hA).mono_set
    (parabolicInterior_subset_closedParabolicCylinder T y₀)

/-- The exact real power-form smooth parabolic ABP estimate on the unit
velocity ball. -/
theorem parabolic_abp_unit_pow
    {d : ℕ} (hd : 0 < d)
    {T : ℝ} (hT : 0 < T) (hT_le_one : T ≤ 1)
    (y₀ : PDE.Vec d) (A : CoefficientField d)
    (f u : TimeVelocity d → ℝ)
    (hAcont : IsContinuousCoefficient A) (hfcont : Continuous f)
    (hu : ContDiff ℝ 2 u)
    (hA : ∀ z ∈ closedParabolicCylinder T y₀,
      (coefficientAt A z).PosDef)
    (hsub : IsParabolicSubsolutionOn A f u (parabolicInterior T y₀))
    (hboundary : ∀ z ∈ forwardParabolicBoundary T y₀, u z ≤ 0)
    {zStar : TimeVelocity d}
    (hzStar : zStar ∈ closedParabolicCylinder T y₀) :
    (volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal *
        (max (u zStar) 0) ^ (d + 1) ≤
      (4 / ((d : ℝ) + 1)) ^ (d + 1) *
        ∫ z in parabolicInterior T y₀,
          (max (f z) 0) ^ (d + 1) /
            (coefficientAt A z).det ∂volume := by
  let M : ℝ := max (u zStar) 0
  let density : TimeVelocity d → ℝ := weightedDensity A f
  have hT_unit : T ∈ Set.Ioc 0 1 := ⟨hT, hT_le_one⟩
  have hd_one : 1 ≤ d := by
    exact_mod_cast (Nat.succ_le_iff.mpr hd)
  have hExponent_pos : 0 < (d : ℝ) + 1 := by linarith
  have hM_nonneg : 0 ≤ M := le_max_right _ _
  have hDensity_integrable : IntegrableOn density (parabolicInterior T y₀) volume := by
    exact integrableOn_weightedDensity_interior A f hAcont hfcont hA
  have hDensity_nonneg : ∀ z ∈ parabolicInterior T y₀, 0 ≤ density z := by
    intro z hz
    exact weightedDensity_nonneg A f hA
      (parabolicInterior_subset_closedParabolicCylinder T y₀ hz)
  have hDensity_lintegral_ne_top :
      (∫⁻ z in parabolicInterior T y₀, ENNReal.ofReal (density z) ∂volume) ≠ ∞ := by
    have hfinite := (MeasureTheory.hasFiniteIntegral_iff_norm _).mp
      hDensity_integrable.integrable.hasFiniteIntegral
    apply ne_of_lt
    refine (lintegral_congr_ae ?_).symm ▸ hfinite
    filter_upwards [ae_restrict_mem (measurableSet_parabolicInterior T y₀)] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (hDensity_nonneg z hz)]
  have hDensity_integral_eq :
      (∫ z in parabolicInterior T y₀, density z ∂volume) =
        (∫⁻ z in parabolicInterior T y₀, ENNReal.ofReal (density z) ∂volume).toReal := by
    refine integral_eq_lintegral_of_nonneg_ae ?_
      hDensity_integrable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_parabolicInterior T y₀)] with z hz
    exact hDensity_nonneg z hz
  by_cases hM_zero : M = 0
  · rw [show max (u zStar) 0 = M by rfl, hM_zero]
    simp
    have hright_nonneg : 0 ≤ ∫ z in parabolicInterior T y₀, density z ∂volume := by
      rw [hDensity_integral_eq]
      exact ENNReal.toReal_nonneg
    exact mul_nonneg (pow_nonneg (by positivity) _) hright_nonneg
  have hM_pos : 0 < M := lt_of_le_of_ne hM_nonneg (Ne.symm hM_zero)
  have hzPositive : 0 < u zStar := by
    by_contra hnot
    have hu_nonpos : u zStar ≤ 0 := le_of_not_gt hnot
    have : M = 0 := by dsimp [M]; exact max_eq_right hu_nonpos
    exact hM_zero this
  have hcoverage := slopeInterceptWedge_subset_image_parabolicSignSet hu hT_unit.1 hboundary
    hzStar hzPositive
  have hmeasure_coverage :
      volume (slopeInterceptWedge d (u zStar)) ≤
        volume (parabolicNormalMap u y₀ '' parabolicSignSet T y₀ u) :=
    measure_mono hcoverage
  have harea := volume_parabolicNormalMap_image_le_lintegral_abs_det_fderiv hu T y₀
  have hpointwise : ∀ z ∈ parabolicSignSet T y₀ u,
      ENNReal.ofReal |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| ≤
        ENNReal.ofReal (density z) /
          ENNReal.ofReal (((d : ℝ) + 1) ^ (d + 1)) := by
    intro z hz
    have hsource := abs_det_fderiv_parabolicNormalMap_le_source hu hz
      (hA z (parabolicInterior_subset_closedParabolicCylinder T y₀ hz.1))
      (hsub z hz.1)
    have hden_pos : 0 < ((d : ℝ) + 1) ^ (d + 1) := pow_pos hExponent_pos _
    rw [← ENNReal.ofReal_div_of_pos hden_pos]
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [density, weightedDensity, div_div, mul_comm] using hsource)
  have hDensity_aeMeasurable :
      AEMeasurable (fun z => ENNReal.ofReal (density z))
        (volume.restrict (parabolicInterior T y₀)) := by
    apply AEMeasurable.ennreal_ofReal
    apply ContinuousOn.aemeasurable
      ((continuousOn_weightedDensity A f hAcont hfcont hA).mono
        (parabolicInterior_subset_closedParabolicCylinder T y₀))
    exact measurableSet_parabolicInterior T y₀
  have hsign_bound :
      (∫⁻ z in parabolicSignSet T y₀ u,
          ENNReal.ofReal |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| ∂volume) ≤
        (∫⁻ z in parabolicSignSet T y₀ u,
          ENNReal.ofReal (density z) /
            ENNReal.ofReal (((d : ℝ) + 1) ^ (d + 1)) ∂volume) := by
    apply setLIntegral_mono_ae
    · apply AEMeasurable.div_const
      apply AEMeasurable.ennreal_ofReal
      apply ContinuousOn.aemeasurable
        ((continuousOn_weightedDensity A f hAcont hfcont hA).mono
          (fun z hz => parabolicInterior_subset_closedParabolicCylinder T y₀ hz.1))
      exact measurableSet_parabolicSignSet hu T y₀
    · exact ae_of_all _ fun z hz => hpointwise z hz
  let q : ℝ := ((d : ℝ) + 1) ^ (d + 1)
  let qE : ℝ≥0∞ := ENNReal.ofReal q
  have hq_pos : 0 < q := pow_pos hExponent_pos _
  have hqE_ne_top : qE ≠ ∞ := ENNReal.ofReal_ne_top
  have hsign_to_interior :
      (∫⁻ z in parabolicSignSet T y₀ u,
          ENNReal.ofReal (density z) / qE ∂volume) ≤
        (∫⁻ z in parabolicInterior T y₀,
          ENNReal.ofReal (density z) / qE ∂volume) :=
    lintegral_mono_set (fun z hz => hz.1)
  have hinterior_factor :
      (∫⁻ z in parabolicInterior T y₀,
          ENNReal.ofReal (density z) / qE ∂volume) =
        (∫⁻ z in parabolicInterior T y₀, ENNReal.ofReal (density z) ∂volume) / qE := by
    simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const'' qE⁻¹ hDensity_aeMeasurable]
  have hwedge_enn :
      volume (slopeInterceptWedge d (u zStar)) ≤
        (∫⁻ z in parabolicInterior T y₀, ENNReal.ofReal (density z) ∂volume) / qE := by
    calc
      volume (slopeInterceptWedge d (u zStar)) ≤
          volume (parabolicNormalMap u y₀ '' parabolicSignSet T y₀ u) := hmeasure_coverage
      _ ≤ ∫⁻ z in parabolicSignSet T y₀ u,
          ENNReal.ofReal |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| ∂volume := harea
      _ ≤ ∫⁻ z in parabolicSignSet T y₀ u,
          ENNReal.ofReal (density z) / qE ∂volume := hsign_bound
      _ ≤ ∫⁻ z in parabolicInterior T y₀,
          ENNReal.ofReal (density z) / qE ∂volume := hsign_to_interior
      _ = _ := hinterior_factor
  have hrhs_ne_top :
      (∫⁻ z in parabolicInterior T y₀, ENNReal.ofReal (density z) ∂volume) / qE ≠ ∞ := by
    apply ENNReal.div_ne_top hDensity_lintegral_ne_top
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hq_pos)
  have hwedge_real := ENNReal.toReal_mono hrhs_ne_top hwedge_enn
  have hM_eq : M = u zStar := by
    dsimp [M]
    exact max_eq_left hzPositive.le
  have hwedge_volume := volume_slopeInterceptWedge_eq (d := d) hzPositive
  rw [hwedge_volume, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (pow_nonneg (div_nonneg hzPositive.le (by norm_num)) _),
    ENNReal.toReal_ofReal hq_pos.le] at hwedge_real
  rw [← hDensity_integral_eq] at hwedge_real
  change (volume (PDE.euclideanBall 0 1)).toReal * M ^ (d + 1) ≤ _
  rw [hM_eq]
  change (volume (PDE.euclideanBall 0 1)).toReal * (u zStar) ^ (d + 1) ≤
    (4 / ((d : ℝ) + 1)) ^ (d + 1) *
      ∫ z in parabolicInterior T y₀, density z ∂volume
  have hconstant_nonneg : 0 ≤ (4 / ((d : ℝ) + 1)) ^ (d + 1) := by positivity
  have hscaled : (u zStar / 4) ^ (d + 1) *
      (volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal * q ≤
        ∫ z in parabolicInterior T y₀, density z ∂volume := by
    apply (le_div_iff₀ hq_pos).mp
    exact hwedge_real
  calc
    (volume (PDE.euclideanBall 0 1)).toReal * (u zStar) ^ (d + 1) =
        (4 / ((d : ℝ) + 1)) ^ (d + 1) *
          ((u zStar / 4) ^ (d + 1) *
            (volume (PDE.euclideanBall 0 1)).toReal * q) := by
      dsimp [q]
      rw [div_pow, div_pow]
      field_simp [hExponent_pos.ne']
    _ ≤ (4 / ((d : ℝ) + 1)) ^ (d + 1) *
        ∫ z in parabolicInterior T y₀, density z ∂volume :=
      mul_le_mul_of_nonneg_left hscaled hconstant_nonneg

/-- Raising the quotient-form ABP root bound to a positive natural power. -/
private theorem abp_root_constant_mul_rpow_pow {n : ℕ} (hn : n ≠ 0)
    {a omega B : ℝ} (homega : 0 < omega) (hB : 0 ≤ B) :
    omega *
        ((a / omega ^ ((n : ℝ)⁻¹)) * B ^ ((n : ℝ)⁻¹)) ^ n =
      a ^ n * B := by
  have homega_root : (omega ^ ((n : ℝ)⁻¹)) ^ n = omega :=
    Real.rpow_inv_natCast_pow homega.le hn
  have hB_root : (B ^ ((n : ℝ)⁻¹)) ^ n = B :=
    Real.rpow_inv_natCast_pow hB hn
  calc
    omega * ((a / omega ^ ((n : ℝ)⁻¹)) * B ^ ((n : ℝ)⁻¹)) ^ n =
        omega * ((a / omega ^ ((n : ℝ)⁻¹)) ^ n *
          (B ^ ((n : ℝ)⁻¹)) ^ n) := by
      rw [mul_pow]
    _ = omega * ((a ^ n / (omega ^ ((n : ℝ)⁻¹)) ^ n) *
          (B ^ ((n : ℝ)⁻¹)) ^ n) := by
      rw [div_pow]
    _ = omega * ((a ^ n / omega) * B) := by
      rw [homega_root, hB_root]
    _ = a ^ n * B := by
      field_simp [homega.ne']


private theorem lower_loewner_posDef_on {d : ℕ} {lam : ℝ} {T : ℝ}
    {y₀ : PDE.Vec d} {A : CoefficientField d} (hlam : 0 < lam)
    (hlo : ∀ z ∈ closedParabolicCylinder T y₀,
      lam • (1 : PDE.Mat d) ≤ coefficientAt A z) :
    ∀ z ∈ closedParabolicCylinder T y₀, (coefficientAt A z).PosDef := by
  intro z hz
  exact posDef_of_loewner_lower hlam (hlo z hz)

private theorem lower_loewner_det_on {d : ℕ} {lam : ℝ} {T : ℝ}
    {y₀ : PDE.Vec d} {A : CoefficientField d} (hlam : 0 < lam)
    (hlo : ∀ z ∈ closedParabolicCylinder T y₀,
      lam • (1 : PDE.Mat d) ≤ coefficientAt A z) :
    ∀ z ∈ closedParabolicCylinder T y₀, lam ^ d ≤ (coefficientAt A z).det := by
  intro z hz
  exact det_lower_of_loewner hlam (hlo z hz)



private theorem source_memLp_on_parabolicInterior {d : ℕ} {T : ℝ}
    {y₀ : PDE.Vec d} {f : TimeVelocity d → ℝ} (hf : Continuous f) :
    MemLp (fun z => max (f z) 0) (parabolicExponent d)
      (volume.restrict (parabolicInterior T y₀)) := by
  have hmeasure : volume (parabolicInterior T y₀ : Set (TimeVelocity d)) < ∞ :=
    (measure_mono (parabolicInterior_subset_closedParabolicCylinder T y₀)).trans_lt
      (isCompact_closedParabolicCylinder T y₀).measure_lt_top
  letI : Fact (volume (parabolicInterior T y₀ : Set (TimeVelocity d)) < ∞) :=
    ⟨hmeasure⟩
  let g : TimeVelocity d → ℝ := fun z => max (f z) 0
  have hg : Continuous g := hf.max continuous_const
  obtain ⟨C, hC⟩ :=
    (isCompact_closedParabolicCylinder T y₀).exists_bound_of_continuousOn hg.continuousOn
  refine MemLp.of_bound hg.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' (measurableSet_parabolicInterior T y₀)]
  exact Eventually.of_forall fun z hz =>
    hC z (parabolicInterior_subset_closedParabolicCylinder T y₀ hz)


private theorem source_integrableOn {d : ℕ} {lam : ℝ} {T : ℝ}
    {y₀ : PDE.Vec d} {f : TimeVelocity d → ℝ} (hlam : 0 < lam)
    (hf : Continuous f) :
    IntegrableOn (fun z => (max (f z) 0) ^ (d + 1) / lam ^ d)
      (parabolicInterior T y₀) volume := by
  have hcont : Continuous (fun z => (max (f z) 0) ^ (d + 1) / lam ^ d) :=
    ((hf.max continuous_const).pow _).div continuous_const
      (fun _ => (pow_pos hlam d).ne')
  exact (hcont.continuousOn.integrableOn_compact
    (isCompact_closedParabolicCylinder T y₀)).mono_set
      (parabolicInterior_subset_closedParabolicCylinder T y₀)


private theorem weighted_integral_le_of_lower {d : ℕ} {lam : ℝ} {T : ℝ}
    {y₀ : PDE.Vec d} {A : CoefficientField d} {f : TimeVelocity d → ℝ}
    (hlam : 0 < lam)
    (hlo : ∀ z ∈ closedParabolicCylinder T y₀,
      lam • (1 : PDE.Mat d) ≤ coefficientAt A z)
    (hweighted : IntegrableOn (fun z =>
      (max (f z) 0) ^ (d + 1) / (coefficientAt A z).det)
      (parabolicInterior T y₀) volume)
    (hsource : IntegrableOn (fun z => (max (f z) 0) ^ (d + 1) / lam ^ d)
      (parabolicInterior T y₀) volume) :
    (∫ z in parabolicInterior T y₀,
      (max (f z) 0) ^ (d + 1) / (coefficientAt A z).det ∂volume) ≤
      ∫ z in parabolicInterior T y₀,
        (max (f z) 0) ^ (d + 1) / lam ^ d ∂volume := by
  refine setIntegral_mono_on hweighted hsource
    (measurableSet_parabolicInterior T y₀) fun z hz => ?_
  refine div_le_div_of_nonneg_left (pow_nonneg (le_max_right _ _) _)
    (pow_pos hlam d) ?_
  exact lower_loewner_det_on hlam hlo z
    (parabolicInterior_subset_closedParabolicCylinder T y₀ hz)

private theorem scalar_root_bound {d : ℕ} {lam C W I : ℝ}
    (hC : 0 ≤ C) (hlam : 0 < lam) (hW : 0 ≤ W)
    (hWI : W ≤ I / lam ^ d) (hI : 0 ≤ I) :
    C * W ^ (1 / ((d : ℝ) + 1) : ℝ) ≤
      (C / (lam ^ d) ^ (1 / ((d : ℝ) + 1) : ℝ)) *
        I ^ (1 / ((d : ℝ) + 1) : ℝ) := by
  have hq : 0 ≤ (1 / ((d : ℝ) + 1) : ℝ) := by positivity
  have hlamPow : 0 ≤ lam ^ d := (pow_pos hlam d).le
  have hpow : W ^ (1 / ((d : ℝ) + 1) : ℝ) ≤
      (I / lam ^ d) ^ (1 / ((d : ℝ) + 1) : ℝ) :=
    Real.rpow_le_rpow hW hWI hq
  calc
    C * W ^ (1 / ((d : ℝ) + 1) : ℝ) ≤
        C * (I / lam ^ d) ^ (1 / ((d : ℝ) + 1) : ℝ) :=
      mul_le_mul_of_nonneg_left hpow hC
    _ = C * (I ^ (1 / ((d : ℝ) + 1) : ℝ) /
        (lam ^ d) ^ (1 / ((d : ℝ) + 1) : ℝ)) := by
      rw [Real.div_rpow hI hlamPow]
    _ = (C / (lam ^ d) ^ (1 / ((d : ℝ) + 1) : ℝ)) *
        I ^ (1 / ((d : ℝ) + 1) : ℝ) := by ring

/-- The smooth parabolic ABP estimate under lower Loewner ellipticity, with
the exact restricted `L^(d + 1)` norm. -/
theorem parabolic_abp_unit_of_lower_ellipticity
    (d : ℕ) (hd : 0 < d) (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T : ℝ}, 0 < T → T ≤ 1 →
      ∀ (y₀ : PDE.Vec d) (A : CoefficientField d)
        (f u : TimeVelocity d → ℝ),
        IsContinuousCoefficient A → Continuous f → ContDiff ℝ 2 u →
        (∀ z ∈ closedParabolicCylinder T y₀,
          lam • (1 : PDE.Mat d) ≤ coefficientAt A z) →
        IsParabolicSubsolutionOn A f u (parabolicInterior T y₀) →
        (∀ z ∈ forwardParabolicBoundary T y₀, u z ≤ 0) →
        ∀ zStar ∈ closedParabolicCylinder T y₀,
          u zStar ≤ C *
            parabolicLpNormOn d (fun z => max (f z) 0)
              (parabolicInterior T y₀)    := by
  have weighted_integrableOn {T : ℝ} {y₀ : PDE.Vec d} {A : CoefficientField d} {f : TimeVelocity d → ℝ} (hAcont : IsContinuousCoefficient A) (hf : Continuous f) (hA : ∀ z ∈ closedParabolicCylinder T y₀, (coefficientAt A z).PosDef) :
      IntegrableOn (fun z =>
      (max (f z) 0) ^ (d + 1) / (coefficientAt A z).det)
      (parabolicInterior T y₀) volume := by
    have hcont : ContinuousOn (fun z =>
        (max (f z) 0) ^ (d + 1) / (coefficientAt A z).det)
        (closedParabolicCylinder T y₀) := by
      refine (((hf.max continuous_const).pow _).continuousOn.div
        hAcont.matrix_det.continuousOn ?_)
      intro z hz
      exact (hA z hz).det_pos.ne'
    exact (hcont.integrableOn_compact (isCompact_closedParabolicCylinder T y₀)).mono_set
      (parabolicInterior_subset_closedParabolicCylinder T y₀)
  have parabolicLpNormOn_eq_integral_pow {d : ℕ} {T : ℝ} {y₀ : PDE.Vec d} {f : TimeVelocity d → ℝ} (hf : MemLp (fun z => max (f z) 0) (parabolicExponent d)
      (volume.restrict (parabolicInterior T y₀))) :
      parabolicLpNormOn d (fun z => max (f z) 0) (parabolicInterior T y₀) =
      (∫ z in parabolicInterior T y₀,
        (max (f z) 0) ^ (d + 1) ∂volume) ^
          (1 / ((d : ℝ) + 1) : ℝ) := by
    have norm_positive_part (x : ℝ) :
        ‖max x 0‖ = max x 0 := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact le_max_of_le_right le_rfl
    have parabolicExponent_eq_ofReal (d : ℕ) :
        parabolicExponent d = ENNReal.ofReal ((d : ℝ) + 1) := by
      rw [show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by norm_num]
      simpa only [parabolicExponent, Nat.cast_add, Nat.cast_one] using
        (ENNReal.ofReal_natCast (d + 1)).symm
    have hp : 0 < (d : ℝ) + 1 := by positivity
    have hf' : MemLp (fun z => max (f z) 0)
        (ENNReal.ofReal ((d : ℝ) + 1))
        (volume.restrict (parabolicInterior T y₀)) := by
      rw [← parabolicExponent_eq_ofReal]
      exact hf
    rw [parabolicLpNormOn, parabolicELpNormOn, parabolicExponent_eq_ofReal]
    calc
      (eLpNorm (fun z => max (f z) 0) (ENNReal.ofReal ((d : ℝ) + 1)
        ) (volume.restrict (parabolicInterior T y₀))).toReal =
          (∫ z in parabolicInterior T y₀,
            ‖max (f z) 0‖ ^ ((d : ℝ) + 1) ∂volume) ^
              (1 / ((d : ℝ) + 1) : ℝ) :=
        PDE.toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv hp hf'
      _ = (∫ z in parabolicInterior T y₀,
            (max (f z) 0) ^ (d + 1) ∂volume) ^
              (1 / ((d : ℝ) + 1) : ℝ) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with z
        rw [norm_positive_part,
          show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
  have parabolic_abp_unit :
      ∃ C : ℝ, 0 < C ∧
      ∀ {T : ℝ}, 0 < T → T ≤ 1 →
      ∀ (y₀ : PDE.Vec d) (A : CoefficientField d)
        (f u : TimeVelocity d → ℝ),
        IsContinuousCoefficient A → Continuous f → ContDiff ℝ 2 u →
        (∀ z ∈ closedParabolicCylinder T y₀,
          (coefficientAt A z).PosDef) →
        IsParabolicSubsolutionOn A f u (parabolicInterior T y₀) →
        (∀ z ∈ forwardParabolicBoundary T y₀, u z ≤ 0) →
        ∀ zStar ∈ closedParabolicCylinder T y₀,
          u zStar ≤ C *
            (∫ z in parabolicInterior T y₀,
              (max (f z) 0) ^ (d + 1) /
                (coefficientAt A z).det ∂volume) ^
              (1 / ((d : ℝ) + 1) : ℝ) := by
    let omega : ℝ :=
      (volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal
    have homega : 0 < omega := by
      dsimp [omega]
      exact PDE.volume_euclideanBall_toReal_pos 0 (by norm_num)
    have hdimension : 0 < (d : ℝ) + 1 := by positivity
    have hrecip :
        1 / ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ)⁻¹ := by
      norm_num [Nat.cast_add, one_div]
    refine ⟨(4 / ((d : ℝ) + 1)) /
        omega ^ (1 / ((d : ℝ) + 1) : ℝ), ?_, ?_⟩
    · exact div_pos (div_pos (by norm_num) hdimension)
        (Real.rpow_pos_of_pos homega _)
    · intro T hT hT_le_one y₀ A f u hAcont hfcont hu hA hsub hboundary zStar hzStar
      let B : ℝ := ∫ z in parabolicInterior T y₀,
        (max (f z) 0) ^ (d + 1) / (coefficientAt A z).det ∂volume
      have hB : 0 ≤ B := by
        dsimp [B]
        apply integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem (measurableSet_parabolicInterior T y₀)] with z hz
        exact div_nonneg (pow_nonneg (le_max_right _ _) _)
          (hA z (parabolicInterior_subset_closedParabolicCylinder T y₀ hz)).det_pos.le
      have hpower :
          omega * (max (u zStar) 0) ^ (d + 1) ≤
            (4 / ((d : ℝ) + 1)) ^ (d + 1) * B := by
        simpa using
          parabolic_abp_unit_pow hd hT hT_le_one y₀ A f u hAcont hfcont hu hA hsub
            hboundary hzStar
      have hroot_power :
          (max (u zStar) 0) ^ (d + 1) ≤
            (((4 / ((d : ℝ) + 1)) /
                omega ^ (1 / ((d : ℝ) + 1) : ℝ)) *
              B ^ (1 / ((d : ℝ) + 1) : ℝ)) ^ (d + 1) := by
        apply le_of_mul_le_mul_left ?_ homega
        calc
          omega * (max (u zStar) 0) ^ (d + 1) ≤
              (4 / ((d : ℝ) + 1)) ^ (d + 1) * B := hpower
          _ = omega *
              (((4 / ((d : ℝ) + 1)) /
                  omega ^ (1 / ((d : ℝ) + 1) : ℝ)) *
                B ^ (1 / ((d : ℝ) + 1) : ℝ)) ^ (d + 1) := by
            rw [hrecip]
            symm
            exact abp_root_constant_mul_rpow_pow (Nat.succ_ne_zero d) homega hB
      have hroot_nonneg :
          0 ≤ ((4 / ((d : ℝ) + 1)) /
                omega ^ (1 / ((d : ℝ) + 1) : ℝ)) *
              B ^ (1 / ((d : ℝ) + 1) : ℝ) :=
        mul_nonneg
          (le_of_lt (div_pos (div_pos (by norm_num) hdimension)
            (Real.rpow_pos_of_pos homega _)))
          (Real.rpow_nonneg hB _)
      have hroot :
          max (u zStar) 0 ≤
            ((4 / ((d : ℝ) + 1)) /
                omega ^ (1 / ((d : ℝ) + 1) : ℝ)) *
              B ^ (1 / ((d : ℝ) + 1) : ℝ) :=
        le_of_pow_le_pow_left₀ (Nat.succ_ne_zero d) hroot_nonneg hroot_power
      calc
        u zStar ≤ max (u zStar) 0 := le_max_left _ _
        _ ≤ ((4 / ((d : ℝ) + 1)) /
                omega ^ (1 / ((d : ℝ) + 1) : ℝ)) *
              B ^ (1 / ((d : ℝ) + 1) : ℝ) := hroot
        _ = ((4 / ((d : ℝ) + 1)) /
                omega ^ (1 / ((d : ℝ) + 1) : ℝ)) *
              (∫ z in parabolicInterior T y₀,
                (max (f z) 0) ^ (d + 1) /
                  (coefficientAt A z).det ∂volume) ^
                (1 / ((d : ℝ) + 1) : ℝ) := rfl
  obtain ⟨C_d, hC_d, hABP⟩ := parabolic_abp_unit
  refine ⟨C_d / (lam ^ d) ^ (1 / ((d : ℝ) + 1) : ℝ),
    div_pos hC_d (Real.rpow_pos_of_pos (pow_pos hlam d) _), ?_⟩
  intro T hT hT_le_one y₀ A f u hAcont hf hu hlo hsub hboundary zStar hzStar
  have hpos := lower_loewner_posDef_on hlam hlo
  have hroot := hABP hT hT_le_one y₀ A f u hAcont hf hu hpos hsub hboundary zStar hzStar
  have hsourceMem := source_memLp_on_parabolicInterior hf (d := d) (T := T) (y₀ := y₀)
  have hweightedInt := weighted_integrableOn hAcont hf hpos
  have hsourceInt := source_integrableOn (d := d) (lam := lam) (T := T) (y₀ := y₀) hlam hf
  have hcomparison := weighted_integral_le_of_lower hlam hlo hweightedInt hsourceInt
  let W : ℝ := ∫ z in parabolicInterior T y₀,
    (max (f z) 0) ^ (d + 1) / (coefficientAt A z).det ∂volume
  let I : ℝ := ∫ z in parabolicInterior T y₀, (max (f z) 0) ^ (d + 1) ∂volume
  have hW : 0 ≤ W := by
    dsimp [W]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (measurableSet_parabolicInterior T y₀)] with z hz
    exact div_nonneg (pow_nonneg (le_max_right _ _) _)
      (hpos z (parabolicInterior_subset_closedParabolicCylinder T y₀ hz)).det_pos.le
  have hI : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun z => pow_nonneg (le_max_right _ _) _
  have hWI : W ≤ I / lam ^ d := by
    dsimp [W, I]
    rw [integral_div] at hcomparison
    exact hcomparison
  calc
    u zStar ≤ C_d * W ^ (1 / ((d : ℝ) + 1) : ℝ) := by
      simpa using hroot
    _ ≤ (C_d / (lam ^ d) ^ (1 / ((d : ℝ) + 1) : ℝ)) *
        I ^ (1 / ((d : ℝ) + 1) : ℝ) :=
      scalar_root_bound hC_d.le hlam hW hWI hI
    _ = (C_d / (lam ^ d) ^ (1 / ((d : ℝ) + 1) : ℝ)) *
        parabolicLpNormOn d (fun z => max (f z) 0)
          (parabolicInterior T y₀) := by
      rw [parabolicLpNormOn_eq_integral_pow hsourceMem]

end HypoellipticAleksandrov.Parabolic

