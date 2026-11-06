module

public import Mathlib.Analysis.Calculus.Deriv.Prod

public import HypoellipticAleksandrov.Parabolic.MovingLensChart
public import HypoellipticAleksandrov.Parabolic.ContactMap
public import HypoellipticAleksandrov.Parabolic.MovingLensSign
public import HypoellipticAleksandrov.Parabolic.JacobianLocal
public import HypoellipticAleksandrov.Parabolic.AreaFormula
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Physical moving-lens first contact

This file records the direct, physical-coordinate first-contact coverage used
by the supplied-source moving-lens ABP argument.  The moving-lens chart is
used only to produce continuous paths inside the lens; no PDE quantity is
pulled back through it.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

open Filter Set
open scoped Topology

variable {d : ℕ} {xi eps tau : ℝ} {y : PDE.Vec d} {z : TimeVelocity d}

/-- Concrete physical contact/area API for supplied-source lower-bound proof: sign set. -/
def movingLensSourceSignSet  (xi eps tau : ℝ) (y : PDE.Vec d)
    (u : TimeVelocity d → ℝ) : Set (TimeVelocity d) :=
  {z | 0 < z.1 ∧ z.1 < tau ∧
    PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1 ∧
    0 < u z ∧ 0 ≤ timeDerivative u z ∧ (-velocityHessian u z).PosSemidef}

/-- Concrete physical contact/area API for supplied-source lower-bound proof: velocity footprint. -/
def movingLensVelocityFootprint (d : ℕ) (kappa : ℝ) : ℝ :=
  kappa + Real.sqrt d * kappa ^ (-3 : ℤ)

/-- Concrete physical contact/area API for supplied-source lower-bound proof: its wedge. -/
def movingLensSlopeInterceptWedge (d : ℕ) (R M : ℝ) : Set (TimeVelocity d) :=
  Set.Ioo (M / 2) (3 * M / 4) ×ˢ
    PDE.euclideanBall (0 : PDE.Vec d) (M / (4 * R))

theorem movingLensSignXi_nonneg {kappa : ℝ} (hkappa : 0 < kappa) :
    0 ≤ movingLensSignXi kappa := by
  unfold movingLensSignXi
  positivity

private theorem movingLensDenominator_lt_kappa_sq
    {kappa eps tau t : ℝ} (hkappa : 0 < kappa)
    (heps_small : 2 * eps ^ 2 < kappa ^ 2) (ht : t ≤ tau)
    (htau_kappa : tau ≤ kappa⁻¹) :
    movingLensDenominator (movingLensSignXi kappa) eps t < kappa ^ 2 := by
  have hxi := movingLensSignXi_nonneg hkappa
  have hslope  := by
    calc
      movingLensSignXi kappa * t ≤ movingLensSignXi kappa * kappa⁻¹ :=
        mul_le_mul_of_nonneg_left (ht.trans htau_kappa) hxi
      _ = kappa ^ 2 / 2 := by
        unfold movingLensSignXi
        grind
  unfold movingLensDenominator
  nlinarith

private theorem vecEuclideanNorm_le_of_sq_le
     {v : PDE.Vec d} {R : ℝ}
    (hR : 0 ≤ R) (h : PDE.vecNormSq v ≤ R ^ 2) :
    PDE.vecEuclideanNorm v ≤ R := by
  have hsq : PDE.vecEuclideanNorm v ^ 2 ≤ R ^ 2 := by
    simpa only [PDE.vecEuclideanNorm_sq] using h
  nlinarith

private theorem movingLensClosed_velocity_norm_lt_footprint
     {kappa tau eps : ℝ} {y : PDE.Vec d}
    (hkappa : 0 < kappa) (htau_kappa : tau ≤ kappa⁻¹)
    (heps_small : 2 * eps ^ 2 < kappa ^ 2)
    (hy : PDE.vecNormSq y ≤ (d : ℝ) * kappa ^ (-4 : ℤ))
    {z : TimeVelocity d}
    (hz : z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y) :
    PDE.vecEuclideanNorm z.2 < movingLensVelocityFootprint d kappa := by
  rcases hz with ⟨hz0, hztau, hzspatial⟩
  have hden  :=
    movingLensDenominator_lt_kappa_sq hkappa heps_small hztau htau_kappa
  have hdisp_sq : PDE.vecNormSq _ < kappa ^ 2 :=
    hzspatial.trans_lt hden
  have hdisp : PDE.vecEuclideanNorm (movingLensDisplacement y z) < kappa := by
    have hsq : PDE.vecEuclideanNorm (movingLensDisplacement y z) ^ 2 < kappa ^ 2 := by
      simpa only [PDE.vecEuclideanNorm_sq] using hdisp_sq
    nlinarith
  have hdnonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hybound : PDE.vecEuclideanNorm y ≤ Real.sqrt d * kappa ^ (-2 : ℤ) := by
    apply vecEuclideanNorm_le_of_sq_le
    · positivity
    · have hsquare : (Real.sqrt d * kappa ^ (-2 : ℤ)) ^ 2 =
          (d : ℝ) * kappa ^ (-4 : ℤ) := by
        rw [mul_pow, Real.sq_sqrt hdnonneg]
        have hpow : (kappa ^ (-2 : ℤ)) ^ 2 = kappa ^ (-4 : ℤ) := by
          calc
            (kappa ^ (-2)) ^ 2 = kappa ^ ((-2) * 2) :=
              (zpow_mul kappa _ 2).symm
            _ = kappa ^ (-4 : ℤ) := by norm_num
        rw [hpow]
      simp_all
  have htime_norm : PDE.vecEuclideanNorm (z.1 • y) ≤
      Real.sqrt d * kappa ^ (-3 : ℤ) := by
    rw [PDE.vecEuclideanNorm_smul, abs_of_nonneg hz0]
    have hfirst  :=
      mul_le_mul_of_nonneg_left hybound hz0
    calc
      z.1 * PDE.vecEuclideanNorm y ≤ z.1 * (Real.sqrt d * kappa ^ (-2)) := hfirst
      _ ≤ kappa⁻¹ * (Real.sqrt d * kappa ^ (-2)) :=
        mul_le_mul_of_nonneg_right (hztau.trans htau_kappa) (by positivity)
      _ = Real.sqrt d * kappa ^ (-3 : ℤ) := by
        field_simp [hkappa.ne']
  have hsplit : z.2 = movingLensDisplacement y z + z.1 • y := by
    rw [movingLensDisplacement]
    simp
  rw [hsplit]
  calc
    PDE.vecEuclideanNorm _ ≤
        PDE.vecEuclideanNorm _ +
          PDE.vecEuclideanNorm _ :=
      PDE.vecEuclideanNorm_add_le _ _
    _ < kappa + Real.sqrt d * kappa ^ (-3) :=
      add_lt_add_of_lt_of_le hdisp htime_norm

private theorem affineVelocity_pos_on_movingLens
     {kappa tau eps M h : ℝ} {y p : PDE.Vec d}
    (hkappa : 0 < kappa) (htau_kappa : tau ≤ kappa⁻¹)
    (heps_small : 2 * eps ^ 2 < kappa ^ 2)
    (hy : PDE.vecNormSq y ≤ (d : ℝ) * kappa ^ (-4 : ℤ))
    (hM : 0 < M) (hh : M / 2 < h)
    (hp : p ∈ PDE.euclideanBall (0 : PDE.Vec d)
      (M / (4 * movingLensVelocityFootprint d kappa)))
    {z : TimeVelocity d}
    (hz : z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y) :
    0 < affineVelocity 0 h p z.2 := by
  have hR : 0 < movingLensVelocityFootprint d kappa := by
    unfold movingLensVelocityFootprint
    positivity
  have hpNorm  := by
    simpa using (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (x₀ := (0)) (x := p)
      (R := M / (4 * movingLensVelocityFootprint d kappa)) (by positivity)).mp hp
  have hzNorm  :=
    movingLensClosed_velocity_norm_lt_footprint hkappa htau_kappa heps_small hy hz
  have hprod : PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm z.2 < M / 4 := by
    calc
      PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm z.2 ≤
          PDE.vecEuclideanNorm p * movingLensVelocityFootprint d kappa :=
        mul_le_mul_of_nonneg_left hzNorm.le (PDE.vecEuclideanNorm_nonneg p)
      _ < (M / (4 * movingLensVelocityFootprint d kappa)) *
          movingLensVelocityFootprint d kappa :=
        mul_lt_mul_of_pos_right hpNorm hR
      _ = M / 4 := by grind
  have hdot : -(M / 4) < PDE.vecDot p z.2 := by
    nlinarith [neg_abs_le (PDE.vecDot p z.2),
      (PDE.abs_vecDot_le_vecEuclideanNorm_mul p z.2).trans_lt hprod]
  rw [affineVelocity_apply]
  simp only [sub_zero]
  linarith

private theorem affineVelocity_lt_on_movingLens
     {kappa tau eps M h : ℝ} {y p : PDE.Vec d}
    (hkappa : 0 < kappa) (htau_kappa : tau ≤ kappa⁻¹)
    (heps_small : 2 * eps ^ 2 < kappa ^ 2)
    (hy : PDE.vecNormSq y ≤ (d : ℝ) * kappa ^ (-4 : ℤ))
    (hM : 0 < M) (hh : h < 3 * M / 4)
    (hp : p ∈ PDE.euclideanBall (0 : PDE.Vec d)
      (M / (4 * movingLensVelocityFootprint d kappa)))
    {z : TimeVelocity d}
    (hz : z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y) :
    affineVelocity 0 h p z.2 < M := by
  have hR : 0 < movingLensVelocityFootprint d kappa := by
    unfold movingLensVelocityFootprint
    positivity
  have hpNorm  := by
    simpa using (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (x₀ := (0)) (x := p)
      (R := M / (4 * movingLensVelocityFootprint d kappa)) (by positivity)).mp hp
  have hzNorm  :=
    movingLensClosed_velocity_norm_lt_footprint hkappa htau_kappa heps_small hy hz
  have hprod : PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm z.2 < M / 4 := by
    calc
      PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm z.2 ≤
          PDE.vecEuclideanNorm p * movingLensVelocityFootprint d kappa :=
        mul_le_mul_of_nonneg_left hzNorm.le (PDE.vecEuclideanNorm_nonneg p)
      _ < (M / (4 * movingLensVelocityFootprint d kappa)) *
          movingLensVelocityFootprint d kappa :=
        mul_lt_mul_of_pos_right hpNorm hR
      _ = M / 4 := by grind
  have hdot : PDE.vecDot p z.2 < M / 4 :=
    lt_of_le_of_lt (le_abs_self _) ((PDE.abs_vecDot_le_vecEuclideanNorm_mul p z.2).trans_lt hprod)
  rw [affineVelocity_apply]
  simp only [sub_zero]
  linarith

private theorem movingLensChartInv_mem_closed
    
    (hxi : 0 ≤ xi) (heps : 0 < eps) {q : TimeVelocity d}
    (hq : q ∈ closedParabolicCylinder tau (0 : PDE.Vec d)) :
    movingLensChartInv xi eps y q ∈ movingLensClosed xi eps tau y := by
  have hqImage : q ∈ movingLensChart xi eps y '' movingLensClosed xi eps tau y := by
    rw [movingLensChart_image_closed hxi heps]
    exact hq
  rcases hqImage with ⟨z, hz, hzq⟩
  aesop

private theorem affineVelocity_line_deriv_at_zero
     (h : ℝ) (p v : PDE.Vec d) (i : Fin d) :
    HasDerivAt
      (fun r : ℝ => affineVelocity 0 h p
        (v + r • ((Pi.single i (1 : ℝ)) : PDE.Vec d)))
      (p i) 0 := by
  let e : PDE.Vec d := Pi.single i 1
  have hfun :
      (fun r : ℝ => affineVelocity 0 h p (v + r • e)) =
        fun r => affineVelocity 0 h p v + r * p i := by
    classical
    funext r
    have hsingle : (∑ x : Fin d, p x * r * e x) = r * p i := by
      dsimp [e]
      rw [Fintype.sum_eq_single i]
      · grind
      simp_all
    unfold affineVelocity PDE.vecDot
    have hsplit  := by
      calc
        h + (∑ x, p x * (v x + r * e x)) =
            h + (∑ x, (p x * v x + p x * r * e x)) := by
              grind
        _ = h + (∑ x, p x * v x) + (∑ x, p x * r * e x) := by
              rw [Finset.sum_add_distrib]
              ring
    simp_all
  rw [hfun]
  simpa only [one_mul] using
    ((hasDerivAt_id' (𝕜 := ℝ) 0).mul_const _).const_add
      _

private theorem movingLensChart_path_mem_closed
    
    (hxi : 0 ≤ xi) (heps : 0 < eps)
    (hz : z ∈ movingLensClosed xi eps tau y) {s : ℝ}
    (hs : s ∈ Set.Icc 0 z.1) :
    movingLensChartInv xi eps y (s, (movingLensChart xi eps y z).2) ∈
      movingLensClosed xi eps tau y := by
  have hzTrunc : z ∈ movingLensClosed xi eps z.1 y := ⟨hz.1, le_rfl, hz.2.2⟩
  have hzChart : movingLensChart xi eps y z ∈
      closedParabolicCylinder z.1 (0) := by
    rw [← movingLensChart_image_closed hxi heps]
    exact ⟨z, hzTrunc, rfl⟩
  rw [mem_closedParabolicCylinder_iff] at hzChart
  have hpathTrunc : movingLensChartInv xi eps y
      (s, (movingLensChart xi eps y z).2) ∈ movingLensClosed xi eps z.1 y := by
    apply movingLensChartInv_mem_closed hxi heps
    simp_all
  exact ⟨hpathTrunc.1, hpathTrunc.2.1.trans hz.2.1, hpathTrunc.2.2⟩

private theorem movingLensChart_path_initial_mem_causalBoundary
    
    (hxi : 0 ≤ xi) (heps : 0 < eps)
    (hz : z ∈ movingLensClosed xi eps tau y) :
    movingLensChartInv xi eps y (0, (movingLensChart xi eps y z).2) ∈
      movingLensClosed xi eps tau y \ movingLensActive xi eps tau y := by
  refine ⟨movingLensChart_path_mem_closed hxi heps hz ⟨le_rfl, hz.1⟩, ?_⟩
  intro hactive
  exact (ne_of_gt hactive.1) (by aesop)

end

end HypoellipticAleksandrov.Parabolic
namespace HypoellipticAleksandrov.Parabolic

noncomputable section

open Filter Set
open scoped Topology

private theorem zero_between_of_continuousOn_of_neg_pos_local
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ c ∈ Set.Ioo a b, f c = 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc _ _ := ⟨hfa.le, hfb.le⟩
  rcases intermediate_value_Icc hab.le hf hzero with ⟨c, hc, hfc⟩
  grind

variable {d : ℕ} {u : TimeVelocity d → ℝ} {z : TimeVelocity d}

private theorem time_slice_hasDerivAt_of_contDiffAt_local
    
    (hu : ContDiffAt ℝ 2 u z) :
    HasDerivAt (fun t : ℝ => u (t, z.2)) (timeDerivative u z) z.1 := by
  have hline : HasDerivAt (fun t : ℝ => (t, z.2))
      ((1, 0)) z.1 := HasDerivAt.prodMk (hasDerivAt_id' (𝕜 := ℝ) z.1)
      (hasDerivAt_const (x := z.1) (c := z.2))
  simpa only [timeDerivative, Function.comp_def] using
    hu.differentiableAt (by norm_num) |>.hasFDerivAt.comp_hasDerivAt z.1 hline

private theorem velocity_slice_hasDerivAt_of_contDiffAt_local
    
    (hu : ContDiffAt ℝ 2 u z) (i : Fin d) :
    HasDerivAt
      (fun r : ℝ => u (z.1,
        z.2 + r • ((Pi.single i (1 : ℝ)) : PDE.Vec d)))
      (velocityGradient u z i) 0 := by
  let e : PDE.Vec d := Pi.single i 1
  have hvline : HasDerivAt (fun r : ℝ => z.2 + r • e) e 0 := by
    simpa using
      ((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const e).const_add z.2
  have hline : HasDerivAt (fun r : ℝ => (z.1, z.2 + r • e))
      (((0 : ℝ), e)) 0 :=
    (hasDerivAt_const (x := (0)) (c := z.1)).prodMk hvline
  have huAt : HasFDerivAt u (fderiv ℝ u z)
      (z.1, z.2 + (0 : ℝ) • e) := by
    simpa using
      (hu.differentiableAt (by norm_num)).hasFDerivAt
  have hcomp := huAt.comp_hasDerivAt 0 hline
  aesop

/-- Concrete physical contact/area API for supplied-source lower-bound proof: local coverage. -/
theorem movingLensSlopeInterceptWedge_subset_image_signSet_local
    (d : ℕ) (hd : 0 < d) (kappa tau eps : ℝ) (y : PDE.Vec d)
    (hkappa : 0 < kappa) (hkappa_one : kappa ≤ 1)
    (htau : 0 < tau) (htau_kappa : tau ≤ kappa⁻¹)
    (heps : 0 < eps) (heps_small : 2 * eps ^ 2 < kappa ^ 2)
    (hy : PDE.vecNormSq y ≤ (d : ℝ) * kappa ^ (-4 : ℤ))
    (u : TimeVelocity d → ℝ)
    (hucont : ContinuousOn u
      (movingLensClosed (movingLensSignXi kappa) eps tau y))
    (hulocal : ∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
      ContDiffAt ℝ 2 u z)
    (hboundary : ∀ z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y \
      movingLensActive (movingLensSignXi kappa) eps tau y, u z ≤ 0)
    (M : ℝ) (hM : 0 < M) (hMvalue : M = u (tau, tau • y)) :
    movingLensSlopeInterceptWedge d (movingLensVelocityFootprint d kappa) M ⊆
      parabolicNormalMap u 0 ''
        movingLensSourceSignSet (movingLensSignXi kappa) eps tau y u := by
  rintro ⟨h, p⟩ hpWedge
  rcases hpWedge with ⟨⟨hhLower, hhUpper⟩, hp⟩
  let xi : ℝ := movingLensSignXi kappa
  let ell : PDE.Vec d → ℝ := affineVelocity 0 h p
  let g : TimeVelocity d → ℝ := fun z => u z - ell z.2
  have hxi : 0 ≤ xi := movingLensSignXi_nonneg hkappa
  have hclosedCenter : (tau, tau • y) ∈ movingLensClosed xi eps tau y := by
    refine ⟨htau.le, le_rfl, ?_⟩
    rw [movingLensDisplacement, sub_self]
    simp only [PDE.vecNormSq, PDE.vecDot, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero]
    exact (movingLensDenominator_pos hxi heps htau.le).le
  have hellPos : ∀ z ∈ movingLensClosed xi eps tau y, 0 < ell z.2 := by
    intro z hz
    exact affineVelocity_pos_on_movingLens hkappa htau_kappa heps_small hy hM hhLower hp hz
  have hellLt : ∀ z ∈ movingLensClosed xi eps tau y, ell z.2 < M := by
    intro z hz
    exact affineVelocity_lt_on_movingLens hkappa htau_kappa heps_small hy hM hhUpper hp hz
  have hgCenter : 0 < g (tau, tau • y) := by
    change 0 < u _ - ell _
    rw [← hMvalue]
    exact sub_pos.mpr (hellLt _ hclosedCenter)
  have hgCont : ContinuousOn g (movingLensClosed xi eps tau y) := by
    have hellCont : Continuous (fun z : TimeVelocity d => ell z.2) := by
      unfold ell affineVelocity PDE.vecDot
      fun_prop
    exact hucont.sub hellCont.continuousOn
  let S : Set (TimeVelocity d) :=
    movingLensClosed xi eps tau y ∩ {z | 0 ≤ g z}
  have hcenterS : (tau, tau • y) ∈ S := ⟨hclosedCenter, hgCenter.le⟩
  have hSCompact : IsCompact S := by
    have hLensCompact : IsCompact (movingLensClosed xi eps tau y) :=
      isCompact_movingLensClosed hxi heps htau.le
    have hSClosed : IsClosed S := hgCont.preimage_isClosed_of_isClosed hLensCompact.isClosed isClosed_Ici
    exact hLensCompact.of_isClosed_subset hSClosed inter_subset_left
  rcases hSCompact.exists_isMinOn ⟨(tau, tau • y), hcenterS⟩
      continuous_fst.continuousOn with ⟨zc, hzcS, hzcMin⟩
  have hzcClosed : zc ∈ movingLensClosed xi eps tau y := hzcS.1
  have hzcNonneg : 0 ≤ g zc := hzcS.2
  have htcPos : 0 < zc.1 := by
    by_contra hnot
    have hzero  := le_antisymm (not_lt.mp hnot) hzcClosed.1
    let path  := fun s =>
      movingLensChartInv xi eps y (s, (movingLensChart xi eps y zc).2)
    have hpathZero : path 0 ∈ movingLensClosed xi eps tau y \
        movingLensActive xi eps tau y := movingLensChart_path_initial_mem_causalBoundary hxi heps hzcClosed
    have hpathEq : path 0 = zc := by
      dsimp only [path]
      have hEq : (0, (movingLensChart xi eps y zc).2) =
          movingLensChart xi eps y zc := by
        apply Prod.ext
        · simpa [movingLensChart] using hzero.symm
        · rfl
      rw [hEq]
      simpa using movingLensChartInv_apply_movingLensChart hxi heps hzcClosed.1
    grind
  have hgcZero : g zc = 0 := by
    apply le_antisymm ?_ hzcNonneg
    by_contra hnot
    have hgcPos : 0 < g zc := lt_of_not_ge hnot
    let path : ℝ → TimeVelocity d := fun s =>
      movingLensChartInv xi eps y (s, (movingLensChart xi eps y zc).2)
    have hpathCont : Continuous path := by
      dsimp only [path, movingLensChartInv]
      unfold movingLensDenominator
      fun_prop
    have hpathZero : path 0 ∈ movingLensClosed xi eps tau y \
        movingLensActive xi eps tau y := movingLensChart_path_initial_mem_causalBoundary hxi heps hzcClosed
    have hgZero : g (path 0) < 0 := by
      have hbd := hboundary _ hpathZero
      have hpz := hellPos _ hpathZero.1
      linarith
    have hpathEnd : path zc.1 = zc := movingLensChartInv_apply_movingLensChart hxi heps hzcClosed.1
    let f : ℝ → ℝ := fun s => g (path s)
    have hfCont : ContinuousOn f (Set.Icc 0 zc.1) := by
      have hcomp := hgCont.comp hpathCont.continuousOn (by
        intro s hs
        exact movingLensChart_path_mem_closed hxi heps hzcClosed hs)
      simpa only [f, Function.comp_def] using hcomp
    rcases zero_between_of_continuousOn_of_neg_pos_local htcPos hfCont
        (by simpa [f] using hgZero) (by simpa [f, hpathEnd] using hgcPos) with
      ⟨s, hs, hfs⟩
    have hsS : path s ∈ S := by
      refine ⟨?_, ?_⟩
      · exact movingLensChart_path_mem_closed hxi heps hzcClosed ⟨hs.1.le, hs.2.le⟩
      · simpa [f] using hfs.ge
    have hmin := hzcMin hsS
    change zc.1 ≤ s at hmin
    grind
  have htcLt : zc.1 < tau := by
    let zT : TimeVelocity d := (tau, tau • y)
    let path : ℝ → TimeVelocity d := fun s =>
      movingLensChartInv xi eps y (s, (movingLensChart xi eps y zT).2)
    have hpathCont : Continuous path := by
      dsimp only [path, movingLensChartInv]
      unfold movingLensDenominator
      fun_prop
    have hpathZero : path 0 ∈ movingLensClosed xi eps tau y \
        movingLensActive xi eps tau y := movingLensChart_path_initial_mem_causalBoundary hxi heps hclosedCenter
    have hgZero : g (path 0) < 0 := by
      have hbd := hboundary _ hpathZero
      have hpz := hellPos _ hpathZero.1
      linarith
    have hpathEnd : path tau = zT := movingLensChartInv_apply_movingLensChart hxi heps hclosedCenter.1
    let f : ℝ → ℝ := fun s => g (path s)
    have hfCont : ContinuousOn f (Set.Icc 0 tau) := by
      have hcomp := hgCont.comp hpathCont.continuousOn (by
        intro s hs
        exact movingLensChart_path_mem_closed hxi heps hclosedCenter hs)
      simpa only [f, Function.comp_def] using hcomp
    rcases zero_between_of_continuousOn_of_neg_pos_local htau hfCont
        (by simpa [f] using hgZero) (by simpa [f, hpathEnd, zT] using hgCenter) with
      ⟨s, hs, hfs⟩
    have hsS : path s ∈ S := by
      refine ⟨?_, ?_⟩
      · exact movingLensChart_path_mem_closed hxi heps hclosedCenter ⟨hs.1.le, hs.2.le⟩
      · simpa [f] using hfs.ge
    have hmin := hzcMin hsS
    change zc.1 ≤ s at hmin
    grind
  have hspatialNonpos : ∀ v : PDE.Vec d,
      (zc.1, v) ∈ movingLensClosed xi eps tau y → g (zc.1, v) ≤ 0 := by
    intro v hv
    by_contra hnot
    have hpos : 0 < g (zc.1, v) := lt_of_not_ge hnot
    let zv : TimeVelocity d := (zc.1, v)
    let path : ℝ → TimeVelocity d := fun s =>
      movingLensChartInv xi eps y (s, (movingLensChart xi eps y zv).2)
    have hpathCont : Continuous path := by
      dsimp only [path, movingLensChartInv]
      unfold movingLensDenominator
      fun_prop
    have hpathZero : path 0 ∈ movingLensClosed xi eps tau y \
        movingLensActive xi eps tau y := movingLensChart_path_initial_mem_causalBoundary hxi heps hv
    have hgZero : g (path 0) < 0 := by
      have hbd := hboundary _ hpathZero
      have hpz := hellPos _ hpathZero.1
      linarith
    have hpathEnd : path zc.1 = zv := movingLensChartInv_apply_movingLensChart hxi heps hv.1
    let f : ℝ → ℝ := fun s => g (path s)
    have hfCont : ContinuousOn f (Set.Icc 0 zc.1) := by
      have hcomp := hgCont.comp hpathCont.continuousOn (by
        intro s hs
        exact movingLensChart_path_mem_closed hxi heps hv hs)
      simpa only [f, Function.comp_def] using hcomp
    rcases zero_between_of_continuousOn_of_neg_pos_local htcPos hfCont
        (by simpa [f] using hgZero) (by simpa [f, hpathEnd, zv] using hpos) with
      ⟨s, hs, hfs⟩
    have hsS : path s ∈ S := by
      refine ⟨?_, ?_⟩
      · exact movingLensChart_path_mem_closed hxi heps hv ⟨hs.1.le, hs.2.le⟩
      · simpa [f] using hfs.ge
    have hmin := hzcMin hsS
    change zc.1 ≤ s at hmin
    grind
  have hzcSpatial : PDE.vecNormSq (movingLensDisplacement y zc) <
      movingLensDenominator xi eps zc.1 := by
    by_contra hnot
    have heq  := le_antisymm hzcClosed.2.2 (not_lt.mp hnot)
    have hbd  := hboundary zc (by
      rw [mem_movingLensClosed_diff_active_iff]
      exact Or.inr ⟨hzcClosed.1, hzcClosed.2.1, heq⟩)
    have hpz := hellPos zc hzcClosed
    linarith
  have hzcActive : zc ∈ movingLensActive xi eps tau y :=
    ⟨htcPos, hzcClosed.2.1, hzcSpatial⟩
  have huz  := hulocal zc hzcActive
  have huzcPos : 0 < u zc := by
    have hpz := hellPos zc hzcClosed
    linarith
  have hspatialLocalMax : IsLocalMax
      (fun v : PDE.Vec d => u (zc.1, v) - ell v) zc.2 := by
    have hopen  := (isOpen_movingLensSpatialStrict xi eps y).preimage
        (continuous_const.prodMk continuous_id) |>.mem_nhds hzcSpatial
    filter_upwards [hopen] with v hv
    have hvClosed : (zc.1, v) ∈ movingLensClosed xi eps tau y :=
      ⟨htcPos.le, hzcClosed.2.1, hv.le⟩
    grind
  have hgrad : velocityGradient u zc = p := by
    ext i
    let q : PDE.Vec d := Pi.single i 1
    let line : ℝ → PDE.Vec d := fun r => zc.2 + r • q
    have hlineCont  :=
      (((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const q).const_add zc.2).continuousAt
    have hmaxLine : IsLocalMax
        (fun r : ℝ => u (zc.1, line r) - ell (line r)) 0 := by
      have hmaxAtLine : IsLocalMax
          (fun v : PDE.Vec d => u (zc.1, v) - ell v) (line 0) := by
        simpa [line, q] using hspatialLocalMax
      exact hmaxAtLine.comp_continuous hlineCont
    have hderiv : HasDerivAt
        (fun r : ℝ => u _ -
          ell _)
        _ 0 :=
      (velocity_slice_hasDerivAt_of_contDiffAt_local huz i).sub
        (affineVelocity_line_deriv_at_zero h p zc.2 i)
    have hzero := hmaxLine.hasDerivAt_eq_zero (by simpa [line, q] using hderiv)
    linarith
  have hcontact : IsLocalMax
      (fun v : PDE.Vec d => u (zc.1, v) -
        (u zc + PDE.vecDot p (v - zc.2))) zc.2 := by
    have hrewrite :
        (fun v : PDE.Vec d => u (zc.1, v) - ell v) =
          fun v : PDE.Vec d => u (zc.1, v) -
            (u zc + PDE.vecDot p (v - zc.2)) := by
      funext v
      dsimp only [ell]
      simp only [affineVelocity_apply, sub_zero]
      have hgcZero' := hgcZero
      dsimp only [g, ell] at hgcZero'
      simp only [affineVelocity_apply, sub_zero] at hgcZero'
      unfold PDE.vecDot at hgcZero' ⊢
      have hsum : (∑ x, p x * v x) =
          (∑ x, p x * zc.2 x) + ∑ x, p x * (v - zc.2) x := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Pi.sub_apply]
        ring
      linarith
    simp_all
  have hhess  :=
    neg_velocityHessian_posSemidef_of_spatial_localMax_affineContact_of_contDiffAt huz hcontact
  have htimeMax : IsLocalMaxOn
      (fun t : ℝ => u (t, zc.2) - ell zc.2) (Set.Iic zc.1) zc.1 := by
    have hpast := movingLensActive_mem_nhdsWithin_past hzcActive
    have hlineTendsto : Tendsto (fun t : ℝ => (t, zc.2))
        (𝓝[Set.Iic zc.1] zc.1) (𝓝[Set.Iic zc.1 ×ˢ Set.univ] zc) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_nhdsWithin_of_tendsto_nhds
        ((continuous_id.prodMk continuous_const).continuousAt.tendsto), ?_⟩
      filter_upwards [eventually_mem_nhdsWithin] with t ht
      exact ⟨ht, mem_univ _⟩
    have hactiveEventually  := hlineTendsto.eventually hpast
    filter_upwards [hactiveEventually, eventually_mem_nhdsWithin] with t ht hle
    have htime : g (t, zc.2) ≤ 0 := by
      by_contra hnot
      have hpos  := lt_of_not_ge hnot
      have htS : (t, zc.2) ∈ S :=
        ⟨movingLensActive_subset_movingLensClosed xi eps tau y ht, hpos.le⟩
      have hmin := hzcMin htS
      have hne : zc.1 ≠ t := by
        intro heq
        subst t
        linarith [hgcZero]
      have hlt  := lt_of_le_of_ne hmin hne
      exact (not_lt_of_ge hle) hlt
    linarith
  have htimeDeriv : HasDerivAt
      (fun t : ℝ => u _ - ell zc.2) _ zc.1 :=
    (time_slice_hasDerivAt_of_contDiffAt_local huz).sub_const (ell zc.2)
  have hminusOne : (-1) ∈ posTangentConeAt (Set.Iic zc.1) zc.1 := by
    have hsegment : segment ℝ zc.1 (zc.1 - 1) ⊆ Set.Iic zc.1 := by
      intro s hs
      rw [segment_symm] at hs
      exact (segment_subset_Icc (sub_le_self _ (by norm_num)) hs).2
    simpa using sub_mem_posTangentConeAt_of_segment_subset hsegment
  have htimeNonneg : 0 ≤ timeDerivative u zc := by
    have hnonpos := htimeMax.hasFDerivWithinAt_nonpos htimeDeriv.hasDerivWithinAt hminusOne
    have hneg  := by simpa using hnonpos
    linarith
  refine ⟨zc, ?_, ?_⟩
  · exact ⟨htcPos, htcLt, hzcSpatial, huzcPos, htimeNonneg, hhess⟩
  · apply Prod.ext
    · change u zc - PDE.vecDot (velocityGradient u zc) (zc.2 - 0) = h
      simp only [sub_zero]
      rw [hgrad]
      dsimp only [g, ell] at hgcZero
      simp only [affineVelocity_apply, sub_zero] at hgcZero
      linarith
    · exact hgrad

end

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

variable {d : Nat}

private theorem movingLensSourceSignSet_areaFormulaData_of_localC2
     {xi eps tau : Real} {y : PDE.Vec d}
    {u : TimeVelocity d -> Real}
    (hlocal : ∀ z ∈ movingLensActive xi eps tau y, ContDiffAt Real 2 u z) :
    MeasurableSet (movingLensSourceSignSet xi eps tau y u) /\
      ∀ z ∈ movingLensSourceSignSet xi eps tau y u,
        HasFDerivWithinAt (parabolicNormalMap u 0)
          (parabolicNormalMapDerivative u 0 z)
          (movingLensSourceSignSet xi eps tau y u) z := by
  let O  := {z | 0 < z.1 /\ z.1 < tau /\
    PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1}
  have hO : IsOpen O := by
    rw [show O = {z | 0 < z.1 /\
        PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1} ∩
          {z | z.1 < tau} by
      aesop]
    exact (isOpen_movingLensPositiveSpatialStrict xi eps y).inter
      (isOpen_Iio.preimage continuous_fst)
  have hO_active : O ⊆ movingLensActive xi eps tau y := by
    rintro z ⟨hzpos, hzlt, hzspatial⟩
    exact ⟨hzpos, hzlt.le, hzspatial⟩
  have huO : ContDiffOn Real 2 u O := fun z hz =>
    (hlocal z (hO_active hz)).contDiffWithinAt
  have hDu : ContDiffOn Real 1 (fderiv Real u) O :=
    huO.fderiv_of_isOpen hO (by norm_num)
  have hD2u : ContDiffOn Real 0 (fderiv Real (fderiv Real u)) O :=
    hDu.fderiv_of_isOpen hO (by norm_num)
  have hucont : ContinuousOn u O := huO.continuousOn
  have htime : ContinuousOn (timeDerivative u) O := by
    unfold timeDerivative
    simpa using hDu.continuousOn.clm_apply continuousOn_const
  have hhess : ContinuousOn (velocityHessian u) O := by
    unfold velocityHessian
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    simpa using hD2u.continuousOn.clm_apply continuousOn_const |>.clm_apply continuousOn_const
  have hpsdclosed : IsClosed {H : PDE.Mat d | H.PosSemidef} := by
    have hhermitian : IsClosed {H : PDE.Mat d | H.IsHermitian} := by
      have hset :
          {H : PDE.Mat d | H.IsHermitian} =
            ⋂ i : Fin d, ⋂ j : Fin d, {H : PDE.Mat d | H j i = H i j} := by
        ext H
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
        constructor
        · intro h i j
          simpa using h.apply i j
        · intro h
          apply Matrix.IsHermitian.ext
          omega
      rw [hset]
      refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      exact isClosed_eq (continuous_id.matrix_elem j i) (continuous_id.matrix_elem i j)
    have hset :
        {H : PDE.Mat d | H.PosSemidef} =
          {H : PDE.Mat d | H.IsHermitian} ∩
            ⋂ q : PDE.Vec d, {H : PDE.Mat d | 0 ≤ dotProduct q (H.mulVec q)} := by
      ext H
      simpa using (Matrix.posSemidef_iff_dotProduct_mulVec (M := H))
    rw [hset]
    refine hhermitian.inter (isClosed_iInter fun q => ?_)
    have hquad : Continuous (fun H : PDE.Mat d => dotProduct q (H.mulVec q)) :=
      continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
    exact isClosed_le continuous_const hquad
  have hpositive : MeasurableSet (O ∩ {z | 0 < u z}) :=
    (hucont.isOpen_inter_preimage hO isOpen_Ioi).measurableSet
  have hnonnegative : MeasurableSet (O ∩ {z | 0 ≤ timeDerivative u z}) := by
    rw [show O ∩ {z | 0 ≤ timeDerivative u z} =
        O \ (O ∩ (timeDerivative u) ⁻¹' Set.Iio 0) by
      aesop]
    exact hO.measurableSet.diff
      (htime.isOpen_inter_preimage hO isOpen_Iio).measurableSet
  have hpsd : MeasurableSet (O ∩ {z | (-velocityHessian u z).PosSemidef}) := by
    rw [show O ∩ {z | (-velocityHessian u z).PosSemidef} = O \ (O ∩
        (fun z => -velocityHessian u z) ⁻¹' {H : PDE.Mat d | H.PosSemidef}ᶜ) by
      simp]
    exact hO.measurableSet.diff
      ((hhess.neg).isOpen_inter_preimage hO hpsdclosed.isOpen_compl).measurableSet
  have hmeas : MeasurableSet (movingLensSourceSignSet xi eps tau y u) := by
    rw [show movingLensSourceSignSet xi eps tau y u =
        (O ∩ {z | 0 < u z}) ∩ (O ∩ {z | 0 ≤ timeDerivative u z}) ∩
          (O ∩ {z | (-velocityHessian u z).PosSemidef}) by
      ext z
      change (0 < z.1 /\ z.1 < tau /\
        PDE.vecNormSq _ < movingLensDenominator xi eps z.1 /\
        0 < u z /\ 0 ≤ timeDerivative u z /\ (-velocityHessian u z).PosSemidef) ↔
        ((z ∈ O /\ 0 < u z) /\ (z ∈ O /\ 0 ≤ timeDerivative u z)) /\
          (z ∈ O /\ (-velocityHessian u z).PosSemidef)
      grind]
    simp_all
  refine ⟨hmeas, ?_⟩
  intro z hz
  exact parabolicNormalMap_hasFDerivWithinAt_of_contDiffAt
    (hlocal z (hO_active ⟨hz.1, hz.2.1, hz.2.2.1⟩))

/-- Concrete physical contact/area API for supplied-source lower-bound proof: wedge-volume bound. -/
theorem movingLensSlopeInterceptWedge_volume_le_lintegral_abs_det_fderiv
     {xi eps tau M R : Real} {y : PDE.Vec d}
    {u : TimeVelocity d -> Real}
    (hlocal : ∀ z ∈ movingLensActive xi eps tau y, ContDiffAt Real 2 u z)
    (hcoverage :
      movingLensSlopeInterceptWedge d R M ⊆
        parabolicNormalMap u 0 '' movingLensSourceSignSet xi eps tau y u) :
    MeasureTheory.MeasureSpace.volume (movingLensSlopeInterceptWedge d R M) ≤
      ∫⁻ z in movingLensSourceSignSet xi eps tau y u,
        ENNReal.ofReal |((fderiv Real (parabolicNormalMap u 0) z).det)|
          ∂MeasureTheory.MeasureSpace.volume := by
  calc
    MeasureTheory.MeasureSpace.volume _ ≤
        MeasureTheory.MeasureSpace.volume
          _ :=
      MeasureTheory.measure_mono hcoverage
    _ ≤ ∫⁻ z in movingLensSourceSignSet xi eps tau y u,
        ENNReal.ofReal _
          ∂MeasureTheory.MeasureSpace.volume :=
      MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv
        MeasureTheory.MeasureSpace.volume
        (movingLensSourceSignSet_areaFormulaData_of_localC2 hlocal).1
        (by
          intro z hz
          have hderiv := parabolicNormalMap_hasFDerivAt_of_contDiffAt (y₀ := 0)
            (hlocal z ⟨hz.1, hz.2.1.le, hz.2.2.1⟩)
          rw [hderiv.fderiv]
          fun_prop)

/-- Concrete physical contact/area API for supplied-source lower-bound proof: wedge volume. -/
theorem volume_movingLensSlopeInterceptWedge
     {R M : Real} (hR : 0 < R) (hM : 0 < M) :
    MeasureTheory.MeasureSpace.volume (movingLensSlopeInterceptWedge d R M) =
      ENNReal.ofReal (M / 4) *
        (ENNReal.ofReal ((M / (4 * R)) ^ d) *
          MeasureTheory.MeasureSpace.volume
            (PDE.euclideanBall (0 : PDE.Vec d) 1)) := by
  unfold movingLensSlopeInterceptWedge
  have hradius : 0 < M / (4 * R) := div_pos hM (mul_pos (by norm_num) hR)
  have hinterval : 3 * M / 4 - M / 2 = M / 4 := by ring
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    Real.volume_Ioo, hinterval,
    PDE.volume_euclideanBall_eq_unit_mul_of_pos _ hradius]

end HypoellipticAleksandrov.Parabolic
