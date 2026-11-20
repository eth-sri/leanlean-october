module

public import Mathlib.Analysis.Calculus.Deriv.Prod

public import HypoellipticAleksandrov.Parabolic.MovingLensChart
public import HypoellipticAleksandrov.Parabolic.ContactMap
public import HypoellipticAleksandrov.Parabolic.MovingLensSign
public import HypoellipticAleksandrov.Parabolic.Jacobian
public import HypoellipticAleksandrov.Parabolic.AreaFormula
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
import HypoellipticAleksandrov.Parabolic.ForwardPropagationGeometry

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

/-- Concrete physical contact/area API for supplied-source lower-bound proof: sign set. -/
def movingLensSourceSignSet {d : ℕ} (xi eps tau : ℝ) (y : PDE.Vec d)
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

private theorem movingLensSignXi_nonneg {kappa : ℝ} (hkappa : 0 < kappa) :
    0 ≤ movingLensSignXi kappa := by
  unfold movingLensSignXi
  positivity

private theorem vecEuclideanNorm_le_of_sq_le
    {d : ℕ} {v : PDE.Vec d} {R : ℝ}
    (hR : 0 ≤ R) (h : PDE.vecNormSq v ≤ R ^ 2) :
    PDE.vecEuclideanNorm v ≤ R := by
  have hv : 0 ≤ PDE.vecEuclideanNorm v := PDE.vecEuclideanNorm_nonneg v
  have hsq : PDE.vecEuclideanNorm v ^ 2 ≤ R ^ 2 := by
    simpa only [PDE.vecEuclideanNorm_sq] using h
  nlinarith

private theorem movingLensClosed_velocity_norm_lt_footprint
    {d : ℕ} {kappa tau eps : ℝ} {y : PDE.Vec d}
    (hkappa : 0 < kappa) (htau_kappa : tau ≤ kappa⁻¹)
    (heps_small : 2 * eps ^ 2 < kappa ^ 2)
    (hy : PDE.vecNormSq y ≤ (d : ℝ) * kappa ^ (-4 : ℤ))
    {z : TimeVelocity d}
    (hz : z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y) :
    PDE.vecEuclideanNorm z.2 < movingLensVelocityFootprint d kappa := by
  rcases hz with ⟨hz0, hztau, hzspatial⟩
  have hkappa_sq : 0 < kappa ^ 2 := sq_pos_of_pos hkappa
  have hden : movingLensDenominator (movingLensSignXi kappa) eps z.1 < kappa ^ 2 :=
    movingLensDenominator_lt_kappa_sq hkappa heps_small hztau htau_kappa
  have hdisp_sq : PDE.vecNormSq (movingLensDisplacement y z) < kappa ^ 2 :=
    hzspatial.trans_lt hden
  have hdisp : PDE.vecEuclideanNorm (movingLensDisplacement y z) < kappa := by
    have hnonneg := PDE.vecEuclideanNorm_nonneg (movingLensDisplacement y z)
    have hsq : PDE.vecEuclideanNorm (movingLensDisplacement y z) ^ 2 < kappa ^ 2 := by
      simpa only [PDE.vecEuclideanNorm_sq] using hdisp_sq
    nlinarith
  have hdnonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hrootnonneg : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hinv2nonneg : 0 ≤ kappa ^ (-2 : ℤ) := by positivity
  have hybound : PDE.vecEuclideanNorm y ≤ Real.sqrt d * kappa ^ (-2 : ℤ) := by
    apply vecEuclideanNorm_le_of_sq_le
    · positivity
    · have hsquare : (Real.sqrt d * kappa ^ (-2 : ℤ)) ^ 2 =
          (d : ℝ) * kappa ^ (-4 : ℤ) := by
        rw [mul_pow, Real.sq_sqrt hdnonneg]
        have hpow : (kappa ^ (-2 : ℤ)) ^ 2 = kappa ^ (-4 : ℤ) := by
          calc
            (kappa ^ (-2 : ℤ)) ^ 2 = kappa ^ ((-2 : ℤ) * 2) :=
              (zpow_mul kappa (-2) 2).symm
            _ = kappa ^ (-4 : ℤ) := by norm_num
        rw [hpow]
      rw [hsquare]
      exact hy
  have htime_norm : PDE.vecEuclideanNorm (z.1 • y) ≤
      Real.sqrt d * kappa ^ (-3 : ℤ) := by
    rw [PDE.vecEuclideanNorm_smul, abs_of_nonneg hz0]
    have hfirst : z.1 * PDE.vecEuclideanNorm y ≤
        z.1 * (Real.sqrt d * kappa ^ (-2 : ℤ)) :=
      mul_le_mul_of_nonneg_left hybound hz0
    calc
      z.1 * PDE.vecEuclideanNorm y ≤ z.1 * (Real.sqrt d * kappa ^ (-2 : ℤ)) := hfirst
      _ ≤ kappa⁻¹ * (Real.sqrt d * kappa ^ (-2 : ℤ)) :=
        mul_le_mul_of_nonneg_right (hztau.trans htau_kappa) (by positivity)
      _ = Real.sqrt d * kappa ^ (-3 : ℤ) := by
        field_simp [hkappa.ne']
  have hsplit : z.2 = movingLensDisplacement y z + z.1 • y := by
    rw [movingLensDisplacement]
    exact (sub_add_cancel _ _).symm
  rw [hsplit]
  calc
    PDE.vecEuclideanNorm (movingLensDisplacement y z + z.1 • y) ≤
        PDE.vecEuclideanNorm (movingLensDisplacement y z) +
          PDE.vecEuclideanNorm (z.1 • y) :=
      PDE.vecEuclideanNorm_add_le _ _
    _ < kappa + Real.sqrt d * kappa ^ (-3 : ℤ) :=
      add_lt_add_of_lt_of_le hdisp htime_norm

private theorem movingLensChartInv_mem_closed
    {d : ℕ} {xi eps tau : ℝ} {y : PDE.Vec d}
    (hxi : 0 ≤ xi) (heps : 0 < eps) {q : TimeVelocity d}
    (hq : q ∈ closedParabolicCylinder tau (0 : PDE.Vec d)) :
    movingLensChartInv xi eps y q ∈ movingLensClosed xi eps tau y := by
  have hqImage : q ∈ movingLensChart xi eps y '' movingLensClosed xi eps tau y := by
    rw [movingLensChart_image_closed hxi heps]
    exact hq
  rcases hqImage with ⟨z, hz, hzq⟩
  have hEq : movingLensChartInv xi eps y q = z := by
    rw [← hzq]
    exact movingLensChartInv_apply_movingLensChart hxi heps hz.1
  rwa [hEq]

section
variable {d : ℕ} {xi eps tau : ℝ} {y : PDE.Vec d} {z : TimeVelocity d} (hxi : 0 ≤ xi)
  (heps : 0 < eps) (hz : z ∈ movingLensClosed xi eps tau y)
include hxi heps hz

private theorem movingLensChart_path_mem_closed {s : ℝ}
    (hs : s ∈ Set.Icc 0 z.1) :
    movingLensChartInv xi eps y (s, (movingLensChart xi eps y z).2) ∈
      movingLensClosed xi eps tau y := by
  have hzTrunc : z ∈ movingLensClosed xi eps z.1 y := ⟨hz.1, le_rfl, hz.2.2⟩
  have hzChart : movingLensChart xi eps y z ∈
      closedParabolicCylinder z.1 (0 : PDE.Vec d) := by
    rw [← movingLensChart_image_closed hxi heps]
    exact ⟨z, hzTrunc, rfl⟩
  rw [mem_closedParabolicCylinder_iff] at hzChart
  have hpathTrunc : movingLensChartInv xi eps y
      (s, (movingLensChart xi eps y z).2) ∈ movingLensClosed xi eps z.1 y := by
    apply movingLensChartInv_mem_closed hxi heps
    rw [mem_closedParabolicCylinder_iff]
    exact ⟨hs.1, hs.2, hzChart.2.2⟩
  exact ⟨hpathTrunc.1, hpathTrunc.2.1.trans hz.2.1, hpathTrunc.2.2⟩

private theorem movingLensChart_path_initial_mem_causalBoundary :
    movingLensChartInv xi eps y (0, (movingLensChart xi eps y z).2) ∈
      movingLensClosed xi eps tau y \ movingLensActive xi eps tau y := by
  refine ⟨movingLensChart_path_mem_closed hxi heps hz ⟨le_rfl, hz.1⟩, ?_⟩
  intro hactive
  exact (ne_of_gt hactive.1) (by simp [movingLensChartInv])

end

end

end HypoellipticAleksandrov.Parabolic
namespace HypoellipticAleksandrov.Parabolic

noncomputable section

open Filter Set
open scoped Topology

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
  have hxi : 0 ≤ xi := by
    dsimp only [xi]
    exact movingLensSignXi_nonneg hkappa
  have hclosedCenter : (tau, tau • y) ∈ movingLensClosed xi eps tau y := by
    refine ⟨htau.le, le_rfl, ?_⟩
    rw [movingLensDisplacement, sub_self]
    simp only [PDE.vecNormSq, PDE.vecDot, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero]
    exact (movingLensDenominator_pos hxi heps htau.le).le
  have hR : 0 < movingLensVelocityFootprint d kappa := by
    unfold movingLensVelocityFootprint
    positivity
  have hell (z : TimeVelocity d) (hz : z ∈ movingLensClosed xi eps tau y) :
      0 < ell z.2 ∧ ell z.2 < M :=
    affineVelocity_bounds_of_wedge hM hR hhLower hhUpper hp (by simpa using
      (movingLensClosed_velocity_norm_lt_footprint hkappa htau_kappa heps_small hy hz).le)
  have hellPos : ∀ z ∈ movingLensClosed xi eps tau y, 0 < ell z.2 := fun z hz => (hell z hz).1
  have hgCenter : 0 < g (tau, tau • y) := by
    change 0 < u (tau, tau • y) - ell (tau • y)
    rw [← hMvalue]
    exact sub_pos.mpr (hell _ hclosedCenter).2
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
    have hSClosed : IsClosed S := by
      dsimp only [S]
      change IsClosed
        (movingLensClosed xi eps tau y ∩ g ⁻¹' Set.Ici 0)
      exact hgCont.preimage_isClosed_of_isClosed hLensCompact.isClosed isClosed_Ici
    exact hLensCompact.of_isClosed_subset hSClosed inter_subset_left
  rcases hSCompact.exists_isMinOn ⟨(tau, tau • y), hcenterS⟩
      continuous_fst.continuousOn with ⟨zc, hzcS, hzcMin⟩
  have hzcClosed : zc ∈ movingLensClosed xi eps tau y := hzcS.1
  have hzcNonneg : 0 ≤ g zc := hzcS.2
  have htcPos : 0 < zc.1 := by
    by_contra hnot
    have hzero : zc.1 = 0 := le_antisymm (not_lt.mp hnot) hzcClosed.1
    let path : ℝ → TimeVelocity d := fun s =>
      movingLensChartInv xi eps y (s, (movingLensChart xi eps y zc).2)
    have hpathZero : path 0 ∈ movingLensClosed xi eps tau y \
        movingLensActive xi eps tau y := by
      dsimp only [path]
      exact movingLensChart_path_initial_mem_causalBoundary hxi heps hzcClosed
    have hpathEq : path 0 = zc := by
      dsimp only [path]
      have hEq : (0, (movingLensChart xi eps y zc).2) =
          movingLensChart xi eps y zc := by
        apply Prod.ext
        · simpa [movingLensChart] using hzero.symm
        · rfl
      rw [hEq]
      simpa using movingLensChartInv_apply_movingLensChart hxi heps hzcClosed.1
    have hneg : g (path 0) < 0 := by
      have hbd := hboundary _ hpathZero
      have hpz := hellPos _ (hpathZero.1)
      change u (path 0) - ell (path 0).2 < 0
      linarith
    rw [hpathEq] at hneg
    linarith
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
        movingLensActive xi eps tau y := by
      dsimp only [path]
      exact movingLensChart_path_initial_mem_causalBoundary hxi heps hzcClosed
    have hgZero : g (path 0) < 0 := by
      have hbd := hboundary _ hpathZero
      have hpz := hellPos _ hpathZero.1
      change u (path 0) - ell (path 0).2 < 0
      linarith
    have hpathEnd : path zc.1 = zc := by
      dsimp only [path]
      exact movingLensChartInv_apply_movingLensChart hxi heps hzcClosed.1
    let f : ℝ → ℝ := fun s => g (path s)
    have hfCont : ContinuousOn f (Set.Icc 0 zc.1) := by
      have hcomp := hgCont.comp hpathCont.continuousOn (by
        intro s hs
        dsimp only [path]
        exact movingLensChart_path_mem_closed hxi heps hzcClosed hs)
      simpa only [f, Function.comp_def] using hcomp
    rcases zero_between_of_continuousOn_of_neg_pos htcPos hfCont
        (by simpa [f] using hgZero) (by simpa [f, hpathEnd] using hgcPos) with
      ⟨s, hs, hfs⟩
    have hsS : path s ∈ S := by
      refine ⟨?_, ?_⟩
      · dsimp only [path]
        exact movingLensChart_path_mem_closed hxi heps hzcClosed ⟨hs.1.le, hs.2.le⟩
      · simpa [f] using hfs.ge
    have hmin := hzcMin hsS
    change zc.1 ≤ s at hmin
    exact (not_lt_of_ge hmin) hs.2
  have htcLt : zc.1 < tau := by
    let zT : TimeVelocity d := (tau, tau • y)
    let path : ℝ → TimeVelocity d := fun s =>
      movingLensChartInv xi eps y (s, (movingLensChart xi eps y zT).2)
    have hpathCont : Continuous path := by
      dsimp only [path, movingLensChartInv]
      unfold movingLensDenominator
      fun_prop
    have hpathZero : path 0 ∈ movingLensClosed xi eps tau y \
        movingLensActive xi eps tau y := by
      dsimp only [path, zT]
      exact movingLensChart_path_initial_mem_causalBoundary hxi heps hclosedCenter
    have hgZero : g (path 0) < 0 := by
      have hbd := hboundary _ hpathZero
      have hpz := hellPos _ hpathZero.1
      change u (path 0) - ell (path 0).2 < 0
      linarith
    have hpathEnd : path tau = zT := by
      dsimp only [path]
      exact movingLensChartInv_apply_movingLensChart hxi heps hclosedCenter.1
    let f : ℝ → ℝ := fun s => g (path s)
    have hfCont : ContinuousOn f (Set.Icc 0 tau) := by
      have hcomp := hgCont.comp hpathCont.continuousOn (by
        intro s hs
        dsimp only [path, zT]
        exact movingLensChart_path_mem_closed hxi heps hclosedCenter hs)
      simpa only [f, Function.comp_def] using hcomp
    rcases zero_between_of_continuousOn_of_neg_pos htau hfCont
        (by simpa [f] using hgZero) (by simpa [f, hpathEnd, zT] using hgCenter) with
      ⟨s, hs, hfs⟩
    have hsS : path s ∈ S := by
      refine ⟨?_, ?_⟩
      · dsimp only [path, zT]
        exact movingLensChart_path_mem_closed hxi heps hclosedCenter ⟨hs.1.le, hs.2.le⟩
      · simpa [f] using hfs.ge
    have hmin := hzcMin hsS
    change zc.1 ≤ s at hmin
    exact hmin.trans_lt hs.2
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
        movingLensActive xi eps tau y := by
      dsimp only [path]
      exact movingLensChart_path_initial_mem_causalBoundary hxi heps hv
    have hgZero : g (path 0) < 0 := by
      have hbd := hboundary _ hpathZero
      have hpz := hellPos _ hpathZero.1
      change u (path 0) - ell (path 0).2 < 0
      linarith
    have hpathEnd : path zc.1 = zv := by
      dsimp only [path, zv]
      exact movingLensChartInv_apply_movingLensChart hxi heps hv.1
    let f : ℝ → ℝ := fun s => g (path s)
    have hfCont : ContinuousOn f (Set.Icc 0 zc.1) := by
      have hcomp := hgCont.comp hpathCont.continuousOn (by
        intro s hs
        dsimp only [path, zv]
        exact movingLensChart_path_mem_closed hxi heps hv hs)
      simpa only [f, Function.comp_def] using hcomp
    rcases zero_between_of_continuousOn_of_neg_pos htcPos hfCont
        (by simpa [f] using hgZero) (by simpa [f, hpathEnd, zv] using hpos) with
      ⟨s, hs, hfs⟩
    have hsS : path s ∈ S := by
      refine ⟨?_, ?_⟩
      · dsimp only [path, zv]
        exact movingLensChart_path_mem_closed hxi heps hv ⟨hs.1.le, hs.2.le⟩
      · simpa [f] using hfs.ge
    have hmin := hzcMin hsS
    change zc.1 ≤ s at hmin
    exact (not_lt_of_ge hmin) hs.2
  have hzcSpatial : PDE.vecNormSq (movingLensDisplacement y zc) <
      movingLensDenominator xi eps zc.1 := by
    by_contra hnot
    have heq : PDE.vecNormSq (movingLensDisplacement y zc) =
        movingLensDenominator xi eps zc.1 := le_antisymm hzcClosed.2.2 (not_lt.mp hnot)
    have hbd : u zc ≤ 0 := hboundary zc (by
      rw [mem_movingLensClosed_diff_active_iff]
      exact Or.inr ⟨hzcClosed.1, hzcClosed.2.1, heq⟩)
    have hpz := hellPos zc hzcClosed
    change u zc - ell zc.2 = 0 at hgcZero
    linarith
  have hzcActive : zc ∈ movingLensActive xi eps tau y :=
    ⟨htcPos, hzcClosed.2.1, hzcSpatial⟩
  have huz : ContDiffAt ℝ 2 u zc := hulocal zc hzcActive
  have huzcPos : 0 < u zc := by
    have hpz := hellPos zc hzcClosed
    change u zc - ell zc.2 = 0 at hgcZero
    linarith
  have hspatialLocalMax : IsLocalMax
      (fun v : PDE.Vec d => u (zc.1, v) - ell v) zc.2 := by
    rw [IsLocalMax]
    have hopen : {v : PDE.Vec d | PDE.vecNormSq
        (movingLensDisplacement y (zc.1, v)) < movingLensDenominator xi eps zc.1} ∈
        𝓝 zc.2 := by
      exact (isOpen_movingLensSpatialStrict xi eps y).preimage
        (continuous_const.prodMk continuous_id) |>.mem_nhds hzcSpatial
    filter_upwards [hopen] with v hv
    have hvClosed : (zc.1, v) ∈ movingLensClosed xi eps tau y :=
      ⟨htcPos.le, hzcClosed.2.1, hv.le⟩
    change g (zc.1, v) ≤ g zc
    rw [hgcZero]
    exact hspatialNonpos v hvClosed
  have hhess : (-velocityHessian u zc).PosSemidef :=
    neg_velocityHessian_posSemidef_of_spatial_localMax_affineContact_of_contDiffAt huz hspatialLocalMax
  have htimeMax : IsLocalMaxOn
      (fun t : ℝ => u (t, zc.2) - ell zc.2) (Set.Iic zc.1) zc.1 := by
    rw [IsLocalMaxOn]
    have hpast := movingLensActive_mem_nhdsWithin_past hzcActive
    have hlineTendsto : Tendsto (fun t : ℝ => (t, zc.2))
        (𝓝[Set.Iic zc.1] zc.1) (𝓝[Set.Iic zc.1 ×ˢ Set.univ] zc) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_nhdsWithin_of_tendsto_nhds
        ((continuous_id.prodMk continuous_const).continuousAt.tendsto), ?_⟩
      filter_upwards [eventually_mem_nhdsWithin] with t ht
      exact ⟨ht, mem_univ _⟩
    have hactiveEventually : ∀ᶠ t in 𝓝[Set.Iic zc.1] zc.1,
        (t, zc.2) ∈ movingLensActive xi eps tau y := hlineTendsto.eventually hpast
    filter_upwards [hactiveEventually, eventually_mem_nhdsWithin] with t ht hle
    change g (t, zc.2) ≤ g zc
    rw [hgcZero]
    exact nonpos_at_or_before_firstContact hzcMin hgcZero hle
      (movingLensActive_subset_movingLensClosed xi eps tau y ht)
  have hdu := huz.differentiableAt (by norm_num)
  exact ⟨zc, ⟨htcPos, htcLt, hzcSpatial, huzcPos, timeDerivative_nonneg_of_localMaxOn_past hdu htimeMax, hhess⟩,
    parabolicNormalMap_eq_of_affineContact hdu (sub_eq_zero.mp hgcZero) hspatialLocalMax⟩

end

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

theorem measurable_movingLensSourceSignSet_of_localC2
    {d : ℕ} {xi eps tau : ℝ} {y : PDE.Vec d} {u : TimeVelocity d → ℝ}
    (hlocal : ∀ z ∈ movingLensActive xi eps tau y, ContDiffAt ℝ 2 u z) :
    MeasurableSet (movingLensSourceSignSet xi eps tau y u) := by
  let O := {z : TimeVelocity d | 0 < z.1 ∧
    PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1} ∩
    (Prod.fst ⁻¹' Set.Iio tau)
  have hO : IsOpen O := (isOpen_movingLensPositiveSpatialStrict xi eps y).inter
    (isOpen_Iio.preimage continuous_fst)
  have hu : ContDiffOn ℝ 2 u O := fun z hz =>
    (hlocal z ⟨hz.1.1, hz.2.le, hz.1.2⟩).contDiffWithinAt
  have hD := hu.fderiv_of_isOpen (m := 1) hO (by norm_num)
  have hD₂ := hD.fderiv_of_isOpen (m := 0) hO (by norm_num)
  have ht : ContinuousOn (timeDerivative u) O := hD.continuousOn.clm_apply continuousOn_const
  have hH : ContinuousOn (velocityHessian u) O :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j =>
      (hD₂.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hpos := (hu.continuousOn.isOpen_inter_preimage hO (isOpen_Ioi (a := (0 : ℝ)))).measurableSet
  have hneg := (ht.isOpen_inter_preimage hO (isOpen_Iio (a := (0 : ℝ)))).measurableSet
  have hpsd : IsClosed {M : PDE.Mat d | M.PosSemidef} := Matrix.posSemidef_is_closed
  have hnpsd := (hH.neg.isOpen_inter_preimage hO hpsd.isOpen_compl).measurableSet
  convert (hpos.diff (hneg.union hnpsd)) using 1
  ext z
  simp only [O, movingLensSourceSignSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_Ioi, Set.mem_Iio, Set.mem_diff, Set.mem_union, Set.mem_compl_iff, Pi.neg_apply, ← not_lt]
  tauto

/-- Concrete physical contact/area API for supplied-source lower-bound proof: wedge-volume bound. -/
theorem movingLensSlopeInterceptWedge_volume_le_lintegral_abs_det_fderiv
    {d : Nat} {xi eps tau M R : Real} {y : PDE.Vec d}
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
    MeasureTheory.MeasureSpace.volume (movingLensSlopeInterceptWedge d R M) ≤
        MeasureTheory.MeasureSpace.volume
          (parabolicNormalMap u 0 '' movingLensSourceSignSet xi eps tau y u) :=
      MeasureTheory.measure_mono hcoverage
    _ ≤ ∫⁻ z in movingLensSourceSignSet xi eps tau y u,
        ENNReal.ofReal |((fderiv Real (parabolicNormalMap u 0) z).det)|
          ∂MeasureTheory.MeasureSpace.volume :=
      MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv
        MeasureTheory.MeasureSpace.volume
        (measurable_movingLensSourceSignSet_of_localC2 hlocal)
        (by
          intro z hz
          have hderiv := parabolicNormalMap_hasFDerivAt_of_contDiffAt (y₀ := 0)
            (hlocal z ⟨hz.1, hz.2.1.le, hz.2.2.1⟩)
          rw [hderiv.fderiv]
          exact hderiv.hasFDerivWithinAt)

/-- Concrete physical contact/area API for supplied-source lower-bound proof: wedge volume. -/
theorem volume_movingLensSlopeInterceptWedge
    {d : Nat} {R M : Real} (hR : 0 < R) (hM : 0 < M) :
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
    PDE.volume_euclideanBall_eq_unit_mul_of_pos (0 : PDE.Vec d) hradius]

end HypoellipticAleksandrov.Parabolic
