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
import Aesop
import HypoellipticAleksandrov.Parabolic.ForwardPropagationGeometry
import Lean.Elab.Tactic.Grind



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
    (u : TimeVelocity d → ℝ) : HypoellipticAleksandrov.Parabolic.Region d :=
  {z | 0 < z.1 ∧ z.1 < tau ∧
    PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1 ∧
    0 < u z ∧ 0 ≤ timeDerivative u z ∧ (-velocityHessian u z).PosSemidef}

variable (d : ℕ)

/-- Concrete physical contact/area API for supplied-source lower-bound proof: velocity footprint. -/
def movingLensVelocityFootprint  (kappa : ℝ) : ℝ :=
  kappa + Real.sqrt d * kappa ^ (-3 : ℤ)

/-- Concrete physical contact/area API for supplied-source lower-bound proof: its wedge. -/
def movingLensSlopeInterceptWedge  (R M : ℝ) : HypoellipticAleksandrov.Parabolic.Region d :=
  Set.Ioo (M / 2) (3 * M / 4) ×ˢ
    PDE.euclideanBall (0 : PDE.Vec d) (M / (4 * R))

private theorem movingLensSignXi_nonneg {kappa : ℝ} (hkappa : 0 < kappa) :
    0 ≤ movingLensSignXi kappa := by
  unfold movingLensSignXi
  positivity



variable {d : ℕ}

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
      add_lt_add_of_lt_of_le (by
          have hnonneg := PDE.vecEuclideanNorm_nonneg (movingLensDisplacement y z)
          have hsq : PDE.vecEuclideanNorm (movingLensDisplacement y z) ^ 2 < kappa ^ 2 := by
            simpa only [PDE.vecEuclideanNorm_sq] using (hzspatial.trans_lt (movingLensDenominator_lt_kappa_sq hkappa heps_small hztau htau_kappa))
          nlinarith) (by
          rw [PDE.vecEuclideanNorm_smul, abs_of_nonneg hz0]

          calc
            z.1 * PDE.vecEuclideanNorm y ≤ z.1 * (Real.sqrt d * kappa ^ (-2 : ℤ)) := (mul_le_mul_of_nonneg_left (by
                apply vecEuclideanNorm_le_of_sq_le
                · positivity
                · have hsquare : (Real.sqrt d * kappa ^ (-2 : ℤ)) ^ 2 =
                      (d : ℝ) * kappa ^ (-4 : ℤ) := by
                    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
                    have hpow : (kappa ^ (-2 : ℤ)) ^ 2 = kappa ^ (-4 : ℤ) := by
                      calc
                        (kappa ^ (-2 : ℤ)) ^ 2 = kappa ^ ((-2 : ℤ) * 2) :=
                          (zpow_mul kappa (-2) 2).symm
                        _ = kappa ^ (-4 : ℤ) := by norm_num
                    rw [hpow]
                  rw [hsquare]
                  exact hy) hz0)
            _ ≤ kappa⁻¹ * (Real.sqrt d * kappa ^ (-2 : ℤ)) :=
              mul_le_mul_of_nonneg_right (hztau.trans htau_kappa) (by positivity)
            _ = Real.sqrt d * kappa ^ (-3 : ℤ) := by
              field_simp [hkappa.ne'])

section
variable {kappa tau eps M h : ℝ} {y p : PDE.Vec d} (hkappa : 0 < kappa) (htau_kappa : tau ≤ kappa⁻¹) (heps_small : 2 * eps ^ 2 < kappa ^ 2) (hy : PDE.vecNormSq y ≤ (d : ℝ) * kappa ^ (-4 : ℤ)) (hM : 0 < M)

include hkappa htau_kappa heps_small hy hM
private theorem affineVelocity_pos_on_movingLens
      (hh : M / 2 < h)
    (hp : p ∈ PDE.euclideanBall (0 : PDE.Vec d)
      (M / (4 * movingLensVelocityFootprint d kappa)))
    {z : TimeVelocity d}
    (hz : z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y) :
    0 < affineVelocity 0 h p z.2 := by
  have hR : 0 < movingLensVelocityFootprint d kappa := by
    unfold movingLensVelocityFootprint
    positivity



  have hdot : -(M / 4) < PDE.vecDot p z.2 := by
    nlinarith [neg_abs_le (PDE.vecDot p z.2),
      (PDE.abs_vecDot_le_vecEuclideanNorm_mul p z.2).trans_lt (by
          calc
            PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm z.2 ≤
                PDE.vecEuclideanNorm p * movingLensVelocityFootprint d kappa :=
              mul_le_mul_of_nonneg_left (movingLensClosed_velocity_norm_lt_footprint hkappa htau_kappa heps_small hy hz).le (PDE.vecEuclideanNorm_nonneg p)
            _ < (M / (4 * movingLensVelocityFootprint d kappa)) *
                movingLensVelocityFootprint d kappa :=
              mul_lt_mul_of_pos_right (by
                  simpa using (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
                    (x₀ := (0 : PDE.Vec d)) (x := p)
                    (R := M / (4 * movingLensVelocityFootprint d kappa)) (by positivity)).mp hp) hR
            _ = M / 4 := by field_simp [hR.ne'])]
  rw [affineVelocity_apply]
  simp only [sub_zero]
  linarith

private theorem affineVelocity_lt_on_movingLens
      (hh : h < 3 * M / 4)
    (hp : p ∈ PDE.euclideanBall (0 : PDE.Vec d)
      (M / (4 * movingLensVelocityFootprint d kappa)))
    {z : TimeVelocity d}
    (hz : z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y) :
    affineVelocity 0 h p z.2 < M := by
  have hR : 0 < movingLensVelocityFootprint d kappa := by
    unfold movingLensVelocityFootprint
    positivity



  have hdot : PDE.vecDot p z.2 < M / 4 :=
    lt_of_le_of_lt (le_abs_self _) ((PDE.abs_vecDot_le_vecEuclideanNorm_mul p z.2).trans_lt (by
        calc
          PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm z.2 ≤
              PDE.vecEuclideanNorm p * movingLensVelocityFootprint d kappa :=
            mul_le_mul_of_nonneg_left (movingLensClosed_velocity_norm_lt_footprint hkappa htau_kappa heps_small hy hz).le (PDE.vecEuclideanNorm_nonneg p)
          _ < (M / (4 * movingLensVelocityFootprint d kappa)) *
              movingLensVelocityFootprint d kappa :=
            mul_lt_mul_of_pos_right (by
                simpa using (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
                  (x₀ := (0 : PDE.Vec d)) (x := p)
                  (R := M / (4 * movingLensVelocityFootprint d kappa)) (by positivity)).mp hp) hR
          _ = M / 4 := by field_simp [hR.ne']))
  rw [affineVelocity_apply]
  simp only [sub_zero]
  linarith
end


private theorem movingLensChartInv_mem_closed
     {xi eps tau : ℝ} {y : PDE.Vec d}
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
        (v + r • ((Pi.single i (1 )) : PDE.Vec d)))
      (p i) 0 := by
  let sharedTerm_17948867c0 := (h + (∑ x, p x * v x))
  let e : PDE.Vec d := Pi.single i 1
  change HasDerivAt (fun r : ℝ => affineVelocity 0 h p (v + r • e)) (p i) 0
  have hfun :
      (fun r : ℝ => affineVelocity 0 h p (v + r • e)) =
        fun r => affineVelocity 0 h p v + r * p i := by
    classical
    funext r
    have hsingle : (∑ x : Fin d, p x * r * e x) = r * p i := by
      dsimp [e]
      rw [Fintype.sum_eq_single i]
      · simp
        ring
      · intro x hxi
        simp [hxi]
    unfold affineVelocity PDE.vecDot
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul,
      sub_zero]
    have hsplit :
        h + (∑ x, p x * (v x + r * e x)) =
          sharedTerm_17948867c0 + (∑ x, p x * r * e x) := by
      calc
        h + (∑ x, p x * (v x + r * e x)) =
            h + (∑ x, (p x * v x + p x * r * e x)) := by
              grind
        _ = sharedTerm_17948867c0 + (∑ x, p x * r * e x) := by
              rw [Finset.sum_add_distrib]
              ring
    rw [hsplit, hsingle]
  rw [hfun]
  simpa only [one_mul] using
    ((hasDerivAt_id' (𝕜 := ℝ) 0).mul_const (p i)).const_add
      (affineVelocity 0 h p v)

variable {xi eps tau : ℝ} {y : PDE.Vec d} {z : TimeVelocity d} (hxi : 0 ≤ xi) (heps : 0 < eps) (hz : z ∈ movingLensClosed xi eps tau y)

include hxi heps hz
private theorem movingLensChart_path_mem_closed
      {s : ℝ}
    (hs : s ∈ Set.Icc 0 z.1) :
    movingLensChartInv xi eps y (s, (movingLensChart xi eps y z).2) ∈
      movingLensClosed xi eps tau y := by

  have hzChart : movingLensChart xi eps y z ∈
      closedParabolicCylinder z.1 (0 : PDE.Vec d) := by
    rw [← movingLensChart_image_closed hxi heps]
    exact ⟨z, (⟨hz.1, le_rfl, hz.2.2⟩), rfl⟩
  rw [mem_closedParabolicCylinder_iff] at hzChart
  have hpathTrunc : movingLensChartInv xi eps y
      (s, (movingLensChart xi eps y z).2) ∈ movingLensClosed xi eps z.1 y := by
    apply movingLensChartInv_mem_closed hxi heps
    rw [mem_closedParabolicCylinder_iff]
    exact ⟨hs.1, hs.2, hzChart.2.2⟩
  exact ⟨hpathTrunc.1, hpathTrunc.2.1.trans hz.2.1, hpathTrunc.2.2⟩

private theorem movingLensChart_path_initial_mem_causalBoundary
      :
    movingLensChartInv xi eps y (0, (movingLensChart xi eps y z).2) ∈
      movingLensClosed xi eps tau y \ movingLensActive xi eps tau y := by
  refine ⟨movingLensChart_path_mem_closed hxi heps hz ⟨le_rfl, hz.1⟩, ?_⟩
  intro hactive
  exact (ne_of_gt hactive.1) (rfl)

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

  rcases intermediate_value_Icc hab.le hf (⟨hfa.le, hfb.le⟩) with ⟨c, hc, hfc⟩
  refine ⟨c, ?_, hfc⟩
  constructor
  · grind
  · grind

section
variable {d : ℕ} {u : TimeVelocity d → ℝ} {z : TimeVelocity d} (hu : ContDiffAt ℝ 2 u z)

include hu
private theorem time_slice_hasDerivAt_of_contDiffAt_local
     :
    HasDerivAt (fun t  => u (t, z.2)) (timeDerivative u z) z.1 := by

  simpa only [timeDerivative, Function.comp_def] using
    hu.differentiableAt (by norm_num) |>.hasFDerivAt.comp_hasDerivAt z.1 (HasDerivAt.prodMk (hasDerivAt_id'  z.1)
          (hasDerivAt_const (x := z.1) (c := z.2)))

private theorem velocity_slice_hasDerivAt_of_contDiffAt_local
     (i : Fin d) :
    HasDerivAt
      (fun r : ℝ => u (z.1,
        z.2 + r • ((Pi.single i (1 )) : PDE.Vec d)))
      (velocityGradient u z i) 0 := by
  let e : PDE.Vec d := Pi.single i 1


  have huAt : HasFDerivAt u (fderiv ℝ u z)
      (z.1, z.2 + (0 : ℝ) • e) := by
    simpa only [zero_smul, add_zero] using
      (hu.differentiableAt (by norm_num)).hasFDerivAt
  have hcomp := huAt.comp_hasDerivAt 0 ((hasDerivAt_const (x := (0 : ℝ)) (c := z.1)).prodMk (show HasDerivAt (fun r : ℝ => z.2 + r • e) e 0 by
      simpa only [one_smul] using
        ((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const e).const_add z.2))
  assumption
end


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
  let ell  := affineVelocity 0 h p
  let g  := fun z => u z - ell z.2
  have hxi : 0 ≤ xi := by
    dsimp only [xi]
    exact movingLensSignXi_nonneg hkappa
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
    change 0 < u (tau, tau • y) - ell (tau • y)
    rw [← hMvalue]
    exact sub_pos.mpr (hellLt _ hclosedCenter)
  have hgCont : ContinuousOn g (movingLensClosed xi eps tau y) := by
    have hellCont : Continuous (fun z : TimeVelocity d => ell z.2) := by
      unfold ell affineVelocity PDE.vecDot
      fun_prop
    exact hucont.sub hellCont.continuousOn
  let S  :=
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
  rcases hSCompact.exists_isMinOn ⟨_, hcenterS⟩
      continuous_fst.continuousOn with ⟨zc, hzcS, hzcMin⟩
  have hzcClosed  := hzcS.1
  have hzcNonneg : 0 ≤ g zc := hzcS.2
  have htcPos : 0 < zc.1 := by
    by_contra hnot
    have hzero  := le_antisymm (not_lt.mp hnot) hzcClosed.1
    let path  := fun s =>
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
        · exact hzero.symm
        · rfl
      rw [hEq]
      exact movingLensChartInv_apply_movingLensChart hxi heps hzcClosed.1
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
    let path  := fun s =>
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
    let f  := fun s => g (path s)
    have hfCont : ContinuousOn f (Set.Icc 0 zc.1) := by
      have hcomp := hgCont.comp hpathCont.continuousOn (by
        intro s hs
        dsimp only [path]
        exact movingLensChart_path_mem_closed hxi heps hzcClosed hs)
      exact hcomp
    rcases zero_between_of_continuousOn_of_neg_pos_local htcPos hfCont
        (hgZero) (by simpa [f, hpathEnd] using hgcPos) with
      ⟨s, hs, hfs⟩
    have hsS : path s ∈ S := by
      refine ⟨?_, ?_⟩
      · dsimp only [path]
        exact movingLensChart_path_mem_closed hxi heps hzcClosed ⟨hs.1.le, hs.2.le⟩
      · exact hfs.ge
    have hmin := hzcMin hsS
    change zc.1 ≤ s at hmin
    exact (not_lt_of_ge hmin) hs.2
  have htcLt : zc.1 < tau := by
    let zT : TimeVelocity d := (tau, tau • y)
    let path  := fun s =>
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
    let f  := fun s => g (path s)

    rcases zero_between_of_continuousOn_of_neg_pos_local htau (by
        have hcomp := hgCont.comp hpathCont.continuousOn ((fun ⦃s⦄ hs => id (movingLensChart_path_mem_closed hxi heps hclosedCenter hs)))
        exact hcomp)
        (hgZero) (by simpa [f, hpathEnd, zT] using hgCenter) with
      ⟨s, hs, hfs⟩

    have hmin := hzcMin (show path s ∈ S by
        refine ⟨?_, ?_⟩
        · dsimp only [path, zT]
          exact movingLensChart_path_mem_closed hxi heps hclosedCenter ⟨hs.1.le, hs.2.le⟩
        · exact hfs.ge)
    change zc.1 ≤ s at hmin
    exact hmin.trans_lt hs.2

  have hzcSpatial : PDE.vecNormSq (movingLensDisplacement y zc) <
      movingLensDenominator xi eps zc.1 := by
    by_contra hnot
    have heq  := le_antisymm hzcClosed.2.2 (not_lt.mp hnot)
    have hbd  := hboundary zc (by
      rw [mem_movingLensClosed_diff_active_iff]
      exact Or.inr ⟨hzcClosed.1, hzcClosed.2.1, heq⟩)
    have hpz := hellPos zc hzcClosed
    change u zc - ell zc.2 = 0 at hgcZero
    linarith
  have hzcActive : zc ∈ movingLensActive xi eps tau y :=
    ⟨htcPos, hzcClosed.2.1, hzcSpatial⟩
  have huz  := hulocal zc hzcActive

  have hspatialLocalMax : IsLocalMax
      (fun v  => u (zc.1, v) - ell v) zc.2 := by
    rw [IsLocalMax]
    have hopen : {v : PDE.Vec d | PDE.vecNormSq
        (movingLensDisplacement y (zc.1, v)) < movingLensDenominator xi eps zc.1} ∈
        𝓝 zc.2 := (isOpen_movingLensSpatialStrict xi eps y).preimage
        (continuous_const.prodMk continuous_id) |>.mem_nhds hzcSpatial
    filter_upwards [hopen] with v hv
    have hvClosed : (zc.1, v) ∈ movingLensClosed xi eps tau y :=
      ⟨htcPos.le, hzcClosed.2.1, hv.le⟩
    change g (zc.1, v) ≤ g zc
    rw [hgcZero]
    exact (show ∀ v : PDE.Vec d,
      (zc.1, v) ∈ movingLensClosed xi eps tau y → g (zc.1, v) ≤ 0 by
        intro v hv
        by_contra hnot
        have hpos : 0 < g (zc.1, v) := lt_of_not_ge hnot
        let zv : TimeVelocity d := (zc.1, v)
        let path  := fun s =>
          movingLensChartInv xi eps y (s, (movingLensChart xi eps y zv).2)
        have hpathCont : Continuous path := by
          dsimp only [path, movingLensChartInv]
          unfold movingLensDenominator
          fun_prop
        have hpathZero : path 0 ∈ movingLensClosed xi eps tau y \
            movingLensActive xi eps tau y := by
          dsimp only [path]
          exact movingLensChart_path_initial_mem_causalBoundary hxi heps hv

        have hpathEnd : path zc.1 = zv := by
          dsimp only [path, zv]
          exact movingLensChartInv_apply_movingLensChart hxi heps hv.1
        let f  := fun s => g (path s)

        rcases zero_between_of_continuousOn_of_neg_pos_local htcPos (show ContinuousOn f (Set.Icc 0 zc.1) by
            have hcomp := hgCont.comp hpathCont.continuousOn ((fun ⦃s⦄ hs => id (movingLensChart_path_mem_closed hxi heps hv hs)))
            exact hcomp)
            ((show g (path 0) < 0 by
                have hbd := hboundary _ hpathZero
                have hpz := hellPos _ hpathZero.1
                change u (path 0) - ell (path 0).2 < 0
                linarith)) (by simpa [f, hpathEnd, zv] using hpos) with
          ⟨s, hs, hfs⟩

        have hmin := hzcMin (show path s ∈ S by
            refine ⟨?_, ?_⟩
            · dsimp only [path, zv]
              exact movingLensChart_path_mem_closed hxi heps hv ⟨hs.1.le, hs.2.le⟩
            · exact hfs.ge)
        change zc.1 ≤ s at hmin
        exact (not_lt_of_ge hmin) hs.2) v hvClosed
  have hgrad : velocityGradient u zc = p := by
    ext i
    let q : PDE.Vec d := Pi.single i 1
    let line : ℝ → PDE.Vec d := fun r => zc.2 + r • q


    have hderiv : HasDerivAt
        (fun r : ℝ => u (zc.1,
          zc.2 + r • ((Pi.single i (1 )) : PDE.Vec d)) -
          ell (zc.2 + r • ((Pi.single i (1 )) : PDE.Vec d)))
        (velocityGradient u zc i - p i) 0 :=
      (velocity_slice_hasDerivAt_of_contDiffAt_local huz i).sub
        (affineVelocity_line_deriv_at_zero h p zc.2 i)
    have hzero := (show IsLocalMax
        (fun r  => u (zc.1, line r) - ell (line r)) 0 by

        exact (show IsLocalMax
            (fun v  => u (zc.1, v) - ell v) (line 0) by
            simpa [line, q] using hspatialLocalMax).comp_continuous (show ContinuousAt line 0 from (((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const q).const_add zc.2).continuousAt)).hasDerivAt_eq_zero ((id hderiv))
    exact sub_eq_zero.mp (hzero)

  have hhess  :=
    neg_velocityHessian_posSemidef_of_spatial_localMax_affineContact_of_contDiffAt huz (show IsLocalMax
      (fun v  => u (zc.1, v) -
        (u zc + PDE.vecDot p (v - zc.2))) zc.2 by
        have hrewrite :
            (fun v  => u (zc.1, v) - ell v) =
              fun v  => u (zc.1, v) -
                (u zc + PDE.vecDot p (v - zc.2)) := by
          funext v
          dsimp only [ell]
          simp only [affineVelocity_apply, sub_zero]
          have hgcZero' := hgcZero
          dsimp only [g, ell] at hgcZero'
          change u zc - affineVelocity 0 h p zc.2 = 0 at hgcZero'
          simp only [affineVelocity_apply, sub_zero] at hgcZero'
          unfold PDE.vecDot at hgcZero' ⊢
          have hsum : (∑ x, p x * v x) =
              (∑ x, p x * zc.2 x) + ∑ x, p x * (v - zc.2) x := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro x hx
            simp only [Pi.sub_apply]
            ring
          rw [hsum]
          linarith
        rw [← hrewrite]
        exact hspatialLocalMax)

  have htimeDeriv : HasDerivAt
      (fun t  => u (t, zc.2) - ell zc.2) (timeDerivative u zc) zc.1 :=
    (time_slice_hasDerivAt_of_contDiffAt_local huz).sub_const (ell zc.2)


  refine ⟨zc, ?_, ?_⟩
  · exact ⟨htcPos, htcLt, hzcSpatial, (show 0 < u zc by
      have hpz := hellPos zc hzcClosed
      change u zc - ell zc.2 = 0 at hgcZero
      linarith), (show _ by
      have hnonpos := (show IsLocalMaxOn
      (fun t  => u (t, zc.2) - ell zc.2) (Set.Iic zc.1) zc.1 by
          rw [IsLocalMaxOn]
          have hpast := movingLensActive_mem_nhdsWithin_past hzcActive
          have hlineTendsto : Tendsto (fun t : ℝ => (t, zc.2))
              (𝓝[Set.Iic zc.1] zc.1) (𝓝[Set.Iic zc.1 ×ˢ Set.univ] zc) := by
            rw [tendsto_nhdsWithin_iff]
            refine ⟨tendsto_nhdsWithin_of_tendsto_nhds
              ((continuous_id.prodMk continuous_const).continuousAt.tendsto), ?_⟩
            filter_upwards [eventually_mem_nhdsWithin] with t ht
            exact ⟨ht, mem_univ _⟩

          filter_upwards [(show ∀ᶠ t in 𝓝[Set.Iic zc.1] zc.1,
              (t, zc.2) ∈ movingLensActive xi eps tau y from hlineTendsto.eventually hpast), eventually_mem_nhdsWithin] with t ht hle

          change u (t, zc.2) - ell zc.2 ≤ u zc - ell zc.2
          change g (t, zc.2) ≤ g zc
          rw [hgcZero]
          exact (show g (t, zc.2) ≤ 0 by
              by_contra hnot
              have hpos : 0 < g (t, zc.2) := lt_of_not_ge hnot
              have htS : (t, zc.2) ∈ S :=
                ⟨movingLensActive_subset_movingLensClosed xi eps tau y ht, hpos.le⟩
              have hmin := hzcMin htS
              change zc.1 ≤ t at hmin
              have hne : zc.1 ≠ t := by
                intro heq
                subst t
                linarith [hgcZero]
              have hlt : zc.1 < t := lt_of_le_of_ne hmin hne
              exact (not_lt_of_ge hle) hlt)).hasFDerivWithinAt_nonpos htimeDeriv.hasDerivWithinAt (by

          simpa using sub_mem_posTangentConeAt_of_segment_subset (show segment ℝ zc.1 (zc.1 - 1) ⊆ Set.Iic zc.1 by
              intro s hs
              rw [segment_symm] at hs
              exact (segment_subset_Icc (sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)) hs).2))
      have hneg : -timeDerivative u zc ≤ 0 := by simpa using hnonpos
      linarith), hhess⟩
  · rw [parabolicNormalMap_apply]
    apply Prod.ext
    · change u zc - PDE.vecDot (velocityGradient u zc) (zc.2 - 0) = h
      simp only [sub_zero]
      rw [hgrad]
      dsimp only [g, ell] at hgcZero
      change u zc - affineVelocity 0 h p zc.2 = 0 at hgcZero
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
  let sharedTerm_bce399468d := ({z | (-velocityHessian u z).PosSemidef})
  let O  := {z | 0 < z.1 /\ z.1 < tau /\
    PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1}
  have hO : IsOpen O := by
    rw [show O = {z | 0 < z.1 /\
        PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1} ∩
          {z | z.1 < tau} by
      ext z
      change (0 < z.1 /\ z.1 < tau /\
        PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1) ↔
        ((0 < z.1 /\
          PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1) /\
          z.1 < tau)
      constructor
      · rintro ⟨ht0, httau, hspatial⟩
        exact ⟨⟨ht0, hspatial⟩, httau⟩
      · grind]
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


  have hnonnegative : MeasurableSet (O ∩ {z | 0 ≤ timeDerivative u z}) := by
    rw [show O ∩ {z | 0 ≤ timeDerivative u z} =
        O \ (O ∩ (timeDerivative u) ⁻¹' Set.Iio 0) by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_preimage, Set.mem_setOf_eq,
        Set.mem_Iio]
      constructor
      · rintro ⟨hz, htimez⟩
        exact ⟨hz, fun hnegative => not_lt_of_ge htimez hnegative.2⟩
      · rintro ⟨hz, hnotnegative⟩
        exact ⟨hz, le_of_not_gt fun hnegative => hnotnegative ⟨hz, hnegative⟩⟩]
    exact hO.measurableSet.diff
      (htime.isOpen_inter_preimage hO isOpen_Iio).measurableSet
  have hpsd : MeasurableSet (O ∩ sharedTerm_bce399468d) := by
    rw [show O ∩ sharedTerm_bce399468d = O \ (O ∩
        (fun z => -velocityHessian u z) ⁻¹' {H : PDE.Mat d | H.PosSemidef}ᶜ) by
      ext z
      simp [sharedTerm_bce399468d]]
    exact hO.measurableSet.diff
      ((hhess.neg).isOpen_inter_preimage hO (show IsClosed {H : PDE.Mat d | H.PosSemidef} by

          have hset :
              {H : PDE.Mat d | H.PosSemidef} =
                {H : PDE.Mat d | H.IsHermitian} ∩
                  ⋂ q : PDE.Vec d, {H : PDE.Mat d | 0 ≤ dotProduct q (H.mulVec q)} := by
            ext H
            simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
            simpa using (Matrix.posSemidef_iff_dotProduct_mulVec (M := H))
          rw [hset]
          refine (show IsClosed {H : PDE.Mat d | H.IsHermitian} by
              have hset :
                  {H : PDE.Mat d | H.IsHermitian} =
                    ⋂ i : Fin d, ⋂ j : Fin d, {H : PDE.Mat d | H j i = H i j} := by
                ext H
                simp only [Set.mem_setOf_eq, Set.mem_iInter]
                constructor
                · intro h i j
                  exact h.apply i j
                · intro h
                  apply Matrix.IsHermitian.ext
                  intro i j
                  exact h i j
              rw [hset]
              refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
              exact isClosed_eq (continuous_id.matrix_elem j i) (continuous_id.matrix_elem i j)).inter (isClosed_iInter fun q => ?_)

          exact isClosed_le continuous_const (show Continuous (fun H : PDE.Mat d => dotProduct q (H.mulVec q)) from continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))).isOpen_compl).measurableSet

  refine ⟨(by
      rw [show movingLensSourceSignSet xi eps tau y u =
          (O ∩ {z | 0 < u z}) ∩ (O ∩ {z | 0 ≤ timeDerivative u z}) ∩
            (O ∩ sharedTerm_bce399468d) by
        ext z
        change (0 < z.1 /\ z.1 < tau /\
          PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1 /\
          0 < u z /\ 0 ≤ timeDerivative u z /\ (-velocityHessian u z).PosSemidef) ↔
          ((z ∈ O /\ 0 < u z) /\ (z ∈ O /\ 0 ≤ timeDerivative u z)) /\
            (z ∈ O /\ (-velocityHessian u z).PosSemidef)
        constructor
        · rintro ⟨ht0, httau, hspatial, hpositivez, htimez, hpsdz⟩
          exact ⟨⟨⟨⟨ht0, httau, hspatial⟩, hpositivez⟩,
            ⟨⟨ht0, httau, hspatial⟩, htimez⟩⟩,
            ⟨⟨ht0, httau, hspatial⟩, hpsdz⟩⟩
        · rintro ⟨⟨⟨hOpositive, hpositivez⟩, ⟨hOtime, htimez⟩⟩, ⟨hOpsd, hpsdz⟩⟩
          exact ⟨hOpositive.1, hOpositive.2.1, hOpositive.2.2,
            hpositivez, htimez, hpsdz⟩]
      exact ((show MeasurableSet (O ∩ {z | 0 < u z}) from (huO.continuousOn.isOpen_inter_preimage hO isOpen_Ioi).measurableSet).inter hnonnegative).inter hpsd), ?_⟩
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
          ∂MeasureTheory.MeasureSpace.volume := (Trans.trans (MeasureTheory.measure_mono hcoverage)
  (MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv MeasureTheory.volume
    (movingLensSourceSignSet_areaFormulaData_of_localC2 hlocal).left fun z hz =>
    Eq.mpr
      (id
        (congrArg (fun _a => HasFDerivWithinAt (parabolicNormalMap u 0) _a (movingLensSourceSignSet xi eps tau y u) z)
          (HasFDerivAt.fderiv
            (parabolicNormalMap_hasFDerivAt_of_contDiffAt
              (hlocal z ⟨hz.left, ⟨LT.lt.le hz.right.left, hz.right.right.left⟩⟩)))))
      (HasFDerivAt.hasFDerivWithinAt
        (parabolicNormalMap_hasFDerivAt_of_contDiffAt
          (hlocal z ⟨hz.left, ⟨LT.lt.le hz.right.left, hz.right.right.left⟩⟩)))))

/-- Concrete physical contact/area API for supplied-source lower-bound proof: wedge volume. -/
theorem volume_movingLensSlopeInterceptWedge
     {R M : Real} (hR : 0 < R) (hM : 0 < M) :
    MeasureTheory.MeasureSpace.volume (movingLensSlopeInterceptWedge d R M) =
      ENNReal.ofReal (M / 4) *
        (ENNReal.ofReal ((M / (4 * R)) ^ d) *
          MeasureTheory.MeasureSpace.volume
            (PDE.euclideanBall (0 : PDE.Vec d) 1)) := by
  unfold movingLensSlopeInterceptWedge

  have hinterval : 3 * M / 4 - M / 2 = M / 4 := by ring
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    Real.volume_Ioo, hinterval,
    PDE.volume_euclideanBall_eq_unit_mul_of_pos (0 : PDE.Vec d) (div_pos hM (mul_pos (by norm_num) hR))]

end HypoellipticAleksandrov.Parabolic
