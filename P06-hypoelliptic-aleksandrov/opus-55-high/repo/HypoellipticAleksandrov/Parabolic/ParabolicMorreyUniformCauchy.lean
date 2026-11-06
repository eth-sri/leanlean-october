module

public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierJetCauchy
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyPhysicalLocalHolder
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDerivativeNorm
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyProjectionRecovery
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Uniform Cauchy control for parabolic mollifications

This module turns the strong selected-jet Cauchy estimate into uniform Cauchy
control on compact carriers.  Compact value support supplies one common
pointwise zero reference for every pair of mollifications.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic.ParabolicW12Function

open Filter MeasureTheory Set
open scoped BigOperators Convolution ENNReal Pointwise Topology


variable {d : Nat} {u : TimeVelocity d -> Real} (g : TimeVelocity d -> Real)

private theorem support_parabolicConvolution_subset_common
     (n : Nat) :
    Function.support (parabolicConvolution g (parabolicMollifier d n)) ⊆
      tsupport g + Metric.closedBall (0 : TimeVelocity d) 1 := by
  refine (support_convolution_subset _).trans ?_
  apply add_subset_add (subset_tsupport g)
  rw [support_parabolicMollifier]
  exact Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (by simpa using parabolicMollifierScale_le_one n))

private theorem support_parabolicConvolution_sub_subset_common
     (m n : Nat) :
    Function.support (fun z =>
      parabolicConvolution g (parabolicMollifier d m) z -
        parabolicConvolution g (parabolicMollifier d n) z) ⊆
      tsupport g + Metric.closedBall (0 : TimeVelocity d) 1 := (Function.support_sub _ _).trans
    (union_subset (support_parabolicConvolution_subset_common g m)
      (support_parabolicConvolution_subset_common g n))

private theorem exists_point_not_mem_of_isCompact
     {S : Set (TimeVelocity d)} (hS : IsCompact S) :
    ∃ z : TimeVelocity d, z ∉ S := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hS.isBounded
  refine ⟨(R + 1, 0), ?_⟩
  intro hz
  have hdist : dist ((R + 1, 0) : TimeVelocity d) 0 <= R := hR hz
  have htime : dist (R + 1) 0 <= R := by
    calc
      dist (R + 1) 0 <= dist _ 0 := le_max_left _ _
      _ <= R := hdist
  have hRnonneg : 0 <= R := (dist_nonneg.trans htime)
  have htime' : |R + 1| <= R := by
    simpa using htime
  rw [abs_of_nonneg (by linarith)] at htime'
  linarith

private theorem convolution_sub_eq_zero_of_not_mem_common
    
    {z : TimeVelocity d}
    (hz : z ∉ tsupport g + Metric.closedBall (0 : TimeVelocity d) 1) (m n : Nat) :
    parabolicConvolution g (parabolicMollifier d m) z -
      parabolicConvolution g (parabolicMollifier d n) z = 0 := by
  apply Function.notMem_support.mp
  intro hsupport
  exact hz (support_parabolicConvolution_sub_subset_common g m n hsupport)

private theorem open_mem_parabolicClosedBox_of_mem_parabolicBox
     {r t0 : Real} {v0 : PDE.Vec d} {z : TimeVelocity d}
    (hz : z ∈ parabolicBox 1 r t0 v0) :
    z ∈ parabolicClosedBox 1 r t0 v0 := by
  rcases mem_parabolicBox_iff.mp hz with ⟨hleft, hright, hvelocity⟩
  exact mem_parabolicClosedBox_iff.mpr ⟨hleft.le, hright.le, fun i => (hvelocity i).le⟩

private theorem exists_forward_box_of_isCompact
     {L : Set (TimeVelocity d)} (hL : IsCompact L) (hLnonempty : L.Nonempty) :
    ∃ (r t0 : Real) (v0 : PDE.Vec d), 0 < r ∧
      L ⊆ parabolicBox 1 r t0 v0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hL.isBounded
  obtain ⟨z0, hz0⟩ := hLnonempty
  have hRnonneg : 0 <= R := dist_nonneg.trans (hR hz0)
  refine ⟨2 * R + 2, -(2 * R + 2) ^ 2 / 2, 0, by linarith, ?_⟩
  intro z hz
  have hdist : dist z 0 <= R := hR hz
  have htime : |z.1| <= R := by
    have hfirst : dist z.1 0 <= R := by
      calc
        dist z.1 0 <= dist z 0 := le_max_left _ _
        _ <= R := hdist
    simpa using hfirst
  have hvelocityNorm : ‖z.2‖ <= R := by
    have hsecond : dist z.2 0 <= R := by
      calc
        dist z.2 0 <= dist z 0 := le_max_right _ _
        _ <= R := hdist
    simpa using hsecond
  have hvelocity : ∀ i : Fin d, |z.2 i| <= R := by
    rw [pi_norm_le_iff_of_nonneg hRnonneg] at hvelocityNorm
    simpa using hvelocityNorm
  rw [mem_parabolicBox_iff]
  refine ⟨?_, ?_, ?_⟩
  · have hsquare : R < (2 * R + 2) ^ 2 / 2 := by nlinarith [sq_nonneg (R + 1)]
    linarith [neg_le.mp (abs_le.mp htime).1]
  · have hsquare : R < (2 * R + 2) ^ 2 / 2 := by nlinarith [sq_nonneg (R + 1)]
    linarith [(abs_le.mp htime).2]
  · intro i
    have hi : |z.2 i| <= R := hvelocity i
    simpa using hi.trans_lt (by linarith)

private theorem parabolicSmoothJetLpNorm_eq_components
     (hu : ParabolicSmoothJetMemLp d u) :
    parabolicSmoothJetLpNorm d u =
      parabolicLpNorm d u + parabolicLpNorm d (timeDerivative u) +
        ∑ i : Fin d, parabolicLpNorm d (fun z => velocityGradient u z i) +
          ∑ i : Fin d, ∑ j : Fin d,
            parabolicLpNorm d
              (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian u z i j) := by
  unfold parabolicSmoothJetLpNorm parabolicSmoothJetELpNorm parabolicLpNorm parabolicELpNorm
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨hu.1.eLpNorm_ne_top, hu.2.1.eLpNorm_ne_top⟩,
      ENNReal.sum_ne_top.mpr fun i _ => (hu.2.2.1 i).eLpNorm_ne_top⟩)
    (ENNReal.sum_ne_top.mpr fun i _ => ENNReal.sum_ne_top.mpr fun j _ =>
      (hu.2.2.2 i j).eLpNorm_ne_top)]
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
    ⟨hu.1.eLpNorm_ne_top, hu.2.1.eLpNorm_ne_top⟩)
    (ENNReal.sum_ne_top.mpr fun i _ => (hu.2.2.1 i).eLpNorm_ne_top)]
  rw [ENNReal.toReal_add hu.1.eLpNorm_ne_top hu.2.1.eLpNorm_ne_top, ENNReal.toReal_sum fun i _ => (hu.2.2.1 i).eLpNorm_ne_top]
  rw [ENNReal.toReal_sum fun i _ => ENNReal.sum_ne_top.mpr fun j _ =>
    (hu.2.2.2 i j).eLpNorm_ne_top]
  simp_rw [ENNReal.toReal_sum fun j _ => (hu.2.2.2 _ j).eLpNorm_ne_top]

private theorem parabolicMorreyPhysical_rhs_le_smoothJet
     (hu : ParabolicSmoothJetMemLp d u)
    (Q : Set (TimeVelocity d)) {r : Real} (hr : 0 < r) :
    (r ^ 2)⁻¹ * parabolicLpNormOn d u Q +
        parabolicLpNormOn d (timeDerivative u) Q +
        r⁻¹ * ∑ i : Fin d, parabolicLpNormOn d
          (fun z => velocityGradient u z i) Q +
        ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
          (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian u z i j) Q <=
      ((r ^ 2)⁻¹ + 1 + r⁻¹ + 1) * parabolicSmoothJetLpNorm d u := by
  have hvalue := parabolicLpNormOn_le_parabolicLpNorm u Q hu.1
  have htime := parabolicLpNormOn_le_parabolicLpNorm _ Q hu.2.1
  have hgrad (i : Fin d) := parabolicLpNormOn_le_parabolicLpNorm
    _ Q (hu.2.2.1 i)
  have hhess (i j : Fin d) := parabolicLpNormOn_le_parabolicLpNorm
    _ Q (hu.2.2.2 i j)
  have hsumGrad : (∑ i : Fin d, parabolicLpNormOn d
      _ Q) <=
      ∑ i : Fin d, parabolicLpNorm d _ :=
    Finset.sum_le_sum fun i _ => hgrad i
  have hsumHess : (∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
      (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian u z i j) Q) <=
      ∑ i : Fin d, ∑ j : Fin d, parabolicLpNorm d
        (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian u z i j) := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.sum_le_sum fun j _ => hhess i j
  have hcomponents := parabolicSmoothJetLpNorm_eq_components hu
  have hvalueNonneg : 0 <= parabolicLpNorm d u := ENNReal.toReal_nonneg
  have htimeNonneg : 0 <= parabolicLpNorm d (timeDerivative u) := ENNReal.toReal_nonneg
  have hgradNonneg : 0 <= ∑ i : Fin d, parabolicLpNorm d
      (fun z => velocityGradient u z i) :=
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hhessNonneg : 0 <= ∑ i : Fin d, ∑ j : Fin d, parabolicLpNorm d
      (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian u z i j) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hrInv : 0 <= r⁻¹ := inv_nonneg.mpr hr.le
  have hrSqInv : 0 <= (r ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg r)
  calc
    (r ^ 2)⁻¹ * parabolicLpNormOn d u Q +
        parabolicLpNormOn d _ Q +
        r⁻¹ * ∑ i : Fin d, parabolicLpNormOn d
          _ Q +
        ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
          _ Q <=
        (r ^ 2)⁻¹ * parabolicLpNorm d u + parabolicLpNorm d _ +
          r⁻¹ * ∑ i : Fin d, parabolicLpNorm d
            _ +
          ∑ i : Fin d, ∑ j : Fin d, parabolicLpNorm d
            _ := by
      gcongr
    _ <= ((r ^ 2)⁻¹ + 1 + r⁻¹ + 1) * parabolicSmoothJetLpNorm d u := by
      nlinarith

/-- Compactly supported value mollifications are uniformly Cauchy on every
compact time--velocity carrier. -/
theorem uniformCauchySeqOn_parabolicConvolution
     (hd : 1 <= d)
    (g : ParabolicW12Function d Set.univ (parabolicExponent d))
    (hg : HasCompactSupport g.toFun)
    (K : Set (TimeVelocity d)) (hK : IsCompact K) :
    UniformCauchySeqOn
      (fun n : Nat => fun z : TimeVelocity d =>
        parabolicConvolution g.toFun (parabolicMollifier d n) z)
      atTop K := by
  let S  := tsupport g.toFun + Metric.closedBall 0 1
  have hScompact : IsCompact S := hg.isCompact.add (isCompact_closedBall 0 1)
  obtain ⟨zStar, hzStar⟩ := exists_point_not_mem_of_isCompact hScompact
  let L  := K ∪ {zStar}
  have hLcompact : IsCompact L := hK.union isCompact_singleton
  have hLnonempty : L.Nonempty := ⟨zStar, Or.inr (mem_singleton _)⟩
  obtain ⟨r, t0, v0, hr, hLbox⟩ := exists_forward_box_of_isCompact hLcompact hLnonempty
  obtain ⟨C, hCpos, hholder⟩ := exists_parabolicMorreyPhysicalLocalHolderFullJetConst d hd
  have halpha : 0 <= parabolicMorreyExponent d := by
    unfold parabolicMorreyExponent
    positivity
  let A  := ((r ^ 2)⁻¹ + 1 + r⁻¹ + 1)
  have hApos : 0 < A := by
    positivity
  let B  := C * (2 * r) ^ parabolicMorreyExponent d * A
  have hBpos : 0 < B := mul_pos (mul_pos hCpos (Real.rpow_pos_of_pos (by positivity) _)) hApos
  rw [Metric.uniformCauchySeqOn_iff]
  intro eps heps
  obtain ⟨N, hN⟩ := g.parabolicSmoothJetLpNorm_convolution_cauchy (eps / B)
    (div_pos heps hBpos)
  refine ⟨N, fun m hm n hn z hz => ?_⟩
  let u  := fun x =>
    parabolicConvolution g.toFun (parabolicMollifier d m) x -
      parabolicConvolution g.toFun (parabolicMollifier d n) x
  have huJet : ParabolicSmoothJetMemLp d u := by
    simpa using g.parabolicSmoothJetMemLp_convolution_sub m n
  have hpOne  := parabolicExponent_one_le d
  have huSmooth : ContDiff Real 2 u := by
    have hm : ContDiff Real 2
        _ :=
      (g.contDiff_convolution hpOne _
        (contDiff_parabolicMollifier d m) (hasCompactSupport_parabolicMollifier d m)).of_le
          (WithTop.coe_le_coe.mpr le_top)
    have hn : ContDiff Real 2
        _ :=
      (g.contDiff_convolution hpOne _
        (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n)).of_le
          (WithTop.coe_le_coe.mpr le_top)
    exact hm.sub hn
  have hzInner  := hLbox (Or.inl hz)
  have hzStarInner  :=
    hLbox (Or.inr (mem_singleton _))
  have hzClosed := open_mem_parabolicClosedBox_of_mem_parabolicBox hzInner
  have hzStarClosed := open_mem_parabolicClosedBox_of_mem_parabolicBox hzStarInner
  have hcoord  :=
    parabolicCoordinateDist_le_two_mul_radius_of_mem_parabolicClosedBox t0 v0 hr hzClosed
      hzStarClosed
  let Q  := parabolicBox 1 (2 * r) (t0 - r ^ 2) v0
  have huValue : ParabolicMemLpOn Q _ u :=
    huJet.1.mono_measure Measure.restrict_le_self
  have huTime : ParabolicMemLpOn Q _ _ :=
    huJet.2.1.mono_measure Measure.restrict_le_self
  have huGrad (i : Fin d) : ParabolicMemLpOn Q _
      _ :=
    (huJet.2.2.1 i).mono_measure Measure.restrict_le_self
  have huHess (i j : Fin d) : ParabolicMemLpOn Q _
      _ :=
    (huJet.2.2.2 i j).mono_measure Measure.restrict_le_self
  have hzero : u zStar = 0 := convolution_sub_eq_zero_of_not_mem_common g.toFun (by simpa using hzStar)
      m n
  have hphysical := hholder t0 v0 r hr z hzInner zStar hzStarInner u
    (by simpa using huSmooth.contDiffOn) huValue huTime huGrad huHess
  have hrhs := parabolicMorreyPhysical_rhs_le_smoothJet huJet Q hr
  have hphysicalRhsNonneg : 0 <=
      (r ^ 2)⁻¹ * parabolicLpNormOn d u Q +
        parabolicLpNormOn d (timeDerivative u) Q +
        r⁻¹ * ∑ i : Fin d, parabolicLpNormOn d
          (fun x => velocityGradient u x i) Q +
        ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
          (fun x => HypoellipticAleksandrov.Parabolic.velocityHessian u x i j) Q := by
    have hvalueNonneg : 0 <= parabolicLpNormOn d u Q := ENNReal.toReal_nonneg
    have htimeNonneg : 0 <= parabolicLpNormOn d (timeDerivative u) Q := ENNReal.toReal_nonneg
    have hgradNonneg : 0 <= ∑ i : Fin d, parabolicLpNormOn d
        (fun x => velocityGradient u x i) Q :=
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    have hhessNonneg : 0 <= ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
        (fun x => HypoellipticAleksandrov.Parabolic.velocityHessian u x i j) Q :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    exact add_nonneg (add_nonneg
      (add_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg r)) hvalueNonneg) htimeNonneg)
      (mul_nonneg (inv_nonneg.mpr hr.le) hgradNonneg)) hhessNonneg
  have hpower  :=
    Real.rpow_le_rpow (parabolicCoordinateDist_nonneg _ _) hcoord halpha
  have hpoint : |u z| <= B * parabolicSmoothJetLpNorm d u := by
    rw [hzero, sub_zero] at hphysical
    calc
      |u z| <= C * (parabolicCoordinateDist z zStar) ^ parabolicMorreyExponent d *
          ((r ^ 2)⁻¹ * parabolicLpNormOn d u Q +
            parabolicLpNormOn d _ Q +
            r⁻¹ * ∑ i : Fin d, parabolicLpNormOn d
              _ Q +
            ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
              _ Q) := hphysical
      _ <= C * (2 * r) ^ parabolicMorreyExponent d *
          (A * parabolicSmoothJetLpNorm d u) := by
        calc
          C * (parabolicCoordinateDist z zStar) ^ parabolicMorreyExponent d *
              ((r ^ 2)⁻¹ * parabolicLpNormOn d u Q +
                parabolicLpNormOn d _ Q +
                r⁻¹ * ∑ i : Fin d, parabolicLpNormOn d
                  _ Q +
                ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
                  _ Q) <=
              C * (2 * r) ^ parabolicMorreyExponent d *
                ((r ^ 2)⁻¹ * parabolicLpNormOn d u Q +
                  parabolicLpNormOn d _ Q +
                  r⁻¹ * ∑ i : Fin d, parabolicLpNormOn d
                    _ Q +
                  ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
                    _ Q) := by
              apply mul_le_mul_of_nonneg_right
              · exact mul_le_mul_of_nonneg_left hpower hCpos.le
              · exact hphysicalRhsNonneg
          _ <= C * (2 * r) ^ parabolicMorreyExponent d *
              (A * parabolicSmoothJetLpNorm d u) := by
              apply mul_le_mul_of_nonneg_left
              · simpa using hrhs
              · exact mul_nonneg hCpos.le (Real.rpow_nonneg (by positivity) _)
      _ = B * parabolicSmoothJetLpNorm d u := by
        ring
  calc
    |u z| <= B * parabolicSmoothJetLpNorm d u := hpoint
    _ < B * (eps / B) := mul_lt_mul_of_pos_left (hN m hm n hn) hBpos
    _ = eps := by field_simp [hBpos.ne']

end HypoellipticAleksandrov.Parabolic.ParabolicW12Function
