module

public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierJetCauchy
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyPhysicalLocalHolder
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDerivativeNorm
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyProjectionRecovery
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.UniformConvergence
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import all HypoellipticAleksandrov.Parabolic.ParabolicMollifierJetCauchy

open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.parabolicExponent_one_le from HypoellipticAleksandrov.Parabolic.ParabolicMollifierJetCauchy


/-!
# Uniform Cauchy control for parabolic mollifications

This module turns the strong selected-jet Cauchy estimate into uniform Cauchy
control on compact carriers.  Compact value support supplies one common
pointwise zero reference for every pair of mollifications.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic.ParabolicW12Function

open Filter MeasureTheory Set
open scoped BigOperators Convolution Pointwise




variable {d : Nat}

variable (g : HypoellipticAleksandrov.Parabolic.ScalarField d)

private theorem support_parabolicConvolution_subset_common
      (n : Nat) :
    Function.support (parabolicConvolution g (parabolicMollifier d n)) ⊆
      tsupport g + Metric.closedBall (0 : TimeVelocity d) 1 := by
  rw [show parabolicConvolution g (parabolicMollifier d n) =
      g ⋆[ContinuousLinearMap.mul Real Real, volume] (parabolicMollifier d n) by rfl]
  refine (support_convolution_subset (ContinuousLinearMap.mul Real Real)).trans ?_
  apply add_subset_add (subset_tsupport g)
  rw [support_parabolicMollifier]
  exact Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (parabolicMollifierScale_le_one n))

private theorem support_parabolicConvolution_sub_subset_common
      (m n : Nat) :
    Function.support (fun z =>
      parabolicConvolution g (parabolicMollifier d m) z -
        parabolicConvolution g (parabolicMollifier d n) z) ⊆
      tsupport g + Metric.closedBall (0 : TimeVelocity d) 1 := (Function.support_sub _ _).trans
    (union_subset (support_parabolicConvolution_subset_common g m)
      (support_parabolicConvolution_subset_common g n))

private theorem exists_point_not_mem_of_isCompact
     {S : HypoellipticAleksandrov.Parabolic.Region d} (hS : IsCompact S) :
    ∃ z : TimeVelocity d, z ∉ S := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hS.isBounded
  refine ⟨(R + 1, 0), ?_⟩
  intro hz

  have htime : dist (R + 1) 0 <= R := by
    calc
      dist (R + 1) 0 <= dist ((R + 1, 0) : TimeVelocity d) 0 := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      _ <= R := (hR hz)
  have hRnonneg : 0 <= R := (dist_nonneg.trans htime)
  have htime' : |R + 1| <= R := by
    simpa only [Real.dist_eq, sub_zero] using htime
  rw [abs_of_nonneg (by linarith : 0 <= R + 1)] at htime'
  linarith

private theorem convolution_sub_eq_zero_of_not_mem_common
     (g : HypoellipticAleksandrov.Parabolic.ScalarField d)
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
     {L : HypoellipticAleksandrov.Parabolic.Region d} (hL : IsCompact L) (hLnonempty : L.Nonempty) :
    ∃ (r t0 : Real) (v0 : PDE.Vec d), 0 < r ∧
      L ⊆ parabolicBox 1 r t0 v0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hL.isBounded
  obtain ⟨z0, hz0⟩ := hLnonempty
  have hRnonneg : 0 <= R := by
    exact dist_nonneg.trans (hR hz0)
  refine ⟨2 * R + 2, -(2 * R + 2) ^ 2 / 2, 0, by linarith, ?_⟩
  intro z hz
  have hdist  := hR hz
  have htime : |z.1| <= R := by
    have hfirst : dist z.1 0 <= R := by
      calc
        dist z.1 0 <= dist z 0 := by
          rw [Prod.dist_eq]
          exact le_max_left _ _
        _ <= R := hdist
    simpa only [Real.dist_eq, sub_zero] using hfirst
  have hvelocityNorm : ‖z.2‖ <= R := by
    have hsecond : dist z.2 0 <= R := by
      calc
        dist z.2 0 <= dist z 0 := by
          rw [Prod.dist_eq]
          exact le_max_right _ _
        _ <= R := hdist
    simpa only [dist_zero_right] using hsecond

  rw [mem_parabolicBox_iff]
  refine ⟨?_, ?_, ?_⟩
  · have hsquare : R < (2 * R + 2) ^ 2 / 2 := by nlinarith [sq_nonneg (R + 1)]
    linarith [neg_le.mp (abs_le.mp htime).1]
  · have hsquare : R < (2 * R + 2) ^ 2 / 2 := by nlinarith [sq_nonneg (R + 1)]
    linarith [(abs_le.mp htime).2]
  · intro i
    have hi  := (show ∀ i : Fin d, |z.2 i| <= R by
        rw [pi_norm_le_iff_of_nonneg hRnonneg] at hvelocityNorm
        exact hvelocityNorm) i
    simpa only [Pi.zero_apply, sub_zero] using hi.trans_lt (by linarith)

section
variable {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (hu : ParabolicSmoothJetMemLp d u)

include hu
private theorem parabolicSmoothJetLpNorm_eq_components
      :
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
  rw [ENNReal.toReal_add hu.1.eLpNorm_ne_top hu.2.1.eLpNorm_ne_top]
  rw [ENNReal.toReal_sum fun i _ => (hu.2.2.1 i).eLpNorm_ne_top]
  rw [ENNReal.toReal_sum fun i _ => ENNReal.sum_ne_top.mpr fun j _ =>
    (hu.2.2.2 i j).eLpNorm_ne_top]
  simp_rw [ENNReal.toReal_sum fun j _ => (hu.2.2.2 _ j).eLpNorm_ne_top]

private theorem parabolicMorreyPhysical_rhs_le_smoothJet

    (Q : HypoellipticAleksandrov.Parabolic.Region d) {r : Real} (hr : 0 < r) :
    (r ^ 2)⁻¹ * parabolicLpNormOn d u Q +
        parabolicLpNormOn d (timeDerivative u) Q +
        r⁻¹ * ∑ i : Fin d, parabolicLpNormOn d
          (fun z => velocityGradient u z i) Q +
        ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
          (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian u z i j) Q <=
      ((r ^ 2)⁻¹ + 1 + r⁻¹ + 1) * parabolicSmoothJetLpNorm d u := by
  let sharedTerm_2ff3485216 := (∑ i : Fin d, ∑ j : Fin d, parabolicLpNorm d (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian u z i j))
  let sharedTerm_1369ffe181 := (∑ i : Fin d, parabolicLpNorm d (fun z => velocityGradient u z i))
  let sharedTerm_f8c4739b7f := (∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian u z i j) Q)
  let sharedTerm_f0754cd928 := (∑ i : Fin d, parabolicLpNormOn d (fun z => velocityGradient u z i) Q)
  have hvalue := parabolicLpNormOn_le_parabolicLpNorm u Q hu.1
  have htime := parabolicLpNormOn_le_parabolicLpNorm _ Q hu.2.1
  have hgrad (i : Fin d) := parabolicLpNormOn_le_parabolicLpNorm
    (fun z => velocityGradient u z i) Q (hu.2.2.1 i)
  have hhess (i j : Fin d) := parabolicLpNormOn_le_parabolicLpNorm
    (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian u z i j) Q (hu.2.2.2 i j)
  have hsumGrad : (sharedTerm_f0754cd928) <=
      sharedTerm_1369ffe181 :=
    Finset.sum_le_sum fun i _ => hgrad i
  have hsumHess : (sharedTerm_f8c4739b7f) <=
      sharedTerm_2ff3485216 := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.sum_le_sum fun j _ => hhess i j
  have hcomponents := parabolicSmoothJetLpNorm_eq_components hu
  have hvalueNonneg : 0 <= parabolicLpNorm d u := ENNReal.toReal_nonneg
  have htimeNonneg : 0 <= parabolicLpNorm d (timeDerivative u) := ENNReal.toReal_nonneg
  have hgradNonneg : 0 <= sharedTerm_1369ffe181 :=
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hhessNonneg : 0 <= sharedTerm_2ff3485216 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg





  have hrInv  := inv_nonneg.mpr hr.le
  have hrSqInv  := inv_nonneg.mpr (sq_nonneg r)
  calc
    (r ^ 2)⁻¹ * parabolicLpNormOn d u Q +
        parabolicLpNormOn d (timeDerivative u) Q +
        r⁻¹ * sharedTerm_f0754cd928 +
        sharedTerm_f8c4739b7f <=
        (r ^ 2)⁻¹ * parabolicLpNorm d u + parabolicLpNorm d (timeDerivative u) +
          r⁻¹ * sharedTerm_1369ffe181 +
          sharedTerm_2ff3485216 := by
      gcongr
    _ <= ((r ^ 2)⁻¹ + 1 + r⁻¹ + 1) * parabolicSmoothJetLpNorm d u := by
      nlinarith
end


/-- Compactly supported value mollifications are uniformly Cauchy on every
compact time--velocity carrier. -/
theorem uniformCauchySeqOn_parabolicConvolution
     (hd : 1 <= d)
    (g : ParabolicW12Function d Set.univ (parabolicExponent d))
    (hg : HasCompactSupport g.toFun)
    (K : HypoellipticAleksandrov.Parabolic.Region d) (hK : IsCompact K) :
    UniformCauchySeqOn
      (fun n  => (parabolicConvolution g.toFun (parabolicMollifier d n)))
      atTop K := by


  obtain ⟨zStar, hzStar⟩ := exists_point_not_mem_of_isCompact (hg.isCompact.add (isCompact_closedBall 0 1))



  obtain ⟨r, t0, v0, hr, hLbox⟩ := exists_forward_box_of_isCompact (hK.union isCompact_singleton) (⟨zStar, Or.inr (mem_singleton _)⟩)
  obtain ⟨C, hCpos, hholder⟩ := exists_parabolicMorreyPhysicalLocalHolderFullJetConst d hd

  let A : Real := ((r ^ 2)⁻¹ + 1 + r⁻¹ + 1)

  let B : Real := C * (2 * r) ^ parabolicMorreyExponent d * A
  have hBpos : 0 < B := by
    dsimp [B]
    exact mul_pos (mul_pos hCpos (Real.rpow_pos_of_pos (by positivity) _)) (by
        dsimp [A]
        positivity)
  rw [Metric.uniformCauchySeqOn_iff]
  intro eps heps
  obtain ⟨N, hN⟩ := g.parabolicSmoothJetLpNorm_convolution_cauchy (eps / B)
    (div_pos heps hBpos)
  refine ⟨N, fun m hm n hn z hz => ?_⟩
  let u  := fun x =>
    parabolicConvolution g.toFun (parabolicMollifier d m) x -
      parabolicConvolution g.toFun (parabolicMollifier d n) x
  have huJet : ParabolicSmoothJetMemLp d u := by
    exact g.parabolicSmoothJetMemLp_convolution_sub m n
  have hpOne  := _root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.parabolicExponent_one_le d

  have hzInner  := hLbox (Or.inl hz)
  have hzStarInner  :=
    hLbox (Or.inr (mem_singleton _))


  have hcoord  :=
    parabolicCoordinateDist_le_two_mul_radius_of_mem_parabolicClosedBox t0 v0 hr (open_mem_parabolicClosedBox_of_mem_parabolicBox hzInner)
      (open_mem_parabolicClosedBox_of_mem_parabolicBox hzStarInner)
  let Q  := parabolicBox 1 (2 * r) (t0 - r ^ 2) v0


  have huGrad (i : Fin d) : ParabolicMemLpOn Q (parabolicExponent d)
      (fun x => velocityGradient u x i) :=
    (huJet.2.2.1 i).mono_measure Measure.restrict_le_self
  have huHess (i j : Fin d) : ParabolicMemLpOn Q (parabolicExponent d)
      (fun x => HypoellipticAleksandrov.Parabolic.velocityHessian u x i j) :=
    (huJet.2.2.2 i j).mono_measure Measure.restrict_le_self
  have hzero : u zStar = 0 := by
    dsimp [u]
    exact convolution_sub_eq_zero_of_not_mem_common g.toFun (hzStar)
      m n
  have hphysical := hholder t0 v0 r hr z hzInner zStar hzStarInner u
    ((show ContDiff Real 2 u by
        dsimp [u]
        have hm : ContDiff Real 2
            (parabolicConvolution g.toFun (parabolicMollifier d m)) :=
          (g.contDiff_convolution hpOne _
            (contDiff_parabolicMollifier d m) (hasCompactSupport_parabolicMollifier d m)).of_le
              (WithTop.coe_le_coe.mpr le_top)
        have hn : ContDiff Real 2
            (parabolicConvolution g.toFun (parabolicMollifier d n)) :=
          (g.contDiff_convolution hpOne _
            (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n)).of_le
              (WithTop.coe_le_coe.mpr le_top)
        exact hm.sub hn).contDiffOn) (huJet.1.mono_measure Measure.restrict_le_self) (huJet.2.1.mono_measure Measure.restrict_le_self) huGrad huHess

  have hphysicalRhsNonneg : 0 <=
      (r ^ 2)⁻¹ * parabolicLpNormOn d u Q +
        parabolicLpNormOn d (timeDerivative u) Q +
        r⁻¹ * ∑ i : Fin d, parabolicLpNormOn d
          (fun x => velocityGradient u x i) Q +
        ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
          (fun x => HypoellipticAleksandrov.Parabolic.velocityHessian u x i j) Q := by




    exact add_nonneg (add_nonneg
      (add_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg r)) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)
      (mul_nonneg (inv_nonneg.mpr hr.le) (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg))) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)


  rw [Real.dist_eq]
  change |u z| < eps
  calc
    |u z| <= B * parabolicSmoothJetLpNorm d u := (by
          rw [hzero, sub_zero] at hphysical
          calc
            |u z| <= C * (parabolicCoordinateDist z zStar) ^ parabolicMorreyExponent d *
                ((r ^ 2)⁻¹ * parabolicLpNormOn d u Q +
                  parabolicLpNormOn d (timeDerivative u) Q +
                  r⁻¹ * ∑ i : Fin d, parabolicLpNormOn d
                    (fun x => velocityGradient u x i) Q +
                  ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
                    (fun x => HypoellipticAleksandrov.Parabolic.velocityHessian u x i j) Q) := hphysical
            _ <= C * (2 * r) ^ parabolicMorreyExponent d *
                (A * parabolicSmoothJetLpNorm d u) := (Trans.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (parabolicCoordinateDist_nonneg _ _) hcoord (show 0 <= parabolicMorreyExponent d by
                    unfold parabolicMorreyExponent
                    positivity)) (LT.lt.le hCpos)) hphysicalRhsNonneg)
        (mul_le_mul_of_nonneg_left (parabolicMorreyPhysical_rhs_le_smoothJet huJet Q hr)
          (le_of_lt
            (mul_pos hCpos
              (Real.rpow_pos_of_pos
                (mul_pos
                  (Mathlib.Meta.Positivity.pos_of_isNat (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))
                    (Eq.refl (Nat.ble 1 2)))
                  hr)
                (parabolicMorreyExponent d))))))
            _ = B * parabolicSmoothJetLpNorm d u := by
              dsimp [B]
              ring)
    _ < B * (eps / B) := mul_lt_mul_of_pos_left (hN m hm n hn) hBpos
    _ = eps := by field_simp [hBpos.ne']

end HypoellipticAleksandrov.Parabolic.ParabolicW12Function
