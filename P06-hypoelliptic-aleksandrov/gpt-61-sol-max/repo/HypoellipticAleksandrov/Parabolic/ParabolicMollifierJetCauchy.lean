module

public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierConvergence
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNorm
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Measure.DensityNearOneMeasure
public import HypoellipticAleksandrov.Measure.TimeVelocity


open private HypoellipticAleksandrov.Parabolic.parabolicExponent_ne_top from HypoellipticAleksandrov.Measure.DensityNearOneMeasure


/-!
# Cauchy selected jets of parabolic mollifications

This module assembles the already established componentwise strong
convergence of a global selected weak jet into the finite selected smooth-jet
norm used by the parabolic Morrey program.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic.ParabolicW12Function

open MeasureTheory
open Filter
open scoped BigOperators

variable (d : Nat)

private theorem parabolicExponent_one_le  :
    (1 : ENNReal) <= parabolicExponent d := by
  simp [parabolicExponent]




variable {d : Nat}

variable {p : ENNReal} (w : ParabolicW12Function d Set.univ p)

private theorem toFun_memLp_global   :
    MemLp w.toFun p  := by
  have h := w.memLp
  change MemLp w.toFun p ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict Set.univ) at h
  simpa only [Measure.restrict_univ] using h

private theorem timeDeriv_memLp_global   :
    MemLp w.timeDeriv p  := by
  have h := w.timeDeriv_memLp
  change MemLp w.timeDeriv p ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict Set.univ) at h
  simpa only [Measure.restrict_univ] using h

private theorem velocityGrad_memLp_global   (i : Fin d) :
    MemLp (fun z => w.velocityGrad z i) p  := by
  have h := w.velocityGrad_memLp i
  change MemLp (fun z => w.velocityGrad z i) p
    ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict Set.univ) at h
  simpa only [Measure.restrict_univ] using h

private theorem velocityHessian_memLp_global   (i j : Fin d) :
    MemLp (fun z => w.velocityHessian z i j) p  := by
  have h := w.velocityHessian_memLp i j
  change MemLp (fun z => w.velocityHessian z i j) p
    ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict Set.univ) at h
  simpa only [Measure.restrict_univ] using h

variable {f g : HypoellipticAleksandrov.Parabolic.ScalarField d}

section
variable (hf : ContDiff Real 1 f) (hg : ContDiff Real 1 g)

include hf hg
private theorem timeDerivative_sub_of_contDiff
     :
    timeDerivative (f - g) = timeDerivative f - timeDerivative g := by
  funext z
  unfold timeDerivative
  rw [fderiv_sub (hf.differentiable (by norm_num) z)
    (hg.differentiable (by norm_num) z)]
  rfl

private theorem velocityGradient_sub_of_contDiff
     (i : Fin d) :
    (fun z => velocityGradient (f - g) z i) =
      fun z => velocityGradient f z i - velocityGradient g z i := by
  funext z
  unfold velocityGradient
  rw [fderiv_sub (hf.differentiable (by norm_num) z)
    (hg.differentiable (by norm_num) z)]
  rfl
end


private theorem velocityHessian_sub_of_contDiff
    (hf : ContDiff Real (⊤ : ENat) f) (hg : ContDiff Real (⊤ : ENat) g) (i j : Fin d) :
    (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian (f - g) z i j) =
      fun z => HypoellipticAleksandrov.Parabolic.velocityHessian f z i j -
        HypoellipticAleksandrov.Parabolic.velocityHessian g z i j := by
  funext z
  have hcoeTop : (⊤ : ENat) <= (↑(⊤ : ENat) : WithTop ENat) :=
    WithTop.coe_le_coe.2 (OrderTop.le_top _)
  have hff : DifferentiableAt Real (fderiv Real f) z :=
    (hf.fderiv_right (m := 1)
      (ENat.add_one_natCast_le_withTop_of_lt
        (ENat.natCast_lt_of_coe_top_le_withTop hcoeTop 1))).differentiable
        (by norm_num) z
  have hgf : DifferentiableAt Real (fderiv Real g) z :=
    (hg.fderiv_right (m := 1)
      (ENat.add_one_natCast_le_withTop_of_lt
        (ENat.natCast_lt_of_coe_top_le_withTop hcoeTop 1))).differentiable
        (by norm_num) z
  unfold HypoellipticAleksandrov.Parabolic.velocityHessian
  have hfirst : fderiv Real (f - g) = fderiv Real f - fderiv Real g := by
    funext x
    exact fderiv_sub (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x)
  rw [hfirst, fderiv_sub hff hgf]
  rfl

variable (w : ParabolicW12Function d Set.univ (parabolicExponent d)) (m n : Nat)

private theorem timeDerivative_convolution_sub
     :
    timeDerivative
        (fun z => parabolicConvolution w.toFun (parabolicMollifier d m) z -
          parabolicConvolution w.toFun (parabolicMollifier d n) z) =
      fun z => parabolicConvolution w.timeDeriv (parabolicMollifier d m) z -
        parabolicConvolution w.timeDeriv (parabolicMollifier d n) z := by

  have hpOne : (1 : ENNReal) <= (parabolicExponent d) := by
    exact parabolicExponent_one_le d
  have hmf := w.contDiff_convolution hpOne _
    (contDiff_parabolicMollifier d m) (hasCompactSupport_parabolicMollifier d m)
  have hnf := w.contDiff_convolution hpOne _
    (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n)
  change timeDerivative
      (parabolicConvolution w.toFun (parabolicMollifier d m) -
        parabolicConvolution w.toFun (parabolicMollifier d n)) = _
  rw [timeDerivative_sub_of_contDiff (hmf.of_le (by norm_num)) (hnf.of_le (by norm_num))]
  rw [w.timeDerivative_convolution hpOne _
      (contDiff_parabolicMollifier d m) (hasCompactSupport_parabolicMollifier d m),
    w.timeDerivative_convolution hpOne _
      (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n)]
  rfl

private theorem velocityGradient_convolution_sub
     (i : Fin d) :
    (fun z => velocityGradient
      (fun z => parabolicConvolution w.toFun (parabolicMollifier d m) z -
        parabolicConvolution w.toFun (parabolicMollifier d n) z) z i) =
      fun z => parabolicConvolution (fun y => w.velocityGrad y i) (parabolicMollifier d m) z -
        parabolicConvolution (fun y => w.velocityGrad y i) (parabolicMollifier d n) z := by

  have hpOne : (1 : ENNReal) <= (parabolicExponent d) := by
    exact parabolicExponent_one_le d
  have hmf := w.contDiff_convolution hpOne _
    (contDiff_parabolicMollifier d m) (hasCompactSupport_parabolicMollifier d m)
  have hnf := w.contDiff_convolution hpOne _
    (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n)
  change (fun z => velocityGradient
      (parabolicConvolution w.toFun (parabolicMollifier d m) -
        parabolicConvolution w.toFun (parabolicMollifier d n)) z i) = _
  rw [velocityGradient_sub_of_contDiff (hmf.of_le (by norm_num))
    (hnf.of_le (by norm_num)) i]
  funext z
  rw [congrFun (w.velocityGradient_convolution hpOne _
      (contDiff_parabolicMollifier d m) (hasCompactSupport_parabolicMollifier d m) i) z,
    congrFun (w.velocityGradient_convolution hpOne _
      (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n) i) z]

private theorem velocityHessian_convolution_sub

    (i j : Fin d) :
    (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian
      (fun z => parabolicConvolution w.toFun (parabolicMollifier d m) z -
        parabolicConvolution w.toFun (parabolicMollifier d n) z) z i j) =
      fun z => parabolicConvolution (fun y => w.velocityHessian y i j)
          (parabolicMollifier d m) z -
        parabolicConvolution (fun y => w.velocityHessian y i j)
          (parabolicMollifier d n) z := by

  have hpOne : (1 : ENNReal) <= (parabolicExponent d) := by
    exact parabolicExponent_one_le d
  have hmf := w.contDiff_convolution hpOne _
    (contDiff_parabolicMollifier d m) (hasCompactSupport_parabolicMollifier d m)
  have hnf := w.contDiff_convolution hpOne _
    (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n)
  change (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian
      (parabolicConvolution w.toFun (parabolicMollifier d m) -
        parabolicConvolution w.toFun (parabolicMollifier d n)) z i j) = _
  rw [velocityHessian_sub_of_contDiff hmf hnf i j]
  funext z
  rw [congrFun (w.velocityHessian_convolution hpOne _
      (contDiff_parabolicMollifier d m) (hasCompactSupport_parabolicMollifier d m) i j) z,
    congrFun (w.velocityHessian_convolution hpOne _
      (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n) i j) z]

private theorem tendsto_eLpNorm_convolution_pair_sub
     {p : ENNReal} {g : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hpOne : 1 <= p) (hpTop : p ≠ ⊤) (hmem : MemLp g p volume)
    (hconv : Tendsto (fun n  => eLpNorm
      (fun z => parabolicConvolution g (parabolicMollifier d n) z - g z) p volume)
      atTop (nhds 0)) :
    Tendsto (fun mn : Nat × Nat => eLpNorm
      (fun z => parabolicConvolution g (parabolicMollifier d mn.1) z -
        parabolicConvolution g (parabolicMollifier d mn.2) z) p volume)
      atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro eta heta

  have hsmall  :=
    ENNReal.tendsto_nhds_zero.1 hconv (eta / 2) (ENNReal.div_pos heta.ne' (by norm_num))


  filter_upwards [(by
      rw [← prod_atTop_atTop_eq]
      exact tendsto_fst.eventually hsmall), (by
      rw [← prod_atTop_atTop_eq]
      exact tendsto_snd.eventually hsmall)] with mn hm hn


  have hdecomp :
      (fun z => parabolicConvolution g (parabolicMollifier d mn.1) z -
        parabolicConvolution g (parabolicMollifier d mn.2) z) =
      (fun z => (parabolicConvolution g (parabolicMollifier d mn.1) z - g z) -
        (parabolicConvolution g (parabolicMollifier d mn.2) z - g z)) := by
    funext z
    ring
  rw [hdecomp]
  calc
    eLpNorm (fun z => (parabolicConvolution g (parabolicMollifier d mn.1) z - g z) -
        (parabolicConvolution g (parabolicMollifier d mn.2) z - g z)) p volume <=
        eLpNorm (fun z => parabolicConvolution g (parabolicMollifier d mn.1) z - g z) p volume +
          eLpNorm (fun z => parabolicConvolution g (parabolicMollifier d mn.2) z - g z) p volume :=
      eLpNorm_sub_le hpOne
    _ <= eta / 2 + eta / 2 := add_le_add hm hn
    _ = eta := ENNReal.add_halves eta

variable (w : ParabolicW12Function d Set.univ (parabolicExponent d))

/-- Every difference of two value mollifications has a finite selected
smooth-jet `L^(d+1)` norm. -/
theorem parabolicSmoothJetMemLp_convolution_sub
     (m n : Nat) :
    ParabolicSmoothJetMemLp d (fun z => parabolicConvolution w.toFun (parabolicMollifier d m) z -
      parabolicConvolution w.toFun (parabolicMollifier d n) z) := by
  let p  := parabolicExponent d
  have hpOne : (1 : ENNReal) <= p := by
    exact parabolicExponent_one_le d
  have hpTop : p ≠ ⊤ := by
    exact _root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_ne_top d
  have hvalue : MemLp
      (fun z => parabolicConvolution w.toFun (parabolicMollifier d m) z -
        parabolicConvolution w.toFun (parabolicMollifier d n) z) p  :=
    (memLp_parabolicConvolution_parabolicMollifier hpOne hpTop (toFun_memLp_global w) m).sub
      (memLp_parabolicConvolution_parabolicMollifier hpOne hpTop (toFun_memLp_global w) n)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hvalue
  · rw [timeDerivative_convolution_sub w m n]
    exact (memLp_parabolicConvolution_parabolicMollifier hpOne hpTop
      (timeDeriv_memLp_global w) m).sub
        (memLp_parabolicConvolution_parabolicMollifier hpOne hpTop
          (timeDeriv_memLp_global w) n)
  · intro i
    rw [velocityGradient_convolution_sub w m n i]
    exact (memLp_parabolicConvolution_parabolicMollifier hpOne hpTop
      (velocityGrad_memLp_global w i) m).sub
        (memLp_parabolicConvolution_parabolicMollifier hpOne hpTop
          (velocityGrad_memLp_global w i) n)
  · intro i j
    rw [velocityHessian_convolution_sub w m n i j]
    exact (memLp_parabolicConvolution_parabolicMollifier hpOne hpTop
      (velocityHessian_memLp_global w i j) m).sub
        (memLp_parabolicConvolution_parabolicMollifier hpOne hpTop
          (velocityHessian_memLp_global w i j) n)

/-- The full extended-real selected smooth-jet norm of two mollifications
tends to zero as both mollifier indices tend to infinity. -/
theorem tendsto_parabolicSmoothJetELpNorm_convolution_sub
     :
    Tendsto (fun mn : Nat × Nat => parabolicSmoothJetELpNorm d
      (fun z => parabolicConvolution w.toFun (parabolicMollifier d mn.1) z -
        parabolicConvolution w.toFun (parabolicMollifier d mn.2) z)) atTop (nhds 0) := by
  let p  := parabolicExponent d
  have hpOne : (1 : ENNReal) <= p := by
    exact parabolicExponent_one_le d
  have hpTop : p ≠ ⊤ := by
    exact _root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_ne_top d
  have hvalue := tendsto_eLpNorm_convolution_pair_sub hpOne hpTop (toFun_memLp_global w)
    (w.tendsto_eLpNorm_convolution_toFun_sub hpOne hpTop)
  have htime := tendsto_eLpNorm_convolution_pair_sub hpOne hpTop (timeDeriv_memLp_global w)
    (w.tendsto_eLpNorm_convolution_timeDeriv_sub hpOne hpTop)
  have hgrad (i : Fin d) :=
    tendsto_eLpNorm_convolution_pair_sub hpOne hpTop (velocityGrad_memLp_global w i)
      (w.tendsto_eLpNorm_convolution_velocityGrad_sub hpOne hpTop i)
  have hhess (i j : Fin d) :=
    tendsto_eLpNorm_convolution_pair_sub hpOne hpTop (velocityHessian_memLp_global w i j)
      (w.tendsto_eLpNorm_convolution_velocityHessian_sub hpOne hpTop i j)

  have hgrad' (i : Fin d) : Tendsto (fun mn : Nat × Nat => parabolicELpNorm d
      (fun z => velocityGradient
        (fun z => parabolicConvolution w.toFun (parabolicMollifier d mn.1) z -
          parabolicConvolution w.toFun (parabolicMollifier d mn.2) z) z i)) atTop (nhds 0) := by
    simp_rw [velocityGradient_convolution_sub w]
    exact hgrad i
  have hhess' (i j : Fin d) : Tendsto (fun mn : Nat × Nat => parabolicELpNorm d
      (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian
        (fun z => parabolicConvolution w.toFun (parabolicMollifier d mn.1) z -
          parabolicConvolution w.toFun (parabolicMollifier d mn.2) z) z i j)) atTop (nhds 0) := by
    simp_rw [velocityHessian_convolution_sub w]
    exact hhess i j
  unfold parabolicSmoothJetELpNorm


  simpa only [parabolicELpNorm, p, add_zero] using
    (((hvalue.add (show Tendsto (fun mn : Nat × Nat => parabolicELpNorm d (timeDerivative
      (fun z => parabolicConvolution w.toFun (parabolicMollifier d mn.1) z -
        parabolicConvolution w.toFun (parabolicMollifier d mn.2) z))) atTop (nhds 0) by
        simp_rw [timeDerivative_convolution_sub w]
        exact htime)).add (show Tendsto (fun mn : Nat × Nat => ∑ i : Fin d, parabolicELpNorm d
      (fun z => velocityGradient
        (fun z => parabolicConvolution w.toFun (parabolicMollifier d mn.1) z -
          parabolicConvolution w.toFun (parabolicMollifier d mn.2) z) z i)) atTop (nhds 0) by
        simpa only [Finset.sum_const_zero] using
          (tendsto_finset_sum Finset.univ fun i _ => hgrad' i))).add (show Tendsto (fun mn : Nat × Nat => ∑ i : Fin d, ∑ j : Fin d,
      parabolicELpNorm d (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian
        (fun z => parabolicConvolution w.toFun (parabolicMollifier d mn.1) z -
          parabolicConvolution w.toFun (parabolicMollifier d mn.2) z) z i j)) atTop (nhds 0) by
        simpa only [Finset.sum_const_zero] using
          (tendsto_finset_sum Finset.univ fun i _ =>
            tendsto_finset_sum Finset.univ fun j _ => hhess' i j)))

/-- The real selected smooth-jet norm of two value mollifications is Cauchy. -/
theorem parabolicSmoothJetLpNorm_convolution_cauchy
     :
    forall eps : Real, 0 < eps -> exists N : Nat, forall m : Nat, N <= m -> forall n : Nat,
      N <= n -> parabolicSmoothJetLpNorm d
        (fun z => parabolicConvolution w.toFun (parabolicMollifier d m) z -
          parabolicConvolution w.toFun (parabolicMollifier d n) z) < eps := (fun eps heps =>
  Exists.casesOn
    (eventually_atTop.mp
      (ENNReal.tendsto_nhds_zero.mp (tendsto_parabolicSmoothJetELpNorm_convolution_sub w) (ENNReal.ofReal (eps / 2))
        (ENNReal.ofReal_pos.mpr (half_pos heps))))
    fun MN hMN =>
    Exists.intro (max MN.1 MN.2) fun m hm n hn =>
      id
        (Eq.mpr
          (id
            (congrArg
              (fun _a =>
                (parabolicSmoothJetELpNorm d fun z =>
                      parabolicConvolution w.toFun (parabolicMollifier d m) z -
                        parabolicConvolution w.toFun (parabolicMollifier d n) z).toReal <
                  _a)
              (Eq.symm (ENNReal.toReal_ofReal (LT.lt.le heps)))))
          ((ENNReal.toReal_lt_toReal (parabolicSmoothJetELpNorm_ne_top (parabolicSmoothJetMemLp_convolution_sub w m n))
                ENNReal.ofReal_ne_top).mpr
            (LE.le.trans_lt
              (hMN (m, n) ⟨LE.le.trans (le_max_left MN.1 MN.2) hm, LE.le.trans (le_max_right MN.1 MN.2) hn⟩)
              ((ENNReal.ofReal_lt_ofReal_iff heps).mpr (half_lt_self heps))))))

end HypoellipticAleksandrov.Parabolic.ParabolicW12Function
