module

public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.CompactScalarJet
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.UniformConvolution
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.SmoothDerivatives
import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.CompactLp
import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.SpatialWeakDerivatives
import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.TimeWeakDerivative
import HypoellipticAleksandrov.Parabolic.WeakJetCutoff
import HypoellipticAleksandrov.Parabolic.WeakJetExtension

/-! # Uniform approximation of the anisotropic scalar jet -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.KrylovEstimate
open Filter Set
open scoped Topology
open MeasureTheory

/- Smooth functions approximate all selected scalar derivatives on interior compact sets. -/
theorem exists_smooth_scalar_jet_close
    {N : ℕ} {V K : Set (TimeVelocity N)} (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V)
    (q : TimeVelocity N → ℝ) (hq : IsScalarC12On q V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : TimeVelocity N → ℝ, ContDiff ℝ 2 w ∧
      ∀ z ∈ K,
        |w z - q z| ≤ ε ∧
        |scalarTimeDerivative w z - scalarTimeDerivative q z| ≤ ε ∧
        (∀ i : Fin N, |scalarSpatialGradient w z i -
          scalarSpatialGradient q z i| ≤ ε) ∧
        (∀ i j : Fin N, |scalarSpatialHessian w z i j -
          scalarSpatialHessian q z i j| ≤ ε) := by
  obtain ⟨W, hv, hvc, ht, htc, hg, hh, ev, et, eg, eh⟩ : ∃ w : ParabolicW12Function N univ 1,
      Continuous w.toFun ∧ HasCompactSupport w.toFun ∧
      Continuous w.timeDeriv ∧ HasCompactSupport w.timeDeriv ∧
      (∀ i, Continuous (fun z => w.velocityGrad z i) ∧
        HasCompactSupport (fun z => w.velocityGrad z i)) ∧
      (∀ i j, Continuous (fun z => w.velocityHessian z i j) ∧
        HasCompactSupport (fun z => w.velocityHessian z i j)) ∧
      EqOn w.toFun q K ∧ EqOn w.timeDeriv (scalarTimeDerivative q) K ∧
      EqOn w.velocityGrad (scalarSpatialGradient q) K ∧
      EqOn w.velocityHessian (scalarSpatialHessian q) K := by
    obtain ⟨U, hU, hKU, hUV, hcU⟩ :=
      exists_open_between_and_isCompact_closure hK hV hKV
    have hsub : U ⊆ V := subset_closure.trans hUV
    have hlocal : IsScalarC12On q U :=
      ⟨hq.continuousOn.mono hsub, fun z hz => hq.timeSlice_differentiableAt (hsub hz),
        fun z hz => hq.spatialSlice_contDiffAt (hsub hz),
        hq.continuousOn_scalarTimeDerivative.mono hsub,
        hq.continuousOn_scalarSpatialGradient.mono hsub,
        hq.continuousOn_scalarSpatialHessian.mono hsub⟩
    let w : ParabolicW12Function N U 1 :=
      { toFun := q
        timeDeriv := scalarTimeDerivative q
        velocityGrad := scalarSpatialGradient q
        velocityHessian := scalarSpatialHessian q
        memLp := memLp_on_of_continuousOn_compact_closure hq.continuousOn hU hcU hUV 1
        timeDeriv_memLp := memLp_on_of_continuousOn_compact_closure
          hq.continuousOn_scalarTimeDerivative hU hcU hUV 1
        velocityGrad_memLp := fun i => memLp_on_of_continuousOn_compact_closure
          ((continuous_apply i).comp_continuousOn hq.continuousOn_scalarSpatialGradient)
          hU hcU hUV 1
        velocityHessian_memLp := fun i j => memLp_on_of_continuousOn_compact_closure
          ((continuous_apply j).comp_continuousOn
            ((continuous_apply i).comp_continuousOn hq.continuousOn_scalarSpatialHessian))
          hU hcU hUV 1
        hasWeakTimeDeriv := IsScalarC12On.hasWeakTimeDerivOn hU hlocal
        hasWeakVelocityPartialDeriv := IsScalarC12On.hasWeakVelocityPartialDerivOn hU hlocal
        hasWeakVelocitySecondPartialDeriv :=
          IsScalarC12On.hasWeakVelocitySecondPartialDerivOn hU hlocal }
    obtain ⟨b, hb, hc, hbOne, hbU, hv, ht, hg, hh⟩ :=
      exists_smooth_compact_cutoff_mul_eventuallyEq_jet hK hU hcU hKU w le_rfl
    let W := w.mulContDiffHasCompactSupport_univ le_rfl hb hc hU hbU
    have hb2 : ContDiff ℝ 2 b := hb.of_le (by simp)
    have hdb : Continuous (timeDerivative b) := by
      exact ((hb2.fderiv_right (m := 1) (by norm_num)).continuous.clm_apply continuous_const)
    have hgb (i : Fin N) : Continuous (fun z => velocityGradient b z i) :=
      (continuous_apply i).comp (contDiff_velocityGradient hb2).continuous
    have hhb (i j : Fin N) : Continuous (fun z => velocityHessian b z i j) := by
      exact (((hb2.fderiv_right (m := 1) (by norm_num)).fderiv_right
        (m := 0) (by norm_num)).continuous.clm_apply continuous_const).clm_apply
        continuous_const
    have hvs : tsupport W.toFun ⊆ tsupport b := tsupport_mul_subset_left
    have hts : tsupport W.timeDeriv ⊆ tsupport b :=
      tsupport_mul_timeDeriv_subset b q (scalarTimeDerivative q)
    have hgs (i : Fin N) : tsupport (fun z => W.velocityGrad z i) ⊆ tsupport b :=
      tsupport_mul_velocityGrad_subset b q (fun z => scalarSpatialGradient q z i)
    have hhs (i j : Fin N) : tsupport (fun z => W.velocityHessian z i j) ⊆ tsupport b :=
      tsupport_mul_velocityHessian_subset b q (fun z => scalarSpatialGradient q z i)
        (fun z => scalarSpatialGradient q z j) (fun z => scalarSpatialHessian q z i j)
    have hvc : Continuous W.toFun :=
      (hb.continuous.continuousOn.mul hlocal.continuousOn).continuous_of_tsupport_subset
        hU (hvs.trans hbU)
    have htc : Continuous W.timeDeriv :=
      ((hb.continuous.continuousOn.mul hlocal.continuousOn_scalarTimeDerivative).add
        (hlocal.continuousOn.mul hdb.continuousOn)).continuous_of_tsupport_subset
        hU (hts.trans hbU)
    have hgc (i : Fin N) : Continuous (fun z => W.velocityGrad z i) :=
      ((hb.continuous.continuousOn.mul
        ((continuous_apply i).comp_continuousOn hlocal.continuousOn_scalarSpatialGradient)).add
        (hlocal.continuousOn.mul (hgb i).continuousOn)).continuous_of_tsupport_subset
        hU ((hgs i).trans hbU)
    have hhc (i j : Fin N) : Continuous (fun z => W.velocityHessian z i j) := by
      apply ContinuousOn.continuous_of_tsupport_subset (s := U) _ hU ((hhs i j).trans hbU)
      exact (((hb.continuous.continuousOn.mul ((continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn hlocal.continuousOn_scalarSpatialHessian))).add
        ((hgb j).continuousOn.mul ((continuous_apply i).comp_continuousOn
          hlocal.continuousOn_scalarSpatialGradient))).add
        (((continuous_apply j).comp_continuousOn hlocal.continuousOn_scalarSpatialGradient).mul
          (hgb i).continuousOn)).add (hlocal.continuousOn.mul (hhb i j).continuousOn)
    have compact (f : TimeVelocity N → ℝ) (hf : tsupport f ⊆ tsupport b) :
        HasCompactSupport f := hc.of_isClosed_subset (isClosed_tsupport _) hf
    have eqon {E : Type} {f g : TimeVelocity N → E} (he : f =ᶠ[𝓝ˢ K] g) : EqOn f g K := by
      obtain ⟨O, _, hKO, hO⟩ := eventually_nhdsSet_iff_exists.mp he
      exact fun z hz => hO z (hKO hz)
    exact ⟨W, hvc, compact _ hvs, htc, compact _ hts,
      fun i => ⟨hgc i, compact _ (hgs i)⟩,
      fun i j => ⟨hhc i j, compact _ (hhs i j)⟩, eqon (E := ℝ) hv, eqon (E := ℝ) ht,
      eqon (E := PDE.Vec N) hg, eqon (E := PDE.Mat N) hh⟩
  have av := eventually_uniform_parabolicConvolution_close W.toFun hv hvc hε
  have atime := eventually_uniform_parabolicConvolution_close W.timeDeriv ht htc hε
  have ag : ∀ᶠ n in atTop, ∀ i : Fin N, ∀ z,
      |parabolicConvolution (fun y => W.velocityGrad y i) (parabolicMollifier N n) z -
        W.velocityGrad z i| ≤ ε := by
    rw [eventually_all]
    exact fun i => eventually_uniform_parabolicConvolution_close _ (hg i).1 (hg i).2 hε
  have ah : ∀ᶠ n in atTop, ∀ i j : Fin N, ∀ z,
      |parabolicConvolution (fun y => W.velocityHessian y i j)
        (parabolicMollifier N n) z - W.velocityHessian z i j| ≤ ε := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    exact fun j => eventually_uniform_parabolicConvolution_close _ (hh i j).1 (hh i j).2 hε
  obtain ⟨n, hn⟩ := (av.and (atime.and (ag.and ah))).exists
  let w := parabolicConvolution W.toFun (parabolicMollifier N n)
  have hs := W.contDiff_convolution le_rfl _ (contDiff_parabolicMollifier N n)
    (hasCompactSupport_parabolicMollifier N n)
  have hw : ContDiff ℝ 2 w := hs.of_le (by simp)
  have dt := W.timeDerivative_convolution le_rfl _ (contDiff_parabolicMollifier N n)
    (hasCompactSupport_parabolicMollifier N n)
  have dg := W.velocityGradient_convolution le_rfl _ (contDiff_parabolicMollifier N n)
    (hasCompactSupport_parabolicMollifier N n)
  have dh := W.velocityHessian_convolution le_rfl _ (contDiff_parabolicMollifier N n)
    (hasCompactSupport_parabolicMollifier N n)
  refine ⟨w, hw, fun z hz => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [← ev hz]
    exact hn.1 z
  · rw [scalarTimeDerivative_eq_timeDerivative w hw z, ← et hz]
    change |timeDerivative (parabolicConvolution W.toFun _) z - W.timeDeriv z| ≤ ε
    rw [dt]
    exact hn.2.1 z
  · intro i
    rw [scalarSpatialGradient_eq_velocityGradient w hw z, ← eg hz]
    change |velocityGradient (parabolicConvolution W.toFun _) z i - W.velocityGrad z i| ≤ ε
    rw [congrFun (dg i) z]
    exact hn.2.2.1 i z
  · intro i j
    rw [scalarSpatialHessian_eq_velocityHessian w hw z, ← eh hz]
    change |velocityHessian (parabolicConvolution W.toFun _) z i j -
      W.velocityHessian z i j| ≤ ε
    rw [congrFun (dh i j) z]
    exact hn.2.2.2 i j z

end HypoellipticAleksandrov.Parabolic.KrylovEstimate
