module

public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierUniformLimit
public import HypoellipticAleksandrov.Parabolic.WeakRepresentativeLocalization
public import HypoellipticAleksandrov.Parabolic.WeakJetExtension
public import Mathlib.Topology.Compactness.SigmaCompact
import HypoellipticAleksandrov.Parabolic.Geometry
import Mathlib.Topology.Separation.Regular

/-!
# Localized jets for weak-solution mollifier convergence

This module packages the concrete cutoff localization of a selected local
parabolic weak jet.  It derives compact-uniform convergence of its literal
global mollifications to a supplied continuous representative.  No equation,
coefficient, residual, sign, or kernel-localization assertion is made here.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

/- A selected local parabolic weak jet together with its concrete compactly
supported global cutoff extension around a compact carrier. -/
structure LocalizedParabolicJet
    (d : Nat) (U K : Set (TimeVelocity d)) (u : TimeVelocity d → Real) where
  V : Set (TimeVelocity d)
  W : Set (TimeVelocity d)
  w : ParabolicW12Function d W (parabolicExponent d)
  b : TimeVelocity d → Real
  g : ParabolicW12Function d Set.univ (parabolicExponent d)
  V_open : IsOpen V
  V_closure_compact : IsCompact (closure V)
  K_subset_V : K ⊆ V
  W_open : IsOpen W
  W_closure_compact : IsCompact (closure W)
  closure_V_subset_W : closure V ⊆ W
  closure_W_subset_U : closure W ⊆ U
  w_ae_eq_u : w.toFun =ᵐ[timeVelocityVolumeOn W] u
  b_smooth : ContDiff Real (⊤ : ℕ∞) b
  b_compact : HasCompactSupport b
  b_tsupport_subset_W : tsupport b ⊆ W
  b_one_near_closure_V : ∀ᶠ z in 𝓝ˢ (closure V), b z = 1
  g_is_cutoff :
    g = w.mulContDiffHasCompactSupport_univ
      (by simp [parabolicExponent]) b_smooth b_compact W_open b_tsupport_subset_W
  g_toFun_eq_near_closure_V : g.toFun =ᶠ[𝓝ˢ (closure V)] w.toFun
  g_timeDeriv_eq_near_closure_V : g.timeDeriv =ᶠ[𝓝ˢ (closure V)] w.timeDeriv
  g_velocityGrad_eq_near_closure_V :
    g.velocityGrad =ᶠ[𝓝ˢ (closure V)] w.velocityGrad
  g_velocityHessian_eq_near_closure_V :
    g.velocityHessian =ᶠ[𝓝ˢ (closure V)] w.velocityHessian

namespace LocalizedParabolicJet

/- The selected cutoff jet agrees with its local jet on an open plateau that
contains the closure of the compact carrier. -/
theorem exists_open_plateau
    {d U K u}
    (J : LocalizedParabolicJet d U K u) :
    ∃ O : Set (TimeVelocity d),
      IsOpen O ∧ closure J.V ⊆ O ∧ O ⊆ J.W ∧
      EqOn J.g.toFun J.w.toFun O ∧
      EqOn J.g.timeDeriv J.w.timeDeriv O ∧
      EqOn J.g.velocityGrad J.w.velocityGrad O ∧
      EqOn J.g.velocityHessian J.w.velocityHessian O := by
  obtain ⟨Ob, hObOpen, hclosureOb, hbOb⟩ :=
    eventually_nhdsSet_iff_exists.mp J.b_one_near_closure_V
  obtain ⟨OtoFun, hOtoFunOpen, hclosureOtoFun, hgOtoFun⟩ :=
    eventually_nhdsSet_iff_exists.mp J.g_toFun_eq_near_closure_V
  obtain ⟨Otime, hOtimeOpen, hclosureOtime, hgOtime⟩ :=
    eventually_nhdsSet_iff_exists.mp J.g_timeDeriv_eq_near_closure_V
  obtain ⟨Ograd, hOgradOpen, hclosureOgrad, hgOgrad⟩ :=
    eventually_nhdsSet_iff_exists.mp J.g_velocityGrad_eq_near_closure_V
  obtain ⟨Ohessian, hOhessianOpen, hclosureOhessian, hgOhessian⟩ :=
    eventually_nhdsSet_iff_exists.mp J.g_velocityHessian_eq_near_closure_V
  let O := Ob ∩ (OtoFun ∩ (Otime ∩ (Ograd ∩ Ohessian)))
  refine ⟨O, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hObOpen.inter (hOtoFunOpen.inter
      (hOtimeOpen.inter (hOgradOpen.inter hOhessianOpen)))
  · intro z hz
    exact ⟨hclosureOb hz, hclosureOtoFun hz,
      hclosureOtime hz, hclosureOgrad hz, hclosureOhessian hz⟩
  · intro z hz
    have hbz := hbOb z hz.1
    have hsupport : z ∈ Function.support J.b := by
      change J.b z ≠ 0
      rw [hbz]
      exact one_ne_zero
    exact J.b_tsupport_subset_W (subset_tsupport (f := J.b) hsupport)
  · intro z hz
    exact hgOtoFun z hz.2.1
  · intro z hz
    exact hgOtime z hz.2.2.1
  · intro z hz
    exact hgOgrad z hz.2.2.2.1
  · intro z hz
    exact hgOhessian z hz.2.2.2.2

end LocalizedParabolicJet

namespace ParabolicW12Loc

/- A local parabolic weak function has a concrete cutoff jet whose literal
mollifications converge uniformly on a compact carrier to any supplied
continuous representative of its restricted-volume almost-everywhere class. -/
end ParabolicW12Loc

end HypoellipticAleksandrov.Parabolic
