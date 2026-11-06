module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileOneAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoWeak
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Profile
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHomogeneousBounds
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileWeakExtension
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! # Assembly of the two exact profile branches -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set
open Filter
open scoped MatrixOrder

/- The higher-dimensional branch yields the shared whole-carrier weak profile. -/
theorem counterProfile_of_branches (d : ℕ) (hd : 1 ≤ d) (alpha )
    (ha : 0 < alpha) (ha1 : alpha < 1)
    (hone : d = 1 → CounterProfileOneStatement alpha)
    (hge : 2 ≤ d → CounterProfileGeTwoStatement d alpha) : CounterProfileStatement d alpha := by
  by_cases hd1 : d = 1
  · subst d
    have h := (hone rfl)
    rcases h with ⟨Lam, c, C, H, gx, gv, hess, hLam, hc, hC, hH, hzero,
      hhom, hcomp, hmx, hmv, hmh, hjets, heq, hgrad, hb, hjhom, hweak, hsmooth⟩
    have hx (i : Fin 1) : LocallyIntegrable (fun q => gx q i) volume := by
      apply homogeneous_component_locallyIntegrable 1 (by omega) (fun q => gx q i)
        ((measurable_pi_apply i).comp hmx) (alpha - 3) (by linarith) (by linarith)
      · intro r hr q
        simpa only [Pi.smul_apply, smul_eq_mul] using congrArg (fun w => w i) (hjhom r hr q).1
      · intro K hK hz
        obtain ⟨M, hM⟩ := hb K hK hz
        exact ⟨M, fun q hq => (by simpa only [Real.norm_eq_abs] using
          (norm_le_pi_norm (gx q) i).trans (hM q hq).1)⟩
    have hv (i : Fin 1) : LocallyIntegrable (fun q => gv q i) volume := by
      apply homogeneous_component_locallyIntegrable 1 (by omega) (fun q => gv q i)
        ((measurable_pi_apply i).comp hmv) (alpha - 1) (by linarith) (by linarith)
      · intro r hr q
        simpa only [Pi.smul_apply, smul_eq_mul] using
          congrArg (fun w => w i) (hjhom r hr q).2.1
      · intro K hK hz
        obtain ⟨M, hM⟩ := hb K hK hz
        exact ⟨M, fun q hq => (by simpa only [Real.norm_eq_abs] using
          (norm_le_pi_norm (gv q) i).trans (hM q hq).2.1)⟩
    have hh (i k : Fin 1) : LocallyIntegrable (fun q => hess q i k) volume := by
      apply homogeneous_component_locallyIntegrable 1 (by omega) (fun q => hess q i k)
        (hmh i k) (alpha - 2) (by linarith) (by linarith)
      · intro r hr q
        simpa only [Matrix.smul_apply, smul_eq_mul] using
          congrArg (fun w => w i k) (hjhom r hr q).2.2
      · intro K hK hz
        obtain ⟨M, hM⟩ := hb K hK hz
        exact ⟨M, fun q hq => (hM q hq).2.2 i k⟩
    refine ⟨1, Lam, c, C, scalarProfileCoefficient Lam, H, gx, gv, hess,
      zero_lt_one, hLam.le, hc, hC, measurable_scalarProfileCoefficient Lam,
      scalarProfileCoefficient_order Lam hLam, hH, hzero, hhom, hcomp,
      hmx, hmv, hmh, hjets, heq, hgrad, hb, hx, hv, hh,
      profile_weak_identities_extend 1 (by omega) H gx gv hess hH hx hv hh hweak,
      (fun hd => by omega), ?_⟩
    filter_upwards [coordinates_ne_zero_ae 1 (by omega)] with q hq
    have hq0 : q.1 0 ≠ 0 := by
      intro hz
      apply hq.1
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi, Pi.zero_apply] using hz
    exact hsmooth.contDiffAt
      ((isOpen_ne.preimage ((continuous_apply 0).comp continuous_fst)).mem_nhds hq0)
  · have hd2 : 2 ≤ d := by omega
    have h := (hge hd2)
    rcases h with ⟨lam, Lam, c, C, A, H, hlam, hLam, hc, hC, hmA, hA, hzero,
      hhom, hcomp, hs, heq, hgrad⟩
    have hd1 : 1 ≤ d := by omega
    have hH : Continuous H := by
      have hc := hc.le
      apply continuous_iff_continuousAt.mpr
      intro q
      by_cases hq : q = 0
      · subst q
        have hmajor : Continuous (fun q : XV d => C * Real.rpow (rho q) alpha) :=
          continuous_const.mul ((continuous_rho d).rpow_const (fun _ => Or.inr ha.le))
        have hm : Tendsto (fun q : XV d => C * Real.rpow (rho q) alpha) (nhds 0) (nhds 0) := by
          simpa only [rho_zero, Real.rpow_eq_pow, Real.zero_rpow ha.ne', mul_zero] using
            hmajor.tendsto 0
        have hz := squeeze_zero (fun q =>
          (mul_nonneg hc (Real.rpow_nonneg (rho_nonneg q) alpha)).trans (hcomp q).1)
          (fun q => (hcomp q).2) hm
        simpa only [ContinuousAt, hzero] using hz
      · exact hs.continuousOn.continuousAt
          (isOpen_compl_singleton.mem_nhds (by simpa using hq))
    obtain ⟨hx, hv, hh⟩ := profile_classical_jets_locallyIntegrable d hd1 H alpha ha ha1 hhom hs
    have heqae : ∀ᵐ q ∂volume, matrixContraction (A q) (dvv H q) = PDE.vecDot q.2 (dx H q) := by
      filter_upwards [coordinates_ne_zero_ae d hd1] with q hq
      exact heq q (fun hz => hq.1 (congrArg Prod.fst hz))
    refine ⟨lam, Lam, c, C, A, H, dx H, dv H, dvv H,
      hlam, hLam, hc, hC, hmA, hA, hH, hzero, hhom, hcomp,
      measurable_dx H, measurable_dv H, measurable_dvv H,
      Filter.Eventually.of_forall (fun _ => ⟨rfl, rfl, rfl⟩), heqae, hgrad,
      profile_jets_compact_bound H hs, hx, hv, hh,
      profile_weak_identities_extend d hd1 H (dx H) (dv H) (dvv H) hH hx hv hh
        (profile_classical_punctured_weak d hd1 H alpha ha ha1 hH hhom hs), (fun _ => hs), ?_⟩
    filter_upwards [coordinates_ne_zero_ae d hd1] with q hq
    have hq0 : q ≠ 0 := fun hz => hq.1 (congrArg Prod.fst hz)
    exact (hs.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hq0))).of_le (by simp)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
