module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Profile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHomogeneousBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileWeakExtension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity



/-! # Scalar branch assembly into the shared profile interface -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set
open scoped MatrixOrder

/-- Scalar multiples of the identity preserve the scalar order. -/
theorem scalar_identity_le {d : ℕ} (a b : ℝ) (hab : a ≤ b) :
    a • (1 : PDE.Mat d) ≤ b • (1 : PDE.Mat d) := (smul_one_mono (PDE.Mat d) hab)

variable (Lam : ℝ)

/-- The literal scalar coefficient is entrywise measurable. -/
theorem measurable_scalarProfileCoefficient  (i k : Fin 1) :
    Measurable (fun q => scalarProfileCoefficient Lam q i k) := (Measurable.mul
  (Measurable.ite
    (measurableSet_lt
      (Measurable.mul (Measurable.comp (measurable_pi_apply 0) measurable_fst)
        (Measurable.comp (measurable_pi_apply 0) measurable_snd))
      measurable_const)
    measurable_const measurable_const)
  measurable_const)

/-- The scalar coefficient has the source's uniform ellipticity bounds everywhere. -/
theorem scalarProfileCoefficient_order  (hLam : 1 < Lam) (q : XV 1) :
    (1 : ℝ) • (1 : PDE.Mat 1) ≤ scalarProfileCoefficient Lam q ∧
      scalarProfileCoefficient Lam q ≤ Lam • (1 : PDE.Mat 1) := by
  unfold scalarProfileCoefficient
  split_ifs
  · exact ⟨scalar_identity_le 1 Lam hLam.le, le_refl _⟩
  · exact ⟨le_refl _, scalar_identity_le 1 Lam hLam.le⟩

/-- The scalar branch yields the whole-carrier profile with no additional analytic premises. -/
theorem counterProfile_one (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileOneStatement alpha) : CounterProfileStatement 1 alpha := by
  rcases h with ⟨Lam, c, C, H, gx, gv, hess, hLam, hc, hC, hH, hzero,
    hhom, hcomp, hmx, hmv, hmh, hjets, heq, hgrad, hb, hjhom, hweak, hsmooth⟩
  have hx (i : Fin 1) : LocallyIntegrable (fun q => gx q i)  := by
    apply homogeneous_component_locallyIntegrable 1 (by omega) (fun q => gx q i)
      ((measurable_pi_apply i).comp hmx) (alpha - 3) (by linarith) (by linarith)
    · intro r hr q
      exact congrArg (fun w => w i) (hjhom r hr q).1
    · intro K hK hz
      obtain ⟨M, hM⟩ := hb K hK hz
      exact ⟨M, fun q hq => ((norm_le_pi_norm (gx q) i).trans (hM q hq).1)⟩
  have hv (i : Fin 1) : LocallyIntegrable (fun q => gv q i)  := by
    apply homogeneous_component_locallyIntegrable 1 (by omega) (fun q => gv q i)
      ((measurable_pi_apply i).comp hmv) (alpha - 1) (by linarith) (by linarith)
    · intro r hr q
      exact congrArg (fun w => w i) (hjhom r hr q).2.1
    · intro K hK hz
      obtain ⟨M, hM⟩ := hb K hK hz
      exact ⟨M, fun q hq => ((norm_le_pi_norm (gv q) i).trans (hM q hq).2.1)⟩
  have hh (i k : Fin 1) : LocallyIntegrable (fun q => hess q i k)  := by
    apply homogeneous_component_locallyIntegrable 1 (by omega) (fun q => hess q i k)
      (hmh i k) (alpha - 2) (by linarith) (by linarith)
    · intro r hr q
      exact congrArg (fun w => w i k) (hjhom r hr q).2.2
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

  exact hsmooth.contDiffAt
    ((isOpen_ne.preimage ((continuous_apply 0).comp continuous_fst)).mem_nhds (show q.1 0 ≠ 0 by
        intro hz
        apply hq.1
        ext i

        simpa only [(show i = 0 from Subsingleton.elim _ _), Pi.zero_apply] using hz))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
