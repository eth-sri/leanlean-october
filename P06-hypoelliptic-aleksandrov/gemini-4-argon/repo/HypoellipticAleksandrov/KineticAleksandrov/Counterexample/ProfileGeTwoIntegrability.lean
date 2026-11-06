module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoHomogeneity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHomogeneousBounds
import Mathlib.Tactic.Linarith
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.GeometryHomogeneity
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoRegularity

/-! # Local integrability of the higher-dimensional profile jets -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set
open Filter

/- All classical profile jets are locally integrable, including at the origin. -/
theorem profile_classical_jets_locallyIntegrable (d ) (hd : 1 ≤ d)
    (H : XV d → ℝ) (alpha ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) :
    (∀ i, LocallyIntegrable (fun q => dx H q i) volume) ∧
    (∀ i, LocallyIntegrable (fun q => dv H q i) volume) ∧
    (∀ i k, LocallyIntegrable (fun q => dvv H q i k) volume) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply homogeneous_component_locallyIntegrable_off_origin d hd (fun q => dx H q i)
      ((measurable_pi_apply i).comp (measurable_dx H))
      (alpha - 3) (by linarith) (by linarith)
    · intro r hr q hq
      exact homogeneous_dx_identity H alpha r hr (hhom r hr) q
        (differentiableAt_profile_off_origin H hs q hq)
        (differentiableAt_profile_off_origin H hs _ (dilate_ne_zero r hr q hq)) i
    · intro K hK hz
      obtain ⟨M, hM⟩ := profile_jets_compact_bound H hs K hK hz
      refine ⟨M, ?_⟩
      intro q hq
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (dx H q) i).trans (hM q hq).1
  · intro i
    apply homogeneous_component_locallyIntegrable_off_origin d hd (fun q => dv H q i)
      ((measurable_pi_apply i).comp (measurable_dv H))
      (alpha - 1) (by linarith) (by linarith)
    · intro r hr q hq
      exact homogeneous_dv_identity H alpha r hr (hhom r hr) q
        (differentiableAt_profile_off_origin H hs q hq)
        (differentiableAt_profile_off_origin H hs _ (dilate_ne_zero r hr q hq)) i
    · intro K hK hz
      obtain ⟨M, hM⟩ := profile_jets_compact_bound H hs K hK hz
      refine ⟨M, ?_⟩
      intro q hq
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (dv H q) i).trans (hM q hq).2.1
  · intro i k
    apply homogeneous_component_locallyIntegrable_off_origin d hd (fun q => dvv H q i k)
      (measurable_dvv H i k) (alpha - 2) (by linarith) (by linarith)
    · intro r hr q hq
      have hhom := (hhom r hr)
      have hg :=
        (contDiffAt_dv_off_origin H hs q hq k).differentiableAt (by simp)
      have hgr : DifferentiableAt ℝ (fun z => dv H z k) (dilate r q) :=
        (contDiffAt_dv_off_origin H hs _ (dilate_ne_zero r hr q hq) k).differentiableAt (by simp)
      have hloc : (fun z => dv H (dilate r z) k) =ᶠ[nhds q]
          (fun z => Real.rpow r (alpha - 1) * dv H z k) := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hq] with z hz
        exact homogeneous_dv_identity H alpha r hr hhom z
          (differentiableAt_profile_off_origin H hs z hz)
          (differentiableAt_profile_off_origin H hs _ (dilate_ne_zero r hr z hz)) k
      have he := congrArg (fun L : XV d →L[ℝ] ℝ => L (0, Pi.single i 1)) hloc.fderiv_eq
      rw [fderiv_fun_comp q hgr (hasFDerivAt_dilate r q).differentiableAt,
        fderiv_const_mul hg, (hasFDerivAt_dilate r q).fderiv] at he
      have hw : dilate r ((0, Pi.single i 1) : XV d) = r • (0, Pi.single i 1) := by
        simp [dilate, Prod.smul_mk]
      simp only [ContinuousLinearMap.comp_apply, dilationLinearMap_apply, smul_apply,
        smul_eq_mul] at he
      rw [hw, map_smul] at he
      change r * dvv H (dilate r q) i k = Real.rpow r (alpha - 1) * dvv H q i k at he
      simp only [Real.rpow_eq_pow] at he ⊢
      rw [show alpha - 2 = (alpha - 1) - 1 by ring, Real.rpow_sub hr, Real.rpow_one,
        div_mul_eq_mul_div]
      apply (eq_div_iff hr.ne').mpr
      simpa only [mul_comm] using he
    · intro K hK hz
      obtain ⟨M, hM⟩ := profile_jets_compact_bound H hs K hK hz
      exact ⟨M, fun q hq => (hM q hq).2.2 i k⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
