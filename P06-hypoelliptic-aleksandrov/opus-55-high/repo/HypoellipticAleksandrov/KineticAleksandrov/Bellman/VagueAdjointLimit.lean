module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitDegree
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitStationary
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitScaling
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureFubini
import Mathlib.Tactic

/-! # Normalized vague limits retain the complete homogeneous adjoint-pair condition -/

@[expose] public section
open Set MeasureTheory Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- A fixed compact normalization survives the limit and prevents a zero adjoint pair. -/
theorem bellman_vague_limit_pair (R betaInf : ℝ) (_hR : 1 ≤ R)
    (beta : ℕ → ℝ) (mu eta : ℕ → Measure BellmanPuncturedPlane)
    (muInf etaInf : Measure BellmanPuncturedPlane)
    (hbeta : Tendsto beta atTop (𝓝 betaInf))
    (hp : ∀ n, IsBellmanAdjointPair 1 R (beta n) (mu n) (eta n))
    (hmInf : IsBellmanRadon muInf) (heInf : IsBellmanRadon etaInf)
    (hmv : IsBellmanVagueLimit mu muInf) (hev : IsBellmanVagueLimit eta etaInf)
    (chi : (ℝ × ℝ) → ℝ) (hchi : Continuous chi) (hc : HasCompactSupport chi)
    (hs : tsupport chi ⊆ {q | q ≠ (0, 0)})
    (hone : ∀ n, ∫ q, chi q.val ∂mu n = 1) :
    IsBellmanAdjointPair 1 R betaInf muInf etaInf ∧
      (∫ q, chi q.val ∂muInf) = 1 := by
  have ht := hmv (fun q => chi q.val) (hchi.comp continuous_subtype_val)
    (bellman_test_compact_subtype hc hs)
  have hn : (∫ q, chi q.val ∂muInf) = 1 := by
    simp_all
  have hnonzero : muInf ≠ 0 := by
    aesop
  have hlo : muInf ≤ etaInf := bellman_vague_limit_le mu eta muInf etaInf
    (fun n => (hp n).2.1.1) hmInf heInf hmv hev
    (fun n => by simpa using (hp n).2.2.2.1)
  have hhi  := bellman_vague_limit_le eta
    _ etaInf _
    (fun n => ((hp n).1.smul _ ENNReal.ofReal_ne_top).1)
    heInf (hmInf.smul _ ENNReal.ofReal_ne_top) hev (hmv.smul _) (fun n => (hp n).2.2.2.2.1)
  have hstat := bellman_vague_limit_stationary mu eta muInf etaInf
    (fun n => (hp n).2.2.2.2.2.1) hmv hev
  have hdm := bellman_vague_limit_degree beta betaInf mu muInf hbeta
    (fun n => (hp n).2.2.2.2.2.2.1) hmInf hmv
  have hde := bellman_vague_limit_degree beta betaInf eta etaInf hbeta
    (fun n => (hp n).2.2.2.2.2.2.2) heInf hev
  exact ⟨⟨hmInf, heInf, Or.inl hnonzero, by
    simp_all, hhi, hstat, hdm, hde⟩, hn⟩

end HypoellipticAleksandrov.KineticAleksandrov
