module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueCompactness
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureFubini
import Mathlib.Tactic
public import PDEFoundation.Calculus.RegularityOrder


/-! # The stationary weak equation survives vague convergence -/

 public section

open MeasureTheory Filter
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The source transport and diffusion tests are continuous and compact on the carrier. -/
theorem bellman_stationary_test_properties (phi : (ℝ × ℝ) → ℝ)
    (hphi : ContDiff ℝ PDE.smoothOrder phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ {q | q ≠ (0, 0)}) :
    (Continuous (fun q : BellmanPuncturedPlane =>
      q.val.2 * fderiv ℝ phi q.val (1, 0)) ∧
      HasCompactSupport (fun q : BellmanPuncturedPlane =>
        q.val.2 * fderiv ℝ phi q.val (1, 0))) ∧
    (Continuous (fun q : BellmanPuncturedPlane =>
      fderiv ℝ (fun z => fderiv ℝ phi z (0, 1)) q.val (0, 1)) ∧
      HasCompactSupport (fun q : BellmanPuncturedPlane =>
        fderiv ℝ (fun z => fderiv ℝ phi z (0, 1)) q.val (0, 1))) := by



  have hls : tsupport (fun q  => q.2 * fderiv ℝ phi q (1, 0)) ⊆ tsupport phi :=
    tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ (1, 0))
  have hrs : tsupport (fun q  =>
      fderiv ℝ (fun z => fderiv ℝ phi z (0, 1)) q (0, 1)) ⊆ tsupport phi :=
    (tsupport_fderiv_apply_subset ℝ (0, 1)).trans
      (tsupport_fderiv_apply_subset ℝ (0, 1))
  exact ⟨⟨(continuous_snd.mul (bellman_contDiff_direction hphi (1, 0)).continuous).comp continuous_subtype_val,
      bellman_test_compact_subtype (hc.of_isClosed_subset (isClosed_tsupport _) hls)
        (hls.trans hs)⟩,
    ⟨(bellman_contDiff_direction (bellman_contDiff_direction hphi (0, 1)) (0, 1)).continuous.comp continuous_subtype_val,
      bellman_test_compact_subtype (hc.of_isClosed_subset (isClosed_tsupport _) hrs)
        (hrs.trans hs)⟩⟩

/-- The actual stationary identity passes to the common vague limit. -/
theorem bellman_vague_limit_stationary (mu eta : ℕ → Measure BellmanPuncturedPlane)
    (muInf etaInf : Measure BellmanPuncturedPlane)
    (hstat : ∀ n, IsBellmanStationaryAdjointPair (mu n) (eta n))
    (hmv : IsBellmanVagueLimit mu muInf) (hev : IsBellmanVagueLimit eta etaInf) :
    IsBellmanStationaryAdjointPair muInf etaInf := by
  intro phi hphi hc hs
  obtain ⟨⟨hl, hlc⟩, ⟨hr, hrc⟩⟩ := bellman_stationary_test_properties phi hphi hc hs
  have ht := (hmv _ hl hlc).add (hev _ hr hrc)

  rw [(funext (fun n => hstat n phi hphi hc hs))] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

end HypoellipticAleksandrov.KineticAleksandrov
