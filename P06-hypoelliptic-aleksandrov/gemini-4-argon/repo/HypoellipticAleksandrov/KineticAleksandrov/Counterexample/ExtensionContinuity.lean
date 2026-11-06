module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffOperator

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeRegularityExtension
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.DenselyOrdered

/-! # Continuity and compact support of the actual zero extension -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set

/- For each time, the actual zero extension is continuous across the profile boundary. -/
theorem continuous_zeroExtendedProfile_spatial_of_profile {d alpha}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) (hr : 0 < r)
    (hmu : 0 < mu) (hR : 0 < R) (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2) (t : ℝ) :
    Continuous (fun q : XV d =>
      zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, q.1, q.2⟩) := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  let Omega := {q | profileFunction h q < 1}
  have he : (fun q : XV d =>
      zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, q.1, q.2⟩) =
      Omega.piecewise (fun q => timeCutoffProfile (profileFunction h) alpha r mu R
        ⟨t, q.1, q.2⟩) (fun _ => 0) := by
    funext q
    by_cases hq : q ∈ Omega
    · rw [piecewise_eq_of_mem Omega _ _ hq]
      exact zeroExtendedProfile_eq_raw_on_profile _ alpha r mu R hr hmu hR hvel _ hq
    · rw [piecewise_eq_of_notMem Omega _ _ hq]
      exact zeroExtendedProfile_eq_zero_of_profile _ alpha r mu R _ (not_lt.mp hq)
  rw [he]
  apply Continuous.piecewise ?_ ?_ continuous_const
  · intro q hq
    have hb := hH.frontier_preimage_subset (Iio 1) hq
    have hq1 : profileFunction h q = 1 := by
      simpa only [frontier_Iio, mem_preimage, mem_singleton_iff] using hb
    have hf := flatProfile_eq_one_sub (profileFunction h) alpha r hr q (hscale.trans hq1.ge)
    have hpos : 0 < barrier mu R ⟨t, q.1, q.2⟩ := by
      have hv := hvel q hq1.le
      have hv1 := (div_lt_one (sq_pos_of_pos hR)).mpr hv
      unfold barrier
      exact mul_pos (Real.exp_pos _) (by linarith)
    unfold timeCutoffProfile
    rw [hf, hq1, sub_self]
    exact timeCutoffTheta_eq_zero _ (by linarith)
  · simpa only [timeCutoffProfile, selectedFlatProfile, barrier] using!
      contDiff_timeCutoffTheta.continuous.comp
        ((continuous_selectedFlatProfile h r).sub
          (contDiff_nativeBarrier d mu R t).continuous)

/- The fixed compact unit profile sublevel contains the support at every time. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
