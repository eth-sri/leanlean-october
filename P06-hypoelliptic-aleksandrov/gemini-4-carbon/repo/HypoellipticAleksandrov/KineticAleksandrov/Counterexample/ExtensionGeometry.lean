module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoff
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Shell
import Mathlib.Tactic.Positivity

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set

/-- Extension by zero outside the positive-time profile domain. -/
def zeroExtendedProfile {d : ℕ} (H : XV d → ℝ) (alpha r mu R : ℝ)
    (P : KineticPoint d) : ℝ :=
  if 0 < P.time ∧ H (P.position, P.velocity) < 1 then
    timeCutoffProfile H alpha r mu R P else 0

/-- The extension is globally nonnegative. -/
theorem zeroExtendedProfile_nonneg {d : ℕ} (H : XV d → ℝ) (alpha r mu R : ℝ)
    (P : KineticPoint d) : 0 ≤ zeroExtendedProfile H alpha r mu R P := by
  unfold zeroExtendedProfile
  split
  · exact timeCutoffProfile_nonneg H alpha r mu R P
  · exact le_refl 0

/-- The extension vanishes at every nonpositive time. -/
theorem zeroExtendedProfile_eq_zero_of_time {d : ℕ} (H : XV d → ℝ)
    (alpha r mu R : ℝ) (P : KineticPoint d) (ht : P.time ≤ 0) :
    zeroExtendedProfile H alpha r mu R P = 0 := by
  simp [zeroExtendedProfile, not_lt.mpr ht]

/-- The extension vanishes everywhere outside the profile domain. -/
theorem zeroExtendedProfile_eq_zero_of_profile {d : ℕ} (H : XV d → ℝ)
    (alpha r mu R : ℝ) (P : KineticPoint d) (hH : 1 ≤ H (P.position, P.velocity)) :
    zeroExtendedProfile H alpha r mu R P = 0 := by
  simp [zeroExtendedProfile, not_lt.mpr hH]

/-- The flattened profile never exceeds one, independently of the profile value. -/
theorem flatProfile_le_one {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ) (hr : 0 < r)
    (q : XV d) : flatProfile H flatteningPsi flatteningOffset alpha r q ≤ 1 := by
  have hpow := (Real.rpow_pos_of_pos hr alpha).le
  have hc : 0 ≤ flatteningOffset := (by linarith [flatteningOffset_bounds.1])
  have h1 := mul_nonneg hc hpow
  have h2 := mul_nonneg hpow (flatteningPsi_nonneg (H q / Real.rpow r alpha))
  unfold flatProfile
  simp at *
  linarith


/-- The closed unit profile sublevel is compact, with the native Euclidean gauge. -/
theorem isCompact_profile_unit_sublevel {d : ℕ} {alpha : ℝ} (ha : 0 < alpha)
    (h : CounterProfileStatement d alpha) : IsCompact {q | profileFunction h q ≤ 1} := by
  obtain ⟨_, _, hc, _, _, _, hH, _, _, hcomp, _⟩ := selectedProfile_spec h
  exact (isCompact_rho_sublevel d
    (Real.rpow (1 / profileLowerComparison h) alpha⁻¹)).of_isClosed_subset
    (isClosed_le hH continuous_const)
    (profile_sublevel_subset_rho _ alpha _ 1 ha hc zero_lt_one (fun q => (hcomp q).1))

/-- One fixed radius strictly bounds every velocity in the closed profile domain. -/
theorem exists_profile_barrier_radius {d : ℕ} {alpha : ℝ} (ha : 0 < alpha)
    (h : CounterProfileStatement d alpha) :
    ∃ R : ℝ, 0 < R ∧ ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2 := by
  obtain ⟨_, _, hc, _, _, _, _, _, _, hcomp, _⟩ := selectedProfile_spec h
  let L := Real.rpow (1 / profileLowerComparison h) alpha⁻¹
  have hL : 0 < L := Real.rpow_pos_of_pos (div_pos zero_lt_one hc) _
  refine ⟨L + 1, by positivity, ?_⟩
  intro q hq
  have hv := (rho_coordinate_bounds q).2.trans (profile_sublevel_subset_rho (profileFunction h) alpha (profileLowerComparison h) 1 ha hc zero_lt_one (fun y => (hcomp y).1) hq)
  have hs := sq_le_sq₀ (PDE.vecEuclideanNorm_nonneg q.2) hL.le |>.2 hv
  rw [PDE.vecEuclideanNorm_sq] at hs
  nlinarith

/-- The profile domain lies strictly inside one Euclidean kinetic cylinder radius.
The time and spatial radii are fixed before the flattening and smoothing scales. -/
theorem exists_profile_cylinder_radius {d : ℕ} {alpha : ℝ} (ha : 0 < alpha)
    (h : CounterProfileStatement d alpha) (T : ℝ) :
    ∃ S : ℝ, 0 < S ∧ T < S ^ 2 ∧ ∀ q, profileFunction h q ≤ 1 →
      PDE.vecEuclideanNorm q.1 < S ^ 3 ∧ PDE.vecEuclideanNorm q.2 < S := by
  obtain ⟨_, _, hc, _, _, _, _, _, _, hcomp, _⟩ := selectedProfile_spec h
  let L := Real.rpow (1 / profileLowerComparison h) alpha⁻¹
  have hL : 0 < L := Real.rpow_pos_of_pos (div_pos zero_lt_one hc) _
  let S := L + |T| + 2
  have hS : 0 < S := by dsimp [S]; positivity
  have hLS : L < S := by dsimp [S]; linarith [abs_nonneg T]
  refine ⟨S, hS, ?_, ?_⟩
  · have ht : T ≤ |T| := le_abs_self T
    have hbig : |T| + 2 ≤ S := by dsimp [S]; linarith
    nlinarith [abs_nonneg T]
  · intro q hq
    have hr := profile_sublevel_subset_rho (profileFunction h) alpha
      (profileLowerComparison h) 1 ha hc zero_lt_one (fun y => (hcomp y).1) hq
    have hb := rho_coordinate_bounds q
    exact ⟨lt_of_le_of_lt (hb.1.trans (pow_le_pow_left₀ (rho_nonneg q) hr 3))
      (pow_lt_pow_left₀ hLS hL.le (by decide)), lt_of_le_of_lt (hb.2.trans hr) hLS⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

