module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ExtensionGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Height
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHolds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Alpha
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Setting
import Mathlib.Tactic.Linarith
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Extension
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Shell
import Mathlib.Tactic.Positivity

/-! # Fixed cylinder and genuine interior height points for the Appendix C construction -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Set

/- With a stationary spatial base point, the cylinder is the literal product cylinder. -/
theorem construction_mem_cylinder_iff {d } (T S : ℝ) (hS : 0 < S) (P : KineticPoint d) :
    P ∈ backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S ↔
      T - S ^ 2 < P.time ∧ P.time < T ∧
      PDE.vecEuclideanNorm P.velocity < S ∧ PDE.vecEuclideanNorm P.position < S ^ 3 := by
  simp [backwardCylinder, relativePosition,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hS,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hS 3)]

/- A positive earlier time at the spatial origin belongs to the chosen fixed cylinder. -/
theorem construction_origin_mem_cylinder {d } (T S t )
    (hS : 0 < S) (hTS : T < S ^ 2) (ht : 0 < t) (htT : t < T) :
    (⟨t, 0, 0⟩ : KineticPoint d) ∈ backwardCylinder ⟨T, 0, 0⟩ S := by
  rw [construction_mem_cylinder_iff T S hS]
  refine ⟨by linarith, htT, ?_, ?_⟩
  · simpa [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot] using hS
  · simpa [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot] using pow_pos hS 3

/- Barrier and cylinder radii are chosen once, independently of all flattening scales. -/
theorem construction_fixed_geometry_of_profile {d } (hd : 1 ≤ d) {alpha }
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha) :
    ∃ R mu S : ℝ, 0 < R ∧ 0 < mu ∧ 0 < S ∧
      mu = (d : ℝ) * profileLowerEllipticity h / R ^ 2 ∧
      barrierTime mu < S ^ 2 ∧
      (∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2) ∧
      (∀ q, profileFunction h q ≤ 1 →
        PDE.vecEuclideanNorm q.1 < S ^ 3 ∧ PDE.vecEuclideanNorm q.2 < S) ∧
      (∀ P, 0 ≤ backwardOperator (fun _t x v => profileMatrix h (x, v))
        (barrier mu R) P) := by
  obtain ⟨R, hR, hv⟩ : ∃ R : ℝ, 0 < R ∧ ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2 := by
      obtain ⟨_, _, hc, _, _, _, _, _, _, hcomp, _⟩ := selectedProfile_spec h
      let L := Real.rpow (1 / profileLowerComparison h) alpha⁻¹
      have hL : 0 < L := Real.rpow_pos_of_pos (div_pos zero_lt_one hc) _
      refine ⟨L + 1, by positivity, ?_⟩
      intro q hq
      have hr := profile_sublevel_subset_rho (profileFunction h) alpha
        (profileLowerComparison h) 1 ha hc zero_lt_one (fun y => (hcomp y).1) hq
      have hv := (rho_coordinate_bounds q).2.trans hr
      have hs := sq_le_sq₀ (PDE.vecEuclideanNorm_nonneg q.2) hL.le |>.2 hv
      rw [PDE.vecEuclideanNorm_sq] at hs
      nlinarith

    /- The profile domain lies strictly inside one Euclidean kinetic cylinder radius.
    The time and spatial radii are fixed before the flattening and smoothing scales. -/
  let mu := (d : ℝ) * profileLowerEllipticity h / R ^ 2
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hlam := (selectedProfile_spec h).1
  have hmu := div_pos (mul_pos hd0 hlam) (sq_pos_of_pos hR)
  obtain ⟨S, hS, hTS, hgeom⟩ : ∃ S : ℝ, 0 < S ∧ (barrierTime mu) < S ^ 2 ∧ ∀ q, profileFunction h q ≤ 1 →
      PDE.vecEuclideanNorm q.1 < S ^ 3 ∧ PDE.vecEuclideanNorm q.2 < S := by
    let T := (barrierTime mu)
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
  refine ⟨R, mu, S, hR, hmu, hS, rfl, hTS, hv, hgeom, ?_⟩
  intro P
  exact barrier_operator_nonneg hd (profileMatrix h) (profileLowerEllipticity h)
    R hlam hR (fun q => ((selectedProfile_spec h).2.2.2.2.2.1 q).1) P

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
