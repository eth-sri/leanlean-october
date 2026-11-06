module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ExtensionGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Height
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHolds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Alpha
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Setting
import Mathlib.Tactic.Linarith

/-! # Fixed cylinder and genuine interior height points for the Appendix C construction -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample



variable {d : ℕ}

/-- With a stationary spatial base point, the cylinder is the literal product cylinder. -/
theorem construction_mem_cylinder_iff  (T S : ℝ) (hS : 0 < S) (P : KineticPoint d) :
    P ∈ backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S ↔
      T - S ^ 2 < P.time ∧ P.time < T ∧
      PDE.vecEuclideanNorm P.velocity < S ∧ PDE.vecEuclideanNorm P.position < S ^ 3 := by
  simp [backwardCylinder, relativePosition,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hS,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hS 3)]

/-- A positive earlier time at the spatial origin belongs to the chosen fixed cylinder. -/
theorem construction_origin_mem_cylinder  (T S t : ℝ)
    (hS : 0 < S) (hTS : T < S ^ 2) (ht : 0 < t) (htT : t < T) :
    (⟨t, 0, 0⟩ : KineticPoint d) ∈ backwardCylinder ⟨T, 0, 0⟩ S := by
  rw [construction_mem_cylinder_iff T S hS]
  refine ⟨by linarith, htT, ?_, ?_⟩
  · simpa [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot] using hS
  · simp_all [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]

/-- Barrier and cylinder radii are chosen once, independently of all flattening scales. -/
theorem construction_fixed_geometry_of_profile  (hd : 1 ≤ d) {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha) :
    ∃ R mu S : ℝ, 0 < R ∧ 0 < mu ∧ 0 < S ∧
      mu = (d : ℝ) * profileLowerEllipticity h / R ^ 2 ∧
      barrierTime mu < S ^ 2 ∧
      (∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2) ∧
      (∀ q, profileFunction h q ≤ 1 →
        PDE.vecEuclideanNorm q.1 < S ^ 3 ∧ PDE.vecEuclideanNorm q.2 < S) ∧
      (∀ P, 0 ≤ backwardOperator (fun _t x v => profileMatrix h (x, v))
        (barrier mu R) P) := by
  obtain ⟨R, hR, hv⟩ := exists_profile_barrier_radius ha h
  let mu := (d : ℝ) * profileLowerEllipticity h / R ^ 2

  have hlam := (selectedProfile_spec h).1

  obtain ⟨S, hS, hTS, hgeom⟩ := exists_profile_cylinder_radius ha h (barrierTime mu)
  refine ⟨R, mu, S, hR, (div_pos (mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)) hlam) (sq_pos_of_pos hR)), hS, rfl, hTS, hv, hgeom, ?_⟩
  intro P
  exact barrier_operator_nonneg hd _ _
    R hlam hR (fun q => ((selectedProfile_spec h).2.2.2.2.2.1 q).1) P

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
