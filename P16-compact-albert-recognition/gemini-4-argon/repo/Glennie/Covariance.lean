/- Invariances of the actual native scalar obtained from the proved pair
reduction and literal sector factor. No covariance conclusion is assumed. -/
module
public import Glennie.UnitShifts
public import Glennie.SectorSubspace
public import Mathlib.Tactic.FieldSimp

@[expose] public section
namespace Glennie
noncomputable section

theorem phi_third_add_first (x y z : Albert) (t : ℝ) :
    phi x y (z+t • x) = phi x y z := by
  obtain ⟨g, hx, hy⟩ := universal_pair_reduction x y
  rw [← g.phi_map x y (z+t • x), ← g.phi_map x y z, map_add, map_smul,
    phi_of_diagonal_complex _ _ _ hx hy, phi_of_diagonal_complex _ _ _ hx hy]
  have hm : hiddenMatrix (g.equiv z+t • g.equiv x) = hiddenMatrix (g.equiv z) := by
    change hiddenMatrixLinear (g.equiv z+t • g.equiv x) = hiddenMatrixLinear (g.equiv z)
    rw [map_add, map_smul]
    change hiddenMatrix (g.equiv z)+t • hiddenMatrix (g.equiv x) = hiddenMatrix (g.equiv z)
    rw [hiddenMatrix_eq_zero _ (diagonal_inComplex _ hx), smul_zero, add_zero]
  rw [hm]

theorem phi_first_add_third (x y z : Albert) (t : ℝ) :
    phi (x+t • z) y z = phi x y z := by
  have hzero (u : Albert) : phi u y 0 = 0 := by simpa using phi_smul_third 0 u y 0
  have hdiag (u : Albert) : phi u y u = 0 := by simpa [hzero] using phi_third_add_first u y 0 1
  have hbal (r : ℝ) : r^3 * phi (x + r • z) y z = -phi (x + r • z) y x := by
    by_cases hr : r = 0
    · simp [hr, hdiag]
    have hv : z + (-r⁻¹) • (x + r • z) = (-r⁻¹) • x := by
      simp only [smul_add, smul_smul, neg_mul, inv_mul_cancel₀ hr, neg_one_smul]; abel
    calc r^3 * phi (x + r • z) y z
      _ = r^3 * phi (x + r • z) y (z + (-r⁻¹) • (x + r • z)) := by rw [phi_third_add_first]
      _ = r^3 * ((-r⁻¹)^3 * phi (x + r • z) y x) := by rw [hv, phi_smul_third]
      _ = -phi (x + r • z) y x := by field_simp
  let b := inner (crossU x z (U y z) - U y (crossU x z z)) (U z (jordan x y)) +
    inner (U x (U y z) - U y (U x z)) (U z (jordan z y))
  let c := inner (U z (U y z) - U y (U z z)) (U z (jordan x y)) +
    inner (crossU x z (U y z) - U y (crossU x z z)) (U z (jordan z y))
  let b' := inner (crossU x z (U y x) - U y (crossU x z x)) (U x (jordan x y)) +
    inner (U x (U y x) - U y (U x x)) (U x (jordan z y))
  let c' := inner (U z (U y x) - U y (U z x)) (U x (jordan x y)) +
    inner (crossU x z (U y x) - U y (crossU x z x)) (U x (jordan z y))
  have heq (r : ℝ) : r^3 * (phi x y z + r * b + r^2 * c + r^3 * phi z y z) =
      -(phi x y x + r * b' + r^2 * c' + r^3 * phi z y x) := by
    simpa only [phi_line_first] using hbal r
  have h1 := heq 1; have hm1 := heq (-1)
  have h2 := heq 2; have hm2 := heq (-2)
  have h3 := heq 3; have hm3 := heq (-3)
  norm_num [hdiag] at h1 hm1 h2 hm2 h3 hm3
  rw [phi_line_first]
  change phi x y z + t * b + t^2 * c + t^3 * phi z y z = phi x y z
  rw [show b = 0 by linarith, show c = 0 by linarith, hdiag]
  ring

theorem phi_swap_first_third (x y z : Albert) : phi z y x = -phi x y z := by
  have h1 := phi_first_add_third x y z 1
  have h2 := phi_third_add_first (x+z) y z (-1)
  have h3 := phi_first_add_third (x+z) y (-x) 1
  have ha : z+(-1 : ℝ) • (x+z) = -x := by module
  have hb : x+z+(1 : ℝ) • (-x) = z := by module
  rw [ha] at h2; rw [hb] at h3; simp only [one_smul] at h1
  have hn : phi z y (-x) = -phi z y x := by
    have h := phi_smul_third (-1) z y x
    rw [neg_smul, one_smul] at h; linarith
  linarith

end
end Glennie
