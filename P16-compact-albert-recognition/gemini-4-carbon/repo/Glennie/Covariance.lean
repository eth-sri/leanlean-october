module
public import Glennie.UnitShifts
public import Glennie.SectorModel

@[expose] public section
namespace Glennie
noncomputable section

theorem phi_third_add_first (x y z : Albert) (t : ℝ) :
    phi x y (z + t • x) = phi x y z := by
  obtain ⟨g, hx, hy⟩ := universal_pair_reduction x y
  rw [← g.phi_map x y (z + t • x), ← g.phi_map x y z, map_add, map_smul,
    phi_of_diagonal_complex _ _ _ hx hy, phi_of_diagonal_complex _ _ _ hx hy]
  have hm : hiddenMatrix (g.equiv z + t • g.equiv x) = hiddenMatrix (g.equiv z) := by
    change hiddenMatrixLinear (g.equiv z + t • g.equiv x) = hiddenMatrixLinear (g.equiv z)
    rw [map_add, map_smul]
    change hiddenMatrix (g.equiv z) + t • hiddenMatrix (g.equiv x) = hiddenMatrix (g.equiv z)
    rw [hiddenMatrix_eq_zero _ (diagonal_inComplex _ hx), smul_zero, add_zero]
  rw [hm]

theorem phi_first_add_third (x y z : Albert) (t : ℝ) :
    phi (x + t • z) y z = phi x y z := by
  have hbal (r : ℝ) (hr : r ≠ 0) : r ^ 3 * phi (x + r • z) y z + phi (x + r • z) y x = 0 := by
    have hv : z + (-r⁻¹) • (x + r • z) = (-r⁻¹) • x := by
      simp only [smul_add, smul_smul, neg_mul, inv_mul_cancel₀ hr, neg_one_smul]; abel
    rw [← phi_third_add_first (x + r • z) y z (-r⁻¹), hv, phi_smul_third]; field_simp; ring
  let b1 (w : Albert) := inner (crossU x z (U y w) - U y (crossU x z w)) (U w (jordan x y)) +
    inner (U x (U y w) - U y (U x w)) (U w (jordan z y))
  let b2 (w : Albert) := inner (U z (U y w) - U y (U z w)) (U w (jordan x y)) +
    inner (crossU x z (U y w) - U y (crossU x z w)) (U w (jordan z y))
  have hl (w : Albert) (r : ℝ) :
      phi (x + r • z) y w = phi x y w + r * b1 w + r ^ 2 * b2 w + r ^ 3 * phi z y w :=
    phi_line_first x y z w r
  have he (r : ℝ) (hr : r ≠ 0) :
      r ^ 3 * (phi x y z + r * b1 z + r ^ 2 * b2 z + r ^ 3 * phi z y z) +
        (phi x y x + r * b1 x + r ^ 2 * b2 x + r ^ 3 * phi z y x) = 0 := by
    rw [← hl, ← hl]; exact hbal r hr
  have h1 := he 1 (by norm_num); have hm1 := he (-1) (by norm_num)
  have h2 := he 2 (by norm_num); have hm2 := he (-2) (by norm_num)
  have h3 := he 3 (by norm_num); have hm3 := he (-3) (by norm_num)
  have h4 := he 4 (by norm_num); have hm4 := he (-4) (by norm_num)
  norm_num at h1 hm1 h2 hm2 h3 hm3 h4 hm4
  rw [hl z t, show b1 z = 0 by linarith, show b2 z = 0 by linarith, show phi z y z = 0 by linarith]
  ring

theorem phi_swap_first_third (x y z : Albert) : phi z y x = -phi x y z := by
  have h1 := phi_first_add_third x y z 1
  have h2 := phi_third_add_first (x + z) y z (-1)
  have h3 := phi_first_add_third (x + z) y (-x) 1
  rw [show z + (-1 : ℝ) • (x + z) = -x by module] at h2
  rw [show x + z + (1 : ℝ) • (-x) = z by module] at h3
  simp only [one_smul] at h1
  have hn := phi_smul_third (-1) z y x
  rw [neg_smul, one_smul] at hn
  linarith

end
end Glennie
