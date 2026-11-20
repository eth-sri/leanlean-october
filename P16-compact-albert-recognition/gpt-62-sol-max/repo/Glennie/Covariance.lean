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
  rw [← g.phi_map x y (z+t • x), ← g.phi_map x y z, map_add, map_smul]
  rw [phi_of_diagonal_complex _ _ _ hx hy, phi_of_diagonal_complex _ _ _ hx hy]
  have h := hiddenMatrix_of_inComplex _ (diagonal_inComplex _ hx)
  change sectorHiddenLinear (g.equiv x) = 0 at h
  have hm : hiddenMatrix (g.equiv z+t • g.equiv x) = hiddenMatrix (g.equiv z) :=
    show sectorHiddenLinear (g.equiv z+t • g.equiv x) = sectorHiddenLinear (g.equiv z) by
      simp [h]
  rw [hm]

/-- The degree-three coefficients on the two sides of the shear identity
are negatives of one another. -/
private theorem skew_of_shear {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : E → E → ℝ)
    (hline : ∀ x z v, ∃ b c : ℝ, ∀ t : ℝ,
      F (x + t • z) v = F x v + b*t + c*t^2 + t^3*F z v)
    (hhom : ∀ x z (t : ℝ), F x (t • z) = t^3 * F x z)
    (hshear : ∀ x z (t : ℝ), F x (z + t • x) = F x z)
    (x z : E) : F z x = -F x z := by
  obtain ⟨b,c,hp⟩ := hline x z z
  obtain ⟨d,e,hq⟩ := hline x z x
  have H (r : ℝ) (hr : r ≠ 0) :
      r^3 * (F x z + b*r + c*r^2 + r^3*F z z) =
        -(F x x + d*r + e*r^2 + r^3*F z x) := by
    rw [← hp r, ← hq r, ← hshear (x + r • z) z (-r⁻¹)]
    rw [show z + (-r⁻¹) • (x + r • z) = (-r⁻¹) • x by
      simp [smul_add, smul_smul, hr], hhom]
    field_simp
  linarith only [H 1 (by norm_num), H 2 (by norm_num), H 3 (by norm_num),
    H (-1) (by norm_num), H (-2) (by norm_num), H (-3) (by norm_num)]

theorem phi_swap_first_third (x y z : Albert) : phi z y x = -phi x y z :=
  skew_of_shear (fun a b => phi a y b) (fun a b c => phi_line_first a y b c)
    (fun a b t => phi_smul_third t a y b) (fun a b t => phi_third_add_first a y b t) x z

theorem phi_cyclic (x y z : Albert) : phi y z x = phi x y z := by
  rw [phi_swap_first_two z y x, phi_swap_first_third x y z, neg_neg]

end
end Glennie
