module
public import PottsDiscontinuity.BetheAnsatz.Scattering

/-! # Transfer weights with a movable spectral parameter

The physical row is `v = 1`. Keeping the Bethe roots fixed and moving `v`
makes every gap geometric, even in a sector containing the zero momentum.
The two-body scattering ratio is independent of `v`.
-/
@[expose] public section
open Finset Complex
open scoped Classical
namespace PottsDiscontinuity.BetheAnsatz
noncomputable section

def rowL (Δ v u : ℂ) := ((2*Δ-v)*u-1)/(u-v)
def rowM (Δ v u : ℂ) := (1+u*v-2*Δ*v)/(u-v)

def rowEntry (Δ v : ℂ) (a b k : ℤ) : ℂ :=
  if k = a then v⁻¹ else if k = b then v else v+v⁻¹-2*Δ

private lemma geom_interval (r : ℂ) (hr : r ≠ 0) {a b : ℤ} (hab : a < b) :
    (∑ j ∈ Ioo a b, r^j) * (r-1) = r^b - r^(a+1) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + 1 + n := ⟨(b-a-1).toNat, by omega⟩
  clear hab
  induction n with
  | zero => simp [show Ioo a (a+1) = ∅ by ext; simp]
  | succ n ih =>
    let c := a + 1 + n
    have he : Ioo a (c+1) = insert c (Ioo a c) := by grind
    rw [Nat.cast_succ, ← add_assoc, he, sum_insert (by simp), add_mul, ih]
    grind [zpow_add_one₀ hr c]

/-- Both geometric endpoints in a single gap. -/
lemma row_gap {Δ v u : ℂ} (hv : v ≠ 0) (hu : u ≠ 0) (hne : u ≠ v)
    {a b : ℤ} (hab : a < b) :
    (∑ j ∈ Icc a b, rowEntry Δ v a b j * (u/v)^j) =
      rowL Δ v u * (u/v)^a + rowM Δ v u * (u/v)^b := by
  let r := u/v
  have h := geom_interval r (div_ne_zero hu hv) hab
  rw [zpow_add_one₀ (div_ne_zero hu hv)] at h
  have he : Icc a b = insert a (insert b (Ioo a b)) := by grind
  rw [he, sum_insert (by grind), sum_insert (by simp)]
  have hi : (∑ j ∈ Ioo a b, rowEntry Δ v a b j * r^j) = (v+v⁻¹-2*Δ) * ∑ j ∈ Ioo a b, r^j := by
    rw [mul_sum]; exact sum_congr rfl fun j hj => by grind [rowEntry]
  simp only [rowEntry, ite_true, hab.ne', ite_false] at hi ⊢
  rw [hi]
  unfold rowL rowM
  grind

variable {Δ : ℝ} (hΔ : Δ < -1)
include hΔ

/-- The Bethe scattering identity holds along the whole spectral family. -/
lemma row_scattering {v : ℂ} {x y : ℝ}
    (hx : z x ≠ v) (hy : z y ≠ v) :
    rowM Δ v (z x) * rowL Δ v (z y) - 1 = exp (I * (Bethe.theta Δ x y : ℂ)) *
      (rowM Δ v (z y) * rowL Δ v (z x) - 1) := by
  rw [exp_I_theta_eq_scattering hΔ]
  have hs := mul_ne_zero (z_ne_zero x) (scattering_ne_zero hΔ x y)
  rw [div_mul_eq_mul_div, eq_div_iff hs, z_mul_scattering, z_mul_scattering]
  grind [rowM, rowL]

lemma rowL_phase (t y : ℝ) :
    rowL Δ (z t) (z y) = -exp (I * (Bethe.theta Δ t y : ℂ)) * rowM Δ (z t) (z y) := by
  rw [exp_I_theta_eq_scattering hΔ]
  have h := mul_ne_zero (z_ne_zero t) (scattering_ne_zero hΔ t y)
  grind [z_mul_scattering, rowL, rowM]

end
end PottsDiscontinuity.BetheAnsatz
