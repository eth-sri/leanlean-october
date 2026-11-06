module

public import PottsDiscontinuity.Bethe.AsymptoticOffset

/-! # Alignment estimates before the offset Taylor expansion -/

public section

open Set

namespace PottsDiscontinuity.Bethe

theorem averaged_spacing_error {Δ N x₀ x₁ x₀' x₁' A D : ℝ}
    {L : NNReal}
    (hL : LipschitzOnWith L (fun z => (rho Δ z)⁻¹) (Icc (-Real.pi) Real.pi))
    (hx₀ : x₀ ∈ Icc (-Real.pi) Real.pi) (hx₁ : x₁ ∈ Icc (-Real.pi) Real.pi)
    (horder : x₀ ≤ x₁) (hgap : x₁ - x₀ ≤ D / N)
    (h₀ : |N * (x₀' - x₀) - (rho Δ x₀)⁻¹| ≤ A / N)
    (h₁ : |N * (x₁' - x₁) - (rho Δ x₁)⁻¹| ≤ A / N) :
    |N * ((x₀' + x₁') / 2 - (x₀ + x₁) / 2) -
      (rho Δ ((x₀ + x₁) / 2))⁻¹| ≤ (A + (L : ℝ) * D) / N := by
  let z := (x₀ + x₁) / 2
  have hz : z ∈ Icc (-Real.pi) Real.pi := by grind
  have hd₀ : |x₀ - z| ≤ D / N := by grind
  have hd₁ : |x₁ - z| ≤ D / N := by grind
  have hl₀ := hL.dist_le_mul x₀ hx₀ z hz
  have hl₁ := hL.dist_le_mul x₁ hx₁ z hz
  rw [Real.dist_eq, Real.dist_eq] at hl₀ hl₁
  have hl₀' := hl₀.trans (mul_le_mul_of_nonneg_left hd₀ L.coe_nonneg)
  have hl₁' := hl₁.trans (mul_le_mul_of_nonneg_left hd₁ L.coe_nonneg)
  have hb₁ := abs_add_le (N * (x₁' - x₁) - (rho Δ x₁)⁻¹)
    ((rho Δ x₁)⁻¹ - (rho Δ z)⁻¹)
  have hb := abs_add_le (N * (x₀' - x₀) - (rho Δ z)⁻¹)
    (N * (x₁' - x₁) - (rho Δ z)⁻¹)
  have heq : N * ((x₀' + x₁') / 2 - (x₀ + x₁) / 2) - (rho Δ z)⁻¹ =
      ((N * (x₀' - x₀) - (rho Δ z)⁻¹) +
        (N * (x₁' - x₁) - (rho Δ z)⁻¹)) / 2 := by ring
  rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  grind

section
variable {N r : ℕ}
/-- Local spacing information in the full configuration also controls the
spacing of the aligned roots in the odd case. -/
theorem alignedRoot_spacing (hr : r ≤ N / 2) (hN : 0 < N)
    {p : Fin (N / 2) → ℝ} (hp : p ∈ S_n (N / 2))
    {Δ A D : ℝ} (hD : 0 ≤ D) {L : NNReal}
    (hL : LipschitzOnWith L (fun z => (rho Δ z)⁻¹) (Icc (-Real.pi) Real.pi))
    (hspacing : ∀ j (hj : j + 1 < N / 2),
      |(N : ℝ) * (p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩) -
        (rho Δ (p ⟨j, by omega⟩))⁻¹| ≤ A / N)
    (hgap : ∀ j (hj : j + 1 < N / 2),
      p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩ ≤ D / N)
    (j : ℕ) (hj : j + 1 < N / 2 - r) :
    |(N : ℝ) * (alignedRoot N r hr p ⟨j + 1, hj⟩ -
      alignedRoot N r hr p ⟨j, by omega⟩) -
      (rho Δ (alignedRoot N r hr p ⟨j, by omega⟩))⁻¹| ≤
      (A + (L : ℝ) * D) / N := by
  unfold alignedRoot
  split
  next he =>
    have hi := hspacing (j + r / 2) (by omega)
    have heq : j + 1 + r / 2 = j + r / 2 + 1 := by omega
    simp only [heq]
    exact hi.trans ((div_le_div_iff_of_pos_right (Nat.cast_pos.mpr hN)).mpr
      (by nlinarith))
  next ho =>
    have hg := hgap (j + (r - 1) / 2) (by omega)
    have heq : j + (r - 1) / 2 + 1 = j + (r + 1) / 2 := by omega
    have hidx : (⟨j + (r - 1) / 2 + 1, by omega⟩ : Fin (N / 2)) =
        ⟨j + (r + 1) / 2, by omega⟩ := Fin.ext heq
    rw [hidx] at hg
    have ho' :=
      (hp.2.1 (show (⟨j + (r - 1) / 2, by omega⟩ : Fin (N / 2)) <
        ⟨j + (r + 1) / 2, by omega⟩ from by
          grind)).le
    have hb := averaged_spacing_error hL
      (show p ⟨j + (r - 1) / 2, by omega⟩ ∈ Icc (-Real.pi) Real.pi from
        ⟨(hp.1 _).1.le, (hp.1 _).2.le⟩)
      (show p ⟨j + (r + 1) / 2, by omega⟩ ∈ Icc (-Real.pi) Real.pi from
        ⟨(hp.1 _).1.le, (hp.1 _).2.le⟩) ho' hg (hspacing (j + (r - 1) / 2) (by omega)) (hspacing (j + (r + 1) / 2) (by omega))
    grind

/-- The actual corrected displacement satisfies the non-circular recurrence,
for both parities of `r`. -/
theorem offsetDisplacement_increment (h4 : 4 ∣ N)
    (hr : r ≤ N / 2) (hN : 0 < N)
    {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hp : p ∈ S_n (N / 2)) (hq : q ∈ S_n (N / 2 - r))
    {Δ A B D : ℝ} (hD : 0 ≤ D) {L : NNReal}
    (hL : LipschitzOnWith L (fun z => (rho Δ z)⁻¹) (Icc (-Real.pi) Real.pi))
    (hpSpacing : ∀ j (hj : j + 1 < N / 2),
      |(N : ℝ) * (p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩) -
        (rho Δ (p ⟨j, by omega⟩))⁻¹| ≤ A / N)
    (hqSpacing : ∀ j (hj : j + 1 < N / 2 - r),
      |(N : ℝ) * (q ⟨j + 1, hj⟩ - q ⟨j, by omega⟩) -
        (rho Δ (q ⟨j, by omega⟩))⁻¹| ≤ B / N)
    (hpGap : ∀ j (hj : j + 1 < N / 2),
      p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩ ≤ D / N)
    (j : ℕ) (hj : j + 1 < N / 2 - r) :
    |offsetDisplacement N r h4 hr p q ⟨j + 1, hj⟩ -
      offsetDisplacement N r h4 hr p q ⟨j, by omega⟩| ≤
      (A + (L : ℝ) * D + B) / N + (L : ℝ) / N *
        |offsetDisplacement N r h4 hr p q ⟨j, by omega⟩| := by
  simpa only [offsetDisplacement_eq_alignedRoot] using
    offset_increment_from_spacing (Nat.cast_pos.mpr hN) hL
      (alignedRoot_mem_Icc hr hp ⟨j, by omega⟩)
      (show q ⟨j, by omega⟩ ∈ Icc (-Real.pi) Real.pi from ⟨(hq.1 _).1.le, (hq.1 _).2.le⟩)
      (alignedRoot_spacing hr hN hp hD hL hpSpacing hpGap j hj) (hqSpacing j hj)
end

end PottsDiscontinuity.Bethe
