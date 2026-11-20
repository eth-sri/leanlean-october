module

public import NormalizerLean.T1General

@[expose] public section

/-!
# Newman's theorem, step 1: normalizing elements are rational up to a scalar ([Nw §2])

If g = [[x, y], [z, w]] normalizes Γ₀(N), the conjugates of T, U, TU are integral, so
x², xz, z², Nyw, Ny², Nw², Nxw, Nxy, Nzw, Nyz are integers.  With t = x (or t = z if x = 0),
N t x, N t y, N t z, N t w are integers, and g = κ·[[α, β/h], [hγ, δ]] with α, β, γ, δ ∈ ℤ
coprime (dividing by the gcd of the entries).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- `r` is an integer. -/
def IsIntR (r : ℝ) : Prop := ∃ m : ℤ, r = m

theorem IsIntR.add {r s : ℝ} (hr : IsIntR r) (hs : IsIntR s) : IsIntR (r + s) := by
  obtain ⟨m, rfl⟩ := hr; obtain ⟨n, rfl⟩ := hs; exact ⟨m + n, by push_cast; ring⟩
theorem IsIntR.sub {r s : ℝ} (hr : IsIntR r) (hs : IsIntR s) : IsIntR (r - s) := by
  obtain ⟨m, rfl⟩ := hr; obtain ⟨n, rfl⟩ := hs; exact ⟨m - n, by push_cast; ring⟩
theorem IsIntR.mul {r s : ℝ} (hr : IsIntR r) (hs : IsIntR s) : IsIntR (r * s) := by
  obtain ⟨m, rfl⟩ := hr; obtain ⟨n, rfl⟩ := hs; exact ⟨m * n, by push_cast; ring⟩
theorem IsIntR.neg {r : ℝ} (hr : IsIntR r) : IsIntR (-r) := by
  obtain ⟨m, rfl⟩ := hr; exact ⟨-m, by push_cast; ring⟩
theorem IsIntR.int (m : ℤ) : IsIntR m := ⟨m, rfl⟩
theorem IsIntR.nat (m : ℕ) : IsIntR m := ⟨m, by simp⟩
theorem IsIntR.one : IsIntR 1 := ⟨1, by simp⟩

theorem isIntR_entries_of_mem {N : ℕ} {γ : SL(2, ℝ)} (hγ : γ ∈ Gamma0R N) (i j : Fin 2) :
    IsIntR ((γ : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  obtain ⟨a, b, c, d, -, -, hm⟩ := exists_entries_of_mem_Gamma0R hγ
  rw [hm]
  fin_cases i <;> fin_cases j <;> simp [IsIntR.int]

/-- T, U, TU ∈ Γ₀(N). -/
def matT : SL(2, ℝ) := ⟨!![1, 1; 0, 1], by simp [det_fin_two_of]⟩
def matU (N : ℕ) : SL(2, ℝ) := ⟨!![1, 0; (N : ℝ), 1], by simp [det_fin_two_of]⟩

theorem coe_conj (g Y : SL(2, ℝ)) :
    ((g * Y * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      (g : Matrix (Fin 2) (Fin 2) ℝ) * (Y : Matrix (Fin 2) (Fin 2) ℝ) *
        (g : Matrix (Fin 2) (Fin 2) ℝ).adjugate := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]

end

end NormalizerLean
