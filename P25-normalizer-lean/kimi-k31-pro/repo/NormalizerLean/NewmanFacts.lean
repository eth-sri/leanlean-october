module

public import NormalizerLean.NewmanVal

@[expose] public section

/-!
# Newman's theorem, step 2 continued: the integer divisibilities

For g = κ·S ∈ Norm(Γ₀(N)), S = [[α, β/h], [hγ, δ]], e = αδ − βγ, with h = h(N), n = n(N),
ε = gcd(N, 24):

* F1  e ∣ h·αγ        F2  e ∣ α²          F3  eN ∣ h²γ²         F4  eε ∣ 2h·αγ
* F5  e ∣ nh·βδ       F6  e ∣ n·β²        F7  e ∣ δ²            F8  eε ∣ 2nh·βδ
* F9  e ∣ N·βγ        F10 eh ∣ N·αβ       F11 eN ∣ Nh·γδ        F12 eε ∣ 2N·βγ
* and, for [[x, y], [N, t]] ∈ Γ₀(N) and s = t − x, the same four with s in place of N.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

theorem int_eq_of_real {e X a : ℤ} (he : e ≠ 0) (h : ((e : ℝ))⁻¹ * (X : ℝ) = a) : X = e * a := by
  have her : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have : (X : ℝ) = e * a := by rw [← h]; field_simp
  exact_mod_cast this

theorem int_eq_of_real_div {e X a : ℤ} {d : ℕ} (he : e ≠ 0) (hd : d ≠ 0)
    (h : ((e : ℝ))⁻¹ * ((X : ℝ) / d) = a) : X = e * d * a := by
  have her : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have hdr : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have : (X : ℝ) = e * d * a := by rw [← h]; field_simp
  exact_mod_cast this

end

end NormalizerLean
