module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.Ideals.BoundedNormFinsets

@[expose] public section


namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

section
variable {F : Type*} [Field F] [NumberField F]
include F
noncomputable def idealDivisors  
    (A : Ideal (𝓞 F))  :=
  if A = ⊥ then ∅ else
    (boundedNormIdeals F (Ideal.absNorm A : ℝ)).filter (fun D => D ∣ A)

@[simp]
theorem mem_idealDivisors  
    {A D : Ideal (𝓞 F)} (hA : A ≠ ⊥) :
    D ∈ idealDivisors A ↔ D ∣ A := by
  rw [idealDivisors, if_neg hA, Finset.mem_filter, mem_boundedNormIdeals]
  refine ⟨fun h => h.2, fun hdvd => ⟨?_, hdvd⟩⟩
  have hpos : 0 < Ideal.absNorm A :=
    Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hA)
  have hdvdn  :=
    Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hdvd)
  exact_mod_cast Nat.le_of_dvd hpos hdvdn

theorem ne_bot_of_mem_idealDivisors  
    {A D : Ideal (𝓞 F)} (hD : D ∈ idealDivisors A) : D ≠ ⊥ := by
  by_cases hA : A = ⊥
  · simp [idealDivisors, hA] at hD
  · intro hDb
    have hle  := Ideal.dvd_iff_le.mp ((mem_idealDivisors hA).mp hD)
    rw [hDb] at hle
    apply hA <;> aesop

theorem absNorm_le_of_mem_idealDivisors  
    {A D : Ideal (𝓞 F)} (hD : D ∈ idealDivisors A) :
    Ideal.absNorm D ≤ Ideal.absNorm A := by
  by_cases hA : A = ⊥
  · simp [idealDivisors, hA] at hD
  · have hpos : 0 < Ideal.absNorm A :=
      Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hA)
    exact Nat.le_of_dvd hpos
      (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp ((mem_idealDivisors hA).mp hD)))

@[simp]
theorem idealDivisors_bot   :
    idealDivisors (⊥ : Ideal (𝓞 F)) = ∅ := by
  simp [idealDivisors]

















noncomputable def idealDivisorCount  
    (A : Ideal (𝓞 F))  :=
  (idealDivisors A).card
end


end DedekindZetaZeroFree.LargeSieve
