module

public import DedekindZetaZeroFree.Arithmetic.Ideals.BoundedNormFinsets

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

noncomputable def idealDivisors {F : Type*} [Field F] [NumberField F]
    (A : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) :=
  if A = ⊥ then ∅ else
    (boundedNormIdeals F (Ideal.absNorm A : ℝ)).filter (fun D => D ∣ A)

@[simp]
theorem mem_idealDivisors {F : Type*} [Field F] [NumberField F]
    {A D : Ideal (𝓞 F)} (hA : A ≠ ⊥) :
    D ∈ idealDivisors A ↔ D ∣ A := by
  rw [idealDivisors, if_neg hA, Finset.mem_filter, mem_boundedNormIdeals]
  refine ⟨fun h => h.2, fun hdvd => ⟨?_, hdvd⟩⟩
  have hpos : 0 < Ideal.absNorm A :=
    Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hA)
  have hdvdn : Ideal.absNorm D ∣ Ideal.absNorm A :=
    Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hdvd)
  exact_mod_cast Nat.le_of_dvd hpos hdvdn

theorem ne_bot_of_mem_idealDivisors {F : Type*} [Field F] [NumberField F]
    {A D : Ideal (𝓞 F)} (hD : D ∈ idealDivisors A) : D ≠ ⊥ := by
  by_cases hA : A = ⊥
  · simp [idealDivisors, hA] at hD
  · intro hDb
    have hle : A ≤ D := Ideal.dvd_iff_le.mp ((mem_idealDivisors hA).mp hD)
    simp_all

theorem absNorm_le_of_mem_idealDivisors {F : Type*} [Field F] [NumberField F]
    {A D : Ideal (𝓞 F)} (hD : D ∈ idealDivisors A) :
    Ideal.absNorm D ≤ Ideal.absNorm A := by
  by_cases hA : A = ⊥
  · simp [idealDivisors, hA] at hD
  · have hpos : 0 < Ideal.absNorm A :=
      Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hA)
    exact Nat.le_of_dvd hpos
      (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp ((mem_idealDivisors hA).mp hD)))

@[simp]
theorem idealDivisors_bot {F : Type*} [Field F] [NumberField F] :
    idealDivisors (⊥ : Ideal (𝓞 F)) = ∅ := by
  simp [idealDivisors]

noncomputable def idealDivisorCount {F : Type*} [Field F] [NumberField F]
    (A : Ideal (𝓞 F)) : ℕ :=
  (idealDivisors A).card
