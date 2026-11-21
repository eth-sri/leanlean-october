module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.Divisors.IdealDivisorBins
public import DedekindZetaZeroFree.Arithmetic.Ideals.PrimeSupportCost

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

lemma column_energy_le (C : Context Q) :
    (∑ u ∈ C.columns, ‖C.lam (C.d * u)‖ ^ 2) ≤ Sieve.energy F c C.N C.lam := by
  apply Finset.sum_le_sum_of_injOn (fun u => C.d * u)
  · intro u _ v _ huv
    exact mul_left_cancel₀ C.hd0 huv
  · intro b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_filter.mp hu).2.1
  · intro u hu
    exact le_rfl
  · intro b _ _
    exact sq_nonneg _

theorem weighted_column_energy_le (η A : ℝ) (hη : 0 < η) (hA : 1 ≤ A)
    (hcount : ∀ u : Ideal (𝓞 F), (idealDivisorCount u : ℝ) ≤ A * norm u ^ η)
    (C : Context Q) (hN : 1 ≤ C.N) (hn : 1 ≤ norm C.d) (S : Finset (Ideal (𝓞 F))) :
    (∑ u ∈ C.columns, (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card *
      ((S.filter (fun f => f ∣ u)).card : ℝ) * ‖C.lam (C.d * u)‖ ^ 2) ≤ (A * (2 * C.N) ^ η) ^ 2 * Sieve.energy F c C.N C.lam := by
  let L := A * (2 * C.N) ^ η
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hu0 : ∀ u ∈ C.columns, u ≠ ⊥ := by
    intro u hu
    exact ((Sieve.mem_idealAdmissibleFinset _ _ _ _).mp (Finset.mem_filter.mp hu).1).1.ne_zero
  have hcnt : ∀ u ∈ C.columns, (idealDivisorCount u : ℝ) ≤ L := by
    intro u hu
    have huN := ((Sieve.mem_idealAdmissibleFinset _ _ _ _).mp (Finset.mem_filter.mp hu).1).2.2
    have hn0 : 0 < norm C.d := by linarith
    have hnorm : norm u ≤ 2 * C.N := by
      have hh := (le_div_iff₀ hn0).mp huN
      change norm u * norm C.d ≤ 2 * C.N at hh
      have hu_non : 0 ≤ norm u := Nat.cast_nonneg _
      nlinarith
    exact (hcount u).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hη.le) (by linarith))
  have hcard : ∀ u ∈ C.columns,
      ((S.filter (fun f => f ∣ u)).card : ℝ) ≤ L := by
    intro u hu
    have hc : (S.filter (fun f => f ∣ u)).card ≤ (idealDivisors u).card := by
      apply Finset.card_le_card
      intro f hf
      exact (mem_idealDivisors (hu0 u hu)).mpr (Finset.mem_filter.mp hf).2
    exact (by exact_mod_cast hc : _ ≤ (idealDivisorCount u : ℝ)).trans (hcnt u hu)
  calc
    _ ≤ ∑ u ∈ C.columns, L ^ 2 * ‖C.lam (C.d * u)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      have hs := (primeSupportCost_le_divisorCount u (hu0 u hu)).trans (hcnt u hu)
      have hc := hcard u hu
      nlinarith [mul_le_mul hc hs (by positivity : 0 ≤ (2 : ℝ) ^
        (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card) hL,
        sq_nonneg ‖C.lam (C.d * u)‖]
    _ = L ^ 2 * ∑ u ∈ C.columns, ‖C.lam (C.d * u)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (column_energy_le C) (sq_nonneg _)

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms
