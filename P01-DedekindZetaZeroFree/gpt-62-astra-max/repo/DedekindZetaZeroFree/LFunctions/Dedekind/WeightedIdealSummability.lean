module

public import DedekindZetaZeroFree.LFunctions.Dedekind.IdealNormSeries

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField

variable (K : Type*) [Field K] [NumberField K] (w : Ideal (𝓞 K) → ℂ)
    (hmul : ∀ I J, w (I * J) = w I * w J) (htop : w ⊤ = 1) (hbot : w ⊥ = 0) (hnorm : ∀ I, ‖w I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re)

include hmul htop hbot hnorm hs in
theorem weightedIdealSummability :
    Summable (fun I : Ideal (𝓞 K) =>
      ‖w I * (Ideal.absNorm I : ℂ) ^ (-s)‖) := by

  refine Summable.of_nonneg_of_le (fun I => norm_nonneg _) ?_
    (DedekindZetaZeroFree.Odlyzko.summable_norm_idealInverseNormPower K hs)
  intro I
  by_cases hI : I = ⊥
  · subst hI
    simp [hbot, DedekindZetaZeroFree.Odlyzko.idealInverseNormPower]
  · rw [DedekindZetaZeroFree.Odlyzko.idealInverseNormPower_of_ne_zero K s hI, norm_mul]
    calc _
        ≤ 1 * ‖(Ideal.absNorm I : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right (hnorm I) (norm_nonneg _)
      _ = ‖(Ideal.absNorm I : ℂ) ^ (-s)‖ := one_mul _

include hmul htop hbot hnorm hs in
theorem weightedIdealSummandHom_exists :
    ∃ g : Ideal (𝓞 K) →*₀ ℂ,
      ∀ I, g I = w I * (Ideal.absNorm I : ℂ) ^ (-s) := by

  let g : Ideal (𝓞 K) →*₀ ℂ :=
    { toFun := fun I => w I * (Ideal.absNorm I : ℂ) ^ (-s)
      map_zero' := by simp [hbot]
      map_one' := by simp [htop]
      map_mul' := by
        intro I J
        rw [hmul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
        ring }
  exact ⟨g, fun I => rfl⟩

end DedekindZetaZeroFree.AbelianQuotient
