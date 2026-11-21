module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.Kernel
public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyCount

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.ActualRowCount

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem row_u_injective : Function.Injective (FixedData.Row.u (D := D)) :=
  FixedData.Row.u_injective

theorem q_eq (r : D.Row) : D.q r = D.recipe.A.exteriorNorm r.toFrequency.ideal := by
  unfold FixedData.q
  change (Nat.card (D.recipe.A.R ⧸ Ideal.span {r.toFrequency.u}) : ℝ) = _
  rw [r.toFrequency.generates.2, D.recipe.A.exteriorResidue_card]
  rfl


def principalRow : D.Row :=
  ⟨⟨1, ⟨⊤, top_ne_bot, by simp⟩,
    ⟨one_ne_zero, by
      change Ideal.span {(1 : D.recipe.A.R)} = Ideal.map _ ⊤
      rw [Ideal.map_top, Ideal.span_singleton_one]⟩,
    by
      intro p
      have h : UniqueFactorizationMonoid.normalizedFactors (⊤ : Ideal (𝓞 F)) = 0 := by
        rw [← Ideal.one_eq_top]
        exact UniqueFactorizationMonoid.normalizedFactors_one
      change (UniqueFactorizationMonoid.normalizedFactors (⊤ : Ideal (𝓞 F))).count _ < 6
      rw [h]
      simp⟩,
    ⟨one_ne_zero, D.recipe.probe.frequencies.containsOne⟩⟩

@[simp] theorem principalRow_u : (principalRow D).u = 1 := rfl

theorem principal_row_unique {r r' : D.Row} (h : r.u = 1) (h' : r'.u = 1) : r = r' :=
  row_u_injective D (h.trans h'.symm)

theorem eq_principalRow {r : D.Row} (h : r.u = 1) : r = principalRow D :=
  principal_row_unique D h rfl

theorem u_eq_one_iff {r : D.Row} : r.u = 1 ↔ r = principalRow D :=
  ⟨eq_principalRow D, fun h => by rw [h]; exact principalRow_u D⟩

theorem q_principalRow : D.q (principalRow D) = 1 := by
  rw [q_eq]
  change (Ideal.absNorm (⊤ : Ideal (𝓞 F)) : ℝ) = 1
  simp [Ideal.absNorm_top]









end

end DedekindZetaZeroFree.Quantitative.ActualRowCount
