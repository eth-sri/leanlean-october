module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.CharacterValues
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.ProductConductorComparison

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Bilinear

open scoped NumberField Classical
open DedekindZetaZeroFree

noncomputable section

variable {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)}

section

variable {m : Ideal (𝓞 F)} (ψ : RayClassCharacter F m)

def cube :
    RayClassCharacter F m where
  toFun I := (ψ I) ^ 3
  map_mul' := fun I J => by rw [ψ.map_mul', mul_pow]
  map_top' := by rw [ψ.map_top', one_pow]
  eq_zero_iff' := fun I => by
    rw [pow_eq_zero_iff (show (3 : ℕ) ≠ 0 by norm_num), ψ.eq_zero_iff' I]
  map_span' := fun α hα hmem hpos => by
    rw [ψ.map_span' α hα hmem hpos, one_pow]

private lemma cube_apply
    (I : Ideal (𝓞 F)) : cube ψ I = (ψ I) ^ 3 := rfl

end

private alias cube_eq_self_mem := DedekindZetaZeroFree.LargeSieve.CharacterValues.mem_zero_one_neg_one_of_cube_eq_self

theorem primitiveProductQuadratic
    (Q : QuadraticHeckeFamily F c)
    {u v : Ideal (𝓞 F)} (hu0 : u ≠ ⊥) (hv0 : v ≠ ⊥)
    (hu : Squarefree u) (hv : Squarefree v)
    (huc : u ⊔ c = ⊤) (hvc : v ⊔ c = ⊤) (huv : u ⊔ v = ⊤)
    (hclass : Q.cls u = Q.cls v)
    (ψ : RayClassCharacter F (u * v))
    (hagrees : ∀ I : Ideal (𝓞 F), I ⊔ (Q.cond u * Q.cond v) = ⊤ →
      ψ I = (Q.χ u) I * starRingEnd ℂ ((Q.χ v) I)) :
    (∀ I : Ideal (𝓞 F), starRingEnd ℂ (ψ I) = ψ I ∧
      ψ I ∈ ({0, 1, -1} : Set ℂ) ∧ (ψ I) ^ 3 = ψ I ∧ ‖ψ I‖ ≤ 1) ∧
      (∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ (u * v) = ⊤ → (ψ I) ^ 2 = 1) := by
  have hcube_eq :=
    RayComparison.away_uniqueness (fun h => (Ideal.mul_eq_bot.mp h).elim hu0 hv0) (fun h =>
      (Ideal.mul_eq_bot.mp h).elim ((Q.primitive u hu huc).1) ((Q.primitive v hv hvc).1)) (cube ψ) ψ (by
      intro I _ hsup
      have hv3 : (starRingEnd ℂ ((Q.χ v) I)) ^ 3 = starRingEnd ℂ ((Q.χ v) I) := by
        rw [← map_pow, Q.quadratic v I hv hvc]
      rw [cube_apply, hagrees I (le_antisymm le_top (hsup ▸ sup_le_sup_left (Ideal.dvd_iff_le.mp ⟨u * v, mul_comm _ _⟩) I)), mul_pow, hv3, Q.quadratic u I hu huc])
  have hquad := fun I =>
    (rfl).symm.trans (hcube_eq I)
  refine ⟨fun I => ?_, fun I hI hcop => ?_⟩
  · have h3 := hquad I
    have hmem := cube_eq_self_mem h3
    refine ⟨?_, hmem, h3, ?_⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h <;> rw [h] <;> simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h <;> rw [h] <;> norm_num
  · have hmem := cube_eq_self_mem (hquad I)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact absurd h (fun h0 =>
      (ψ.eq_zero_iff' I).mp h0 |>.elim hI (fun hc => hc hcop))
    · rw [h]; norm_num
    · rw [h]; norm_num

end

end DedekindZetaZeroFree.LargeSieve.Bilinear
