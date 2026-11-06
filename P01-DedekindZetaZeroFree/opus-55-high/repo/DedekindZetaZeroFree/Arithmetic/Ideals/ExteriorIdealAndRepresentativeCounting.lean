module

public import DedekindZetaZeroFree.Arithmetic.Kummer.FrequencyClassesAndCharacterRigidity
public import DedekindZetaZeroFree.Arithmetic.Ideals.Counting.NormSeries

@[expose] public section

section

namespace DedekindZetaZeroFree.ProbeExteriorPrincipalIdealFibers

theorem finite_preimage_card_bound {ι κ : Type*} (f : ι → κ) (M : ℕ)
    (hf : ∀ b : κ, {i : ι | f i = b}.Finite ∧ Nat.card {i : ι // f i = b} ≤ M)
    (B : Set κ) (hB : B.Finite) :
    {i : ι | f i ∈ B}.Finite ∧
      Nat.card {i : ι // f i ∈ B} ≤ M * Nat.card B := by
  classical
  have hEq : {i : ι | f i ∈ B} = ⋃ b ∈ B, {i : ι | f i = b} := by
    ext i
    simp
  have hfin : {i : ι | f i ∈ B}.Finite := by
    rw [hEq]
    exact hB.biUnion fun b _ => (hf b).1
  refine ⟨hfin, ?_⟩
  have hcard : Nat.card {i : ι // f i ∈ B} = ({i : ι | f i ∈ B} : Set ι).ncard :=
    Nat.card_coe_set_eq _
  rw [hcard, hEq]
  have h1 : (⋃ b ∈ B, {i : ι | f i = b}).ncard ≤
      ∑ b ∈ hB.toFinset, ({i : ι | f i = b} : Set ι).ncard := by
    simpa [hB.coe_toFinset] using
      Finset.set_ncard_biUnion_le hB.toFinset (fun b => {i : ι | f i = b})
  have hb : ∀ b ∈ hB.toFinset, ({i : ι | f i = b} : Set ι).ncard ≤ M := by
    intro b _
    exact (hf b).2
  have h2 : ∑ b ∈ hB.toFinset, ({i : ι | f i = b} : Set ι).ncard ≤
      ∑ _b ∈ hB.toFinset, M :=
    Finset.sum_le_sum hb
  have h3 : ∑ _b ∈ hB.toFinset, M = M * Nat.card B := by
    rw [Finset.sum_const_nat (fun _ _ => rfl), Nat.card_coe_set_eq,
      Set.ncard_eq_toFinset_card B hB, Nat.mul_comm]
  omega

end DedekindZetaZeroFree.ProbeExteriorPrincipalIdealFibers

end

section

noncomputable section
open scoped NumberField Classical WithZero NNReal
open IsDedekindDomain

namespace DedekindZetaZeroFree.ProbeExteriorPrincipalIdealFibers

variable (F : Type) [Field F] [NumberField F]

end DedekindZetaZeroFree.ProbeExteriorPrincipalIdealFibers

end

end

section

noncomputable section
open scoped NumberField Classical nonZeroDivisors
open IsDedekindDomain

namespace DedekindZetaZeroFree.ProbeExteriorPrincipalIdealFibers

end DedekindZetaZeroFree.ProbeExteriorPrincipalIdealFibers

end

end

section

noncomputable section
set_option maxHeartbeats 800000

namespace DedekindZetaZeroFree.ProbeExteriorIdealCount

open scoped NumberField
open IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

theorem ideal_count_linear (cS : Ideal (𝓞 F)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      {a : ExteriorIdeal cS | idealNorm a.val ≤ T}.Finite ∧
      (Nat.card {a : ExteriorIdeal cS // idealNorm a.val ≤ T} : ℝ) ≤ C * T := by
  classical
  unfold ExteriorIdeal
  obtain ⟨C, C', hC, _, hbound⟩ := ideal_counting_harmonic_bounds F
  refine ⟨C, hC.le, ?_⟩
  intro T hT
  let f : ExteriorIdeal cS → NonzeroIdeal F := fun a => ⟨a.val, a.property.1⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (congrArg (fun z : NonzeroIdeal F => z.val) h)
  have hfinite : {a : ExteriorIdeal cS | idealNorm a.val ≤ T}.Finite :=
    (normBoundedIdeals_finite F T).preimage hf.injOn
  refine ⟨hfinite, ?_⟩
  change (Nat.card ↥{a : ExteriorIdeal cS | idealNorm a.val ≤ T} : ℝ) ≤ C * T
  rw [Nat.card_coe_set_eq]
  have hn := Set.ncard_le_ncard_of_injOn f (fun a ha => ha) hf.injOn
    (normBoundedIdeals_finite F T)
  have hb := (hbound Set.univ).1 T hT
  simp only [Set.univ_inter] at hb
  exact (Nat.cast_le.mpr hn).trans hb

theorem ideal_norm_summable (cS : Ideal (𝓞 F)) (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun a : ExteriorIdeal cS => (idealNorm a.val) ^ (-σ)) := by
  let f : ExteriorIdeal cS → NonzeroIdeal F := fun a => ⟨a.val, a.property.1⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (congrArg (fun z : NonzeroIdeal F => z.val) h)
  change Summable ((fun I : NonzeroIdeal F => idealNorm I.val ^ (-σ)) ∘ f)
  simpa only [Real.rpow_eq_pow] using
    (ideal_norm_rpow_summable F σ hσ).comp_injective hf

theorem ideal_count_annulus (cS : Ideal (𝓞 F))
    (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 1 ≤ Y →
      {a : ExteriorIdeal cS | c₀ * Y ≤ idealNorm a.val ∧ idealNorm a.val ≤ c₁ * Y}.Finite ∧
      (Nat.card {a : ExteriorIdeal cS //
        c₀ * Y ≤ idealNorm a.val ∧ idealNorm a.val ≤ c₁ * Y} : ℝ) ≤ C * Y := by
  classical
  unfold ExteriorIdeal
  obtain ⟨C, hC, hbound⟩ := ideal_count_linear F cS
  refine ⟨C * max c₁ 1, mul_nonneg hC (le_max_of_le_right zero_le_one), ?_⟩
  intro Y hY
  have hMY : 1 ≤ max c₁ 1 * Y := by
    nlinarith [le_max_right c₁ (1 : ℝ)]
  obtain ⟨hf, hb⟩ := hbound (max c₁ 1 * Y) hMY
  have hsub : {a : ExteriorIdeal cS | c₀ * Y ≤ idealNorm a.val ∧ idealNorm a.val ≤ c₁ * Y} ⊆
      {a : ExteriorIdeal cS | idealNorm a.val ≤ max c₁ 1 * Y} := by
    intro a ha
    exact ha.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  refine ⟨hf.subset hsub, ?_⟩
  change (Nat.card ↥{a : ExteriorIdeal cS | c₀ * Y ≤ idealNorm a.val ∧ idealNorm a.val ≤ c₁ * Y} : ℝ) ≤ _
  change (Nat.card ↥{a : ExteriorIdeal cS | idealNorm a.val ≤ max c₁ 1 * Y} : ℝ) ≤ _ at hb
  rw [Nat.card_coe_set_eq] at hb ⊢
  exact (Nat.cast_le.mpr (Set.ncard_le_ncard hsub hf)).trans (by simpa [mul_assoc] using hb)
