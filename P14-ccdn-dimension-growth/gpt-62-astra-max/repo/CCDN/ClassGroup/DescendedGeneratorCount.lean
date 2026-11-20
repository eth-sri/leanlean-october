/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.ClassGroup.SquareClassDescent
public import CCDN.ClassGroup.BalancedGenerator
import CCDN.ClassGroup.TranslateFibers
import CCDN.ForMathlib.FieldTheory
public import CCDN.ClassGroup.NumberFieldLatticeBox
public import CCDN.ClassGroup.NumberFieldShortBasis
public import CCDN.ClassGroup.PrimeFactorSubpower
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

@[expose] public section
namespace CCDN
noncomputable section
open NumberField Finset
open scoped nonZeroDivisors IntermediateField

abbrev fieldDegree (K : Type*) [Field K] [NumberField K] := Module.finrank ℚ K
abbrev absDiscriminant (K : Type*) [Field K] [NumberField K] := |(NumberField.discr K : ℝ)|
abbrev balancedRadius (K : Type*) [Field K] [NumberField K] := 9 * absDiscriminant K ^ (1/(fieldDegree K:ℝ))
abbrev classExponent (n : ℕ) := (1/2-1/(2*(n:ℝ)) : ℝ)
abbrev trivialTorsionCost (n : ℕ) := numberFieldLatticeBoxConstant n ((n:ℝ)^2) * (9:ℝ)^n
lemma trivialTorsionCost_nonneg (n : ℕ) : 0 ≤ trivialTorsionCost n := by simp_all [numberFieldLatticeBoxConstant_nonneg]

theorem crude_class_bound (K : Type*) [Field K] [NumberField K] :
    (classGroupTwoTorsionCard K : ℝ) ≤ trivialTorsionCost (fieldDegree K) * Real.sqrt (absDiscriminant K) := by
  let n := fieldDegree K
  let D := absDiscriminant K
  let B := balancedRadius K
  have hn : (0:ℝ) < n := by exact_mod_cast Module.finrank_pos
  have hD := one_le_abs_discr K
  have hB : D^(1/(n:ℝ)) ≤ B := by linarith [Real.rpow_nonneg (abs_nonneg (discr K : ℝ)) (1/(fieldDegree K))]
  have hc :=
    (classGroupTwoTorsionCard_le_boundedSquareNormIntegers K).trans (Set.ncard_le_ncard (fun _ hx => hx.2.1) (boundedArchimedeanIntegers_finite K B))
  obtain ⟨b,hb,hs⟩ := exists_numberField_short_basis K
  have hh := boundedArchimedeanIntegers_count_of_relative_short_basis K b hb (B := B) (by positivity) (sq_nonneg _)
    (fun i => (hs i).trans (mul_le_mul_of_nonneg_left hB (sq_nonneg _)))
  have he : B^n = (9:ℝ)^n * D := by
    rw [mul_pow,← Real.rpow_mul_natCast (abs_nonneg _),one_div_mul_cancel (by linarith),Real.rpow_one]
  apply le_of_mul_le_mul_right (a := Real.sqrt D) _ (Real.sqrt_pos.mpr (by linarith))
  apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (Real.sqrt_nonneg D)).trans (hh.trans_eq ?_)
  rw [he,mul_assoc,Real.mul_self_sqrt (by linarith)]; ring

/-- A finite sum of fiber bounds, with a real rather than an integral budget. -/
lemma card_le_fiber_budget {α τ : Type*} [Finite α] [Finite τ] (f : α → τ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t, Nonempty {i // f i = t} → (Nat.card {i // f i = t} : ℝ) ≤ C) : (Nat.card α : ℝ) ≤ C * Nat.card τ := by
  classical
  let := Fintype.ofFinite τ
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f),Nat.card_sigma,Nat.cast_sum]
  calc
    _ ≤ ∑ _ : τ, C := sum_le_sum fun t _ => by
      cases isEmpty_or_nonempty {i // f i = t} with
      | inl he => simp_all
      | inr he => exact h t he
    _ = _ := by simp [Nat.card_eq_fintype_card, mul_comm]

/-- A single subpower bound for the generators lying in a proper subfield.
No induction is needed: the base discriminant contributes at most `D^(1/4)`. -/
theorem imprimitive_class_bound (n : ℕ) (hn : 3 ≤ n) : ∃ C : ℝ, 0 < C ∧
    ∀ (K : Type*) [Field K] [NumberField K], fieldDegree K = n →
    ∀ {ι : Type*} [Finite ι] (J : ι → (Ideal (𝓞 K))⁰) (β : ι → 𝓞 K), Function.Injective (ClassGroup.mk0 ∘ J) →
      (∀ i, β i ≠ 0) → (∀ i, (J i : Ideal (𝓞 K))^2 = Ideal.span {β i}) →
      (∀ i, ∃ L : IntermediateField ℚ K, L ≠ ⊤ ∧ (β i : K) ∈ L) →
      (Nat.card ι : ℝ) ≤ C * absDiscriminant K ^ classExponent n := by
  classical
  obtain ⟨A,hA,hpow⟩ := two_pow_primeFactors_subpower n (by norm_num : (0:ℝ) < 1/12)
  let V := 1 + ∑ m ∈ range (n+1), trivialTorsionCost m
  have hV : 0 < V := add_pos_of_pos_of_nonneg one_pos (sum_nonneg fun m _ => trivialTorsionCost_nonneg m)
  refine ⟨V*A*2^n,by positivity,?_⟩
  intro K _ _ hdeg ι _ J β hinj h0 hsq hsub
  change Module.finrank ℚ K = n at hdeg
  let D := absDiscriminant K
  have hD := one_le_abs_discr K
  choose L hL hmem using hsub
  let := Field.finite_intermediateField_of_exists_primitive_element ℚ K (Field.exists_primitive_element ℚ K)
  have hp := hpow _ (numberField_discriminant_natAbs_pos K)
  rw [numberField_discriminant_natAbs_cast] at hp
  have hh := card_le_fiber_budget L (show 0 ≤ V*A*D^classExponent n by positivity) (fun F ⟨j,hj⟩ => by
    let I := {i // L i = F}
    have htwo : 2 ≤ Module.finrank F K := by
      have hne := IntermediateField.finrank_eq_one_iff_eq_top.not.mpr (hj ▸ hL j)
      have hp : 0 < Module.finrank F K := Module.finrank_pos
      omega
    let x (i : I) : 𝓞 F := ⟨⟨(β i.val),Eq.mp (by solve_by_elim [i.property]) (hmem i.val)⟩,(isIntegral_algebraMap_iff (R := ℤ) (A := F) (B := K)).mp (β i.val).isIntegral_coe⟩
    have hx (i : I) : algebraMap _ _ (x i) = β i.val := rfl
    have hcard := descended_square_class_count K F (fun i : I => J i.val) (hinj.comp Subtype.val_injective) x
      (fun i he => h0 i.val (by rw [← hx,he,map_zero])) (by simp [hsq, Ideal.map_span, hx])
    have hbase := crude_class_bound F
    have hm : fieldDegree F ≤ n := by
      have := Module.finrank_mul_finrank ℚ F K; nlinarith
    have hcost := (single_le_sum (fun m _ => trivialTorsionCost_nonneg m) (mem_range.mpr (Nat.lt_succ_of_le hm))).trans (le_add_of_nonneg_left zero_le_one)
    have hdisc' : absDiscriminant F ^ 2 ≤ D := by
      dsimp [D, absDiscriminant]; rw [← numberField_discriminant_natAbs_cast,← numberField_discriminant_natAbs_cast]
      exact_mod_cast (Nat.pow_le_pow_right (numberField_discriminant_natAbs_pos F) htwo).trans (absolute_discriminant_power_le K F)
    have hroot : Real.sqrt (absDiscriminant F) ≤ D^(1/4:ℝ) := by
      have h := Real.rpow_le_rpow (sq_nonneg _) hdisc' (by norm_num : (0:ℝ) ≤ 1/4)
      rw [← Real.rpow_natCast,← Real.rpow_mul (abs_nonneg _)] at h
      norm_num at h; simpa [Real.sqrt_eq_rpow] using h
    have hh := (Nat.cast_le (α := ℝ)).mpr hcard
    rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,hdeg] at hh
    apply hh.trans (mul_le_mul (hbase.trans (mul_le_mul hcost hroot (Real.sqrt_nonneg _) hV.le)) hp (by positivity) (by positivity) |>.trans ?_)
    have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
    have he : 1/4+1/12 ≤ classExponent n := by dsimp [classExponent]; rw [le_sub_comm,div_le_iff₀ (by positivity)]; linarith
    calc _ = V*A*D^(1/4+1/12:ℝ) := by rw [Real.rpow_add (by linarith)]; ring
         _ ≤ _ := by gcongr)
  have ht : ((Nat.card (IntermediateField ℚ K)):ℝ) ≤ (2:ℝ)^n := by exact_mod_cast hdeg ▸ IntermediateField.card_le_two_pow_finrank ℚ K
  calc _ ≤ _ := hh
       _ ≤ (V*A*D^classExponent n)*2^n := by gcongr
       _ = _ := by ring

end
end CCDN
