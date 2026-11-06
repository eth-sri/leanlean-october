module

public import ValuedFieldTheory.LocalField.Analytic.DenominatorValuation
public import ValuedFieldTheory.LocalField.Analytic.FieldUnitLogUniqueness
public import ValuedFieldTheory.LocalField.Analytic.LogExpAdditivity
public import ValuedFieldTheory.LocalField.Analytic.FieldUnitLogExtension
public import ValuedFieldTheory.LocalField.DiscreteValuationField.WithZeroValuationTopology

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# The local-field logarithm

This file packages the ramification-scaled principal-unit logarithm as a
continuous homomorphism and extends it to field units with the unique
uniformizer value forced by `log p = 0`.
-/

noncomputable section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

open Filter
open scoped Topology

variable {K : Type u} [Field K]

/-- The ramification-scaled logarithm homomorphism on first principal units is
continuous.  Near the identity its valuation agrees with that of `u - 1`,
because one may restrict to an arbitrarily deep ball above `e/(p-1)`. -/
theorem continuous_principalUnitLogSeriesHomOfWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e : ℕ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Continuous
      (principalUnitLogSeriesHomOfWithZeroValuationScaled
        (v := v) (p := p) e hnK hnval hcomplete) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  have hMulSubring :
      Continuous (fun z : F.valuationSubring × F.valuationSubring =>
        z.1 * z.2) := by
    apply Continuous.subtype_mk
    exact
      (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
  let : ContinuousMul F.valuationSubring := ⟨hMulSubring⟩
  have hInv :
      Continuous (fun u : F.valuationSubringˣ => u⁻¹) := by
    rw [Units.continuous_iff]
    constructor
    · change Continuous (fun u : F.valuationSubringˣ =>
        ((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring))
      exact Units.continuous_coe_inv
    · simpa using (Units.continuous_val :
        Continuous (fun u : F.valuationSubringˣ =>
          (u : F.valuationSubring)))
  have hMul :
      Continuous (fun z : F.valuationSubringˣ × F.valuationSubringˣ =>
        z.1 * z.2) := by
    rw [Units.continuous_iff]
    constructor
    · exact
        (Units.continuous_val.comp continuous_fst).mul
          (Units.continuous_val.comp continuous_snd)
    · change Continuous (fun z : F.valuationSubringˣ × F.valuationSubringˣ =>
        (((z.1 * z.2)⁻¹ : F.valuationSubringˣ) : F.valuationSubring))
      have hc : Continuous
          (fun z : F.valuationSubringˣ × F.valuationSubringˣ =>
            ((z.1⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
              ((z.2⁻¹ : F.valuationSubringˣ) : F.valuationSubring)) :=
        (Units.continuous_coe_inv.comp continuous_fst).mul
          (Units.continuous_coe_inv.comp continuous_snd)
      simpa [Units.val_inv_eq_inv_val, mul_comm] using hc
  let : ContinuousMul F.valuationSubringˣ := ⟨hMul⟩
  let : ContinuousInv F.valuationSubringˣ := ⟨hInv⟩
  have : IsTopologicalGroup F.valuationSubringˣ := by infer_instance
  have : IsTopologicalGroup ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) := by
    infer_instance
  let φ :=
    principalUnitLogSeriesHomOfWithZeroValuationScaled
      (v := v) (p := p) e hnK hnval hcomplete
  apply continuous_of_continuousAt_one φ
  dsimp [φ, principalUnitLogSeriesHomOfWithZeroValuationScaled]
  rw [ContinuousAt]
  suffices hlog :
    Tendsto
      (fun u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1 =>
        principalUnitLogSeriesOfWithZeroValuation v u hnK)
      (𝓝 1) (𝓝 0) by
    rw [principalUnitLogSeries_one_ofWithZeroValuation v hnK]
    change Tendsto
      (fun u => Multiplicative.ofAdd
        (principalUnitLogSeriesOfWithZeroValuation v u hnK))
      (𝓝 1) (𝓝 (Multiplicative.ofAdd (0 : K)))
    exact (continuous_ofAdd.tendsto (0 : K)).comp hlog
  rw [(Valued.hasBasis_nhds_zero K
    (WithZero (Multiplicative ℤ))).tendsto_right_iff]
  intro γ _
  let γ' : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (v : K →*₀ WithZero (Multiplicative ℤ)))) γ
  obtain ⟨N₀, hN₀γ⟩ :=
    WithZero.exists_exp_neg_natCast_lt γ'.ne_zero
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ,
      (e : ℚ) / ((p : ℚ) - 1) < (N₁ : ℚ) :=
    exists_nat_gt ((e : ℚ) / ((p : ℚ) - 1))
  let N := max N₀ N₁
  have hNγ : WithZero.exp (-(N : ℤ)) <
      (γ' : WithZero (Multiplicative ℤ)) := by
    exact lt_of_le_of_lt
      (by
        apply WithZero.exp_le_exp.mpr
        simp only [neg_le_neg_iff]
        exact_mod_cast Nat.le_max_left N₀ N₁)
      hN₀γ
  have hNth :
      (e : ℚ) / ((p : ℚ) - 1) < (N : ℚ) :=
    lt_of_lt_of_le hN₁ (by exact_mod_cast Nat.le_max_right N₀ N₁)
  have hsubContinuous :
      Continuous
        (fun u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1 =>
          principalUnitSubOneOfWithZeroValuation v u) := by
    unfold principalUnitSubOneOfWithZeroValuation
    fun_prop
  have hball :
      {x : K | v x < WithZero.exp (-(N : ℤ))} ∈ 𝓝 (0 : K) := by
    let g : (WithZero (Multiplicative ℤ))ˣ :=
      Valuation.IsRankOneDiscrete.generator v
    have hg : (g : WithZero (Multiplicative ℤ)) < 1 := by
      exact Valuation.IsRankOneDiscrete.generator_lt_one v
    let a : ℤ := WithZero.log (g : WithZero (Multiplicative ℤ))
    have ha : a ≤ -1 := by
      have ha0 : a < 0 := by
        have hlog := (WithZero.log_lt_log (Units.ne_zero g)
          (one_ne_zero : (1 : WithZero (Multiplicative ℤ)) ≠ 0)).2 hg
        simpa [a] using hlog
      omega
    let m := N + 1
    have hm :
        (g : WithZero (Multiplicative ℤ)) ^ m <
          WithZero.exp (-(N : ℤ)) := by
      rw [show m = N + 1 by rfl, ← WithZero.exp_log (Units.ne_zero g),
        ← WithZero.exp_nsmul, WithZero.exp_lt_exp]
      change ((N + 1 : ℕ) : ℤ) * a < -(N : ℤ)
      calc
        ((N + 1 : ℕ) : ℤ) * a ≤ ((N + 1 : ℕ) : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left ha (by omega)
        _ < -(N : ℤ) := by omega
    rcases Valuation.IsRankOneDiscrete.generator_mem_range K v with ⟨z, hz⟩
    have hz0 : z ≠ 0 := (Valuation.ne_zero_iff v).mp (by
      rw [hz]
      exact Units.ne_zero g)
    have hzm0 : z ^ m ≠ 0 := pow_ne_zero m hz0
    rw [Valued.mem_nhds_zero]
    refine ⟨Units.mk0 (v.restrict (z ^ m))
      ((Valuation.ne_zero_iff v.restrict).2 hzm0), ?_⟩
    intro x hx
    change v.restrict x < v.restrict (z ^ m) at hx
    have hx' : v x < v (z ^ m) := v.restrict_lt_iff.mp hx
    exact hx'.trans (by simpa [v.map_pow, hz] using hm)
  have hpre :
      {u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1 |
        v (principalUnitSubOneOfWithZeroValuation v u) <
          WithZero.exp (-(N : ℤ))} ∈ 𝓝 1 := by
    have hballOne :
        {x : K | v x < WithZero.exp (-(N : ℤ))} ∈
          𝓝 (principalUnitSubOneOfWithZeroValuation v
            (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)) := by
      simpa using hball
    have ht := (hsubContinuous.tendsto
      (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)) hballOne
    exact ht
  refine Filter.mem_of_superset hpre ?_
  intro u hu
  change
    v.restrict (principalUnitLogSeriesOfWithZeroValuation v u hnK) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  let x := principalUnitSubOneOfWithZeroValuation v u
  by_cases hx : x = 0
  · have hlog : principalUnitLogSeriesOfWithZeroValuation v u hnK = 0 := by
      simp [principalUnitLogSeriesOfWithZeroValuation, x, hx]
    rw [hlog, v.map_zero]
    exact zero_lt_iff.mpr
      (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  · have hxv_ne : v x ≠ 0 := (_root_.Valuation.ne_zero_iff v).2 hx
    have hloglt : WithZero.log (v x) < -(N : ℤ) := by
      exact
        (WithZero.log_lt_log hxv_ne
          (WithZero.exp_ne_zero (a := -(N : ℤ)))).2 (by simpa [x] using hu)
    have hvalN :
        (N : ℤ) < (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      change (N : ℤ) < -WithZero.log (v x)
      linarith
    have hthreshold :
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) :=
      lt_of_lt_of_le hNth (by exact_mod_cast hvalN.le)
    have hvx : v x < (1 : WithZero (Multiplicative ℤ)) :=
      principalUnitSubOne_val_lt_one_ofWithZeroValuation v u
    have hval :=
      valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
        (v := v) (p := p) e (x := x) hx hnK hnval hvx hthreshold hcomplete
    rw [principalUnitLogSeriesOfWithZeroValuation, hval]
    exact lt_trans (by simpa [x] using hu) (by simpa [γ'] using hNγ)









end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
