module

public import ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring
public import ValuedFieldTheory.Valuation.AbsoluteValue.Completeness
public import Mathlib.RingTheory.AdicCompletion.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Principal adic filtrations in complete nonarchimedean valuation rings

For a complete nonarchimedean absolute value, a nonzero element of the open
unit ball generates a separated and precomplete principal filtration on the
closed unit ball.  These facts are shared by the coefficientwise Hensel
construction and the irreducible-polynomial coefficient estimate.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

/-- Membership in the `π`-adic principal power is exactly the corresponding
absolute-value bound on the closed unit ball of a nonarchimedean valued field. -/
theorem principal_pow_mem_iff_abs_le
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {π x : absoluteValueValuationSubring v hnonarch}
    (hπne : π ≠ 0) (n : ℕ) :
    x ∈ (Ideal.span ({π} : Set
        (absoluteValueValuationSubring v hnonarch))) ^ n ↔
      v (x : K) ≤ v ((π : absoluteValueValuationSubring v hnonarch) : K) ^ n := by
  let V := absoluteValueValuationSubring v hnonarch
  have hπK_ne : ((π : V) : K) ≠ 0 := fun hzero => hπne (Subtype.ext hzero)
  constructor
  · intro hx
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    rcases hx with ⟨c, hc⟩
    calc
      _ = v ((((π : V) : K) ^ n) * ((c : V) : K)) := congrArg (fun y : V => v ((y : V) : K)) hc
      _ = v (((π : V) : K) ^ n) * v ((c : V) : K) := by rw [v.map_mul]
      _ = v ((π : V) : K) ^ n * v ((c : V) : K) := by rw [map_pow]
      _ ≤ v ((π : V) : K) ^ n * 1 :=
        mul_le_mul_of_nonneg_left ((mem_absoluteValueValuationSubring_iff
          v hnonarch ((c : V) : K)).1 c.property) (pow_nonneg (v.nonneg _) n)
      _ = v ((π : V) : K) ^ n := by rw [mul_one]
  · intro hx
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    let cK := (x : K) / (((π : V) : K) ^ n)
    have hcK_mem : cK ∈ V := by
      rw [mem_absoluteValueValuationSubring_iff]
      have hdiv :
          v cK = v (x : K) / v (((π : V) : K) ^ n) := by
        change v ((x : K) / (((π : V) : K) ^ n)) =
          v (x : K) / v (((π : V) : K) ^ n)
        rw [div_eq_mul_inv, v.map_mul, map_inv₀, div_eq_mul_inv]
      rw [hdiv]
      exact div_le_one_of_le₀ (by simpa using hx) (le_of_lt (v.pos (pow_ne_zero n hπK_ne)))
    refine ⟨⟨cK, hcK_mem⟩, ?_⟩
    apply Subtype.ext
    change (x : K) =
      (((π : V) : K) ^ n) * ((x : K) / (((π : V) : K) ^ n))
    rw [mul_comm, div_mul_cancel₀]
    positivity

section

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {π x y : absoluteValueValuationSubring v hnonarch} (hπne : π ≠ 0) {n : ℕ}

include hπne in
/-- Principal congruence modulo `(π)^n` is exactly an absolute-value bound for
the difference. -/
theorem principal_smodEq_iff_abs_sub_le :
    x ≡ y [SMOD
      ((Ideal.span ({π} : Set
        (absoluteValueValuationSubring v hnonarch))) ^ n •
          ⊤ : Submodule
            (absoluteValueValuationSubring v hnonarch)
            (absoluteValueValuationSubring v hnonarch))] ↔
    v ((x : K) - (y : K)) ≤
      v ((π : absoluteValueValuationSubring v hnonarch) : K) ^ n := by
  let V := absoluteValueValuationSubring v hnonarch
  constructor
  · intro hxy
    have hmem : (x - y : V) ∈ (Ideal.span ({π} : Set V)) ^ n := by
      simpa [smul_eq_mul, Ideal.mul_top, V] using (SModEq.sub_mem.mp hxy)
    simpa using
      (principal_pow_mem_iff_abs_le
        v hnonarch hπne n).1 hmem
  · intro hxy
    rw [SModEq.sub_mem]
    have hmem : (x - y : V) ∈ (Ideal.span ({π} : Set V)) ^ n := by
      rw [principal_pow_mem_iff_abs_le
        v hnonarch hπne n]
      exact hxy
    simpa using hmem

include hπne in
/-- Forward direction of
`principal_smodEq_iff_abs_sub_le`. -/
theorem abs_sub_le_of_principal_smodEq
    (hxy : x ≡ y [SMOD
      ((Ideal.span ({π} : Set
        (absoluteValueValuationSubring v hnonarch))) ^ n •
          ⊤ : Submodule
            (absoluteValueValuationSubring v hnonarch)
            (absoluteValueValuationSubring v hnonarch))]) :
    v ((x : K) - (y : K)) ≤
      v ((π : absoluteValueValuationSubring v hnonarch) : K) ^ n :=
  (principal_smodEq_iff_abs_sub_le
    v hnonarch (π := π) (x := x) (y := y) hπne).1 hxy

end

/-- Principal separatedness for the element `π` chosen in the proof, as
soon as `π` is a nonzero element of the open unit ball. -/
theorem principalHausdorff_of_nonzero_mem_maximalIdeal
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {π : absoluteValueValuationSubring v hnonarch}
    (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch)) :
    IsHausdorff (Ideal.span ({π} : Set
      (absoluteValueValuationSubring v hnonarch)))
      (absoluteValueValuationSubring v hnonarch) := by
  let V := absoluteValueValuationSubring v hnonarch
  refine ⟨?_⟩
  intro x hx
  by_contra hxne
  rcases exists_pow_lt_of_lt_one (v.pos (fun hxzero => hxne (Subtype.ext hxzero))) ((absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
    v hnonarch π).1 hπmem) with ⟨n, hn⟩
  exact not_lt_of_ge ((principal_pow_mem_iff_abs_le
    v hnonarch hπne n).1 (by
      simpa using ((SModEq.zero.mp (hx n))))) hn

/-- Principal precompleteness for the element `π` chosen in the proof,
deduced from completeness of the valued field. -/
theorem principalPrecomplete_of_complete
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {π : absoluteValueValuationSubring v hnonarch}
    (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch)) :
    IsPrecomplete (Ideal.span ({π} : Set
      (absoluteValueValuationSubring v hnonarch)))
      (absoluteValueValuationSubring v hnonarch) := by
  let V := absoluteValueValuationSubring v hnonarch
  have hπ_abs_lt :=
    (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
      v hnonarch π).1 hπmem
  have hπ_abs_pos := v.pos (fun hzero => hπne (Subtype.ext hzero))
  refine ⟨?_⟩
  intro f hf
  let u := fun n => (WithAbs.equiv v).symm ((f n : V) : K)
  let v₀ := v ((π : V) : K)
  have hu : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    rcases exists_pow_lt_of_lt_one hε hπ_abs_lt with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    wlog hmn : m ≤ n generalizing m n with H
    · simpa [dist_comm] using H n hn m hm (le_of_not_ge hmn)
    have hdist_le :
        dist (u m) (u n) ≤ v₀ ^ N := by
      calc
        _ =
            v (((f m : V) : K) - ((f n : V) : K)) := by
          simp [u, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs]
        _ ≤ v₀ ^ m := (abs_sub_le_of_principal_smodEq
          v hnonarch hπne (hf hmn))
        _ ≤ v₀ ^ N := (pow_le_pow_of_le_one (le_of_lt hπ_abs_pos) hπ_abs_lt.le hm)
    exact hdist_le.trans_lt hN
  rcases (absoluteValueCompleteness_complete_iff_cauchySeq_converges v).1
      hcomplete u hu with
    ⟨a, ha⟩
  let aK := WithAbs.equiv v a
  have ha_dist_lt_one : ∃ N : ℕ, dist (u N) a < 1 := by
    rcases Filter.eventually_atTop.1
        ((Metric.tendsto_nhds.mp ha) 1 zero_lt_one) with
      ⟨N, hN⟩
    exact ⟨N, hN N le_rfl⟩
  rcases ha_dist_lt_one with ⟨N₁, hN₁⟩
  have ha_sub_lt_one :
      v (aK - ((f N₁ : V) : K)) < 1 := by
    have hneg : aK - ((f N₁ : V) : K) = -(((f N₁ : V) : K) - aK) := by
      ring
    rw [hneg]
    rw [v.map_neg]
    exact (by
      simp_all [aK, u, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs])
  have ha_mem : aK ∈ V := by
    rw [mem_absoluteValueValuationSubring_iff]
    calc
      v aK = v (((f N₁ : V) : K) + (aK - ((f N₁ : V) : K))) := by
        ring_nf
      _ ≤ max (v (((f N₁ : V) : K))) (v (aK - ((f N₁ : V) : K))) :=
        LubinTate.Valuations.strong_triangle_of_nonarchimedean
          v hnonarch (((f N₁ : V) : K)) (aK - ((f N₁ : V) : K))
      _ ≤ 1 := max_le ((mem_absoluteValueValuationSubring_iff
        v hnonarch (((f N₁ : V) : K))).1 (f N₁).property) ha_sub_lt_one.le
  let L : V := ⟨aK, ha_mem⟩
  refine ⟨L, ?_⟩
  intro n
  rcases Filter.eventually_atTop.1
      ((Metric.tendsto_nhds.mp ha) (v₀ ^ n) (pow_pos hπ_abs_pos n)) with
    ⟨N₀, hN₀⟩
  let N := max n N₀
  have hN_lim :
      v (((f N : V) : K) - aK) ≤ v₀ ^ n := by
    exact le_of_lt (by
      simpa [aK, u, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs] using (hN₀ N (le_max_right n N₀)))
  have hdiff_le :
      v (((f n : V) : K) - (L : K)) ≤ v₀ ^ n := by
    calc
      _ =
          v ((((f n : V) : K) - ((f N : V) : K)) +
              (((f N : V) : K) - (L : K))) := by
        ring_nf
      _ ≤ max
          (v (((f n : V) : K) - ((f N : V) : K)))
          (v (((f N : V) : K) - (L : K))) :=
        LubinTate.Valuations.strong_triangle_of_nonarchimedean
          v hnonarch
          (((f n : V) : K) - ((f N : V) : K))
          (((f N : V) : K) - (L : K))
      _ ≤ v₀ ^ n := max_le (abs_sub_le_of_principal_smodEq
        v hnonarch hπne (hf (le_max_left n N₀))) hN_lim
  exact
    (principal_smodEq_iff_abs_sub_le
      v hnonarch (π := π) (x := f n) (y := L) hπne).2
      (by assumption)

end Valuations
end AlgebraicNumberTheory

end
