module

public import Mathlib

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.RingTheory.Filtration
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




/-!
# Successive principal-unit quotients

Develops `U^n/U^(n+1)` and identifies it with the additive ideal quotient
`𝓂^n/𝓂^(n+1)` through the first-order map `a ↦ 1 + a`.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

open Filter

/-- The actual successive quotient `U^n / U^(n+1)` of principal units. -/
def PrincipalUnitsSuccQuot (K : Type u) [Field K] [ValuativeRel K] (n : Nat)  :=
  principalUnits K n ⧸ (principalUnits K (n + 1)).subgroupOf (principalUnits K n)

/-- Equips the successive principal-unit quotient `U^n/U^(n+1)` with its commutative group
structure. -/
instance principalUnitsSuccQuotCommGroup
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    CommGroup (PrincipalUnitsSuccQuot K n) := by
  change CommGroup
    (principalUnits K n ⧸
      (principalUnits K (n + 1)).subgroupOf (principalUnits K n))
  infer_instance

/-- Explicit access to the concrete quotient representation. -/
def principalUnitsSuccQuotConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    PrincipalUnitsSuccQuot K n ≃*
      (principalUnits K n ⧸
        (principalUnits K (n + 1)).subgroupOf (principalUnits K n)) := by
  change
    (principalUnits K n ⧸
        (principalUnits K (n + 1)).subgroupOf (principalUnits K n)) ≃*
      (principalUnits K n ⧸
        (principalUnits K (n + 1)).subgroupOf (principalUnits K n))
  exact MulEquiv.refl _

/-- The quotient map `U^n → U^n/U^(n+1)`. -/
def principalUnitsSuccQuotMk (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    principalUnits K n →* PrincipalUnitsSuccQuot K n := by
  change principalUnits K n →*
    (principalUnits K n ⧸
      (principalUnits K (n + 1)).subgroupOf (principalUnits K n))
  exact QuotientGroup.mk'
    ((principalUnits K (n + 1)).subgroupOf (principalUnits K n))

section
variable {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : principalUnits K n →* M)
    (h : (principalUnits K (n + 1)).subgroupOf
      (principalUnits K n) ≤ f.ker)
include K M n f h
/-- Descend a homomorphism that kills `U^(n+1)` inside `U^n`. -/
def principalUnitsSuccQuotLift
      :
    PrincipalUnitsSuccQuot K n →* M := by
  change
    (principalUnits K n ⧸
      (principalUnits K (n + 1)).subgroupOf (principalUnits K n)) →* M
  exact QuotientGroup.lift
    ((principalUnits K (n + 1)).subgroupOf (principalUnits K n)) f h

/-- The homomorphism descended from `U^n` agrees with the original homomorphism on quotient
representatives. -/
@[simp]
theorem principalUnitsSuccQuotLift_mk
      (x : principalUnits K n) :
    principalUnitsSuccQuotLift n f h
        (principalUnitsSuccQuotMk K n x) = f x :=
  rfl
end


/-- Eliminate a successive principal-unit class through the canonical map. -/
protected theorem PrincipalUnitsSuccQuot.inductionOn
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : PrincipalUnitsSuccQuot K n → Prop}
    (q : PrincipalUnitsSuccQuot K n)
    (h : ∀ x : principalUnits K n,
      motive (principalUnitsSuccQuotMk K n x)) :
    motive q := by
  change motive
    (show principalUnits K n ⧸
      (principalUnits K (n + 1)).subgroupOf (principalUnits K n) from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x

/-! ### Separatedness of the principal-unit filtration -/

section
variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
include K
/-- Krull separatedness of the maximal-ideal filtration of the valuation integer
ring of a nonarchimedean local field. -/
theorem maximalIdeal_iInf_pow_eq_bot
      :
    (⨅ n : Nat, (𝓂[K] ^ n : Ideal 𝒪[K])) = ⊥ := Ideal.iInf_pow_eq_bot_of_isLocalRing
    (I := (𝓂[K] : Ideal 𝒪[K])) Ideal.IsPrime.ne_top'

/-- An element of the valuation integer ring lying in every power of the
maximal ideal is zero. -/
theorem eq_zero_of_mem_all_maximalIdeal_pow
      (x : 𝒪[K])
    (hx : ∀ n : Nat, x ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) :
    x = 0 := by
  have hxInf : x ∈ (⨅ n : Nat, (𝓂[K] ^ n : Ideal 𝒪[K])) := by
    rw [Ideal.mem_iInf]
    exact hx
  rw [maximalIdeal_iInf_pow_eq_bot K] at hxInf
  apply Ideal.mem_bot.mp <;> assumption

/-- The principal-unit filtration is separated: a unit lying in every `U^n`
is the unit `1`. -/
theorem principalUnits_eq_one_of_mem_all
      (u : 𝒪[K]ˣ)
    (hu : ∀ n : Nat, u ∈ principalUnits K n) :
    u = 1 := by
  apply Units.ext
  have hsub  :=
    eq_zero_of_mem_all_maximalIdeal_pow K ((u : 𝒪[K]) - 1) (by
      intro n
      exact (mem_principalUnits_iff K u n).1 (hu n))
  exact sub_eq_zero.mp hsub

/-- Variant tailored to finite-depth approximation statements: if a unit lies
in `U^(n+d)` for every `d`, then it is `1`. -/
theorem principalUnits_eq_one_of_mem_add_all
      (n : Nat) (u : 𝒪[K]ˣ)
    (hu : ∀ d : Nat, u ∈ principalUnits K (n + d)) :
    u = 1 := by
  refine principalUnits_eq_one_of_mem_all K u ?_
  intro m
  by_cases hm : m ≤ n
  · exact principalUnits_antitone K hm (hu 0)
  · have hnm  := Nat.le_of_not_ge hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact hu d

/-! ### Maximal-ideal powers as local neighborhoods -/

/-- Every neighborhood of zero in the valuation integer ring contains a
sufficiently deep power of the maximal ideal. -/
theorem exists_maximalIdeal_pow_subset_nhds_zero
      (s : Set 𝒪[K])
    (hs : s ∈ nhds (0 : 𝒪[K])) :
    ∃ N : Nat, ((𝓂[K] ^ N : Ideal 𝒪[K]) : Set 𝒪[K]) ⊆ s := by
  rcases (mem_nhds_subtype ((ValuativeRel.valuation K).integer : Set K)
      (0 : 𝒪[K]) s).1 hs with
    ⟨t, ht, hts⟩
  rcases (IsValuativeTopology.hasBasis_nhds_zero K).mem_iff.mp ht with
    ⟨γ, -, hγt⟩
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨ϖ, hϖ⟩
  rcases exists_pow_lt₀
      (Valuation.integer.v_irreducible_lt_one (v := ValuativeRel.valuation K) hϖ)
      γ with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro x hx
  apply hts
  apply hγt
  have hset := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
    (v := ValuativeRel.valuation K) hϖ N
  have hxset  := hx
  rw [hset] at hxset
  exact hxset.trans_lt hN

/-- Eventual form of `exists_maximalIdeal_pow_subset_nhds_zero`: all deeper
powers of the maximal ideal lie in a fixed zero-neighborhood. -/
theorem eventually_maximalIdeal_pow_subset_nhds_zero
      (s : Set 𝒪[K])
    (hs : s ∈ nhds (0 : 𝒪[K])) :
    ∃ N : Nat, ∀ m : Nat, N ≤ m →
      ((𝓂[K] ^ m : Ideal 𝒪[K]) : Set 𝒪[K]) ⊆ s := by
  rcases exists_maximalIdeal_pow_subset_nhds_zero K s hs with ⟨N, hN⟩
  refine ⟨N, fun m hm x hx => hN ?_⟩
  exact Ideal.pow_le_pow_right hm hx

/-- Each power of the maximal ideal is closed in the valuation integer ring. -/
theorem isClosed_maximalIdeal_pow
      (n : Nat) :
    IsClosed (((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) := by
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨ϖ, hϖ⟩
  have hset := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
    (v := ValuativeRel.valuation K) hϖ n
  rw [hset]
  have hclosed :
      IsClosed {x : 𝒪[K] |
        (ValuativeRel.valuation K).restrict (x : K) ≤
          (ValuativeRel.valuation K).restrict ((ϖ : K) ^ n)} :=
    ((ValuativeRel.valuation K).isClosed_closedBall
      ((ValuativeRel.valuation K).restrict ((ϖ : K) ^ n))).preimage
        (continuous_subtype_val : Continuous (fun x : 𝒪[K] => (x : K)))
  convert hclosed using 1
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [← map_pow, Valuation.restrict_le_iff, map_pow]

/-- Each power of the maximal ideal is a zero-neighborhood in the valuation
integer ring. -/
theorem maximalIdeal_pow_mem_nhds_zero
      (n : Nat) :
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) ∈ nhds (0 : 𝒪[K]) := by
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨ϖ, hϖ⟩
  let γ : (ValuativeRel.ValueGroupWithZero K)ˣ :=
    Units.mk0 (ValuativeRel.valuation K (ϖ : K) ^ n)
      (pow_ne_zero n (ne_of_gt (Valuation.integer.v_irreducible_pos
        (v := ValuativeRel.valuation K) hϖ)))
  refine (mem_nhds_subtype ((ValuativeRel.valuation K).integer : Set K)
      (0 : 𝒪[K]) (((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]))).2 ?_
  refine ⟨{x : K | ValuativeRel.valuation K x <
      (γ : ValuativeRel.ValueGroupWithZero K)}, ?_, ?_⟩
  · exact (IsValuativeTopology.hasBasis_nhds_zero K).mem_of_mem (i := γ) trivial
  · intro x hx
    change x ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
    have hset := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
      (v := ValuativeRel.valuation K) hϖ n
    rw [hset]
    have hxv : ValuativeRel.valuation K ((x : 𝒪[K]) : K) <
        (γ : ValuativeRel.ValueGroupWithZero K) := hx
    exact le_of_lt hxv

/-- Powers of an element of the maximal ideal tend to zero in the valuation
integer ring. -/
theorem tendsto_pow_succ_of_mem_maximalIdeal
      {x : 𝒪[K]}
    (hx : x ∈ (𝓂[K] : Ideal 𝒪[K])) :
    Tendsto (fun d : Nat => x ^ (d + 1)) atTop (nhds (0 : 𝒪[K])) := by
  rw [tendsto_def]
  intro s hs
  rcases eventually_maximalIdeal_pow_subset_nhds_zero K s hs with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N] with d hd
  exact hN (d + 1) (le_trans hd (Nat.le_succ d))
    (Ideal.pow_mem_pow hx (d + 1))

/-- The signed version used by finite geometric inverse corrections. -/
def tendsto_neg_pow_succ_of_mem_maximalIdeal
      {x : 𝒪[K]}
    (hx : x ∈ (𝓂[K] : Ideal 𝒪[K]))  :=
  tendsto_pow_succ_of_mem_maximalIdeal K ((𝓂[K] : Ideal 𝒪[K]).neg_mem hx)
end


/-- If a sequence of valuation integers converges, then its difference from
the limit is eventually in any fixed power of the maximal ideal. -/
theorem eventually_sub_mem_maximalIdeal_pow_of_tendsto
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] {f : Nat → 𝒪[K]} {x : 𝒪[K]} (n : Nat)
    (hf : Tendsto f atTop (nhds x)) :
    ∀ᶠ d in atTop, f d - x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  have hdiff : Tendsto (fun d : Nat => f d - x) atTop (nhds (0 : 𝒪[K])) := by
    simpa using hf.sub (tendsto_const_nhds (x := x))
  exact hdiff.eventually (maximalIdeal_pow_mem_nhds_zero K n)

/-- If valuation-ring units converge in the valuation integer ring, then their
quotient by the limit is eventually in every fixed principal-unit level. -/
theorem eventually_div_mem_principalUnits_of_tendsto_units
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] {f : Nat → 𝒪[K]ˣ} {x : 𝒪[K]ˣ} (n : Nat)
    (hf : Tendsto (fun d : Nat => ((f d : 𝒪[K]ˣ) : 𝒪[K])) atTop
      (nhds (x : 𝒪[K]))) :
    ∀ᶠ d in atTop, f d / x ∈ principalUnits K n := by
  have hsub := eventually_sub_mem_maximalIdeal_pow_of_tendsto K n hf
  filter_upwards [hsub] with d hd
  rw [mem_principalUnits_iff]
  change (((f d / x : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
  rw [show (((f d / x : 𝒪[K]ˣ) : 𝒪[K]) - 1) =
      (((f d : 𝒪[K]ˣ) : 𝒪[K]) - (x : 𝒪[K])) * ↑(x⁻¹) by
    simp only [div_eq_mul_inv, Units.val_mul]
    calc
      ((f d : 𝒪[K]ˣ) : 𝒪[K]) * ↑(x⁻¹) - 1 =
          ((f d : 𝒪[K]ˣ) : 𝒪[K]) * ↑(x⁻¹) -
            (x : 𝒪[K]) * ↑(x⁻¹) := by
            simp
      _ = (((f d : 𝒪[K]ˣ) : 𝒪[K]) - (x : 𝒪[K])) * ↑(x⁻¹) := by
            ring]
  exact (𝓂[K] ^ n : Ideal 𝒪[K]).mul_mem_right _ hd

/-! ### Finite correction products for complete lifting -/

/-- Finite product of a correction sequence whose `d`-th term lies in
`U^(n+d)`. This algebraic partial product is the finite-stage input to the
complete-limit construction. -/
def principalUnitsCorrectionProduct (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (z : ∀ d : Nat, principalUnits K (n + d)) :
    Nat → 𝒪[K]ˣ
  | 0 => 1
  | d + 1 => principalUnitsCorrectionProduct K n z d * (z d : 𝒪[K]ˣ)

/-- The correction product with no factors is the identity unit. -/
@[simp]
theorem principalUnitsCorrectionProduct_zero
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    principalUnitsCorrectionProduct K n z 0 = 1 :=
  rfl

/-- The next correction product appends the correction at the current filtration depth. -/
@[simp]
theorem principalUnitsCorrectionProduct_succ
    (K : Type u) [Field K] [ValuativeRel K] (n d : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    principalUnitsCorrectionProduct K n z (d + 1) =
      principalUnitsCorrectionProduct K n z d * (z d : 𝒪[K]ˣ) :=
  rfl

/-- Every finite correction product stays in the initial principal-unit level
`U^n`. -/
theorem principalUnitsCorrectionProduct_mem
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) (d : Nat) :
    principalUnitsCorrectionProduct K n z d ∈ principalUnits K n := by
  induction d with
  | zero =>
      simp [principalUnitsCorrectionProduct]
  | succ d ih =>
      rw [principalUnitsCorrectionProduct_succ]
      exact (principalUnits K n).mul_mem ih
        (principalUnits_antitone K (Nat.le_add_right n d) (z d).2)

/-- The tail quotient of two finite correction products lies in the principal
unit level controlled by the earlier index. This is the filtration input for
the later Cauchy argument. -/
theorem principalUnitsCorrectionProduct_div_mem
    (K : Type u) [Field K] [ValuativeRel K] (n m d : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    principalUnitsCorrectionProduct K n z (m + d) /
        principalUnitsCorrectionProduct K n z m ∈
      principalUnits K (n + m) := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hprod :
          principalUnitsCorrectionProduct K n z (m + (d + 1)) =
            principalUnitsCorrectionProduct K n z (m + d) *
              (z (m + d) : 𝒪[K]ˣ) := by
        rw [Nat.add_succ]
        rfl
      rw [hprod]
      have hz  := principalUnits_antitone K
          (Nat.add_le_add_left (Nat.le_add_right m d) n) (z (m + d)).2
      have hEq :
          principalUnitsCorrectionProduct K n z (m + d) *
              (z (m + d) : 𝒪[K]ˣ) /
              principalUnitsCorrectionProduct K n z m =
            (principalUnitsCorrectionProduct K n z (m + d) /
              principalUnitsCorrectionProduct K n z m) *
              (z (m + d) : 𝒪[K]ˣ) := by
        simp [div_eq_mul_inv, mul_assoc, mul_comm]
      rw [hEq]
      exact (principalUnits K (n + m)).mul_mem ih hz

/-- Ring-valued form of the tail-control statement: the two finite correction
products are congruent modulo `𝓂^(n+m)`. -/
def principalUnitsCorrectionProduct_div_sub_one_mem
    (K : Type u) [Field K] [ValuativeRel K] (n m d : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d))  := (mem_principalUnits_iff K
    (principalUnitsCorrectionProduct K n z (m + d) /
      principalUnitsCorrectionProduct K n z m) (n + m)).1
    (principalUnitsCorrectionProduct_div_mem K n m d z)

/-- Rewrites a difference of units as the earlier unit times a quotient error.
This is the algebraic bridge from multiplicative tail control to additive
uniformity control. -/
lemma unit_sub_eq_mul_div_sub_one
    (K : Type u) [Field K] [ValuativeRel K] (a b : 𝒪[K]ˣ) :
    (a : 𝒪[K]) - (b : 𝒪[K]) =
      (b : 𝒪[K]) * (((a / b : 𝒪[K]ˣ) : 𝒪[K]) - 1) := by
  have hmul : (b : 𝒪[K]) * ((a / b : 𝒪[K]ˣ) : 𝒪[K]) = (a : 𝒪[K]) := by
    simp [div_eq_mul_inv, mul_left_comm]
  calc
    (a : 𝒪[K]) - (b : 𝒪[K]) =
        (b : 𝒪[K]) * ((a / b : 𝒪[K]ˣ) : 𝒪[K]) - (b : 𝒪[K]) := by
      rw [hmul]
    _ = (b : 𝒪[K]) * (((a / b : 𝒪[K]ˣ) : 𝒪[K]) - 1) := by
      ring

/-- Additive form of the correction-product tail control. This is the form
needed by the additive uniformity on the valuation integer ring. -/
theorem principalUnitsCorrectionProduct_sub_mem
    (K : Type u) [Field K] [ValuativeRel K] (n m d : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    ((principalUnitsCorrectionProduct K n z (m + d) : 𝒪[K]ˣ) : 𝒪[K]) -
        ((principalUnitsCorrectionProduct K n z m : 𝒪[K]ˣ) : 𝒪[K]) ∈
      (𝓂[K] ^ (n + m) : Ideal 𝒪[K]) := by
  let a  := principalUnitsCorrectionProduct K n z (m + d)
  let b  := principalUnitsCorrectionProduct K n z m
  have htail : (((a / b : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈
      (𝓂[K] ^ (n + m) : Ideal 𝒪[K]) := by
    apply principalUnitsCorrectionProduct_div_sub_one_mem
  rw [unit_sub_eq_mul_div_sub_one K a b]
  exact Ideal.mul_mem_left _ _ htail

/-- Uniform-tail algebraic input: two sufficiently late correction products
are congruent modulo any fixed earlier level of the maximal-ideal filtration. -/
theorem principalUnitsCorrectionProduct_sub_mem_of_le
    (K : Type u) [Field K] [ValuativeRel K] (n N i j : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d))
    (hi : N ≤ i) (hj : N ≤ j) :
    ((principalUnitsCorrectionProduct K n z i : 𝒪[K]ˣ) : 𝒪[K]) -
        ((principalUnitsCorrectionProduct K n z j : 𝒪[K]ˣ) : 𝒪[K]) ∈
      (𝓂[K] ^ (n + N) : Ideal 𝒪[K]) := by
  by_cases hji : j ≤ i
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
    exact Ideal.pow_le_pow_right (Nat.add_le_add_left hj n)
      (principalUnitsCorrectionProduct_sub_mem K n j d z)
  · have hij  := Nat.le_of_not_ge hji
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    have hdiff :
        ((principalUnitsCorrectionProduct K n z (i + d) : 𝒪[K]ˣ) : 𝒪[K]) -
            ((principalUnitsCorrectionProduct K n z i : 𝒪[K]ˣ) : 𝒪[K]) ∈
          (𝓂[K] ^ (n + N) : Ideal 𝒪[K]) := Ideal.pow_le_pow_right (Nat.add_le_add_left hi n)
        (principalUnitsCorrectionProduct_sub_mem K n i d z)
    have hEq :
        ((principalUnitsCorrectionProduct K n z i : 𝒪[K]ˣ) : 𝒪[K]) -
            ((principalUnitsCorrectionProduct K n z (i + d) : 𝒪[K]ˣ) : 𝒪[K]) =
          -(((principalUnitsCorrectionProduct K n z (i + d) : 𝒪[K]ˣ) : 𝒪[K]) -
            ((principalUnitsCorrectionProduct K n z i : 𝒪[K]ˣ) : 𝒪[K])) := by
      ring
    rw [hEq]
    exact (𝓂[K] ^ (n + N) : Ideal 𝒪[K]).neg_mem hdiff

section
variable (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d))
include K n z
/-- The finite correction products form a Cauchy sequence in the valuation
integer ring. This is the first complete-side output of the tail estimates. -/
theorem principalUnitsCorrectionProduct_cauchySeq
      :
    CauchySeq fun d : Nat =>
      ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]) := by
  rw [cauchySeq_iff]
  intro V hV
  rw [uniformity_eq_comap_nhds_zero 𝒪[K]] at hV
  rw [mem_comap] at hV
  rcases hV with ⟨s, hs, hsub⟩
  rcases eventually_maximalIdeal_pow_subset_nhds_zero K s hs with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i hi j hj
  apply hsub
  exact hN (n + N) (Nat.le_add_left N n)
    (principalUnitsCorrectionProduct_sub_mem_of_le K n N j i z hj hi)

/-- Completeness of the valuation integer ring gives a limit for the finite
correction products. The statement deliberately stops at an `𝒪[K]`-valued
limit; proving that the limit is a unit and remains in the intended
principal-unit level is the next frontier. -/
def exists_tendsto_principalUnitsCorrectionProduct
       :=
  cauchySeq_tendsto_of_complete
    (principalUnitsCorrectionProduct_cauchySeq K n z)

/-- Any limit of the correction-product sequence still satisfies the defining
congruence of `U^n`, viewed inside the valuation integer ring. -/
theorem principalUnitsCorrectionProduct_limit_sub_one_mem
      (x : 𝒪[K])
    (hx : Tendsto
      (fun d : Nat => ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]))
      atTop (nhds x)) :
    x - 1 ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  have hclosed := isClosed_maximalIdeal_pow K n
  refine hclosed.mem_of_tendsto
    (f := fun d : Nat =>
      ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]) - 1)
    (b := (atTop : Filter Nat)) (x := x - 1) ?_ ?_
  · exact hx.sub tendsto_const_nhds
  · exact Eventually.of_forall fun d =>
      (mem_principalUnits_iff K (principalUnitsCorrectionProduct K n z d) n).1
        (principalUnitsCorrectionProduct_mem K n z d)

/-- Complete-side output with the retained principal-unit congruence: the
finite correction products have an `𝒪[K]`-valued limit whose difference from
`1` lies in `𝓂^n`. -/
theorem exists_tendsto_principalUnitsCorrectionProduct_sub_one_mem
      :
    ∃ x : 𝒪[K], Tendsto
        (fun d : Nat => ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]))
        atTop (nhds x) ∧
      x - 1 ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  rcases exists_tendsto_principalUnitsCorrectionProduct K n z with ⟨x, hx⟩
  exact ⟨x, hx, principalUnitsCorrectionProduct_limit_sub_one_mem K n z x hx⟩
end


section
variable (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat)
include K n
/-- The concrete quotient equivalence sends a principal-unit class to the corresponding
`QuotientGroup` class. -/
@[simp]
theorem principalUnitsSuccQuotConcreteEquiv_mk
      (u : principalUnits K n) :
    principalUnitsSuccQuotConcreteEquiv K n
        (principalUnitsSuccQuotMk K n u) =
      QuotientGroup.mk u :=
  rfl



























































/-- Every class in `U^n/U^(n+1)` has a representative in `U^n`. -/
def principalUnitsSuccQuotMk_surjective
       :=
  QuotientGroup.mk'_surjective ((principalUnits K (n + 1)).subgroupOf (principalUnits K n))
























































/-- The class of a principal unit is trivial exactly when the unit belongs to `U^(n+1)`. -/
theorem principalUnitsSuccQuotMk_eq_one_iff
     
    (u : principalUnits K n) :
    principalUnitsSuccQuotMk K n u = 1 ↔
      u ∈ (principalUnits K (n + 1)).subgroupOf (principalUnits K n) := by
  constructor
  · intro h
    apply (QuotientGroup.eq_one_iff
      (N := (principalUnits K (n + 1)).subgroupOf (principalUnits K n)) u).mp
    have h' := congrArg (principalUnitsSuccQuotConcreteEquiv K n) h
    simpa using h'
  · intro h
    apply (principalUnitsSuccQuotConcreteEquiv K n).injective
    simpa using
      (QuotientGroup.eq_one_iff
        (N := (principalUnits K (n + 1)).subgroupOf (principalUnits K n)) u).mpr h



















/-- Two principal units define the same successive-quotient class exactly when their quotient lies
in `U^(n+1)`. -/
theorem principalUnitsSuccQuotMk_eq_iff_div_mem
     
    (u v : principalUnits K n) :
    principalUnitsSuccQuotMk K n u = principalUnitsSuccQuotMk K n v ↔
      u / v ∈ (principalUnits K (n + 1)).subgroupOf (principalUnits K n) := by
  constructor
  · intro h
    have h' := congrArg (principalUnitsSuccQuotConcreteEquiv K n) h
    exact (QuotientGroup.eq_iff_div_mem
      (N := (principalUnits K (n + 1)).subgroupOf (principalUnits K n))).mp h'
  · intro h
    apply (principalUnitsSuccQuotConcreteEquiv K n).injective
    exact (QuotientGroup.eq_iff_div_mem
      (N := (principalUnits K (n + 1)).subgroupOf (principalUnits K n))).mpr h































/-- Membership in the embedded subgroup `U^(n+1)` is equivalent to congruence to one modulo
`𝓂^(n+1)`. -/
theorem mem_principalUnits_succ_subgroupOf_iff
     
    (u : principalUnits K n) :
    u ∈ (principalUnits K (n + 1)).subgroupOf (principalUnits K n) ↔
      (((u : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈
        (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) := by
  rw [Subgroup.mem_subgroupOf, mem_principalUnits_iff]

/-- The submodule `𝓂^(n+1)` inside `𝓂^n`. -/
abbrev maximalIdealPowSuccSubmodule
      :
    Submodule (𝒪[K]) ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) :=
  Submodule.comap (Submodule.subtype (p := (𝓂[K] ^ n : Ideal 𝒪[K])))
    ((𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) : Submodule (𝒪[K]) (𝒪[K]))

/-- The additive ideal-power quotient `𝓂^n/𝓂^(n+1)`. -/
def MaximalIdealPowSuccQuot
      : Type u :=
  ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸ maximalIdealPowSuccSubmodule K n
end


/-- Equips the additive quotient `𝓂^n/𝓂^(n+1)` with its additive commutative group structure. -/
instance maximalIdealPowSuccQuotAddCommGroup
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    AddCommGroup (MaximalIdealPowSuccQuot K n) := by
  change AddCommGroup
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n)
  infer_instance

/-- Equips `𝓂^n/𝓂^(n+1)` with the module structure induced from the valuation ring. -/
instance maximalIdealPowSuccQuotModule
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Module 𝒪[K] (MaximalIdealPowSuccQuot K n) := by
  change Module 𝒪[K]
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n)
  infer_instance

section
variable (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
include K n
/-- Explicit access to the concrete submodule-quotient representation. -/
def maximalIdealPowSuccQuotConcreteLinearEquiv
      :
    MaximalIdealPowSuccQuot K n ≃ₗ[𝒪[K]]
      (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
        maximalIdealPowSuccSubmodule K n) := by
  change
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
        maximalIdealPowSuccSubmodule K n) ≃ₗ[𝒪[K]]
      (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
        maximalIdealPowSuccSubmodule K n)
  exact LinearEquiv.refl 𝒪[K] _

/-- The quotient map `𝓂^n → 𝓂^n/𝓂^(n+1)`. -/
def maximalIdealPowSuccQuotMk
      :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) →ₗ[𝒪[K]]
      MaximalIdealPowSuccQuot K n := by
  change ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) →ₗ[𝒪[K]]
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n)
  exact Submodule.mkQ (maximalIdealPowSuccSubmodule K n)

/-- The concrete linear equivalence sends an ideal-power class to the corresponding
submodule-quotient class. -/
@[simp]
theorem maximalIdealPowSuccQuotConcreteLinearEquiv_mk
     
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotConcreteLinearEquiv K n
        (maximalIdealPowSuccQuotMk K n a) =
      Submodule.Quotient.mk a :=
  rfl
end








/-- Eliminate an ideal-power quotient class through its canonical class map. -/
protected theorem MaximalIdealPowSuccQuot.inductionOn
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : MaximalIdealPowSuccQuot K n → Prop}
    (q : MaximalIdealPowSuccQuot K n)
    (h : ∀ a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u),
      motive (maximalIdealPowSuccQuotMk K n a)) :
    motive q := by
  change motive
    (show ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n from q)
  refine Quotient.inductionOn q ?_
  intro a
  exact h a

/-- Binary elimination through arbitrary ideal-power representatives. -/
protected theorem MaximalIdealPowSuccQuot.inductionOn₂
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : MaximalIdealPowSuccQuot K n →
      MaximalIdealPowSuccQuot K n → Prop}
    (q r : MaximalIdealPowSuccQuot K n)
    (h : ∀ a b : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u),
      motive (maximalIdealPowSuccQuotMk K n a)
        (maximalIdealPowSuccQuotMk K n b)) :
    motive q r := by
  refine MaximalIdealPowSuccQuot.inductionOn n
    (motive := fun q' => motive q' r) q ?_
  intro a
  refine MaximalIdealPowSuccQuot.inductionOn n
    (motive := fun r' => motive (maximalIdealPowSuccQuotMk K n a) r') r ?_
  intro b
  exact h a b

section
variable {K : Type u} {P : Sort*} [Field K] [ValuativeRel K] (n : Nat)
    (f : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) → P)
    (h : ∀ a b, a - b ∈ maximalIdealPowSuccSubmodule K n →
      f a = f b)
include K P n f h
/-- Descend an arbitrary representative-level function that is constant
modulo `𝓂^(n+1)`. -/
def maximalIdealPowSuccQuotLift
      :
    MaximalIdealPowSuccQuot K n → P := by
  change
    ((((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n) → P)
  refine Quotient.lift f ?_
  intro a b hab
  have hq :
      (Submodule.Quotient.mk a :
        ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
          maximalIdealPowSuccSubmodule K n) =
        Submodule.Quotient.mk b :=
    Quotient.sound hab
  exact h a b
    ((Submodule.Quotient.eq (maximalIdealPowSuccSubmodule K n)).1 hq)

/-- A function descended to `𝓂^n/𝓂^(n+1)` agrees with the original function on representatives. -/
@[simp]
theorem maximalIdealPowSuccQuotLift_mk
     
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotLift n f h
        (maximalIdealPowSuccQuotMk K n a) = f a :=
  rfl
end


section
variable {K : Type u} {M : Type*} [Field K] [ValuativeRel K]
    [AddCommGroup M] [Module 𝒪[K] M] (n : Nat)
    (f : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) →ₗ[𝒪[K]] M)
    (h : maximalIdealPowSuccSubmodule K n ≤ f.ker)
include K M n f h
/-- Descend a linear map that vanishes on `𝓂^(n+1)` inside `𝓂^n`. -/
def maximalIdealPowSuccQuotLinearLift
      :
    MaximalIdealPowSuccQuot K n →ₗ[𝒪[K]] M := by
  change
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n) →ₗ[𝒪[K]] M
  exact (maximalIdealPowSuccSubmodule K n).liftQ f h

/-- A linear map descended to `𝓂^n/𝓂^(n+1)` agrees with the original linear map on representatives.
A linear map descended to `𝓂^n/𝓂^(n+1)` agrees with the original linear map on representatives. -/
@[simp]
theorem maximalIdealPowSuccQuotLinearLift_mk
     
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotLinearLift n f h
        (maximalIdealPowSuccQuotMk K n a) = f a :=
  rfl
end


section
variable (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u))
include K n a
/-- An element of `𝓂^n` belongs to the defining submodule exactly when its value lies in `𝓂^(n+1)`.
An element of `𝓂^n` belongs to the defining submodule exactly when its value lies in `𝓂^(n+1)`. -/
theorem mem_maximalIdealPowSuccSubmodule_iff
      :
    a ∈ maximalIdealPowSuccSubmodule K n ↔
      (a : 𝒪[K]) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) :=
  Iff.rfl

/-- The class of an element of `𝓂^n` is zero exactly when its value lies in `𝓂^(n+1)`. -/
theorem maximalIdealPowSuccQuotMk_eq_zero_iff
      :
    maximalIdealPowSuccQuotMk K n a = 0 ↔
      (a : 𝒪[K]) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) := by
  change (Submodule.Quotient.mk a :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl
end


/-- Two elements of `𝓂^n` define the same quotient class exactly when their difference lies in
`𝓂^(n+1)`. -/
@[simp]
theorem maximalIdealPowSuccQuotMk_eq_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (a b : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotMk K n a =
        maximalIdealPowSuccQuotMk K n b ↔
      a - b ∈ maximalIdealPowSuccSubmodule K n := by
  change (Submodule.Quotient.mk a :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n) =
    Submodule.Quotient.mk b ↔ _
  apply Submodule.Quotient.eq

section
variable (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a : 𝒪[K]) (ha : a ∈ (𝓂[K] ^ n : Ideal 𝒪[K]))
include K n hn a ha
/-- If `a ∈ 𝓂^n` with `n ≥ 1`, then `1 + a` is a unit of the valuation ring. -/
theorem isUnit_one_add_of_mem_maximalIdeal_pow
      : IsUnit (1 + a) := by
  have ha1 : a ∈ (𝓂[K] : Ideal 𝒪[K]) := by
    have hle : (𝓂[K] ^ n : Ideal 𝒪[K]) ≤ (𝓂[K] ^ 1 : Ideal 𝒪[K]) :=
      Ideal.pow_le_pow_right hn
    simpa using hle ha
  have hnon : (-a) ∈ nonunits 𝒪[K] := by
    rw [← IsLocalRing.mem_maximalIdeal]
    exact (𝓂[K] : Ideal 𝒪[K]).neg_mem ha1
  have hunit : IsUnit (1 - (-a)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-a) hnon
  simpa [sub_neg_eq_add] using hunit

/-- The unit `1 + a` attached to an element `a ∈ 𝓂^n`, for `n ≥ 1`. -/
noncomputable def principalUnitOneAddOfMemPow
      : 𝒪[K]ˣ :=
  (isUnit_one_add_of_mem_maximalIdeal_pow K hn a ha).unit

/-- The valuation-ring value of the unit constructed from `a ∈ 𝓂^n` is `1 + a`. -/
@[simp]
theorem principalUnitOneAddOfMemPow_val
      :
    ((principalUnitOneAddOfMemPow K hn a ha : 𝒪[K]ˣ) : 𝒪[K]) = 1 + a :=
  IsUnit.unit_spec (isUnit_one_add_of_mem_maximalIdeal_pow K hn a ha)

/-- The unit `1 + a`, viewed as an element of `U^n`. -/
noncomputable def principalUnitOneAddOfMemPowSubgroup
      : principalUnits K n :=
  ⟨principalUnitOneAddOfMemPow K hn a ha, by
    rw [mem_principalUnits_iff]
    simp [principalUnitOneAddOfMemPow_val, ha]
  ⟩

/-- Viewing the unit `1 + a` in `U^n` preserves its underlying valuation-ring unit. -/
@[simp]
theorem principalUnitOneAddOfMemPowSubgroup_val
      :
    ((principalUnitOneAddOfMemPowSubgroup K hn a ha : principalUnits K n) : 𝒪[K]ˣ) =
      principalUnitOneAddOfMemPow K hn a ha :=
  rfl
end


/-- For `n ≥ 1`, the complete limit of finite correction products can be
viewed as an element of the principal-unit subgroup `U^n`. -/
theorem exists_tendsto_principalUnitsCorrectionProduct_principalUnit
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat) (hn : 1 ≤ n)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    ∃ x : principalUnits K n, Tendsto
      (fun d : Nat => ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]))
      atTop (nhds ((x : 𝒪[K]ˣ) : 𝒪[K])) := by
  rcases exists_tendsto_principalUnitsCorrectionProduct_sub_one_mem K n z with
    ⟨x, hx, hmem⟩
  let u  :=
    principalUnitOneAddOfMemPowSubgroup K hn (x - 1) hmem
  refine ⟨u, ?_⟩
  have huval : ((u : 𝒪[K]ˣ) : 𝒪[K]) = x := by
    aesop
  simpa [huval] using hx

section
variable (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n)
include K n hn
/-- The concrete map `𝓂^n → U^n/U^(n+1)` sending `a` to the class of `1 + a`. -/
noncomputable def principalUnitsSuccQuotOfIdealPow
      :
    (𝓂[K] ^ n : Ideal 𝒪[K]) → PrincipalUnitsSuccQuot K n :=
  fun a =>
    principalUnitsSuccQuotMk K n
      (principalUnitOneAddOfMemPowSubgroup K hn a.1 a.2)

/-- The map from `𝓂^n` sends `a` to the successive principal-unit class represented by `1 + a`. -/
@[simp]
theorem principalUnitsSuccQuotOfIdealPow_apply
     
    (a : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    principalUnitsSuccQuotOfIdealPow K n hn a =
      principalUnitsSuccQuotMk K n
        (principalUnitOneAddOfMemPowSubgroup K hn a.1 a.2) :=
  rfl

/-- If a principal unit has the same first-order term as `1 + a` modulo
`𝓂^(n+1)`, then it has the same class in `U^n/U^(n+1)`. -/
theorem principalUnitsSuccQuotMk_eq_oneAdd_of_sub_one_sub_mem_succ
     
    (u : principalUnits K n) (a : (𝓂[K] ^ n : Ideal 𝒪[K]))
    (h : (((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 - (a : 𝒪[K])) ∈
      (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])) :
    principalUnitsSuccQuotMk K n u =
      principalUnitsSuccQuotOfIdealPow K n hn a := by
  rw [principalUnitsSuccQuotOfIdealPow_apply]
  apply (principalUnitsSuccQuotMk_eq_iff_div_mem K n _ _).2
  rw [mem_principalUnits_succ_subgroupOf_iff]
  change ((((u : 𝒪[K]ˣ) /
        principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈
    (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])
  rw [show ((((u : 𝒪[K]ˣ) /
        principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 : 𝒪[K]ˣ) : 𝒪[K]) - 1) =
      (((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 - (a : 𝒪[K])) *
        ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ by
    simp only [div_eq_mul_inv, Units.val_mul]
    have hunit :
        ((principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 : 𝒪[K]ˣ) : 𝒪[K]) *
          ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ = 1 := by
      simp
    calc
      ((u : 𝒪[K]ˣ) : 𝒪[K]) *
            ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ - 1 =
          ((u : 𝒪[K]ˣ) : 𝒪[K]) *
              ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ -
            ((principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 : 𝒪[K]ˣ) : 𝒪[K]) *
              ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ := by
        rw [hunit]
      _ = (((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 - (a : 𝒪[K])) *
          ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ := by
        rw [principalUnitOneAddOfMemPow_val K hn (a : 𝒪[K]) a.2]
        ring]
  exact (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]).mul_mem_right _ h

/-- Elements of `𝓂^(n+1)` map to the trivial class in `U^n/U^(n+1)`. -/
theorem principalUnitsSuccQuotOfIdealPow_eq_one_of_mem_succ
     
    (a : (𝓂[K] ^ n : Ideal 𝒪[K]))
    (ha : (a : 𝒪[K]) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])) :
    principalUnitsSuccQuotOfIdealPow K n hn a = 1 := by
  apply (principalUnitsSuccQuotMk_eq_one_iff K n _).2
  rw [mem_principalUnits_succ_subgroupOf_iff]
  simp [principalUnitOneAddOfMemPowSubgroup, principalUnitOneAddOfMemPow_val, ha]











/-- The map `a ↦ 1 + a` is insensitive to changing `a` modulo `𝓂^(n+1)`. -/
theorem principalUnitsSuccQuotOfIdealPow_eq_of_sub_mem_succ
     
    (a b : (𝓂[K] ^ n : Ideal 𝒪[K]))
    (hab : ((a : 𝒪[K]) - (b : 𝒪[K])) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])) :
    principalUnitsSuccQuotOfIdealPow K n hn a =
      principalUnitsSuccQuotOfIdealPow K n hn b := by
  apply (principalUnitsSuccQuotMk_eq_iff_div_mem K n _ _).2
  rw [mem_principalUnits_succ_subgroupOf_iff]
  change (((principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 /
            principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2 : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈
    (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])
  rw [show (((principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 /
            principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2 : 𝒪[K]ˣ) : 𝒪[K]) - 1) =
      ((a : 𝒪[K]) - (b : 𝒪[K])) *
        ↑(principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2)⁻¹ by
    simp only [div_eq_mul_inv, Units.val_mul]
    rw [principalUnitOneAddOfMemPow_val K hn (a : 𝒪[K]) a.2]
    have hbval :
        ((principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2 : 𝒪[K]ˣ) : 𝒪[K]) =
          1 + (b : 𝒪[K]) :=
      principalUnitOneAddOfMemPow_val K hn (b : 𝒪[K]) b.2
    have hbinv :
        ((principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2 : 𝒪[K]ˣ) : 𝒪[K]) *
          ↑(principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2)⁻¹ = 1 := by
      simp
    calc
      (1 + (a : 𝒪[K])) * ↑(principalUnitOneAddOfMemPow K hn ↑b b.2)⁻¹ - 1 =
          (1 + (a : 𝒪[K])) * ↑(principalUnitOneAddOfMemPow K hn ↑b b.2)⁻¹ -
            ((principalUnitOneAddOfMemPow K hn ↑b b.2 : 𝒪[K]ˣ) : 𝒪[K]) *
              ↑(principalUnitOneAddOfMemPow K hn ↑b b.2)⁻¹ := by
        rw [hbinv]
      _ = (↑a - ↑b) * ↑(principalUnitOneAddOfMemPow K hn ↑b b.2)⁻¹ := by
        rw [hbval]
        ring]
  exact (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]).mul_mem_right _ hab














/-- The descent of `a ↦ [1 + a]` to `𝓂^n/𝓂^(n+1)`. -/
noncomputable def principalUnitsSuccQuotOfMaximalIdealPowSuccQuot
      :
    MaximalIdealPowSuccQuot K n → PrincipalUnitsSuccQuot K n :=
  maximalIdealPowSuccQuotLift n
    (principalUnitsSuccQuotOfIdealPow K n hn)
    (fun a b hab =>
      principalUnitsSuccQuotOfIdealPow_eq_of_sub_mem_succ K n hn a b ((mem_maximalIdealPowSuccSubmodule_iff K n (a - b)).1 hab))

/-- The descended map on `𝓂^n/𝓂^(n+1)` sends a representative class to the class represented by `1 +
a`. -/
@[simp]
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk
     
    (a : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
        (maximalIdealPowSuccQuotMk K n a) =
      principalUnitsSuccQuotOfIdealPow K n hn a :=
  rfl
end


/-- Products of two elements of `𝓂^n`, for `n ≥ 1`, lie in `𝓂^(n+1)`. -/
theorem maximalIdealPow_mul_mem_succ
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a b : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    ((a : 𝒪[K]) * (b : 𝒪[K])) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) := by
  have hmul : ((a : 𝒪[K]) * (b : 𝒪[K])) ∈ (𝓂[K] ^ (n + n) : Ideal 𝒪[K]) := by
    simpa [pow_add] using (Ideal.mul_mem_mul a.2 b.2)
  have hle : (𝓂[K] ^ (n + n) : Ideal 𝒪[K]) ≤
      (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) :=
    Ideal.pow_le_pow_right (Nat.add_le_add_left hn n)
  exact hle hmul

section
variable (K : Type u) [Field K] [ValuativeRel K] {ι : Type*}
    (s : Finset ι) (n : Nat) (hn : 1 ≤ n) (a : ι → 𝒪[K])
    (ha : ∀ i ∈ s, a i ∈ (𝓂[K] ^ n : Ideal 𝒪[K]))
include K ι s n hn a ha
/-- If every `aᵢ` lies in `𝓂^n` with `n ≥ 1`, then
`∏ᵢ (1 + aᵢ) - 1` lies in the maximal ideal. -/
theorem finset_prod_one_add_sub_one_mem_maximalIdeal_of_mem_pow
      :
    (s.prod fun i => 1 + a i) - 1 ∈ (𝓂[K] : Ideal 𝒪[K]) := by
  classical
  revert a
  refine Finset.induction_on s ?base ?step
  · intro a ha
    simp
  · intro i s hi ih a ha
    have hai_pow : a i ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := ha i (by simp [hi])
    have hai : a i ∈ (𝓂[K] : Ideal 𝒪[K]) := by
      have hle : (𝓂[K] ^ n : Ideal 𝒪[K]) ≤ (𝓂[K] ^ 1 : Ideal 𝒪[K]) :=
        Ideal.pow_le_pow_right hn
      simpa using hle hai_pow
    have hs : ∀ j ∈ s, a j ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
      intro j hj
      exact ha j (by simp [hj])
    have hprod : (s.prod fun j => 1 + a j) - 1 ∈ (𝓂[K] : Ideal 𝒪[K]) :=
      ih a hs
    have hterm : a i * (s.prod fun j => 1 + a j) ∈ (𝓂[K] : Ideal 𝒪[K]) :=
      (𝓂[K] : Ideal 𝒪[K]).mul_mem_right _ hai
    rw [Finset.prod_insert hi]
    rw [show (1 + a i) * (s.prod fun j => 1 + a j) - 1 =
        ((s.prod fun j => 1 + a j) - 1) +
          a i * (s.prod fun j => 1 + a j) by
      ring]
    exact (𝓂[K] : Ideal 𝒪[K]).add_mem hprod hterm

/-- First-order expansion of products in the principal-unit filtration:
if every `aᵢ ∈ 𝓂^n` and `n ≥ 1`, then
`∏ᵢ (1 + aᵢ) ≡ 1 + Σᵢ aᵢ mod 𝓂^(n+1)`. -/
theorem finset_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ
      :
    (s.prod fun i => 1 + a i) - 1 - (s.sum fun i => a i) ∈
      (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) := by
  classical
  revert a
  refine Finset.induction_on s ?base ?step
  · intro a ha
    simp
  · intro i s hi ih a ha
    have hai : a i ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := ha i (by simp [hi])
    have hs : ∀ j ∈ s, a j ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
      intro j hj
      apply ha <;> aesop
    have hind :
        (s.prod fun j => 1 + a j) - 1 - (s.sum fun j => a j) ∈
          (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) :=
      ih a hs
    have hprod  :=
      finset_prod_one_add_sub_one_mem_maximalIdeal_of_mem_pow K s n hn a hs
    have hmul_raw :
        a i * ((s.prod fun j => 1 + a j) - 1) ∈
          (𝓂[K] ^ n : Ideal 𝒪[K]) * (𝓂[K] : Ideal 𝒪[K]) :=
      Ideal.mul_mem_mul hai hprod
    have hmul :
        a i * ((s.prod fun j => 1 + a j) - 1) ∈
          (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) := hmul_raw
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [show (1 + a i) * (s.prod fun j => 1 + a j) - 1 -
          (a i + (s.sum fun j => a j)) =
        ((s.prod fun j => 1 + a j) - 1 - (s.sum fun j => a j)) +
          a i * ((s.prod fun j => 1 + a j) - 1) by
      ring]
    exact (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]).add_mem hind hmul
end


section
variable (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n)
include K n hn
/-- The zero element of `𝓂^n` maps to the identity class in `U^n/U^(n+1)`. -/
@[simp]
theorem principalUnitsSuccQuotOfIdealPow_zero
      :
    principalUnitsSuccQuotOfIdealPow K n hn (0 : (𝓂[K] ^ n : Ideal 𝒪[K])) = 1 := by
  apply principalUnitsSuccQuotOfIdealPow_eq_one_of_mem_succ
  simp

/-- Modulo `U^(n+1)`, the class represented by `1 + (a+b)` is the product of the classes represented
by `1+a` and `1+b`. -/
theorem principalUnitsSuccQuotOfIdealPow_add
     
    (a b : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    principalUnitsSuccQuotOfIdealPow K n hn (a + b) =
      principalUnitsSuccQuotOfIdealPow K n hn a *
        principalUnitsSuccQuotOfIdealPow K n hn b := by
  rw [principalUnitsSuccQuotOfIdealPow_apply,
    principalUnitsSuccQuotOfIdealPow_apply,
    principalUnitsSuccQuotOfIdealPow_apply,
    ← (principalUnitsSuccQuotMk K n).map_mul]
  symm
  apply (principalUnitsSuccQuotMk_eq_iff_div_mem K n _ _).2
  rw [mem_principalUnits_succ_subgroupOf_iff]
  change ((((principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 *
              principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2 : 𝒪[K]ˣ) /
            principalUnitOneAddOfMemPow K hn
              ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2 :
              𝒪[K]ˣ) : 𝒪[K]) - 1) ∈
    (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])
  rw [show ((((principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 *
              principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2 : 𝒪[K]ˣ) /
            principalUnitOneAddOfMemPow K hn
              ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2 :
              𝒪[K]ˣ) : 𝒪[K]) - 1) =
      ((a : 𝒪[K]) * (b : 𝒪[K])) *
        ↑(principalUnitOneAddOfMemPow K hn
          ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2)⁻¹ by
    simp only [div_eq_mul_inv, Units.val_mul]
    rw [principalUnitOneAddOfMemPow_val K hn (a : 𝒪[K]) a.2,
      principalUnitOneAddOfMemPow_val K hn (b : 𝒪[K]) b.2]
    have habval :
        ((principalUnitOneAddOfMemPow K hn
            ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2 : 𝒪[K]ˣ) :
            𝒪[K]) =
          1 + (a : 𝒪[K]) + (b : 𝒪[K]) := by
      rw [principalUnitOneAddOfMemPow_val K hn
        ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2]
      change 1 + ((a : 𝒪[K]) + (b : 𝒪[K])) = 1 + (a : 𝒪[K]) + (b : 𝒪[K])
      ring
    have habinv :
        ((principalUnitOneAddOfMemPow K hn
            ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2 : 𝒪[K]ˣ) :
            𝒪[K]) *
          ↑(principalUnitOneAddOfMemPow K hn
            ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2)⁻¹ = 1 := by
      simp
    calc
      ((1 + (a : 𝒪[K])) * (1 + (b : 𝒪[K]))) *
            ↑(principalUnitOneAddOfMemPow K hn
              ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2)⁻¹ - 1 =
          ((1 + (a : 𝒪[K])) * (1 + (b : 𝒪[K]))) *
              ↑(principalUnitOneAddOfMemPow K hn
                ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2)⁻¹ -
            ((principalUnitOneAddOfMemPow K hn
                ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2 :
                𝒪[K]ˣ) : 𝒪[K]) *
              ↑(principalUnitOneAddOfMemPow K hn
                ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2)⁻¹ := by
        rw [habinv]
      _ = ((a : 𝒪[K]) * (b : 𝒪[K])) *
          ↑(principalUnitOneAddOfMemPow K hn
            ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2)⁻¹ := by
        rw [habval]
        ring]
  exact (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]).mul_mem_right _
    (maximalIdealPow_mul_mem_succ K hn a b)

/-- The descended map from `𝓂^n/𝓂^(n+1)` sends zero to the identity principal-unit class. -/
@[simp]
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_map_zero
      :
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn 0 = 1 := by
  rw [← map_zero (maximalIdealPowSuccQuotMk K n)]
  change principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
      (maximalIdealPowSuccQuotMk K n (0 : (𝓂[K] ^ n : Ideal 𝒪[K]))) = 1
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk]
  apply principalUnitsSuccQuotOfIdealPow_zero

/-- The descended map sends addition in `𝓂^n/𝓂^(n+1)` to multiplication in `U^n/U^(n+1)`. -/
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_map_add
     
    (x y : MaximalIdealPowSuccQuot K n) :
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn (x + y) =
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x *
        principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn y := by
  refine MaximalIdealPowSuccQuot.inductionOn₂ n
    (motive := fun x' y' =>
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn (x' + y') =
        principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x' *
          principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn y') x y ?_
  intro a b
  let qa  := maximalIdealPowSuccQuotMk K n a
  let qb  := maximalIdealPowSuccQuotMk K n b
  have hleft :
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn (qa + qb) =
        principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
          (maximalIdealPowSuccQuotMk K n (a + b)) := by
    rfl
  have hrep :
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
          (maximalIdealPowSuccQuotMk K n (a + b)) =
        principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn qa *
          principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn qb := by
    dsimp [qa, qb]
    change principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
        (maximalIdealPowSuccQuotMk K n (a + b)) =
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
        (maximalIdealPowSuccQuotMk K n a) *
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
        (maximalIdealPowSuccQuotMk K n b)
    rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk,
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk,
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk]
    apply principalUnitsSuccQuotOfIdealPow_add
  exact hleft.trans hrep

/-- Additive form of the descended map `𝓂^n/𝓂^(n+1) → U^n/U^(n+1)`. -/
noncomputable def principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd
      :
    MaximalIdealPowSuccQuot K n →+ Additive (PrincipalUnitsSuccQuot K n) where
  toFun x := Additive.ofMul (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x)
  map_zero' := by
    change Additive.ofMul (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn 0) = 0
    simp [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_map_zero]
  map_add' x y := by
    simp_all [LocalFieldTheory.principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_map_add] <;> aesop

/-- The additive recoding of the descended map has the same underlying successive principal-unit
class. -/
@[simp]
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_apply
     
    (x : MaximalIdealPowSuccQuot K n) :
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn x =
      Additive.ofMul (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x) :=
  rfl

/-- The class represented by `1 + a` is trivial exactly when `a` lies in `𝓂^(n+1)`. -/
theorem principalUnitsSuccQuotOfIdealPow_eq_one_iff
     
    (a : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    principalUnitsSuccQuotOfIdealPow K n hn a = 1 ↔
      (a : 𝒪[K]) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) := by
  constructor
  · intro h
    have hmem := (principalUnitsSuccQuotMk_eq_one_iff K n _).1 h
    rw [mem_principalUnits_succ_subgroupOf_iff] at hmem
    simpa [principalUnitsSuccQuotOfIdealPow, principalUnitOneAddOfMemPowSubgroup,
      principalUnitOneAddOfMemPow_val] using hmem
  · intro ha
    apply principalUnitsSuccQuotOfIdealPow_eq_one_of_mem_succ <;> assumption

/-- The descended image of an ideal-power quotient class is trivial exactly when that class is zero.
The descended image of an ideal-power quotient class is trivial exactly when that class is zero. -/
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_eq_one_iff
     
    (x : MaximalIdealPowSuccQuot K n) :
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x = 1 ↔ x = 0 := by
  refine MaximalIdealPowSuccQuot.inductionOn n
    (motive := fun x' =>
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x' = 1 ↔ x' = 0)
    x ?_
  intro a
  rw [← map_zero (maximalIdealPowSuccQuotMk K n)]
  change principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
      (maximalIdealPowSuccQuotMk K n a) = 1 ↔
    (maximalIdealPowSuccQuotMk K n a : MaximalIdealPowSuccQuot K n) = 0
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk,
    maximalIdealPowSuccQuotMk_eq_zero_iff]
  apply principalUnitsSuccQuotOfIdealPow_eq_one_iff

/-- Every successive principal-unit class is represented by `1 + a` for some `a ∈ 𝓂^n`. -/
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_surjective
      :
    Function.Surjective (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn) := by
  intro x
  rcases principalUnitsSuccQuotMk_surjective K n x with ⟨u, rfl⟩
  let a0  := ((u : 𝒪[K]ˣ) : 𝒪[K]) - 1
  have ha0 : a0 ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
    dsimp [a0]
    exact (mem_principalUnits_iff K (u : 𝒪[K]ˣ) n).1 u.2
  let a : (𝓂[K] ^ n : Ideal 𝒪[K]) := ⟨a0, ha0⟩
  refine ⟨maximalIdealPowSuccQuotMk K n a, ?_⟩
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk,
    principalUnitsSuccQuotOfIdealPow_apply]
  congr 1
  dsimp [a]
  apply Subtype.ext
  rw [principalUnitOneAddOfMemPowSubgroup_val]
  apply Units.ext
  rw [principalUnitOneAddOfMemPow_val]
  dsimp [a0]
  ring

/-- The additive map induced by `a ↦ 1 + a` onto the successive principal-unit quotient is
surjective. -/
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_surjective
      :
    Function.Surjective (principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn) := by
  intro y
  rcases principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_surjective K n hn
      (Additive.toMul y) with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  change Additive.ofMul (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x) = y
  rw [hx]
  rfl

/-- The additive map induced by `a ↦ 1 + a` on successive quotients is injective. -/
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_injective
      :
    Function.Injective (principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn) := by
  intro x y hxy
  have hzero : principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hmul : principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn (x - y) = 1 := by
    assumption
  have hxmy  :=
    (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_eq_one_iff K n hn (x - y)).1 hmul
  exact sub_eq_zero.mp hxmy

/-- The additive isomorphism `𝓂^n/𝓂^(n+1) ≃ U^n/U^(n+1)` induced by `a ↦ 1+a`. -/
noncomputable def maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot
       :=
  AddEquiv.ofBijective (principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn)
    ⟨principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_injective K n hn,
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_surjective K n hn⟩

/-- The additive equivalence between successive ideal and principal-unit quotients agrees with the
descended `a ↦ 1+a` map. -/
@[simp]
theorem maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot_apply
     
    (x : MaximalIdealPowSuccQuot K n) :
    maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn x =
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn x :=
  rfl

/-- Multiplicative form of
`𝓂^n/𝓂^(n+1) ≃+ Additive (U^n/U^(n+1))`, suitable for the multiplicative
Herbrand quotient API. -/
noncomputable def maximalIdealPowSuccQuotMulEquivPrincipalUnitsSuccQuot
      :
    Multiplicative (MaximalIdealPowSuccQuot K n) ≃*
      PrincipalUnitsSuccQuot K n where
  toFun x :=
    Additive.toMul
      (maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn
        (Multiplicative.toAdd x))
  invFun x :=
    Multiplicative.ofAdd
      ((maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn).symm
        (Additive.ofMul x))
  left_inv := by
    intro x
    change Multiplicative.ofAdd
        ((maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn).symm
          (maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn
            (Multiplicative.toAdd x))) =
      Multiplicative.ofAdd (Multiplicative.toAdd x)
    exact congrArg Multiplicative.ofAdd
      ((maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn).left_inv
        (Multiplicative.toAdd x))
  right_inv := by
    intro x
    change Additive.toMul
        (maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn
          ((maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn).symm
            (Additive.ofMul x))) =
      Additive.toMul (Additive.ofMul x)
    apply congrArg <;> aesop
  map_mul' := by
    intro x y
    rw [show Multiplicative.toAdd (x * y) =
        Multiplicative.toAdd x + Multiplicative.toAdd y from rfl]
    change Additive.toMul
        (maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn
          (Multiplicative.toAdd x + Multiplicative.toAdd y)) =
      Additive.toMul
        (maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn
          (Multiplicative.toAdd x) +
        maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn
          (Multiplicative.toAdd y))
    exact congrArg Additive.toMul
      ((maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn).map_add
        (Multiplicative.toAdd x) (Multiplicative.toAdd y))

/-- The multiplicative recoding of the successive-quotient equivalence sends `a` to the
principal-unit class represented by `1+a`. -/
@[simp]
theorem maximalIdealPowSuccQuotMulEquivPrincipalUnitsSuccQuot_apply
     
    (x : MaximalIdealPowSuccQuot K n) :
    maximalIdealPowSuccQuotMulEquivPrincipalUnitsSuccQuot K n hn
        (Multiplicative.ofAdd x) =
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x :=
  rfl
end


end
end LocalFieldTheory
