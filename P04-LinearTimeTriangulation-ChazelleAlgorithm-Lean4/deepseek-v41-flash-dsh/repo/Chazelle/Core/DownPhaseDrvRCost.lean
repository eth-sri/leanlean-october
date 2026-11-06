module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvRInv

/-!
# Down-phase driver (RAM side), D1 part 2: the cost of the level loop

The level loop runs the levels `λ = p, μ(p), μ(μ(p)), …` while `λ ≥ 16` (`μ = nextLvl`).  Its
budget is the potential `pot f λ = f λ + f (μ λ) + …` (`pot`), where `f λ` is the budget of one
level plus the driver's bookkeeping, `lvlBudget K₁ cnt p λ = K₁ (Kb λ + 1) (lemma41Nat (μ λ) + 1)`
with `Kb λ = cnt λ (2^p + 2^⌈βλ⌉) / 2^⌈βλ⌉` the bound on the chord count given by (I3).

* `pot_le_sum`: the potential is at most the sum of the per-level bounds over `j ≤ λ`
  (the levels visited are distinct);
* `lemma41Nat_add_one_le`: `lemma41Nat g + 1 ≤ 4 lemma41Bound g` for `g ≥ 2`;
* `lvlBudget_le`: `f λ ≤ 4096 (C + 1) (4 K₁) 2^p downOverhead λ` for `16 ≤ λ ≤ p`, from
  `Cost.downStep_cost_le` (the regions are at most `K + 1 ≤ (C + 1)(2^p/2^⌈βλ⌉ + 1)`);
* **`pot_lvlBudget_le`**: `pot f λ ≤ potConst C K₁ · 2^p` for `λ ≤ p`, with the explicit
  constant `potConst C K₁ = 4500³ · 3000 · 4096 (C + 1) (4 K₁)` (`Cost.sum_downOverhead_le`).
-/

namespace Chazelle.Core

namespace DrvR

open Finset

@[expose] public section

/-- **The potential of the level loop**: `pot f λ = f λ + pot f (μ λ)` for `λ ≥ 16`, else `0`. -/
noncomputable def pot (f : ℕ → ℕ) (lam : ℕ) : ℕ :=
  if _h : 16 ≤ lam then f lam + pot f (nextLvl lam) else 0
termination_by lam
decreasing_by exact nextLvl_lt _h

theorem pot_of_le {f : ℕ → ℕ} {lam : ℕ} (h : 16 ≤ lam) :
    pot f lam = f lam + pot f (nextLvl lam) := by
  Ξ pot, dite_eq_left h

theorem pot_of_lt {f : ℕ → ℕ} {lam : ℕ} (h : lam < 16) : pot f lam = 0 := by
  rw [pot, dite_eq_right (⋄)]

/-- **The potential is at most the sum of the per-level bounds** over `j ≤ λ`. -/
theorem pot_le_sum (f : ℕ → ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (L₀ : ℕ)
    (hf : ∀ j, 16 ≤ j → j ≤ L₀ → (f j : ℝ) ≤ B j) :
    ∀ lam, lam ≤ L₀ → (pot f lam : ℝ) ≤ ∑ j ∈ range (lam + 1), B j := by
  intro lam
  induction lam using Nat.strong_induction_on with
  | _ lam ih =>
    intro hl
    by_cases h16 : 16 ≤ lam
    · Ξ pot_of_le h16
      have hlt := nextLvl_lt h16
      have hih := ih (nextLvl lam) hlt (⋄)
      have hsub : ∑ j ∈ range (nextLvl lam + 1), B j ≤ ∑ j ∈ range lam, B j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (⋄))
          (fun j _ _ => hB j)
      Ξ Finset.sum_range_succ
      push_cast
      have := hf lam h16 hl
      linarith
    · rw [pot_of_lt (⋄)]
      push_cast
      exact Finset.sum_nonneg (fun j _ => hB j)

/-! ## The budget of one level -/

/-- The bound on the chord count at level `λ` given by (I3):
`Kb λ = cnt λ (2^p + 2^⌈βλ⌉) / 2^⌈βλ⌉`. -/
noncomputable def kBound (cnt : ℕ → ℕ) (p lam : ℕ) : ℕ :=
  cnt lam * (2 ^ p + 2 ^ Cost.ceilBeta lam) / 2 ^ Cost.ceilBeta lam

/-- **The budget of one level** (with the driver's bookkeeping in the constant `K₁`):
`K₁ (Kb λ + 1) (lemma41Nat (μ λ) + 1)`. -/
noncomputable def lvlBudget (K₁ : ℕ) (cnt : ℕ → ℕ) (p lam : ℕ) : ℕ :=
  K₁ * ((kBound cnt p lam + 1) * (lemma41Nat (nextLvl lam) + 1))

/-- `lemma41Nat g + 1 ≤ 4 · lemma41Bound g` for `g ≥ 2`. -/
theorem lemma41Nat_add_one_le {g : ℕ} (hg : 2 ≤ g) :
    (lemma41Nat g : ℝ) + 1 ≤ 4 * Cost.lemma41Bound g := by
  unfold lemma41Nat
  Ξ Cost.lemma41Bound_eq
  have hc : (1 : ℝ) ≤ Nat.clog 2 g := by
    have : 1 ≤ Nat.clog 2 g := Nat.clog_pos (⊛) (by omega)
    exact_mod_cast this
  have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hq : (1 : ℝ) ≤ (2 : ℝ) ^ ((74 / 75 : ℝ) * g) :=
    Real.one_le_rpow (⊛) (by positivity)
  have e : (74 : ℝ) / 75 * g = (74 / 75 : ℝ) * g := ⊛
  Ξ e
  set x : ℝ := (2 : ℝ) ^ ((74 / 75 : ℝ) * g) with hx
  have hx0 : 0 ≤ (g : ℝ) ^ 2 * ((Nat.clog 2 g : ℝ) + 1) * x := ⟢
  have hceil := Nat.ceil_lt_add_one hx0
  have hg2 : (4 : ℝ) ≤ (g : ℝ) ^ 2 := ⊞
  have h1 : (g : ℝ) ^ 2 * ((Nat.clog 2 g : ℝ) + 1) * x ≤
      2 * ((g : ℝ) ^ 2 * (Nat.clog 2 g : ℝ) * x) := by
    have : (g : ℝ) ^ 2 * x ≥ 0 := ⟢
    nlinarith
  have h2 : (1 : ℝ) ≤ (g : ℝ) ^ 2 * (Nat.clog 2 g : ℝ) * x := by
    have h3 : (1 : ℝ) ≤ (g : ℝ) ^ 2 * (Nat.clog 2 g : ℝ) := ⊞
    nlinarith
  linarith

/-- `Kb λ + 1 ≤ (C + 1)(2^p / 2^⌈βλ⌉ + 1)` when `cnt λ ≤ C`. -/
theorem kBound_add_one_le {cnt : ℕ → ℕ} {C p lam : ℕ} (hc : cnt lam ≤ C) :
    (kBound cnt p lam : ℝ) + 1 ≤
      ((C : ℝ) + 1) * ((2 : ℝ) ^ p / (2 : ℝ) ^ Cost.ceilBeta lam + 1) := by
  unfold kBound
  have h2 : (0 : ℝ) < (2 : ℝ) ^ Cost.ceilBeta lam := ⟢
  have hdiv := Nat.cast_div_le (α := ℝ) (m := cnt lam * (2 ^ p + 2 ^ Cost.ceilBeta lam))
    (n := 2 ^ Cost.ceilBeta lam)
  push_cast at hdiv
  have e : (cnt lam : ℝ) * ((2 : ℝ) ^ p + (2 : ℝ) ^ Cost.ceilBeta lam) /
      (2 : ℝ) ^ Cost.ceilBeta lam = (cnt lam : ℝ) * ((2 : ℝ) ^ p / (2 : ℝ) ^ Cost.ceilBeta lam + 1) := by
    field_simp
  rw [e] at hdiv
  have hC : (cnt lam : ℝ) ≤ C := by exact_mod_cast hc
  have hy : (1 : ℝ) ≤ (2 : ℝ) ^ p / (2 : ℝ) ^ Cost.ceilBeta lam + 1 := by
    have : (0 : ℝ) ≤ (2 : ℝ) ^ p / (2 : ℝ) ^ Cost.ceilBeta lam := ⟢
    linarith
  have := mul_le_mul_of_nonneg_right hC (by linarith : (0 : ℝ) ≤
    (2 : ℝ) ^ p / (2 : ℝ) ^ Cost.ceilBeta lam + 1)
  nlinarith

/-- The per-level constant `4096 (C + 1) (4 K₁)`. -/
def lvlConst (C K₁ : ℕ) : ℕ := 4096 * (C + 1) * (4 * K₁)

/-- **The budget of one level against Lemma 4.2's overhead**: for `16 ≤ λ ≤ p`,
`f λ ≤ lvlConst C K₁ · 2^p · downOverhead λ` (`Cost.downStep_cost_le`). -/
theorem lvlBudget_le {cnt : ℕ → ℕ} {C K₁ p lam : ℕ} (hc : cnt lam ≤ C) (h16 : 16 ≤ lam)
    (hp : lam ≤ p) :
    (lvlBudget K₁ cnt p lam : ℝ) ≤ (lvlConst C K₁ : ℝ) * ((2 : ℝ) ^ p * Cost.downOverhead lam) := by
  have hR := kBound_add_one_le (p := p) hc
  have hl := lemma41Nat_add_one_le (g := nextLvl lam) (by unfold nextLvl; omega)
  have hK0 : (0 : ℝ) ≤ (C : ℝ) + 1 := ⟢
  have hk0 : (0 : ℝ) ≤ 4 * (K₁ : ℝ) := ⟢
  have hstep := Cost.downStep_cost_le hK0 hk0 (by omega : 14 ≤ lam) hp hR
  unfold lvlBudget lvlConst
  push_cast
  have hR0 : (0 : ℝ) ≤ (kBound cnt p lam : ℝ) + 1 := ⟢
  have hK1 : (0 : ℝ) ≤ (K₁ : ℝ) := ⟢
  have hn : nextLvl lam = Cost.ceilBeta lam + 11 := rfl
  rw [hn] at hl ⊢
  have hmain : (K₁ : ℝ) * (((kBound cnt p lam : ℝ) + 1) *
      ((lemma41Nat (Cost.ceilBeta lam + 11) : ℝ) + 1)) ≤
      ((kBound cnt p lam : ℝ) + 1) * (4 * (K₁ : ℝ) * Cost.lemma41Bound (Cost.ceilBeta lam + 11)) := by
    have := mul_le_mul_of_nonneg_left hl (mul_nonneg hK1 hR0)
    calc (K₁ : ℝ) * (((kBound cnt p lam : ℝ) + 1) * ((lemma41Nat (Cost.ceilBeta lam + 11) : ℝ) + 1))
        = ((K₁ : ℝ) * ((kBound cnt p lam : ℝ) + 1)) *
            ((lemma41Nat (Cost.ceilBeta lam + 11) : ℝ) + 1) := ⋆
      _ ≤ ((K₁ : ℝ) * ((kBound cnt p lam : ℝ) + 1)) *
            (4 * Cost.lemma41Bound (Cost.ceilBeta lam + 11)) := this
      _ = ((kBound cnt p lam : ℝ) + 1) *
            (4 * (K₁ : ℝ) * Cost.lemma41Bound (Cost.ceilBeta lam + 11)) := ⋆
  have e : (4096 : ℝ) * ((C : ℝ) + 1) * (4 * (K₁ : ℝ)) * ((2 : ℝ) ^ p * Cost.downOverhead lam) =
      4096 * ((C : ℝ) + 1) * (4 * (K₁ : ℝ)) * ((2 : ℝ) ^ p * Cost.downOverhead lam) := rfl
  linarith

/-- The constant of the whole level loop: `4500³ · 3000 · lvlConst C K₁`. -/
def potConst (C K₁ : ℕ) : ℕ := 4500 ^ 3 * 3000 * lvlConst C K₁

/-- **The cost of the level loop is linear**: `pot f λ ≤ potConst C K₁ · 2^p` for `λ ≤ p`, when
`cnt` is bounded by `C`. -/
theorem pot_lvlBudget_le {cnt : ℕ → ℕ} {C : ℕ} (hc : ∀ l, cnt l ≤ C) (K₁ p lam : ℕ)
    (hl : lam ≤ p) : pot (lvlBudget K₁ cnt p) lam ≤ potConst C K₁ * 2 ^ p := by
  have hB : ∀ j, (0 : ℝ) ≤ (lvlConst C K₁ : ℝ) * ((2 : ℝ) ^ p * Cost.downOverhead j) :=
    fun j => mul_nonneg (⟢) (mul_nonneg (by positivity) (Cost.downOverhead_nonneg j))
  have h1 := pot_le_sum (lvlBudget K₁ cnt p) _ hB p
    (fun j h16 hj => lvlBudget_le (hc j) h16 hj) lam hl
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h1
  have h2 := Cost.sum_downOverhead_le (lam + 1)
  have h3 : (pot (lvlBudget K₁ cnt p) lam : ℝ) ≤ (potConst C K₁ : ℝ) * (2 : ℝ) ^ p := by
    unfold potConst
    push_cast
    have h0 : (0 : ℝ) ≤ (lvlConst C K₁ : ℝ) * (2 : ℝ) ^ p := ⟢
    have := mul_le_mul_of_nonneg_left h2 h0
    nlinarith
  exact_mod_cast h3

end

end DrvR

end Chazelle.Core
