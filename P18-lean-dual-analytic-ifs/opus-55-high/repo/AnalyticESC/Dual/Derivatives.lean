module

public import AnalyticESC.Dual.HigherDerivatives

public section

set_option hygiene false
local notation "𝖁" => hD0 _
local notation "𝖀" => Φ.dualProj w
local notation "𝕿" => Φ.dualProj (.fin (w.take n))
local notation "𝕾" => Φ.nonlin i
local notation "𝖋" => c.length - 1

local notation "𝖊" => n + m

local notation "𝖉" => 1 - Φ.cmax

local notation "𝖈" => c.partSize j - 1

/-!
# Derivatives of the dual natural projection

Lemma 2.9 (uniform bounds for `H_w^{(k)}` on `I`), Corollary 2.10 (Lipschitz bounds) and
Lemma 2.11 (dependence on the common prefix), using the Faà di Bruno formula of Lemma 2.8,
induction on the derivative order, polynomial bounds and geometric-series tails.
-/

namespace AnalyticESC



namespace IFS

variable (Φ : IFS N ε) (k : ℕ)

/-- The constants `D_{k+1}`: derivatives of `φ_i' = f_i''/f_i'` are bounded on `I`. -/
theorem exists_nonlin_iteratedDeriv_bound :
    ∃ D ≥ 0, ∀ i, Ɐ ‖iteratedDeriv k 𝕾 x‖ ≤ D := by
  have hb : ∀ i, ∃ D, Ɐ ‖iteratedDeriv k 𝕾 x‖ ≤ D := by
    intro i
    obtain ⟨U, hUo, hU, hd⟩ := Φ.exists_differentiableOn_nonlin i
    have hc : ContinuousOn (iteratedDeriv k 𝕾) U := fun z hz =>
      (differentiableAt_iteratedDeriv hUo hd k hz).continuousAt.continuousWithinAt
    exact isCompact_Icc.exists_bound_of_continuousOn
      (hc.comp Complex.continuous_ofReal.continuousOn fun x hx =>
        hU (Φ.ofReal_mem_cl hx))
  choose D hD using hb
  refine ⟨∑ i, |D i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i x hx => ?_⟩
  exact (hD i x hx).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (D j)) (Finset.mem_univ i)))

/-- The induction step in Lemma 2.9. Bounds for the lower derivatives bound each polynomial
in Lemma 2.8; the remaining factor is at most `c_max^n`, since every partition is nonempty. -/
theorem exists_dualDerivTerm_bound_of_lower (C : ℕ → ℝ) (hC0 : ∀ ℓ, 0 ≤ C ℓ)
    (hC : ∀ ℓ < k, Ɐ ∀ w, ‖iteratedDeriv ℓ 𝖀 x‖ ≤ C ℓ) :
    ∃ A ≥ 0, ∀ (w : Word N) n, Ɐ
      ‖Φ.dualDerivTerm w k n x‖ ≤ A * Φ.cmax ^ n := by
  classical
  choose E hE0 hE using fun m =>
    exists_norm_aeval_le_of_supported (gPoly_mem_supported m) C (fun ℓ _ => hC0 ℓ)
  choose D hD0 hD using Φ.exists_nonlin_iteratedDeriv_bound
  let B (c : OrderedFinpartition (k + 1)) := D 𝖋 * ∏ j, E 𝖈
  have hB : ∀ c, 0 ≤ B c := fun c => mul_nonneg 𝖁
    (Finset.prod_nonneg fun j _ => hE0 _)
  refine ⟨∑ c, B c, Finset.sum_nonneg fun c _ => hB c, fun w n x hx => ?_⟩
  cases hw : w.get? n with
  | none =>
    simp [dualDerivTerm, hw]
    exact mul_nonneg (Finset.sum_nonneg fun c _ => hB c) (pow_nonneg Φ.cmax_nonneg n)
  | some i =>
    have hlen : (w.take n).length = n := by
      cases w with
      | fin v =>
        simp [Nat.min_eq_left ((List.getElem?_eq_some_iff.1 hw).1).le]
      | inf v => simp
    have hcomp : Φ.comp 𝔱 x = ((Φ.comp 𝔱 x).re : ℂ) :=
      Φ.comp_ofReal _ hx
    simp [dualDerivTerm, hw]
    calc
      _ ≤ ∑ c : OrderedFinpartition (k + 1),
          ‖iteratedDeriv 𝖋 𝕾 (Φ.comp 𝔱 x) *
            𝔡ᶜ Φ 𝔱 x ^ c.length *
            ∏ j, MvPolynomial.aeval (fun ℓ => iteratedDeriv ℓ
              𝕿 x) (gPoly 𝖈)‖ := norm_sum_le _ _
      _ ≤ ∑ c, B c * Φ.cmax ^ n := by
        refine Finset.sum_le_sum fun c _ => ?_
        have hd := hD 𝖋 i _ (Φ.re_comp_mem_I 𝔱 hx)
        rw [← hcomp] at hd
        have hp : ∀ j,
            ‖MvPolynomial.aeval (fun ℓ => iteratedDeriv ℓ 𝕿 x)
              (gPoly 𝖈)‖ ≤ E 𝖈 := by
          intro j
          apply hE
          intro ℓ hℓ
          have hℓ' := Finset.mem_range.1 hℓ
          exact hC ℓ (by have := c.partSize_le j; omega) x hx _
        have hc : ‖𝔡ᶜ Φ 𝔱 x‖ ^ c.length ≤ Φ.cmax ^ n := by
          calc _ ≤ (Φ.cmax ^ n) ^ c.length := pow_le_pow_left₀ (norm_nonneg _) (by simpa [hlen] using Φ.norm_deriv_comp_le 𝔱 (subset_closure (ofReal_mem_nbhd Φ.ε_pos hx))) _
            _ = Φ.cmax ^ (n * c.length) := by ring
            _ ≤ Φ.cmax ^ n := pow_le_pow_of_le_one Φ.cmax_nonneg Φ.cmax_lt_one.le
              (by have := c.length_pos k.succ_pos; nlinarith)
        rw [norm_mul, norm_mul, norm_pow, norm_prod]
        calc _ ≤ D 𝖋 * Φ.cmax ^ n * ∏ j, E 𝖈 :=
              mul_le_mul (mul_le_mul hd hc (by positivity) 𝖁)
                (Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hp j))
                (Finset.prod_nonneg fun j _ => norm_nonneg _)
                (mul_nonneg 𝖁 (pow_nonneg Φ.cmax_nonneg n))
          _ = B c * Φ.cmax ^ n := by grind
      _ = (∑ c, B c) * Φ.cmax ^ n := (Finset.sum_mul ..).symm

/-- Lemma 2.9 by strong induction using Lemma 2.8. The bounds also control the geometric tails
needed for Lemma 2.11. -/
theorem exists_dualDerivTerm_bound :
    ∃ A ≥ 0, ∀ (w : Word N) n, Ɐ
      ‖Φ.dualDerivTerm w k n x‖ ≤ A * Φ.cmax ^ n := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hb : ∀ ℓ < k, ∃ C ≥ 0, Ɐ ∀ w,
        ‖iteratedDeriv ℓ 𝖀 x‖ ≤ C := by
      intro ℓ hℓ
      obtain ⟨A, hA0, hA⟩ := ih ℓ hℓ
      have hc1 := sub_pos.2 Φ.cmax_lt_one
      refine ⟨A * 𝖉⁻¹, by positivity, fun x hx w => ?_⟩
      exact (Φ.lemma_2_8 w ℓ hx).2 ▸ tsum_of_norm_bounded
        ((hasSum_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left A)
        (fun n => hA w n x hx)
    let C : ℕ → ℝ := fun ℓ => if hℓ : ℓ < k then (hb ℓ hℓ).choose else 0
    exact Φ.exists_dualDerivTerm_bound_of_lower k C (by grind) fun ℓ hℓ => by grind

/-- One family `C_k` serving Lemmas 2.9 and 2.11, the latter for every common prefix length
`m ≤ |i ∧ j|`. -/
theorem exists_iteratedDeriv_bounds :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      (∀ k, Ɐ ∀ w, ‖iteratedDeriv k 𝖀 x‖ ≤ C k) ∧
      ∀ k, Ɐ ∀ (i j : Word N) (m : ℕ), (m : ℕ∞) ≤ i.commonPrefixLength j →
        ‖iteratedDeriv k (Φ.dualProj i) x - iteratedDeriv k (Φ.dualProj j) x‖ ≤
          2 * C k * Φ.cmax ^ m := by
  classical
  choose A hA0 hA using Φ.exists_dualDerivTerm_bound
  let C k := A k * 𝖉⁻¹ + 1
  have hc1 := sub_pos.2 Φ.cmax_lt_one
  have htail : ∀ k w m x, x ∈ I →
      ‖∑' n, Φ.dualDerivTerm w k 𝖊 x‖ ≤ A k * 𝖉⁻¹ * Φ.cmax ^ m := by
    intro k w m x hx
    have hb : ∀ n, ‖Φ.dualDerivTerm w k 𝖊 x‖ ≤ A k * Φ.cmax ^ m * Φ.cmax ^ n := by
      intro n
      calc _ ≤ A k * Φ.cmax ^ 𝖊 := hA k w _ x hx
        _ = _ := by grind
    simpa only [mul_right_comm (A k)] using tsum_of_norm_bounded ((hasSum_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left (A k * Φ.cmax ^ m)) hb
  refine ⟨C, fun k => by have := hA0 k; dsimp [C]; positivity, ?_, ?_⟩
  · intro k x hx w
    rw [(Φ.lemma_2_8 w k hx).2]
    have ht := htail k w 0 x hx
    simp at ht
    linarith
  · intro k x hx i j m hm
    have hprefix : ∀ n < m, Φ.dualDerivTerm i k n x = Φ.dualDerivTerm j k n x := by
      obtain ⟨a, i', j', ha, rfl, rfl⟩ := Word.exists_eq_prepend hm
      intro n hn
      have hn' : n < a.length := by omega
      simp [dualDerivTerm, Word.get?_prepend_of_lt a _ hn',
        Word.take_prepend_of_le a _ hn'.le]
    have heq : (∑ n ∈ Finset.range m, Φ.dualDerivTerm i k n x) =
        ∑ n ∈ Finset.range m, Φ.dualDerivTerm j k n x :=
      Finset.sum_congr rfl fun n hn => hprefix n (Finset.mem_range.1 hn)
    rw [(Φ.lemma_2_8 i k hx).2, (Φ.lemma_2_8 j k hx).2,
      ← (Φ.lemma_2_8 i k hx).1.sum_add_tsum_nat_add m,
      ← (Φ.lemma_2_8 j k hx).1.sum_add_tsum_nat_add m, heq, add_sub_add_left_eq_sub]
    calc _ ≤ ‖∑' n, Φ.dualDerivTerm i k 𝖊 x‖ +
          ‖∑' n, Φ.dualDerivTerm j k 𝖊 x‖ := by bound
      _ ≤ A k * 𝖉⁻¹ * Φ.cmax ^ m +
          A k * 𝖉⁻¹ * Φ.cmax ^ m := by bound
      _ ≤ 2 * C k * Φ.cmax ^ m := by dsimp [C]; nlinarith [pow_nonneg Φ.cmax_nonneg m]

end IFS

end AnalyticESC
