/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.TimeClaims.Sec3.Arithmetic
public import ThreeSumApsp.Util.Asymptotics.LogU

/-!
# Running-time claims of Section 3.4: Theorems 21 and 22

All lemmas are about an arbitrary interpretation `M : DetTimeModel` of "is solved in time T".  They
are deductions between running-time sentences: those of the paper for Theorem 22, and for
Theorem 21, which the paper cites, those of the route taken here.

* Theorem 21(a) from two reductions, [CH20, Theorem 5.1] followed by [VW13, Theorem 4.3]:
  `Theorem21a.of_CH20_VW13`.  The sizes, numbers of instances and extra times compose
  by the rules for `n^{a+o(1)}`.
* Theorem 21(b) for the (min,+)-product from [VW13, Theorem 3.3] and [VW18, Theorem 4.2]:
  `Theorem21b.minPlus_of_VW13_VW18`.  The time of the first reduction is again a good
  time (`GoodTime.mul_logU`), and `log (cU) = O(log U)` (`dominated_logU_mul`).
* Theorem 21(b) for APSP by repeated squaring: `Theorem21b.apsp_of_minPlus`, whose
  arithmetic is `dominated_repeatedSquaring`.
* "Plug Theorem 19 into Theorem 21": `threeSum_of_uniform_theorem_21a`,
  `minPlus_of_uniform_theorem_21b`, `apsp_of_uniform_theorem_21b`.
* Theorem 22: the roundings such as `n^{2-1/1296+o(1)} ≤ O(n^{1.99923})`
  (`Claim.SolvedAlongPow.mono`).
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Theorem 21(a) -/

/-- Theorem 21(a) from two reductions: [CH20, Theorem 5.1] followed by [VW13, Theorem 4.3]. -/
theorem Theorem21a.of_CH20_VW13 M (hCH : Claim.CH20_Theorem_5_1 M)
    (hVW : Claim.VW13_Theorem_4_3 M) : Claim.Theorem_21a M := by
  obtain ⟨c, E₂, Num₂, size₂, hc, hE₂, hNum₂, hsize₂, hsize₂_pos, hVW⟩ := hVW
  intro κ hκ
  obtain ⟨E₁, Num₁, mag₁, N, c', κ', hE₁, hNum₁, hN, hpos, hCH⟩ := hCH κ hκ
  have hN' := hN.isPowLittleO
  have hwords :=
    ((isPowPolylog_const 1).add (isPowPolylog_logU_of_le fun n hn => (hpos n hn).2)).isPowLittleO
  refine ⟨fun n => E₁ n + Num₁ n * (E₂ (N n) * (1 + logU (mag₁ n))), fun n => Num₁ n * Num₂ (N n),
    fun n => c * mag₁ n, fun n => size₂ (N n), c * c', κ', ?_, ?_, ?_, fun n hn => ?_,
    fun T hT => ?_⟩
  · -- the extra time: `Õ(n^{3/2}) + Õ(1) · N^{3/2+o(1)} · Õ(1)`
    exact hE₁.isPowLittleO.add ((hNum₁.isPowLittleO.mul
      ((hE₂.comp hN' (by norm_num) (by norm_num)).mul hwords)).mono (by norm_num))
  · -- the number of instances: `Õ(1) · O(N^{1/2})`
    exact (hNum₁.isPowLittleO.mul
      (hNum₂.isPowLittleO.comp hN' (by norm_num) (by norm_num))).mono (by norm_num)
  · -- their size: `O(N^{1/2})`
    exact (hsize₂.isPowLittleO.comp hN' (by norm_num) (by norm_num)).mono (by norm_num)
  · obtain ⟨hN1, hmag1, hmag⟩ := hpos n hn
    refine ⟨hsize₂_pos _ hN1, one_le_mul_of_one_le_of_one_le hc hmag1, ?_⟩
    nlinarith
  · grind

/-! ## Theorem 21(b): the (min,+)-product -/

/-! ## Theorem 21(b): APSP -/

/-! ## "Plug Theorem 19 into Theorem 21"

The time of Theorem 19 is `uniformTime K δ e s u = K s^{3-δ} (log s + 1)^e (1 + log u)²`.
Theorem 21 evaluates it at sizes `s(n)` and bounds `u(n) ≤ c n^κ` on the numbers, and multiplies it
by powers of `n` and logarithms.  So each bound is a product of functions of known classes. -/

/-- "Plug Theorem 19 into Theorem 21", 3SUM, in general form: with exponent `3 - δ` for Exact
Triangle the time for 3SUM is `n^{2-δ/2+o(1)}`. -/
theorem threeSum_of_uniform_theorem_21a M {δ} e (hδ1 : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform M δ e) (h21 : Claim.Theorem_21a M) :
    (Claim.SolvedAlongPow M.threeSum UpperPowLittleO (2 - δ / 2) : Prop) := by
  obtain ⟨K, -, hex⟩ := hu
  intro κ hκ
  obtain ⟨E, Num, mag, size, c', κ', hE, hNum, hsize, hpos, h⟩ := h21 κ hκ
  obtain ⟨T', hT', hb⟩ := h _ hex


  have htotal : IsPowLittleO (fun n => E n + Num n * uniformTime K δ e (size n) (mag n))
      (2 - δ / 2) :=
    (hE.mono (by linarith)).add
      ((hNum.mul ((((isPowPolylog_rpow_mul_log_add_one_pow (3 - δ) e).isPowLittleO.comp hsize
        (by linarith) (by norm_num)
      ).mul (((isPowPolylog_const 1).add
        (isPowPolylog_logU_of_le fun n hn => (hpos n hn).2)).pow 2).isPowLittleO).const_mul K)).mono (le_of_eq (by push_cast; ring)))
  exact ⟨T', hT', htotal.upperPowLittleO.mono_left (Filter.eventually_atTop.2 ⟨1, hb⟩)⟩

/-! ## Theorem 22 -/

/-- The roundings of Theorem 22, such as "n^{2-1/1296+o(1)} ≤ O(n^{1.99923})", at the level of
claims: an inclusion between two classes of running times carries over to the claims. -/
theorem Claim.SolvedAlongPow.mono {S} {Cls Cls'}
    {a b} (h : Claim.SolvedAlongPow S Cls a) (hCls : ∀ f, Cls f a → Cls' f b) :
    Claim.SolvedAlongPow S Cls' b := fun κ hκ =>
  let ⟨T, hT, hb⟩ := h κ hκ
  ⟨T, hT, hCls _ hb⟩

end ThreeSumApsp
