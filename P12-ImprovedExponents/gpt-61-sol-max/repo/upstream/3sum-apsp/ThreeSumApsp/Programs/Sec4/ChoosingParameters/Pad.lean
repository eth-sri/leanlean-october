/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Contracts

/-!
# Padding X with zero columns

Proof of Corollary 26: "pad the inner dimension to 4^m < 4D with zero columns of X". Row by row: a
copy of the row and a fill with zeros. The invariant `PadX.Rows` says that the first i rows of the
padded matrix have been written; `PadX.Rows.succ` is what a round does to the memory, and
`padX_meets` the specification.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp


/-- padX(N, D, D', aX, aX'): for each row i, copy its D entries from aX + i D to aX' + i D', and
fill the D' - D cells behind them with zeros. -/
def padXBody : Stmt :=
  .for 5 (v 0) (
    .call 58 [v 3 +' v 5 *' v 1, v 4 +' v 5 *' v 2, v 1] 6 ;;
    .call 59 [v 4 +' v 5 *' v 2 +' v 1, v 2 -' v 1, k 0] 6)

namespace PadX

variable {N D₀ D' aX aX' i : ℕ} {X : ThreeSumApsp.IntMatrix N D₀} {μ μ' μ₁ μ₂ : Light.Memory}

/-- The memory before row i: the first i rows of the padded matrix stand at aX', and no cell outside
them has changed. -/
def Rows (μ : Light.Memory) (aX' D' : ℕ) (X : ThreeSumApsp.IntMatrix N D₀) (i : ℕ) (μ' : Light.Memory) : Prop :=
  (∀ (r : Fin N) (j : Fin D'), r < i → μ' (aX' + r * D' + j) = padInnerCols D' X r j) ∧
    SameOutside μ μ' aX' (i * D')

/-- A round: row i of X has been copied, and zeros have been written behind it. -/
theorem Rows.succ (h : Rows μ aX' D' X i μ') (hX : MatAt μ aX X) (hsep : aX + N * D₀ ≤ aX')
    (hi : i < N) (hcopy : ∀ j < D₀, μ₁ (aX' + i * D' + j) = μ' (aX + i * D₀ + j))
    (hout₁ : SameOutside μ' μ₁ (aX' + i * D') D₀)
    (hfill : ∀ j < D' - D₀, μ₂ (aX' + i * D' + D₀ + j) = 0)
    (hout₂ : SameOutside μ₁ μ₂ (aX' + i * D' + D₀) (D' - D₀)) (hDD : D₀ ≤ D') :
    Rows μ aX' D' X (i + 1) μ₂ := by
  have  : i * D₀ + D₀ ≤ N * D₀ := Nat.mul_add_le_mul hi le_rfl
  refine ⟨fun r j hr => ?_, fun b hb => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
    · -- an earlier row lies below the cells that the round has written
      have := Nat.mul_add_lt_mul hlt j.isLt
      rw [hout₂ _ (.inl (by omega)), hout₁ _ (.inl (by omega))]
      exact h.1 r j hlt
    · by_cases hj : (j : ℕ) < D₀
      · -- an entry of X, which is as at the start
        rw [heq, hout₂ _ (.inl (by omega)), hcopy _ hj, h.2 _ (.inl (by omega)), padInnerCols,
          dif_pos hj, ← heq]
        exact hX r ⟨j, hj⟩
      · -- a zero

        rw [(by
          rw [heq]; omega
         : aX' + (r : ℕ) * D' + (j : ℕ) = aX' + i * D' + D₀ + ((j : ℕ) - D₀)), hfill _ (by omega), padInnerCols, dif_neg hj]
  · rw [Nat.succ_mul] at hb
    rw [hout₂ b (by omega), hout₁ b (by omega), h.2 b (by omega)]

end PadX

open PadX in
theorem padX_meets {lim } {P } (hP : P[62]? = some padXBody)
    (hcopy : CopySpec lim P) (hfill : FillSpec lim P) (hstd : Std lim) : PadXSpec lim P := by
  intro N D₀ D' aX aX' X μ hDD hD1 hX hsep hsp
  refine fun d hd => ⟨padXBody, hP, ?_⟩
  have  := hstd.space_le

  have  : N ≤ N * D' := Nat.le_mul_of_pos_right _ hD1

  unfold padXBody tPadX
  -- for i < N
  refine Ends.for (fun i σ => ∃ (r : ℤ) (μ' : Light.Memory),
      σ = ⟨frame [N, D₀, D', aX, aX', i, r], μ'⟩ ∧ Rows μ aX' D' X i μ') N (16 * D' + 60)
    ?start ?round ?done ?bound
  case start =>
    exact ⟨0, μ, by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl,
      fun r j hr => absurd hr (Nat.not_lt_zero _), fun _ _ => rfl⟩
  case bound =>
    simp_all
  case done =>
    ram_aesop [Light.Sec4.PadX.Rows]
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, hrows⟩
    -- row i of X and row i of the padded matrix lie within their arrays
    have  : i * D₀ + D₀ ≤ N * D₀ := Nat.mul_add_le_mul hi le_rfl
    have  : i * D' + D' ≤ N * D' := Nat.mul_add_le_mul hi le_rfl
    -- copy(aX + i D, aX' + i D', D)
    refine Ends.callToThen (hcopy (aX + i * D₀) (aX' + i * D') D₀ μ' (by omega) (by omega)
      (by omega) (.inl (by omega)) _ hd) ?_ (hT := by simp [tCopy]; omega)
    rintro - μ₁ ⟨hc, hout₁⟩
    -- fill(aX' + i D' + D, D' - D, 0)
    refine Ends.callTo (hfill (aX' + i * D' + D₀) (D' - D₀) 0 μ₁ (by omega) (by omega) _
      hd) ?_ (by light_side [(Nat.cast_sub hDD).symm]) (hT := by simp [tCopy, tFill]; omega)
    rintro r' μ₂ ⟨hf, hout₂⟩
    exact ⟨rfl, r', μ₂, by rw [update_frame_setLocal]; rfl,
      hrows.succ hX hsep hi hc hout₁ hf hout₂ hDD⟩

end Light.Sec4
