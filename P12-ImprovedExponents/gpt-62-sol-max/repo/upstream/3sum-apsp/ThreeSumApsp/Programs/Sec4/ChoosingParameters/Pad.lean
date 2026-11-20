/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers
import ThreeSumApsp.Lang.Tactics

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

namespace PadX

/-- The local variables of padX: the arguments N, D, D', aX, aX', the row, and a result that is not
used. -/
registers [Height, Width, Padded, Source, Dest, Row, Unused]

end PadX

open PadX in
/-- padX(N, D, D', aX, aX'): for each row i, copy its D entries from aX + i D to aX' + i D', and
fill the D' - D cells behind them with zeros. -/
def padXBody : Stmt :=
  .for Row (v Height) (
    .call Proc.copy [v Source +' v Row *' v Width, v Dest +' v Row *' v Padded, v Width] Unused ;;
    .call Proc.fill [v Dest +' v Row *' v Padded +' v Width, v Padded -' v Width, k 0] Unused)

namespace PadX

variable {N D₀ D' aX aX' i : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ} {μ μ' μ₁ μ₂ : ℕ → ℤ}

/-- The memory before row i: the first i rows of the padded matrix stand at aX', and no cell outside
them has changed. -/
def Rows (μ : ℕ → ℤ) (aX' D' : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (i : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ (r : Fin N) (j : Fin D'), (r : ℕ) < i → μ' (aX' + r * D' + j) = padInnerCols D' X r j) ∧
    SameOutside μ μ' aX' (i * D')


end PadX

open PadX in
theorem padX_meets {lim : Limits} {P : Program} (hP : P[Proc.padX]? = some padXBody)
    (hcopy : CopySpec lim P) (hfill : FillSpec lim P) (hstd : Std lim) : PadXSpec lim P := by
  intro N D₀ D' aX aX' X μ hDD hD1 hX hsep hsp
  refine fun d hd => ⟨padXBody, hP, ?_⟩
  light_facts hstd
  have hN : N ≤ N * D' := Nat.le_mul_of_pos_right _ hD1
  have hsub : (D' : ℤ) - D₀ = ((D' - D₀ : ℕ) : ℤ) := (Nat.cast_sub hDD).symm
  unfold padXBody tPadX
  refine Ends.forShape (fun i r ν => ⟨frame [N, D₀, D', aX, aX', i, r], ν⟩)
    (fun i _ => Rows μ aX' D' X i) N (16 * D' + 60) 0
    ⟨by simp, .refl⟩ ?_ (fun _ _ h => ⟨fun i j => h.1 i j i.isLt, h.2⟩)
    (first := by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
  intro i _ ν hi h
  have hsrc : i * D₀ + D₀ ≤ N * D₀ := Nat.mul_add_le_mul hi le_rfl
  have hdst : i * D' + D' ≤ N * D' := Nat.mul_add_le_mul hi le_rfl
  light_call (hcopy (aX + i * D₀) (aX' + i * D') D₀ ν (by omega) (by omega)
    (by omega) (.inl (by omega))) using tCopy with - μ₁ ⟨hc, h₁⟩
  light_call (hfill (aX' + i * D' + D₀) (D' - D₀) 0 μ₁ (by omega) (by omega))
    using hsub, tCopy, tFill with r μ₂ ⟨hf, h₂⟩
  refine ⟨r, μ₂, rfl, fun r j hr => ?_, fun b hb => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
    · have := Nat.mul_add_lt_mul hlt j.isLt
      rw [h₂ _ (.inl (by omega)), h₁ _ (.inl (by omega))]
      exact h.1 r j hlt
    · by_cases hj : (j : ℕ) < D₀
      · rw [heq, h₂ _ (.inl (by omega)), hc _ hj, h.2 _ (.inl (by omega)), padInnerCols,
          dif_pos hj, ← heq]
        exact hX r ⟨j, hj⟩
      · rw [show aX' + (r : ℕ) * D' + (j : ℕ) = aX' + i * D' + D₀ + ((j : ℕ) - D₀) by grind,
          hf _ (by omega), padInnerCols, dif_neg hj]
  · rw [Nat.succ_mul] at hb
    rw [h₂ b (by omega), h₁ b (by omega), h.2 b (by omega)]

end Light.Sec4
