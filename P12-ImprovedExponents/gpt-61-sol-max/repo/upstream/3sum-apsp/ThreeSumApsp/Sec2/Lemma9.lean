/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Sec2.Lemma7_8
public import ThreeSumApsp.Sec2.Levels

/-!
# Lemma 9: one run of `Full` computes all the products `X_Q Y_Q`

Section 2.3.3. The inner set of a string is the set of the levels at which it has
an inner variable (`p`, `q` or `z₀`). For a set `Q` of `m` levels, the left strings with inner set
`Q` index the entries of an `N₀ × D` matrix `X_Q`, the right strings those of a `D × N₀` matrix
`Y_Q`, and the output strings those of the product `X_Q Y_Q`. The arrays `a` and `b` hold all the
`X_Q` and all the `Y_Q` side by side. Lemma 9 says that `Mult(a, b)[w] = (X_Q Y_Q)[w]` for every
output string `w` with such an inner set.

* The strings with inner set `Q` are `leftStrOf Q hQ r π`, `rightStrOf Q hQ π c` and
  `outStrOf Q hQ r c` (`existsUnique_leftStr`, `existsUnique_rightStr`, `existsUnique_outStr`). At
  the first two the arrays hold `X_Q[r, π]` and `Y_Q[π, c]` (`arrayL_leftStrOf`,
  `arrayR_rightStrOf`).
* The two facts about `γ` that the proof needs are finite checks on the definition of `gamma`
  (`gamma_z0`, `gamma_x_y_z`); no other lemma is used for them.
* The proof of Lemma 9. By Lemma 8 the entry at `w` is a sum over all pairs `(u, v)`. In a summand
  that is not zero, `u` has inner set `Q`, the row of `w` as its outer part and some inner part `π`,
  and `v` has inner set `Q`, the column of `w` as its outer part and the same inner part
  (`exists_of_summand_ne_zero`). Each of these summands has coefficient 1 (`prod_gamma_eq_one`).
  Their sum is the entry of the matrix product (`Mult_arrays_eq_mul`, `lemma_9`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### The sizes of the matrices, and Figure 4 -/

/-! ### The input arrays -/

/-- The entry of the left input array at the string with inner set `Q`, outer part `r` and inner
part `π` is `X_Q[r, π]`. -/
@[simp]
theorem arrayL_leftStrOf {L m} X Q
     hQ (r : OuterStr L m) π :
    arrayL m X (leftStrOf Q hQ r π) = X Q r π := by
  simp_all [arrayL]

/-- The entry of the right input array at the string with inner set `Q`, inner part `π` and outer
part `c` is `Y_Q[π, c]`. -/
@[simp]
theorem arrayR_rightStrOf {L m} Y Q
     hQ π (c : OuterStr L m) :
    arrayR m Y (rightStrOf Q hQ π c) = Y Q π c := by
  simp_all [arrayR]

/-! ### The proof of Lemma 9 -/

/-- In the proof of Lemma 9: "the only monomials of G + E that contain z₀ are the p_ij q_ij
z₀, with coefficient 1." Stated for `γ(s, t, z₀)`, which is the coefficient of `s t z₀` in `G + E`
by `gamma_eq_coeff`. -/
theorem gamma_z0 s t :
    gamma s t .z0 = if ∃ i j, s = .p i j ∧ t = .q i j then 1 else 0 := by
  decide +revert

/-- In the proof of Lemma 9: "The only monomial of G + E that contains z_ij and no inner
variable is x_i y_j z_ij, with coefficient 1". Stated for `γ(x_i', y_j', z_ij)`, which is the
coefficient of `x_i' y_j' z_ij` in `G + E` by `gamma_eq_coeff`. -/
theorem gamma_x_y_z i' j' i j :
    gamma (.x i') (.y j') (.z i j) = if i' = i ∧ j' = j then 1 else 0 := by
  decide +revert

/-- The statement on `γ(x_i', y_j', z_ij)` as it is used: if `s` and `t` are outer and
`γ(s, t, z_ij) ≠ 0`, then `(s, t) = (x_i, y_j)`. -/
private theorem eq_x_y_of_gamma_ne_zero {s} {t} {i j}
    (hs : ¬ s.IsInner) (ht : ¬ t.IsInner) (h : gamma s t (.z i j) ≠ 0) : s = .x i ∧ t = .y j := by
  rcases s with i' | _
  · rcases t with j' | _
    · grind [gamma_x_y_z]
    · exact (ht trivial).elim
  · exact (hs trivial).elim

/-- The summands of Lemma 8 that can be nonzero. Let `w` be the output string with inner
set `Q`, row `r` and column `c`. If `γ(u_ℓ, v_ℓ, w_ℓ) ≠ 0` at every level and the inner sets of `u`
and `v` have `m` elements, then `u` has inner set `Q`, outer part `r` and some inner part `π`, and
`v` has inner set `Q`, outer part `c` and the inner part with the same indices. -/
private theorem exists_of_summand_ne_zero {L m} Q (hQ : Q.card = m)
     r c {u} {v : RightStr L}
    (hγ : ∀ ℓ, gamma (u ℓ) (v ℓ) (outStrOf Q hQ r c ℓ) ≠ 0) (hu : (innerSetL u).card = m)
    (hv : (innerSetR v).card = m) : ∃ π, u = leftStrOf Q hQ r π ∧ v = rightStrOf Q hQ π c := by
  simp only [outStrOf, forall_level_iff Q hQ, glue_innerLevel, glue_outerLevel] at hγ
  obtain ⟨hγin, hγout⟩ := hγ
  -- "at a level ℓ ∈ Q we have w_ℓ = z₀ […] So (u_ℓ, v_ℓ) = (p_ij, q_ij) for some i, j."
  have hin : ∀ k, ∃ ij : Fin 2 × Fin 2,
      u (innerLevel Q hQ k) = .p ij.1 ij.2 ∧ v (innerLevel Q hQ k) = .q ij.1 ij.2 := fun k => by
    by_contra hne
    exact hγin k ((gamma_z0 _ _).trans (if_neg fun ⟨i, j, h⟩ => hne ⟨(i, j), h⟩))
  choose π hπ using hin
  -- "Thus u and v have an inner variable at every level of Q, and their inner sets are therefore
  -- exactly Q."  So "u_ℓ and v_ℓ are outer" at the levels outside Q.
  have huQ :=
    filter_eq_of_forall_innerLevel Q hQ fun k => by rw [(hπ k).1]; trivial hu
  have hvQ :=
    filter_eq_of_forall_innerLevel Q hQ fun k => by rw [(hπ k).2]; trivial hv

  have hvout := ((filter_eq_iff_forall_level Q hQ).mp hvQ).2
  -- "at a level ℓ ∉ Q we have w_ℓ = z_ij for some i, j […] so (u_ℓ, v_ℓ) = (x_i, y_j)."
  have hout :=
    fun k => eq_x_y_of_gamma_ne_zero (((filter_eq_iff_forall_level Q hQ).mp huQ).2 k) (hvout k) (hγout k)
  exact ⟨π, (eq_glue_iff Q hQ).mpr ⟨fun k => (hπ k).1, fun k => (hout k).1⟩,
    (eq_glue_iff Q hQ).mpr ⟨fun k => (hπ k).2, fun k => (hout k).2⟩⟩

/-- In the proof of Lemma 9: the coefficient of the summand of `π` "is 1". -/
private theorem prod_gamma_eq_one {L m} Q hQ
    (r c : OuterStr L m) π :
    ∏ ℓ, gamma (leftStrOf Q hQ r π ℓ) (rightStrOf Q hQ π c ℓ) (outStrOf Q hQ r c ℓ) = 1 := by
  have hone : ∀ ℓ,
      gamma (leftStrOf Q hQ r π ℓ) (rightStrOf Q hQ π c ℓ) (outStrOf Q hQ r c ℓ) = 1 := by
    simp only [forall_level_iff Q hQ, leftStrOf, rightStrOf, outStrOf, glue_innerLevel,
      glue_outerLevel]
    exact ⟨fun _ => (gamma_z0 _ _).trans (if_pos ⟨_, _, rfl, rfl⟩),
      fun _ => (gamma_x_y_z _ _ _ _).trans (if_pos ⟨rfl, rfl⟩)⟩
  exact prod_eq_one fun ℓ _ => hone ℓ

/-- Lemma 9 for the output string with inner set `Q`, row `r` and column `c`: by Lemma 8 the entry
is a sum over all pairs `(u, v)`, and the summands that remain are those of the matrix product. -/
theorem Mult_arrays_eq_mul {L m} X
     Y Q hQ
    (r c : OuterStr L m) :
    Mult (arrayL m X) (arrayR m Y) (outStrOf Q hQ r c) = (X Q * Y Q) r c := by
  -- To show: `∑_{(u,v)} ∏_ℓ γ(u_ℓ, v_ℓ, w_ℓ) a[u] b[v] = ∑_π X_Q[r, π] Y_Q[π, c]`. The right-hand
  -- side is the part of the left-hand side over the pairs `(u, v)` that belong to some `π`.
  rw [lemma_8, Matrix.mul_apply, ← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_of_injective (fun π => (leftStrOf Q hQ r π, rightStrOf Q hQ π c)) ?_ _ _ ?_ ?_
  · -- "There is one such summand for each of the D strings π".
    exact fun π π' h => (leftStrOf_inj.mp (congrArg Prod.fst h)).2
  · -- Every other summand is zero.  "a[u] b[v] ≠ 0 requires the inner sets of u and v to have
    -- exactly m elements."
    rintro ⟨u, v⟩ hnot
    by_contra hne
    obtain ⟨⟨hγ, ha⟩, hb⟩ : (∏ ℓ, gamma (u ℓ) (v ℓ) (outStrOf Q hQ r c ℓ) ≠ 0
        ∧ arrayL m X u ≠ 0) ∧ arrayR m Y v ≠ 0 := by
      simp_all
    obtain ⟨π, rfl, rfl⟩ := exists_of_summand_ne_zero Q hQ r c
      (fun ℓ => prod_ne_zero_iff.mp hγ ℓ (mem_univ ℓ))
      (by_contra fun h => ha (dif_neg h)) (by_contra fun h => hb (dif_neg h))
    exact hnot ⟨π, rfl⟩
  · -- The summand of `π` is `1 · X_Q[r, π] · Y_Q[π, c]`.
    ram_arith [prod_gamma_eq_one]

/-- Section 2.3.3: "one run of Full […] computes all K of the products X_Q Y_Q." -/
theorem Full_arrays_eq_mul {L m} X
     Y Q hQ
     r c :
    Full L (arrayL m X) (arrayR m Y) (outStrOf Q hQ r c) = (X Q * Y Q) r c := by
  rw [Lemma7.returns_Mult]
  exact Mult_arrays_eq_mul X Y Q hQ r c

end ThreeSumApsp
