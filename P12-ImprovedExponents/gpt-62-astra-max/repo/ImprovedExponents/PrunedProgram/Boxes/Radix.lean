/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-! Horner's rule serves both the leaf (decimal) and the box (base 11) array. -/
@[expose] public section
namespace Light.Sec4.BoxTable
open ThreeSumApsp ThreeSumApsp.Spec

namespace Digits
slots 0 Str Len Level Acc
end Digits
open Digits

def radixBody (b : ℕ) : Stmt :=
  .set Level (k 0) ;; .set Acc (k 0) ;; .while (v Level <' v Len) (
    .set Acc (v Acc *' k b +' M (v Str +' v Level)) ;; .set Level (v Level +' k 1)) ;;
  .set Str (v Acc)

def RadixSpec (lim : Limits) (P : Program) (p b : ℕ) : Prop :=
  ∀ (a L : ℕ) (l : List ℕ) (μ : ℕ → ℤ), SegN μ a l → l.length = L → (∀ x ∈ l, x < b) →
    a+L < lim.space → (b:ℤ)^L ≤ lim.word → ∀ d, d ≤ lim.depth →
      Meets lim P p d [a,L] μ (tHorner L) fun r ν => r = (ofDigitList b l : ℕ) ∧ ν = μ

theorem radix_spec {lim : Limits} {P : Program} {p b : ℕ} (hb : 1 ≤ b) (hb' : b ≤ 100)
    (hP : P[p]? = some (radixBody b)) (hs : Std lim) : RadixSpec lim P p b := by
  rintro a _ l μ hseg rfl hd ha hpow
  refine fun d _ => ⟨radixBody b, hP, ?_⟩
  light_facts hs
  -- every number formed on the way is below b^L, so it fits in a word
  have hfits : ∀ i ≤ l.length, ((ofDigitList b (l.take i) : ℕ) : ℤ) < lim.word := fun i hi => by
    have hlt := ofDigitList_lt (b := b) (l.take i) fun x hx => hd x (List.mem_of_mem_take hx)
    have hpow' : b ^ (l.take i).length ≤ b ^ l.length :=
      Nat.pow_le_pow_right hb (List.length_take_le' _ _)
    exact by linarith
  let I (i : ℕ) (σ : State) := σ = ⟨frame [a,l.length,i,(ofDigitList b (l.take i) : ℕ)], μ⟩
  unfold tHorner
  -- level := 0; acc := 0
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  -- while level < len
  refine Ends.next _ (Ends.whileBlock I l.length ?start ?round ?done (hT := le_rfl))
  case start => rfl
  case round =>
    rintro i _ hi rfl
    have hcell : μ (a + i) = (l.getD i 0 : ℕ) := hseg.read hi
    have hnext : ((ofDigitList b (l.take (i + 1)) : ℕ) : ℤ)
        = (ofDigitList b (l.take i) : ℕ) * b + (l.getD i 0 : ℕ) := by
      exact_mod_cast ofDigitList_take_succ b l hi
    have hfit := hfits (i + 1) hi
    have hbz : 0 ≤ (ofDigitList b (l.take i) : ℤ) * b := by positivity
    generalize l.getD i 0 = digit at hcell hnext
    -- acc := acc * b + mem[str + level]; level := level + 1
    refine ⟨by light_side, by light_side, by light_side [hcell], ?_⟩
    simp [I, update_frame_setLocal, hcell, hnext]
  case done =>
    rintro _ rfl
    refine ⟨by light_side, by light_side, ?_⟩
    -- return acc
    light_set (ofDigitList b l : ℕ) using List.take_length
    exact ⟨rfl, rfl⟩

end Light.Sec4.BoxTable
