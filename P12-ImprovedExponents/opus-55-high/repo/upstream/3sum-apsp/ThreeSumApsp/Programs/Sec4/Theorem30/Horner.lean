/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Tactics
import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# Horner's rule: the code of a string of decimal digits

horner(a, L) returns the number whose L decimal digits, most significant first, are in the cells
from a.  It is used to index an encoding by a leaf (Section 4.3: "The encodings are indexed by the
leaves (Section 2.4.1) […].  Thus reading the product at a leaf […] takes O(L) operations").

After i rounds the routine holds the number formed by the first i digits (`Horner.Inv`).  One more
digit multiplies it by ten and adds the digit (`ofDigitList_take_succ`), and it stays below 10^L
(`ofDigitList_lt`), which fits in a word.  `horner_spec` is the specification.
-/


open ThreeSumApsp

namespace Light.Sec4


namespace Horner

/- The local variables of horner: the arguments (the address of the string and its length), the
level, and the number formed so far.  Local 0 also takes the result. -/
slots Str
slots Result Len Level Acc

/-- Before round i the number formed by the first i digits has been computed.  The memory is not
changed. -/
def Inv (a : ℕ) (l : List ℕ) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [a, l.length, i, (ofDigitList 10 (l.take i) : ℕ)], μ⟩

end Horner

open Horner in
/-- horner(str, len): multiply by ten and add the next digit, from the most significant digit on. -/
def hornerBody : Stmt :=
  .set Level (k 0) ;;
  .set Acc (k 0) ;;
  .while (v Level <' v Len) (
    .set Acc (v Acc *' k 10 +' M (v Str +' v Level)) ;;
    .set Level (v Level +' k 1)) ;;
  .set Result (v Acc)

open Horner in
/-- **horner** returns the number with the given decimal digits, and leaves the memory as it
was. -/
theorem horner_spec {lim : Limits} {P : Program} (hP : P[Proc.horner]? = some hornerBody)
    (hs : Std lim) : HornerSpec lim P := by
  rintro a _ l μ hseg rfl hd ha hpow
  refine fun d _ => ⟨hornerBody, hP, ?_⟩
  have hfits : ∀ i ≤ l.length, (ofDigitList 10 _ : ℕ) < lim.word := fun i hi => by
    have hlt := ofDigitList_lt (l.take i) fun x hx => hd x (List.mem_of_mem_take hx)
    have hpow' : 10 ^ (l.take i).length ≤ 10 ^ l.length :=
      Nat.pow_le_pow_right (by norm_num) (List.length_take_le' _ _)
    linarith
  unfold tHorner
  -- level := 0; acc := 0
  light_set 0
  light_set 0
  -- while level < len
  refine Ends.next _ (Ends.whileBlock (Inv a l μ) l.length ?_ ?_ ?_ (hT := le_rfl))
  · rfl
  ·
    rintro i _ hi rfl
    have hcell := hseg.read hi
    have hnext : (ofDigitList 10 (l.take (i + 1)) : ℕ)
        = ofDigitList 10 (l.take i) * 10 + l.getD i 0 := by
      grind [ofDigitList_take_succ]
    have hfit := hfits (i + 1) hi
    generalize l.getD i 0 = digit at hcell hnext
    -- acc := acc * 10 + mem[str + level]; level := level + 1
    refine ⟨by light_side, by light_side, by light_side [hcell], ?_⟩
    simp_all [Horner.Inv, update_frame_setLocal]
  ·
    rintro _ rfl
    refine ⟨by light_side, by light_side, ?_⟩
    -- return acc
    light_set (ofDigitList 10 l) using List.take_length
    simp
