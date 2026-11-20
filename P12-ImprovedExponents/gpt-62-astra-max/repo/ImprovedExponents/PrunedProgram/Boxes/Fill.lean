/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module
public import ImprovedExponents.PrunedProgram.Boxes.Sum
public import ImprovedExponents.PrunedProgram.Boxes.Page

@[expose] public section
namespace Light.Sec4.BoxTable
open ThreeSumApsp ThreeSumApsp.Spec

structure Passes (lim : Limits) (P : Program) : Prop where
  first : NineFirstSpec lim P
  next : NineNextSpec lim P
  star : StarFirstSpec lim P
  decimal : HornerSpec lim P
  boxCode : RadixSpec lim P Proc.lookup 11
  sum : SumSpec lim P

namespace Fill
slots 0 E A B Base Cur Box L Mt More Star Value Code Ret

def value : Stmt := .ite (v E =' k 0)
  (.call Proc.horner [v Box,v L] Code ;;
   .set Value (M (v A +' v Code) *' M (v B +' v Code)))
  (.call Proc.sumTen [v Base,v Box,v L,v Star] Value)

def round : Stmt := .call Proc.starFirst [v Cur,v Box,v L,v E] Star ;; value ;;
  .call Proc.lookup [v Box,v L] Code ;; .store (v Base +' v Code) (v Value) ;;
  .call Proc.nineNext [v Cur,v L,v E,v Mt] More

def body : Stmt := .call Proc.nineFirst [v Cur,v L,v E] Ret ;;
  .set More (k 1) ;; .while (v More =' k 1) round

abbrev args (x : Tile) (e : ℕ) : List ℤ := [e,x.a,x.b,x.page,x.cur,x.box,x.L,(x.m-x.t:ℕ)]
abbrev loc (x : Tile) (e : ℕ) (more star v c r : ℤ) := frame (args x e ++ [more,star,v,c,r])
abbrev kept (x : Tile) (μ ν : ℕ → ℤ) := SameOutside3 μ ν x.cur x.L x.box x.L x.page (stride x.L)

structure Mem (x : Tile) (μ : ℕ → ℤ) (e i : ℕ) (ν : ℕ → ℤ) : Prop where
  leaf : ∀ h : i < (x.leaves e).length, SegN ν x.cur (x.leaves e)[i]
  tile : x.Done ν e i
  a : SegOn x.m ν x.a x.A
  b : SegOn x.m ν x.b x.B
  same : kept x μ ν

def Inv (x : Tile) (μ : ℕ → ℤ) (e i : ℕ) (σ : State) := ∃ s v c r ν,
  σ = ⟨loc x e (if i < (x.leaves e).length then 1 else 0) s v c r,ν⟩ ∧ Mem x μ e i ν

variable {lim : Limits} {P : Program} {d : ℕ} (K : Passes lim P) {x : Tile} (H : x.Safe lim)

include H

private theorem power_fits : (11:ℤ)^x.L ≤ lim.word := by
  have hle := (pow_le_stride x.L).trans (by omega) |>.trans H.layout.2.2.2.2.le
  exact (show (11:ℤ)^x.L ≤ (lim.space:ℤ) by exact_mod_cast hle).trans H.std.space_le

include K

private theorem value_spec {ν e i more val code ret l} (hd : d+2 ≤ lim.depth) (he : e ≤ x.m-x.t)
    (hl : l ∈ x.leaves e) (hbox : SegN ν x.box (starFirst e l)) (tile : x.Done ν e i)
    (a : SegOn x.m ν x.a x.A) (b : SegOn x.m ν x.b x.B) :
    let s : ℤ := ((lastStar (starFirst e l)).getD 0 : ℕ)
    Ends lim P d value ⟨loc x e more s val code ret,ν⟩ (tHorner x.L + tSumTen x.L + 24)
      fun σ => ∃ c, σ = ⟨loc x e more s (x.val (starFirst e l)) c ret,ν⟩ := by
  dsimp only
  have hp := H.layout; have hw := H.std.space_le; have h100 := H.std.const_le
  obtain ⟨A',B',hA,hB,hword⟩ := H.bounds
  have hboxMem : starFirst e l ∈ x.keys e := List.mem_map.mpr ⟨l,hl,rfl⟩
  have digits := (mem_nineStrs _).mp hl
  have pow := power_fits H
  have h10 : (10:ℤ)^x.L ≤ lim.word := by grind
  unfold value
  refine Ends.iteLast (fun yes => ?_) (fun no => ?_) (hT := by simp <;> omega)
  · have e0 : e = 0 := by simpa using yes
    subst e; simp only [starFirst_zero] at hbox hboxMem ⊢
    obtain ⟨τ,rfl⟩ := exists_digitsT l digits.1 digits.2.1
    have ok : (P0Levels τ).card ≤ x.m := (card_P0Levels _ ▸ digits.2.2.2).trans (Nat.sub_le ..)
    have ac := a.get ok; have bc := b.get ok; have c_lt := codeT_lt τ
    have Hprod := mul_le_mul (hA τ) (hB τ) (abs_nonneg _) ((abs_nonneg _).trans (hA τ))
    have bound := (le_mul_of_one_le_left (mul_nonneg ((abs_nonneg _).trans (hA τ))
      ((abs_nonneg _).trans (hB τ))) (one_le_pow₀ (by norm_num : (1:ℤ) ≤ 10))).trans hword
    rw [← abs_mul] at Hprod; have hb := Hprod.trans bound
    have eqv : x.val (digitsT τ) = x.A τ * x.B τ := by
      rw [Tile.val,storedD,starCount_of_mem_starBoxes hboxMem,dpValueD,
        starsToNines_of_notMem (fun hh => absurd (digits.2.1 _ hh) (lt_irrefl _)),leafProduct_digitsT]
    light_call (K.decimal x.box x.L _ _ hbox digits.1 digits.2.1 (by omega) h10 _ (by omega)) with _ _ ⟨rfl,rfl⟩
    rw [ofDigitList_digitsT]; generalize codeT τ = c at *
    light_set (x.A τ * x.B τ) using ac,bc,abs_le.mp hb
    exact ⟨(c:ℤ),by rw [eqv]; rfl⟩
  · have ep : e ≠ 0 := by simpa using no
    obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ep
    let key := starFirst (e+1) l
    obtain ⟨pos,last,child⟩ := exists_lastStar_of_mem_starBoxes hboxMem
    have pk : pos < key.length := by
      have H := ((lastStar_eq_some_iff _ _).mp last).1
      by_contra! hc; rw [List.getD_eq_default _ _ hc] at H; omega
    have len := (starBoxes_digits hboxMem).1
    have sums (j : ℕ) : |((tenValues (dpValueD (arrT x.A) (arrT x.B) e) key pos).take j).sum| ≤ lim.word := by
      obtain ⟨π,hπ⟩ := exists_of_mem_starBoxes key hboxMem
      rw [← hπ]
      have hab := mul_nonneg ((abs_nonneg _).trans (hA (fun _ => .P0))) ((abs_nonneg _).trans (hB (fun _ => .P0)))
      exact (abs_dp_partial_sum_le hA hB e π ⟨pos,pk.trans_le len.le⟩ j).trans
        ((mul_le_mul_of_nonneg_right (by apply pow_le_pow_right₀ <;> omega) hab).trans hword)
    refine Ends.callTo (K.sum x.page x.box pos key _ ν pk hbox (starBoxes_digits hboxMem).2
      (by dsimp only [key]; rw [len]; omega) (by dsimp only [key]; rw [len]; have := pow_le_stride x.L; omega)
      (fun j hj => tile.read (child j hj)) (fun j _ => sums j) _ (by omega)) ?_
      (ha := by light_side [key,len,last]) (hT := by dsimp only [key]; rw [len]; simp; omega)
    rintro _ _ ⟨rfl,rfl⟩
    exact ⟨_,by simp only [Tile.val,storedD,starCount_of_mem_starBoxes hboxMem,dpValueD,sumAtLastStar,last]; rfl⟩

private theorem round_spec {ν μ e i more star val code ret} (hd : d+2 ≤ lim.depth)
    (he : e ≤ x.m-x.t) (hi : i < (x.leaves e).length) (hm : Mem x μ e i ν) :
    Ends lim P d round ⟨loc x e more star val code ret,ν⟩ (tFillRound x.L) (Inv x μ e (i+1)) := by
  obtain ⟨leaf,done,sa,sb,keep₀⟩ := hm
  let l := (x.leaves e)[i]
  let key := starFirst e l
  have hl : l ∈ x.leaves e := List.getElem_mem hi
  have dk := starBoxes_digits (starFirst_mem_starBoxes hi)
  have bound : ofDigitList 11 key < stride x.L := Tile.address (x:=x) (starFirst_mem_starBoxes hi)
  have places := H.layout; light_facts H.std
  have pow := power_fits H
  have len : l.length = x.L := length_of_mem_nineStrs hl
  unfold round tFillRound
  light_call (K.star x.cur x.box x.L e l ν (leaf hi) len (by omega) (by omega) (by omega) _ (by omega))
    with _ ν₁ ⟨sk,rfl,o₁⟩
  have done₁ : x.Done ν₁ e i := Tile.Holds.keep done
  refine Ends.pieceThen (value_spec K H hd he hl sk done₁ sa.keep sb.keep) ?_ (by simp; omega)
  rintro _ ⟨c,rfl⟩
  light_call (K.boxCode x.box x.L key ν₁ sk dk.1 dk.2 (by omega) pow _ (by omega)) using tHorner,tInsert
    with _ ν₁ ⟨rfl,rfl⟩
  light_store (x.page+ofDigitList 11 key) (x.val (starFirst e l)) using tHorner,tInsert
  let ν₂ := Function.update ν₁ (x.page+ofDigitList 11 key) (x.val key)
  have done₂ : x.Done ν₂ e (i+1) := done₁.write hi
  have out : SameOutside ν₁ ν₂ x.page (stride x.L) := SameOutside.refl.update (by constructor <;> omega) _
  have lseg : SegN ν x.cur l := leaf hi
  have sl : SegN ν₂ x.cur l := lseg.keep (by light_keep [len])
  light_call (K.next x.cur x.L e (x.m-x.t) l ν₂ sl hl (by omega) _ (by omega)) using tHorner,tInsert
    with r ν₃ ⟨next,hr,o₃⟩
  have hn := nineNext_getElem x.L e (x.m-x.t) i hi
  change nineNext e (x.m-x.t) l = (x.leaves e)[i+1]? at hn
  rw [hn] at next hr
  refine ⟨((lastStar key).getD 0 : ℕ), x.val key, (ofDigitList 11 key:ℕ), ret, ν₃, ?_, ⟨fun h => ?_,Tile.Holds.keep done₂,sa.keep,sb.keep,by light_keep⟩⟩
  · rw [hr]; simp; rfl
  · rwa [List.getElem?_eq_getElem h] at next

/-- Fill one level; below `e` the table is already initialized. -/
theorem spec {μ e} (hd : d+2 ≤ lim.depth) (he : e ≤ x.m-x.t) (ready : x.Done μ e 0)
    (sa : SegOn x.m μ x.a x.A) (sb : SegOn x.m μ x.b x.B) :
    Ends lim P d body ⟨frame (args x e),μ⟩ (tFillList x.L (x.keys e).length) fun σ' =>
      x.Done σ'.mem (e+1) 0 ∧ kept x μ σ'.mem := by
  have places := H.layout; have sizes := H.sizes; light_facts H.std
  have pos : 0 < (x.leaves e).length := length_nineStrs_pos (by omega) he
  have first : (x.leaves e)[0] = nineFirst x.L e := getElem_nineStrs pos
  unfold body tFillList
  rw [Tile.keys,length_starBoxes_eq_length_nineStrs]
  light_call (K.first x.cur x.L e μ (by omega) (by omega) _ (by omega)) with r ν ⟨seg,keep⟩
  light_set (1:ℤ)
  refine Ends.whileConst (Inv x μ e) (x.leaves e).length (tFillRound x.L) ?start ?round ?done ?time
  case start => exact ⟨0,0,0,r,ν,by simp [pos]; rfl,fun _ => first ▸ seg,Tile.Holds.keep ready,
    sa.keep,sb.keep,by light_keep⟩
  case round =>
    rintro i _ hi ⟨s,v,c,r,ν,rfl,hm⟩
    exact ⟨by light_side [hi],by simp [hi],round_spec K H hd he hi hm⟩
  case done => rintro _ ⟨_,_,_,_,ν,rfl,hm⟩; exact ⟨by light_side,by simp,hm.tile.next,hm.same⟩
  case time => simp [tFillStep,Tile.leaves]; ring_nf; omega

end Fill
end Light.Sec4.BoxTable
