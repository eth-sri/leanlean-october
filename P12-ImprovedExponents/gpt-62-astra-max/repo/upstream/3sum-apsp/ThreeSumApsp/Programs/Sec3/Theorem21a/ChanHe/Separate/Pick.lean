/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Separate.Classes

/-! Collect the values at a residue class of indices as a set. The bitmap
is addressed by value, but never initialized in proportion to the magnitude:
only flags of values actually present are cleared. -/
@[expose] public section
namespace Light.Sec3.ChanHe.Separate
open ThreeSumApsp ThreeSumApsp.ChanHe Finset

structure View where
  (n src q r dst bias : ℕ)
  x : ℕ → ℤ

namespace View
variable (g : View)
def key (i : ℕ) := ((g.bias:ℤ)+g.x i).toNat
abbrev items (j : ℕ) := slice g.x g.n g.q g.r j
abbrev args : List ℤ := [g.n,g.src,g.q,g.r,g.dst,g.bias]
structure Room (lim : Limits) : Prop where
  srcEnd : g.src+g.n ≤ g.dst
  dstEnd : g.dst+g.n ≤ lim.space
  index : g.r+g.n*g.q ≤ lim.space
  mark : ∀ i<g.n, g.dst+g.n ≤ g.key i ∧ g.key i < lim.space ∧ (g.key i:ℤ) = g.bias+g.x i
  word : (lim.space:ℤ) ≤ lim.word
  one : 1 ≤ lim.word
abbrev Input (μ : ℕ → ℤ) := ∀ i<g.n, μ (g.src+i)=g.x i

structure Acc (μ ν : ℕ → ℤ) (j len : ℕ) : Prop where
  kept : Kept μ ν g.dst
  values : SetAt ν g.dst len (g.items j)
  bit : ∀ i<g.n, ν (g.key i)=0 ↔ g.x i ∉ g.items j

variable {g} {lim : Limits} {μ ν : ℕ → ℤ} {j len : ℕ}
private theorem prefix_le : #(g.items j) ≤ j :=
  (card_image_le).trans ((card_filter_le ..).trans (card_range j).le)

theorem Acc.add (place : g.Room lim) (h : g.Acc μ ν j len) (hj : j<g.n)
    (i : ℕ) (hi : i<g.n) (eqi : g.r+j*g.q=i) (fresh : g.x i ∉ g.items j) :
    g.Acc μ (Function.update (Function.update ν (g.dst+len) (g.x i)) (g.key i) 1) (j+1) (len+1) := by
  have hk := place.mark i hi
  have hl := h.values.card.symm.trans_le prefix_le
  have step : g.items (j+1) = insert (g.x i) (g.items j) := by simp [items,slice_succ,eqi,hi]
  refine ⟨fun u hu => ?_,?_,fun t ht => ?_⟩
  · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),h.kept _ hu]
  · rw [step]; obtain ⟨l,rfl,sl,nd,he⟩ := h.values
    exact ⟨l++[g.x i],by simp,(sl.snoc _).update_out (Or.inr (by simp; omega)) _,
      by have hf : g.x i ∉ l := by simpa [← he] using fresh
         simp [List.nodup_append,nd]; grind,
      by ext; simp [← he,or_comm]⟩
  · have hkt := place.mark t ht
    rw [step]
    by_cases e : g.key t=g.key i
    · have : g.x t = g.x i := by omega
      simp [e,this]
    · have : g.x t ≠ g.x i := fun he => e (by simp [key,he])
      rw [Function.update_of_ne e,Function.update_of_ne (by omega),h.bit t ht]; simp [this]
end View

namespace SelectReg
slots 0 N Src Mod Res Dst Bias Idx Len
end SelectReg
open SelectReg

def reset : Stmt := .for Idx (v N) (.store (v Bias +' M (v Src +' v Idx)) (k 0))
abbrev pos := v Res +' v Idx *' v Mod
abbrev value := M (v Src +' pos)
abbrev mark := v Bias +' value

def writeNew : Stmt := .store (v Dst +' v Len) value ;; .store mark (k 1) ;; .set Len (v Len +' k 1)
def collect : Stmt := .for Idx (v N) (.ite (pos <' v N) (.ite (M mark =' k 0) writeNew .skip) .skip)
def pickBody : Stmt := reset ;; .set Len (k 0) ;; collect ;; .set N (v Len)

variable {lim : Limits} {P : Program} {g : View} {d : ℕ} {μ : ℕ → ℤ}

private theorem reset_spec (H : g.Room lim) (input : g.Input μ) :
    Ends lim P d reset ⟨frame g.args, μ⟩ (30*g.n+10) fun σ => ∃ ν,
      σ = ⟨frame (g.args++[(g.n:ℤ)]),ν⟩ ∧ Kept μ ν g.dst ∧ ∀ i<g.n, ν (g.key i)=0 := by
  obtain ⟨srcEnd,dstEnd,idxBound,marks,hw,_⟩ := H
  unfold reset
  refine Ends.forFrame (fun j ν => Kept μ ν g.dst ∧ ∀ i<j, ν (g.key i)=0) g.n ⟨SameOn.refl,by simp⟩ ?_
    (fun ν h => ⟨ν,rfl,h⟩) (hT := by simp [Stmt.blockCost]; omega)
  intro j ν hj ⟨hk,hm⟩
  obtain ⟨lo,hi,eq⟩ := marks j hj
  have cell := (hk (g.src+j) (by omega)).trans (input _ hj)
  unfold View.args
  light_store (g.key j) 0 using cell
  refine ⟨rfl,fun u hu => (Function.update_of_ne (by omega) ..).trans (hk u hu),fun i hi => ?_⟩
  by_cases e : g.key i=g.key j
  · simp [e]
  · have : i ≠ j := fun h => e (h ▸ rfl)
    exact (Function.update_of_ne e ..).trans (hm i (by omega))

private abbrev pickState (g : View) (j k : ℕ) (ν : ℕ → ℤ) : State :=
  ⟨frame (g.args++[(j:ℤ), k]),ν⟩

theorem pick_spec {p} (hp : P[p]?=some pickBody) (H : g.Room lim) (input : g.Input μ) :
    Meets lim P p d g.args μ (tPick g.n) fun z ν => z = (#(g.items g.n):ℕ) ∧
      SetAt ν g.dst #(g.items g.n) (g.items g.n) ∧ Kept μ ν g.dst := by
  refine Meets.of_body hp ?_
  have hw := H.word; have hone := H.one; have srcEnd := H.srcEnd; have dstEnd := H.dstEnd
  unfold pickBody tPick
  light_piece (reset_spec H input) with _ ⟨ν,rfl,kept,hzero⟩
  light_set 0
  have start : g.Acc μ ν 0 0 := by
    exact ⟨kept,⟨[],rfl,Seg.nil,List.nodup_nil,by simp [View.items,slice]⟩,
      fun i hi => by simp [View.items,slice,hzero i hi]⟩
  unfold collect
  refine Ends.next (g.n*100+6) (Ends.forCarry (pickState g) (fun j k τ => g.Acc μ τ j k) g.n 90 0 start ?_ ?_
    (hT:=by simp; omega)) (by light_time)
  · intro j k τ hj acc
    let i := g.r+j*g.q
    have room := H.index
    have hprod := Nat.mul_le_mul_right g.q hj.le
    have hbound : (i:ℤ) ≤ lim.space := by exact_mod_cast (show i≤lim.space by dsimp [i]; omega)
    have expr : (g.r:ℤ) + j*g.q = (i:ℤ) := by simp [i]
    have hp0 : (0:ℤ)≤j*g.q := by positivity
    have hk := acc.values.card.symm.trans_le View.prefix_le
    unfold pickState View.args
    light_if hi hn : i<g.n using pos,expr
    · have cell := (acc.kept (g.src+i) (by omega)).trans (input _ hi)
      obtain ⟨lo,up,eq⟩ := H.mark i hi
      have bit := acc.bit i hi
      have addr : ((g.bias:ℤ)+g.x i).toNat = g.key i := rfl
      light_if fresh old : g.x i ∉ g.items j using mark,value,pos,expr,cell,addr,bit
      · unfold writeNew
        light_store (g.dst+k) (g.x i) using value,pos,expr,cell
        have cell' : Function.update τ (g.dst+k) (g.x i) (g.src+i) = g.x i := by
          rw [Function.update_of_ne (by omega),cell]
        light_store (g.key i) 1 using mark,value,pos,expr,cell'
        light_set (k+1 : ℕ)
        exact ⟨_,_,rfl,acc.add H hj i hi rfl fresh⟩
      · have eq' : g.items (j+1) = g.items j := by
          simp [View.items,slice_succ,show g.r+j*g.q<g.n from hi,show g.x i ∈ g.items j from not_not.1 old,i] at *
        exact Ends.skip ⟨k,τ,rfl,⟨acc.kept,eq' ▸ acc.values,eq' ▸ acc.bit⟩⟩
    · have eq' : g.items (j+1) = g.items j := by simp [View.items,slice_succ,show ¬g.r+j*g.q<g.n from hn]
      exact Ends.skip ⟨k,τ,rfl,⟨acc.kept,eq' ▸ acc.values,eq' ▸ acc.bit⟩⟩
  · intro k τ h
    unfold pickState View.args
    light_set (k:ℕ)
    exact ⟨by simpa using (congrArg (Nat.cast : ℕ → ℤ) h.values.card.symm), h.values.card ▸ h.values, h.kept⟩
end Light.Sec3.ChanHe.Separate
