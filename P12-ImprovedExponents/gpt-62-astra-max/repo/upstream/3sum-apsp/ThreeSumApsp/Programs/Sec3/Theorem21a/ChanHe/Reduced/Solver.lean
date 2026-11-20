/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Reduced.Grid
public import ThreeSumApsp.Lang.PolyBounded

@[expose] public section
namespace Light.Sec3.HashTriangle
open ThreeSumApsp

slots 0 Side Bound Mod Src Free Area Padding Found Shift Answer

def fillOne (p : ℕ) (h : Fin 3) : Stmt :=
  let off := k h.val *' v Area
  .call (p+h.val) [v Side,v Free +' off,v Src +' off,v Mod,v Shift,v Padding] Answer

def round (p et : ℕ) : Stmt := fillOne p 0 ;; fillOne p 1 ;; fillOne p 2 ;;
  .call et [v Side,v Padding,v Free,v Free +' v Area,v Free +' k 2 *' v Area,v Free +' k 3 *' v Area] Answer ;;
  .ite (v Answer =' k 1) (.set Found (k 1)) .skip

def body (p et : ℕ) : Stmt := .set Area (v Side *' v Side) ;; .set Padding (k 2 *' v Bound +' k 1) ;;
  .set Found (k 0) ;; .for Shift (v Side +' k 1) (round p et) ;; .set 0 (v Found)

def own (t : ℕ) := (t+1)*(3*Trace.Grid.time t+140)+50
def time (T : ℕ→ℕ→ℕ) (t U : ℕ) := own t+(t+1)*T t (2*U+1)
def need (r : ℕ→ℕ→Need) (t U : ℕ) : Need := let k := r t (2*U+1)
  ⟨k.word+2*U+t+8,k.cells+3*(t*t),k.depth+1⟩

variable {x : Job} {μ ν η : ℕ → ℤ} {fr s : ℕ}

private theorem base_kept {z : ℕ} (h : Fin 3) (o : SameOutside ν η (block fr z h) z) : Kept ν η fr :=
  fun i hi => o _ (Or.inl (lt_of_lt_of_le hi (Nat.le_add_right ..)))

private theorem Pre.keep (H : Pre x μ fr) (k : Kept μ ν fr) : Pre x ν fr := {H with
  cells := fun h i hi => (k _ (by have := block_le x.base x.area h; have := H.cap; have := H.below; omega)).trans (H.cells h _ hi)}

private theorem array (H : Pre x μ fr) (h : Fin 3) (w : Trace.At ν (block fr x.area h) x.t (entry x s h)) :
    ArrayAt ν (block fr x.area h) (flat x.t (entry x s h)) x.area x.fill (fr+3*x.area) := by
  refine ⟨by simp,?_,?_,block_le ..⟩
  · intro u hu; obtain ⟨i,hi,j,hj,rfl⟩ := Nat.exists_eq_mul_add_of_lt_mul (show u<x.t*x.t by simpa using hu)
    simpa [Nat.add_assoc,Nat.mul_add_div_of_lt hj,Nat.mul_add_mod_of_lt hj] using w _ hi _ hj
  · rintro _ hv; obtain ⟨_,_,rfl⟩ := List.mem_map.mp hv; exact entry_fits H ..

private abbrev state (x : Job) (fr i : ℕ) (v : ℤ × ℤ) (ν : ℕ → ℤ) : State :=
  ⟨frame (x.args ++ [(fr:ℤ),x.area,x.fill,v.1,i,v.2]),ν⟩

private theorem run {P R : Program} {lim : Limits} {d p et : ℕ} {T r} (hs : Solves etTask P et T r)
    (cells : ∀ h : Fin 3, (P++R)[p+h.val]?=some (Trace.Grid.code (cell h))) (H : Pre x μ fr)
    (ok : (need r x.t x.U).Ok lim fr d) :
    Ends lim (P++R) d (body p et) ⟨frame (x.args++[(fr:ℤ)]),μ⟩ (time T x.t x.U) fun σ =>
      σ.loc 0=flag x.hit ∧ Kept μ σ.mem fr := by
  have hsok : (r x.t x.fill).Ok lim (fr+3*x.area) (d+1) := by apply ok.mono <;> simp [need,Job.fill,Job.area] <;> omega
  have room := hsok.cells; have hw := ok.space; have depth := hsok.depth; have word := ok.word
  dsimp only [need] at word; have src := H.below
  have ad := (Int.ofNat_le.mpr (by omega : fr+3*x.area≤lim.space)).trans hw
  push_cast at ad; have nz : 0 ≤ (x.t:ℤ)*x.t := by positivity
  have ht : 1≤x.t := by have m := H.positive; have b := H.cap; by_contra! e; simp [Job.area,show x.t=0 by omega] at b; omega
  let seen i := ∃ k < i,yesAt x k
  let unit := 3*Trace.Grid.time x.t + T x.t x.fill + 120
  have t_eq : time T x.t x.U = 50+(x.t+1)*(unit+20) := by unfold time own unit Job.fill; ring
  rw [t_eq]; unfold body
  light_set (x.t*x.t:ℕ)
  light_set (2*x.U+1:ℕ)
  light_set 0
  refine Ends.next _ (Ends.forCarry (state x fr) (fun i v ν => v.1= flag (seen i) ∧ Kept μ ν fr)
    (x.t+1) unit (0,0) ⟨(flag_of_not (by simp [seen])).symm,.refl⟩ ?_ ?_ (first:=by rw [update_frame_setLocal,← frame_append_zeros _ 1]; rfl) (hT:=le_rfl)) (by simp [Nat.mul_add,Nat.add_mul]; omega)
  · rintro i ⟨f,old⟩ ν hi ⟨rfl,kν⟩
    have doGrid (h : Fin 3) {v} (k : Kept μ v fr) := grid_spec (d:=d+1) h (cells h) (H.keep k) (by omega : i≤x.t) hw (by omega)
    unfold round fillOne state
    light_call (doGrid 0 kν) using unit with _ ν₀ ⟨a,o₀⟩
    have k₀ := kν.trans (base_kept 0 o₀)
    light_call (doGrid 1 k₀) using unit with _ ν₁ ⟨b,o₁⟩
    have k₁ := k₀.trans (base_kept 1 o₁)
    light_call (doGrid 2 k₁) using unit with _ ν₂ ⟨c,o₂⟩
    have k₂ := k₁.trans (base_kept 2 o₂)
    have v₀ := array H 0 ((a.keep o₁ (by simp [block])).keep o₂ (by simp [block, Job.area]; omega))
    have v₁ := array H 1 (b.keep o₂ (by simp [block, Job.area]; omega))
    have v₂ := array H 2 c
    simp [block] at v₀ v₁ v₂
    have V : (instanceAt x fr i).Pre ν₂ (fr+3*x.area) := by
      simpa [instanceAt,block] using triPre_of_arrays ht (by unfold Job.fill; omega : 1≤x.fill) v₀ v₁ v₂
    light_call (hs.meets R (instanceAt x fr i) _ V hsok) using unit,etTask,instanceAt with ans ν₃ ⟨e,o₃⟩
    have same := k₂.then o₃ fun b hb => by exact ⟨hb,by omega⟩
    replace e := e.trans (flag_congr (yes_iff x fr i)); subst ans
    have sameCost : T (etTask.size (instanceAt x fr i)) (etTask.bound (instanceAt x fr i)) = T x.t x.fill := rfl
    have step : seen (i+1) ↔ seen i ∨ yesAt x i := Nat.exists_lt_succ_right
    by_cases hit : yesAt x i
    · rw [flag_of hit]; light_if yes no : True
      · light_set 1
        exact ⟨(1,1),ν₃,rfl,(flag_of (step.mpr (.inr hit))).symm,same⟩
      · contradiction
    · rw [flag_of_not hit]; light_if yes no : False
      · contradiction
      · exact Ends.skip ⟨(_,0),ν₃,rfl,(flag_congr (step.trans (or_iff_left hit))).symm,same⟩
  · rintro ⟨f,old⟩ ν ⟨rfl,keep⟩
    exact Ends.setTo (flag (seen (x.t+1))) ⟨(flag_congr (hit_iff H)).symm,keep⟩ (hT:=by simp [Nat.mul_add,Nat.add_mul]; omega)

theorem host : IsHost etTask task time need := by
  refine ⟨fun P et T r hs => ?_,fun r hr => ?_⟩
  · let p := P.length
    refine ⟨[Trace.Grid.code (cell 0),Trace.Grid.code (cell 1),Trace.Grid.code (cell 2),body p et],p+3,body p et,by simp [p],?_⟩
    intro R lim d x μ fr H ok; rw [List.append_assoc]
    exact run hs (fun h => by fin_cases h <;> simp [p]) H ok
  · unfold need; poly_need [hr.word,hr.cells,hr.depth]
end Light.Sec3.HashTriangle
