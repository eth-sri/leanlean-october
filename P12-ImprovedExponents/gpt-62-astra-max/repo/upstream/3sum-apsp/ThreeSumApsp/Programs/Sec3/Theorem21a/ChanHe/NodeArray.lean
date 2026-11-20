/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.NodeMemory
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Reduced.Table

/-! Construct the entire modular instance with three applications of the same
bucket minimum pass. Neither unique-bucket flags nor an interleaving of the
three arrays are needed. -/
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp ThreeSumApsp.ChanHe

namespace NodeArray
slots 0 Mod A LA B LB C LC Bound Side Base Area Top Pad Result

def make (p src len h : ℕ) (sg : Expr) := Stmt.call p
  [v len,v src,v Mod,sg,v Area,v Base +' k h *' v Area,v Top,v Pad] Result

def body (p : ℕ) : Stmt := .set Area (v Side *' v Side) ;; .set Top (v Base +' k 3 *' v Area) ;;
  .set Pad (k 2 *' v Bound +' k 1) ;;
  make p A LA 0 (k 1) ;; make p B LB 1 (k 1) ;; make p C LC 2 (k 0 -' k 1)

private theorem rep_bound {V S} (h : Bdd V S) (M k : ℕ) (sg : ℤ) : |rep S M V sg k| ≤ (2*V+1:ℕ) := by
  rcases rep_cases h M sg k with e|⟨_,hb⟩ <;> simp_all [Limit,abs_le] <;> omega

private theorem bounded {a : NodeArgs} {μ} (H : NodeMem μ a) (M : ℕ) (h : Fin 3) (i : ℕ) :
    |(a.job M).values h i| ≤ (a.job M).U := by
  fin_cases h
  · exact rep_bound H.set₁.bdd M i 1
  · exact rep_bound H.set₂.bdd M i 1
  · exact rep_bound H.set₃.bdd M i (-1)

/-- A sequence of writes entirely to the right of `b` preserves its belowWrites. -/
private theorem belowWrites {μ ν : ℕ → ℤ} {b dst C top : ℕ} (h : KeptBut μ ν top dst C)
    (lo : b≤dst) (hi : b≤top) : Kept μ ν b := fun _ hb => h _ ⟨by omega,Or.inl (by omega)⟩

set_option maxHeartbeats 750000 in
theorem spec {lim : Limits} {P : Program} {p w e : ℕ} (hp : P[p]?=some (body w))
    (wr : P[w]?=some (RepTable.body e)) (em : EmodSpec lim P e) : NodeArraySpec lim P p := by
  intro a M μ H hM hC d ok
  let C := a.m*a.m
  have hword := ok.word; have room := ok.cells; have dep : d+2≤lim.depth := ok.depth; have hw := ok.space
  have W := mul_le_word (x:=1) (y:=a.m*a.m+1) (z:=64*(a.V+1)) hword (Nat.one_le_pow _ _ (by omega)) le_rfl le_rfl
  have big : ((4*a.V+4*M+16:ℕ):ℤ) ≤ lim.word := by
    push_cast at W ⊢; nlinarith [mul_nonneg (Nat.cast_nonneg (a.m*a.m+1) : (0:ℤ) ≤ ↑(a.m*a.m+1)) (Nat.cast_nonneg a.V),
      (show (M:ℤ) ≤ (a.m:ℤ)*a.m by exact_mod_cast hC),mul_nonneg (mul_self_nonneg (a.m:ℤ)) (Nat.cast_nonneg a.V)]
  have okE : (emodNeed a.V M).Ok lim a.top (d+1+1) := ⟨big,by dsimp only [nodeArrayNeed,emodNeed] at *; omega,hw,by dsimp only [nodeArrayNeed,emodNeed] at *; omega⟩
  have mem : a.fr+3*C ≤ lim.space := by change a.fr+3*C+_≤_ at room; omega
  have adr := (Int.ofNat_le.mpr mem).trans hw; push_cast at adr; have nz := mul_self_nonneg (a.m:ℤ)
  have build (X : Slot) (hs : X.Ok μ a.toEnv) (sg : ℤ) (sign : sg=1 ∨ sg= -1) (k : ℕ) (idx : k≤2)
      {ν} (keep : Kept μ ν a.fr) :=
    let args : RepTable.Args := ⟨X.addr,M,C,a.fr+k*C,a.top,a.V,sg⟩
    have b := hs.below
    have pre : RepTable.Ready args lim (d+1) X.set ν X.len :=
      ⟨hs.set.kept b keep,hs.bdd,hM,hC,sign,by change X.addr+X.len≤a.fr+k*C; change X.addr+X.len≤a.fr at b; omega,
       by have := Nat.mul_le_mul_right C idx; change a.fr+k*C+C≤a.fr+3*C; omega,okE⟩
    RepTable.spec wr em pre
  apply Meets.of_body hp; unfold body make
  light_set (a.m*a.m:ℕ) using tNodeArray
  light_set (a.fr+3*(a.m*a.m):ℕ) using tNodeArray
  light_set (2*a.V+1:ℕ) using big,tNodeArray
  light_call (build a.X₁ H.set₁ 1 (.inl rfl) 0 (by decide) .refl) using tNodeArray,C,Limit with _ ν₁ ⟨v₁,k₁⟩
  have p₁ : Kept μ ν₁ a.fr := belowWrites k₁ (by simp) (by change a.fr≤a.fr+3*C; omega)
  light_call (build a.X₂ H.set₂ 1 (.inl rfl) 1 (by decide) p₁) using tNodeArray,C,Limit with _ ν₂ ⟨v₂,k₂⟩
  have p₂ : Kept ν₁ ν₂ (a.fr+C) := belowWrites k₂ (by simp) (by change a.fr+C≤a.fr+3*C; omega)
  have orig : Kept μ ν₂ a.fr := p₁.then p₂ fun _ hb => by omega
  light_call (build a.X₃ H.set₃ (-1) (.inr rfl) 2 (by decide) orig) using tNodeArray,C,Limit with _ ν₃ ⟨v₃,k₃⟩
  have p₃ : Kept ν₂ ν₃ (a.fr+2*C) := belowWrites k₃ le_rfl (by change a.fr+2*C≤a.fr+3*C; omega)
  refine ⟨⟨hM,hC,by simp,fun h i _ => bounded H M h i,?_,le_rfl⟩,orig.then p₃ fun _ hb => by omega⟩
  · intro h i hi; change i<M at hi
    have small : i<C := hi.trans_le hC
    fin_cases h
    · change ν₃ (a.fr+0*C+i)=_; change ∀ i<C, ν₁ (a.fr+0*C+i)=_ at v₁; simp only [zero_mul,add_zero] at v₁ ⊢
      exact (p₃ _ (by omega)).trans ((p₂ _ (by omega)).trans (v₁ _ small))
    · change ν₃ (a.fr+1*C+i)=_; exact (p₃ _ (by omega)).trans (v₂ _ small)
    · exact v₃ _ small
end NodeArray
end Light.Sec3.ChanHe
