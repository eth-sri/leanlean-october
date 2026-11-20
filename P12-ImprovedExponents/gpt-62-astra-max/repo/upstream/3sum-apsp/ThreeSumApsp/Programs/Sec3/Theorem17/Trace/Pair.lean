/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Trace.Recurse
public import ThreeSumApsp.Programs.Sec3.Theorem17.Trace.Mask

@[expose] public section
namespace Light.Sec3.Trace
structure Batch where
  (p n j tab fr : ℕ)
  (a b c : Input)
abbrev Batch.N (x : Batch) := side x.j
abbrev Batch.regs (x : Batch) (s t : ℕ) : List ℤ := [s,t,x.p,x.n,x.j,x.N,x.tab,x.a.address,x.b.address,x.c.address,x.fr]

structure Ready (x : Batch) (μ : Mem) (lim : Limits) (top : ℕ) : Prop where
  src : ∀ z ∈ [x.a,x.b,x.c], At μ z.address x.n z.values ∧ z.address+x.n*x.n ≤ x.fr
  pow : ∀ k<x.j, μ (x.tab+k) = (side k : ℕ)
  tab : x.tab+x.j ≤ x.fr
  room : x.fr+6*(x.N*x.N) ≤ top
  space : top ≤ lim.space
  hw : lim.space ≤ lim.word
  word : (64*(x.p+1)^2*(x.N+1)^3:ℕ) ≤ lim.word

theorem Ready.keep {x μ ν lim top} (H : Ready x μ lim top) (same : Untouched μ ν x.fr top) : Ready x ν lim top := {H with
  src := fun z hz => ⟨fun i hi j hj => (same _ (Or.inl (by have := idx hi hj; have := (H.src z hz).2; omega))).trans ((H.src z hz).1 _ hi _ hj),(H.src z hz).2⟩
  pow := fun k hk => (same _ (Or.inl (by have := H.tab; omega))).trans (H.pow _ hk)}

namespace Pair
slots 0 S T Prime N Level Side Tab A B C Free Key Area Res

def makeKey := Stmt.ite (v S +' v T =' k 0) (.set Key (k 0))
  (.ite (v Prime <' (v S +' v T)) (.set Key (k 2 *' v Prime -' (v S +' v T))) (.set Key (v Prime -' (v S +' v T))))

def makeMask (p src out r : ℕ) := Stmt.call p [v Side,v Free +' k out *' v Area,v src,k 0,v N,v r] Res

def body (mask kernel : ℕ) : Stmt := makeKey ;; .set Area (v Side *' v Side) ;;
  makeMask mask A 0 S ;; makeMask mask B 1 T ;; makeMask mask C 2 Key ;;
  .call kernel [v Level,v Tab,v Free,v Free +' v Area,v Free +' k 2 *' v Area,v Free +' k 3 *' v Area] S

def time (j : ℕ) := 3*Grid.time (side j) + Kernel.cost j + 150

variable {lim : Limits} {P : Program} {μ : Mem} {d s t kernel mask top : ℕ} {x : Batch}

private theorem makeKey_spec (hs : s<x.p) (ht : t<x.p) (word : 2*(x.p:ℤ)+4 ≤ lim.word) :
    Ends lim P d makeKey ⟨frame (x.regs s t),μ⟩ 20 fun τ => τ = ⟨frame (x.regs s t ++ [key x.p s t]),μ⟩ := by
  apply Ends.block (hT:=by decide)
  have e : (s:ℤ)+t=0 ↔ s+t=0 := by omega
  have b : (x.p:ℤ)<(s:ℤ)+t ↔ x.p<s+t := by omega
  by_cases h : s+t=0
  · have a : s=0 := by omega
    have b : t=0 := by omega
    simp [Stmt.Runs,makeKey,key,a,b,update_frame_setLocal]; omega
  · by_cases le : s+t≤x.p <;> simp [Stmt.Runs,makeKey,key,le,h,e,b,show (x.p<s+t) ↔ ¬s+t≤x.p by omega,
      abs_le,update_frame_setLocal,-Nat.add_eq_zero_iff] <;> omega

/-- One scalar contraction of three padded indicator matrices. -/
theorem spec {p : ℕ} (hp : P[p]?=some (body mask kernel)) (hm : P[mask]?=some (Grid.code maskCell))
    (hk : ∀ j, Kernel.Spec lim P kernel j) (H : Ready x μ lim top) (hs : s<x.p) (ht : t<x.p)
    (depth : d+x.j+2 ≤ lim.depth) : Meets lim P p d (x.regs s t) μ (time x.j) fun z ν =>
      z=part x.n x.N x.p x.a.values x.b.values x.c.values s t ∧ Untouched μ ν x.fr top := by
  let u := x.N*x.N
  have room := H.room; have sp := H.space; have hw := H.hw
  have uh : ((x.fr+6*(x.N*x.N):ℕ):ℤ) ≤ lim.word := (Int.ofNat_le.mpr (room.trans sp)).trans hw
  push_cast at uh; have un : 0 ≤ (x.N:ℤ)*x.N := by positivity
  have word := H.word; have pos : 1≤(x.N+1)^3 := Nat.one_le_pow _ _ (by omega)
  have large : (64*((x.p+1)^2):ℕ) ≤ lim.word := (Int.ofNat_le.mpr (Nat.le_mul_of_pos_right _ pos)).trans word
  have wp : 2*(x.p:ℤ)+4 ≤ lim.word := by push_cast at large; nlinarith
  have one : 1≤lim.word := by omega
  have mk {ν} (z : Input) (hz : z∈[x.a,x.b,x.c]) (r : ℤ) (i : ℕ) (hi : i≤2) (R : Ready x ν lim top) :=
    mask_spec (d:=d+1) hm r (R.src z hz).1 hw one (dst:=x.fr+i*u) (le_trans (R.src z hz).2 (Nat.le_add_right ..))
      (by have := Nat.mul_le_mul_right u hi; change x.fr+i*u+u ≤ _; dsimp [u] at *; omega)
  have clean {ν ν' : Mem} {i : ℕ} (hi : i≤2) (o : SameOutside ν ν' (x.fr+i*u) u) : Untouched ν ν' x.fr top :=
    SameOn.mono o fun _ h => by have := Nat.mul_le_mul_right u hi; dsimp [u] at *; rcases h with h|h <;> omega
  apply Meets.of_body hp; unfold body makeMask
  light_piece (makeKey_spec (d:=d) (P:=P) hs ht wp) using time with _ rfl
  light_set (x.N*x.N : ℕ) using time
  light_call (mk x.a (by simp) s 0 (by decide) H) using time,u with _ ν₁ ⟨a,o₁⟩
  have k₁ := clean (by decide : 0≤2) o₁
  light_call (mk x.b (by simp) t 1 (by decide) (H.keep k₁)) using time,u with _ ν₂ ⟨b,o₂⟩
  have k₂ := k₁.trans (clean (by decide : 1≤2) o₂)
  light_call (mk x.c (by simp) (key x.p s t) 2 (by decide) (H.keep k₂)) using time,u with _ ν₃ ⟨c,o₃⟩
  have same := k₂.trans (clean (by decide : 2≤2) o₃)
  let task : Task := ⟨x.tab,x.fr+3*u, ⟨x.fr,mark x.n x.a.values s⟩,⟨x.fr+u,mark x.n x.b.values t⟩,⟨x.fr+2*u,mark x.n x.c.values (key x.p s t)⟩⟩
  have bd (A : Mat) (r : ℤ) : Bdd x.N (mark x.n A r) 1 := fun i _ j _ => by simp [mark]; split_ifs <;> norm_num
  have ok : Ok task ν₃ x.j 1 lim (d+1) top := by
    simp only [zero_mul,one_mul,add_zero] at a b o₂
    change x.fr+6*u ≤ top at room
    refine ⟨⟨(a.keep o₂ (by omega)).keep o₃ (by omega),by change x.fr+u≤x.fr+3*u; omega,bd _ _⟩,
      ⟨b.keep o₃ (by omega),by change x.fr+u+u≤x.fr+3*u; omega,bd _ _⟩,
      ⟨c,by change x.fr+2*u+u≤x.fr+3*u; omega,bd _ _⟩,(H.keep same).pow,
      by have := H.tab; change x.tab+x.j ≤ x.fr+3*u; omega,by change x.fr+3*u+2*u≤top; omega,sp,hw,?_,by omega⟩
    simp only [mul_one]; refine le_trans (Int.ofNat_le.mpr (Nat.mul_le_mul_right _ ?_)) word
    have := Nat.one_le_pow 2 (x.p+1) (by omega); omega
  light_call (hk x.j _ _ _ _ _ ok) using time,u,task with _ ν₄ ⟨rfl,o₄⟩
  exact ⟨rfl,same.then o₄ fun b hb => ⟨hb,by change b<x.fr+3*u ∨ _; omega⟩⟩
end Pair
end Light.Sec3.Trace
