/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Trace.Mix
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace Light.Sec3.Trace

structure Input where
  address : ℕ
  values : Mat
structure Input.Ok (x : Input) (μ : Mem) (fr n h : ℕ) : Prop where
  read : At μ x.address n x.values
  below : x.address+n*n ≤ fr
  bounded : Bdd n x.values h

/-- Only cells in the half-open scratch interval may change. -/
abbrev Untouched (μ ν : Mem) (fr hi : ℕ) := SameOn (fun c => c<fr ∨ hi≤c) μ ν

structure Task where
  (tab fr : ℕ)
  (a b c : Input)

def side (j : ℕ) : ℕ := 2^j
abbrev Task.regs (x : Task) (j : ℕ) : List ℤ := [j,x.tab,x.a.address,x.b.address,x.c.address,x.fr]

structure Ok (x : Task) (μ : Mem) (j h : ℕ) (lim : Limits) (d top : ℕ) : Prop where
  a : x.a.Ok μ x.fr (side j) h
  b : x.b.Ok μ x.fr (side j) h
  c : x.c.Ok μ x.fr (side j) h
  pow : ∀ k < j, μ (x.tab+k) = (side k : ℕ)
  below : x.tab+j ≤ x.fr
  room : x.fr+2*(side j*side j) ≤ top
  space : top ≤ lim.space
  hw : lim.space ≤ lim.word
  word : (16*(side j*h+1)^3 : ℕ) ≤ lim.word
  depth : d+j+1 ≤ lim.depth

theorem Input.Ok.keep {x : Input} {μ ν : Mem} {fr n h top : ℕ} (H : x.Ok μ fr n h) (same : Untouched μ ν fr top) : x.Ok ν fr n h :=
  {H with read := fun i hi j hj => (same _ (Or.inl (by have := idx hi hj; have := H.below; omega))).trans (H.read _ hi _ hj)}

theorem Ok.keep {x : Task} {μ ν j h lim d top} (H : Ok x μ j h lim d top) (same : Untouched μ ν x.fr top) : Ok x ν j h lim d top :=
  {H with a:=H.a.keep same,b:=H.b.keep same,c:=H.c.keep same,pow:=fun k hk => (same _ (Or.inl (by have := H.below; omega))).trans (H.pow k hk)}

namespace Kernel
slots 0 Level Table A B C Free Half Area Acc Res

def pos (base : ℕ) (q : Fin 4) : Expr := v base +' (k (q.val/2) *' v Half *' (v Half +' v Half) +' k (q.val%2) *' v Half)

def project (p base out : ℕ) (m : Mix) := Stmt.call p
  [v Half,v Free +' k out *' v Area, pos base m.a,pos base m.b,v Half +' v Half,k (m.s+1).toNat -' k 1] Res

def phase (mix self : ℕ) (r : Row) : Stmt :=
  project mix A 0 r.a ;; project mix B 1 r.b ;; project mix C 2 r.c ;;
  .call self [v Level -' k 1,v Table,v Free,v Free +' v Area,v Free +' k 2 *' v Area,v Free +' k 3 *' v Area] Res ;;
  .set Acc (v Acc +' v Res)

def stages (mix self : ℕ) : List Row → Stmt
  | [] => .set Level (v Acc)
  | r::rs => phase mix self r ;; stages mix self rs

def body (mix self : ℕ) : Stmt := .ite (v Level =' k 0)
  (.set Level (M (v A) *' M (v B) *' M (v C)))
  (.set Half (M (v Table +' v Level -' k 1)) ;; .set Area (v Half *' v Half) ;;
   .set Acc (k 0) ;; .set Res (k 0) ;; stages mix self rows)

def cost : ℕ → ℕ
  | 0 => 16
  | j+1 => 7*(3*Grid.time (side j) + cost j + 250)+50

abbrev phaseTime (j : ℕ) := 3*Grid.time (side j) + cost j + 250
abbrev value (x : Task) (j : ℕ) := tri (side j) x.a.values x.b.values x.c.values
abbrev gain (x : Task) (j : ℕ) (r : Row) := r.val (side j) x.a.values x.b.values x.c.values
abbrev loc (x : Task) (j : ℕ) (acc res : ℤ) := frame (x.regs (j+1) ++ ([side j,(side j*side j:ℕ),acc,res] : List ℤ))

variable {lim : Limits} {P : Program} {d j h top self mix : ℕ} {x : Task} {μ : Mem}

def Spec (lim : Limits) (P : Program) (self j : ℕ) := ∀ x μ d h top, Ok x μ j h lim d top →
  Meets lim P self d (x.regs j) μ (cost j) fun z ν => z = value x j ∧ Untouched μ ν x.fr top

abbrev small (x : Task) (j : ℕ) (r : Row) : Task :=
  let n := side j; let u := n*n
  ⟨x.tab, x.fr+3*u, ⟨x.fr,r.a.mat n x.a.values⟩,⟨x.fr+u,r.b.mat n x.b.values⟩,⟨x.fr+2*u,r.c.mat n x.c.values⟩⟩

private theorem givesPos {σ : State} {id src n : ℕ} (q : Fin 4) (base : σ.loc id = src)
    (half : σ.loc Half = n) (hn : 2*n+2 ≤ lim.word) (room : ((src+origin q n:ℕ):ℤ) ≤ lim.word) :
    (pos id q).Gives lim σ (src+origin q n : ℕ) := by
  have nn : 0≤(n:ℤ)*(n+n) := by positivity
  fin_cases q <;> norm_num [pos,origin,base,half,abs_le,-abs_mul] at room ⊢ <;> omega

theorem callMix (p rslot out : ℕ) (m : Mix) (hp : P[p]?=some (Grid.code mixCell))
    (H : Ok x μ (j+1) h lim d top) (hs : |m.s| ≤ 1) (z : Input) (data : z.Ok μ x.fr (side (j+1)) h)
    (acc res : ℤ) (reg : loc x j acc res rslot = z.address) (hout : out ≤ 2) :
    Ends lim P d (project p rslot out m) ⟨loc x j acc res,μ⟩ (Grid.time (side j)+60) fun σ => ∃ y ν,
      σ = ⟨loc x j acc y,ν⟩ ∧ At ν (x.fr+out*(side j*side j)) (side j) (m.mat (side j) z.values) ∧
      SameOutside μ ν (x.fr+out*(side j*side j)) (side j*side j) := by
  generalize en : side j = n at *
  have two : side (j+1)=n+n := by rw [← en]; simp [side,pow_succ,Nat.mul_two]
  have posN : 1≤n := en ▸ Nat.one_le_pow j 2 (by decide)
  have data' := two ▸ data.below; have room := H.room; rw [two] at room
  have dep := H.depth; have hw := H.hw; have sp := H.space
  have hroom : x.fr + out*(n*n)+n*n ≤ lim.space := by nlinarith [Nat.mul_le_mul_right (n*n) hout]
  have word := H.word; rw [two] at word
  have base : 2*h ≤ (n+n)*h := by gcongr; omega
  have hword : (2*h:ℕ) ≤ lim.word := le_trans (Int.ofNat_le.mpr (by change 2*h ≤ 16*((n+n)*h+1)^3; nlinarith only [base,Nat.le_self_pow (by decide : 3≠0) ((n+n)*h+1)])) word
  have leN : 2*n+2 ≤ lim.word := by zify at room sp posN; push_cast at room; nlinarith
  have addr (q : Fin 4) : ((z.address+origin q n : ℕ):ℤ) ≤ lim.word := by
    have := idx (offs (i:=0) (by omega : 0<n) q).1 (offs (i:=0) (by omega : 0<n) q).2
    simp only [Nat.zero_add] at this; unfold origin; omega
  have ok (q : Fin 4) := givesPos (σ:=⟨loc x j acc res,μ⟩) q reg (show loc x j acc res Half = n from congrArg Nat.cast en) leN (addr q)
  have c₁ := (ok m.a).1; have c₂ := (ok m.b).1
  have v₁ := (ok m.a).2; have v₂ := (ok m.b).2
  have cs : ((m.s+1).toNat:ℤ) = m.s+1 := by rw [Int.toNat_of_nonneg]; rw [abs_le] at hs; omega
  refine Ends.callTo (mix_spec (d:=d+1) m hp (two ▸ data.read) (two ▸ data.bounded) hs hw hword (le_trans data' (Nat.le_add_right ..)) hroom)
    (fun y ν h => ⟨y,ν,rfl,h⟩) ?_ (by omega) (by simp [project,pos,Expr.cost]; omega)
  rw [abs_le] at hs
  zify at hroom; push_cast at hroom
  have nn : 0≤(out:ℤ)*(n*n) := by positivity
  have nn' : 0≤(n:ℤ)*n := by positivity
  simp [loc,en] at c₁ c₂ v₁ v₂
  light_side [en,c₁,c₂,v₁,v₂,cs]

/-- The three small squares occupy consecutive pages. Reusing the same pages
for each row only costs quadratic scratch space at a level. -/
theorem phase_spec (hp : P[mix]?=some (Grid.code mixCell)) (ih : Spec lim P self j)
    (H : Ok x μ (j+1) h lim d top) (r : Row) (signs : |r.a.s| ≤ 1 ∧ |r.b.s| ≤ 1 ∧ |r.c.s| ≤ 1)
    (acc res : ℤ) (fits : |acc+gain x j r| ≤ lim.word) :
    Ends lim P d (phase mix self r) ⟨loc x j acc res,μ⟩ (phaseTime j) fun σ => ∃ ν,
      σ = ⟨loc x j (acc+gain x j r) (gain x j r),ν⟩ ∧ Untouched μ ν x.fr top := by
  let n := side j; let u := n*n
  have two : side (j+1)=n+n := by simp [side,n,pow_succ,Nat.mul_two]
  have room := H.room; rw [two] at room
  have hroom : x.fr+5*u ≤ top := by dsimp [u]; nlinarith
  have dep := H.depth; have := H.space; have := H.hw
  rcases signs with ⟨s₁,s₂,s₃⟩
  have clean {ν ν' : Mem} {i : ℕ} (hi : i ≤ 2) (s : SameOutside ν ν' (x.fr+i*u) u) : Untouched ν ν' x.fr top :=
    SameOn.mono s (fun _ h => by have := Nat.mul_le_mul_right u hi; rcases h with h|h <;> omega)
  unfold phase
  light_piece (callMix _ _ 0 _ hp H s₁ _ H.a acc res rfl (by decide)) using phaseTime with _ ⟨r₁,ν₁,rfl,a,same₁⟩
  have kept₁ := clean (by decide : 0≤2) same₁
  light_piece (callMix _ _ 1 _ hp (H.keep kept₁) s₂ _ ((H.keep kept₁).b) acc r₁ rfl (by decide)) using phaseTime with _ ⟨r₂,ν₂,rfl,b,same₂⟩
  have kept₂ := kept₁.trans (clean (by decide : 1≤2) same₂)
  light_piece (callMix _ _ 2 _ hp (H.keep kept₂) s₃ _ ((H.keep kept₂).c) acc r₂ rfl (by decide)) using phaseTime with _ ⟨r₃,ν₃,rfl,c,same₃⟩
  have same := kept₂.trans (clean (by decide : 2≤2) same₃)
  have sub : Ok (small x j r) ν₃ j (2*h) lim (d+1) top := by
    simp only [Nat.zero_mul,Nat.add_zero,Nat.one_mul] at a same₁ b same₂
    refine ⟨⟨(a.keep same₂ (by omega)).keep same₃ (by omega),by change x.fr+u ≤ x.fr+3*u; omega,bdd_mix _ s₁ (two ▸ H.a.bounded)⟩,
      ⟨b.keep same₃ (by omega),by change x.fr+u+u ≤ x.fr+3*u; omega,bdd_mix _ s₂ (two ▸ H.b.bounded)⟩,
      ⟨c,by change x.fr+2*u+u ≤ x.fr+3*u; omega,bdd_mix _ s₃ (two ▸ H.c.bounded)⟩,
      fun k hk => (H.keep same).pow k (by omega),by have := H.below; change x.tab+j≤x.fr+3*u; omega,
      by change x.fr+3*u+2*u≤top; omega,H.space,H.hw,?_,by omega⟩
    have word := H.word; rw [two] at word; have e : side j * (2*h) = (n+n)*h := by dsimp [n]; ring
    exact e ▸ word
  have hw := H.word; have posN := Nat.one_le_pow j 2 (by decide); change 1≤side j at posN
  have big : (3:ℤ) ≤ lim.word := le_trans (by exact_mod_cast (show 3≤16*(side (j+1)*h+1)^3 from by have := Nat.one_le_pow 3 (side (j+1)*h+1) (by omega); omega)) hw
  have hs : ((x.fr+5*(side j*side j):ℕ):ℤ) ≤ lim.word := le_trans (Int.ofNat_le.mpr (hroom.trans H.space)) H.hw
  push_cast at hs
  have sn : 0≤(side j:ℤ)*side j := by positivity
  have := H.below
  light_call (ih _ _ _ _ _ sub) using phaseTime,n,u with _ ν₄ ⟨rfl,same₄⟩
  have ev : value (small x j r) j = gain x j r := rfl
  have h := abs_le.mp fits
  light_set (acc+gain x j r) using ev,phaseTime,n,u
  exact ⟨ν₄,rfl,same.then same₄ fun b hb => ⟨hb,by change b<x.fr+3*u ∨ _; omega⟩⟩
end Kernel
end Light.Sec3.Trace
