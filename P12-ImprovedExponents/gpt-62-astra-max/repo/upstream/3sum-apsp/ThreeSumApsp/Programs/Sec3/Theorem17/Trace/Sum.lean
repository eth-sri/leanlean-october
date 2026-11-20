/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Trace.Pair

@[expose] public section
namespace Light.Sec3.Trace.Sum
open Finset Pair
slots 11 Acc Idx Res

def body (child : ℕ) : Stmt := .set Acc (k 0) ;; .set Res (k 0) ;;
  .for Idx (v Prime) (.call child [v T,v Idx,v Prime,v N,v Level,v Side,v Tab,v A,v B,v C,v Free] Res ;;
    .set Acc (v Acc +' v Res)) ;; .set S (v Acc)

def time (p c : ℕ) := p*(c+30)+20

variable {lim : Limits} {P : Program} {d top p child a b c : ℕ} {x : Batch} {μ : Mem}

theorem abs_psum {f : ℕ → ℤ} {m : ℕ} {B : ℤ} (bound : ∀ i < m, |f i| ≤ B) :
    |∑ i ∈ range m, f i| ≤ m*B :=
  (Finset.abs_sum_le_sum_abs ..).trans (le_trans (sum_le_sum fun _ hi => bound _ (mem_range.1 hi)) (by simp))

/-- Shift the latest residue into the first argument and sum over its successor.
Link the same loop twice to enumerate all ordered pairs of residues. -/
theorem spec (hp : P[p]? = some (body child)) (f : ℕ → ℤ) (H : Ready x μ lim top)
    (hd : d<lim.depth) (hW : (x.p:ℤ) ≤ lim.word) (hF : ∀ i≤x.p, |∑ k ∈ range i, f k| ≤ lim.word)
    (hsub : ∀ i<x.p, ∀ ν, Ready x ν lim top → Meets lim P child (d+1) (x.regs b i) ν c fun v τ =>
      v=f i ∧ Untouched ν τ x.fr top) :
    Meets lim P p d (x.regs a b) μ (time x.p c) fun z ν => z=∑ i ∈ range x.p, f i ∧ Untouched μ ν x.fr top := by
  let val i := ∑ k ∈ range i, f k
  have next (i : ℕ) : val (i+1) = val i+f i := sum_range_succ _ _
  have hzero : val 0=0 := rfl
  apply Meets.of_body hp; unfold body time
  light_set (val 0) using hzero
  light_set (0:ℤ)
  refine Ends.next _ (Ends.forCarry (fun i (r : ℤ × ℤ) ν => ⟨frame (x.regs a b ++ ([r.1,i,r.2]:List ℤ)),ν⟩)
    (fun i r ν => r.1=val i ∧ Untouched μ ν x.fr top) x.p (c+18) (val 0,0) ⟨rfl,SameOn.refl⟩ ?_ ?_
    (first:=by rw [update_frame_setLocal]; rfl) (hT:=le_rfl)) (by simp; nlinarith)
  · rintro i ⟨_,r⟩ ν hi ⟨rfl,same⟩
    have bd := abs_le.mp (hF (i+1) hi)
    change _ ≤ val (i+1) ∧ val (i+1) ≤ _ at bd; rw [next] at bd
    light_call (hsub i hi ν (H.keep same)) with _ τ ⟨rfl,o⟩
    light_set (val (i+1)) using next
    exact ⟨(val (i+1),f i),τ,rfl,rfl,same.trans o⟩
  · rintro ⟨_,r⟩ ν ⟨rfl,same⟩
    exact Ends.setTo (val x.p) ⟨rfl,same⟩ (hT:=by simp; ring_nf; omega)

/-- The two nested folds and the leaf contraction, with one common scratch bound. -/
theorem all {pair kernel mix mask inner : ℕ}
    (hmix : P[mix]?=some (Grid.code mixCell)) (hk : P[kernel]?=some (Kernel.body mix kernel))
    (hm : P[mask]?=some (Grid.code maskCell)) (leaf : P[pair]?=some (Pair.body mask kernel))
    (h₁ : P[inner]?=some (body pair)) (h₂ : P[p]?=some (body inner)) (H : Ready x μ lim top)
    (hd : d+x.j+4 ≤ lim.depth) (hpos : 0<x.p) :
    Meets lim P p d (x.regs 0 0) μ (time x.p (time x.p (Pair.time x.j))) fun z ν =>
      z=∑ s ∈ range x.p, ∑ t ∈ range x.p, part x.n x.N x.p x.a.values x.b.values x.c.values s t ∧ Untouched μ ν x.fr top := by
  let v := part x.n x.N x.p x.a.values x.b.values x.c.values
  let U : ℤ := (x.N:ℤ)^3
  have U₀ : 0≤U := by dsimp [U]; positivity
  have cap : (x.p:ℤ)*(x.p*U) ≤ lim.word := le_trans (by
    change (x.p:ℤ)*(x.p*(x.N:ℤ)^3) ≤ ((64*(x.p+1)^2*(x.N+1)^3:ℕ):ℤ)
    exact_mod_cast (show x.p*(x.p*x.N^3) ≤ _ by rw [← Nat.mul_assoc,← sq]; gcongr <;> nlinarith)) H.word
  have U₁ : 1≤U := by dsimp [U]; exact_mod_cast Nat.one_le_pow 3 x.N (Nat.one_le_pow _ _ (by decide))
  have wp : (x.p:ℤ) ≤ lim.word := le_trans (by zify at hpos; nlinarith [mul_le_mul_of_nonneg_left U₁ (Nat.cast_nonneg x.p)]) cap
  have hb s i (hi : i≤x.p) : |∑ t ∈ range i, v s t| ≤ x.p*U :=
    (abs_psum (fun t _ => part_bound ..)).trans (mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hi) U₀)
  refine spec h₂ _ H (by omega) wp (fun i hi => (abs_psum (fun s _ => hb s x.p le_rfl)).trans
    (le_trans (mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hi) (by positivity)) cap)) ?_
  intro s hs ν R
  refine spec h₁ _ R (by omega) wp (fun i hi => (hb s i hi).trans ((le_mul_of_one_le_left (by positivity) (Int.ofNat_le.mpr hpos)).trans cap)) ?_
  exact fun t ht τ ok => Pair.spec leaf hm (Kernel.spec hmix hk) ok hs ht (by omega)
end Light.Sec3.Trace.Sum
