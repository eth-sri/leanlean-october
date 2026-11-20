/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Reduced.Instance
public import ThreeSumApsp.Programs.Sec3.Theorem17.Trace.Table

/-! Each edge is one bounded table lookup. The three matrices use the same
nested loops; for AC only, subtract the modulus before the lookup if needed. -/
@[expose] public section
namespace Light.Sec3.HashTriangle
open Trace Grid ThreeSumApsp

def raw (h : Fin 3) : Expr := if h=0 then v I *' v N +' v J else if h=1 then
  v Stride *' v N +' v J -' v I else (v I +' v Stride) *' v N +' v J

def put (z : Expr) : Stmt := .ite (z <' k 0) (save (v Factor))
  (.ite (z <' v Src₂) (save (M (v Src₁ +' z))) (save (v Factor)))

def cell (h : Fin 3) : Stmt := if h=2 then .ite (raw h <' v Src₂) (put (raw h)) (put (raw h -' v Src₂)) else put (raw h)

abbrev gridArgs (x : Job) (s fr : ℕ) (h : Fin 3) : Args :=
  ⟨x.t,block fr x.area h,block x.base x.area h,x.M,s,x.fill⟩

variable {lim : Limits} {P : Program} {μ : Mem} {fr s d p : ℕ} {x : Job}

theorem block_le (base area : ℕ) (h : Fin 3) : block base area h+area ≤ base+3*area := by
  have := Nat.mul_le_mul_right area (show h.val ≤ 2 by omega); unfold block; omega

theorem grid_spec (h : Fin 3) (hp : P[p]?=some (code (cell h))) (H : Pre x μ fr) (hs : s≤x.t)
    (hw : lim.space≤lim.word) (room : fr+3*x.area ≤ lim.space) :
    Meets lim P p d (gridArgs x s fr h).regs μ (time x.t) fun _ ν =>
      At ν (block fr x.area h) x.t (entry x s h) ∧ SameOutside μ ν (block fr x.area h) x.area := by
  let dst := block fr x.area h; let src := block x.base x.area h
  have fit : dst+x.area≤lim.space := (block_le fr x.area h).trans room
  have below : src+x.M≤dst := by
    have := H.cap; have := (block_le x.base x.area h).trans H.below; dsimp [dst,src,block] at *; omega
  refine tabulate hp hw fit (by fin_cases h <;> decide) ?_
  intro i hi j hj ν same
  change i<x.t at hi; change j<x.t at hj; change SameOutside μ ν dst x.area at same
  let σ : State := ⟨(gridArgs x s fr h).loc i j,ν⟩
  have lim₀ : 0≤lim.word := by omega
  have dest := idx hi hj
  have adr : ((dst:ℤ)+i*x.t+j).toNat=dst+i*x.t+j := by exact_mod_cast rfl
  have loc : (v Dst +' v I *' v N +' v J).Safe lim σ ∧ lim.Addr ((dst:ℤ)+i*x.t+j) := by
    change ((True ∧ (True ∧ True ∧ |(i:ℤ)*x.t| ≤ lim.word) ∧ |(dst:ℤ)+i*x.t|≤lim.word) ∧ True ∧ |(dst:ℤ)+i*x.t+j|≤lim.word) ∧ _
    have nz : 0≤(i:ℤ)*x.t := by positivity
    change dst+x.t*x.t≤_ at fit; simp only [true_and,abs_le,Limits.Addr]; omega
  have saveSpec (e : Expr) (v : ℤ) (se : e.Safe lim σ) (ee : e.val σ=v) :
      (save e).Runs lim σ fun τ => τ=⟨σ.loc,Function.update ν (dst+i*x.t+j) v⟩ := by
    refine ⟨⟨loc.1,se,loc.2⟩,?_⟩
    change (State.mk _ (Function.update ν ((dst:ℤ)+i*x.t+j).toNat (e.val σ)))=_
    rw [adr,ee]
  have val (e : Expr) (z : ℤ) (safe : e.Safe lim σ) (eq : e.val σ=z) :
      (put e).Runs lim σ fun τ => τ=⟨σ.loc,Function.update ν (dst+i*x.t+j) (pick x h z)⟩ := by
    have pad := saveSpec (v Factor) x.fill trivial (by rfl)
    unfold put
    by_cases neg : z<0
    · exact .ite_pos (by simpa [pick,not_le.mpr neg] using pad) (by change e.val σ<0; omega) ⟨safe,lim₀⟩
    refine Stmt.Runs.ite_neg ?_ (by change ¬ e.val σ<0; omega) (by exact ⟨safe,lim₀⟩)
    by_cases lt : z<x.M
    · refine Stmt.Runs.ite_pos ?_ (by change e.val σ<x.M; omega) (by exact ⟨safe,trivial⟩)
      have read := (same (src+z.toNat) (Or.inl (by omega))).trans (H.cells h _ (show z.toNat<x.M by omega))
      apply saveSpec
      · change (True ∧ e.Safe lim σ ∧ |(src:ℤ)+e.val σ|≤lim.word) ∧ lim.Addr ((src:ℤ)+e.val σ)
        simp [safe,eq,abs_le,Limits.Addr]; omega
      · change ν ((src:ℤ)+e.val σ).toNat=_
        rwa [eq,show ((src:ℤ)+z).toNat=src+z.toNat by omega, pick,if_pos ⟨by omega,lt⟩]
    · exact .ite_neg (by simpa [pick,lt] using pad) (by change ¬e.val σ<x.M; omega) ⟨safe,trivial⟩
  let z := index h x.t s i j
  have ij := Nat.mul_le_mul_right x.t hi.le; have ss := Nat.mul_le_mul_right x.t hs
  have comb : (i+s)*x.t=i*x.t+s*x.t := Nat.add_mul ..
  have small := Nat.le_mul_self x.t; have cap := H.cap
  have w : ((3*(x.t*x.t):ℕ):ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : 3*x.area ≤ lim.space)).trans hw
  have rz : (raw h).val σ=z := by simp [σ,z,raw,index]; split_ifs <;> rfl
  have rs : (raw h).Safe lim σ ∧ |z-x.M|≤lim.word := by
    dsimp only [Job.area] at cap; have pp : 0 ≤ (i:ℤ)*x.t := by positivity
    have qq : 0 ≤ (s:ℤ)*x.t := by positivity
    simp [σ,z,raw,index,abs_le,-abs_mul,add_mul]; split_ifs <;> simp [abs_le,-abs_mul,add_mul] <;> omega
  apply Ends.block (hT:=le_rfl)
  change (cell h).Runs lim σ fun τ => τ=⟨σ.loc,Function.update ν (dst+i*x.t+j) (pick x h (if h=2 ∧ x.M≤z then z-x.M else z))⟩
  by_cases type : h=2
  · rw [cell,if_pos type]; by_cases le : (x.M:ℤ)≤z
    · rw [if_pos ⟨type,le⟩]; exact .ite_neg (val (raw h -' v Src₂) (z-x.M) (by simpa [rz,σ] using rs) (by simp [rz,σ])) (by change ¬ (raw h).val σ<x.M; omega) ⟨rs.1,trivial⟩
    · rw [if_neg (by simp [le])]; exact .ite_pos (val _ _ rs.1 rz) (by change (raw h).val σ<x.M; omega) ⟨rs.1,trivial⟩
  · simpa [cell,type] using val _ _ rs.1 rz
end Light.Sec3.HashTriangle
