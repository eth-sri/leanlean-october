/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Trace.Algebra
public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Lang.Slots

@[expose] public section
namespace Light.Sec3.Trace
abbrev Mem := ℕ → ℤ

def At (μ : Mem) (base n : ℕ) (A : Mat) := ∀ i < n, ∀ j < n, μ (base + i*n+j) = A i j

theorem idx {n i j : ℕ} (hi : i<n) (hj : j<n) : i*n+j < n*n := by
  have := Nat.mul_le_mul_right n hi; rw [Nat.succ_mul] at this; omega

theorem At.keep {μ ν : Mem} {base n : ℕ} {A} (h : At μ base n A) {a l : ℕ}
    (same : SameOutside μ ν a l) (below : base+n*n ≤ a) : At ν base n A := fun i hi j hj =>
  (same _ (Or.inl (by have := idx hi hj; omega))).trans (h _ hi _ hj)

namespace Grid
slots 0 N Dst Src₁ Src₂ Stride Factor I J
structure Args where
  (n dst a b stride : ℕ)
  (s : ℤ)

abbrev Args.regs (x : Args) : List ℤ := [x.n,x.dst,x.a,x.b,x.stride,x.s]
abbrev Args.loc (x : Args) (i j : ℤ) := frame (x.regs ++ [i,j])

def code (cell : Stmt) : Stmt := .for I (v N) (.for J (v N) cell)

def save (e : Expr) : Stmt := .store (v Dst +' v I *' v N +' v J) e

def time (n : ℕ) := 160*(n+1)^2

variable {lim : Limits} {P : Program} {d : ℕ} {x : Args} {μ : Mem}

theorem tabulate {p : ℕ} {cell : Stmt} {A : Mat} (hp : P[p]? = some (code cell))
    (hw : lim.space ≤ lim.word) (room : x.dst+x.n*x.n ≤ lim.space) (cost : cell.blockCost ≤ 100)
    (one : ∀ i < x.n, ∀ j < x.n, ∀ ν, SameOutside μ ν x.dst (x.n*x.n) →
      Ends lim P d cell ⟨x.loc i j,ν⟩ cell.blockCost fun τ =>
        τ = ⟨x.loc i j,Function.update ν (x.dst+i*x.n+j) (A i j)⟩) :
    Meets lim P p d x.regs μ (time x.n) fun _ ν => At ν x.dst x.n A ∧ SameOutside μ ν x.dst (x.n*x.n) := by
  let f t := A (t/x.n) (t%x.n)
  let w t := wrote μ x.dst f t
  have leN := Nat.le_mul_self x.n
  have wnext i (hi : i<x.n) j (hj : j<x.n) :
      Function.update (w (i*x.n+j)) (x.dst+i*x.n+j) (A i j) = w (i*x.n+j+1) := by
    simpa [w,f,Nat.add_assoc,Nat.mul_add_div_of_lt hj,Nat.mul_add_mod_of_lt hj] using
      (wrote_succ (μ:=μ) (dst:=x.dst) (f:=f) (j:=i*x.n+j))
  refine .of_body hp (Ends.forShape (fun i (j : ℤ) ν => ⟨x.loc i j,ν⟩)
    (fun i ν => ν = w (i*x.n)) x.n (x.n*(cell.blockCost+8)+6) 0 (by simp [w,wrote_zero]) ?_ ?_
    (first:= by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
    (hT:=by simp [time]; nlinarith [Nat.mul_le_mul_left (x.n*x.n) cost]))
  · rintro i z _ hi rfl
    refine Ends.forFrame (fun j ν => ν=w (i*x.n+j)) x.n rfl ?_ ?_ (hT:=by simp; ring_nf; omega)
    · rintro j _ hj rfl
      refine (one i hi j hj _ (fun b h => wrote_rest (by have := idx hi hj; rcases h with h|h <;> omega))).mono le_rfl ?_
      rintro _ rfl; exact ⟨rfl,wnext i hi j hj⟩
    · rintro _ rfl; exact ⟨x.n,_,rfl,by rw [Nat.succ_mul]⟩
  · rintro _ _ rfl
    exact ⟨fun i hi j hj => by dsimp only [w]; rw [Nat.add_assoc, wrote_done (idx hi hj)]; simp [f,Nat.mul_add_div_of_lt hj,Nat.mul_add_mod_of_lt hj], fun _ h => wrote_rest h⟩

end Grid
end Light.Sec3.Trace
