/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Trace.Table

@[expose] public section
namespace Light.Sec3.Trace
open Grid

def origin (q : Fin 4) (n : ℕ) := q.val/2*n*(n+n) + q.val%2*n

theorem address (q : Fin 4) (src n i j : ℕ) : src+origin q n + i*(n+n)+j =
    src+(i+q.val/2*n)*(n+n)+(j+q.val%2*n) := by unfold origin; ring

def mixCell := save (M (v Src₁ +' v I *' v Stride +' v J) +' v Factor *' M (v Src₂ +' v I *' v Stride +' v J))

abbrev Mix.args (m : Mix) (n dst src : ℕ) : Grid.Args :=
  ⟨n,dst,src+origin m.a n,src+origin m.b n,n+n,m.s⟩

variable {lim : Limits} {P : Program} {d p src dst n h : ℕ} {μ : Mem}

theorem mix_spec (m : Mix) (hp : P[p]? = some (code mixCell)) {A : Mat} (hA : At μ src (n+n) A)
    (hB : Bdd (n+n) A h) (hs : |m.s| ≤ 1) (hw : lim.space ≤ lim.word) (bound : (2*h:ℕ) ≤ lim.word)
    (below : src+(n+n)*(n+n) ≤ dst) (room : dst+n*n ≤ lim.space) :
    Meets lim P p d (m.args n dst src).regs μ (time n) fun _ ν => At ν dst n (m.mat n A) ∧ SameOutside μ ν dst (n*n) := by
  refine tabulate (x:=m.args n dst src) hp hw room (by decide) ?_
  intro i hi j hj ν same
  change i<n at hi; change j<n at hj; change SameOutside μ ν dst (n*n) at same
  have z := idx hi hj
  have read (q : Fin 4) : ν (src+origin q n + i*(n+n)+j) = quad n q A i j := by
    rw [address, same _ (Or.inl (by have := idx (offs hi q).1 (offs hj q).2; omega))]
    exact hA _ (offs hi q).1 _ (offs hj q).2
  have fit (q : Fin 4) : src+origin q n + i*(n+n)+j < dst := by
    rw [address]; have := idx (offs hi q).1 (offs hj q).2; omega
  have bnd (q : Fin 4) : |quad n q A i j| ≤ h := hB _ (offs hi q).1 _ (offs hj q).2
  have b₁ := abs_le.mp (bnd m.a)
  have b₂ := mul_le_mul hs (bnd m.b) (abs_nonneg _) (by norm_num)
  rw [← abs_mul,one_mul,abs_le] at b₂
  have f₁ := fit m.a; have f₂ := fit m.b
  refine Ends.storeTo (dst+i*n+j) (m.mat n A i j) rfl ?_ le_rfl
  dsimp only [mixCell, save, Mix.mat, Mix.args, Args.loc, Args.regs]; have rr := read m.a; have ss := read m.b
  generalize origin m.a n = oa at *; generalize origin m.b n = ob at *
  generalize n+n = stride at rr ss f₁ f₂ ⊢
  have ad (q : ℕ) : ((src:ℤ)+q+i*(stride:ℤ)+j).toNat = src+q+i*stride+j := by exact_mod_cast rfl
  light_side [ad,rr,ss]
end Light.Sec3.Trace
