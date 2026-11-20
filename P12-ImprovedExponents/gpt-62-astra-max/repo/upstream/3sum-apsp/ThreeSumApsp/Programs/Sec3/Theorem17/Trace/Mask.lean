/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Trace.Measure
public import ThreeSumApsp.Programs.Sec3.Theorem17.Trace.Table

@[expose] public section
namespace Light.Sec3.Trace
open Grid

def maskCell : Stmt := .ite (v I <' v Stride) (.ite (v J <' v Stride)
  (.ite (M (v Src₁ +' v I *' v Stride +' v J) =' v Factor) (save (k 1)) (save (k 0))) (save (k 0))) (save (k 0))

abbrev maskArgs (N dst src n : ℕ) (r : ℤ) : Args := ⟨N,dst,src,0,n,r⟩

theorem mask_spec {lim : Limits} {P : Program} {d p n N src dst : ℕ} {μ : Mem} {A : Mat}
    (hp : P[p]?=some (code maskCell)) (target : ℤ) (hA : At μ src n A) (hw : lim.space ≤ lim.word)
    (word : 1≤lim.word) (below : src+n*n≤dst) (room : dst+N*N≤lim.space) :
    Meets lim P p d (maskArgs N dst src n target).regs μ (time N) fun _ ν =>
      At ν dst N (mark n A target) ∧ SameOutside μ ν dst (N*N) := by
  refine tabulate hp hw room (by decide) ?_
  intro i hi j hj ν same
  change i<N at hi; change j<N at hj; change SameOutside μ ν dst (N*N) at same
  have := idx hi hj
  have adr (o n : ℕ) : ((o:ℤ)+i*n+j).toNat=o+i*n+j := by exact_mod_cast rfl
  apply Ends.block (hT:=le_rfl)
  by_cases a : i<n <;> by_cases b : j<n
  · have := idx a b; have read := (same _ (Or.inl (show src+i*n+j<dst by omega))).trans (hA _ a _ b)
    by_cases e : A i j=target <;> simp [Stmt.Runs,maskCell,save,mark,adr,read,a,b,e,Limits.Addr,abs_le] <;> try omega
  all_goals simp [Stmt.Runs,maskCell,save,mark,adr,a,b,Limits.Addr,abs_le] <;> try omega
end Light.Sec3.Trace
