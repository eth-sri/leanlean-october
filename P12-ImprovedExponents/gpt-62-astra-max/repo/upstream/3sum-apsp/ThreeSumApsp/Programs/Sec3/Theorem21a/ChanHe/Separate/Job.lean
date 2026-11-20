/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Separate.Pick

@[expose] public section
namespace Light.Sec3.ChanHe.Separate
open ThreeSumApsp ThreeSumApsp.ChanHe Finset

/-- The prime list starts at `base`, followed by the count table and the three
output slices. The bitmap starts in node scratch space and is no longer live
when the node procedure is called. -/
structure Job where
  (n V src base : ℕ)
  x : ℕ → ℤ
namespace Job
variable (w : Job)
abbrev B := bound w.n
abbrev f := fuel w.n
abbrev m := mPar w.n w.V
abbrev np := #(Nat.primesLE w.m)
abbrev cnt := w.base+w.m
abbrev out := w.cnt+w.m*w.m
abbrev top := w.out+3*w.n
abbrev bias := w.top+w.V
abbrev env : Env := ⟨w.top,w.n,w.V,w.m,w.np,w.base,w.cnt⟩
abbrev view (dst q r : ℕ) : View := ⟨w.n,w.src,q,r,dst,w.bias,w.x⟩
abbrev slot (dst q r : ℕ) : Slot :=
  let s := slice w.x w.n q r w.n
  ⟨dst,#s,s⟩
abbrev node (q a b c : ℕ) : NodeArgs := ⟨w.env,w.slot w.out q a,
  w.slot (w.out+w.n) q b,w.slot (w.out+w.n+w.n) q c⟩

/-- The constant suffix is passed by value, both through the four searches and
on to the recursive solver. No memory-resident directory is needed. -/
abbrev tail : List ℤ := [w.n,w.src,w.V,w.m,Lam w.V,w.np,w.base,w.cnt,w.f,w.out,w.top,w.bias]
abbrev args (a b c d : ℕ) : List ℤ := [(w.B:ℤ),a,b,c,d] ++ w.tail
end Job

namespace Param
slots 0 Bound GapA GapB GapC GapD Nums Input Mag PrimeMax Digits NumPrimes Primes Counts Fuel Out Free Bias
abbrev tail : List Expr := [v Nums,v Input,v Mag,v PrimeMax,v Digits,v NumPrimes,v Primes,v Counts,v Fuel,v Out,v Free,v Bias]
end Param
end Light.Sec3.ChanHe.Separate
