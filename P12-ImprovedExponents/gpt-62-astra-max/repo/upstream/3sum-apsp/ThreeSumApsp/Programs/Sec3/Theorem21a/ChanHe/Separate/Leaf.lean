/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Separate.Search
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Separate.Ready

@[expose] public section
namespace Light.Sec3.ChanHe.Separate
open ThreeSumApsp ThreeSumApsp.ChanHe Finset
namespace Leaf
open Param
slots 17 Second Third Modulus LenA LenB LenC
abbrev middle := v Out +' v Nums
abbrev lastSet := middle +' v Nums
abbrev pickArgs (res dst : Expr) := [v Nums,v Input,v Modulus,res,dst,v Bias]

def body (pick nodes : ℕ) : Stmt :=
  .set Second (v GapA +' v GapB +' k 1) ;;
  .set Third (v Second +' v GapC +' k 1) ;;
  .set Modulus (v Third +' v GapD +' k 1) ;;
  .call pick (pickArgs (v GapA) (v Out)) LenA ;;
  .call pick (pickArgs (v Second) middle) LenB ;;
  .call pick (pickArgs (v Third) lastSet) LenC ;;
  .call nodes [v Fuel,v Out,v LenA,middle,v LenB,lastSet,v LenC,v Free,v Mag,v PrimeMax,v Digits,
    v NumPrimes,v Primes,v Counts] 0

variable {lim : Limits} {P : Program} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {w : Job}
  {p nproc pick d : ℕ} {μ ν : ℕ → ℤ}

def time (T : ℕ → ℕ → ℕ) (w : Job) :=
  3*Separate.tPick w.n+180+tNodes T w.n w.V w.m w.np (visits w.f)

private theorem chosen (hp : P[pick]?=some pickBody) (H : w.Fits lim r) (R : w.Ready μ ν)
    (dst q z : ℕ) (left : w.out ≤ dst) (right : dst+w.n ≤ w.top) (hz : z≤q) (hq : q≤4*w.B) :
    Meets lim P pick d [w.n,w.src,q,z,dst,w.bias] ν (Separate.tPick w.n) fun len τ =>
      len = ((w.slot dst q z).len:ℕ) ∧ SetAt τ dst (w.slot dst q z).len (w.slot dst q z).set ∧
      Kept ν τ dst ∧ w.Ready μ τ :=
  (pick_spec hp (H.view left right hz hq) R.input).mono le_rfl fun _ _ h =>
    ⟨h.1,h.2.1,h.2.2,R.keep H (fun b hb => h.2.2 b (hb.trans_le left))⟩

set_option maxHeartbeats 1600000 in
theorem spec (hp : P[p]?=some (body pick nproc)) (hpick : P[pick]?=some pickBody)
    (hN : NodesSpec lim P nproc T r) (H : w.Fits lim r) :
    Probe lim P p w ((w.need r).depth+1) (time T w) (w.Ready μ) (hit w.x w.n) := by
  intro a ha b hb c hc e he ν R d hd
  apply Meets.of_body hp
  let s := a+b+1; let t := s+c+1; let q := t+e+1
  have hq : q≤4*w.B := by dsimp [q,t,s]; omega
  have h := H.index; have hw := H.space; have hm := H.bitmap
  have top : w.out+3*w.n=w.top := rfl
  have address : (w.out:ℤ) = (w.base:ℤ)+w.m+w.m*w.m := by simp [Job.out, Job.cnt]
  have width : (q:ℤ) ≤ lim.word := le_trans (by exact_mod_cast (show q≤lim.space by omega)) hw
  unfold time body Job.args Job.tail
  light_set (s:ℕ) using s
  light_set (t:ℕ) using t
  light_set (q:ℕ) using q
  light_call (chosen hpick H R w.out q a le_rfl (by omega) (by dsimp [q,t,s]; omega) hq)
    with _ ν₁ ⟨rfl,setA,_,R₁⟩
  light_call (chosen hpick H R₁ (w.out+w.n) q s (by omega) (by omega) (by dsimp [q,t]; omega) hq)
    with _ ν₂ ⟨rfl,setB,same₂,R₂⟩
  light_call (chosen hpick H R₂ (w.out+w.n+w.n) q t (by omega) (by omega) (by dsimp [q]; omega) hq)
    with _ ν₃ ⟨rfl,setC,same₃,R₃⟩
  have sz {dst res : ℕ} : (w.slot dst q res).len ≤ w.n :=
    card_image_le.trans ((card_filter_le ..).trans (card_range _).le)
  have pre := R₃.nodePre H (q:=q) (a:=a) (b:=s) (c:=t)
    ((setA.kept (Nat.add_le_add_left sz _) same₂).kept (by have := @sz w.out a; omega) same₃)
    (setB.kept (Nat.add_le_add_left sz _) same₃) setC (d:=d+1) (by omega)
  have eqn := Job.node_iff pre H.npos
  light_call (hN w.f (w.node q a s t) (Lam w.V) ν₃ (d+1) pre) with _ τ ⟨rfl,same⟩
  exact ⟨flag_congr eqn.symm,R₃.keep H (fun i hi => same i (lt_of_lt_of_le hi (show w.out ≤ w.top by omega)))⟩
end Leaf
end Light.Sec3.ChanHe.Separate
