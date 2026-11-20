/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module
public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Separate.Leaf
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Parameters

@[expose] public section
namespace Light.Sec3.ChanHe.Separate.Core
open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

slots 0 N V Src Base Void Digits PrimeMax Levels Log W Choices Count Out Top Bias NumPrimes

def body (params log primes fill any : ℕ) : Stmt :=
  .call params [v N,v V,v Base] Void ;;
  .set Digits (M (v Base)) ;; .set PrimeMax (M (v Base +' k 1)) ;;
  .set Levels (M (v Base +' k 2)) ;;
  .call log [k 2 *' (v N *' v N *' v N)] Log ;;
  .set W (k 5 *' (v Log +' k 1) +' k 1) ;; .set Choices (v W *' (k 2 *' v W +' k 4)) ;;
  .set Count (v Base +' v PrimeMax) ;; .set Out (v Count +' v PrimeMax *' v PrimeMax) ;;
  .set Top (v Out +' k 3 *' v N) ;; .set Bias (v Top +' v V) ;;
  .call primes [v PrimeMax,v Base,v Count] NumPrimes ;;
  .call fill [v Count,v PrimeMax *' v PrimeMax,k 0] Void ;;
  .call any [v Choices,k 0,k 0,k 0,k 0,v N,v Src,v V,v PrimeMax,v Digits,v NumPrimes,v Base,
    v Count,v Levels,v Out,v Top,v Bias] 0

abbrev four (B t : ℕ) := moreTime B (moreTime B (moreTime B (moreTime B t)))

theorem budget (T : ℕ → ℕ → ℕ) (w : Job) : tParams w.n w.V + tLog2 (2*w.n^3) + tPrimes w.m +
    fillTime (w.m*w.m) + four w.B (Leaf.time T w) + 240 ≤ coreTime T w.n w.V := by
  unfold coreTime coreOwn tSetup coreCalls leafOwn Leaf.time
  rw [tNodes_eq]
  simp only [callsB,inputsB,four,moreTime,fillTime,Job.B,Job.f,Job.m,Job.np]
  ring_nf; omega

structure Link (lim : Limits) (P : Program) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need)
    (params log primes fill pick nodes leaf bottom : ℕ) : Prop where
  par : ParamsSpec lim P params
  lg : Log2Spec lim P log
  sieve : PrimesSpec lim P primes
  zeros : P[fill]?=some fillBody
  select : P[pick]?=some pickBody
  tree : NodesSpec lim P nodes T r
  once : P[leaf]?=some (Leaf.body pick nodes)
  more : ∀ i<4, P[bottom+i]?=some (anyBody (if i=0 then leaf else bottom+(i-1)))

variable {lim : Limits} {P : Program} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
  {μ : ℕ → ℤ} {d params log primes fill pick nodes leaf bottom p : ℕ}
  (K : Link lim P T r params log primes fill pick nodes leaf bottom)
include K

private theorem search {w : Job} (H : w.Fits lim r) (ν : ℕ → ℤ) (pr : w.Ready μ ν)
    (hd : d+(w.need r).depth+5 ≤ lim.depth) : Meets lim P (bottom+3) d (w.args 0 0 0 0) ν
      (four w.B (Leaf.time T w)) fun z τ => z = flag (ThreeSum (fun i : Fin w.n => w.x i)) ∧ Kept μ τ w.base := by
  have pos : 0<w.B := by unfold Job.B bound width; positivity
  have h := H.index; have hw := H.space
  have hb : (w.B:ℤ) ≤ lim.word := (show (w.B:ℤ) ≤ lim.space by exact_mod_cast (show w.B≤lim.space by omega)).trans hw
  have h₁ : 1 ≤ lim.word := by omega
  have k := Leaf.spec (μ:=μ) K.once K.select K.tree H
  have k0 := probe_any (K.more 0 (by decide)) k hb h₁
  have k1 := probe_any (K.more 1 (by decide)) k0 hb h₁
  have k2 := probe_any (K.more 2 (by decide)) k1 hb h₁
  have k3 := probe_any (K.more 3 (by decide)) k2 hb h₁
  exact (k3 0 pos 0 pos 0 pos 0 pos ν pr d (by omega)).mono le_rfl fun _ _ h =>
    ⟨h.1.trans (flag_congr (correct w.x w.n).symm),h.2.kept⟩

private theorem solve (w : Job) (input : ∀ i<w.n, μ (w.src+i)=w.x i)
    (mag : ∀ i<w.n, |w.x i| ≤ w.V) (srcEnd : w.src+w.n≤w.base) (hn : 1≤w.n) (hv : 1≤w.V)
    (hok : (coreNeed r w.n w.V).Ok lim w.base d) (hp : P[p]?=some (body params log primes fill (bottom+3))) :
    Meets lim P p d [w.n,w.V,w.src,w.base] μ (coreTime T w.n w.V) fun z τ =>
      z = flag (ThreeSum (fun i : Fin w.n => w.x i)) ∧ Kept μ τ w.base := by
  have hw := hok.space
  have room := hok.cells
  change w.base+((w.need r).cells+ (8*(w.m+1)^2+9*w.V+8*w.n+10*w.n^3+2*w.n^2+
    4*w.B+w.n*(4*w.B)+500)) ≤ lim.space at room
  have sq : (w.m+1)^2=w.m*w.m+2*w.m+1 := by ring
  have count : w.base+w.m=w.cnt := rfl
  have out : w.cnt+w.m*w.m=w.out := rfl
  have top : w.out+3*w.n=w.top := rfl
  have bias : w.top+w.V=w.bias := rfl
  have H : w.Fits lim r := ⟨srcEnd,hn,hv,mag,by omega,by omega,by omega,hok.word,hw⟩
  have hd : d+(w.need r).depth+10 ≤ lim.depth := by simpa only [coreNeed,Job.need,Nat.add_assoc] using hok.depth
  have hword (a : ℕ) (h : a ≤ lim.space) : (a:ℤ) ≤ lim.word := (by exact_mod_cast h : (a:ℤ) ≤ lim.space) |>.trans hw
  have ok : (primesNeed w.m).Ok lim w.cnt (d+1) := ⟨hword _ (by change 4*w.m+16≤_; omega),by change w.cnt+(w.m+1)≤_; omega,hw,by change d+1+0≤_; omega⟩
  have cost := budget T w
  have c₃ : (w.n:ℤ)*w.n*w.n=(w.n:ℤ)^3 := by ring
  have c₂ : (w.n:ℤ)*w.n=(w.n:ℤ)^2 := by ring
  have z₂ := hword (w.n^2) (by omega); have z₃ := hword (2*w.n^3) (by omega)
  have z₀ : 0 ≤ (w.n:ℤ)^3 := by positivity
  have z₁ : 0 ≤ (w.n:ℤ)^2 := by positivity
  push_cast at z₂ z₃
  refine Meets.of_body hp ?_
  light_call (K.par (d+1) w.n w.V w.base μ (by omega) hw (hword _ (by change 8*(w.m+1)^2+8*w.V+4*w.n+64≤_; omega))
    (by omega)) with _ μ₁ ⟨par,same₁⟩
  simp only [seg_cons,add_assoc,Nat.reduceAdd] at par
  obtain ⟨l,m,f,-⟩ := par
  light_set (Lam w.V) using l
  light_set w.m using m
  have adr : ((w.base:ℤ)+2).toNat=w.base+2 := by omega
  light_set w.f using adr,f
  have z₄ := hword (8*w.n^3+4) (by omega); push_cast at z₄
  have cube : (w.n:ℤ)^2*w.n=(w.n:ℤ)^3 := by ring
  light_call (K.lg (d+1) (2*w.n^3) μ₁ (by push_cast; omega)) using c₃,c₂,cube with _ _ ⟨rfl,rfl⟩
  have ew : width w.n=5*(Nat.log 2 (2*w.n^3)+1)+1 := rfl
  have eb : w.B=width w.n*(2*width w.n+4) := rfl
  have wle : width w.n ≤ w.B := Nat.le_mul_of_pos_right _ (by omega)
  have pw : (width w.n:ℤ) * (2*width w.n+4) = (w.B:ℤ) := by exact_mod_cast eb.symm
  have pre : 2*width w.n+4 ≤ w.B := by apply Nat.le_mul_of_pos_left; unfold width; omega
  zify at ew pre
  light_set (width w.n : ℕ)
  light_set (w.B : ℕ)
  light_set (w.cnt : ℕ)
  light_set (w.out : ℕ)
  light_set (w.top : ℕ)
  light_set (w.bias : ℕ)
  light_call (K.sieve (d+1) w.cnt w.m w.base _ count.le ok) with _ μ₂ ⟨rfl,pr,same₂⟩
  light_call (fill_meets (μ:=μ₂) (dst:=w.cnt) (n:=w.m*w.m) (x:=0) K.zeros hw (by omega)) with _ μ₃ ⟨zero,same₃⟩
  have kept : Kept μ μ₃ w.base := same₁.then (same₂.then same₃ fun _ h => by omega) fun _ h => by omega
  have ready : w.Ready μ μ₃ := ⟨fun i hi => (kept _ (by omega)).trans (input _ hi),
    ⟨rfl,pr.of_sameOutside same₃ (.inl (by simpa using Nat.add_le_add_left (Nat.card_primesLE_le w.m) w.base))⟩,
    fun i hi => by rw [zero i (by simpa using hi)]; simp,kept⟩
  light_call (search K H μ₃ ready (d:=d+1) (by omega)) with _ τ h
  exact h

theorem spec (hp : P[p]?=some (body params log primes fill (bottom+3))) : CoreSpec lim P p T r := by
  intro d n U src base X μ len hX seg below hn hu h
  let w : Job := ⟨n,2*U,src,base,fun i => X.getD i 0⟩
  exact solve K w (fun i hi => seg.getD (len ▸ hi) 0) (fun i _ =>
    (hX.abs_getD_le (by positivity) i).trans (by change (U:ℤ) ≤ ((2*U:ℕ):ℤ); omega)) below hn (by change 1≤2*U; omega) h hp
end Light.Sec3.ChanHe.Separate.Core
