/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Trace.Sum
public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Residues
public import ThreeSumApsp.Spec.Sec3.Theorem17.Choice
public import ThreeSumApsp.Lang.Lib.PowTable

/-! Count modular triangles by summing ordinary scalar matrix contractions.
For residues `s,t` of the AC and BC edges the needed AB residue is unique.
The matrices are zero-padded to the next power of two. -/
@[expose] public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec Trace
variable {lim : Limits} {P : Program} {d : ℕ} {μ : Trace.Mem}
structure CpNums where
  (pDbl pResid pResidues pow mix kernel mask pair inner outer : ℕ)
structure CpCtx (P : Program) (ν : CpNums) : Prop where
  hDbl : P[ν.pDbl]? = some dblTableBody
  hResid : P[ν.pResid]? = some residBody
  hResidues : P[ν.pResidues]? = some (residuesBody ν.pResid)
  powers : P[ν.pow]? = some powTableBody
  mix : P[ν.mix]? = some (Grid.code mixCell)
  kernel : P[ν.kernel]? = some (Kernel.body ν.mix ν.kernel)
  mask : P[ν.mask]? = some (Grid.code maskCell)
  pair : P[ν.pair]? = some (Pair.body ν.mask ν.kernel)
  inner : P[ν.inner]? = some (Sum.body ν.pair)
  outer : P[ν.outer]? = some (Sum.body ν.inner)

namespace CountPrime
slots 0 Num ListAB ListBC ListAC Prime Len Level Rows Work Square ResAB ResBC ResAC Powers Scratch Result
end CountPrime
open CountPrime in
def countPrimeBody (ν : CpNums) : Stmt :=
  .set Square (v Num *' v Num) ;;
  .set ResAB (v Work +' v Len +' k 1) ;;
  .set ResBC (v ResAB +' v Square) ;; .set ResAC (v ResBC +' v Square) ;;
  .set Powers (v ResAC +' v Square) ;; .set Scratch (v Powers +' v Level) ;;
  .call ν.pDbl [v Work,v Prime,v Len] Result ;;
  .call ν.pResidues [v ListAB,v ResAB,v Square,v Work,v Len] Result ;;
  .call ν.pResidues [v ListBC,v ResBC,v Square,v Work,v Len] Result ;;
  .call ν.pResidues [v ListAC,v ResAC,v Square,v Work,v Len] Result ;;
  .call ν.pow [v Powers,v Level,k 2,k 0,k 0] Result ;;
  .call ν.outer [k 0,k 0,v Prime,v Num,v Level,v Rows,v Powers,v ResAC,v ResBC,v ResAB,v Scratch] Num

/-- A polynomial workspace and word envelope. Only the six matrix pages of the
trace and the tables in the prefix actually have to be initialized. -/
def countCells (n p len K : ℕ) :=
  len+1+3*(n*n)+K+6*(side K*side K)+64*(p+1)^2*(side K+1)^3+p+2

def countTime (n p len K : ℕ) := tDblTable len + 3*tResidues (n*n) len + powTableTime K +
  50000*(p+1)^2*7^K + 200

structure CountPrimePre (lim : Limits) (d : ℕ) (μ : ℕ → ℤ) (x : TriInst) (p len K w : ℕ) :
    Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  inst : x.Pre μ w
  p_pos : 1 ≤ p
  hK : K = Nat.clog 2 x.n
  hU : x.U < 2 ^ len
  cells : w + countCells x.n p len K ≤ lim.space
  wordDbl : ((p * 2 ^ (len + 1) : ℕ) : ℤ) ≤ lim.word
  depth : d + K + 5 ≤ lim.depth

/-- A list of residues is as long as the list of numbers. -/
@[simp] theorem length_residList (p : ℕ) (l : List ℤ) : (residList p l).length = l.length := by
  simp [residList]

/-- Residues modulo p are below p. -/
theorem lt_of_mem_residList {p } (hp : 1 ≤ p) {l } {x } (hx : x ∈ residList p l) :
    x < p := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact resid_lt (by omega) w

/-- **dblTable** as a procedure. -/
theorem dblTable_meets {q dst p len } (hP : P[q]? = some dblTableBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + (len + 1) ≤ lim.space)
    (hp : ((p * 2 ^ len : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [dst, p, len] μ (tDblTable len) fun _ μ' =>
      Seg μ' dst (dblList p len) ∧ SameOutside μ μ' dst (len + 1) :=
  Meets.of_body hP (dblTable_spec hw hdst hp)

/-- **residues** as a procedure. -/
theorem residues_meets {q pResid src dst m dbl p len U } {l }
    (hP : P[q]? = some (residuesBody pResid)) (hR : P[pResid]? = some residBody)
    (hd : d < lim.depth) (pre : ResiduesPre lim μ src dst m dbl p len U l) :
    Meets lim P q d [src, dst, m, dbl, len] μ (tResidues m len) fun _ μ' =>
      SegN μ' dst (residList p l) ∧ SameOutside μ μ' dst m :=
  Meets.of_body hP (residues_spec hR hd pre)

theorem CountPrimePre.residuesPre {μ μbase : Trace.Mem} {x : TriInst} {p len K w : ℕ} (pre : CountPrimePre lim d μbase x p len K w)
    {src dst } {l } (segDbl : Seg μ w (dblList p len)) (segSrc : Seg μ src l)
    (hlen : l.length = x.n * x.n) (hle : AbsLe l x.U) (hsrc : src + x.n * x.n ≤ w)
    (hdst : w + (len + 1) ≤ dst) (hend : dst + x.n * x.n ≤ lim.space) :
    ResiduesPre lim μ src dst (x.n * x.n) w p len x.U l := by
  exact ⟨pre.space_le, pre.p_pos, segDbl, segSrc, hlen, hle, pre.hU, by omega, by omega, hend,
    by omega, Or.inr (by omega), Or.inr (by omega), pre.wordDbl⟩

private theorem foldTime (p K : ℕ) : Sum.time p (Sum.time p (Pair.time K)) ≤ 50000*(p+1)^2*7^K := by
  have h := Kernel.cost_le K
  have sq : side K*side K=4^K := by unfold side; rw [← mul_pow]; rfl
  have n := Nat.le_mul_self (side K); rw [sq] at n
  have pos : 1≤7^K := Nat.one_le_pow _ _ (by decide)
  have hpair : Pair.time K+100 ≤ 50000*7^K := by
    unfold Pair.time Grid.time; nlinarith only [h,sq,n,pos,Nat.pow_le_pow_left (by decide : 4≤7) K]
  have aux (q : ℕ) : Sum.time p (Sum.time p q) ≤ (p+1)^2*(q+100) := by unfold Sum.time; nlinarith
  exact (aux _).trans (le_trans (Nat.mul_le_mul_left _ hpair) (by rw [Nat.mul_left_comm,Nat.mul_assoc]))

private theorem residMat {μ : Trace.Mem} {z n p : ℕ} {L : List ℤ} (h : SegN μ z (residList p L))
    (len : L.length=n*n) : At μ z n (mat n p L) := by
  intro i hi j hj
  rw [Nat.add_assoc,h.read (i:=i*n+j) (by simpa [len] using idx hi hj),getD_residList]; rfl

open CountPrime in
theorem countPrime_meets {q p len K w} {x : TriInst} {μ : Trace.Mem} {ν : CpNums}
    (hP : P[q]? = some (countPrimeBody ν)) (ctx : CpCtx P ν) (pre : CountPrimePre lim d μ x p len K w) :
    Meets lim P q d [x.n,x.ab,x.bc,x.ac,p,len,K,(2^K:ℕ),w] μ (countTime x.n p len K) fun r τ =>
      r = countOf x.n p x.AB x.BC x.AC ∧ SameOutside μ τ w (countCells x.n p len K) := by
  let rab := w+len+1; let size := x.n*x.n; let rbc := rab+size; let rac := rbc+size
  let powers := rac+size; let fr := powers+K; let top := w+countCells x.n p len K
  let y : Batch := ⟨p,x.n,K,powers,fr,⟨rac,mat x.n p x.AC⟩,⟨rbc,mat x.n p x.BC⟩,⟨rab,mat x.n p x.AB⟩⟩
  have layout : rab=w+len+1 ∧ rbc=rab+size ∧ rac=rbc+size ∧ powers=rac+size ∧ fr=powers+K ∧
      top=fr+6*(side K*side K)+64*(p+1)^2*(side K+1)^3+p+2 := by
    dsimp [rab,rbc,rac,powers,fr,top,countCells,size]; omega
  have hw := pre.space_le; have sp : top≤lim.space := pre.cells
  have dep := pre.depth; have pp := pre.p_pos; have := pre.inst.n_pos
  have pw : ∀ k≤K, ((2^k:ℕ):ℤ) ≤ lim.word := by
    intro k hk; have h : 2^k ≤ side K := Nat.pow_le_pow_right (by decide) hk
    have := Nat.le_mul_self (side K); omega
  have lN : (2^K:ℕ) = side K := rfl
  have zero := pw 0 (by omega)
  have hsize : size=x.n*x.n := rfl
  have htop : top=w+countCells x.n p len K := rfl
  have hleft := foldTime p K
  light_facts pre.inst
  apply Meets.of_body hP; unfold countPrimeBody countTime
  light_set (size:ℕ) using size
  light_set rab
  light_set rbc
  light_set rac
  light_set powers
  light_set fr
  light_call (dblTable_meets (dst:=w) (p:=p) (len:=len) ctx.hDbl hw (by omega) (pre.wordDbl.trans' (by exact_mod_cast Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.le_succ len))))) with _ μ₁ ⟨dbl,rest₁⟩
  light_call (residues_meets ctx.hResidues ctx.hResid (by omega) (pre.residuesPre (dst:=rab) dbl pre.inst.segAB.keep pre.inst.lenAB pre.inst.leAB pre.inst.belowAB (by omega) (by omega))) using size with _ μ₂ ⟨ab,rest₂⟩
  light_call (residues_meets ctx.hResidues ctx.hResid (by omega) (pre.residuesPre (dst:=rbc) dbl.keep pre.inst.segBC.keep pre.inst.lenBC pre.inst.leBC pre.inst.belowBC (by omega) (by omega))) using size with _ μ₃ ⟨bc,rest₃⟩
  light_call (residues_meets ctx.hResidues ctx.hResid (by omega) (pre.residuesPre (dst:=rac) dbl.keep pre.inst.segAC.keep pre.inst.lenAC pre.inst.leAC pre.inst.belowAC (by omega) (by omega))) using size with _ μ₄ ⟨ac,rest₄⟩
  light_call (Meets.of_body (Q:=fun _ τ => Seg τ powers (powList 2 K) ∧ SameOutside μ₄ τ powers K) ctx.powers
    (powTable_ends 0 0 [] hw (by omega) pw)) with _ μ₅ ⟨tab,rest₅⟩
  have ready : Ready y μ₅ lim top := by
    refine ⟨fun z hz => ?_,fun k hk => ?_,by change powers+K≤fr; omega,by change fr+6*(side K*side K)≤top; omega,sp,hw,?_⟩
    · simp at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨residMat ac.keep pre.inst.lenAC,by change rac+size≤fr; omega⟩
      · exact ⟨residMat bc.keep pre.inst.lenBC,by change rbc+size≤fr; omega⟩
      · exact ⟨residMat ab.keep pre.inst.lenAB,by change rab+size≤fr; omega⟩
    · exact (tab _ (by simpa using hk)).trans (by simp [side])
    · change ((64*(p+1)^2*(side K+1)^3:ℕ):ℤ) ≤ _; omega
  light_call (Sum.all ctx.mix ctx.kernel ctx.mask ctx.pair ctx.inner ctx.outer ready (by change d+1+K+4 ≤ lim.depth; omega) pp) using y,lN with _ τ ⟨rfl,same⟩
  refine ⟨?_, ?_⟩
  · exact total pp (by change x.n ≤ 2^K; rw [pre.hK]; exact Nat.le_pow_clog (by decide) _) _ _ _
  · have r₀ : SameOutside μ μ₅ w (countCells x.n p len K) := by
      change SameOn (Outside w _) μ μ₅; apply SameOn.trans (rest₁.mono le_rfl (by omega)); apply SameOn.trans (rest₂.mono (by omega) (by omega)); apply SameOn.trans (rest₃.mono (by omega) (by omega)); exact (rest₄.mono (by omega) (by omega)).trans (rest₅.mono (by omega) (by omega))
    exact r₀.trans (SameOn.mono same fun i hi => by change i < fr ∨ top ≤ i; omega)

theorem countCells_mono {p q : ℕ} (hpq : p≤q) (n len K : ℕ) : countCells n p len K ≤ countCells n q len K := by unfold countCells; gcongr

theorem countTime_mono {p q : ℕ} (hpq : p≤q) (n len K : ℕ) : countTime n p len K ≤ countTime n q len K := by unfold countTime; gcongr
end Light.Sec3
