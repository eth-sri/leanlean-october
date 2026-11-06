/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec3.Theorem17.Host.InstanceFacts
import ThreeSumApsp.Programs.Sec3.Theorem17.Instances.WriteMatrices

/-!
# The host of Theorem 17: the loop over the instances

Proof of Theorem 17.  After the prime has been chosen and the query pairs have been sorted into
classes and cut into chunks, the host runs through all instances: instance number t belongs to the
piece number t / chunkCount of the third part of the vertices and to the chunk number t % chunkCount
of the table of chunks.  For each instance it writes the two biadjacency matrices, calls the solver
of Lop-AE-SparseTri on the chunk (a segment of the sorted arrays of query pairs, so nothing is
copied), and scans the piece for every accepted query pair, as long as no zero triangle has been
found.

The solver is arbitrary.  The facts about the data that the loop relies on are collected in the
structure `HostOk`.

* What the four calls assume is proved without any program: `HostSetting.writeX`,
  `HostSetting.writeY`, `HostSetting.solver`, `HostSetting.weights`, `HostSetting.answers`.
* The program has one lemma for each part of a round: `hostParams_spec` (the parameters of the
  instance), `hostCalls_spec` (the four calls) and `hostNext_spec` (the counters).
  `hostRound_spec` puts them together, and `hostLoop_spec` is the loop: hostLoop returns 1 if a scan
  has found a zero triangle (`X.found X.m`) and 0 if not, changes no cell below x, and takes at most
  `tHostLoop` steps, the sum over the instances of the times of the four calls.
-/


namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-! ## The procedure -/

namespace HostLocal

/- The number n of vertices of a part. -/
slots Size
/- The inner dimension D. -/
slots 1 ParD
/- The prime p. -/
slots 2 ThePrime
/- The number q of vertices of a piece. -/
slots 3 PieceLen
/- The number chunkCount of chunks. -/
slots 4 NumChunks
/- The number m of instances. -/
slots 5 NumInst
/- The weights w(a,b). -/
slots 6 AdrAB
/- The weights w(b,c). -/
slots 7 AdrBC
/- The weights w(a,c). -/
slots 8 AdrAC
/- The residues of the weights w(a,c). -/
slots 9 ResAC
/- The residues of the weights w(b,c). -/
slots 10 ResBC
/- The rows of the sorted query pairs. -/
slots 11 Rows
/- The columns of the sorted query pairs. -/
slots 12 Cols
/- The classes of the chunks. -/
slots 13 TabR
/- The first places of the chunks. -/
slots 14 TabL
/- The numbers of query pairs of the chunks. -/
slots 15 TabW
/- The matrix X. -/
slots 16 MatX
/- The matrix Y. -/
slots 17 MatY
/- The answers of the solver. -/
slots 18 AdrOut
/- The free pointer. -/
slots 19 SolverFree
/- The number t of the instance. -/
slots 20 Inst
/- The number ch of its chunk. -/
slots 21 ChunkNo
/- The first vertex c0 of its piece. -/
slots 22 PieceStart
/- 1 if a zero triangle has been found. -/
slots 23 Found
/- The number len of vertices of the piece. -/
slots 24 Len
/- The class rho of the chunk. -/
slots 25 Residue
/- The first place lo of the chunk. -/
slots 26 Start
/- The number w of query pairs of the chunk. -/
slots 27 NumPairs
/- Results that are not used. -/
slots 28 Unused

end HostLocal

open HostLocal

/-- The four calls for one instance: the two matrices, the solver, the scans. -/
def hostCalls (pS pWriteX pWriteY pScanPairs : ℕ) : Stmt :=
  .call pWriteX [v MatX, v ResAC, v Size, v ParD, v ThePrime, v PieceStart, v Len, v Residue]
    Unused ;;
  .call pWriteY [v MatY, v ResBC, v Size, v ParD, v ThePrime, v PieceStart, v Len] Unused ;;
  .call pS [v Size, v ParD, v NumPairs, k 1, v MatX, v MatY, v Rows +' v Start, v Cols +' v Start,
    v AdrOut, v SolverFree] Unused ;;
  .call pScanPairs [v AdrOut, v Rows +' v Start, v Cols +' v Start, v NumPairs, v Found, v AdrAB,
    v AdrBC, v AdrAC, v Size, v PieceStart, v Len] Found

/-- The numbers of the next instance, of its chunk, and the first vertex of its piece. -/
def hostNext : Stmt :=
  .set ChunkNo (v ChunkNo +' k 1) ;;
  .ite (v ChunkNo =' v NumChunks)
    (.set ChunkNo (k 0) ;; .set PieceStart (v PieceStart +' v PieceLen)) .skip ;;
  .set Inst (v Inst +' k 1)

/-- The parameters of the instance: the number of vertices of its piece, and the class, the first
place and the number of query pairs of its chunk. -/
def hostParams : Stmt :=
  .set Len (v PieceLen) ;;
  .ite (v Size -' v PieceStart <' v PieceLen) (.set Len (v Size -' v PieceStart)) .skip ;;
  .set Residue (M (v TabR +' v ChunkNo)) ;;
  .set Start (M (v TabL +' v ChunkNo)) ;;
  .set NumPairs (M (v TabW +' v ChunkNo))

/-- One round of hostLoop. -/
def hostRound (pS pWriteX pWriteY pScanPairs : ℕ) : Stmt :=
  hostParams ;;
  hostCalls pS pWriteX pWriteY pScanPairs ;;
  hostNext

/-- hostLoop(n, D, p, q, chunkCount, m, ab, bc, ac, rac, rbc, qi, qj, cr, cl, cw, x, y, out, fr). -/
def hostLoopBody (pS pWriteX pWriteY pScanPairs : ℕ) : Stmt :=
  .set Inst (k 0) ;; .set ChunkNo (k 0) ;; .set PieceStart (k 0) ;; .set Found (k 0) ;;
  .while (v Inst <' v NumInst) (hostRound pS pWriteX pWriteY pScanPairs) ;;
  .set 0 (v Found)

/-- The time for writing the two matrices of an instance whose piece has len vertices, with the
calls and the bookkeeping of a round. -/
def tWrites (n D len : ℕ) : ℕ := 101 + tWriteX n D len + tWriteY n D len

/-- The number of steps of hostLoop, if the solver takes Tn. -/
def tHostLoop (Tn : List ℕ → ℕ) (X : HostData) : ℕ :=
  (∑ t ∈ Finset.range X.m, (tWrites X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
    tScanPairs (X.w t) (X.len t) (X.execs t))) + 14

/-! ## What the loop relies on -/

/-- The facts about the data that the loop relies on; U is a bound on the weights. -/
structure HostOk (X : HostData) (U : ℕ) : Prop where
  valid : X.Valid
  leAB : AbsLe X.AB U
  leBC : AbsLe X.BC U
  leAC : AbsLe X.AC U

/-- The addresses of the arrays. -/
structure HostAddr : Type where
  (ab bc ac rac rbc qi qj cr cl cw x y out fr : ℕ)

/-- What the memory holds: the weights, the residues of w(a,c) and w(b,c), the sorted query pairs,
and the three components of the table of chunks. -/
structure HostMem (X : HostData) (A : HostAddr) (μ : ℕ → ℤ) : Prop where
  segAB : Seg μ A.ab X.AB
  segBC : Seg μ A.bc X.BC
  segAC : Seg μ A.ac X.AC
  segRAC : SegN μ A.rac X.RAC
  segRBC : SegN μ A.rbc X.RBC
  segQI : SegN μ A.qi X.QI
  segQJ : SegN μ A.qj X.QJ
  segCR : SegN μ A.cr (X.CT.map fun c => c.residue)
  segCL : SegN μ A.cl (X.CT.map fun c => c.start)
  segCW : SegN μ A.cw (X.CT.map fun c => c.len)

/-- Where the arrays lie: everything that is read lies below x; then come the two matrices, the
answers, and the free pointer. -/
structure HostLay (X : HostData) (A : HostAddr) : Prop where
  bAB : A.ab + X.n * X.n ≤ A.x
  bBC : A.bc + X.n * X.n ≤ A.x
  bAC : A.ac + X.n * X.n ≤ A.x
  bRAC : A.rac + X.n * X.n ≤ A.x
  bRBC : A.rbc + X.n * X.n ≤ A.x
  bQI : A.qi + X.n * X.n ≤ A.x
  bQJ : A.qj + X.n * X.n ≤ A.x
  bCR : A.cr + X.chunkCount ≤ A.x
  bCL : A.cl + X.chunkCount ≤ A.x
  bCW : A.cw + X.chunkCount ≤ A.x
  xy : A.x + X.n * X.D ≤ A.y
  yo : A.y + X.D * X.n ≤ A.out
  ofr : ∀ t < X.m, A.out + X.w t ≤ A.fr

/-- What the limits have to allow for; need is the need of the solver. -/
structure HostLim (lim : Limits) (d : ℕ) (X : HostData) (U : ℕ) (A : HostAddr)
    (need : List ℕ → Need) : Prop where
  space : (lim.space : ℤ) ≤ lim.word
  fr : A.fr < lim.space
  prime : 2 * X.p < lim.space
  count : (X.m : ℤ) ≤ lim.word
  step : ((X.n + X.q : ℕ) : ℤ) ≤ lim.word
  weights : ((3 * U + 1 : ℕ) : ℤ) ≤ lim.word
  depth : d + 2 ≤ lim.depth
  solver : ∀ t < X.m, (need [X.n, X.D, X.w t]).Ok lim A.fr (d + 1)

/-- The context of hostLoop: a solver of Lop-AE-SparseTri, and the procedures writeX, writeY,
scanPairs, scan in the program. -/
structure HostCtx (P₀ R : Program) (pS pWriteX pWriteY pScanPairs pScan : ℕ) (Tn : List ℕ → ℕ)
    (need : List ℕ → Need) : Prop where
  sol : SolvesN lopDetectTask P₀ pS Tn need
  writeX : (P₀ ++ R)[pWriteX]? = some writeXBody
  writeY : (P₀ ++ R)[pWriteY]? = some writeYBody
  scanPairs : (P₀ ++ R)[pScanPairs]? = some (scanPairsBody pScan)
  scan : (P₀ ++ R)[pScan]? = some scanBody

/-- The arguments of hostLoop. -/
def hostLoopArgs (X : HostData) (A : HostAddr) : List ℤ :=
  [X.n, X.D, X.p, X.q, X.chunkCount, X.m, A.ab, A.bc, A.ac, A.rac, A.rbc, A.qi, A.qj, A.cr, A.cl,
    A.cw, A.x, A.y, A.out, A.fr]

/-! ## What the calls assume -/

/-- Everything that hostLoop assumes, and a memory μ' that agrees with the first memory μ below
x. -/
structure HostSetting (lim : Limits) (d : ℕ) (X : HostData) (U : ℕ) (A : HostAddr)
    (need : List ℕ → Need) (μ μ' : ℕ → ℤ) : Prop where
  ok : HostOk X U
  mem : HostMem X A μ
  lay : HostLay X A
  fits : HostLim lim d X U A need
  kept : Kept μ μ' A.x

/-- Entries 0 and 1 have absolute value at most 1. -/
theorem absLe_one_of_zero_or_one {L : List ℤ} (h : ∀ e ∈ L, e = 0 ∨ e = 1) :
    AbsLe L ((1 : ℕ) : ℤ) := by
  intro e he
  grind

namespace HostSetting

variable {X : HostData} {U : ℕ} {A : HostAddr} {need : List ℕ → Need} {μ μ' μ'' : ℕ → ℤ} {t : ℕ}

/-- The order of the regions of the memory, the limits, and the sizes of instance t. -/
theorem places (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    A.ab + X.n * X.n ≤ A.x ∧ A.bc + X.n * X.n ≤ A.x ∧ A.ac + X.n * X.n ≤ A.x ∧
      A.rac + X.n * X.n ≤ A.x ∧ A.rbc + X.n * X.n ≤ A.x ∧ A.qi + X.n * X.n ≤ A.x ∧
      A.qj + X.n * X.n ≤ A.x ∧ A.cr + X.chunkCount ≤ A.x ∧ A.cl + X.chunkCount ≤ A.x ∧
      A.cw + X.chunkCount ≤ A.x ∧ A.x + X.n * X.D ≤ A.y ∧ A.y + X.D * X.n ≤ A.out ∧
      A.out + X.w t ≤ A.fr ∧
      (lim.space : ℤ) ≤ lim.word ∧ A.fr < lim.space ∧ 2 * X.p < lim.space ∧
      (X.m : ℤ) ≤ lim.word ∧ ((X.n + X.q : ℕ) : ℤ) ≤ lim.word ∧ d + 2 ≤ lim.depth ∧
      X.c0 t + X.len t ≤ X.n ∧ X.lo t + X.w t ≤ X.n * X.n ∧ t % X.chunkCount < X.chunkCount :=
  ⟨S.lay.bAB, S.lay.bBC, S.lay.bAC, S.lay.bRAC, S.lay.bRBC, S.lay.bQI, S.lay.bQJ, S.lay.bCR,
    S.lay.bCL, S.lay.bCW, S.lay.xy, S.lay.yo, S.lay.ofr t ht, S.fits.space, S.fits.fr, S.fits.prime,
    S.fits.count, S.fits.step, S.fits.depth, S.ok.valid.piece_le ht, S.ok.valid.lo_add_le ht,
    HostData.mod_chunkCount_lt ht⟩

/-- A later memory that agrees with μ' below x. -/
theorem next (S : HostSetting lim d X U A need μ μ') (h : ∀ a < A.x, μ'' a = μ' a) :
    HostSetting lim d X U A need μ μ'' :=
  { S with kept := fun a ha => (h a ha).trans (S.kept a ha) }

/-- There are `n²` residues of the weights `w(a,c)`. -/
theorem length_RAC (S : HostSetting lim d X U A need μ μ') : X.RAC.length = X.n * X.n := by
  simp [HostData.RAC, residList, S.ok.valid.lenAC]

/-- There are `n²` residues of the weights `w(b,c)`. -/
theorem length_RBC (S : HostSetting lim d X U A need μ μ') : X.RBC.length = X.n * X.n := by
  simp [HostData.RBC, residList, S.ok.valid.lenBC]

/-- What the loop reads stands in μ' as it stood in μ. -/
theorem mem' (S : HostSetting lim d X U A need μ μ') : HostMem X A μ' := by
  light_facts S S.lay S.ok.valid
  have lenRAC := S.length_RAC
  have lenRBC := S.length_RBC
  have lenQI := S.ok.valid.length_QI
  have lenQJ := S.ok.valid.length_QJ
  have lenCT : X.CT.length = X.chunkCount := rfl
  have h := S.mem
  exact
    ⟨h.segAB.keep, h.segBC.keep, h.segAC.keep, h.segRAC.keep, h.segRBC.keep, h.segQI.keep, h.segQJ.keep, h.segCR.keep, h.segCL.keep, h.segCW.keep⟩

/-- Reading an entry of a component of the table of chunks. -/
theorem read_tab {a : ℕ} (f : Chunk → ℕ) (h : SegN μ a (X.CT.map f)) {i : ℕ}
    (hi : i < X.chunkCount) : μ (a + i) = (f (X.CT.getD i ⟨0, 0, 0⟩) : ℤ) := by
  have hi' : i < X.CT.length := hi
  rw [h i (by simp_all), List.getD_eq_getElem _ _ hi']
  simp

/-- The three parameters of the chunk of instance t, in the memory. -/
theorem read_chunk (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    μ' (A.cr + t % X.chunkCount) = X.rho t ∧ μ' (A.cl + t % X.chunkCount) = X.lo t ∧
      μ' (A.cw + t % X.chunkCount) = X.w t :=
  ⟨read_tab _ S.mem'.segCR (HostData.mod_chunkCount_lt ht),
    read_tab _ S.mem'.segCL (HostData.mod_chunkCount_lt ht),
    read_tab _ S.mem'.segCW (HostData.mod_chunkCount_lt ht)⟩

/-- What writeX and writeY assume, for a matrix of size cells at dst and the residues of a list of
weights at r. -/
theorem write (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) {dst size r : ℕ}
    {weights : List ℤ} (seg : SegN μ' r (residList X.p weights))
    (length : (residList X.p weights).length = X.n * X.n) (hsize : size = X.D * X.n)
    (hdst : dst + size < lim.space) (hr : r + X.n * X.n ≤ dst) :
    WritePre lim μ' dst size r X.n X.D X.p (X.c0 t) (X.len t) (residList X.p weights) := ⟨S.fits.space, seg, length, fun x hx => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx
    exact resid_lt S.ok.valid.p_ne z, S.ok.valid.len_mul_le t, S.ok.valid.piece_le ht, hsize, hdst, by omega, S.fits.prime, Or.inr hr⟩

/-- The precondition of writeX holds. -/
theorem writeX (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    WritePre lim μ' A.x (X.n * X.D) A.rac X.n X.D X.p (X.c0 t) (X.len t) X.RAC := by
  have hplaces := S.places ht
  exact S.write ht S.mem'.segRAC S.length_RAC (by grind) (by omega) (by omega)

/-- The precondition of writeY holds. -/
theorem writeY (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    WritePre lim μ' A.y (X.D * X.n) A.rbc X.n X.D X.p (X.c0 t) (X.len t) X.RBC := by
  have hplaces := S.places ht
  exact S.write ht S.mem'.segRBC S.length_RBC rfl (by omega) (by omega)

/-- The instance number t, as the solver gets it. -/
def inst (X : HostData) (A : HostAddr) (t : ℕ) : ThinInst :=
  ⟨X.n, X.D, X.w t, 1, A.x, A.y, A.qi + X.lo t, A.qj + X.lo t, A.out, X.matX t, X.matY t, X.WI t, X.WJ t⟩

/-- The precondition of the solver holds, once the two matrices are written. -/
theorem solver (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) (hX : Seg μ' A.x (X.matX t))
    (hY : Seg μ' A.y (X.matY t)) : lopDetectTask.Pre (inst X A t) μ' A.fr := by
  have hplaces := S.places ht
  have hv := S.ok.valid
  refine ⟨?_, ⟨X.matX_zero_or_one t, X.matY_zero_or_one t⟩, rfl⟩
  exact
    ⟨hv.n_pos, le_trans (Nat.mul_pos hv.q_pos hv.p_pos) hv.qp_le, le_rfl, X.length_matX t, X.length_matY t, hv.length_WI ht, hv.length_WJ ht, hX, hY, S.mem'.segQI.drop_take _ _, S.mem'.segQJ.drop_take _ _, absLe_one_of_zero_or_one (X.matX_zero_or_one t), absLe_one_of_zero_or_one (X.matY_zero_or_one t), fun _ => HostData.lt_of_mem_WI, fun _ => HostData.lt_of_mem_WJ, X.nodup_zip t, by grind [inst], by grind [inst], by grind [inst], by grind [inst], by aesop, by grind [inst], by aesop, by grind [inst], by grind [inst]⟩

/-- The weights are where the scans read them. -/
theorem weights (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    Weights lim μ' A.ab A.bc A.ac X.n U X.AB X.BC X.AC := by
  have hplaces := S.places ht
  have hm := S.mem'
  have hv := S.ok.valid
  exact
    ⟨S.fits.space, by exact_mod_cast S.fits.weights, Light.ArrayAt.mk hv.lenAB hm.segAB S.ok.leAB, Light.ArrayAt.mk hv.lenBC hm.segBC S.ok.leBC, Light.ArrayAt.mk hv.lenAC hm.segAC S.ok.leAC⟩

/-- The answers of the solver and the query pairs of the chunk are where the scans read them. -/
theorem answers (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (hans : Seg μ' A.out (X.ans t)) :
    Answers lim μ' A.out (A.qi + X.lo t) (A.qj + X.lo t) (X.w t) X.n (X.ans t) (X.WI t)
      (X.WJ t) := by
  have hplaces := S.places ht
  have hv := S.ok.valid
  exact
    { arrOUT :=
        Light.ListAt.mk (by simp [HostData.ans, thinOut, hv.length_WI ht, hv.length_WJ ht]) hans
      arrQA :=
        Light.IndexAt.mk (hv.length_WI ht) (SegN.drop_take S.mem'.segQI _ _) fun _ => HostData.lt_of_mem_WI
      arrQB :=
        Light.IndexAt.mk (hv.length_WJ ht) (SegN.drop_take S.mem'.segQJ _ _) fun _ => HostData.lt_of_mem_WJ
      w_lt := by omega }

end HostSetting

/-! ## The parts of a round -/

variable {P₀ R : Program} {pS pWriteX pWriteY pScanPairs pScan : ℕ} {Tn : List ℕ → ℕ}
  {need : List ℕ → Need} {X : HostData} {U : ℕ} {A : HostAddr} {μ μ' : ℕ → ℤ} {t : ℕ}

/-- The state of hostLoop: the arguments, the numbers t, ch and c0 of the instance, and what the
locals Found, Len, Residue, Start, NumPairs and Unused hold. -/
abbrev hostState (X : HostData) (A : HostAddr) (t ch c0 : ℕ) (fnd len rho lo w res : ℤ)
    (μ' : ℕ → ℤ) : State :=
  ⟨frame [X.n, X.D, X.p, X.q, X.chunkCount, X.m, A.ab, A.bc, A.ac, A.rac, A.rbc, A.qi, A.qj, A.cr,
    A.cl, A.cw, A.x, A.y, A.out, A.fr, t, ch, c0, fnd, len, rho, lo, w, res], μ'⟩

variable {P : Program}

/-- **The parameters of instance t.** -/
theorem hostParams_spec (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (fnd len rho lo w res : ℤ) :
    Ends lim P d hostParams (hostState X A t (t % X.chunkCount) (X.c0 t) fnd len rho lo w res μ') 27
      (· = hostState X A t (t % X.chunkCount) (X.c0 t) fnd (X.len t) (X.rho t) (X.lo t) (X.w t) res
        μ') := by
  have hplaces := S.places ht
  obtain ⟨hrho, hlo, hw⟩ := S.read_chunk ht
  have hlen : X.len t = min X.q _ := rfl
  generalize t % X.chunkCount = ch at *
  -- rho := mem[cr + ch]; lo := mem[cl + ch]; w := mem[cw + ch]
  have htail : ∀ len' : ℤ, len' = X.len t → Ends lim P d
      (.set Residue (M (v TabR +' v ChunkNo)) ;; .set Start (M (v TabL +' v ChunkNo)) ;;
        .set NumPairs (M (v TabW +' v ChunkNo)))
      (hostState X A t ch (X.c0 t) fnd len' rho lo w res μ') 15
      (· = hostState X A t ch (X.c0 t) fnd (X.len t) (X.rho t) (X.lo t) (X.w t) res μ') := by
    rintro _ rfl
    refine Ends.setToThen (X.rho t) ?_ (by light_side [hrho])
    refine Ends.setToThen (X.lo t) ?_ (by light_side [hlo])
    exact Ends.setTo _ rfl (by light_side [hw])
  light_set X.q
  -- if n - c0 < q then len := n - c0
  refine Ends.iteThen (fun hc => ?_) fun hc => ?_
  · replace hc : (X.n : ℤ) - X.c0 t < X.q := by assumption
    exact Ends.setToThen (X.len t) (by simp_all)
  · replace hc : ¬ (X.n : ℤ) - X.c0 t < X.q := by assumption
    refine Ends.next 0 (Ends.skip ?_)
    exact (htail _ (by omega)).mono (by light_time) fun _ h => h

/-- The time of the four calls. -/
def tCalls (Tn : List ℕ → ℕ) (X : HostData) (t : ℕ) : ℕ :=
  tWriteX X.n X.D (X.len t) + tWriteY X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
    tScanPairs (X.w t) (X.len t) (X.execs t) + 52

/-- The call of writeX for instance t. -/
theorem HostCtx.writeX_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    Meets lim (P₀ ++ R) pWriteX (d + 1)
      [(A.x : ℤ), A.rac, X.n, X.D, X.p, X.c0 t, X.len t, X.rho t] μ' (tWriteX X.n X.D (X.len t))
      fun _ μ₁ => Seg μ₁ A.x (X.matX t) ∧ SameOutside μ' μ₁ A.x (X.n * X.D) :=
  Meets.of_body C.writeX (writeX_spec (S.writeX ht) (S.ok.valid.rho_lt ht))

/-- The call of writeY for instance t. -/
theorem HostCtx.writeY_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    Meets lim (P₀ ++ R) pWriteY (d + 1) [(A.y : ℤ), A.rbc, X.n, X.D, X.p, X.c0 t, X.len t] μ'
      (tWriteY X.n X.D (X.len t))
      fun _ μ₁ => Seg μ₁ A.y (X.matY t) ∧ SameOutside μ' μ₁ A.y (X.D * X.n) :=
  Meets.of_body C.writeY (writeY_spec (S.writeY ht))

/-- The call of the solver for instance t, once the two matrices are written. -/
theorem HostCtx.solver_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) (hX : Seg μ' A.x (X.matX t))
    (hY : Seg μ' A.y (X.matY t)) :
    Meets lim (P₀ ++ R) pS (d + 1)
      [(X.n : ℤ), X.D, X.w t, (1 : ℕ), A.x, A.y, (A.qi + X.lo t : ℕ), (A.qj + X.lo t : ℕ), A.out,
        A.fr] μ' (Tn [X.n, X.D, X.w t])
      fun _ μ₁ => Seg μ₁ A.out (X.ans t) ∧ KeptBut μ' μ₁ A.fr A.out (X.w t) :=
  C.sol.meets R _ (S.solver ht hX hY) (S.fits.solver t ht)

/-- The call of scanPairs for instance t, once the solver has answered. -/
theorem HostCtx.scanPairs_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) (hans : Seg μ' A.out (X.ans t)) :
    Meets lim (P₀ ++ R) pScanPairs (d + 1)
      [(A.out : ℤ), (A.qi + X.lo t : ℕ), (A.qj + X.lo t : ℕ), X.w t, bit (X.found t), A.ab, A.bc,
        A.ac, X.n, X.c0 t, X.len t] μ' (tScanPairs (X.w t) (X.len t) (X.execs t))
      fun r μ₁ => r = bit (X.found (t + 1)) ∧ μ₁ = μ' := by
  have hplaces := S.places ht
  exact Meets.of_body C.scanPairs (scanPairs_spec C.scan (S.weights ht)
    (S.answers ht hans) (by omega) (S.ok.valid.piece_le ht))

/-- **The four calls for instance t.** -/
theorem hostCalls_spec (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) (ch : ℕ) (res : ℤ) :
    Ends lim (P₀ ++ R) d (hostCalls pS pWriteX pWriteY pScanPairs)
      (hostState X A t ch (X.c0 t) (bit (X.found t)) (X.len t) (X.rho t) (X.lo t) (X.w t) res μ')
      (tCalls Tn X t) fun σ => ∃ (res' : ℤ) (μ'' : ℕ → ℤ),
        σ = hostState X A t ch (X.c0 t) (bit (X.found (t + 1))) (X.len t) (X.rho t) (X.lo t)
          (X.w t) res' μ'' ∧ HostSetting lim d X U A need μ μ'' := by
  have hplaces := S.places ht
  unfold hostCalls tCalls
  -- res := writeX(x, rac, n, D, p, c0, len, rho)
  light_call (C.writeX_meets S ht) with r₁ μ₁ ⟨hX, hrest₁⟩
  have S₁ := S.next fun a ha => hrest₁ a (Or.inl ha)
  -- res := writeY(y, rbc, n, D, p, c0, len)
  light_call (C.writeY_meets S₁ ht) with r₂ μ₂ ⟨hY, hrest₂⟩
  have S₂ := S₁.next fun a ha => hrest₂ a (by omega)
  replace hX :=
    hX.keep (by light_keep [X.length_matX t])
  -- res := solver(n, D, w, 1, x, y, qi + lo, qj + lo, out, fr)
  light_call (C.solver_meets S₂ ht hX hY) with r₃ μ₃ ⟨hans, hkept₃⟩
  have S₃ := S₂.next fun a ha => hkept₃ a (by omega)
  -- fnd := scanPairs(out, qi + lo, qj + lo, w, fnd, ab, bc, ac, n, c0, len)
  light_call (C.scanPairs_meets S₃ ht hans) with _ μ₄ ⟨rfl, rfl⟩
  aesop

/-- **The counters**: from instance t to instance t + 1. -/
theorem hostNext_spec (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (fnd len rho lo w res : ℤ) :
    Ends lim P d hostNext (hostState X A t (t % X.chunkCount) (X.c0 t) fnd len rho lo w res μ') 18
      (· = hostState X A (t + 1) ((t + 1) % X.chunkCount) (X.c0 (t + 1)) fnd len rho lo w res
        μ') := by
  have hplaces := S.places ht
  have hlast := Nat.succ_div_mod_of_eq (n := X.chunkCount) (i := t)
  have hinner := Nat.succ_div_mod_of_ne (n := X.chunkCount) (i := t) (by omega)
  have hc0 : X.c0 t = t / X.chunkCount * X.q := rfl
  have hc0' : X.c0 _ = (t + 1) / X.chunkCount * X.q := rfl
  generalize t % X.chunkCount = ch at *
  generalize (t + 1) % X.chunkCount = ch' at *
  -- t := t + 1
  have htail : Ends lim P d (.set Inst (v Inst +' k 1))
      (hostState X A t ch' (X.c0 (t + 1)) fnd len rho lo w res μ') 4
      (· = hostState X A (t + 1) ch' (X.c0 (t + 1)) fnd len rho lo w res μ') :=
    Ends.setTo _ rfl
  light_set (ch + 1 : ℕ)
  -- if ch = chunkCount
  refine Ends.iteThen (fun hc => ?_) fun hc => ?_
  · replace hc : ch + 1 = X.chunkCount := by
      have : ((ch + 1 : ℕ) : ℤ) = X.chunkCount := by assumption
      omega
    have hstep : X.c0 (t + 1) = X.c0 t + X.q := by grind
    -- ch := 0; c0 := c0 + q
    have hwrap : Ends lim P d (.set ChunkNo (k 0) ;; .set PieceStart (v PieceStart +' v PieceLen))
        (hostState X A t (ch + 1) (X.c0 t) fnd len rho lo w res μ') 6
        (· = hostState X A t 0 (X.c0 (t + 1)) fnd len rho lo w res μ') :=
      Ends.setToThen 0
        (Ends.setTo _ rfl (by light_side [hstep]))
    refine Ends.next _ (hwrap.mono le_rfl ?_)
    simp_all
  · replace hc : ch + 1 ≠ X.chunkCount := fun h => by simp_all
    obtain ⟨hdiv, rfl⟩ := hinner hc
    have hstep : X.c0 (t + 1) = X.c0 t := by simp_all
    -- skip
    refine Ends.next 0 (Ends.skip ?_)
    rw [← hstep]
    exact htail.mono (by light_time) fun _ h => h

/-! ## The loop -/

/-- The invariant of the loop, before instance t. -/
def HostInv (lim : Limits) (d : ℕ) (X : HostData) (U : ℕ) (A : HostAddr) (need : List ℕ → Need)
    (μ : ℕ → ℤ) (t : ℕ) (σ : State) : Prop :=
  ∃ (len rho lo w res : ℤ) (μ' : ℕ → ℤ),
    σ = hostState X A t (t % X.chunkCount) (X.c0 t) (bit (X.found t)) len rho lo w res μ' ∧
    HostSetting lim d X U A need μ μ'

/-- **One round of the loop.** -/
theorem hostRound_spec (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (ht : t < X.m) {σ : State} (hσ : HostInv lim d X U A need μ t σ) :
    Ends lim (P₀ ++ R) d (hostRound pS pWriteX pWriteY pScanPairs) σ (tCalls Tn X t + 45)
      (HostInv lim d X U A need μ (t + 1)) := by
  obtain ⟨len, rho, lo, w, res, μ', rfl, S⟩ := hσ
  light_piece (hostParams_spec S ht _ len rho lo w res) with _ rfl
  -- the four calls
  light_piece (hostCalls_spec C S ht _ res) with _ ⟨res', μ'', rfl, S'⟩
  -- the counters
  light_piece (hostNext_spec S' ht _ _ _ _ _ res') with _ rfl
  exact ⟨_, _, _, _, _, μ'', rfl, S'⟩

/-- **hostLoop** returns 1 if a scan has found a zero triangle, and 0 if not, and changes no cell
below x. -/
theorem hostLoop_spec (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (hok : HostOk X U) (hmem : HostMem X A μ) (hlay : HostLay X A)
    (hlim : HostLim lim d X U A need) :
    Ends lim (P₀ ++ R) d (hostLoopBody pS pWriteX pWriteY pScanPairs)
      ⟨frame (hostLoopArgs X A), μ⟩ (tHostLoop Tn X) fun σ' =>
      σ'.loc 0 = bit (X.found X.m) ∧ Kept μ σ'.mem A.x := by
  have hw := hlim.space
  have hT : ∑ t ∈ Finset.range X.m, (4 + (tCalls Tn X t + 45))
      ≤ ∑ t ∈ Finset.range X.m, (tWrites X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
        tScanPairs (X.w t) (X.len t) (X.execs t)) :=
    by grind [tCalls, tWrites]
  unfold hostLoopBody tHostLoop hostLoopArgs
  -- t := 0; ch := 0; c0 := 0; fnd := 0
  light_set 0
  light_set 0
  light_set 0
  light_set 0
  -- while t < m
  refine Ends.next _ (Ends.while (HostInv lim d X U A need μ) X.m (fun t => tCalls Tn X t + 45)
    ?_ ?_ ?_) (by grind [Cond.cost, Expr.cost, Nat.reduceAdd])
  ·
    refine ⟨0, 0, 0, 0, 0, μ, ?_, hok, hmem, hlay, hlim, by tauto⟩
    rw [← frame_append_zeros _ 5]
    simp [HostData.c0, HostData.found, bit]
  ·
    intro t σ ht hσ
    obtain ⟨len, rho, lo, w, res, μ', rfl, -⟩ := id hσ
    exact ⟨by simp, by simp_all, hostRound_spec C ht hσ⟩
  ·
    rintro _ ⟨len, rho, lo, w, res, μ', rfl, S⟩
    -- return fnd
    exact ⟨by simp, by simp, Ends.setTo (bit (X.found X.m)) ⟨by simp, S.kept⟩⟩
