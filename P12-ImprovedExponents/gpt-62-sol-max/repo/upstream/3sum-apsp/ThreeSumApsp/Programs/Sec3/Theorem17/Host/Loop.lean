/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.InstanceFacts
public import ThreeSumApsp.Programs.Sec3.Theorem17.Instances.WriteMatrices

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

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-! ## The procedure -/

namespace HostLocal

/-- The number n of vertices of a part. -/
registers [
  Size,
  /- The inner dimension D. -/ ParD,
  /- The prime p. -/ ThePrime,
  /- The number q of vertices of a piece. -/ PieceLen,
  /- The number chunkCount of chunks. -/ NumChunks,
  /- The number m of instances. -/ NumInst,
  /- The weights w(a,b). -/ AdrAB,
  /- The weights w(b,c). -/ AdrBC,
  /- The weights w(a,c). -/ AdrAC,
  /- The residues of the weights w(a,c). -/ ResAC,
  /- The residues of the weights w(b,c). -/ ResBC,
  /- The rows of the sorted query pairs. -/ Rows,
  /- The columns of the sorted query pairs. -/ Cols,
  /- The classes of the chunks. -/ TabR,
  /- The first places of the chunks. -/ TabL,
  /- The numbers of query pairs of the chunks. -/ TabW,
  /- The matrix X. -/ MatX,
  /- The matrix Y. -/ MatY,
  /- The answers of the solver. -/ AdrOut,
  /- The free pointer. -/ SolverFree,
  /- The number t of the instance. -/ Inst,
  /- The number ch of its chunk. -/ ChunkNo,
  /- The first vertex c0 of its piece. -/ PieceStart,
  /- 1 if a zero triangle has been found. -/ Found,
  /- The number len of vertices of the piece. -/ Len,
  /- The class rho of the chunk. -/ Residue,
  /- The first place lo of the chunk. -/ Start,
  /- The number w of query pairs of the chunk. -/ NumPairs,
  /- Results that are not used. -/ Unused]

end HostLocal

open HostLocal

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

/-- The time for writing the two matrices of an instance whose piece has len vertices, with the
calls and the bookkeeping of a round. -/
def tWrites (n D len : ℕ) : ℕ := 101 + tWrite n D len + tWrite n D len

/-! ## What the loop relies on -/

/-- The facts about the data that the loop relies on; U is a bound on the weights. -/
structure HostOk (X : HostData) (U : ℕ) : Prop where
  valid : X.Valid
  leAB : AbsLe X.AB U
  leBC : AbsLe X.BC U
  leAC : AbsLe X.AC U

/-- The addresses of the arrays. -/
structure HostAddr : Type where
  ab : ℕ
  bc : ℕ
  ac : ℕ
  rac : ℕ
  rbc : ℕ
  qi : ℕ
  qj : ℕ
  cr : ℕ
  cl : ℕ
  cw : ℕ
  x : ℕ
  y : ℕ
  out : ℕ
  fr : ℕ

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
structure HostCtx (P₀ R : Program) (pS pWriteX pWriteY pScan : ℕ) (Tn : List ℕ → ℕ)
    (need : List ℕ → Need) : Prop where
  sol : SolvesN lopDetectTask P₀ pS Tn need
  writeX : (P₀ ++ R)[pWriteX]? = some writeXBody
  writeY : (P₀ ++ R)[pWriteY]? = some writeYBody
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
private theorem absLe_one_of_zero_or_one {L : List ℤ} (h : ∀ e ∈ L, e = 0 ∨ e = 1) :
    AbsLe L ((1 : ℕ) : ℤ) := by
  intro e he
  rcases h e he with rfl | rfl <;> simp

namespace HostSetting

variable {X : HostData} {U : ℕ} {A : HostAddr} {need : List ℕ → Need} {μ μ' μ'' : ℕ → ℤ} {t : ℕ}

/-- Bring layout, word bounds and the selected instance's extent into the arithmetic context. -/
macro "host_facts " s:term:max t:term:max : tactic => `(tactic|
  (light_facts ($s).lay ($s).fits
   have := ($s).lay.ofr _ $t
   have := ($s).ok.valid.piece_le $t
   have := ($s).ok.valid.lo_add_le $t
   have := HostData.mod_chunkCount_lt $t))

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
    { segAB := h.segAB.keep
      segBC := h.segBC.keep
      segAC := h.segAC.keep
      segRAC := h.segRAC.keep
      segRBC := h.segRBC.keep
      segQI := h.segQI.keep
      segQJ := h.segQJ.keep
      segCR := h.segCR.keep
      segCL := h.segCL.keep
      segCW := h.segCW.keep }

/-- Reading an entry of a component of the table of chunks. -/
theorem read_tab {a : ℕ} (f : Chunk → ℕ) (h : SegN μ a (X.CT.map f)) {i : ℕ}
    (hi : i < X.chunkCount) : μ (a + i) = (f (X.CT.getD i ⟨0, 0, 0⟩) : ℤ) := by
  have hi' : i < X.CT.length := hi
  rw [h i (by simpa using hi'), List.getD_eq_getElem _ _ hi']
  simp

/-- The three parameters of the chunk of instance t, in the memory. -/
theorem read_chunk (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    μ' (A.cr + t % X.chunkCount) = X.rho t ∧ μ' (A.cl + t % X.chunkCount) = X.lo t ∧
      μ' (A.cw + t % X.chunkCount) = X.w t :=
  ⟨read_tab (fun c => c.residue) S.mem'.segCR (HostData.mod_chunkCount_lt ht),
    read_tab (fun c => c.start) S.mem'.segCL (HostData.mod_chunkCount_lt ht),
    read_tab (fun c => c.len) S.mem'.segCW (HostData.mod_chunkCount_lt ht)⟩

/-- What writeX and writeY assume, for a matrix of size cells at dst and the residues of a list of
weights at r. -/
private theorem write (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) {dst size r : ℕ}
    {weights : List ℤ} (seg : SegN μ' r (residList X.p weights))
    (length : (residList X.p weights).length = X.n * X.n) (hsize : size = X.D * X.n)
    (hdst : dst + size < lim.space) (hr : r + X.n * X.n ≤ dst) :
    WritePre lim μ' dst size r X.n X.D X.p (X.c0 t) (X.len t) (residList X.p weights) where
  hw := S.fits.space
  seg := seg
  length := length
  lt := fun x hx => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx
    exact resid_lt S.ok.valid.p_ne z
  fits := S.ok.valid.len_mul_le t
  piece := S.ok.valid.piece_le ht
  size := hsize
  spaceM := hdst
  spaceR := by omega
  spaceP := S.fits.prime
  apart := Or.inr hr

/-- The precondition of writeX holds. -/
theorem writeX (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    WritePre lim μ' A.x (X.n * X.D) A.rac X.n X.D X.p (X.c0 t) (X.len t) X.RAC := by
  host_facts S ht
  exact S.write ht S.mem'.segRAC S.length_RAC (Nat.mul_comm _ _) (by omega) (by omega)

/-- The precondition of writeY holds. -/
theorem writeY (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    WritePre lim μ' A.y (X.D * X.n) A.rbc X.n X.D X.p (X.c0 t) (X.len t) X.RBC := by
  host_facts S ht
  exact S.write ht S.mem'.segRBC S.length_RBC rfl (by omega) (by omega)

/-- The instance number t, as the solver gets it. -/
def inst (X : HostData) (A : HostAddr) (t : ℕ) : ThinInst :=
  { N := X.n, D := X.D, w := X.w t, U := 1, x := A.x, y := A.y, wi := A.qi + X.lo t,
    wj := A.qj + X.lo t, out := A.out, X := X.matX t, Y := X.matY t, WI := X.WI t, WJ := X.WJ t }

/-- The precondition of the solver holds, once the two matrices are written. -/
theorem solver (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) (hX : Seg μ' A.x (X.matX t))
    (hY : Seg μ' A.y (X.matY t)) : lopDetectTask.Pre (inst X A t) μ' A.fr := by
  host_facts S ht
  have hv := S.ok.valid
  refine ⟨?_, ⟨X.matX_zero_or_one t, X.matY_zero_or_one t⟩, rfl⟩
  exact
    { N_pos := hv.n_pos
      D_pos := le_trans (Nat.mul_pos hv.q_pos hv.p_pos) hv.qp_le
      U_pos := le_rfl
      lenX := X.length_matX t
      lenY := X.length_matY t
      lenWI := hv.length_WI ht
      lenWJ := hv.length_WJ ht
      segX := hX
      segY := hY
      segWI := SegN.drop_take S.mem'.segQI _ _
      segWJ := SegN.drop_take S.mem'.segQJ _ _
      leX := absLe_one_of_zero_or_one (X.matX_zero_or_one t)
      leY := absLe_one_of_zero_or_one (X.matY_zero_or_one t)
      ltWI := fun _ => HostData.lt_of_mem_WI
      ltWJ := fun _ => HostData.lt_of_mem_WJ
      nodup := X.nodup_zip t
      belowX := by simp only [inst]; omega
      belowY := by simp only [inst]; omega
      belowWI := by simp only [inst]; omega
      belowWJ := by simp only [inst]; omega
      belowOut := by simp only [inst]; omega
      apartX := by simp only [inst]; omega
      apartY := by simp only [inst]; omega
      apartWI := by simp only [inst]; omega
      apartWJ := by simp only [inst]; omega }

/-- The weights are where the scans read them. -/
theorem weights (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    Weights lim μ' ⟨X.n, U, A.ab, A.bc, A.ac, X.AB, X.BC, X.AC⟩ := by
  host_facts S ht
  have hm := S.mem'
  have hv := S.ok.valid
  exact
    { hw := S.fits.space
      hU := by exact_mod_cast S.fits.weights
      arrAB := { len := hv.lenAB, seg := hm.segAB, bound := S.ok.leAB }
      arrBC := { len := hv.lenBC, seg := hm.segBC, bound := S.ok.leBC }
      arrAC := { len := hv.lenAC, seg := hm.segAC, bound := S.ok.leAC } }

/-- The answers of the solver and the query pairs of the chunk are where the scans read them. -/
theorem answers (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (hans : Seg μ' A.out (X.ans t)) :
    Answers lim μ' A.out (A.qi + X.lo t) (A.qj + X.lo t) (X.w t) X.n (X.ans t) (X.WI t)
      (X.WJ t) := by
  host_facts S ht
  have hv := S.ok.valid
  exact
    { arrOUT :=
        { len := by simp [HostData.ans, thinOut, hv.length_WI ht, hv.length_WJ ht], seg := hans }
      arrQA :=
        { len := hv.length_WI ht, seg := SegN.drop_take S.mem'.segQI _ _
          lt := fun _ => HostData.lt_of_mem_WI }
      arrQB :=
        { len := hv.length_WJ ht, seg := SegN.drop_take S.mem'.segQJ _ _
          lt := fun _ => HostData.lt_of_mem_WJ }
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

/-- **The parameters of instance t.** -/
theorem hostParams_spec {P : Program} (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (fnd len rho lo w res : ℤ) :
    Ends lim P d hostParams (hostState X A t (t % X.chunkCount) (X.c0 t) fnd len rho lo w res μ') 27
      (· = hostState X A t (t % X.chunkCount) (X.c0 t) fnd (X.len t) (X.rho t) (X.lo t) (X.w t) res
        μ') := by
  host_facts S ht
  obtain ⟨hrho, hlo, hw⟩ := S.read_chunk ht
  have hlen : X.len t = min X.q (X.n - X.c0 t) := rfl
  generalize t % X.chunkCount = ch at *
  unfold hostParams
  light_set X.q
  light_if hlt hge : X.n - X.c0 t < X.q
  · light_set (X.len t : ℕ) using hlen, Nat.min_eq_right hlt.le
    light_steps using hrho, hlo, hw
    rfl
  · rw [← show X.q = X.len t by omega]
    light_steps using hrho, hlo, hw
    rfl

/-- The call of writeX for instance t. -/
theorem HostCtx.writeX_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    Meets lim (P₀ ++ R) pWriteX (d + 1)
      [(A.x : ℤ), A.rac, X.n, X.D, X.p, X.c0 t, X.len t, X.rho t] μ' (tWrite X.n X.D (X.len t))
      fun _ μ₁ => Seg μ₁ A.x (X.matX t) ∧ SameOutside μ' μ₁ A.x (X.n * X.D) :=
  Meets.of_body C.writeX (writeX_spec (S.writeX ht) (S.ok.valid.rho_lt ht))

/-- The call of writeY for instance t. -/
theorem HostCtx.writeY_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    Meets lim (P₀ ++ R) pWriteY (d + 1) [(A.y : ℤ), A.rbc, X.n, X.D, X.p, X.c0 t, X.len t] μ'
      (tWrite X.n X.D (X.len t))
      fun _ μ₁ => Seg μ₁ A.y (X.matY t) ∧ SameOutside μ' μ₁ A.y (X.D * X.n) :=
  Meets.of_body C.writeY (writeY_spec (S.writeY ht))

/-- The call of the solver for instance t, once the two matrices are written. -/
theorem HostCtx.solver_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) (hX : Seg μ' A.x (X.matX t))
    (hY : Seg μ' A.y (X.matY t)) :
    Meets lim (P₀ ++ R) pS (d + 1)
      [(X.n : ℤ), X.D, X.w t, (1 : ℕ), A.x, A.y, (A.qi + X.lo t : ℕ), (A.qj + X.lo t : ℕ), A.out,
        A.fr] μ' (Tn [X.n, X.D, X.w t])
      fun _ μ₁ => Seg μ₁ A.out (X.ans t) ∧ KeptBut μ' μ₁ A.fr A.out (X.w t) :=
  C.sol.meets R (HostSetting.inst X A t) (S.solver ht hX hY) (S.fits.solver t ht)

/-- **The counters**: from instance t to instance t + 1. -/
theorem hostNext_spec {P : Program} (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (fnd len rho lo w res : ℤ) :
    Ends lim P d hostNext (hostState X A t (t % X.chunkCount) (X.c0 t) fnd len rho lo w res μ') 18
      (· = hostState X A (t + 1) ((t + 1) % X.chunkCount) (X.c0 (t + 1)) fnd len rho lo w res
        μ') := by
  host_facts S ht
  have hlast := Nat.succ_div_mod_of_eq (n := X.chunkCount) (i := t)
  have hinner := Nat.succ_div_mod_of_ne (n := X.chunkCount) (i := t) (by omega)
  have hc0 : X.c0 t = t / X.chunkCount * X.q := rfl
  have hc0' : X.c0 (t + 1) = (t + 1) / X.chunkCount * X.q := rfl
  generalize t % X.chunkCount = ch at *
  generalize (t + 1) % X.chunkCount = ch' at *
  unfold hostNext
  light_step
  light_if hc hn : ch + 1 = X.chunkCount
  · obtain ⟨hdiv, rfl⟩ := hlast hc
    have hstep : X.c0 (t + 1) = X.c0 t + X.q := by rw [hc0', hc0, hdiv, Nat.succ_mul]
    light_steps
    simp [hstep]
  · obtain ⟨hdiv, rfl⟩ := hinner hn
    have hstep : X.c0 (t + 1) = X.c0 t := by rw [hc0', hc0, hdiv]
    light_steps
    simp [hstep]

end Light.Sec3
