/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Lang.Auto
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


/-- The four calls for one instance: the two matrices, the solver, the scans. -/
def hostCalls (pS pWriteX pWriteY pScanPairs : ℕ) (dst  := 23)  :=
  .call pWriteX [v 16, v 9, v 0, v 1, v 2, v 22, v 24, v 25]
    28 ;;
  .call pWriteY [v 17, v 10, v 0, v 1, v 2, v 22, v 24] 28 ;;
  .call pS [v 0, v 1, v 27, k 1, v 16, v 17, v 11 +' v 26, v 12 +' v 26,
    v 18, v 19] 28 ;;
  .call pScanPairs [v 18, v 11 +' v 26, v 12 +' v 26, v 27, v 23, v 6,
    v 7, v 8, v 0, v 22, v 24] dst

/-- The numbers of the next instance, of its chunk, and the first vertex of its piece. -/
def hostNext  :=
  .set 21 (v 21 +' k 1) ;;
  .ite (v 21 =' v 4)
    (.set 21 (k 0) ;; .set 22 (v 22 +' v 3)) .skip ;;
  .set 20 (v 20 +' k 1)

/-- The parameters of the instance: the number of vertices of its piece, and the class, the first
place and the number of query pairs of its chunk. -/
def hostParams  :=
  .set 24 (v 3) ;;
  .ite (v 0 -' v 22 <' v 3) (.set 24 (v 0 -' v 22)) .skip ;;
  .set 25 (M (v 13 +' v 21)) ;;
  .set 26 (M (v 14 +' v 21)) ;;
  .set 27 (M (v 15 +' v 21))

/-- One round of hostLoop. -/
def hostRound pS pWriteX pWriteY pScanPairs :=
  hostParams ;;
  hostCalls pS pWriteX pWriteY pScanPairs ;;
  hostNext

/-- hostLoop(n, D, p, q, chunkCount, m, ab, bc, ac, rac, rbc, qi, qj, cr, cl, cw, x, y, out, fr). -/
def hostLoopBody (pS pWriteX pWriteY pScanPairs : ℕ)  :=
  .set 20 (k 0) ;; .set 21 (k 0) ;; .set 22 (k 0) ;; .set 23 (k 0) ;;
  .while (v 20 <' v 5) (hostRound pS pWriteX pWriteY pScanPairs) ;;
  .set 0 (v 23)

/-- The time for writing the two matrices of an instance whose piece has len vertices, with the
calls and the bookkeeping of a round. -/
def tWrites n D len := 101 + tWriteX n D len + tWriteY n D len

/-- The number of steps of hostLoop, if the solver takes Tn. -/
def tHostLoop (Tn : Light.InputTime) (X : HostData) : ℕ :=
  ∑ t ∈ Finset.range X.m, (tWrites X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
    tScanPairs (X.w t) (X.len t) (X.execs t)) + 14

/-! ## What the loop relies on -/

/-- The facts about the data that the loop relies on; U is a bound on the weights. -/
structure HostOk (X : HostData) (U : ℕ) : Prop where
  valid : X.Valid
  leAB : AbsLe X.AB U
  leBC : AbsLe X.BC U
  leAC : AbsLe X.AC U

/-- The addresses of the arrays. -/
structure HostAddr where
  (ab bc ac rac rbc qi qj cr cl cw x y out fr : ℕ)

/-- What the memory holds: the weights, the residues of w(a,c) and w(b,c), the sorted query pairs,
and the three components of the table of chunks. -/
structure HostMem (X : HostData) (A : HostAddr) (μ : Light.Memory) : Prop where
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
    (need : Light.InputNeed) : Prop where
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
structure HostCtx (P₀ R : Program) (pS pWriteX pWriteY pScanPairs pScan : ℕ) (Tn : Light.InputTime)
    (need : Light.InputNeed) : Prop where
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
    (need : Light.InputNeed) (μ μ' : Light.Memory) : Prop where
  ok : HostOk X U
  mem : HostMem X A μ
  lay : HostLay X A
  fits : HostLim lim d X U A need
  kept : Kept μ μ' A.x

/-- Entries 0 and 1 have absolute value at most 1. -/
private theorem absLe_one_of_zero_or_one {L} (h : ∀ e ∈ L, e = 0 ∨ e = 1) :
    AbsLe L (1 : ℕ) := by
  intro e he
  rcases h e he with rfl | rfl <;> simp

namespace HostSetting

variable {X : HostData} {U : ℕ} {A : HostAddr} {need : Light.InputNeed} {μ μ' μ'' : Light.Memory} {t : ℕ}

variable (S : HostSetting lim d X U A need μ μ')

variable (ht : t < X.m)

include S ht in
/-- The order of the regions of the memory, the limits, and the sizes of instance t. -/
theorem places  :
    A.ab + X.n * X.n ≤ A.x ∧ A.bc + X.n * X.n ≤ A.x ∧ A.ac + X.n * X.n ≤ A.x ∧
      A.rac + X.n * X.n ≤ A.x ∧ A.rbc + X.n * X.n ≤ A.x ∧ A.qi + X.n * X.n ≤ A.x ∧
      A.qj + X.n * X.n ≤ A.x ∧ A.cr + X.chunkCount ≤ A.x ∧ A.cl + X.chunkCount ≤ A.x ∧
      A.cw + X.chunkCount ≤ A.x ∧ A.x + X.n * X.D ≤ A.y ∧ A.y + X.D * X.n ≤ A.out ∧
      A.out + X.w t ≤ A.fr ∧
      lim.space ≤ lim.word ∧ A.fr < lim.space ∧ 2 * X.p < lim.space ∧
      X.m ≤ lim.word ∧ (X.n + X.q : ℕ) ≤ lim.word ∧ d + 2 ≤ lim.depth ∧
      X.c0 t + X.len t ≤ X.n ∧ X.lo t + X.w t ≤ X.n * X.n ∧ t % X.chunkCount < X.chunkCount :=
  ⟨S.lay.bAB, S.lay.bBC, S.lay.bAC, S.lay.bRAC, S.lay.bRBC, S.lay.bQI, S.lay.bQJ, S.lay.bCR,
    S.lay.bCL, S.lay.bCW, S.lay.xy, S.lay.yo, S.lay.ofr t ht, S.fits.space, S.fits.fr, S.fits.prime,
    S.fits.count, S.fits.step, S.fits.depth, S.ok.valid.piece_le ht, S.ok.valid.lo_add_le ht,
    HostData.mod_chunkCount_lt ht⟩

/-- A later memory that agrees with μ' below x. -/
def next (S : HostSetting lim d X U A need μ μ') (h : ∀ a < A.x, μ'' a = μ' a) :=
  { S with kept := fun a ha => (h a ha).trans (S.kept a ha) }

include S in
/-- There are `n²` residues of the weights `w(a,c)`. -/
theorem length_RAC : X.RAC.length = X.n * X.n := by
  simp [HostData.RAC, residList, S.ok.valid.lenAC]

include S in
/-- There are `n²` residues of the weights `w(b,c)`. -/
theorem length_RBC : X.RBC.length = X.n * X.n := by
  simp [HostData.RBC, residList, S.ok.valid.lenBC]

/-- What the loop reads stands in μ' as it stood in μ. -/
theorem mem' (S : HostSetting lim d X U A need μ μ') : HostMem X A μ' := by
  light_facts S S.lay S.ok.valid
  have  := S.length_RAC
  have  := S.length_RBC
  have  := S.ok.valid.length_QI
  have  := S.ok.valid.length_QJ
  have  : X.CT.length = X.chunkCount := rfl
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
theorem read_tab {a} f (h : SegN μ a (X.CT.map f)) {i}
    (hi : i < X.chunkCount) : μ (a + i) = (f (X.CT.getD i ⟨0, 0, 0⟩) : ℤ) := by
  have hi' : i < X.CT.length := hi
  rw [h i (by simpa using hi'), List.getD_eq_getElem _ _ hi']
  simp

include S ht in
/-- The three parameters of the chunk of instance t, in the memory. -/
theorem read_chunk  :
    μ' (A.cr + t % X.chunkCount) = X.rho t ∧ μ' (A.cl + t % X.chunkCount) = X.lo t ∧
      μ' (A.cw + t % X.chunkCount) = X.w t :=
  ⟨read_tab (fun c => c.residue) S.mem'.segCR (HostData.mod_chunkCount_lt ht),
    read_tab (fun c => c.start) S.mem'.segCL (HostData.mod_chunkCount_lt ht),
    read_tab (fun c => c.len) S.mem'.segCW (HostData.mod_chunkCount_lt ht)⟩

include S ht in
/-- What writeX and writeY assume, for a matrix of size cells at dst and the residues of a list of
weights at r. -/
private theorem write  {dst size r}
    {weights} (seg : SegN μ' r (residList X.p weights))
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

include S ht in
/-- The precondition of writeX holds. -/
theorem writeX  :
    WritePre lim μ' A.x (X.n * X.D) A.rac X.n X.D X.p (X.c0 t) (X.len t) X.RAC := by
  have  := S.places ht
  exact S.write ht S.mem'.segRAC S.length_RAC (Nat.mul_comm _ _) (by omega) (by omega)

include S ht in
/-- The precondition of writeY holds. -/
theorem writeY  :
    WritePre lim μ' A.y (X.D * X.n) A.rbc X.n X.D X.p (X.c0 t) (X.len t) X.RBC := by
  have  := S.places ht
  exact S.write ht S.mem'.segRBC S.length_RBC rfl (by omega) (by omega)

/-- The instance number t, as the solver gets it. -/
def inst (X : HostData) (A : HostAddr) (t : ℕ) : ThinInst :=
  { N := X.n, D := X.D, w := X.w t, U := 1, x := A.x, y := A.y, wi := A.qi + X.lo t,
    wj := A.qj + X.lo t, out := A.out, X := X.matX t, Y := X.matY t, WI := X.WI t, WJ := X.WJ t }

include S ht in
/-- The precondition of the solver holds, once the two matrices are written. -/
theorem solver  (hX : Seg μ' A.x (X.matX t))
    (hY : Seg μ' A.y (X.matY t)) : lopDetectTask.Pre (inst X A t) μ' A.fr := by
  have  := S.places ht
  have hv := S.ok.valid
  refine ⟨?_, ⟨X.matX_zero_or_one t, X.matY_zero_or_one t⟩, rfl⟩
  exact
    { N_pos := hv.n_pos
      D_pos := le_trans (Nat.mul_pos hv.q_pos hv.p_pos) hv.qp_le
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
      belowX := by simp only [inst]; omega
      belowY := by simp only [inst]; omega
      belowWI := by simp only [inst]; omega
      belowWJ := by simp only [inst]; omega
      belowOut := by simp only [inst]; omega
      apartX := by simp only [inst]; omega
      apartY := by simp only [inst]; omega
      apartWI := by simp only [inst]; omega
      apartWJ := by simp only [inst]; omega }

include S ht in
/-- The weights are where the scans read them. -/
theorem weights  :
    Weights lim μ' A.ab A.bc A.ac X.n U X.AB X.BC X.AC := by
  have  := S.places ht
  have hm := S.mem'
  have hv := S.ok.valid
  exact
    { hw := S.fits.space
      hU := mod_cast S.fits.weights
      arrAB := { len := hv.lenAB, seg := hm.segAB, bound := S.ok.leAB }
      arrBC := { len := hv.lenBC, seg := hm.segBC, bound := S.ok.leBC }
      arrAC := { len := hv.lenAC, seg := hm.segAC, bound := S.ok.leAC } }

include S ht in
/-- The answers of the solver and the query pairs of the chunk are where the scans read them. -/
theorem answers
    (hans : Seg μ' A.out (X.ans t)) :
    Answers lim μ' A.out (A.qi + X.lo t) (A.qj + X.lo t) (X.w t) X.n (X.ans t) (X.WI t)
      (X.WJ t) := by
  have  := S.places ht
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

variable {P₀ R : Program} {pS pWriteX pWriteY pScanPairs pScan : ℕ} {Tn : Light.InputTime}
  {need : Light.InputNeed} {X : HostData} {U : ℕ} {A : HostAddr} {μ μ' : Light.Memory} {t : ℕ}

/-- The state of hostLoop: the arguments, the numbers t, ch and c0 of the instance, and what the
locals Found, Len, Residue, Start, NumPairs and Unused hold. -/
abbrev hostState (X : HostData) (A : HostAddr) (t ch c0 : ℕ) (fnd len rho lo w res : ℤ)
    (μ' : Light.Memory) : State :=
  ⟨frame [X.n, X.D, X.p, X.q, X.chunkCount, X.m, A.ab, A.bc, A.ac, A.rac, A.rbc, A.qi, A.qj, A.cr,
    A.cl, A.cw, A.x, A.y, A.out, A.fr, t, ch, c0, fnd, len, rho, lo, w, res], μ'⟩

/-- **The parameters of instance t.** -/
theorem hostParams_spec {P} (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
     fnd len rho lo w res :
    Ends lim P d hostParams (hostState X A t (t % X.chunkCount) (X.c0 t) fnd len rho lo w res μ') 27
      (· = hostState X A t (t % X.chunkCount) (X.c0 t) fnd (X.len t) (X.rho t) (X.lo t) (X.w t) res
        μ') := by
  have  := S.places ht
  obtain ⟨hrho, hlo, hw⟩ := S.read_chunk ht
  have  : X.len t = min X.q (X.n - X.c0 t) := rfl
  generalize t % X.chunkCount = ch at *
  -- rho := mem[cr + ch]; lo := mem[cl + ch]; w := mem[cw + ch]
  have htail : ∀ len' , len' = X.len t → Ends lim P d
      (.set 25 (M (v 13 +' v 21)) ;; .set 26 (M (v 14 +' v 21)) ;;
        .set 27 (M (v 15 +' v 21)))
      (hostState X A t ch (X.c0 t) fnd len' rho lo w res μ') 15
      (· = hostState X A t ch (X.c0 t) fnd (X.len t) (X.rho t) (X.lo t) (X.w t) res μ') := by
    rintro _ rfl
    refine Ends.setToThen (X.rho t : ℤ) ?_ (by light_side [hrho])
    refine Ends.setToThen (X.lo t : ℤ) ?_ (by light_side [hlo])
    exact Ends.setTo (X.w t : ℤ) rfl (by light_side [hw])
  unfold hostParams
  -- len := q
  light_set X.q
  -- if n - c0 < q then len := n - c0
  refine Ends.iteThen (fun hc => ?_) fun hc => ?_
  · replace hc  := by simpa using hc
    exact Ends.setToThen _ ((htail _ rfl).mono (by light_time) fun _ h => h)
  · replace hc  := by simpa using hc
    refine Ends.next 0 (Ends.skip ?_)
    exact (htail _ (by omega)).mono (by light_time) fun _ h => h

/-- The time of the four calls. -/
def tCalls (Tn : Light.InputTime) (X : HostData) t :=
  tWriteX X.n X.D (X.len t) + tWriteY X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
    tScanPairs (X.w t) (X.len t) (X.execs t) + 52

variable (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)

variable (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)

include C S ht in
/-- The call of writeX for instance t. -/
theorem HostCtx.writeX_meets
     :
    Meets lim (P₀ ++ R) pWriteX (d + 1)
      [A.x, A.rac, X.n, X.D, X.p, X.c0 t, X.len t, X.rho t] μ' (tWriteX X.n X.D (X.len t))
      fun _ μ₁ => Seg μ₁ A.x (X.matX t) ∧ SameOutside μ' μ₁ A.x (X.n * X.D) :=
  Meets.of_body C.writeX (writeX_spec (S.writeX ht) (S.ok.valid.rho_lt ht))

include C S ht in
/-- The call of writeY for instance t. -/
theorem HostCtx.writeY_meets
     :
    Meets lim (P₀ ++ R) pWriteY (d + 1) [A.y, A.rbc, X.n, X.D, X.p, X.c0 t, X.len t] μ'
      (tWriteY X.n X.D (X.len t))
      fun _ μ₁ => Seg μ₁ A.y (X.matY t) ∧ SameOutside μ' μ₁ A.y (X.D * X.n) :=
  Meets.of_body C.writeY (writeY_spec (S.writeY ht))

include C S ht in
/-- The call of the solver for instance t, once the two matrices are written. -/
theorem HostCtx.solver_meets
     (hX : Seg μ' A.x (X.matX t))
    (hY : Seg μ' A.y (X.matY t)) :
    Meets lim (P₀ ++ R) pS (d + 1)
      [X.n, X.D, X.w t, 1, A.x, A.y, A.qi + X.lo t, A.qj + X.lo t, A.out,
        A.fr] μ' (Tn [X.n, X.D, X.w t])
      fun _ μ₁ => Seg μ₁ A.out (X.ans t) ∧ KeptBut μ' μ₁ A.fr A.out (X.w t) :=
  C.sol.meets R _ (S.solver ht hX hY) (S.fits.solver t ht)

include C S ht in
/-- The call of scanPairs for instance t, once the solver has answered. -/
theorem HostCtx.scanPairs_meets
     (hans : Seg μ' A.out (X.ans t)) :
    Meets lim (P₀ ++ R) pScanPairs (d + 1)
      [A.out, A.qi + X.lo t, A.qj + X.lo t, X.w t, bit (X.found t), A.ab, A.bc,
        A.ac, X.n, X.c0 t, X.len t] μ' (tScanPairs (X.w t) (X.len t) (X.execs t))
      fun r μ₁ => r = bit (X.found (t + 1)) ∧ μ₁ = μ' := by
  have  := S.places ht
  exact Meets.of_body C.scanPairs (scanPairs_spec (f := X.found t) C.scan (S.weights ht)
    (S.answers ht hans) (by omega) (S.ok.valid.piece_le ht))

include C S ht in
/-- **The four calls for instance t.** -/
theorem hostCalls_spec
     ch res :
    Ends lim (P₀ ++ R) d (hostCalls pS pWriteX pWriteY pScanPairs)
      (hostState X A t ch (X.c0 t) (bit (X.found t)) (X.len t) (X.rho t) (X.lo t) (X.w t) res μ')
      (tCalls Tn X t) fun σ => ∃ (res' : ℤ) (μ'' : Light.Memory),
        σ = hostState X A t ch (X.c0 t) (bit (X.found (t + 1))) (X.len t) (X.rho t) (X.lo t)
          (X.w t) res' μ'' ∧ HostSetting lim d X U A need μ μ'' := by
  have  := S.places ht
  unfold hostCalls tCalls
  -- res := writeX(x, rac, n, D, p, c0, len, rho)
  light_call (C.writeX_meets S ht) with r₁ μ₁ ⟨hX, hrest₁⟩
  have S₁ := S.next fun a ha => hrest₁ a (Or.inl ha)
  -- res := writeY(y, rbc, n, D, p, c0, len)
  light_call (C.writeY_meets S₁ ht) with r₂ μ₂ ⟨hY, hrest₂⟩
  have S₂ := S₁.next fun a ha => hrest₂ a (Or.inl (by omega))
  replace hX  :=
    hX.keep (by light_keep [X.length_matX t])
  -- res := solver(n, D, w, 1, x, y, qi + lo, qj + lo, out, fr)
  light_call (C.solver_meets S₂ ht hX hY) with r₃ μ₃ ⟨hans, hkept₃⟩
  have S₃ := S₂.next fun a ha => hkept₃ a (by omega)
  -- fnd := scanPairs(out, qi + lo, qj + lo, w, fnd, ab, bc, ac, n, c0, len)
  light_call (C.scanPairs_meets S₃ ht hans) with _ μ₄ ⟨rfl, rfl⟩
  exact ⟨r₃, μ₄, rfl, S₃⟩

/-- **The counters**: from instance t to instance t + 1. -/
theorem hostNext_spec {P} (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
     fnd len rho lo w res :
    Ends lim P d hostNext (hostState X A t (t % X.chunkCount) (X.c0 t) fnd len rho lo w res μ') 18
      (· = hostState X A (t + 1) ((t + 1) % X.chunkCount) (X.c0 (t + 1)) fnd len rho lo w res
        μ') := by
  have  := S.places ht
  have hlast := Nat.succ_div_mod_of_eq (n := X.chunkCount) (i := t)
  have hinner := Nat.succ_div_mod_of_ne (n := X.chunkCount) (i := t) (by omega)
  have hc0 : X.c0 t = t / X.chunkCount * X.q := rfl
  have hc0' : X.c0 (t + 1) = (t + 1) / X.chunkCount * X.q := rfl
  generalize t % X.chunkCount = ch at *
  generalize (t + 1) % X.chunkCount = ch' at *
  -- t := t + 1
  have htail : Ends lim P d (.set 20 (v 20 +' k 1))
      (hostState X A t ch' (X.c0 (t + 1)) fnd len rho lo w res μ') 4
      (· = hostState X A (t + 1) ch' (X.c0 (t + 1)) fnd len rho lo w res μ') :=
    Ends.setTo (t + 1 : ℕ) rfl
  unfold hostNext
  -- ch := ch + 1
  light_set (ch + 1 : ℕ)
  -- if ch = chunkCount
  refine Ends.iteThen (fun hc => ?_) (fun hc => ?_)
  · replace hc : ch + 1 = X.chunkCount := by
      have := by simpa using hc
      exact_mod_cast this


    -- ch := 0; c0 := c0 + q

    light_block []
  · replace hc : ch + 1 ≠ X.chunkCount := fun h => hc (by simp; exact_mod_cast h)
    obtain ⟨hdiv, rfl⟩ := hinner hc
    have hstep : X.c0 (t + 1) = X.c0 t := by rw [hc0', hc0, hdiv]
    -- skip
    refine Ends.next 0 (Ends.skip ?_)
    rw [← hstep]
    exact htail.mono (by light_time) fun _ h => h

/-! ## The loop -/

/-- The invariant of the loop, before instance t. -/
def HostInv lim d X U A need
     μ t σ :=
  ∃ (len rho lo w res : ℤ) (μ' : Light.Memory),
    σ = hostState X A t (t % X.chunkCount) (X.c0 t) (bit (X.found t)) len rho lo w res μ' ∧
    HostSetting lim d X U A need μ μ'

include C in
/-- **One round of the loop.** -/
theorem hostRound_spec
    (ht : t < X.m) {σ} (hσ : HostInv lim d X U A need μ t σ) :
    Ends lim (P₀ ++ R) d (hostRound pS pWriteX pWriteY pScanPairs) σ (tCalls Tn X t + 45)
      (HostInv lim d X U A need μ (t + 1)) := by
  obtain ⟨len, rho, lo, w, res, μ', rfl, S⟩ := hσ
  unfold hostRound
  -- the parameters of the instance
  light_piece (hostParams_spec S ht _ len rho lo w res) with _ rfl
  -- the four calls
  light_piece (hostCalls_spec C S ht _ res) with _ ⟨res', μ'', rfl, S'⟩
  -- the counters
  light_piece (hostNext_spec S' ht _ _ _ _ _ res') with _ rfl
  exact ⟨_, _, _, _, _, μ'', rfl, S'⟩

include C in
/-- **hostLoop** returns 1 if a scan has found a zero triangle, and 0 if not, and changes no cell
below x. -/
theorem hostLoop_spec
    (hok : HostOk X U) (hmem : HostMem X A μ) (hlay : HostLay X A)
    (hlim : HostLim lim d X U A need) :
    Ends lim (P₀ ++ R) d (hostLoopBody pS pWriteX pWriteY pScanPairs)
      ⟨frame (hostLoopArgs X A), μ⟩ (tHostLoop Tn X) fun σ' =>
      σ'.loc 0 = bit (X.found X.m) ∧ Kept μ σ'.mem A.x := by
  have  := hlim.space
  have hT : ∑ t ∈ Finset.range X.m, (4 + (tCalls Tn X t + 45))
      ≤ ∑ t ∈ Finset.range X.m, (tWrites X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
        tScanPairs (X.w t) (X.len t) (X.execs t)) :=
    Finset.sum_le_sum fun t _ => by simp [tCalls, tWrites]; omega
  unfold hostLoopBody tHostLoop hostLoopArgs
  -- t := 0; ch := 0; c0 := 0; fnd := 0
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  -- while t < m
  refine Ends.next _ (Ends.while (HostInv lim d X U A need μ) X.m (fun t => tCalls Tn X t + 45)
    ?start ?round ?done) (by light_side)
  case start =>
    refine ⟨0, 0, 0, 0, 0, μ, ?_, hok, hmem, hlay, hlim, fun _ _ => rfl⟩
    rw [hostState, ← frame_append_zeros _ 5]
    simp [HostData.c0, HostData.found, bit]
  case round =>
    intro t σ ht hσ
    obtain ⟨len, rho, lo, w, res, μ', rfl, -⟩ := id hσ
    exact ⟨⟨trivial, trivial⟩, by simpa using ht, hostRound_spec C ht hσ⟩
  case done =>
    rintro _ ⟨len, rho, lo, w, res, μ', rfl, S⟩
    -- return fnd
    exact ⟨⟨trivial, trivial⟩, by simp, Ends.setTo (bit (X.found X.m)) ⟨rfl, S.kept⟩
      (hT := by light_side)⟩

end Light.Sec3
