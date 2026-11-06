/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Need
import ThreeSumApsp.Spec.Sec3.Theorem17.ClassStarts

/-!
# The host of Theorem 17: the arrays and the loop

The third part of the host procedure `et17` (Exact Triangle by Theorem 17) fills the table of
doubles and the three lists of residues (`resid_then`), sorts the pairs into classes and cuts the
classes into chunks (`classes_then`), and calls the loop over the instances.

`et17Tables_spec` is the specification of the whole part: within `hostRunTime` steps, local 0 holds
the bit `found m` of the loop over the instances, and the cells below the free pointer are
unchanged.  Three lemmas connect the calls to the loop: `ready_of` (a run of et17 provides what this
part needs), `hostMem_of` (the arrays that the loop reads are in the memory) and `hostLay_of` (they
lie where the loop expects them).
-/


open ThreeSumApsp.Spec

namespace Light.Sec3

open ThreeSumApsp

namespace Et17


/-- What the third part needs, for the data X of the loop: the limits, the prime, and the three
matrices below the free pointer. -/
structure Ready (lim : Limits) (d : ℕ) (x : TriInst) (X : HostData) (μ : ℕ → ℤ) (fr : ℕ) :
    Prop where
  space : (lim.space : ℤ) ≤ lim.word
  depth : d + 2 ≤ lim.depth
  prime : 1 ≤ X.p
  word : ((X.p * 2 ^ (bitLen x.U + 1) : ℕ) : ℤ) ≤ lim.word
  top : aFr X x.U fr < lim.space
  segAB : Seg μ x.ab X.AB
  segBC : Seg μ x.bc X.BC
  segAC : Seg μ x.ac X.AC
  lenAB : X.AB.length = X.n * X.n
  lenBC : X.BC.length = X.n * X.n
  lenAC : X.AC.length = X.n * X.n
  leAB : AbsLe X.AB x.U
  leBC : AbsLe X.BC x.U
  leAC : AbsLe X.AC x.U
  belowAB : x.ab + X.n * X.n ≤ fr
  belowBC : x.bc + X.n * X.n ≤ fr
  belowAC : x.ac + X.n * X.n ≤ fr

variable {lim : Limits} {P : Program} {d : ℕ} {x : TriInst} {X : HostData} {μ : ℕ → ℤ} {fr : ℕ}

/-- The places of the lists of residues: they stand one after the other behind the table of doubles,
and end where the array of the classes begins, below the free pointer of the solver. -/
theorem resid_places (X : HostData) (U fr : ℕ) :
    aRab X U fr = fr + (bitLen U + 1) ∧ aRbc X U fr = aRab X U fr + X.n * X.n ∧
      aRac X U fr = aRbc X U fr + X.n * X.n ∧ aCls X U fr = aRac X U fr + X.n * X.n ∧
      aCls X U fr ≤ aFr X U fr := by
  grind [host_places]

/-- The places of the arrays of the classes and the chunks: they stand one after the other behind
the lists of residues, and end at aX, the first matrix of the instance that is handed to the solver,
below the free pointer of the solver. -/
theorem class_places (X : HostData) (U fr : ℕ) :
    aRbc X U fr = aRab X U fr + X.n * X.n ∧ aRac X U fr = aRbc X U fr + X.n * X.n ∧
      aCls X U fr = aRac X U fr + X.n * X.n ∧ aCur X U fr = aCls X U fr + (X.p + 1) ∧
      aQi X U fr = aCur X U fr + X.p ∧ aQj X U fr = aQi X U fr + X.n * X.n ∧
      aCr X U fr = aQj X U fr + X.n * X.n ∧ aCl X U fr = aCr X U fr + (X.n * X.n + X.p) ∧
      aCw X U fr = aCl X U fr + (X.n * X.n + X.p) ∧ aX X U fr = aCw X U fr + (X.n * X.n + X.p) ∧
      aX X U fr ≤ aFr X U fr := by
  grind [host_places]

/-- The memory after the first four calls: the three lists of residues; only cells between the free
pointer and the array of the classes have changed. -/
structure ResidMem (x : TriInst) (X : HostData) (fr : ℕ) (μ μ' : ℕ → ℤ) : Prop where
  rab : SegN μ' (aRab X x.U fr) X.RAB
  rbc : SegN μ' (aRbc X x.U fr) X.RBC
  rac : SegN μ' (aRac X x.U fr) X.RAC
  same : SameOn (fun c => c < fr ∨ aCls X x.U fr ≤ c) μ μ'

/-- The memory after the next two calls: the pairs, class after class, and the table of the chunks;
only cells between the array of the classes and aX, the first matrix of the instance that is handed
to the solver, have changed. -/
structure ClassMem (x : TriInst) (X : HostData) (fr : ℕ) (μ μ' : ℕ → ℤ) : Prop where
  qi : SegN μ' (aQi X x.U fr) X.QI
  qj : SegN μ' (aQj X x.U fr) X.QJ
  cr : SegN μ' (aCr X x.U fr) (X.CT.map fun c => c.residue)
  cl : SegN μ' (aCl X x.U fr) (X.CT.map fun c => c.start)
  cw : SegN μ' (aCw X x.U fr) (X.CT.map fun c => c.len)
  same : SameOn (fun c => c < aCls X x.U fr ∨ aX X x.U fr ≤ c) μ μ'

/-- What residues needs, for a matrix below the free pointer and a destination between the table of
doubles and the end of the arrays. -/
theorem Ready.residuesPre (h : Ready lim d x X μ fr) {μ' : ℕ → ℤ} {src dst : ℕ} {l : List ℤ}
    (hdbl : Seg μ' fr (dblList X.p (bitLen x.U))) (hsrc : Seg μ' src l)
    (hlen : l.length = X.n * X.n) (hle : AbsLe l x.U) (hbelow : src + X.n * X.n ≤ fr)
    (hlow : fr + (bitLen x.U + 1) ≤ dst := by omega)
    (hhigh : dst + X.n * X.n < lim.space := by omega) :
    ResiduesPre lim μ' src dst (X.n * X.n) fr X.p (bitLen x.U) x.U l :=
  ⟨h.space, h.prime, hdbl, hsrc, hlen, hle, Nat.lt_size_self _, by omega, by omega, by omega, by omega, by omega, by omega, h.word⟩

variable {g s : ℤ} {t : Stmt} {T : ℕ} {Q : State → Prop}

/-- **The table of doubles and the three lists of residues**, followed by the rest t of the text. -/
theorem resid_then {pDbl pResid pResidues : ℕ} (hDbl : P[pDbl]? = some dblTableBody)
    (hResid : P[pResid]? = some residBody) (hResidues : P[pResidues]? = some (residuesBody pResid))
    (hr : Ready lim d x X μ fr)     (h : ∀ res μ', ResidMem x X fr μ μ' → Ends lim P d t ⟨frame (locals x X fr g s 0 res), μ'⟩
      (T - (tDblTable (bitLen x.U) + 3 * tResidues (X.n * X.n) (bitLen x.U) + 26)) Q)
    (hT : tDblTable (bitLen x.U) + 3 * tResidues (X.n * X.n) (bitLen x.U) + 26 ≤ T := by omega) :
    Ends lim P d
      (.call pDbl [v Free, v ThePrime, v Bits] Small ;;
        .call pResidues [v AdrAB, v ResAB, v SizeSq, v Free, v Bits] Small ;;
        .call pResidues [v AdrBC, v ResBC, v SizeSq, v Free, v Bits] Small ;;
        .call pResidues [v AdrAC, v ResAC, v SizeSq, v Free, v Bits] Small ;; t)
      ⟨frame (locals x X fr g s 0 0), μ⟩ T Q := by
  have hdepth := hr.depth
  have htop := hr.top
  have hplaces := resid_places X x.U fr
  have lenAB := hr.lenAB
  have lenBC := hr.lenBC
  have lenAC := hr.lenAC
  have hAB := hr.belowAB
  have hBC := hr.belowBC
  have hAC := hr.belowAC
  have hword : X.p * 2 ^ bitLen x.U ≤ lim.word := le_trans (by
    exact_mod_cast Nat.mul_le_mul_left _ (by grind))
    hr.word
  light_call (dblTable_meets (dst := fr) (p := X.p) (len := bitLen x.U) hDbl hr.space
    (by omega) hword) with r₁ μ₁ ⟨hdbl, same₁⟩
  light_call (residues_meets hResidues hResid (by omega) (hr.residuesPre
    (dst := aRab X x.U fr) hdbl hr.segAB.keep hr.lenAB hr.leAB hr.belowAB)) with r₂ μ₂ ⟨hrab, same₂⟩
  light_call (residues_meets hResidues hResid (by omega) (hr.residuesPre
    (dst := aRbc X x.U fr) hdbl.keep hr.segBC.keep hr.lenBC hr.leBC hr.belowBC))
    with r₃ μ₃ ⟨hrbc, same₃⟩
  light_call (residues_meets hResidues hResid (by omega) (hr.residuesPre
    (dst := aRac X x.U fr) hdbl.keep hr.segAC.keep hr.lenAC hr.leAC hr.belowAC))
    with r₄ μ₄ ⟨hrac, same₄⟩
  exact (h r₄ μ₄ ⟨hrab.keep, hrbc.keep, hrac, by light_keep⟩).mono (by simp; omega) fun _ hQ => hQ

/-- There are at most n² + p chunks. -/
theorem Ready.chunkCount_le (hr : Ready lim d x X μ fr) (hcap : 1 ≤ X.cap) :
    X.chunkCount ≤ X.n * X.n + X.p :=
  length_chunkTab_le_add hcap fun i hi => lt_of_mem_residList hr.prime (by
    rw [List.getD_eq_getElem _ _ (by rw [HostData.RAB, length_residList, hr.lenAB]; assumption)]
    exact List.getElem_mem _)

variable {μ₁ : ℕ → ℤ}

/-- **The classes and the chunks**, followed by the rest t of the text. -/
theorem classes_then {pClasses pChunks : ℕ} (hClasses : P[pClasses]? = some classesBody)
    (hChunks : P[pChunks]? = some chunksBody) (hr : Ready lim d x X μ fr) (hcap : 1 ≤ X.cap)
    (hrab : SegN μ₁ (aRab X x.U fr) X.RAB) {res : ℤ}    
    (h : ∀ res' μ', ClassMem x X fr μ₁ μ' → Ends lim P d t
      ⟨frame (locals x X fr g s X.chunkCount res'), μ'⟩
      (T - (tClasses X.n X.p + tChunks X.p X.chunkCount + 17)) Q)
    (hT : tClasses X.n X.p + tChunks X.p X.chunkCount + 17 ≤ T) :
    Ends lim P d
      (.call pClasses [v ResAB, v Size, v ThePrime, v Cls, v Cur, v Rows, v Cols] Small ;;
        .call pChunks [v Cls, v ThePrime, v Cap, v TabR, v TabL, v TabW] NumChunks ;; t)
      ⟨frame (locals x X fr g s 0 res), μ₁⟩ T Q := by
  have hchunks : X.chunkCount = (chunkTabOf X.p X.cap _).length := rfl
  rw [hchunks] at h hT
  have hdepth := hr.depth
  have hp := hr.prime
  have htop := hr.top
  have hplaces := class_places X x.U fr
  have lenRAB : X.RAB.length = X.n * X.n := (length_residList _ _).trans hr.lenAB
  have ltRAB : ∀ r ∈ X.RAB, r < X.p := fun r hmem => lt_of_mem_residList (by omega) hmem
  refine Ends.callToThen (classes_meets hClasses hr.space
    ⟨aRab X x.U fr, X.n, X.p, aCls X x.U fr, aCur X x.U fr, aQi X x.U fr, aQj X x.U fr, X.RAB⟩ μ₁
    (Light.Sec3.ClassesPre.mk hrab lenRAB ltRAB)) ?_ (by simp)
  rintro r₁ μ₂ ⟨hcls, hqi, hqj, same₂⟩
  refine Ends.callToThen (chunks_meets hChunks hr.space
    ⟨aCls X x.U fr, X.p, X.cap, aCr X x.U fr, aCl X x.U fr, aCw X x.U fr, X.n * X.n + X.p, X.n * X.n, classStarts X.n X.p X.RAB⟩ μ₂
    (Light.Sec3.ChunksPre.mk hcls (length_classStarts X.n X.p X.RAB) (fun y hy => le_of_mem_classStarts hy) (hr.chunkCount_le hcap))) ?_ (by simp)
    (hT := by simp [ChunksArgs.table]; light_time)
  rintro _ μ₃ ⟨rfl, hcr, hcl, hcw, same₃⟩
  simp [ChunksArgs.table, ChunksArgs.Same] at hcr hcl hcw same₃ ⊢
  have hsorted : (sortedIdx X.n X.p X.RAB).length ≤ X.n * X.n := by
    grind [length_sortedIdx_eq, classStart_le_sq]
  have keep : ∀ {a : ℕ} {l : List ℕ}, SegN μ₂ a l → a + l.length ≤ aCr X x.U fr → SegN μ₃ a l := by
    intro a l hs hle
    refine hs.congr fun i hi => same₃ _ ⟨by grind, by grind, by grind⟩
  refine (h r₁ μ₃ ⟨by grind [HostData.QI, queryRows],
    by grind [HostData.QJ, queryCols], hcr, hcl, hcw,
    fun c hc => ?_⟩).mono (by omega) fun _ hQ => hQ
  exact (same₃ c ⟨by omega, by omega, by omega⟩).trans (same₂ c (by grind))

/-- Where the arrays lie, for the addresses of et17. -/
theorem hostLay_of (hr : Ready lim d x X μ fr) (hchunks : X.chunkCount ≤ X.n * X.n + X.p) :
    HostLay X (hostAddr x X fr) := by
  light_facts hr
  have hplaces := host_places X x.U fr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun t ht => ?_⟩
  case refine_13 =>
    have := X.w_le_cap ht
    grind [hostAddr]
  all_goals
    grind [hostAddr]

/-- The arrays that the loop over the instances reads are in the memory. -/
theorem hostMem_of (hr : Ready lim d x X μ fr) {μ₂ : ℕ → ℤ}
    (hresid : ResidMem x X fr μ μ₁) (hclass : ClassMem x X fr μ₁ μ₂) :
    HostMem X (hostAddr x X fr) μ₂ := by
  light_facts hr hresid hclass
  have hplaces := resid_places X x.U fr
  have lenRAC : X.RAC.length = X.n * X.n := (length_residList _ _).trans hr.lenAC
  have lenRBC : X.RBC.length = X.n * X.n := (length_residList _ _).trans hr.lenBC
  exact
    ⟨hr.segAB.keep, hr.segBC.keep, hr.segAC.keep, hresid.rac.keep, hresid.rbc.keep, hclass.qi, hclass.qj, hclass.cr, hclass.cl, hclass.cw⟩

/-- What the third part needs holds for the data of a run of et17. -/
theorem ready_of {need : List ℕ → Need} {D g a b : ℕ} (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    Ready lim d x (hostData x D g) μ fr := by
  have hD16 := hbig.sixteen_le
  have hcells := hok.cells
  have hdepth := hok.depth
  have htop := aFr_le (x := x) (g := g) hD16 fr
  have hp := two_le_hostData_p x g hD16
  have hps := Nat.mul_le_mul_right (2 ^ (bitLen x.U + 1)) (hostData_p_le x g hD16)
  simp [hostNeedAt] at hcells hdepth
  exact
    ⟨hok.space, by omega, by omega, le_word_of_le_hostWord hok, by omega, hpre.segAB, hpre.segBC, hpre.segAC, hpre.lenAB, hpre.lenBC, hpre.lenAC, hpre.leAB, hpre.leBC, hpre.leAC, hpre.belowAB, hpre.belowBC, hpre.belowAC⟩

end Et17

