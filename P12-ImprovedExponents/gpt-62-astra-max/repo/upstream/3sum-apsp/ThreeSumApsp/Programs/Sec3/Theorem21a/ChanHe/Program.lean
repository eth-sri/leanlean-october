/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Host
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Buckets
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.LibraryContracts
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Modulus
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.NodeArray
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Separate.Core
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.TimeBound

/-!
# The program of the reduction from 3SUM to Convolution-3SUM, assembled

The procedures of the reduction are appended to the program of an arbitrary solver of
Convolution-3SUM. Each of them meets its specification because the procedures that it calls meet
theirs; the last one, the host, solves 3SUM (`isHost_s3`).  That the answer is right comes from
`core_spec`, through `threeSum_iff_trees`.  With the arithmetic of `claim_CH20_Theorem_5_1_of_host`
this gives [CH20, Theorem 5.1] (Theorem 21(a)) for programs of the light language
(`claim_CH20_Theorem_5_1`).
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp

namespace Proc

/-- The places of the procedures in the list `chBodies`. -/
slots 0 emod log2 clog2 sqrt sieve fill resid tally coll heavy search modulus nodeArray nodes
  params pick leaf any0 any1 any2 any3 core host table

end Proc

/-- The procedures of the reduction, for a solver of Convolution-3SUM that is procedure number pC3
of a program with o procedures: the procedure at the place i of this list gets the number o + i.
The places have the names `Proc.emod`, …, `Proc.host`, in the order of the list. -/
def chBodies (κ pC3 o : ℕ) : Program :=
  [emodBody,
    log2Body,
    clog2Body,
    sqrtBody,
    sieveBody,
    fillBody,
    residBody (o + Proc.emod),
    tallyBody,
    collBody (o + Proc.resid) (o + Proc.tally),
    heavyBody (o + Proc.resid) (o + Proc.tally),
    searchBody (o + Proc.coll),
    modulusBody (o + Proc.search) (o + Proc.coll),
    NodeArray.body (o+Proc.table),
    nodesBody (o + Proc.nodes) (o + Proc.modulus) (o + Proc.nodeArray) pC3 (o + Proc.heavy),
    paramsBody (o + Proc.log2) (o + Proc.clog2) (o + Proc.sqrt),
    Separate.pickBody,
    Separate.Leaf.body (o + Proc.pick) (o + Proc.nodes),
    Separate.anyBody (o + Proc.leaf), Separate.anyBody (o + Proc.any0),
    Separate.anyBody (o + Proc.any1), Separate.anyBody (o + Proc.any2),
    Separate.Core.body (o + Proc.params) (o + Proc.log2) (o + Proc.sieve) (o + Proc.fill) (o + Proc.any3),
    hostBody κ (o + Proc.core), RepTable.body (o+Proc.emod)]

/-- **The host**: from every solver of Convolution-3SUM, the procedures of the reduction make a
solver of 3SUM. -/
theorem isHost_s3 (κ : ℕ) : IsHost HashTriangle.task s3Task (chTime κ) (chNeed κ) := by
  refine ⟨fun P₀ pC3 T r hsol => ⟨chBodies κ pC3 P₀.length, P₀.length + Proc.host,
    hostBody κ (P₀.length + Proc.core), ?_,
    fun R lim d x μ fr hpre hok => ?_⟩, fun r hr => polyNeed_chNeed κ r hr⟩
  · have := getElem?_append_append (P₀ := P₀) (B := chBodies κ pC3 P₀.length) [] (i := Proc.host)
      rfl
    assumption
  rw [List.append_assoc]
  have L : ∀ {i } {body }, (chBodies κ pC3 P₀.length)[i]? = some body →
      (P₀ ++ (chBodies κ pC3 P₀.length ++ R))[P₀.length + i]? = some body :=
    fun h => getElem?_append_append R h
  have hEmod : EmodSpec lim (P₀ ++ (chBodies κ pC3 P₀.length ++ R)) P₀.length :=
    emodSpec_of (L (i := Proc.emod) rfl)
  have hLog2 := log2Spec_of (lim := lim) (L (i := Proc.log2) rfl)
  have hClog2 := clog2Spec_of (lim := lim) (L (i := Proc.clog2) rfl)
  have hPrimes := primesSpec_of (lim := lim) (L (i := Proc.sieve) rfl)
  have hResid := resid_spec (L (i := Proc.resid) rfl) hEmod
  have hTally := tally_spec (lim := lim) (L (i := Proc.tally) rfl)
  have hColl := coll_spec (L (i := Proc.coll) rfl) hResid hTally
  have hHeavy := heavy_spec (L (i := Proc.heavy) rfl) hResid hTally
  have hModulus := modulusSpec_of (L (i := Proc.modulus) rfl) (L rfl) hColl
  have hArray := NodeArray.spec (L (i:=Proc.nodeArray) rfl) (L (i:=Proc.table) rfl) hEmod
  have hNodes := nodes_spec ⟨hsol, L (i := Proc.nodes) rfl, hModulus, hArray, hHeavy⟩
  have hParams := params_spec (L (i := Proc.params) rfl) hLog2 hClog2 (L rfl)
  have hCore := Separate.Core.spec
    (params:=P₀.length+Proc.params) (log:=P₀.length+Proc.log2) (primes:=P₀.length+Proc.sieve)
    (fill:=P₀.length+Proc.fill) (pick:=P₀.length+Proc.pick) (nodes:=P₀.length+Proc.nodes)
    (leaf:=P₀.length+Proc.leaf) (bottom:=P₀.length+Proc.any0)
    ⟨hParams,hLog2,hPrimes,L (i:=Proc.fill) rfl,L (i:=Proc.pick) rfl,hNodes,L (i:=Proc.leaf) rfl,
      by intro i hi; interval_cases i <;> first | exact L (i:=Proc.any0) rfl | exact L (i:=Proc.any1) rfl | exact L (i:=Proc.any2) rfl | exact L (i:=Proc.any3) rfl⟩
    (L (i:=Proc.core) rfl)
  exact host_spec hCore hpre hok

end Light.Sec3.ChanHe
