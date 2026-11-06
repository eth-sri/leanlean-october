module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvXContracts
public import Chazelle.Core.DownPhaseDrvXPos2
public import Chazelle.Core.DownPhaseDrvXKept

/-!
# Down phase, extraction (D6): glue A

**`xeGlue : XEGlue`**: from the precondition of `DrvR.ExtractRamSpec`, the facts `XE` of the run
(values `xvOf`, arc list `rasOf`) and the set-up facts `SetupFacts`.

* memory facts: `NFAt`, `HostAt`, `ChainDescAt` through `Robust`, bounds by `Restore.nf_bounds`;
* the model descriptor describes a chain (`Restore.chainModel_ne_interior`), so `ChainWF` gives
  `HostWF` and `≤ 64` host items;
* the arcs of `N`: `XHyp.arc_facts`, `DownMath.regArcs_facts`;
* the kept chords: `XCtx.kept_iff`, `XCtx.kept_pos`, `onArc_iff`;
* the record ends of `N_R`: `XCtx.chord_data` (`lp, rp < 2 m + 7`).
-/

namespace Chazelle.Core

namespace DrvX

open Machine BuildNF
open DrvR (regHost OnArcKey)

@[expose] public section

/-- An empty region has an empty host. -/
theorem ga_regHost_nil (li : Bool) (n : ℕ) (N : NF) (r : ℕ) (h : (N.region r).arcs.length = 0) :
    regHost li n N r = [] := by
  unfold regHost DrvR.walkItems
  Ξ h
  split_ifs <;> simp

/-- An end on an arc of the region is on one of the arcs of the arc list, by comparisons. -/
theorem ga_onArc {P : Polygon} {li : Bool} {N : NF} {r : ℕ}
    (hli : li = true ↔ Mountain.LeftInside (Qof P)) (hdh : DistinctHeights (Qof P))
    (hn : 2 ≤ (Qof P).n)
    (hgood : ∀ j, j < N.arcs.length → GoodPos (Qof P) (N.arc j).s ∧ GoodPos (Qof P) (N.arc j).e)
    (hras : ∀ t, t < (N.region r).arcs.length → (N.region r).arcs.getD t 0 < N.arcs.length)
    {x : WPos} (hx : GoodPos (Qof P) x) {j : ℕ} (hj : j ∈ (N.region r).arcs)
    (ho : OnArcKey (Qof P) N j x) :
    ∃ t, t < (N.region r).arcs.length ∧ OnArcP (Qof P) li N (rasOf N r t) x := by
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hj
  have e : rasOf N r t = (N.region r).arcs[t] := by
    unfold rasOf; rw [List.getD_eq_getElem _ _ ht]
  have hjA := hras t ht
  rw [List.getD_eq_getElem _ _ ht] at hjA
  refine ⟨t, ht, ?_⟩
  Ξ e
  exact (onArc_iff hli hdh hn hx (hgood _ hjA).1 (hgood _ hjA).2).1 ho


/-- **Glue A.** -/
theorem xeGlue : XEGlue := by
  intro P W c L E C NR hG hWh hb1 hbit hLne hok hperm hsort hdeg hNW hr hHost hHB hCP hCs hCm
    hMDwf hMDa hCDa hNRW hNR hroom
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hG.1
  have hdh : DistinctHeights (Qof P) := (goodShear_epsOf hG.2).2.1
  have hn : (Qof P).n = P.n := shear_n _ _
  have hn3 : 3 ≤ (Qof P).n := by have := hQ.1; omega
  have hWn : 256 * P.n + 16 ≤ W := hWh
  have hli : decide (c.nreg 217002 = 1) = true ↔ Mountain.LeftInside (Qof P) := by
    rw [decide_eq_true_iff]; exact hbit
  obtain ⟨-, -, -, reg, hRC, hCS, hAO, hRO, -⟩ := DownMath.isNF_build hQ hok hperm hsort
  have X : XHyp P (decide (c.nreg 217002 = 1)) L E reg (c.nreg 217001) C NR :=
    ⟨hG, hli, hLne, hok, hperm, hsort, ⟨hRC, hCS, hAO, hRO⟩, hr, hCP, hCs, hCm, hNR⟩
  obtain ⟨i0, g, Y⟩ := X.ctx
  obtain ⟨hgood, hinc, hnext, hfree⟩ := X.arc_facts
  obtain ⟨hras1, -, -⟩ := DownMath.regArcs_facts hQ hok hperm hsort X.hK X.hregs hr
  have hras : ∀ t, t < ((buildNF (interiorModel (Qof P)) (Qof P) L E).region (c.nreg 217001)).arcs.length →
      ((buildNF (interiorModel (Qof P)) (Qof P) L E).region (c.nreg 217001)).arcs.getD t 0 <
        (buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length := fun t ht => (hras1 t ht).1
  -- memory
  have hNat := hNW.holds
  have hNRat := hNRW.holds
  obtain ⟨b1, -, b3, b4, b5, -⟩ := Restore.nf_bounds hNW
  obtain ⟨c1, c2, -, -, -, -⟩ := Restore.nf_bounds hNRW
  unfold xKappa at hroom
  have hA0W : c.nreg ALLOC ≤ W := by omega
  have hK : c.nmem (c.nreg 217006) = NR.chords.length := hNRat.1
  -- the model descriptor is a chain descriptor
  have hMD0 : c.nmem (c.nreg 217005) = 0 := by
    rcases hMDa.holds with ⟨h0, -⟩ | ⟨-, -, hI⟩
    · exact h0
    · exact absurd hI (Restore.chainModel_ne_interior C _)
  have hCD := hCDa.holds
  obtain ⟨hlen64, hwfP, -, -⟩ := (hMDwf.2 hMD0).2 _ _ hCD
  have hwf : HostWF (Qof P).n (regHost (decide (c.nreg 217002 = 1)) (Qof P).n
      (buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001)) := by
    have h := hwfP; rwa [← hn] at h
  have hmp : C.m + 1 = ((regHost (decide (c.nreg 217002 = 1)) (Qof P).n
      (buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001)).pts (Qof P).n).length := by
    rw [hCm, hCP]; simp [Host.poly, Polygon.n]
  have hm1 := C.one_le
  have hptsle := Host.pts_length_le hwf
  have hptsle' : (regHost (decide (c.nreg 217002 = 1)) (Qof P).n
      (buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001)).length * (Qof P).n ≤
      64 * (Qof P).n := Nat.mul_le_mul_right _ hlen64
  -- the region has an arc
  have hnRA1 : 1 ≤ ((buildNF (interiorModel (Qof P)) (Qof P) L E).region (c.nreg 217001)).arcs.length := by
    by_contra h0
    have hnil := ga_regHost_nil (decide (c.nreg 217002 = 1)) (Qof P).n
      (buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001) (by omega)
    rw [hnil] at hmp
    simp [Host.pts] at hmp
  have hnRA32 := regHost_length_ge (decide (c.nreg 217002 = 1)) (Qof P).n
    (buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001)
  have hr' : c.nreg 217001 < (buildNF (interiorModel (Qof P)) (Qof P) L E).regions.length := hr
  have hreg4 := b4 _ hr
  have hRA := b5 _ hr _ (show ((buildNF (interiorModel (Qof P)) (Qof P) L E).region
    (c.nreg 217001)).arcs.length - 1 < _ by omega)
  have hA1 : 1 ≤ (buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length := by
    have := hras 0 (by omega); omega
  have hAB := b3 _ (show (buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length - 1 < _ by omega)
  refine ⟨⟨hG, hli, hdh, by omega, by rw [hn]; exact hWn, rfl, by show _ + 5 * NR.chords.length ≤ W; omega,
    fun mm hmm => hHost mm hmm, hwf, hlen64, hHB, hm1, hmp, C.topIdx_le, ?_, ?_, ?_, rfl,
    fun j hj => hgood j hj, hinc, hnext, hfree, ?_, ?_, fun t ht => hras t ht, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl⟩, ?_⟩
  · -- the chord records of `N_R`
    intro mm hmm i hi
    have h := ((hNRW mm hmm).2.2.2.2.2.1 i hi)
    rw [hmm (c.nreg 217006 + 3) (by omega)] at h
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · intro i hi; exact c2 i hi
  · intro i hi
    obtain ⟨A, B, hAB, hc, hh, hadm, hl, hrr, hzl, hzr⟩ := Y.chord_data hi
    have h1 := hl.1
    have h2 := hrr.1
    rw [C.sideWalk_n] at h1 h2
    exact ⟨by omega, by show _ ≤ 2 * C.m + 6; omega, by show _ ≤ 2 * C.m + 6; omega⟩
  · -- the arc records of `N`
    intro mm hmm j hj
    have h := ((hNW mm hmm).2.2.2.2.2.2.1 j hj)
    rw [hmm (c.nreg 217000 + 4) (by omega)] at h
    exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · -- the arc list of the region
    intro mm hmm t ht
    have h := ((hNW mm hmm).2.2.2.2.2.2.2.1 _ hr').2.2.2.1 t ht
    rw [hmm (c.nreg 217000 + 5) (by omega), hmm (c.nreg 217000 + 7) (by omega),
      hmm (c.nmem (c.nreg 217000 + 5) + 5 * c.nreg 217001 + 1) (by omega)] at h
    exact h
  · intro j hj; exact b3 j hj
  · show (c.nmem (c.nreg 217000 + 7) + c.nmem (c.nmem (c.nreg 217000 + 5) + 5 * c.nreg 217001 + 1)) + ((buildNF (interiorModel (Qof P)) (Qof P) L E).region (c.nreg 217001)).arcs.length ≤ c.nreg ALLOC; omega
  · show ((buildNF (interiorModel (Qof P)) (Qof P) L E).region (c.nreg 217001)).arcs.length ≤ 32; omega
  · show 2 * (buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length + 2 ≤ W; omega
  · -- the kept chords
    intro i hi hk
    have hkeep := (Y.kept_iff hi).1 hk
    obtain ⟨-, -, -, hpl, hpr, ⟨j1, hj1, ho1⟩, ⟨j2, hj2, ho2⟩⟩ := Y.kept_pos hi hkeep
    have hgp : ∀ p, ProperPos (interiorModel (Qof P)) (Qof P) (Qof P).n
        (xPos (Qof P).n (regHost (decide (c.nreg 217002 = 1)) (Qof P).n
          (buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001)) (decide (c.nreg 217002 = 1))
          C.m C.topIdx C.sideBeta (NR.chord i).h p) →
        GoodPos (Qof P) (xPos (Qof P).n (regHost (decide (c.nreg 217002 = 1)) (Qof P).n
          (buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 217001)) (decide (c.nreg 217002 = 1))
          C.m C.topIdx C.sideBeta (NR.chord i).h p) := fun p hp => by
      refine ⟨hp, by simp [xPos], ?_⟩
      show pEdge _ _ _ < _
      refine pEdge_lt _ (hpt_lt hwf (by omega) ?_)
      have := tK_le C.sideBeta hm1 (T := C.topIdx) p
      omega
    exact ⟨hgp _ hpl, hgp _ hpr, ga_onArc hli hdh (by omega) hgood hras (hgp _ hpl) hj1 ho1,
      ga_onArc hli hdh (by omega) hgood hras (hgp _ hpr) hj2 ho2⟩
  · -- the set-up facts
    refine ⟨hCD.2.2.2.1, hCD.2.2.2.2.1, hCD.2.2.2.2.2, (hHost.holds).1, hK, hNat.2.1,
      ((hNat.2.2.2.2.2.2.2.1 _ hr').1), by omega, by have := hMDwf.1; omega, ?_, by omega,
      by omega, by omega, by omega, by show (c.nmem (c.nreg 217000 + 7) + c.nmem (c.nmem (c.nreg 217000 + 5) + 5 * c.nreg 217001 + 1)) ≤ W; omega, by omega⟩
    omega

end

end DrvX

end Chazelle.Core
