module

public import Chazelle.Core.DownPhaseMathWalk

/-!
# Down phase, math (H-R1): the symbolic points the driver writes for one arc

For a region `r` of `N = buildNF I Q L E` (`RegCtx`): the point `DrvR.ptI li n x isEnd` written
for a chord position `x` represents its host key when `isEnd` is set exactly at arc ends
(`ptSym_rep`; `start_rep`, `end_rep`, `junc_rep`), and the run items of an arc represent its inner
walk vertices (`run_rep`).
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost
open BuildNF (buildNF)
open DrvR (ivB qE atVtx partner ptI runCnt runItems arcItems walkItems regHost)

/-- **The setting of a region record of `buildNF`** (the hypotheses of `DrvR.HostR1Spec`). -/
structure RegCtx (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (reg : ℕ → Set Point)
    (r : ℕ) : Prop where
  hQ : Q.Simple
  hdh : DistinctHeights Q
  hL : ChordTriplesOK (interiorModel Q) Q L
  hperm : E.Perm (List.range (2 * L.length))
  hsort : E.Pairwise (BuildNF.codeLe (interiorModel Q) Q L)
  hK : 0 < L.length
  hregs : Restore.NFRegs (interiorModel Q) Q (buildNF (interiorModel Q) Q L E) reg
  hr : r < (buildNF (interiorModel Q) Q L E).nRegions

section
variable (li : Bool) (n : ℕ) (x : WPos) (isEnd : Bool)
include li n x isEnd
/-- The symbolic point inside `DrvR.ptI`. -/
def ptSym : SymPt :=
  .onEdge (qE li n (if isEnd && atVtx li n x then (x.edge + n - 1) % n else x.edge)) (x.hgt - 1)

theorem ptI_eq :
    ptI li n x isEnd = .pt (ptSym li n x isEnd) := rfl


end

variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point} {r : ℕ}

/-- An arc end is preceded by an arc gap. -/
theorem arcGap_prev_of_end {S : Set (Set Point)} {R : Set Point} (hQ : Q.Simple)
    (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
    (hR : R ∈ (interiorModel Q).regions S) {i : ℕ} (hi : i < nk (interiorModel Q) S R) {a : ℝ}
    (harc : (interiorModel Q).IsArc S R a (hk (interiorModel Q) S R i)) :
    ArcGap (interiorModel Q) S R (prevIdx (nk (interiorModel Q) S R) i) := by
  have hM : WalkAx (interiorModel Q) := walkAx_interiorModel hQ
  have h3 := three_le_nk hQ hFam hne hR
  obtain ⟨i_l, d, hD⟩ := arc_keys hM hFam.2.1 hFam.1 hne hR harc
  have hidx := hk_inj hM hFam.2.1 hFam.1 (Nat.mod_lt _ (by omega)) hi hD.hr
  have hd0 := hD.hd0
  have e : prevIdx (nk (interiorModel Q) S R) i = (i_l + (d - 1)) % nk (interiorModel Q) S R := by
    have h1 : i = ((i_l + (d - 1)) % nk (interiorModel Q) S R + 1) % nk (interiorModel Q) S R := by
      grind
    rw [h1]; exact prevIdx_succ (Nat.mod_lt _ (by omega))
  rw [e]
  exact arcData_gap hQ hFam hne hR harc hD (by omega)

/-- **The symbolic point of a chord position represents its host key**, when `isEnd` marks
exactly the vertex keys after an arc gap. -/
theorem ptSym_rep {N : NF} {R : Set Point} (hN : IsNF (interiorModel Q) Q N)
    (hdh : DistinctHeights Q) {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) {x : WPos}
    (hx : ChordPos N x) {i : ℕ}
    (hki : hk (interiorModel Q) (N.F (interiorModel Q) Q) R i = (interiorModel Q).key Q x)
    (hex : hk (interiorModel Q) (N.F (interiorModel Q) Q) R i ∈
      exitKeys (interiorModel Q) (N.F (interiorModel Q) Q) R)
    {isEnd : Bool}
    (hend : (interiorModel Q).key Q x = ⌊(interiorModel Q).key Q x⌋₊ →
      (isEnd = true ↔ ArcGap (interiorModel Q) (N.F (interiorModel Q) Q) R
        (prevIdx (nk (interiorModel Q) (N.F (interiorModel Q) Q) R) i))) :
    RepPt li Q (N.F (interiorModel Q) Q) R i (ptSym li Q.n x isEnd) := by
  obtain ⟨c, hc, hxc⟩ := hx
  obtain ⟨-, hA, ek, eh, hh, hy⟩ := chordPos_attach hN hc hxc
  have hfl : ⌊(interiorModel Q).key Q x⌋₊ = x.edge := by rw [ek, floor_add hA.2.1 hA.2.2.1]
  right
  refine ⟨hex, x.hgt - 1, by omega, ?_, ?_⟩
  · rw [hki, ek, hostPt_eq _ hA.2.1 hA.2.2.1, eh, Nat.add_sub_cancel]; simp_all
  · rw [hki]
    by_cases hb : (isEnd && atVtx li Q.n x) = true
    · have hb' := hb
      simp only [Bool.and_eq_true] at hb'
      have hint := (atVtx_iff hN hdh hli ⟨c, hc, hxc⟩).1 hb'.2
      left
      refine ⟨hint, (hend hint).1 hb'.1, ?_⟩
      unfold ptSym; rw [ite_eq_left hb, hfl]
    · right
      refine ⟨fun ⟨hint, hAp⟩ => hb ?_, ?_⟩
      · simp only [Bool.and_eq_true]
        exact ⟨(hend hint).2 hAp, (atVtx_iff hN hdh hli ⟨c, hc, hxc⟩).2 hint⟩
      grind [ptSym]

end

end DownMath

end Chazelle.Core
