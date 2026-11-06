module

public import Chazelle.Core.NFBuildCmp
public import Chazelle.Core.NFLocateSpec

/-!
# WP-C (BuildNF): the reduction of `BuildNFSpec` to its RAM part

`BuildNFRamSpec` is `BuildNFSpec` with the mathematical content removed: the procedure must write
the layout of `buildNF M Q L E` (`NFWithin`) for **some** ordering `E` of the event codes that is
sorted by the comparator `codeLe` (one walk-key comparison and one tie bit).  All geometric and
combinatorial facts are proved (`BuildNF.isNF_goodModel`), so:

* `buildNFSpec_of_ram : BuildNFRamSpec → BuildNFSpec`.

The open part of WP-C/BuildNF is `BuildNFRamSpec` itself: sort the `2K` event codes with
`SortR.sortStmt` and a comparator procedure implementing `codeLe` (`WalkKey.keyCmp` on the two
walk positions `wposOf`, then `WalkKey.dirCode` of the walk edge for the tie bit), run the stack
pass of `BuildStack.run` over the chord word (which computes `outside i` and the labels
`label w (m + 1)` of the gaps), compare consecutive keys to find the gap starts, bucket the arcs
and exit chords by region, compute the weights with the closed form `arcWtNat` (`NFBuildWt`), and
write the layout, within `κ (K (⌈log₂ K⌉ + 1) + 1)` steps.
-/

namespace Chazelle.Core

namespace BuildNF

@[expose] public section

open Chazelle.Machine (Stmt)

/-- **The RAM part of `BuildNFSpec`**: the procedure writes the computed normal form of a sorted
ordering of the event codes. -/
def BuildNFRamSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s {bBuild, bSort, bSign}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bBuild 0) ∧
      ∃ M L, ModelDescAt c.nmem (rd c bBuild 0) (Qof P) M ∧
      GoodModel M ∧ rd c bBuild 2 = L.length ∧ rd c bBuild 1 + 3 * L.length ≤ c.nreg ALLOC ∧
      ChordListAt c.nmem (rd c bBuild 1) L ∧ ChordTriplesOK M (Qof P) L)
    (fun P c c' => ∀ M L, ModelDescAt c.nmem (rd c bBuild 0) (Qof P) M →
      rd c bBuild 2 = L.length → ChordListAt c.nmem (rd c bBuild 1) L →
        ∃ E : List ℕ, E.Perm (List.range (2 * L.length)) ∧ E.Pairwise (codeLe M (Qof P) L) ∧
          c.nreg ALLOC ≤ rd c' bBuild 3 ∧
          NFWithin c'.nmem (rd c' bBuild 3) (c'.nreg ALLOC) (buildNF M (Qof P) L E))
    (fun _ c => κ * (rd c bBuild 2 * (Nat.clog 2 (rd c bBuild 2) + 1) + 1))

/-- A chord list in memory is determined by its length. -/
theorem chordListAt_unique {m : ℕ → ℕ} {A : ℕ} {L L' : List (ℕ × ℕ × ℕ)} (h : ChordListAt m A L)
    (h' : ChordListAt m A L') (hlen : L.length = L'.length) : L = L' := by
  apply List.ext_getElem hlen
  intro i hi hi'
  obtain ⟨a1, a2, a3⟩ := h i hi
  obtain ⟨b1, b2, b3⟩ := h' i hi'
  have e1 : L.getD i (0, 0, 0) = L[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have e2 : L'.getD i (0, 0, 0) = L'[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  rw [e1] at a1 a2 a3
  rw [e2] at b1 b2 b3
  exact Prod.ext (a1.symm.trans b1) (Prod.ext (a2.symm.trans b2) (a3.symm.trans b3))

/-- **The reduction**: the RAM part implies `BuildNFSpec`. -/
theorem buildNFSpec_of_ram (hram : BuildNFRamSpec) : BuildNFSpec := by
  obtain ⟨s, κ, hs⟩ := hram
  refine ⟨s, κ, fun P W c hw hpre hcost => ?_⟩
  obtain ⟨c', k, hexec, hk, hpost, hframe⟩ := hs P W c hw hpre hcost
  refine ⟨c', k, hexec, hk, fun M L hM hlen hL => ?_, hframe⟩
  obtain ⟨-, -, -, M₀, L₀, hM₀, hgood, hlen₀, -, hL₀, hok⟩ := hpre
  obtain rfl := NFLoc.modelDesc_unique hM₀ hM
  obtain rfl := chordListAt_unique hL₀ hL (hlen₀.symm.trans hlen)
  obtain ⟨E, hperm, hsort, hB, hN⟩ := hpost M₀ L₀ hM hlen hL
  obtain ⟨hnf, hch, hdec⟩ := isNF_goodModel hgood hok hperm hsort
  exact ⟨buildNF M₀ (Qof P) L₀ E, hB, hN, hnf, hch, hdec⟩

end

end BuildNF

end Chazelle.Core
