module

public import Chazelle.Core.DownPhaseDrvRHostSpec
public import Chazelle.Core.DownPhaseMathRec
public import Chazelle.Core.DownPhaseMathHost
public import Chazelle.Core.GranNF
public import Chazelle.Core.RestoreTRead

/-!
# Down-phase driver, host RAM (D3a), part 1: the facts about the region

For region `r` of `N = buildNF I Q L E` (interior model `I` of `Q`, valid sorted input, at least
one chord, degree `≤ 4`), the host RAM only needs the combinatorial facts `HFacts Q.n N r`:

* the region lists at most `5` arcs and at most `4` exit chords (`region_arcs_le_of`, the
  alternation of arcs and exit chords, `WalkAx.arcs_bound`);
* its arcs and exit chords are valid record indices;
* the ends of its arcs and of its exit chords lie on walk edges `< n`, at height codes `≤ n`
  (they are chord positions, `DownMath.arc_pos`, `DownMath.chordPos_attach`).

`hfacts_of` proves them from the precondition of `DrvR.HostRamSpec`.
-/

namespace Chazelle.Core

namespace DrvH

@[expose] public section

open DrvR

/-- **The facts about region `r` of `N`** used by the host RAM. -/
structure HFacts (n : ℕ) (N : NF) (r : ℕ) : Prop where
  hr : r < N.nRegions
  hA : (N.region r).arcs.length ≤ 5
  hK : (N.region r).chords.length ≤ 4
  harc : ∀ j ∈ (N.region r).arcs, j < N.arcs.length ∧ (N.arc j).s.edge < n ∧
    (N.arc j).s.hgt ≤ n ∧ (N.arc j).e.edge < n ∧ (N.arc j).e.hgt ≤ n
  hch : ∀ i ∈ (N.region r).chords, i < N.nChords ∧ (N.chord i).lp < n ∧ (N.chord i).rp < n ∧
    (N.chord i).h + 1 ≤ n

/-- **A region lists at most five arcs** (degree `≤ 4`; any model satisfying the walk axioms). -/
theorem region_arcs_le_of {M : Model} {Q : Polygon} {N : NF} (hM : WalkAx M) (hN : IsNF M Q N)
    (hdeg : M.DegLe (N.F M Q) 4) {r : ℕ} (hr : r < N.regions.length) :
    (N.region r).arcs.length ≤ 5 := by
  classical
  obtain ⟨hF, -, -, reg, hR, -, hA, hRs, -⟩ := hN
  have hU : reg r ∈ M.regions (N.F M Q) := hR.1 r hr
  have hnd := (hRs r hr).2.2.1
  set L := (N.region r).arcs
  set f : ℕ → ℝ × ℝ := fun j => (M.key Q (N.arc j).s, M.key Q (N.arc j).e)
  have hmem : ∀ j ∈ L, j < N.arcs.length ∧ (N.arc j).reg = r := fun j hj => (hA.2.2.2 r hr j).1 hj
  have hinj : Set.InjOn f {j | j ∈ L} := by
    intro j hj j' hj' hjj
    obtain ⟨h1, h2⟩ := hmem j hj
    obtain ⟨h1', h2'⟩ := hmem j' hj'
    exact hA.2.1 j j' h1 h1' (h2.trans h2'.symm) (congrArg Prod.fst hjj)
  have hsub : f '' {j | j ∈ L} ⊆ {ab : ℝ × ℝ | M.IsArc (N.F M Q) (reg r) ab.1 ab.2} := by
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨h1, h2⟩ := hmem j hj
    have := (hA.1 j h1).2
    grind
  obtain ⟨hfin, hcard⟩ := hM.arcs_bound hF.2.1 hF.1 hU
  have hdg := hdeg _ hU
  have hL : L.length = ({j | j ∈ L} : Set ℕ).ncard := by
    rw [show ({j | j ∈ L} : Set ℕ) = ↑L.toFinset by ext; simp, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup hnd]
  have h1 : ({j | j ∈ L} : Set ℕ).ncard = (f '' {j | j ∈ L}).ncard :=
    (Set.InjOn.ncard_image hinj).symm
  have h2 := Set.ncard_le_ncard hsub hfin
  omega

/-- **The facts about region `r`** of the interior normal form `buildNF I Q L E`. -/
theorem hfacts_of {Q : Polygon} (hQ : Q.Simple) {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    (hLne : L ≠ []) (hL : ChordTriplesOK (interiorModel Q) Q L)
    (hperm : E.Perm (List.range (2 * L.length)))
    (hsort : E.Pairwise (BuildNF.codeLe (interiorModel Q) Q L))
    (hdeg : (interiorModel Q).DegLe
      ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) 4) {r : ℕ}
    (hr : r < (BuildNF.buildNF (interiorModel Q) Q L E).nRegions) :
    HFacts Q.n (BuildNF.buildNF (interiorModel Q) Q L E) r := by
  set N := BuildNF.buildNF (interiorModel Q) Q L E with hNdef
  have hK : 0 < L.length := List.length_pos_iff_exists_mem.2 (List.exists_mem_of_ne_nil _ hLne)
  have hN : IsNF (interiorModel Q) Q N := DownMath.isNF_build hQ hL hperm hsort
  have hM : WalkAx (interiorModel Q) := walkAx_interiorModel hQ
  have hpos : ∀ x : WPos, DownMath.ChordPos N x → x.edge < Q.n ∧ x.hgt ≤ Q.n := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hx
    obtain ⟨-, hA, -, eh, hh, -⟩ := DownMath.chordPos_attach hN hi hxi
    exact ⟨DownMath.walk_n Q ▸ hA.1, by omega⟩
  obtain ⟨-, -, -, reg, hRC, -, hAO, hRO, -, hh, -⟩ := id hN
  refine ⟨hr, region_arcs_le_of hM hN hdeg hr, ?_, fun j hj => ?_, fun i hi => ?_⟩
  · rw [← Gran.deg_region hN hRC hRO hr]
    exact hdeg _ (hRC.1 r hr)
  · have hj' := ((hAO.2.2.2 r hr j).1 hj).1
    obtain ⟨hs, he⟩ := DownMath.arc_pos hQ hL hperm hsort hK hj'
    simp_all
  · have hi' := ((hRO r hr).1 i).1 hi |>.1
    have h1 := hpos _ ⟨i, hi', Or.inl rfl⟩
    have h2 := hpos _ ⟨i, hi', Or.inr rfl⟩
    exact ⟨hi', h1.1, h2.1, by simp_all⟩

end

end DrvH

end Chazelle.Core
