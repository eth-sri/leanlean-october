module

public import Chazelle.Core.DownPhaseMathGroup

/-!
# Down phase, math (H-R1): the exit chord after an arc end, and `DrvR.partner`

For a region `R` of `S = N.F` (`N` a normal form of the interior model, `RC` the exit-chord list of
its region record):

* `exit_record`: the end of an arc of `R` is an end of an exit chord record of the region;
* `partner_key`: `DrvR.partner` at the end of an arc returns a chord position whose key is the host
  key after the end (an exit key).
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost
open DrvR (partner)

variable {Q : Polygon} {N : NF} {R : Set Point} {r : ℕ}

/-- Three attachment keys of one chord, two of them distinct, the third distinct from the first:
the third is the second. -/
theorem attach_third {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {x y z : ℝ}
    (hx : x ∈ DownDrv.attachKeys M c) (hy : y ∈ DownDrv.attachKeys M c)
    (hz : z ∈ DownDrv.attachKeys M c) (hxy : x ≠ y) (hzx : z ≠ x) : z = y := by
  obtain ⟨k₁, k₂, hsub⟩ := DownDrv.attachKeys_sub hM hc
  have m0 := hsub hx
  have m1 := hsub hy
  have m2 := hsub hz
  simp only [mem_insert_iff, mem_singleton_iff] at m0 m1 m2
  rcases m0 with e0 | e0 <;> rcases m1 with e1 | e1 <;> rcases m2 with e2 | e2
  all_goals first
    | exact (hxy (e0.trans e1.symm)).elim
    | exact (hzx (e2.trans e0.symm)).elim
    | exact e2.trans e1.symm

variable (hQ : Q.Simple) (hdh : DistinctHeights Q) (hN : IsNF (interiorModel Q) Q N)
  (hne : (N.F (interiorModel Q) Q).Nonempty)
  (hR : R ∈ (interiorModel Q).regions (N.F (interiorModel Q) Q))
  (hRC : ∀ i, i ∈ (N.region r).chords ↔
    i < N.nChords ∧ TouchesIn (interiorModel Q).D ((N.chord i).toSet (interiorModel Q) Q) R)

/-- A chord of `N.F` is a chord record. -/
theorem chord_of_mem {c : Set Point} (hc : c ∈ N.F (interiorModel Q) Q) :
    ∃ i, i < N.nChords ∧ c = (N.chord i).toSet (interiorModel Q) Q := by
  obtain ⟨rc, hrc, rfl⟩ := hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrc
  exact ⟨i, hi, by unfold NF.chord; rw [List.getD_eq_getElem _ _ hi]⟩

include hQ hdh hN hne hR hRC in
/-- **The end of an arc is an end of an exit chord record of the region.** -/
theorem exit_record {x : WPos} (hx : ChordPos N x) {a : ℝ}
    (harc : (interiorModel Q).IsArc (N.F (interiorModel Q) Q) R a ((interiorModel Q).key Q x)) :
    ∃ i ∈ (N.region r).chords, x = (N.chord i).lpos ∨ x = (N.chord i).rpos := by
  have hM : WalkAx (interiorModel Q) := walkAx_interiorModel hQ
  obtain ⟨c, ⟨hc, ht⟩, p, t, hA, he⟩ := hM.exists_exit_at_end hN.1.2.1 hN.1.1 hne hR harc
  obtain ⟨i, hi, rfl⟩ := chord_of_mem hc
  refine ⟨i, (hRC i).2 ⟨hi, ht⟩, ?_⟩
  obtain ⟨-, hAl, ekl, -, -, -⟩ := chordPos_attach hN hi (Or.inl rfl)
  obtain ⟨-, hAr, ekr, -, -, -⟩ := chordPos_attach hN hi (Or.inr rfl)
  have hxk : (interiorModel Q).key Q x ∈ DownDrv.attachKeys (interiorModel Q)
      ((N.chord i).toSet (interiorModel Q) Q) := ⟨p, t, hA, he⟩
  have hlk : (interiorModel Q).key Q (N.chord i).lpos ∈ DownDrv.attachKeys (interiorModel Q)
      ((N.chord i).toSet (interiorModel Q) Q) := ⟨_, _, hAl, ekl⟩
  have hrk : (interiorModel Q).key Q (N.chord i).rpos ∈ DownDrv.attachKeys (interiorModel Q)
      ((N.chord i).toSet (interiorModel Q) Q) := ⟨_, _, hAr, ekr⟩
  have hlr := chordPos_ne hN hM hi
  by_cases hxl : (interiorModel Q).key Q x = (interiorModel Q).key Q (N.chord i).lpos
  · exact Or.inl (chordPos_eq hN hdh hx ⟨i, hi, Or.inl rfl⟩ hxl)
  · have := attach_third hM (hN.1.2.1 hc) hlk hrk hxk hlr hxl
    exact Or.inr (chordPos_eq hN hdh hx ⟨i, hi, Or.inr rfl⟩ this)

include hQ hdh hN hne hR hRC in
/-- **`DrvR.partner` at the end of an arc**: a chord position whose key is the host key after the
end, which is an exit key. -/
theorem partner_key {x : WPos} (hx : ChordPos N x) {m : ℕ}
    (hm : m < nk (interiorModel Q) (N.F (interiorModel Q) Q) R)
    (hkm : hk (interiorModel Q) (N.F (interiorModel Q) Q) R m = (interiorModel Q).key Q x)
    {a : ℝ}
    (harc : (interiorModel Q).IsArc (N.F (interiorModel Q) Q) R a ((interiorModel Q).key Q x)) :
    ChordPos N (partner N r x) ∧
      (interiorModel Q).key Q (partner N r x) =
        hk (interiorModel Q) (N.F (interiorModel Q) Q) R
          ((m + 1) % nk (interiorModel Q) (N.F (interiorModel Q) Q) R) ∧
      hk (interiorModel Q) (N.F (interiorModel Q) Q) R
          ((m + 1) % nk (interiorModel Q) (N.F (interiorModel Q) Q) R) ∈
        exitKeys (interiorModel Q) (N.F (interiorModel Q) Q) R := by
  have hM : WalkAx (interiorModel Q) := walkAx_interiorModel hQ
  have h3 := three_le_nk hQ hN.1 hne hR
  obtain ⟨i₀, hi₀, hcases⟩ := partner_spec (exit_record hQ hdh hN hne hR hRC hx harc)
  obtain ⟨hi₀n, ht₀⟩ := (hRC i₀).1 hi₀
  set c₀ := (N.chord i₀).toSet (interiorModel Q) Q
  obtain ⟨hc₀S, hAl, ekl, -, -, -⟩ := chordPos_attach hN hi₀n (Or.inl rfl)
  obtain ⟨-, hAr, ekr, -, -, -⟩ := chordPos_attach hN hi₀n (Or.inr rfl)
  -- the chord is attached at `x` and at the partner
  obtain ⟨hAx, hAp, ekx, ekp, hxp⟩ : ∃ (_ : SideAttach (interiorModel Q).W c₀ x.edge
        ((interiorModel Q).param Q x))
      (_ : SideAttach (interiorModel Q).W c₀ (partner N r x).edge
        ((interiorModel Q).param Q (partner N r x))),
      (interiorModel Q).key Q x = x.edge + (interiorModel Q).param Q x ∧
      (interiorModel Q).key Q (partner N r x) =
        (partner N r x).edge + (interiorModel Q).param Q (partner N r x) ∧
      (interiorModel Q).key Q x ≠ (interiorModel Q).key Q (partner N r x) := by
    rcases hcases with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
    · rw [hp]; exact ⟨hAl, hAr, ekl, ekr, chordPos_ne hN hM hi₀n⟩
    · rw [hp]; exact ⟨hAr, hAl, ekr, ekl, (chordPos_ne hN hM hi₀n).symm⟩
  have hpos : ChordPos N (partner N r x) := by
    rcases hcases with ⟨-, hp⟩ | ⟨-, hp⟩
    · exact ⟨i₀, hi₀n, Or.inr hp⟩
    · exact ⟨i₀, hi₀n, Or.inl hp⟩
  -- after the end: the chord continues to the next host key
  have hex : hk (interiorModel Q) (N.F (interiorModel Q) Q) R m ∈
      exitKeys (interiorModel Q) (N.F (interiorModel Q) Q) R :=
    ⟨c₀, hc₀S, ht₀, _, _, hAx, by rwa [hkm]⟩
  have hAp' := DownMath.arcGap_prev_of_end hQ hN.1 hne hR hm (by rwa [hkm])
  obtain ⟨-, hnext⟩ := end_chord hQ hN.1 hne hR hm hex hAp'
  obtain ⟨p', t', hA', he'⟩ := hnext c₀ hc₀S ht₀ _ _ hAx (by rwa [hkm])
  have hz : hk (interiorModel Q) (N.F (interiorModel Q) Q) R
      ((m + 1) % nk (interiorModel Q) (N.F (interiorModel Q) Q) R) =
      (interiorModel Q).key Q (partner N r x) := by
    apply attach_third hM (hN.1.2.1 hc₀S) ⟨_, _, hAx, ekx⟩ ⟨_, _, hAp, ekp⟩ ⟨p', t', hA', he'⟩
      hxp
    rw [← hkm]
    exact (hk_succ_ne hM hN.1.2.1 hN.1.1 (by omega) hm).symm
  exact ⟨hpos, hz.symm, ⟨c₀, hc₀S, ht₀, p', t', hA', he'⟩⟩

end

end DownMath

end Chazelle.Core
