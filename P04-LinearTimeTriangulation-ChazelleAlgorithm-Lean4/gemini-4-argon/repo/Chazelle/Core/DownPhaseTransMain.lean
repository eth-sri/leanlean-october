module

public import Chazelle.Core.DownPhaseTransWt

/-!
# WP-M (T, part 7): the transition theorem

For a simple polygon `Q` with distinct vertex heights and its top chain `C`, a chord family `F₀`
of `chainModel C` that is `γ`-semigranular with degree at most `D` gives, by clipping its chords
to the interior of `Q` (`pieces Q F₀`), a chord family of the interior model (T1) with degree at
most `D` (T2), weight at most `2γ + 1` (T3) and at most `|F₀|` chords (T4) (`transition`).
-/

namespace Chazelle.Core

namespace Trans

@[expose] public section

variable {Q : Polygon} {C : Chain}

/-- **(T3) Semigranularity after the transition.** -/
theorem semigranular_pieces (hQ : Q.Simple) (T : Top Q C) (hD : DistinctH Q)
    {F₀ : Set (Set Point)} (hF₀ : (chainModel C).ChordFamily C.P F₀) {γ : ℕ}
    (hγ : (chainModel C).Semigranular F₀ γ) :
    (interiorModel Q).Semigranular (pieces Q F₀) (2 * γ + 1) := by
  have hP : C.P.Simple := by rwa [T.hP]
  obtain ⟨c₀, h6, hle, hvtx⟩ := exists_shift hQ T hD
  have H : Shift Q C c₀ := ⟨h6, hle, hvtx⟩
  intro V hV
  obtain ⟨U, hU, hVU⟩ := exists_chain_region hQ T hF₀.2.1 hV
  apply csSup_le'
  rintro _ ⟨⟨a, b⟩, hab, rfl⟩
  have := arcWt_le_trans H T hQ hP hF₀.2.1 hF₀.1 hU hVU hab
  have hw := hγ U hU
  simp only at this ⊢
  omega

/-- **The transition** (T1–T4). -/
theorem transition (hQ : Q.Simple) (T : Top Q C) (hD : DistinctH Q)
    {F₀ : Set (Set Point)} (hF₀ : (chainModel C).ChordFamily C.P F₀) {γ d : ℕ}
    (hγ : (chainModel C).Semigranular F₀ γ) (hd : (chainModel C).DegLe F₀ d) :
    (interiorModel Q).ChordFamily Q (pieces Q F₀) ∧
      (interiorModel Q).DegLe (pieces Q F₀) d ∧
      (interiorModel Q).Semigranular (pieces Q F₀) (2 * γ + 1) ∧
      (pieces Q F₀).ncard ≤ F₀.ncard := by
  have hmn := T.hm
  have hm1 := C.one_le
  have hh : (Q.vtx C.m).2 ≠ (Q.vtx 0).2 := hD C.m 0 (by omega) (by omega) (by omega)
  obtain ⟨hfam, hcard⟩ := chordFamily_pieces T hF₀ hQ hh
  exact ⟨hfam, degLe_pieces hQ T hh hF₀ hd, semigranular_pieces hQ T hD hF₀ hγ, hcard⟩

end

end Trans

end Chazelle.Core
