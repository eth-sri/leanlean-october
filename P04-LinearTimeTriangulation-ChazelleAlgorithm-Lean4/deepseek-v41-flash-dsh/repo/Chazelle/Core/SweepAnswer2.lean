module

public import Chazelle.Golf

public import Chazelle.Core.SweepDetect2

/-!
# The sweep (WP-D), part 15: answering queries along chords (gap S4)

The typical query of the fusion starts at an endpoint of a chord of `S₁` and runs along it; its
ray is in no region of `S₁` (and, for a collinear piece of `F₂⁺`, in no region of `F₂⁺`), so
`answer_of_label` does not apply.  The answer is assembled from one first hit per chain:

* `genuine_along_chord`: a ray from an endpoint of an admissible chord along it first leaves the
  domain at the other endpoint (read from the chord record, no shot);
* `genuine_of_region`: a ray starting in a region of a chord family is genuine at the first hit
  of the chain (and `firstHit_arcs` computes it by local shooting);
* `whole_of_genuine`, `whole_of_genuine_above`: the first hit of `C` is the earlier of the first
  hits of `C₁` and `C₂` (only `C₁` above the top of `C₂`), and the direction is free for `C`;
* `answer_of_label_gen`: `answer_of_label` with the part of `C₁` given by any set off the domain of
  `C₁` on which the ray first hits at the first hit of `C₁` (the arcs of the region of the ray, or
  the far end of the chord of `S₁` along the ray).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (point_ext)
open Chazelle.Merge (FreeAt)

namespace Sweep

section ChainModel

variable (C : Chain)

/-- **A ray along an admissible chord from one endpoint** first leaves the domain at the other
endpoint. -/
theorem genuine_along_chord {e : Set Point} (he : e ∈ Merge.augChords C) {z : Point}
    (hze : z ∈ e) (hzD : z ∉ C.dom) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hτ : 0 < τ)
    (hwe : rayPt z σ τ ∈ e) (hwD : rayPt z σ τ ∉ C.dom) : Genuine C z σ τ := by
  obtain ⟨y, l, r, hH, -, rfl, -, -⟩ := Merge.augChords_spec he
  obtain ⟨hzy, hzl, hzr⟩ := hze
  obtain ⟨-, hwl, hwr⟩ := hwe
  simp only [rayPt_fst] at hwl hwr
  have hend : ∀ x : ℝ, l ≤ x → x ≤ r → ((x, y) : Point) ∉ C.dom → x = l ∨ x = r := by
    intro x h1 h2 hx
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · exact absurd (hH.open_mem x h1 h2) hx
      · exact Or.inr h2
    · exact Or.inl h1.symm
  have hz := hend z.1 hzl hzr (by rw [show ((z.1, y) : Point) = z from Prod.ext rfl hzy.symm]; exact hzD)
  have hw := hend (z.1 + σ * τ) hwl hwr (by
    rw [show ((z.1 + σ * τ, y) : Point) = rayPt z σ τ from
      point_ext (⊚ rayPt) (⊚ rayPt, hzy)]; exact hwD)
  refine ⟨hτ, fun s h0 h1 => ?_, hwD⟩
  rw [show rayPt z σ s = ((z.1 + σ * s, y) : Point) from
    point_ext (⊚ rayPt) (⊚ rayPt, hzy)]
  have hlr := hH.lt
  apply hH.open_mem <;> rcases hσ with rfl | rfl <;> rcases hz with hz | hz <;>
    rcases hw with hw | hw <;> nlinarith

end ChainModel

section Junction

variable (J : Merge.Junction)

end Junction

end Sweep

end

end Chazelle.Core
