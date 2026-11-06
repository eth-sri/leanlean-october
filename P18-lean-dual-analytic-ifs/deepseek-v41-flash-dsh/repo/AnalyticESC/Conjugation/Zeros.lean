module

public import AnalyticESC.Conjugation.Basic

@[expose] public section

/-!
# Conjugacies by injective analytic maps

Two facts about an analytic map `g` that is injective on `[0,1]` and conjugates contractions of
`[0,1]` to affine maps: `g'` has no zero in `[0,1]` once two of the maps have distinct fixed
points, and maps with a common fixed point commute.
-/

namespace AnalyticESC

open Set Filter Topology

/-- Two maps of `[0,1]` with a common fixed point that are conjugated by an injective `g` to
affine maps commute on `[0,1]`. -/
theorem comp_comm_of_conj {F G g : ℝ → ℝ} (hinj : InjOn g I) (hF : MapsTo F I I)
    (hG : MapsTo G I I) {a b s t : ℝ} (hgF : ∀ x ∈ I, g (F x) = a * g x + s)
    (hgG : ∀ x ∈ I, g (G x) = b * g x + t) {p : ℝ} (hp : p ∈ I) (hFp : F p = p) (hGp : G p = p) :
    ∀ x ∈ I, F (G x) = G (F x) := by
  intro x hx
  have hs : g p = a * g p + s := by simpa only [hFp] using hgF p hp
  have ht : g p = b * g p + t := by simpa only [hGp] using hgG p hp
  refine hinj (hF (hG hx)) (hG (hF hx)) ?_
  rw [hgF _ (hG hx), hgG _ (hF hx), hgG x hx, hgF x hx]
  linear_combination (1 - a) * ht - (1 - b) * hs
