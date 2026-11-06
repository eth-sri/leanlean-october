module

public import Chazelle.Core.RestoreShoot

/-!
# WP-E, Lemma 3.2 part 11: the exit point avoids the walk edges at the origin

The ray shooter must not be asked to shoot at a subarc containing the origin (`ShooterOK`), so
local shooting from a walk point `z` removes from every arc of the region the walk edges through
the positions of `z` ("holes").  This file shows that the exit point of the ray is never on such an
edge: a walk edge containing both `z` and the exit point `w` would contain the segment `zw`, whose
interior is in the domain.

* `no_common_edge`: the points of a walk edge at parameters `t₁`, `t₂` cannot be the origin and
  the exit point of a ray whose open part lies in the domain.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set
open Chazelle.Chain (sidePt)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp point_ext)

variable {M : Model}

/-- **The exit point is not on a walk edge through the origin.** -/
theorem no_common_edge (hM : WalkAx M) {z : Point} {σ T : ℝ} (_hσ : σ = 1 ∨ σ = -1) (hT : 0 < T)
    (hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ M.D) {p : ℕ} (hp : p < M.W.n) {t₁ t₂ : ℝ}
    (ht₁ : 0 ≤ t₁) (ht₁1 : t₁ ≤ 1) (ht₂ : 0 ≤ t₂) (ht₂1 : t₂ ≤ 1)
    (hz : sidePt M.W p t₁ = z) (hw : sidePt M.W p t₂ = rayPt z σ T) : False := by
  have hmid : sidePt M.W p ((t₁ + t₂) / 2) = rayPt z σ (T / 2) := by
    have e1 := congrArg Prod.fst hz
    have e2 := congrArg Prod.snd hz
    have e3 := congrArg Prod.fst hw
    have e4 := congrArg Prod.snd hw
    unfold sidePt at *
    simp only [Geometry.lerp_fst, Geometry.lerp_snd, rayPt_fst, rayPt_snd] at *
    apply point_ext
    · simp only [Geometry.lerp_fst, rayPt_fst]; linarith
    · simp only [Geometry.lerp_snd, rayPt_snd]; linarith
  exact hM.trace p hp _ (by linarith) (by linarith) (hmid ▸ hdom (T / 2) (by linarith)
    (by linarith))

end

end Restore

end Chazelle.Core
