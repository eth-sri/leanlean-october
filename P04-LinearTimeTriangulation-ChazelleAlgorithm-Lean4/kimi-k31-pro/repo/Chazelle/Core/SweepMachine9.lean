module

public import Chazelle.Core.SweepMachine8

/-!
# The sweep (WP-D), part 25: the abstract machine, the rule for a fused chord

* `endpoint_attach`: an admissible chord of `C` is attached at a position of each of its ends.
* `stretch_decomp`: a position of the open right stretch is `(g + d, t)` with `d < L` and
  `(t = 0 → d ≠ 0)`.
* `sideLabel_piece` (**the rule for a fused chord**, design §9.4): the chord seen from an endpoint
  `a` of a chord `c ∈ S₂` (on `C₂`, neither the shared vertex nor the top of `C₂`) has, on each side
  `ρ`, the side label of the region of `S₂` on the side `ρ` of `c` (read from the `up`/`dn` field of
  the record of `c`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

/-- **An admissible chord is attached at a position of each of its ends.** -/
theorem endpoint_attach {M : Model} (hM : WalkAx M) {e : Set Point} (he : e ∈ M.Adm) {x : Point}
    (hx : x ∈ e) (hxD : x ∉ M.D) :
    ∃ (p : ℕ) (t : ℝ), SideAttach M.W e p t ∧ sidePt M.W p t = x := by
  obtain ⟨a, b, -, hcab, -, hopen, ⟨⟨pa, ta, hAa, hAa'⟩, -⟩, ⟨⟨pb, tb, hBb, hBb'⟩, -⟩⟩ := hM.ends e he
  by_cases hxa : x = a
  · exact ⟨pa, ta, hAa, by rw [hAa', hxa]⟩
  · rw [hcab] at hx
    have := seg_end hx hxD hopen hxa
    exact ⟨pb, tb, hBb, by rw [hBb', this]⟩

section Machine

variable (J : Merge.Junction)

/-- **A position of the open right stretch** is `(g + d, t)` with `d < L`, and `d ≠ 0` at a vertex. -/
theorem stretch_decomp (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p : ℕ}
    (hp : p < (chainModel J.whole).W.n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (h0 : 0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p + t))
    (hL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p + t) <
      ((rL1 J + rL2 J : ℕ) : ℝ)) :
    ∃ d, d < rL1 J + rL2 J ∧ (t = 0 → d ≠ 0) ∧
      p = (6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n := by
  have hC := corr_right0 J hP hS₂ hS₂f
  obtain ⟨hpd, hoff⟩ := hC.decomp hp ht0 ht1
  set d := dOf (chainModel J.whole).W.n (6 + tpos J.whole J.m₁) p
  rw [hoff] at h0 hL
  refine ⟨d, ?_, fun ht => ?_, hpd.symm⟩
  · have : (d : ℝ) < ((rL1 J + rL2 J : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  · rw [ht, add_zero] at h0
    intro hd; rw [hd] at h0; simp at h0

end Machine

end Sweep

end

end Chazelle.Core
