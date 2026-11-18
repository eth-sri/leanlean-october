module

public import Chazelle.Core.SweepMachine16

/-!
# The sweep (WP-D), part 33: the abstract machine, wall pieces

A chord of `S₂` with an endpoint `b` on a box wall gives the wall piece `shoot J.whole b σ`
(precomputed stop).  Where the box of `C` lies decides its kind:

* `off_box`: the box positions of the walk of `C` (edges `0 … 5`) have offsets inside the open right
  stretch when the box lies in it (`rlen = 2 m₂ + 7`), and at least `L` otherwise;
* `sideLabel_sub` (the general rule for a chord inside a chord `c ∈ S₂`): if it is attached at a
  point of `C₂` other than the shared vertex and the top of `C₂`, or at a position inside a walk
  edge of the open right stretch, its side labels are the regions of `S₂` on the same side of `c`.
  This covers the fused chords, the wall pieces ending on `C₂`, and the wall pieces starting on a
  wall of the right stretch.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

section Machine

variable (J : Merge.Junction)

/-- **The rule for a chord inside a chord of `S₂`** (fused chords and wall pieces): let `f ∈ F₂⁺`,
`f ⊆ c ∈ S₂`, be attached at a position `(pB, tB)` of the open right stretch which is not the
split vertex (for instance at a point of `C₂` other than the top of `C₂`, or inside a walk edge);
then its side labels are the regions of `S₂` on the same side of `c`. -/
theorem sideLabel_sub (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {c f : Set Point} (hc : c ∈ S₂)
    (hf : f ∈ F₂plus J S₂) (hfc : f ⊆ c) {pB : ℕ} {tB : ℝ}
    (hB : SideAttach (chainModel J.whole).W f pB tB)
    (h0 : 0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pB + tB))
    (hL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pB + tB) <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hns : tB = 0 → sidePt (chainModel J.whole).W pB tB ≠ J.right.top)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {V : Set Point}
    (hV : V ∈ (chainModel J.right).regions S₂) (hVs : SideOf (chainModel J.right) ρ c V) :
    SideLabel J S₂ f ρ V := by
  have hS₂a : S₂ ⊆ Merge.augChords J.right := hS₂.2.1
  obtain ⟨d, hd, hd0, hpd⟩ := stretch_decomp J hP hS₂a hS₂.1 hB.1 hB.2.1 hB.2.2.1 h0 hL
  have hns' := hns
  rw [hpd] at hB hns'
  have hsec : tB = 0 → d ≠ 0 ∧ d ≠ rL1 J := by
    intro ht
    refine ⟨hd0 ht, fun hdr => ?_⟩
    have hlt : rL1 J < rL1 J + rL2 J := by omega
    apply hns' ht
    rw [ht, hdr]
    exact sidePt_split J hP hS₂a hS₂.1 hlt
  exact sideLabel_fused J hP hS₂ hF hf hc hfc hd hB.2.1 hB.2.2.1 hsec hB hρ hV hVs

end Machine

end Sweep

end

end Chazelle.Core
