module

public import Chazelle.Golf

public import Chazelle.Core.SweepQuery
public import Chazelle.Core.Facts2

/-!
# The sweep (WP-D), part 7: events (lemma (E), the local cases)

The sweep walks the part of the walk of `C = J.whole` outside the right stretch (the `C₁` part)
and keeps a label (a region of `S₂`) for the current region of `F₂⁺`.  When it crosses a chord `e`
of `F₂⁺` attached on the `C₁` part, the new region is on the other side of `e`:

* `label_above`, `label_below` (**transition across a fused chord**): if `e` is the chord of the
  fusion contained in `c ∈ S₂`, attached at a position of the right stretch (at the endpoint of `c`
  on `C₂`) where no other chord of `F₂⁺` is attached, the region of `F₂⁺` above (below) `e` has as
  label the region of `S₂` above (below) `c` — the region recorded as `up`/`dn` of `c` in the
  normal form of `S₂` (`ChordSidesOK`).
* `no_label_of_bracket` (**brackets**): a region faced between the two attachments of a chord of
  `F₂⁺` whose both attachments lie on the `C₁` part (on the side away from the right stretch) has
  no label: no query in it sees `C₂` (`query_right`), so the sweep need not know a label there.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft freeIn regionsIn
  sideKey_inj)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open WalkEmbed

namespace Sweep

section Bracket

variable (J : Merge.Junction)

/-- **Brackets have no label.**  Let a chord `e` of `F₂⁺` be attached at two positions of the
`C₁` part (offsets from the base of the right stretch at least the length of the stretch), and let
a non-cut position inside a walk edge, strictly between them in offsets, face the region `G`.
Then `G` has no label. -/
theorem no_label_of_bracket (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂)) {e : Set Point}
    (he : e ∈ F₂plus J S₂) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach (chainModel J.whole).W e pa ta) (hB : SideAttach (chainModel J.whole).W e pb tb)
    (hAB : sidePt (chainModel J.whole).W pa ta ≠ sidePt (chainModel J.whole).W pb tb)
    (hAo : ((rL1 J + rL2 J : ℕ) : ℝ) ≤
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pa + ta))
    (hBo : ((rL1 J + rL2 J : ℕ) : ℝ) ≤
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb))
    {px : ℕ} {tx : ℝ} (hpx : px < (chainModel J.whole).W.n) (htx : tx ∈ Ioo (0 : ℝ) 1)
    (hcx : ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (px + tx))
    (hfx : (chainModel J.whole).Faces px tx G)
    (hbtw : Btw (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pa + ta))
      (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb))
      (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (px + tx))) :
    ∀ V, ¬ RLabel J S₂ G V := by
  rintro V ⟨d, hd, t, ht, hc, hf, -⟩
  have hC := corr_right0 J hP hS₂ hS₂f
  have hn := hC.n_pos
  set n := (chainModel J.whole).W.n with hndef
  set g := 6 + tpos J.whole J.m₁ with hgdef
  have hg := hC.hg
  have hg0 : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg _
  have hgn : (g : ℝ) < n := by exact_mod_cast hg
  have hne := (hC.hM.eq_iff_not_separates hC.hF hC.hfin hG hG hpx (Nat.mod_lt _ hn) htx ht hcx
    hc hfx hf).1 rfl e he
  apply hne
  refine ⟨pa, pb, ta, tb, hA, hB, hAB, ?_⟩
  have hk13 := WalkAx.key_ne_of_pt_ne (M := chainModel J.whole) hA hB hAB
  obtain ⟨a0, a1⟩ := Corr.key_mem hA.1 hA.2.1 hA.2.2.1
  obtain ⟨b0, b1⟩ := Corr.key_mem hB.1 hB.2.1 hB.2.2.1
  obtain ⟨x0, x1⟩ := Corr.key_mem hpx htx.1.le htx.2
  obtain ⟨y0, y1⟩ := Corr.key_mem (Nat.mod_lt (g + d) hn) ht.1.le ht.2
  have hoy : off n g (((g + d) % n : ℕ) + t) = d + t := off_key hg (by have := hC.hL; omega)
    ht.1.le ht.2
  have hyrl : (d : ℝ) + t < ((rL1 J + rL2 J : ℕ) : ℝ) := by
    have : (d : ℝ) + 1 ≤ ((rL1 J + rL2 J : ℕ) : ℝ) := by exact_mod_cast hd
    linarith [ht.2]
  have hxy : (px : ℝ) + tx ≠ (((g + d) % n : ℕ) : ℝ) + t := by
    intro h
    have := congrArg (off n g) h
    rw [hoy] at this
    unfold Btw at hbtw
    rcases hbtw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have hxa : (px : ℝ) + tx ≠ pa + ta := fun h => hcx ⟨e, he, pa, ta, hA, h⟩
  have hxb : (px : ℝ) + tx ≠ pb + tb := fun h => hcx ⟨e, he, pb, tb, hB, h⟩
  have hya : (((g + d) % n : ℕ) : ℝ) + t ≠ pa + ta := fun h => hc ⟨e, he, pa, ta, hA, h⟩
  have hyb : (((g + d) % n : ℕ) : ℝ) + t ≠ pb + tb := fun h => hc ⟨e, he, pb, tb, hB, h⟩
  refine (sep_iff_btw hg0 hgn a0 a1 b0 b1 x0 x1 y0 y1 hk13 hxy hxa hxb hya hyb).2 ?_
  Ξ hoy
  unfold Btw at hbtw ⊢
  constructor
  · intro h1 h2
    rcases h1 with ⟨h7, h8⟩ | ⟨h7, h8⟩ <;> rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rcases hbtw with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> linarith
  · intro h1
    rcases hbtw with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · right; constructor <;> linarith
    · exfalso; apply h1; right; constructor <;> linarith

end Bracket

/-! ## Transition across a fused chord -/

section Transition

variable (J : Merge.Junction)

/-- Two regions containing the points just above (below) an open point of a chord are equal. -/
theorem region_eq_of_side {M : Model} {F : Set (Set Point)} {U U' : Set Point}
    (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F) {z : Point} {τ : ℝ}
    (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + τ * δ) : Point) ∈ U)
    (h' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + τ * δ) : Point) ∈ U') : U = U' := by
  obtain ⟨δ, h1, h2⟩ := (h.and h').exists
  Ξ Chazelle.Chain.regionsIn_eq_component hU h1, Chazelle.Chain.regionsIn_eq_component hU' h2

/-- A region containing the points just above (below) a point of a chord in the domain touches
the chord (it is an exit chord of the region). -/
theorem touches_of_side {D : Set Point} {c U : Set Point} {z : Point} (hz : z ∈ c) (hzD : z ∈ D)
    {τ : ℝ} (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + τ * δ) : Point) ∈ U) :
    Chazelle.Chain.TouchesIn D c U := by
  refine ⟨z, ⟨hz, hzD⟩, ?_⟩
  have hlim : Tendsto (fun δ : ℝ => ((z.1, z.2 + τ * δ) : Point)) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have hc : Continuous (fun δ : ℝ => ((z.1, z.2 + τ * δ) : Point)) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  exact mem_closure_of_tendsto hlim h

end Transition

end Sweep

end

end Chazelle.Core
