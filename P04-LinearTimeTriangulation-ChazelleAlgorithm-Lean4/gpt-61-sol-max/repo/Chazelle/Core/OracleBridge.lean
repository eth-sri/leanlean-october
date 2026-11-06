module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.OracleArcs
public import Chazelle.Core.FactsTree

/-!
# Lemma 3.6 (WP-H), part 6: from crossings of the chain to zipper edges

The node-level cluster argument (`OracleQ.cluster_query_nodes`) needs, for two distinct regions
facing each other across the chain (`CrossAdj`), two adjacent nodes.  The nodes are the arcs of
the normal form (spine positions); this file shows that the arcs of the two regions at the
crossing point contain, in their interiors, keys of two positions at that point of the chain
(`ZipRel`), which is what the preprocessing's zipper edges record.

* `not_mem_chord_of_crossAdj`: a crossing point lies on no chord.
* `arcHit_of_crossAdj`: both regions have an arc through the crossing point.
* `interior_of_arcHit`: an arc through a point of the chain off the chords contains a key of a
  position at that point in its interior.
* `cross_zip`: **the bridge**.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sideInArc sidePt regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)

namespace OracleQ

/-- The arcs at spine positions `p` and `q` meet at a point of the chain: their interiors
contain keys of two positions at that point. -/
def ZipRel (C : Chain) (Q : Polygon) (N : NF) (p q : ℕ) : Prop :=
  ∃ p₁ p₂ : ℕ, ∃ t₁ t₂ : ℝ, p₁ < (chainModel C).W.n ∧ p₂ < (chainModel C).W.n ∧
    0 ≤ t₁ ∧ t₁ < 1 ∧ 0 ≤ t₂ ∧ t₂ < 1 ∧
    sidePt (chainModel C).W p₁ t₁ ∈ C.set ∧
    sidePt (chainModel C).W p₁ t₁ = sidePt (chainModel C).W p₂ t₂ ∧
    sideInArc (sk (chainModel C) Q N p) (ek (chainModel C) Q N p) (p₁ + t₁) ∧
    sideInArc (sk (chainModel C) Q N q) (ek (chainModel C) Q N q) (p₂ + t₂)

theorem ZipRel.symm {C : Chain} {Q : Polygon} {N : NF} {p q : ℕ} (h : ZipRel C Q N p q) :
    ZipRel C Q N q p := by
  obtain ⟨p₁, p₂, t₁, t₂, h1, h2, h3, h4, h5, h6, hx, he, i1, i2⟩ := h
  exact ⟨p₂, p₁, t₂, t₁, h2, h1, h5, h6, h3, h4, he ▸ hx, he.symm, i2, i1⟩

section
variable (C : Chain)
/-- **A crossing point lies on no chord**: the points of the line just before and just after
it are in regions. -/
theorem not_mem_chord_of_crossAdj {F : Set (Set Point)}
    (hF : F ⊆ Merge.augChords C) {A B : Set Point} (hA : A ∈ (chainModel C).regions F)
    (hB : B ∈ (chainModel C).regions F) {x : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hAe : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x (-σ) t ∈ A)
    (hBe : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x σ t ∈ B) : ∀ c ∈ F, x ∉ c := by
  intro c hc hxc
  obtain ⟨y, a, b, h, -, rfl, -, -⟩ := Merge.augChords_spec (hF hc)
  obtain ⟨hy, ha, hb⟩ := hxc
  have hA' : A ∈ regionsIn C.dom F := hA
  have hB' : B ∈ regionsIn C.dom F := hB
  -- points of the chord in either direction are free, which is impossible
  have hfreeA : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x (-σ) t ∉ ⋃₀ F :=
    hAe.mono fun t ht => (Chazelle.Chain.regionsIn_subset hA' ht).2
  have hfreeB : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x σ t ∉ ⋃₀ F :=
    hBe.mono fun t ht => (Chazelle.Chain.regionsIn_subset hB' ht).2
  have hab := h.lt
  -- one of the two directions runs along the chord
  have hmem : ∀ τ : ℝ, (τ = 1 ∨ τ = -1) → (∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x τ t ∉ ⋃₀ F) →
      (τ = 1 → b ≤ x.1) ∧ (τ = -1 → x.1 ≤ a) := by
    intro τ hτ hfree
    constructor
    · intro hτ1
      subst hτ1
      by_contra hlt
      push Not at hlt
      obtain ⟨t, ht, ht'⟩ := (hfree.and (Ioo_mem_nhdsGT (sub_pos.2 hlt))).exists
      grind [Visibility.hseg, rayPt]
    · intro hτ1
      subst hτ1
      by_contra hlt
      push Not at hlt
      obtain ⟨t, ht, ht'⟩ := (hfree.and (Ioo_mem_nhdsGT (sub_pos.2 hlt))).exists
      grind [Visibility.hseg, rayPt]
  have hnσ : -σ = 1 ∨ -σ = -1 := by grind
  have e1 := hmem σ hσ hfreeB
  have e2 := hmem (-σ) hnσ hfreeA
  grind

/-- **Both regions of a crossing have an arc through the crossing point.** -/
theorem arcHit_of_crossAdj (hP : C.P.Simple) {Q : Polygon} {F : Set (Set Point)}
    (hFam : (chainModel C).ChordFamily Q F) {A B : Set Point}
    (hA : A ∈ (chainModel C).regions F) (hB : B ∈ (chainModel C).regions F)
    {x : Point} (hx : x ∈ C.set) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hAe : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x (-σ) t ∈ A)
    (hBe : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x σ t ∈ B) : ArcHit C F A x ∧ ArcHit C F B x := by
  have hz : x.2 ≤ C.top.2 := C.snd_le_top_of_mem_set hx
  have hxd : x ∉ C.dom := fun h => C.not_mem_set_of_mem_dom h hx
  have hnσ : -σ = 1 ∨ -σ = -1 := by grind
  
  obtain ⟨εA, hεA, hsubA⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hAe
  obtain ⟨εB, hεB, hsubB⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hBe
  have h1 := arcHit_right C hP hFam hA hz hnσ (s := 0) (b := εA) hεA
    (fun t h0 h1 => hsubA ⟨h0, h1⟩) (by simp_all)
  have h2 := arcHit_right C hP hFam hB hz hσ (s := 0) (b := εB) hεB
    (fun t h0 h1 => hsubB ⟨h0, h1⟩) (by simp_all)
  simp_all

/-- **An arc through a point of the chain off the chords contains in its interior the key of a
position at that point** (for a nonempty family). -/
theorem interior_of_arcHit {F : Set (Set Point)} (hne : F.Nonempty) {V : Set Point}
    {a b : ℝ} (harc : (chainModel C).IsArc F V a b) {x : Point} (hx : x ∈ C.set)
    (hxF : ∀ c ∈ F, x ∉ c) (hmem : x ∈ (chainModel C).arcSet a b) :
    ∃ p : ℕ, ∃ t : ℝ, p < (chainModel C).W.n ∧ 0 ≤ t ∧ t < 1 ∧
      sidePt (chainModel C).W p t = x ∧ sideInArc a b (p + t) := by
  obtain ⟨hca, hcb, hab⟩ := WalkAx.arc_cuts hne harc
  obtain ⟨p, t, hp, ht0, ht1, hkey, rfl⟩ := hmem
  -- a key of a position at `x` is not a cut
  have hnocut : ∀ (q : ℕ) (s : ℝ), 0 ≤ s → s < 1 → sidePt (chainModel C).W q s =
      Geometry.lerp ((chainModel C).wa p) ((chainModel C).wb p) t →
      ¬ (chainModel C).IsCut F (q + s) := by
    rintro q s hs0 hs1 hq ⟨c, hc, q', s', hatt, hk⟩
    obtain ⟨-, hs'0, hs'1, hin, -⟩ := hatt
    obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj hs0 hs1 hs'0 hs'1 hk
    simp_all
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · -- the end of the walk edge: the start of the next one
    subst h1
    by_cases hlast : p + 1 < (chainModel C).W.n
    · have hpt : sidePt (chainModel C).W (p + 1) 0 =
          Geometry.lerp ((chainModel C).wa p) ((chainModel C).wb p) 1 := by
        rw [Chazelle.Chain.sidePt_zero, Geometry.lerp_one]
        show (chainModel C).W.vtx (p + 1) = (chainModel C).W.vtx ((p + 1) % (chainModel C).W.n)
        rw [Nat.mod_eq_of_lt hlast]
      have hnc := hnocut (p + 1) 0 le_rfl one_pos hpt
      ram_grind
    · exfalso
      have hp1 : p + 1 = (chainModel C).W.n := by omega
      have hv : Geometry.lerp ((chainModel C).wa p) ((chainModel C).wb p) 1 = C.slitTop := by
        rw [Geometry.lerp_one]
        show (C.sideWalk C.sideBeta).vtx ((p + 1) % (C.sideWalk C.sideBeta).n) = C.slitTop
        have : (p + 1) % (C.sideWalk C.sideBeta).n = 0 := by
          show (p + 1) % (chainModel C).W.n = 0
          grind [Nat.mod_self]
        rw [this, C.sideWalk_vtx_zero]
      rw [hv] at hx
      have := C.snd_le_top_of_mem_set hx
      simp only [Chain.slitTop] at this
      linarith [C.top_snd_lt_radius]
  · have hnc := hnocut p t ht0 h1 rfl
    refine ⟨p, t, hp, ht0, h1, rfl, ?_⟩
    grind

/-- **The bridge from crossings to zipper edges.**  If two distinct regions face each other
across the chain, arcs of them at two spine positions meet at a point of the chain
(`ZipRel`). -/
theorem cross_zip (hP : C.P.Simple) {Q : Polygon} {N : NF}
    (hN : IsNF (chainModel C) Q N) {reg : ℕ → Set Point}
    (hR : RegionCorr (chainModel C) Q N reg) (hA : ArcsOK (chainModel C) Q N reg)
    {A B : Set Point} (hAr : A ∈ (chainModel C).regions (N.F (chainModel C) Q))
    (hBr : B ∈ (chainModel C).regions (N.F (chainModel C) Q)) (hAB : A ≠ B)
    (hcr : CrossAdj C A B) :
    ∃ p q, p < N.arcs.length ∧ q < N.arcs.length ∧ reg (rgi N p) = A ∧ reg (rgi N q) = B ∧
      ZipRel C Q N p q := by
  set F := N.F (chainModel C) Q
  have hFam : (chainModel C).ChordFamily Q F := hN.1
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  obtain ⟨x, hx, σ, hσ, hAe, hBe⟩ := hcr
  -- the family is nonempty: otherwise there is a single region
  have hne : F.Nonempty := by
    by_contra hF
    rw [Set.not_nonempty_iff_eq_empty] at hF
    obtain ⟨hfin, hcard, -⟩ := regionTree _ Q F hGM hFam
    rw [hF, Set.ncard_empty, zero_add] at hcard
    obtain ⟨U, hU⟩ := Set.ncard_eq_one.1 hcard
    simp_all
  have hxF := not_mem_chord_of_crossAdj C hFam.2.1 hAr hBr hσ hAe hBe
  obtain ⟨hitA, hitB⟩ := arcHit_of_crossAdj C hP hFam hAr hBr hx hσ hAe hBe
  -- the arcs of the two regions through `x`, located on the spine
  have locate : ∀ V, V ∈ (chainModel C).regions F → ArcHit C F V x →
      ∃ p, p < N.arcs.length ∧ reg (rgi N p) = V ∧ ∃ p₁ : ℕ, ∃ t₁ : ℝ,
        p₁ < (chainModel C).W.n ∧ 0 ≤ t₁ ∧ t₁ < 1 ∧ sidePt (chainModel C).W p₁ t₁ = x ∧
        sideInArc (sk (chainModel C) Q N p) (ek (chainModel C) Q N p) (p₁ + t₁) := by
    intro V hV ⟨a, b, harc, hmem⟩
    obtain ⟨p₁, t₁, hp₁, ht₀, ht₁, hpt, hin⟩ := interior_of_arcHit C hne harc hx hxF hmem
    obtain ⟨r, hr, rfl⟩ := hR.2.2 V hV
    obtain ⟨j, hj, hjr, hja, hjb⟩ := hA.2.2.1 r hr a b harc
    obtain ⟨p, hp, hpj⟩ := NFLoc.seq_surj hN hj
    refine ⟨p, hp, ?_, p₁, t₁, hp₁, ht₀, ht₁, hpt, ?_⟩
    · show reg (N.arc (N.seq.getD p 0)).reg = reg r
      simp_all
    · show sideInArc ((chainModel C).key Q (N.arc (N.seq.getD p 0)).s)
        ((chainModel C).key Q (N.arc (N.seq.getD p 0)).e) (p₁ + t₁)
      simp_all
  obtain ⟨p, hp, hpA, p₁, t₁, hp₁, h10, h11, hpt₁, hin₁⟩ := locate A hAr hitA
  obtain ⟨q, hq, hqB, p₂, t₂, hp₂, h20, h21, hpt₂, hin₂⟩ := locate B hBr hitB
  exact ⟨p, q, hp, hq, hpA, hqB, p₁, p₂, t₁, t₂, hp₁, hp₂, h10, h11, h20, h21,
    hpt₁ ▸ hx, hpt₁.trans hpt₂.symm, hin₁, hin₂⟩


end

end OracleQ

end

end Chazelle.Core
