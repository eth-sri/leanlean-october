module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoS0MathB

/-!
# The side-0 answer cases (sweep, `Side0MathSpec`), part 3: rays along a chord of `F₂⁺`

* `F₂plus_origin`: a chord of `F₂⁺` is the chord of `C` shot from the shared vertex, the top of
  `C₂`, or an end of a chord of `S₂` (into the chord);
* `along_end`: a ray from a point `z` off the domain along such a chord, `z` other than the
  origin, first hits `C` at the origin, in the direction opposite to the shot, and the shot ends
  at `z`;
* `arrival_of_attach`: a position at which a chord along the ray is attached is an arrival
  position of the reversed ray;
* `stopSet_eq`, `endOrigin_big`: the stop chord is the shot from its origin; the origin of an
  endpoint query out of range lies on the vertical line of the top of `C₂`.
-/

namespace Chazelle.Core

namespace S0Math

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed Sweep

@[expose] public section

variable (J : Merge.Junction)

/-- **The origins of the chords of `F₂⁺`.** -/
theorem F₂plus_origin {S₂ : Set (Set Point)} {e : Set Point} (he : e ∈ F₂plus J S₂) :
    ∃ (o : Point) (d : ℝ), (d = 1 ∨ d = -1) ∧ FreeAt J.whole o d ∧ e = Merge.shoot J.whole o d ∧
      (o = J.shared ∨ o = J.right.top ∨
        ∃ c ∈ S₂, (d = 1 ∧ o = Merge.lend c) ∨ (d = -1 ∧ o = Merge.rend c)) := by
  rcases he with ((⟨c₀, hc₀, hfr, rfl⟩ | ⟨c₀, hc₀, hfr, rfl⟩) | ⟨σ, hσ, hfr, rfl⟩) |
      ⟨σ, hσ, hfr, rfl⟩
  · ram_grind
  · ram_grind
  · exact ⟨J.shared, σ, hσ, hfr, rfl, Or.inl rfl⟩
  · have hv : J.whole.vertex (J.m₁ + J.right.topIdx) = J.right.top := by
      rw [Merge.Junction.whole_vertex_add]; rfl
    refine ⟨J.right.top, σ, hσ, ?_, ?_, Or.inr (Or.inl rfl)⟩
    · rw [← hv]; exact hfr
    · rw [← hv]; rfl

/-- **A ray along a shot chord from its far end.** -/
theorem along_end {e : Set Point} (he : e ∈ Merge.augChords J.whole) {z o : Point} {σ d : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hd : d = 1 ∨ d = -1) (hzD : z ∉ J.whole.dom)
    (hoD : o ∉ J.whole.dom) (hzo : z ≠ o) (heo : e = Merge.shoot J.whole o d)
    (hfo : FreeAt J.whole o d) (hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e) :
    rayPt z σ (J.whole.hitParam z σ) = o ∧ d = -σ ∧ rayPt o d (J.whole.hitParam o d) = z ∧
      0 < J.whole.hitParam z σ ∧ (∀ p ∈ e, p ∉ J.whole.dom → p = z ∨ p = o) ∧
      (∀ p ∈ e, p.2 = z.2) := by
  obtain ⟨y, l, r, hH, hy, hcd, -, -⟩ := Merge.augChords_spec he
  have hmem : ∀ p : Point, p ∈ e ↔ p.2 = y ∧ l ≤ p.1 ∧ p.1 ≤ r := by
    intro p; rw [hcd]; rfl
  have hlr := hH.lt
  have hends : ∀ p ∈ e, p ∉ J.whole.dom → p.1 = l ∨ p.1 = r := by
    grind [Chazelle.Merge.FreeAt, Chazelle.Chain.IsHChordIn]
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hδ' : (0 : ℝ) < δ := hδ
  have hray : ∀ s, 0 < s → s < δ → z.2 = y ∧ l ≤ z.1 + σ * s ∧ z.1 + σ * s ≤ r := by
    intro s h0 h1
    have := (hmem _).1 (hsub ⟨h0, h1⟩)
    grind [rayPt_fst, rayPt_snd]
  have hzy : z.2 = y := (hray (δ / 2) (by linarith) (by linarith)).1
  -- the side of `z`
  have hzlr : (σ = 1 ∧ z.1 = l) ∨ (σ = -1 ∧ z.1 = r) := by
    have hz1 : l ≤ z.1 ∧ z.1 ≤ r := by
      constructor
      · by_contra h
        push Not at h
        set s := min (δ / 2) ((l - z.1) / 2) with hs
        have hs0 : 0 < s := lt_min (by linarith) (by linarith)
        have hs1 := min_le_left (δ / 2) ((l - z.1) / 2)
        have hs2 := min_le_right (δ / 2) ((l - z.1) / 2)
        have := (hray s hs0 (by linarith)).2.1
        rcases hσ with rfl | rfl <;> nlinarith
      · by_contra h
        push Not at h
        set s := min (δ / 2) ((z.1 - r) / 2) with hs
        have hs0 : 0 < s := lt_min (by linarith) (by linarith)
        have hs1 := min_le_left (δ / 2) ((z.1 - r) / 2)
        have hs2 := min_le_right (δ / 2) ((z.1 - r) / 2)
        have := (hray s hs0 (by linarith)).2.2
        rcases hσ with rfl | rfl <;> nlinarith
    have hze : z ∈ e := (hmem z).2 ⟨hzy, hz1⟩
    have hs0 : (0 : ℝ) < min (δ / 2) ((r - l) / 2) := lt_min (by linarith) (by linarith)
    have hs1 := min_le_left (δ / 2) ((r - l) / 2)
    have h := hray (min (δ / 2) ((r - l) / 2)) hs0 (by linarith)
    rcases hends z hze hzD with h1 | h1 <;> rcases hσ with rfl | rfl
    · ram_grind
    · linarith
    all_goals ram_grind
  have hze : z ∈ e := (hmem z).2 ⟨hzy, by ram_grind⟩
  -- the origin is the other end
  have hoe : o ∈ e := by rw [heo]; exact origin_mem J
  obtain ⟨hoy, -, -⟩ := (hmem o).1 hoe
  have hoz1 : o.1 ≠ z.1 := fun h => hzo (Prod.ext h.symm (by grind))
  have hoend := hends o hoe hoD
  set τ := r - l with hτ
  have hτ0 : 0 < τ := by linarith
  have hwo : rayPt z σ τ = o := by
    grind [rayPt_fst, rayPt_snd]
  have hg : Genuine J.whole z σ τ :=
    genuine_along_chord J.whole he hze hzD hσ hτ0 (by grind) (by grind)
  have hT : J.whole.hitParam z σ = τ :=
    ((genuine_iff J.whole (by grind) hσ).1 hg).2
  -- the shot from the origin ends at `z`
  have ho2 : o.2 ≤ J.whole.top.2 := by grind
  obtain ⟨hτo, hhD, -⟩ := Merge.hit_of_freeAt J.whole ho2 hd hfo
  have hhe : rayPt o d (J.whole.hitParam o d) ∈ e := by
    rw [heo]; exact Geometry.right_mem_segment _ _
  have hh1 := hends _ hhe hhD
  rw [rayPt_fst] at hh1
  have hhz : rayPt o d (J.whole.hitParam o d) = z := by
    apply point_ext
    · grind [rayPt_fst]
    grind
  ram_grind

/-- **An attachment of a chord along the ray is an arrival position of the reversed ray.** -/
theorem arrival_of_attach {W : Polygon} {e : Set Point} {p : ℕ} {t : ℝ} {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hA : SideAttach W e p t) (hpt : sidePt W p t = z)
    (hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e) : Arrival W z (-σ) p t := by
  obtain ⟨hp, ht0, ht1, -, r, hr, hcl⟩ := hA
  refine ⟨hp, ht0, ht1, hpt, ?_⟩
  rw [neg_neg]
  obtain ⟨s, ⟨hse, hsr⟩, hs0⟩ := ((hev.and (Ioo_mem_nhdsGT hr)).and self_mem_nhdsWithin).exists
  have hs0' : (0 : ℝ) < s := hs0
  have hdist : dist (rayPt z σ s) z = s := dist_rayPt z hσ hs0'.le
  have h1 : sideLeft W p t (rayPt z σ s) := by
    grind [dist_self]
  rw [← hpt] at h1 ⊢
  exact (sideLeft_rayPt_iff W p t σ hs0' one_pos).1 h1

section
variable (Q : Polygon) (N : NF)
/-- **The stop chord is the shot from its origin.** -/
theorem stopSet_eq (kind k b : ℕ) :
    stopSet J Q N kind k b = Merge.shoot J.whole (SweepIo.stopOrig J Q N kind k b) (dirOf b) := by
  unfold stopSet SweepIo.stopOrig
  split_ifs <;> rfl

/-- **The origin of an endpoint query out of range** is on the vertical line of the top of `C₂`
(the default chord record is the slit top). -/
theorem endOrigin_big {j : ℕ} (hj : N.nChords ≤ j / 2) :
    (endOrigin J Q N j).1 = J.right.top.1 := by
  have hch : N.chord (j / 2) = ⟨0, 0, 0, 0, 0⟩ := by
    unfold NF.chord; exact List.getD_eq_default _ _ hj
  
  have hpos : (chainModel J.right).pos Q ⟨0, 0 + 1⟩ = J.right.slitTop := by
    have hwa : (chainModel J.right).wa 0 = J.right.slitTop := rfl
    have hwb : (chainModel J.right).wb 0 = ((-J.right.radius, J.right.radius) : Point) := by
      aesop
    have hpar : (chainModel J.right).param Q ⟨0, 0 + 1⟩ = 0 := by
      show (if ((chainModel J.right).wa 0).2 = ((chainModel J.right).wb 0).2 then 0 else _) = _
      rw [ite_eq_left (by aesop)]
    simp_all [Model.pos, Geometry.lerp_zero] 
  have hset : (N.chord (j / 2)).toSet (chainModel J.right) Q =
      hseg (Q.vtx 0).2 J.right.slitTop.1 J.right.slitTop.1 := by
    simp_all [CRec.toSet, CRec.lpos, CRec.rpos] 
  unfold endOrigin
  split_ifs
  · rw [hset, Merge.lend_hseg le_rfl]; rfl
  · rw [hset, Merge.rend_hseg le_rfl]; rfl


end

end

end S0Math

end Chazelle.Core
