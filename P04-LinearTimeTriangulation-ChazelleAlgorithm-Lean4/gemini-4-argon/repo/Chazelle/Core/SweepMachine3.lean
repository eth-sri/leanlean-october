module

public import Chazelle.Core.SweepMachine2

/-!
# The sweep (WP-D), part 19: the abstract machine, brackets, pockets and the start

* `no_label_of_pocket`: a chord of `F₂⁺` attached at the base copy of the shared vertex (offset `0`)
  and at a key of the `C₁` part closes a **pocket**: the regions faced after that key (up to the
  end of the walk) have no label.  (The `C₁`-part analogue of `no_label_of_bracket`.)
* `dir_opposite`: the two attachments of a chord are its two ends, so the chord leaves them in
  opposite directions (the side label stored when a bracket opens is the one used when it closes).
* `valid_start`: the region faced just before the start of the `C₁` part (the other copy of the
  shared vertex, offset `L`) has the label faced in the model of `C₂` just before the end of the
  right stretch (`rlabel_before0`), the initial label `λ₀` of the sweep.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft freeIn regionsIn)
open WalkEmbed

namespace Sweep

section Machine

variable (J : Merge.Junction)

/-- **The regions of a pocket have no label**: a chord of `F₂⁺` attached at the base copy of the
shared vertex (offset `0`) and at a key `A` of the `C₁` part; every non-cut position after `A`
faces an unlabelled region. -/
theorem no_label_of_pocket (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂)) {e : Set Point}
    (he : e ∈ F₂plus J S₂) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach (chainModel J.whole).W e pa ta) (hB : SideAttach (chainModel J.whole).W e pb tb)
    (hAB : sidePt (chainModel J.whole).W pa ta ≠ sidePt (chainModel J.whole).W pb tb)
    (hAo : ((rL1 J + rL2 J : ℕ) : ℝ) ≤
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pa + ta))
    (hBo : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) = 0)
    {px : ℕ} {tx : ℝ} (hpx : px < (chainModel J.whole).W.n) (htx : tx ∈ Ioo (0 : ℝ) 1)
    (hcx : ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (px + tx))
    (hfx : (chainModel J.whole).Faces px tx G)
    (hx : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pa + ta) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (px + tx)) :
    ∀ V, ¬ RLabel J S₂ G V := by
  rintro V ⟨d, hd, t, ht, hc, hf, -⟩
  have hC := corr_right0 J hP hS₂ hS₂f
  have hn := hC.n_pos
  set n := (chainModel J.whole).W.n
  set g := 6 + tpos J.whole J.m₁
  have hg : g < n := hC.hg
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
  have hy0 : (0 : ℝ) < d + t := by have := ht.1; positivity
  have hxy : (px : ℝ) + tx ≠ (((g + d) % n : ℕ) : ℝ) + t := by
    intro h
    have := congrArg (off n g) h
    rw [hoy] at this
    linarith
  have hxa : (px : ℝ) + tx ≠ pa + ta := fun h => hcx ⟨e, he, pa, ta, hA, h⟩
  have hxb : (px : ℝ) + tx ≠ pb + tb := fun h => hcx ⟨e, he, pb, tb, hB, h⟩
  have hya : (((g + d) % n : ℕ) : ℝ) + t ≠ pa + ta := fun h => hc ⟨e, he, pa, ta, hA, h⟩
  have hyb : (((g + d) % n : ℕ) : ℝ) + t ≠ pb + tb := fun h => hc ⟨e, he, pb, tb, hB, h⟩
  refine (sep_iff_btw hg0 hgn a0 a1 b0 b1 x0 x1 y0 y1 hk13 hxy hxa hxb hya hyb).2 ?_
  rw [hoy, hBo]
  unfold Btw
  constructor
  · intro _ h2
    rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> linarith
  · intro _
    right; constructor <;> linarith

/-- **The two attachments of a chord are its two ends**: the chord leaves them in opposite
directions. -/
theorem dir_opposite {M : Model} (hM : WalkAx M) {e : Set Point} (he : e ∈ M.Adm) {pa pb : ℕ}
    {ta tb : ℝ} (hA : SideAttach M.W e pa ta) (hB : SideAttach M.W e pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    (hdA : ∀ z ∈ e, (sidePt M.W pa ta).1 ≤ z.1) : ∀ z ∈ e, z.1 ≤ (sidePt M.W pb tb).1 := by
  obtain ⟨a, b, hab, hcab, hy, -, -, -⟩ := hM.ends e he
  obtain ⟨a', b', -, hcab', hend⟩ := end_of_not_mem hM he
  have hAe := hA.2.2.2.1
  have hBe := hB.2.2.2.1
  have hAD : sidePt M.W pa ta ∉ M.D := hM.trace pa hA.1 ta hA.2.1 hA.2.2.1.le
  have hBD : sidePt M.W pb tb ∉ M.D := hM.trace pb hB.1 tb hB.2.1 hB.2.2.1.le
  have hA' := hend _ hAe hAD
  have hB' := hend _ hBe hBD
  rw [hcab'] at hAe hBe ⊢
  intro z hz
  obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz
  have ha'e : a' ∈ e := by rw [hcab']; exact Geometry.left_mem_segment _ _
  have hb'e : b' ∈ e := by rw [hcab']; exact Geometry.right_mem_segment _ _
  have h1 := hdA a' ha'e
  have h2 := hdA b' hb'e
  simp only [Geometry.lerp_fst]
  rcases hA' with hA' | hA' <;> rcases hB' with hB' | hB'
  · exact absurd (hA'.trans hB'.symm) hAB
  · rw [hB']; rw [hA'] at h2; nlinarith
  · rw [hB']; rw [hA'] at h1; nlinarith
  · exact absurd (hA'.trans hB'.symm) hAB

/-- **The initial label**: the region faced just before the start of the `C₁` part (the copy of the
shared vertex at offset `L`) has the label `λ₀` faced in the model of `C₂` just before the end of
the right stretch. -/
theorem valid_start (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) (hL1 : 1 ≤ rL1 J + rL2 J)
    {G V : Set Point} (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hV : V ∈ (chainModel J.right).regions S₂)
    (hW : BeforeFaces (chainModel J.whole)
      ((6 + tpos J.whole J.m₁ + (rL1 J + rL2 J)) % (chainModel J.whole).W.n) 0 G)
    (hW₂ : BeforeFaces (chainModel J.right)
      ((6 + tpos J.right 0 + (dq (rL1 J) (rδ J) (rL1 J + rL2 J - 1) + 1)) %
        (chainModel J.right).W.n) 0 V) :
    Valid J S₂ G V :=
  valid_of_rlabel J hP hS₂ hS₂f hG hV
    (rlabel_before0 J hP hS₂ hS₂f hL1 le_rfl hW hW₂)

end Machine

end Sweep

end

end Chazelle.Core
