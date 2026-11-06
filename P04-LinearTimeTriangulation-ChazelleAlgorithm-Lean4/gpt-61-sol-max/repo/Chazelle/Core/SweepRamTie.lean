module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepMachine21L

/-!
# The sweep RAM (WP-D), part 1: the chords at an event key

At an event key `K` of the `C₁` part the RAM must know **all** chords of `F₂⁺` attached there (at a
walk vertex there may be two, a tie).  The detection finds one of them; this file shows how the RAM
completes the set:

* `sub_of_mem_dom`: an admissible chord of `C` through a point of a chord `c ∈ S₂` lying in the
  domain of `C₂` is contained in `c`;
* `tie_parent`: the two chords of a tie at a point of the domain of `C₂` lie in one chord of `S₂`;
* `piece_of_parent`: a chord of `F₂⁺` inside `c ∈ S₂` and attached at a point of the domain of `C₂`
  is the chord seen from one endpoint of `c` (towards the key), so the RAM finds the partner of a
  chord `e ⊆ c` of a tie by one shot from the other endpoint of `c`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

section Machine

variable (J : Merge.Junction)

section
variable (hP : J.P.Simple) {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
include hP hS₂
/-- **An admissible chord of `C` through a point of a chord `c ∈ S₂` in the domain of `C₂` lies in
`c`**: its points beyond an end of `c` would put that end (not in the domain of `C₂`) strictly
inside the chord, in the domain of `C`. -/
theorem sub_of_mem_dom {e c : Set Point}
    (he : e ∈ (chainModel J.whole).Adm) (hc : c ∈ S₂) {K : Point} (hKe : K ∈ e) (hKc : K ∈ c)
    (hKD : K ∈ J.right.dom) : e ⊆ c := by
  have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
  obtain ⟨y, l, r, hH, hy, hceq, -, -⟩ := Merge.augChords_spec (hS₂ hc)
  obtain ⟨a, b, hab, heab, hab2, hopen, -, -⟩ := hM.ends e he
  subst hceq
  obtain ⟨hKy, hKl, hKr⟩ := hKc
  
  have hl : l < K.1 := by
    rcases hKl.lt_or_eq with h | h
    · exact h
    · exfalso; apply hH.left_not; grind
  have hr : K.1 < r := by
    rcases hKr.lt_or_eq with h | h
    · exact h
    · exfalso; apply hH.right_not; grind
  have hya : a.2 = y := by
    have := hKe; rw [heab] at this
    obtain ⟨v, -, -, hv⟩ := Geometry.mem_segment_iff_lerp.1 this
    grind [Geometry.lerp_snd]
  -- a point strictly between two points of the chord is in the domain of `C`
  have inner : ∀ u₁ u₂ : ℝ, u₁ ∈ Icc (0 : ℝ) 1 → u₂ ∈ Icc (0 : ℝ) 1 → ∀ x : ℝ,
      (lerp a b u₁).1 < x → x < (lerp a b u₂).1 → ((x, y) : Point) ∈ J.whole.dom := by
    intro u₁ u₂ hu₁ hu₂ x hx1 hx2
    have hd : (lerp a b u₂).1 - (lerp a b u₁).1 ≠ 0 := by linarith
    have hne : b.1 - a.1 ≠ 0 := by
      grind
    set s := u₁ + (u₂ - u₁) * ((x - (lerp a b u₁).1) / ((lerp a b u₂).1 - (lerp a b u₁).1))
      with hs
    have hq : 0 < (x - (lerp a b u₁).1) / ((lerp a b u₂).1 - (lerp a b u₁).1) :=
      div_pos (by linarith) (by linarith)
    have hq1 : (x - (lerp a b u₁).1) / ((lerp a b u₂).1 - (lerp a b u₁).1) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    have hu : u₁ ≠ u₂ := by grind
    have hs01 : s ∈ Ioo (0 : ℝ) 1 := by
      rcases lt_or_gt_of_ne hu with h | h
      · constructor <;> nlinarith [hu₁.1, hu₂.2]
      · constructor <;> nlinarith [hu₁.2, hu₂.1]
    have hpt : lerp a b s = ((x, y) : Point) := by
      grind [Geometry.lerp_fst, Geometry.lerp_snd]
    rw [← hpt]; exact hopen s hs01
  intro z hz
  have hz' := hz
  rw [heab] at hz'
  obtain ⟨u₂, hu₂0, hu₂1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz'
  have hK' := hKe
  rw [heab] at hK'
  obtain ⟨u₁, hu₁0, hu₁1, hKu⟩ := Geometry.mem_segment_iff_lerp.1 hK'
  have hzy : (lerp a b u₂).2 = y := by
    core_grind
  refine ⟨hzy, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    have := inner u₂ u₁ ⟨hu₂0, hu₂1⟩ ⟨hu₁0, hu₁1⟩ l hc (by grind)
    exact hH.left_not (dom_right J this (by omega))
  · by_contra hc
    push Not at hc
    have := inner u₁ u₂ ⟨hu₁0, hu₁1⟩ ⟨hu₂0, hu₂1⟩ r (by grind) hc
    exact hH.right_not (dom_right J this (by omega))

/-- **The two chords of a tie lie in one chord of `S₂`**: two chords of `F₂⁺` attached at one
position whose point is in the domain of `C₂`. -/
theorem tie_parent {e e' : Set Point} (he : e ∈ F₂plus J S₂)
    (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W e p t) (hA' : SideAttach (chainModel J.whole).W e' p t)
    (hKD : sidePt (chainModel J.whole).W p t ∈ J.right.dom) :
    ∃ c ∈ S₂, e ⊆ c ∧ e' ⊆ c := by
  have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
  have hFs : F₂plus J S₂ ⊆ (chainModel J.whole).Adm := F₂plus_subset J hS₂
  set K := sidePt (chainModel J.whole).W p t with hK
  have hKe : K ∈ e := hA.2.2.2.1
  have hKe' : K ∈ e' := hA'.2.2.2.1
  rcases F₂plus_cases J hS₂ he with ⟨c, hc, hec⟩ | ⟨hv, hvy⟩ | ⟨ht, hty⟩
  · exact ⟨c, hc, hec, sub_of_mem_dom J hP hS₂ (hFs he') hc hKe' (hec hKe) hKD⟩
  all_goals
    rcases F₂plus_cases J hS₂ he' with ⟨c, hc, hec⟩ | ⟨hv', hvy'⟩ | ⟨ht', hty'⟩
    · exact ⟨c, hc, sub_of_mem_dom J hP hS₂ (hFs he) hc hKe (hec hKe') hKD, hec⟩
    all_goals exfalso
  -- two chords through points of `C₂` (the shared vertex or the top of `C₂`) on both sides of `K`
  all_goals
    have hdir := hM.tie_pair hFs he he' (Ne.symm hne) hA hA'
  · -- both through the shared vertex
    have hvD : J.shared ≠ K := fun h => J.right.not_mem_set_of_mem_dom (h ▸ hKD) J.shared_mem_right
    grind
  · -- the shared vertex and the top of `C₂` at one height: they coincide
    have hvt : J.shared = J.right.top := shared_eq_top_of_snd J
      (show J.shared.2 = J.right.top.2 by grind).ge
    have hvD : J.shared ≠ K := fun h => J.right.not_mem_set_of_mem_dom (h ▸ hKD) J.shared_mem_right
    grind
  · have hvt : J.shared = J.right.top := shared_eq_top_of_snd J
      (show J.shared.2 = J.right.top.2 by grind).ge
    have hvD : J.shared ≠ K := fun h => J.right.not_mem_set_of_mem_dom (h ▸ hKD) J.shared_mem_right
    grind
  · -- both through the top of `C₂`
    have htD : J.right.top ≠ K := fun h =>
      J.right.not_mem_set_of_mem_dom (h ▸ hKD) J.right.top_mem_set
    grind

/-- **A chord of `F₂⁺` inside a chord `c ∈ S₂`, attached at a point of the domain of `C₂`, is the
chord seen from an endpoint of `c`**: from the left end in the direction `1` or from the right end
in the direction `-1`. -/
theorem piece_of_parent {e c : Set Point} (he : e ∈ F₂plus J S₂) (hc : c ∈ S₂)
    (hec : e ⊆ c) {p : ℕ} {t : ℝ} (hA : SideAttach (chainModel J.whole).W e p t)
    (hKD : sidePt (chainModel J.whole).W p t ∈ J.right.dom) :
    (FreeAt J.whole (Merge.lend c) 1 ∧ e = Merge.shoot J.whole (Merge.lend c) 1) ∨
      (FreeAt J.whole (Merge.rend c) (-1) ∧ e = Merge.shoot J.whole (Merge.rend c) (-1)) := by
  have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
  have hFs : F₂plus J S₂ ⊆ (chainModel J.whole).Adm := F₂plus_subset J hS₂
  obtain ⟨y, l, r, hH, hy, hceq, hl, hr⟩ := Merge.augChords_spec (hS₂ hc)
  have hlD : ((l, y) : Point) ∉ J.whole.dom := fun h => hH.left_not (dom_right J h hy)
  have hrD : ((r, y) : Point) ∉ J.whole.dom := fun h => hH.right_not (dom_right J h hy)
  -- the far end of `e` is an end of `c`
  obtain ⟨a, b, hab, heab, -, hopen, -, -⟩ := hM.ends e (hFs he)
  have hK := hA.2.2.2.1
  set K := sidePt (chainModel J.whole).W p t
  -- an end of `c` lies in `e`
  have hend : ((l, y) : Point) ∈ e ∨ ((r, y) : Point) ∈ e := by
    rcases F₂plus_cases J hS₂ he with ⟨c', hc', hec'⟩ | ⟨hv, -⟩ | ⟨ht, -⟩
    · -- a fused piece: its origin is an end of its chord, which is `c`
      rcases he with ((⟨c₁, hc₁, hfree, rfl⟩ | ⟨c₁, hc₁, hfree, rfl⟩) | hsh) | htop
      · have hc₁S : c₁ ∈ S₂ := by simp_all
        have ho : Merge.lend c₁ ∈ Merge.shoot J.whole (Merge.lend c₁) 1 := origin_mem J
        have hsub : Merge.shoot J.whole (Merge.lend c₁) 1 ⊆ c₁ :=
          Merge.Junction.shoot_lend_subset J (Or.inr (hS₂ hc₁S))
        obtain ⟨y₁, l₁, r₁, hH₁, -, hc₁eq, hl₁, -⟩ := Merge.augChords_spec (hS₂ hc₁S)
        have hsame : c₁ = c := by
          have hKc₁ := hsub hK
          have hKc := hec hK
          rw [hc₁eq] at hKc₁; rw [hceq] at hKc
          rcases Chazelle.Chain.hchordIn_inter hH₁ hH hKc₁ hKc with ⟨rfl, rfl, rfl⟩ | ⟨-, h⟩
          · simp_all
          · exfalso
            rcases h with h | h
            · exact hH.left_not (h ▸ hKD)
            · exact hH.right_not (h ▸ hKD)
        grind
      · have hc₁S : c₁ ∈ S₂ := by simp_all
        have ho : Merge.rend c₁ ∈ Merge.shoot J.whole (Merge.rend c₁) (-1) := origin_mem J
        have hsub : Merge.shoot J.whole (Merge.rend c₁) (-1) ⊆ c₁ :=
          Merge.Junction.shoot_rend_subset J (Or.inr (hS₂ hc₁S))
        obtain ⟨y₁, l₁, r₁, hH₁, -, hc₁eq, -, hr₁⟩ := Merge.augChords_spec (hS₂ hc₁S)
        have hsame : c₁ = c := by
          have hKc₁ := hsub hK
          have hKc := hec hK
          rw [hc₁eq] at hKc₁; rw [hceq] at hKc
          rcases Chazelle.Chain.hchordIn_inter hH₁ hH hKc₁ hKc with ⟨rfl, rfl, rfl⟩ | ⟨-, h⟩
          · simp_all
          · exfalso
            rcases h with h | h
            · exact hH.left_not (h ▸ hKD)
            · exact hH.right_not (h ▸ hKD)
        grind
      · obtain ⟨σ, -, -, rfl⟩ := hsh
        have hv : J.shared ∈ J.whole.chordSet J.m₁ σ := by
          have : J.whole.vertex J.m₁ = J.shared := rfl
          rw [← this]; exact Geometry.left_mem_segment _ _
        have hvc := hec hv
        rw [hceq] at hvc
        obtain ⟨hvy, hvl, hvr⟩ := hvc
        have hvD : J.shared ∉ J.right.dom := fun h =>
          J.right.not_mem_set_of_mem_dom h J.shared_mem_right
        have hvpt : J.shared = ((J.shared.1, y) : Point) := Prod.ext rfl hvy
        rcases hvl.lt_or_eq with h1 | h1
        · rcases hvr.lt_or_eq with h2 | h2
          · exact absurd (by rw [hvpt]; exact hH.open_mem _ h1 h2) hvD
          grind
        grind
      · obtain ⟨σ, -, -, rfl⟩ := htop
        have hv' : J.whole.vertex (J.m₁ + J.right.topIdx) = J.right.top := by
          rw [Merge.Junction.whole_vertex_add]; rfl
        have hv : J.right.top ∈ J.whole.chordSet (J.m₁ + J.right.topIdx) σ := by
          rw [← hv']; exact Geometry.left_mem_segment _ _
        have hvc := hec hv
        rw [hceq] at hvc
        obtain ⟨hvy, hvl, hvr⟩ := hvc
        have hvD : J.right.top ∉ J.right.dom := fun h =>
          J.right.not_mem_set_of_mem_dom h J.right.top_mem_set
        have hvpt : J.right.top = ((J.right.top.1, y) : Point) := Prod.ext rfl hvy
        rcases hvl.lt_or_eq with h1 | h1
        · rcases hvr.lt_or_eq with h2 | h2
          · exact absurd (by rw [hvpt]; exact hH.open_mem _ h1 h2) hvD
          grind
        grind
    · have hvc := hec hv
      rw [hceq] at hvc
      obtain ⟨hvy, hvl, hvr⟩ := hvc
      have hvD : J.shared ∉ J.right.dom := fun h =>
        J.right.not_mem_set_of_mem_dom h J.shared_mem_right
      have hvpt : J.shared = ((J.shared.1, y) : Point) := Prod.ext rfl hvy
      rcases hvl.lt_or_eq with h1 | h1
      · rcases hvr.lt_or_eq with h2 | h2
        · exact absurd (by rw [hvpt]; exact hH.open_mem _ h1 h2) hvD
        grind
      grind
    · have hvc := hec ht
      rw [hceq] at hvc
      obtain ⟨hvy, hvl, hvr⟩ := hvc
      have hvD : J.right.top ∉ J.right.dom := fun h =>
        J.right.not_mem_set_of_mem_dom h J.right.top_mem_set
      have hvpt : J.right.top = ((J.right.top.1, y) : Point) := Prod.ext rfl hvy
      rcases hvl.lt_or_eq with h1 | h1
      · rcases hvr.lt_or_eq with h2 | h2
        · exact absurd (by rw [hvpt]; exact hH.open_mem _ h1 h2) hvD
        grind
      grind
  -- the chord seen from that end
  rcases hend with hle | hre
  · obtain ⟨σ, hσ, hfree, heq⟩ := chord_eq_shoot_of_end J.whole (hFs he) hle hlD
    rcases hσ with rfl | rfl
    · simp_all
    · exfalso
      -- the chord seen to the west from the left end leaves `c`
      obtain ⟨hT0, -, -⟩ := Merge.hit_of_freeAt J.whole
        (by simpa using hy.trans J.right_top_le) (Or.inr rfl) hfree
      have hmem : rayPt ((l, y) : Point) (-1) (J.whole.hitParam (l, y) (-1)) ∈ e := by
        rw [heq]; exact Geometry.right_mem_segment _ _
      have := hec hmem
      rw [hceq] at this
      obtain ⟨-, h1, -⟩ := this
      grind [rayPt_fst]
  · obtain ⟨σ, hσ, hfree, heq⟩ := chord_eq_shoot_of_end J.whole (hFs he) hre hrD
    rcases hσ with rfl | rfl
    · exfalso
      obtain ⟨hT0, -, -⟩ := Merge.hit_of_freeAt J.whole
        (by simpa using hy.trans J.right_top_le) (Or.inl rfl) hfree
      have hmem : rayPt ((r, y) : Point) 1 (J.whole.hitParam (r, y) 1) ∈ e := by
        rw [heq]; exact Geometry.right_mem_segment _ _
      have := hec hmem
      rw [hceq] at this
      obtain ⟨-, -, h1⟩ := this
      grind [rayPt_fst]
    simp_all


end

end Machine

end Sweep

end

end Chazelle.Core
