module

public import Chazelle.MacT
public import Chazelle.Core.ShotListCut
public import Chazelle.Core.ShootCutCore2
public import Chazelle.Core.SweepPrimJun
public import Chazelle.Core.DownPhaseOracleArc
public import Chazelle.Core.SweepPrimKer
public import Chazelle.Core.DownPhaseDrvBCtx
public import Chazelle.Core.OracleQuery
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.GranInitL3
public import Chazelle.Core.DownPhaseDrvRExtSpec

section
set_option hygiene false
local macro "zqwf" : tactic => `(tactic| (have hs1 := lt_of_lt_of_le hs.2 ztwth
                                          have hs2 := lt_of_lt_of_le hs.2 ztwti
                                          have hs3 := lt_of_lt_of_le hs.2 ztgh))
local macro "zqwg" : tactic => `(tactic| (obtain ⟨f', hf', hne, hA'⟩ := htie
                                          obtain ⟨-, hhor, hdn, -⟩ := FW2 f' hf' hne hA'))
local macro "zqwh" : tactic => `(tactic| (set W := (chainModel J.whole).W with hWdef
                                          set W₂ := (chainModel J.right).W with hW₂def
                                          set P := ztlv % W.n with hPdef
                                          set P₂ := ztfw % W₂.n with hP₂def))
local macro "zqwi" : tactic => `(tactic| have hC := corr_right0 J hP hS₂ hS₂f)
local macro "zqwj" : tactic => `(tactic| by_cases htie : ∃ f' ∈ F₂plus J S₂, f' ≠ f ∧ SideAttach W f' Pu 0)
local macro "zqwk" : tactic => `(tactic| (have hn0 := hC.n_pos
                                          have hn₂ := hC.n₂_pos
                                          zubdc
                                          set P' := ztdlg % (chainModel J.whole).W.n with hP'def))
local macro "zqwl" : tactic => `(tactic| rcases hf with ((⟨c₀, hc₀, -, rfl⟩ | ⟨c₀, hc₀, -, rfl⟩) | ⟨σ, -, -, rfl⟩) | ⟨σ, -, -, rfl⟩)
local macro "zqwm" : tactic => `(tactic| (refine Or.inr ⟨hgapV, f', hf', hne, hA', (hdn ztikw).1 rfl, ?_⟩
                                          rcases hpart f' hf' hA' with ⟨c', hc'x, hfc'⟩ | hoff))
local macro "zqwn" : tactic => `(tactic| (obtain ⟨-, -, hp1, hp2, hs1, hs2⟩ := copy_facts J hδ
                                          have hRt := J.right.top_snd_lt_radius
                                          have hA0 := sideTour_sub_top_snd J.right J.right.sideBeta ztdkj
                                          have hB0 := sideTour_sub_top_snd J.right J.right.sideBeta 1))
local macro "zqwo" : tactic => `(tactic| (exfalso
                                          subst h2
                                          rcases h with ⟨h3, h4, h5⟩ | ⟨h3, h4 | h4⟩ | ⟨h3, h4, h5⟩ | ⟨h3, h4, h5 | h5⟩))
local macro "zqwp" : tactic => `(tactic| (obtain ⟨U', hU', hU's⟩ := side_region_exists' hM₂ hSs hSx.1 hc'x ztp
                                          obtain ⟨V', hV', hU'V'⟩ := super_region ztoip hU'))
local macro "zqwq" : tactic => `(tactic| obtain ⟨FW1, FW2⟩ := faced_or_middle hGM hF hf hfA hρ hG hGs hdirF)
local macro "zqwr" : tactic => `(tactic| (obtain ⟨b1, b2⟩ := B
                                          obtain ⟨a1, a2⟩ := A
                                          zulsl
                                          simp only [sideCcw, sideCross, sideDot] at h ⊢))
local macro "zqws" : tactic => `(tactic| (obtain ⟨y, a, b, -, hy, rfl, -, -⟩ := Merge.augChords_spec (hS₂ hc₀')
                                          rw [hz'.1]; exact hy))
local macro "zqwt" : tactic => `(tactic| refine ⟨d - 1, by_omega, 1 - s, ⟨by_linarith, by_grind⟩, ?_, ?_, ?_⟩)
local macro "zqwu" : tactic => `(tactic| obtain ⟨s, hs0, -, rfl⟩ := hseg z hz)
local macro "zqwv" : tactic => `(tactic| (have hGM : ztebh := Or.inl ⟨J.whole, hP, rfl⟩
                                          have hGM₂ : ztebh := Or.inl ztkis))
local macro "zqww" : tactic => `(tactic| have hc₀' : c₀ ∈ S₂ := by_simp_all)
local macro "zqwx" : tactic => `(tactic| obtain ⟨U, hU, hUV, hUs⟩ := sub_region_side hM₂ ztoip hSs hSx.1 hc hρ hV hVs)
local macro "zqwy" : tactic => `(tactic| (obtain ⟨s, hs0, -, rfl⟩ := hseg' z by_grind
                                          zvnap; linarith))
local macro "zqwz" : tactic => `(tactic| rcases hρ with rfl | rfl)
local macro "zqxa" : tactic => `(tactic| by_cases htie₂ : ∃ c'' ∈ S₂x J S₂, c'' ≠ c ∧ SideAttach W₂ c'' P₂ 0)
local macro "zqxb" : tactic => `(tactic| (push Not at htie₂
                                          exact FV1 fun c'' hc'' hA'' => by_contra fun h => htie₂ c'' hc'' h hA''))
local macro "zqxc" : tactic => `(tactic| (have hSx := S₂x_family J hS₂ hF
                                          have hM := hC.hM
                                          zuglq
                                          have hFs := hC.hF))
set_option hygiene true

/-!
# The sweep (WP-D), part 8b: chains of chords without `TopStrict` (F2)

With ties at the top of `C₂` (other points of `C₂` at the height `h` of its top `u`), two
things change in the walk along a chain of collinear chords (`SweepChain`):

* a chord of `F₂⁺` in a tie may be a top chord of `C` at `u` ending on `C₂`: it is then an
  augmented chord of `C₂` itself, and the walk tracks it through the family
  `S₂x = S₂ ∪ (F₂⁺ ∩ augChords C₂)` of the model of `C₂` (`local_step2`);
* in case G the chain may reach the split vertex (the copy of `u` in the right stretch), where the
  model of `C₂` has its slit: there the tracked region of `S₂` may switch to the region on the
  other side of the slit, and both are the gap labels (`split_step`).

The walk (`half_walk2`, `end_bound2`) concludes a label, a bound, or a pair of gap labels, and
lemma (E) holds in the weakened form of (K3) (`label_side_gen2`).

* `shared_eq_top_of_snd`: the shared vertex at the height of the top is the top (least index).
* `S₂x`, `corr_right0x`: the enlarged family and its correspondence.
* `OffOut`, `partner_cases`: a chord of `F₂⁺` attached in the stretch is an augmented chord of
  `C₂`, or its other end is off the stretch.
-/
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft sideLeftOf sideCcw
  sideCross sideDot freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp)
open WalkEmbed
namespace Sweep
section Generic
theorem exists_of_eventually_gt {P : ℝ → Prop} (h : ∀ᶠ s in 𝓝[>] (0 : ℝ), P s) :
    ∃ δ > (0 : ℝ), ∀ s, 0 < s → s < δ → P s := by
  zuvg
  exact ⟨u, hu, fun s h0 h1 => hsub by_simp_all⟩

/-- Keys just before a key inside an open cyclic interval are inside it. -/
theorem sideInArc_eventually_sub {a b x : ℝ} (h : sideInArc a b x) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), sideInArc a b ztfvh := by
  zusg
  zudwd
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT zthkj]
      with s hs hs'
    grind
  · zuy
    · zuhdc

    · zusq
      grind
theorem faces_mono {M : Model} {p : ℕ} {t : ℝ} {U V : Set Point} (h : M.Faces p t U)
    (hUV : U ⊆ V) : M.Faces p t V :=
  h.mono by_grind
variable {M : Model} {p : ℕ} {t : ℝ} {U V : Set Point}
theorem afterFaces_mono (h : AfterFaces M p t U)
    (hUV : U ⊆ V) : AfterFaces M p t V := by
  obtain ⟨δ, hδ, h⟩ := h
  exact ⟨δ, hδ, fun s h0 h1 h2 => faces_mono by_simp_all hUV⟩
theorem beforeFaces_mono
    (h : BeforeFaces M p t U) (hUV : U ⊆ V) : BeforeFaces M p t V := by
  obtain ⟨δ, hδ, h1, h2⟩ := h
  exact ⟨δ, hδ, fun ht s h0 h1' h2' => faces_mono by_simp_all hUV,
    fun ht s h0 h1' => faces_mono by_simp_all hUV⟩
theorem facedSide_mono {t ρ dir : ℝ} {U V : Set Point}
    (h : FacedSide M p t ρ dir U) (hUV : U ⊆ V) : FacedSide M p t ρ dir V :=
  ⟨fun h' => afterFaces_mono (h.1 h') hUV, fun h' => beforeFaces_mono (h.2 h') hUV⟩
theorem sideOf_mono {ρ : ℝ} {c U V : Set Point} (h : SideOf M ρ c U)
    (hUV : U ⊆ V) : SideOf M ρ c V :=
  fun z hz hzD => (h z hz hzD).mono by_grind

/-- An admissible chord has a point in the domain. -/
theorem adm_mem_dom (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) :
    ∃ z ∈ c, z ∈ M.D := by
  obtain ⟨a, b, -, hcab, -, hopen, -, -⟩ := hM.ends c hc
  refine ⟨lerp a b ztcn, ?_, by_grind⟩
  zummz
  zujus

/-- Every chord of a finite admissible family has a region on each side. -/
theorem side_region_exists' (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) :
    ∃ U ∈ M.regions F, SideOf M ρ c U := by
  zucsh
  zqwz
  · exact ztkyg
  · exact ⟨Dn, hDn, fun z hz hzD => (hside z hz hzD).mono fun δ h => by
      simpa [sub_eq_add_neg] using h.2⟩

/-- A region of a finer family lies in a region of a coarser one. -/
theorem super_region {M : Model} {F F' : Set ztf} (hFF : F ⊆ F') {U : Set Point}
    (hU : U ∈ M.regions F') : ∃ V ∈ M.regions F, U ⊆ V := by
  zugqz
  have hsub : ztpos :=
    sdiff_subset_sdiff_right ztvdf
  refine ⟨connectedComponentIn _ z, ⟨z, hsub hz, rfl⟩, ?_⟩
  exact (isPreconnected_connectedComponentIn).subset_connectedComponentIn
    ztvyu ztdeh

/-- **The region of a finer family on a side of a chord** lies in the region of the coarser
family on that side. -/
theorem sub_region_side (hM : WalkAx M) {F F' : Set ztf} (hFF : F ⊆ F')
    (hF' : F' ⊆ M.Adm) (hfin : F'.Finite) {c : Set Point} (hc : c ∈ F') {ρ : ℝ}
    (hρ : ρ = 1 ∨ ρ = -1) {V : Set Point} (hV : V ∈ M.regions F) (hVs : SideOf M ρ c V) :
    ∃ U ∈ M.regions F', U ⊆ V ∧ SideOf M ρ c U := by
  obtain ⟨U, hU, hUs⟩ := side_region_exists' hM hF' hfin hc hρ
  refine ⟨U, hU, ?_, hUs⟩
  obtain ⟨z, hz, hzD⟩ := adm_mem_dom hM (hF' hc)
  obtain ⟨δ, h1, h2⟩ := ((hUs z hz hzD).and (hVs z hz hzD)).exists
  have hsub : ztpos :=
    sdiff_subset_sdiff_right ztvdf
  obtain ⟨w, -, rfl⟩ := hU
  exact subset_region hV isPreconnected_connectedComponentIn
    ztdeh h1 h2
end Generic

/-! ## The shared vertex at the top height -/
section Basic
variable (J : Merge.Junction)

/-- **The shared vertex at the height of the top of `C₂` is the top** (`topIdx` is the least
index of a topmost vertex, and the shared vertex is vertex `0` of `C₂`). -/
theorem shared_eq_top_of_snd (h : J.right.top.2 ≤ J.shared.2) : J.shared = J.right.top := by
  have h0 : J.right.topIdx = 0 := by
    apply Nat.le_zero.1
    refine J.right.topIdx_min ztbg fun i hi => ?_
    rw [J.right_vertex_zero]
    exact (J.right.vertex_snd_le_top hi).trans h
  show J.shared = J.right.vertex J.right.topIdx
  rw [h0, J.right_vertex_zero]
variable {S₂ : Set (Set Point)}
/-- **The chords of `F₂⁺` are not above the top of `C₂`.** -/
theorem F₂plus_snd_le (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {f : Set Point} (hf : f ∈ F₂plus J S₂) {z : Point} (hz : z ∈ f) : z.2 ≤ J.right.top.2 := by
  zqwl
  · zqww
    have hz' := J.shoot_lend_subset by_grind hz
    zqws
  · zqww
    have hz' := J.shoot_rend_subset by_grind hz
    zqws
  · zugbs
    rw [hz.1, Merge.Junction.whole_vertex_m₁]
    exact J.right.snd_le_top_of_mem_set J.shared_mem_right
  · zugbs
    rw [hz.1, Merge.Junction.whole_vertex_add]
    rfl

/-- **The kinds of chords of `F₂⁺`**: inside a chord of `S₂`, through the shared vertex, or
through the top of `C₂`. -/
theorem F₂plus_kind (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {f : Set Point} (hf : f ∈ F₂plus J S₂) :
    (∃ c ∈ S₂, f ⊆ c) ∨ J.shared ∈ f ∨ J.right.top ∈ f := by
  zqwl
  · zqww
    exact Or.inl ⟨c₀, hc₀', J.shoot_lend_subset by_grind⟩
  · zqww
    exact Or.inl ⟨c₀, hc₀', J.shoot_rend_subset by_grind⟩
  · zuhl
    rw [← Merge.Junction.whole_vertex_m₁]
    zucvg
  · zulw
    show J.right.vertex J.right.topIdx ∈ _
    rw [← Merge.Junction.whole_vertex_add]
    zucvg
end Basic

/-! ## The enlarged family of `C₂` -/
section Family
variable (J : Merge.Junction)

/-- **The family of `C₂` along the stretch**: `S₂` together with the chords of `F₂⁺` that are
augmented chords of `C₂` (such as a top chord of `C` at the top of `C₂` ending on `C₂`). -/
def S₂x (S₂ : Set ztf) : Set ztf :=
  S₂ ∪ {e | e ∈ F₂plus J S₂ ∧ e ∈ Merge.augChords J.right}
theorem subset_S₂x (S₂ : Set ztf) : S₂ ⊆ S₂x J S₂ := subset_union_left
variable {S₂ : Set (Set Point)}
theorem S₂x_subset (hS₂ : S₂ ⊆ Merge.augChords J.right) :
    S₂x J S₂ ⊆ Merge.augChords J.right := by
  rintro c (hc | ⟨-, hc⟩)
  · grind
  omega
theorem S₂x_finite (hS₂f : S₂.Finite) : (S₂x J S₂).Finite :=
  hS₂f.union ((F₂plus_finite J hS₂f).subset by_simp_all)
theorem S₂x_family {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) :
    (chainModel J.right).ChordFamily Q zttdg := by
  refine ⟨S₂x_finite J hS₂.1, S₂x_subset J hS₂.2.1, ?_⟩
  rintro c (hc | ⟨hc, -⟩)
  · exact hS₂.2.2 c hc
  · exact hF.2.2 c hc

/-- **The right correspondence with the enlarged family.** -/
theorem corr_right0x (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) :
    Corr0 ztbm ztj ztbi zttdg
      ztve ztbrv ztns ztqvh ztpg := by
  zqwi
  refine { hC with hS := S₂x_subset J hS₂, hSfin := S₂x_finite J hS₂f, trans := ?_ }
  rintro c (hc | ⟨hcF, -⟩) q hq hqD hqv
  · exact hC.trans c hc q hq hqD hqv
  grind

/-- The other attachments of a chord of `F₂⁺` are off the open right stretch. -/
def OffOut (f : Set Point) (P : ℕ) (t : ℝ) : Prop :=
  ∀ (p' : ℕ) (t' : ℝ), SideAttach (chainModel J.whole).W f p' t' →
    sidePt (chainModel J.whole).W p' t' ≠ sidePt (chainModel J.whole).W P t →
    ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztjg ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztjg <
        ((rL1 J + rL2 J : ℕ) : ℝ))

/-- **The points of the stretch are not in the domain of `C₂`.** -/
theorem stretch_not_dom₂ (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p : ℕ}
    (hp : p < (chainModel J.whole).W.n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hin : 0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztk ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztk <
        ((rL1 J + rL2 J : ℕ) : ℝ)) :
    sidePt (chainModel J.whole).W p t ∉ J.right.dom := by
  zqwi
  zucib

  have hd : ztizq := by
    have h := hin.2
    rw [hoff] at h
    zuhdh
    zufc
  rw [← hpd, hC.sidePt_eq hd t]
  exact hC.hM₂.trace _ ztfoj t ht0 ht1.le

/-- **A chord of `F₂⁺` attached in the right stretch is an augmented chord of `C₂`, or its other
end is off the stretch.** -/
theorem partner_cases (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {f : Set Point}
    (hf : f ∈ F₂plus J S₂) {p : ℕ} {t : ℝ} (hA : SideAttach (chainModel J.whole).W f p t)
    (hin : 0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztk ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztk <
        ((rL1 J + rL2 J : ℕ) : ℝ)) :
    f ∈ Merge.augChords J.right ∨ OffOut J f p t := by
  by_cases hfA : f ∈ Merge.augChords J.right
  · simp_all
  right
  intro p' t' hB hne hin'
  zqwi
  zust
  obtain ⟨y, a, b, hH, -, rfl, -, -⟩ := Merge.augChords_spec ztleo
  have hw := stretch_not_dom₂ J hP hS₂ hS₂f hA.1 hA.2.1 hA.2.2.1 hin
  have hw' := stretch_not_dom₂ J hP hS₂ hS₂f hB.1 hB.2.1 hB.2.2.1 hin'
  have hwD := hM.trace _ hA.1 t hA.2.1 hA.2.2.1.le
  have hwD' := hM.trace _ hB.1 t' hB.2.1 hB.2.2.1.le
  have hyh : y ≤ J.right.top.2 := by
    have := F₂plus_snd_le J hS₂ hf hA.2.2.2.1
    rwa [hA.2.2.2.1.1] at this
  -- an end of a point of the chord off the domain
  have hend : ∀ z ∈ Visibility.hseg y a b, z ∉ (chainModel J.whole).D → z.1 = a ∨ z.1 = b := by
    rintro z ⟨hzy, hza, hzb⟩ hzD
    rcases hza.lt_or_eq with h1 | h1
    · rcases hzb.lt_or_eq with h2 | h2
      · exact absurd (show z ∈ (chainModel J.whole).D by
          rw [show z = zthlk from Prod.ext rfl hzy]; exact hH.open_mem z.1 h1 h2) hzD
      simp_all
    simp_all
  have hpt : ∀ z ∈ Visibility.hseg y a b, z.1 = a ∨ z.1 = b → z = ztdv ∨ z = ztdy := by
    rintro z ⟨hzy, -, -⟩ (h | h)
    · grind
    grind
  apply hfA
  refine ⟨y, a, b, ⟨hH.lt, ?_, ?_, fun x h1 h2 => ?_⟩, hyh, rfl⟩
  rotate_right
  · exact dom_right J ztrrl by_omega
  all_goals
    intro hD
    have e1 := hpt _ hA.2.2.2.1 (hend _ hA.2.2.2.1 hwD)
    have e2 := hpt _ hB.2.2.2.1 (hend _ hB.2.2.2.1 hwD')
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;>
      first
      | exact by_simp_all
      | (zvmxy at hw; exact hw hD)
      | (zvnlz at hw'; exact hw' hD)
end Family

/-! ## Junction facts without `TopStrict` -/
section JunctionFacts2
variable (J : Merge.Junction)

/-- **`RLabel` from the positions just after a position of the right stretch.** -/
theorem rlabel_after2 (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {G V : Set Point}
    (hW : AfterFaces ztbm
      ztbn t G)
    (hW₂ : AfterFaces ztj
      ztwmz t V) :
    RLabel J S₂ G V := by
  zqwi
  zucte

  obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_after hC.hM hC.hF hC.hfin
    ztwlh).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < min ztkaw ztca from
      lt_min ztdvj by_linarith))).exists
  zubqy

/-- **`RLabel` from the positions just before a position of the right stretch.** -/
theorem rlabel_before2 (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J) {G V : Set Point}
    (hW : BeforeFaces ztbm
      ztbn t G)
    (hW₂ : BeforeFaces ztj
      ztwmz t V) :
    RLabel J S₂ G V := by
  zqwi
  zubjl

  · obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_before hC.hM hC.hF hC.hfin
      ztwlh).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < min _ t from
        lt_min ztdvj htpos))).exists
    zqwf
    refine ⟨d, hd, t - s, ztomq, ?_, by_grind,
      h2a htpos s hs.1 hs2 hs3⟩
    grind
  · zugij

    zqwk
    have hPm : ztwoi := by
      zugdg
    zuccz
    have hdq1 : ztxda := by
      have := (hsec rfl).2; unfold dq; split_ifs <;> omega
    have hPm₂ : ztwpj % (chainModel J.right).W.n =
        (ztfw % (chainModel J.right).W.n +
          (chainModel J.right).W.n - 1) % (chainModel J.right).W.n := by
      zuhlo
    obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_before hC.hM hC.hF hC.hfin
      ztcro).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < min _ 1 from
        lt_min ztdvj one_pos))).exists
    zqwf
    zqwt
    · grind
    · zubii
    grind

/-- **A chord of `S₂` containing a chord of `F₂⁺` attached at a position of the right stretch is
attached at the corresponding position of the walk of `C₂`.** -/
theorem attach_counterpart2 (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J)
    {f c : Set Point} (hf : f ∈ F₂plus J S₂) (hc : c ∈ Merge.augChords J.right) (hfc : f ⊆ c)
    (hfA : SideAttach (chainModel J.whole).W f
      ztbn t) :
    SideAttach (chainModel J.right).W c
      ztwmz t := by
  zqwi
  set w := sidePt (chainModel J.whole).W (ztlv %
    (chainModel J.whole).W.n) t with hwdef
  zuhfu
  rw [← hwdef] at hw₂
  have hwD₂ : w ∉ J.right.dom := by
    rw [← hw₂]; exact hC.hM₂.trace _ ztfoj t ht0 ht1.le
  obtain ⟨y, a, b, hH, -, hcdef, -, -⟩ := Merge.augChords_spec hc
  obtain ⟨y₁, a₁, b₁, hH₁, -, hfdef⟩ := F₂plus_subset J hS₂ hf
  have hwf := hfA.2.2.2.1
  have hwc := hfc hwf
  obtain ⟨rf, hrf, hlf⟩ := hfA.2.2.2.2
  have hsecEq := hC.sideLeft_eq hd hsec
  have hab₁ := hH₁.lt
  refine ⟨Nat.mod_lt _ hC.n₂_pos, ht0, ht1, by_simp_all, min rf (b₁ - a₁),
    by simp_all, fun x hx hxne hxd => ?_⟩
  rw [hw₂] at hxne hxd
  rw [← hsecEq]
  refine hlf x ?_ hxne by_simp_all
  have hxd' : dist x w < b₁ - a₁ := by_simp_all
  have hx1 : |x.1 - w.1| < b₁ - a₁ := by
    have := (le_max_left _ _).trans_lt by_omega
    omega
  rw [hfdef] at hwf hfc ⊢
  rw [hcdef] at hwc hfc hx
  obtain ⟨hwy₁, hwa₁, hwb₁⟩ := hwf
  zugpu
  obtain ⟨hxy, hxa, hxb⟩ := hx
  obtain ⟨hy1, ha1, -⟩ : ((a₁, y₁) : Point) ∈ Visibility.hseg y a b := hfc ⟨rfl, le_rfl, hab₁.le⟩
  obtain ⟨-, -, hb1⟩ : ((b₁, y₁) : Point) ∈ Visibility.hseg y a b := hfc ⟨rfl, hab₁.le, le_rfl⟩
  simp only at hy1 ha1 hb1
  -- `w` is an endpoint of `c`
  have hwend : w.1 = a ∨ w.1 = b := by
    zukmp
    · zukmq
      · exact absurd (show w ∈ J.right.dom by
          zunqm; exact hH.open_mem w.1 h1 h2) hwD₂
      grind
    grind
  refine ⟨by_grind, ?_, ?_⟩ <;> rcases hwend with h | h <;>
    zvncj at hx1 <;> linarith [hx1.1, hx1.2]

/-- **No tie at the top of `C₂`** on the right stretch: two chords of `F₂⁺` are never attached at
one position of the right stretch whose point is the top of `C₂` (the corresponding position of
the walk of `C₂` is next to the slit). -/
theorem no_tie_at_top2 (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ} (hd : d < rL1 J + rL2 J)
    (hsec : d ≠ 0 ∧ d ≠ rL1 J) {e e' : Set Point} (he : e ∈ F₂plus J S₂)
    (he' : e' ∈ F₂plus J S₂) (hne : e ≠ e')
    (hA : SideAttach (chainModel J.whole).W e
      ztbn 0)
    (hA' : SideAttach (chainModel J.whole).W e'
      ztbn 0)
    (htop : sidePt (chainModel J.whole).W
      ztbn 0 = J.right.top) : False := by
  zqwi
  zust
  have hF := hC.hF
  zqwh
  have hsec' : zthoa := by_omega
  -- east and west chords
  obtain ⟨ce, cw, hce, hcw, hAe, hAw, hE, hW⟩ : ∃ ce cw, ce ∈ F₂plus J S₂ ∧ cw ∈ F₂plus J S₂ ∧
      SideAttach W ce P 0 ∧ SideAttach W cw P 0 ∧ (∀ z ∈ ce, (sidePt W P 0).1 ≤ z.1) ∧
      (∀ z ∈ cw, z.1 ≤ (sidePt W P 0).1) := by
    rcases hM.tie_pair hF he he' hne hA hA' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨e, e', he, he', hA, hA', h1, h2⟩
    · exact ⟨e', e, he', he, hA', hA, h2, h1⟩
  zucbd
  obtain ⟨-, hhor, -⟩ := hM.tie_shape hF hce hcw hAe hAw hE hW
  have hv : (chainModel J.whole).wa P = J.right.top := by
    rw [← htop, Chazelle.Chain.sidePt_zero]; rfl
  have hv₂ : W₂.vtx P₂ = J.right.top := by
    have := hC.sidePt_eq hd 0
    zuigi
    rw [← this, ← htop, Chazelle.Chain.sidePt_zero]
  have hnext : (chainModel J.whole).wb P = W₂.vtx ((P₂ + 1) % W₂.n) := hC.sideNext_eq hd
  have hprev : W.vtx ((P + W.n - 1) % W.n) = W₂.vtx ((P₂ + W₂.n - 1) % W₂.n) := by
    have := hC.sidePrev_eq hd hsec'
    zulvb

  -- the position of the walk of `C₂` at its top is a tour vertex
  have hP₂n : P₂ < W₂.n := Nat.mod_lt _ hC.n₂_pos
  obtain ⟨-, i, hi, hP₂i, -⟩ := pos_eq_vertex J.right hP J.right.sideBeta hP₂n le_rfl
    zero_lt_one J.right.topIdx_le (by rw [Chazelle.Chain.sidePt_zero]; exact hv₂)
  zuuy
  have hm1 := J.right.one_le
  zujei
  · -- the leaving edge goes down: the upward direction is in the sector
    have hB2 : ((chainModel J.whole).wb P - (chainModel J.whole).wa P).2 < 0 := by
      zujnv
    obtain ⟨-, hX⟩ := Tie.ccw_down hs₂ hB2 hsW
    have hup : ∀ ε > (0 : ℝ), sideLeft W₂ P₂ 0 (ztpzg : Point) := by
      zudik
      rw [← hC.sideLeft_eq hd hsec', Chazelle.Chain.sideLeft_zero]
      unfold Chazelle.Chain.sideLeftOf
      have key := hX ((ztpzg : Point) - (chainModel J.whole).wa P)
        (Or.inr (Or.inl (by zvmyq; simp only [Prod.snd_sub]; linarith)))
      zvmyq at key
      have hvP : (chainModel J.whole).W.vtx
          ztbn = J.right.top := hv
      rw [hvP]
      exact key
    obtain ⟨r, hr, hsf⟩ := sector_free hC.hM₂ hC.hS hC.hSfin hP₂n le_rfl zero_lt_one
    rw [Chazelle.Chain.sidePt_zero, hv₂] at hsf
    have hR := J.right.top_snd_lt_radius
    set ε := min ztzr ztmya with hε
    zusv
    have hxD := (hsf _ (by
      zukxn
      simp only [Real.dist_eq, sub_self, abs_zero, add_sub_cancel_left, abs_of_pos hε0]
      rw [max_eq_right hε0.le]
      exact lt_of_le_of_lt ztff by_linarith) (hup ε hε0)).1
    apply hxD.2
    right
    show _ ∈ Chazelle.segment _ _
    zuewp
    refine ⟨ε / (J.right.radius - J.right.top.2), by_positivity, ?_, ?_⟩
    · zunwx; linarith [min_le_right ztzr ztmya]
    · zufqm
      · simp [Geometry.lerp, Chain.slitTop]
      · simp only [Geometry.lerp_snd, Chain.slitTop]
        rw [div_mul_cancel₀ _ by_linarith]
  · -- the leaving edge goes up: both neighbours would be above the top
    have hB2 : 0 < ((chainModel J.whole).wb P - (chainModel J.whole).wa P).2 := by
      zujnv
    obtain ⟨hA2, -⟩ := Tie.ccw_up hs₁ hB2 hsE
    rw [hnext, hv] at hB2
    rw [hprev, show (chainModel J.whole).wa P = W.vtx P from rfl] at hA2
    have hvP : W.vtx P = J.right.top := hv
    rw [hvP] at hA2
    simp only [Prod.snd_sub] at hB2 hA2
    rw [hP₂i] at hB2 hA2
    rcases lt_or_eq_of_le hi with hi' | hi'
    · have e1 : ztcim % W₂.n = ztg + 6 := by
        rw [hn₂, show i + 6 + 1 = ztg + 6 by ring]; exact Nat.mod_eq_of_lt by_omega
      rw [e1, hW₂def, cm_W, J.right.sideWalk_vtx_tour _ by_omega] at hB2
      have := J.right.vertex_snd_le_top (J.right.sideIdx_le J.right.sideBeta ztg)
      unfold Chain.sideTour at hB2
      linarith
    · have e1 : (i + 6 + W₂.n - 1) % W₂.n = ztei + 6 := by
        rw [hn₂, show i + 6 + ztqf - 1 = ztqrc + ztqf by
          omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
      rw [e1, hW₂def, cm_W, J.right.sideWalk_vtx_tour _ by_omega] at hA2
      have := J.right.vertex_snd_le_top (J.right.sideIdx_le J.right.sideBeta ztei)
      unfold Chain.sideTour at hA2
      linarith

/-- **`RLabel` from the positions just before a vertex position of the stretch** (offset
`1 ≤ d ≤ rL1 + rL2`): the corresponding positions of the walk of `C₂` are those just before the
position following the counterpart of `d - 1`.  This covers the split vertex (`d = rL1`, case G)
and the end of the stretch (`d = rL1 + rL2`). -/
theorem rlabel_before0_2 (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ} (hd1 : 1 ≤ d)
    (hd : d ≤ rL1 J + rL2 J) {G V : Set Point}
    (hW : BeforeFaces ztbm
      ztbn 0 G)
    (hW₂ : BeforeFaces ztj
      ztbalh 0 V) :
    RLabel J S₂ G V := by
  zqwi
  zucbq

  zqwk
  have hPm : ztwoi := by
    zugdh
  have hPm₂ : ztwpj % (chainModel J.right).W.n =
      (ztwlf % (chainModel J.right).W.n +
        (chainModel J.right).W.n - 1) % (chainModel J.right).W.n := by
    zuilr

  obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_before hC.hM hC.hF hC.hfin
    ztcro).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < min ztkaw 1 from
      lt_min ztdvj one_pos))).exists
  zqwf
  zqwt
  · grind
  · zubii
  grind
end JunctionFacts2

/-! ## The local step with the enlarged family -/
section Local2
variable (J : Merge.Junction)

/-- **The local step without `TopStrict`.**  As `local_step`, with the chord `c ⊇ f` of the
model of `C₂` taken in the enlarged family `S₂x`; the partner at a tie is inside a chord of
`S₂x` with `V` on its side `ρ`, or its other end is off the stretch. -/
theorem local_step2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J)
    {f c : Set Point} (hf : f ∈ F₂plus J S₂) (hc : c ∈ S₂x J S₂) (hfc : f ⊆ c)
    (hfA : SideAttach (chainModel J.whole).W f
      ztbn t)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G V : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hV : V ∈ (chainModel J.right).regions S₂) (hGs : SideOf ztbm ρ f G)
    (hVs : SideOf ztj ρ c V) :
    RLabel J S₂ G V ∨ (t = 0 ∧ ∃ f' ∈ F₂plus J S₂, f' ≠ f ∧
      SideAttach (chainModel J.whole).W f' (ztlv %
        (chainModel J.whole).W.n) 0 ∧ SideOf (chainModel J.whole) ρ f' G ∧
      ((∃ c' ∈ S₂x J S₂, f' ⊆ c' ∧ SideOf ztj ρ c' V) ∨
        (ztbym ∧
          OffOut J f' ztbn 0))) := by
  zucf
  have hCx := corr_right0x J hP hS₂.2.1 hS₂.1
  zqxc
  have hSs := hCx.hS
  zqwx
  zqwh
  have hcA :=
    attach_counterpart2 J hP hS₂.2.1 hS₂.1 hd ht0 ht1 hsec hf (S₂x_subset J hS₂.2.1 hc) hfc hfA
  zuhfu
  zqwv
  -- the common direction of `f` and `c`
  obtain ⟨dir, hdirF, hdirC⟩ : ∃ dir : ℝ,
      ((dir = 1 ∧ ∀ z ∈ f, (sidePt W P t).1 ≤ z.1) ∨ (dir = -1 ∧ ∀ z ∈ f, z.1 ≤ (sidePt W P t).1)) ∧
      ((dir = 1 ∧ ∀ z ∈ c, (sidePt W₂ P₂ t).1 ≤ z.1) ∨
        (dir = -1 ∧ ∀ z ∈ c, z.1 ≤ (sidePt W₂ P₂ t).1)) := by
    rw [hw₂]
    rcases hM₂.attach_dir ztjxo hcA with h | h <;> rw [hw₂] at h
    · exact ⟨1, Or.inl ztygd, by_grind⟩
    · exact ⟨-1, Or.inr ztygd, by_grind⟩
  zqwq
  obtain ⟨FV1, FV2⟩ := faced_or_middle hGM₂ hSx hc hcA hρ hU hUs hdirC
  -- facing on the same side gives the label
  have hRL : FacedSide ztbm P t ρ dir G →
      FacedSide ztj P₂ t ρ dir U → RLabel J S₂ G V := by
    zujay
    have h2' := facedSide_mono h2 hUV
    have hρd : ρ * dir = -1 ∨ ρ * dir = 1 := by
      rcases hρ with rfl | rfl <;> rcases hdirF with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
    zukmx
    · exact rlabel_after2 J hP hS₂.2.1 hS₂.1 hd ht0 ht1 (h1.1 h) (h2'.1 h)
    · exact rlabel_before2 J hP hS₂.2.1 hS₂.1 hd ht0 ht1 hsec (h1.2 h) (h2'.2 h)
  by_cases htie : ∃ f' ∈ F₂plus J S₂, f' ≠ f ∧ SideAttach W f' P t
  swap
  · -- no tie
    zucyh
    have huW : ∀ e' ∈ F₂plus J S₂, SideAttach W e' P t → e' = f := by
      intro e' he' hA'
      zuct
      exact htie e' he' hne hA'
    have huW₂ : ∀ c' ∈ S₂x J S₂, SideAttach W₂ c' P₂ t → c' = c := by
      zujax
      obtain ⟨e'', he'', hec'', -, hA''⟩ := hCx.transfer hd ht0 ht1 hsec hc' hA'
      have := huW e'' he'' hA''
      zumo
      exact s2_eq_of_sub J zthcp hc' hc (F₂plus_subset J hS₂.2.1 he'') hec''
        hfc
    exact Or.inl (hRL (FW1 huW) (FV1 huW₂))
  -- a tie
  obtain ⟨f', hf', hne, hA'⟩ := htie
  obtain ⟨ht00, hhor, hdn, hup⟩ := FW2 f' hf' hne hA'
  subst ht00
  have hsec0 := hsec rfl
  have hwa : (chainModel J.right).wa P₂ = (chainModel J.whole).wa P := by
    have := hC.sidePt_eq hd 0
    zuigi
    exact this.symm
  have hwb : (chainModel J.right).wb P₂ = (chainModel J.whole).wb P := (hC.sideNext_eq hd).symm
  -- the faced case in `W₂`
  have hfaced₂ : ((chainModel J.whole).wb P).2 < ((chainModel J.whole).wa P).2 → ρ = -1 →
      FacedSide ztj P₂ 0 ρ dir U := by
    intro hdown hρ1
    zqxa
    · zufis
      obtain ⟨-, -, h1, -⟩ := FV2 c'' hc'' hne'' hA''
      zuisn
    · zqxb
  have hfaced₂' : ((chainModel J.whole).wa P).2 < ((chainModel J.whole).wb P).2 → ρ = 1 →
      FacedSide ztj P₂ 0 ρ dir U := by
    intro hupd hρ1
    zqxa
    · zufis
      obtain ⟨-, -, -, h1⟩ := FV2 c'' hc'' hne'' hA''
      zuisn
    · zqxb
  -- the middle case in `W₂`, for a partner inside a chord of `S₂x`
  have hmid₂ : ∀ c' ∈ S₂x J S₂, f' ⊆ c' →
      (((chainModel J.whole).wb P).2 < ((chainModel J.whole).wa P).2 → ρ = 1 →
        SideOf ztj ρ c' V) ∧
      (((chainModel J.whole).wa P).2 < ((chainModel J.whole).wb P).2 → ρ = -1 →
        SideOf ztj ρ c' V) := by
    intro c' hc' hfc'
    have hc'A :=
      attach_counterpart2 J hP hS₂.2.1 hS₂.1 hd le_rfl zero_lt_one hsec hf'
        (S₂x_subset J hS₂.2.1 hc') hfc' hA'
    have hc'c : c' ≠ c := by
      zunq
      rcases hdirC with ⟨-, hc1⟩ | ⟨-, hc1⟩ <;> rw [hw₂] at hc1
      · exact hne (hM.attach_east_unique hFs hf' hf hA' hfA ztkwj
          ztyqz)
      · exact hne (hM.attach_west_unique hFs hf' hf hA' hfA ztkwj
          ztyqz)
    obtain ⟨-, -, h1, h2⟩ := FV2 c' hc' hc'c hc'A
    exact ⟨fun hd' hρ1 => sideOf_mono ((h1 ztdlz).1 hρ1) hUV,
      fun hu' hρ1 => sideOf_mono ((h2 ztdlz).1 hρ1) hUV⟩
  -- the partner: an augmented chord of `C₂`, or its other end is off the stretch
  have hpartner : ztkyc ∨
      (ztbym ∧ OffOut J f' P 0) := by
    have hin : 0 < off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztnns ∧
        off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztnns < ((rL1 J + rL2 J : ℕ) : ℝ) := by
      have e := hC.off_M hd le_rfl zero_lt_one
      zui
      have h1 : ztpgl := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hsec0.1
      have h2 : ztbrp := by exact_mod_cast hd
      zulea
    zuebo
    · exact Or.inl ztmqj
    rcases partner_cases J hP hS₂.2.1 hS₂.1 hf' hA' hin with h | h
    · exact Or.inl ztkyj
    · exact Or.inr ⟨hkind, h⟩
  rcases lt_or_gt_of_ne hhor with hdown | hupd
  · zqwz
    · refine Or.inr ⟨rfl, f', hf', hne, hA', (hdn hdown).1 rfl, ?_⟩
      zufln
      · exact Or.inl ⟨c', hc', hfc', (hmid₂ c' hc' hfc').1 hdown rfl⟩
      · exact Or.inr hsh
    · exact Or.inl (hRL ((hdn hdown).2 rfl) (hfaced₂ hdown rfl))
  · zqwz
    · exact Or.inl (hRL ((hup hupd).2 rfl) (hfaced₂' hupd rfl))
    · refine Or.inr ⟨rfl, f', hf', hne, hA', (hup hupd).1 rfl, ?_⟩
      zufln
      · exact Or.inl ⟨c', hc', hfc', (hmid₂ c' hc' hfc').2 hupd rfl⟩
      · exact Or.inr hsh
end Local2

/-! ## Horizontal directions at the split vertex -/
section SplitGeo
variable {a x : ℝ} {A B : Point} {W : Polygon} {c : Set Point} {p : ℕ}
/-- **A west direction of a corner below the horizontal** lies in the corner from the upward
slit (converse of `ccw_lower_left`). -/
theorem ccw_corner_west (ha : 0 < a) (hA : A.2 ≤ 0) (hB : B.2 ≤ 0)
    (h : sideCcw B (ztcxb : Point) A) (hx : x < 0) :
    sideCcw (ztfmp : Point) (ztcxb : Point) A := by
  zqwr
  have hxa : 0 < -(a * x) := by_nlinarith
  rcases lt_trichotomy a1 0 with h1 | h1 | h1
  · zukkr
    · left
      exact ztkiy
    · zqwo
      · nlinarith
      · have hb : b2 < 0 := by_nlinarith
        nlinarith
      · nlinarith
      · have hb : ztsdt := by
          grind
        simp_all
      · simp_all
      · have hb : ztsdt := by
          grind
        zulsy
        have : b1 < 0 := by_nlinarith
        nlinarith
  · zucuj
    zukkr
    · zurx
      exact ztrat
    simp_all
  · zujga

/-- **An east direction of a corner below the horizontal** lies in the corner to the upward
slit (converse of `ccw_lower_right`). -/
theorem ccw_corner_east (ha : 0 < a) (hA : A.2 ≤ 0) (hB : B.2 ≤ 0)
    (h : sideCcw B (ztcxb : Point) A) (hx : 0 < x) :
    sideCcw B (ztcxb : Point) (ztfmp : Point) := by
  zqwr
  have hxa : 0 < x * a := by_nlinarith
  rcases lt_trichotomy b1 0 with h1 | h1 | h1
  · zuhl
    exact ztugb
  · zucuj
    zukks
    · zurx
      exact ztrat
    simp_all
  · zukks
    · left
      exact ztkiy
    · zqwo
      · nlinarith
      · nlinarith
      · nlinarith
      · nlinarith
      · simp_all
      · nlinarith

/-- **An admissible chord through a point off the domain** is a horizontal segment from it. -/
theorem seg_of_end {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {u : Point}
    (hu : u ∈ c) (huD : u ∉ M.D) : ∃ w, w ≠ u ∧ w.2 = u.2 ∧ c = Chazelle.segment u w := by
  obtain ⟨a, b, hab, heq, hy, hopen, -, -⟩ := hM.ends c hc
  have hue' := hu
  zudac

  zunm
  · zuji
    · simp_all
    · zuikp
      exact ⟨a, by_simp_all, by_simp_all, by
        zuobk⟩
  · zuhny
    grind

/-- The direction of a horizontal segment attached at a vertex position lies in its left
sector. -/
theorem sideLeft_of_attach_seg {u w : Point}
    (hpu : sidePt W p 0 = u) (hA : SideAttach W c p 0) (hcw : c = Chazelle.segment u w)
    {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T)
    (hray : ∀ s, 0 ≤ s → s ≤ T → rayPt u σ s ∈ Chazelle.segment u w) :
    sideLeft W p 0 zthzn := by
  zuddt
  zuiop
  zucmx
  have hz := hl (rayPt u σ ε) by_grind
    (by
      rw [hpu]; intro h
      have := congrArg Prod.fst h; zvnap at this
      grind)
    (by
      rw [hpu, dist_rayPt _ hσ hε0.le]
      simp_all)
  rw [← hpu] at hz ⊢
  zuisi

/-- A horizontal segment from the point of a vertex position, with its direction in the left
sector, is attached there. -/
theorem attach_of_sideLeft_seg (hp : p < W.n)
    {u w : Point} (hpu : sidePt W p 0 = u) {σ T : ℝ} (hsl : sideLeft W p 0 zthzn)
    (hcw : c = Chazelle.segment u w)
    (hseg : ∀ z ∈ Chazelle.segment u w, ∃ s, 0 ≤ s ∧ s ≤ T ∧ z = rayPt u σ s) :
    SideAttach W c p 0 := by
  refine ⟨hp, le_rfl, zero_lt_one, by rw [hpu, hcw]; exact Geometry.left_mem_segment _ _, 1,
    one_pos, fun z hz hzu _ => ?_⟩
  rw [hcw] at hz
  zqwu
  have hs : ztxx := by
    zuvl
    · zubh
    · exfalso; apply hzu; rw [← h, hpu]; simp
  rw [← hpu] at hsl ⊢
  zuish

/-- Two horizontal segments from `u` sharing a point other than `u` have the same direction. -/
theorem ray_dir_eq {u : Point} {σ σ' T T' : ℝ} (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1)
    (hT : 0 < T) (hmem : ∃ s, 0 ≤ s ∧ s ≤ T' ∧ rayPt u σ T = rayPt u σ' s) : σ = σ' := by
  obtain ⟨s, hs0, -, h⟩ := hmem
  zuftb
  zvnap at h1
  zuzq
  · rfl
  · grind
  · grind
  · rfl
end SplitGeo

/-! ## The split vertex of the right stretch (case G) -/
section Split

/-- **The regions around a vertex position that is not a cut**: one region is faced just before
and just after it. -/
theorem faces_around_vertex {M : Model} (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {p : ℕ} (hp : p < M.W.n) (hp0 : 0 < p)
    (hcut : ¬ M.IsCut F (p : ℝ)) :
    ∃ X ∈ M.regions F, AfterFaces M p 0 X ∧ BeforeFaces M p 0 X := by
  zukeq
  zucsj
  have hfac := harc.2.2.2.2.2.2
  obtain ⟨δ₁, hδ₁, h1⟩ := exists_of_eventually_gt ztkfe
  obtain ⟨δ₂, hδ₂, h2⟩ := exists_of_eventually_gt ztwdy
  refine ⟨X, hX, ⟨δ₁, hδ₁, fun s h0 h1' h2' => ?_⟩,
    ⟨min δ₂ 1, lt_min hδ₂ one_pos, fun h => absurd h ztgkw, fun _ s h0 h1' => ?_⟩⟩
  · simp_all
  · zukfp
    have hsδ : ztslx := by_simp_all
    rw [prev_mod hp hp0]
    refine hfac _ _ by_omega by_linarith by_linarith ?_
    simp_all
variable (J : Merge.Junction)

/-- The two copies of the top of `C₂` next to the slit, in the walk of `C₂` (case G). -/
theorem copy_facts (hδ : 0 < rδ J) :
    ztuk % (chainModel J.right).W.n = 2 * J.right.m + 6 ∧
    ztjp % (chainModel J.right).W.n = 6 ∧
    sidePt (chainModel J.right).W ztwua 0 =
      J.right.top ∧
    sidePt (chainModel J.right).W
      ztwty 0 = J.right.top ∧
    (∀ x, sideLeft (chainModel J.right).W
        ztwua 0 x ↔
      sideLeftOf ztztp J.right.top
        J.right.slitTop x) ∧
    (∀ x, sideLeft (chainModel J.right).W
        ztwty 0 x ↔
      sideLeftOf J.right.slitTop J.right.top ztsym x) := by
  obtain ⟨g1, g2, v26, v0, v25, v6, v5, v7⟩ := gap_walk J hδ
  zuuy
  zueri
  have g2' : ztymc := by
    grind
  refine ⟨g1, g2', by rw [g1, Chazelle.Chain.sidePt_zero, v26],
    by rw [g2', Chazelle.Chain.sidePt_zero, v6], fun x => ?_, fun x => ?_⟩
  · rw [g1, Chazelle.Chain.sideLeft_zero]
    have e1 : (2 * J.right.m + 6 + 1) % (chainModel J.right).W.n = 0 := by
      simp_all
    have e2 : (2 * J.right.m + 6 + (chainModel J.right).W.n - 1) % (chainModel J.right).W.n =
        2 * J.right.m + 5 := by
      rw [hn₂, show 2 * J.right.m + 6 + ztqf - 1 = ztgcc +
        ztqf by omega, Nat.add_mod_right]
      simp
    simp_all
  · rw [g2', Chazelle.Chain.sideLeft_zero]
    have e1 : ztsua % (chainModel J.right).W.n = 7 := by
      zupbv; exact Nat.mod_eq_of_lt by_omega
    have e2 : ztfzt := by
      rw [hn₂, show 6 + ztqf - 1 = 5 + ztqf by omega,
        Nat.add_mod_right]
      simp
    grind

/-- **The direction of a chord at a copy of the split vertex**: a chord of `C₂` attached at the
copy before the slit goes west, at the copy after it east. -/
theorem copy_dir (hP : J.P.Simple) (hδ : 0 < rδ J) {c : Set Point}
    (hc : c ∈ Merge.augChords J.right) :
    (SideAttach (chainModel J.right).W c
        ztwua 0 →
      ∀ z ∈ c, z.1 ≤ J.right.top.1) ∧
    (SideAttach (chainModel J.right).W c
        ztwty 0 →
      ∀ z ∈ c, J.right.top.1 ≤ z.1) := by
  zubnr
  zqwn
  have shape : ∀ P : ℕ, sidePt (chainModel J.right).W P 0 = J.right.top →
      SideAttach (chainModel J.right).W c P 0 → ∃ σ T : ℝ, ztdd ∧ 0 < T ∧
        sideLeft (chainModel J.right).W P 0 (rayPt J.right.top σ 1) ∧
        ∀ z ∈ c, ∃ s, 0 ≤ s ∧ s ≤ T ∧ z = rayPt J.right.top σ s := by
    intro P hpu hA
    have hu := hpu ▸ hA.2.2.2.1
    have huD : J.right.top ∉ (chainModel J.right).D := by
      rw [← hpu]; exact hM₂.trace _ hA.1 0 le_rfl zero_le_one
    obtain ⟨w, hwu, hwy, hcw⟩ := seg_of_end hM₂ hc hu huD
    zudey
    exact ⟨σ, T, hσ, hT, sideLeft_of_attach_seg hpu hA hcw hσ hT hray,
      by simp_all⟩
  constructor
  · intro hA
    obtain ⟨σ, T, hσ, -, hsl, hseg⟩ := shape _ hp1 hA
    rw [hs1] at hsl
    zufqf

    have hneg := ccw_up_left by_linarith hA0 hsl
    zugh
    zqwu
    zudln
    nlinarith
  · intro hA
    obtain ⟨σ, T, hσ, -, hsl, hseg⟩ := shape _ hp2 hA
    rw [hs2] at hsl
    zufqf

    have hpos := ccw_up_right by_linarith hB0 hsl
    zugh
    zqwu
    zudln
    nlinarith

/-- **The copy of a chord at the split vertex**: a chord of `C` attached at the split vertex of
the right stretch, inside an augmented chord `c` of `C₂`, goes west and `c` is attached at the
copy before the slit, or it goes east and `c` is attached at the copy after the slit. -/
theorem split_copy (hP : J.P.Simple) (hδ : 0 < rδ J) {f c : Set Point}
    (hf : f ∈ Merge.augChords J.whole) (hc : c ∈ Merge.augChords J.right) (hfc : f ⊆ c)
    (hfA : SideAttach (chainModel J.whole).W f
      ztif 0) :
    (ztgnt ∧ SideAttach (chainModel J.right).W c
        ztwua 0) ∨
      (ztgns ∧ SideAttach (chainModel J.right).W c
        ztwty 0) := by
  zucvz
  zubnr
  zugpq
  zqwn
  have hn₂ : ztphm := by zvokr; omega
  zukzy
  have huf := hpt ▸ hfA.2.2.2.1
  have huD : ztpqg := by
    zvnbr; exact hM.trace _ hfA.1 0 le_rfl zero_le_one
  obtain ⟨w, hwu, hwy, hfw⟩ := seg_of_end hM hf huf huD
  obtain ⟨σ, T, hσ, hT, hray, -⟩ := seg_ray hwu hwy
  have hslM := sideLeft_of_attach_seg hpt hfA hfw hσ hT hray
  rw [hsec] at hslM
  unfold sideLeftOf at hslM
  rw [rayPt_sub_self] at hslM
  -- the shape of `c`
  have huD₂ := fun h =>
    J.right.not_mem_set_of_mem_dom h J.right.top_mem_set
  obtain ⟨w', hwu', hwy', hcw⟩ := seg_of_end hM₂ hc (hfc huf) huD₂
  obtain ⟨σ', T', hσ', -, -, hseg'⟩ := seg_ray hwu' hwy'
  have hσσ : σ = σ' := by
    refine ray_dir_eq (u := u) (T' := T') hσ hσ' hT ?_
    have : rayPt u σ T ∈ Chazelle.segment u w' := by
      rw [← hcw]; exact hfc (hfw ▸ hray T hT.le le_rfl)
    obtain ⟨s, hs0, hs1', he⟩ := hseg' _ this
    exact ⟨s, hs0, hs1', he⟩
  subst hσσ
  zur
  · right
    refine ⟨fun z hz => ?_, attach_of_sideLeft_seg ztbar hp2 ?_ hcw hseg'⟩
    · zqwy
    · rw [hs2]
      zucfg
      zukyn
      exact ccw_corner_east by_linarith hA0 hB0 hslM one_pos
  · left
    refine ⟨fun z hz => ?_, attach_of_sideLeft_seg ztbar hp1 ?_ hcw hseg'⟩
    · zqwy
    · rw [hs1]
      zucfg
      zukyn
      exact ccw_corner_west by_linarith hA0 hB0 hslM by_norm_num
end Split

/-! ## The split step -/
section SplitStep
variable (J : Merge.Junction)

/-- **No chord of `S₂` at the other copy of the split vertex** when a single chord of `F₂⁺` is
attached at the split vertex of the right stretch (case G): its piece at the top of `C₂` would be
attached there too. -/
theorem other_copy_not_cut (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) (hδ : 0 < rδ J) {f c : Set Point}
    (hf : f ∈ F₂plus J S₂) (hc : c ∈ Merge.augChords J.right) (hfc : f ⊆ c)
    (hfA : SideAttach (chainModel J.whole).W f
      ztif 0)
    (huniq : ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e'
      ztif 0 → e' = f) :
    (ztgnt → ¬ (chainModel J.right).IsCut S₂
      ((ztjp % (chainModel J.right).W.n : ℕ) : ℝ)) ∧
    (ztgns → ¬ (chainModel J.right).IsCut S₂
      ((ztuk % (chainModel J.right).W.n : ℕ) : ℝ)) := by
  zqwi
  zuglq
  obtain ⟨hpt, -⟩ := split_facts J hδ
  zuddw
  obtain ⟨hL1, -, -, -, -⟩ := caseG_consts J hδ
  zubtn
  zuuy
  have huD₂ := fun h =>
    J.right.not_mem_set_of_mem_dom h J.right.top_mem_set
  have hunV : J.right.top ≠ (chainModel J.right).W.vtx ztbrv := by
    rw [← hp1]
    have hoff := off_key hC.hg' (show rL1 J < (chainModel J.right).W.n by omega) le_rfl
      zero_lt_one
    have h1 : ztida := by exact_mod_cast by_grind
    have hL := hC.hfull hδ
    have h2 : (rL1 J : ℝ) + 1 ≤ ((rL1 J + rδ J + rL2 J : ℕ) : ℝ) := by
      zuhuk
    refine hC.noV _ ztfoj 0 le_rfl zero_lt_one ?_ ?_
    · grind
    grind
  -- a chord of `S₂` at a copy of the split vertex is `c`
  have hsame : ∀ k : ℕ, ztecn → ∀ c'' ∈ S₂,
      SideAttach (chainModel J.right).W c'' (ztnhq %
        (chainModel J.right).W.n) 0 →
      sidePt (chainModel J.right).W ztqp 0 =
        J.right.top → c'' = c := by
    intro k hk c'' hc'' hA'' hpk
    have hu'' := hpk ▸ hA''.2.2.2.1
    obtain ⟨e'', he'', hue'', hec''⟩ := hC.trans c'' hc'' _ hu'' huD₂ hunV
    have heA := splitAttach_right J hP hS₂ hδ k hk c'' hc'' hA'' e'' he'' hec''
      by_grind
    have := huniq e'' he'' heA
    zumo
    exact s2_eq_of_sub J subset_rfl (hS₂ hc'') hc
      (F₂plus_subset J hS₂ he'') hec'' hfc
  -- `c` does not go both ways
  have hboth : ztgnt → ztgns → False := by
    intro hW hE
    have hu := hfc (hpt ▸ hfA.2.2.2.1)
    obtain ⟨w, hwu, hwy, hcw⟩ := seg_of_end hM₂ hc hu huD₂
    have hw : ztsmv := by rw [hcw]; exact Geometry.right_mem_segment _ _
    exact hwu (Geometry.point_ext (le_antisymm (hW w hw) (hE w hw)) hwy)
  constructor
  · rintro hW ⟨c'', hc'', p, t, hA'', hkey⟩
    obtain ⟨hp, ht⟩ := Chazelle.Chain.sideKey_inj le_rfl zero_lt_one hA''.2.1 hA''.2.2.1
      (show ((ztjp % (chainModel J.right).W.n : ℕ) : ℝ) + 0 =
        p + t by zvncl; exact hkey)
    zulte
    have hA2 : SideAttach (chainModel J.right).W c''
        (ztbpg % (chainModel J.right).W.n) 0 := by
      grind
    have hcc := hsame _ ztbt c'' hc'' hA2 by_grind
    zulat
    exact hboth hW ((copy_dir J hP hδ hc).2 hA'')
  · rintro hE ⟨c'', hc'', p, t, hA'', hkey⟩
    obtain ⟨hp, ht⟩ := Chazelle.Chain.sideKey_inj le_rfl zero_lt_one hA''.2.1 hA''.2.2.1
      (show ((ztuk % (chainModel J.right).W.n : ℕ) : ℝ) + 0 =
        p + t by zvncl; exact hkey)
    zulte
    have hcc := hsame _ ztp c'' hc'' hA'' hp1
    zulat
    exact hboth ((copy_dir J hP hδ hc).1 hA'') hE
end SplitStep
section SplitStep2
variable (J : Merge.Junction)

/-- **The split step** (case G).  Let `f ∈ F₂⁺`, inside a chord `c` of `S₂x`, be attached at the
split vertex of the right stretch, with `G` on its side `ρ` and `V` on the side `ρ` of `c`.
Then `V` is a label of `G`; or `V` is a gap label and `G` has a gap label; or `V` is a gap label
and the split vertex is a tie whose other chord `f'` (with `G` on its side `ρ` too) lies in a
chord of `S₂x` whose side `ρ` is a gap label, or has its other end off the stretch. -/
theorem split_step (hP : J.P.Simple) {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) (hδ : 0 < rδ J)
    {f c : Set Point} (hf : f ∈ F₂plus J S₂) (hc : c ∈ S₂x J S₂) (hfc : f ⊆ c)
    (hfA : SideAttach (chainModel J.whole).W f
      ztif 0)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G V : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hV : V ∈ (chainModel J.right).regions S₂) (hGs : SideOf ztbm ρ f G)
    (hVs : SideOf ztj ρ c V) :
    RLabel J S₂ G V ∨ (GapLab J S₂ V ∧ ∃ Vg, GapLab J S₂ Vg ∧ RLabel J S₂ G Vg) ∨
      (GapLab J S₂ V ∧ ∃ f' ∈ F₂plus J S₂, f' ≠ f ∧ SideAttach (chainModel J.whole).W f'
        ztif 0 ∧
        SideOf ztbm ρ f' G ∧
        ((∃ c' ∈ S₂x J S₂, f' ⊆ c' ∧ ∃ V' ∈ (chainModel J.right).regions S₂,
            SideOf ztj ρ c' V' ∧ GapLab J S₂ V') ∨
          (ztbym ∧
            OffOut J f' ztif 0))) := by
  zucf
  zqxc
  have hSs := S₂x_subset J hS₂.2.1
  zqwv
  zudrg
  zubtn
  zunc
  zucgj

  obtain ⟨hk1, hk2, hp1, hp2, -, -⟩ := copy_facts J hδ
  zuuy
  zurn
  zudgi

  set k₁ := ztuk % W₂.n with hk₁def
  set k₂ := ztjp % W₂.n with hk₂def
  set u := J.right.top with hudef
  have hk₂' : ztbpg % W₂.n = k₂ := by_grind
  have hk1n : k₁ < W₂.n := by_omega
  have hk2n : k₂ < W₂.n := by_omega
  -- the region of `S₂x` on the side `ρ` of `c`
  zqwx
  -- labels from the positions around the split vertex
  have hRLa : ∀ X, AfterFaces ztbm Pu 0 G →
      AfterFaces ztj k₂ 0 X → RLabel J S₂ G X := by
    zumgi
    refine rlabel_after2 J hP hS₂.2.1 hS₂.1 hd le_rfl zero_lt_one h1 ?_
    have e : 6 + tpos J.right 0 + dq ztns ztpg ztns =
        6 + tpos J.right 0 + rL1 J + rδ J := by
      zudcm
    zujhz
  have hRLb : ∀ X, BeforeFaces ztbm Pu 0 G →
      BeforeFaces ztj k₁ 0 X → RLabel J S₂ G X := by
    zumgi
    refine rlabel_before0_2 J hP hS₂.2.1 hS₂.1 hL1pos hd.le h1 ?_
    have e : 6 + tpos J.right 0 + (dq ztns ztpg (rL1 J - 1) + 1) =
        6 + tpos J.right 0 + rL1 J := by
      zudcm
    zujhz
  -- the leaving edge at the split vertex is not above it
  have hwa : (chainModel J.whole).wa Pu = u := by
    zuhnw
  have hwb : ((chainModel J.whole).wb Pu).2 ≤ u.2 := by
    have e := hC.sideNext_eq hd
    have edq : ztygr := by
      zumsl
    zuchk
    rw [edq, g2] at e
    have e7 : sideNext W₂ 6 = J.right.sideTour J.right.sideBeta 1 := by
      zufdc
    show (sideNext W Pu).2 ≤ u.2
    rw [e, e7]
    have := sideTour_sub_top_snd J.right J.right.sideBeta 1
    zuipa

  have hinPu : 0 < off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zteiu ∧
      off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zteiu < ((rL1 J + rL2 J : ℕ) : ℝ) := by
    zucca

  have hdw : ∀ f' ∈ F₂plus J S₂, f' ≠ f → SideAttach W f' Pu 0 →
      ((chainModel J.whole).wb Pu).2 ≠ ((chainModel J.whole).wa Pu).2 →
      ((chainModel J.whole).wb Pu).2 < ((chainModel J.whole).wa Pu).2 := by
    grind
  have hpart : ∀ f' ∈ F₂plus J S₂, SideAttach W f' Pu 0 → ztkyc ∨
      (ztbym ∧ OffOut J f' Pu 0) := by
    intro f' hf' hA'
    zuebo
    · exact Or.inl ztmqj
    rcases partner_cases J hP hS₂.2.1 hS₂.1 hf' hA' hinPu with h | h
    · exact Or.inl ztkyj
    grind
  rcases split_copy J hP hδ (F₂plus_subset J hS₂.2.1 hf) ztjxo hfc hfA with
    ⟨hcW, hAk⟩ | ⟨hcE, hAk⟩
  · -- `c` goes west, attached at the copy before the slit
    have hdirF : ((-1 : ℝ) = 1 ∧ ∀ z ∈ f, (sidePt W Pu 0).1 ≤ z.1) ∨
        ((-1 : ℝ) = -1 ∧ ∀ z ∈ f, z.1 ≤ (sidePt W Pu 0).1) :=
      Or.inr ⟨rfl, fun z hz => by zvmxe; exact hcW z ztfhu⟩
    have hdirC : ((-1 : ℝ) = 1 ∧ ∀ z ∈ c, (sidePt W₂ k₁ 0).1 ≤ z.1) ∨
        ((-1 : ℝ) = -1 ∧ ∀ z ∈ c, z.1 ≤ (sidePt W₂ k₁ 0).1) :=
      Or.inr ztgtd
    zqwq
    have hFV := (faced_or_middle hGM₂ hSx hc hAk hρ hU hUs hdirC).1 (fun c'' hc'' hA'' =>
      oneAt_right J hP zthcp hδ _ ztp c'' hc'' c hc hA'' hAk)
    zqwz
    · -- above `c`: the west side of the slit
      have hgapV : ztpke :=
        ⟨hδ, hV, Or.inl ztoxy⟩
      right
      zqwj
      · zqwg
        zqwm
        · left
          rcases split_copy J hP hδ ztrjl ztvtz hfc' hA' with
            ⟨hW', -⟩ | ⟨hE', hAk'⟩
          · exact absurd (hM.attach_west_unique hFs hf' hf hA' hfA
              (fun z hz => by zvmxe; exact hW' z ztvve)
              (fun z hz => by zvmxe; exact hcW z ztfhu)) hne
          · zqwp
            have hdirC' : ((1 : ℝ) = 1 ∧ ∀ z ∈ c', (sidePt W₂ k₂ 0).1 ≤ z.1) ∨
                ((1 : ℝ) = -1 ∧ ∀ z ∈ c', z.1 ≤ (sidePt W₂ k₂ 0).1) :=
              Or.inl ⟨rfl, fun z hz => by rw [hp2]; exact hE' z hz⟩
            have hFV' := (faced_or_middle hGM₂ hSx hc'x hAk' ztp hU' hU's hdirC').1
              (fun c'' hc'' hA'' => oneAt_right J hP zthcp hδ _
                ztbt c'' hc'' c' hc'x zteqa
                zteqa)
            exact ⟨c', hc'x, hfc', V', hV', sideOf_mono hU's hU'V', hδ, hV',
              Or.inr (beforeFaces_mono (hFV'.2 by_norm_num) hU'V')⟩
        · exact Or.inr hoff
      · zucyh
        have huniq :=
          fun e' he' hA' => by_contra fun h => htie e' he' h hA'
        have hGa := (FW1 huniq).1 by_norm_num
        have hnc := (other_copy_not_cut J hP hS₂.2.1 hS₂.1 hδ hf ztjxo hfc hfA huniq).1 hcW
        obtain ⟨X, hX, hXa, hXb⟩ := faces_around_vertex hGM₂ hS₂ hk2n by_omega
          hnc
        exact Or.inl ⟨hgapV, X, ⟨hδ, hX, Or.inr hXb⟩, hRLa X hGa hXa⟩
    · -- below `c`: faced before the split vertex in both walks
      left
      have hGb : BeforeFaces ztbm Pu 0 G := by
        zqwj
        · zqwg
          exact ((hdn ztikw).2 rfl).2 by_norm_num
        · zucyh
          exact (FW1 fun e' he' hA' => by_contra fun h => htie e' he' h hA').2 by_norm_num
      exact hRLb V hGb ztoyb
  · -- `c` goes east, attached at the copy after the slit
    have hdirF : ((1 : ℝ) = 1 ∧ ∀ z ∈ f, (sidePt W Pu 0).1 ≤ z.1) ∨
        ((1 : ℝ) = -1 ∧ ∀ z ∈ f, z.1 ≤ (sidePt W Pu 0).1) :=
      Or.inl ⟨rfl, fun z hz => by zvmxe; exact hcE z ztfhu⟩
    have hdirC : ((1 : ℝ) = 1 ∧ ∀ z ∈ c, (sidePt W₂ k₂ 0).1 ≤ z.1) ∨
        ((1 : ℝ) = -1 ∧ ∀ z ∈ c, z.1 ≤ (sidePt W₂ k₂ 0).1) :=
      Or.inl ztgte
    zqwq
    have hFV := (faced_or_middle hGM₂ hSx hc hAk hρ hU hUs hdirC).1 (fun c'' hc'' hA'' =>
      oneAt_right J hP zthcp hδ _ ztbt c'' hc'' c hc
        zteqa zteqa)
    zqwz
    · -- above `c`: the east side of the slit
      have hgapV : ztpke :=
        ⟨hδ, hV, Or.inr ztoyb⟩
      right
      zqwj
      · zqwg
        zqwm
        · left
          rcases split_copy J hP hδ ztrjl ztvtz hfc' hA' with
            ⟨hW', hAk'⟩ | ⟨hE', -⟩
          · zqwp
            have hdirC' : ((-1 : ℝ) = 1 ∧ ∀ z ∈ c', (sidePt W₂ k₁ 0).1 ≤ z.1) ∨
                ((-1 : ℝ) = -1 ∧ ∀ z ∈ c', z.1 ≤ (sidePt W₂ k₁ 0).1) :=
              Or.inr ⟨rfl, fun z hz => by zuowo; exact hW' z hz⟩
            have hFV' := (faced_or_middle hGM₂ hSx hc'x hAk' ztp hU' hU's hdirC').1
              (fun c'' hc'' hA'' => oneAt_right J hP zthcp hδ _
                ztp c'' hc'' c' hc'x hA'' hAk')
            exact ⟨c', hc'x, hfc', V', hV', sideOf_mono hU's hU'V', hδ, hV',
              Or.inl (afterFaces_mono (hFV'.1 by_norm_num) hU'V')⟩
          · exact absurd (hM.attach_east_unique hFs hf' hf hA' hfA
              (fun z hz => by zvmxe; exact hE' z ztvve)
              (fun z hz => by zvmxe; exact hcE z ztfhu)) hne
        · exact Or.inr hoff
      · zucyh
        have huniq :=
          fun e' he' hA' => by_contra fun h => htie e' he' h hA'
        have hGb := (FW1 huniq).2 by_norm_num
        have hnc := (other_copy_not_cut J hP hS₂.2.1 hS₂.1 hδ hf ztjxo hfc hfA huniq).2 hcE
        obtain ⟨X, hX, hXa, hXb⟩ := faces_around_vertex hGM₂ hS₂ hk1n by_omega
          hnc
        exact Or.inl ⟨hgapV, X, ⟨hδ, hX, Or.inl hXa⟩, hRLb X hGb hXb⟩
    · -- below `c`: faced after the split vertex in both walks
      left
      have hGa : AfterFaces ztbm Pu 0 G := by
        zqwj
        · zqwg
          exact ((hdn ztikw).2 rfl).1 by_norm_num
        · zucyh
          exact (FW1 fun e' he' hA' => by_contra fun h => htie e' he' h hA').1 by_norm_num
      exact hRLa V hGa ztoxy
end SplitStep2
end Sweep
end
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqsf" : tactic => `(tactic| (rw [hd, h03, interior_iff _ _ (x := ⟨e, hc⟩) ht ht1] at b₁; have w₁ := e₁.wb_right; have p32 : ztizk := by rw [r₁ _ by_decide, hE.r32]))
local macro "zqsg" : tactic => `(tactic| have hn7 : ztdh := C.sideWalk_n _)
local macro "zqsh" : tactic => `(tactic| (refine ⟨by zunsp, fun _ => ?_, fun h => absurd q10 h⟩; zuopk))
local macro "zqsi" : tactic => `(tactic| rw [r₁ _ by_decide, r₁ _ by_decide, h01, hE.r85] at h5)
local macro "zqsj" : tactic => `(tactic| have hn : ztdh := C.sideWalk_n _)
set_option hygiene true

/-!
# Sweep RAM primitives (WP-D2), part 8: `arrivalPos`

`arrivalPos` (design-merge-v2 §9.6 item 1).  Input: the walk position `x = (e, h)` of
`chainModel C` in `50201, 50202` (a proper position whose point `w` is strictly inside the
height range of the box) and, in `50203`, the code `ρ` of the **reversed** ray direction: the ray
arrives at `w` in direction `σ = -dirOf ρ` (so its left-sector test is in direction `dirOf ρ`; for
a shot in direction `dirOf v` pass `ρ = 1 - v` if `v ≤ 1`, see `neg_dirOf_flip`).  Output:
`50210 = 1` and a proper position `(p, h')` in `50211, 50212` with
`Sweep.Arrival W w σ p (param (p, h'))`, or `50210 = 0` if no position of `w` is an arrival
position (`ArrRes`).

The machine classifies `x` like `leftSec` (inside an edge, or at a tour vertex), then

* inside an edge: tests the edge; if the test fails, the answer is the twin edge (a slit edge or a
  tour edge; `twin_left`), or none on a vertical side of the box (`wall_none`);
* at the chain vertex `v_k`: tests the candidates `candIdx m S k`, `candIdx m S (2m - k)` and, if
  `k` is the top, `2m` (`cand_complete`, `vertex_positions`).
-/
namespace Chazelle.Core
namespace SweepPrim
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideE sideLeft sidePt)
@[expose] public section
def ArrRes (P : Polygon) (C : Chain) (e h ρ : ℕ) (c' : Config) : Prop :=
  c'.nreg 50210 ≤ 1 ∧
    (c'.nreg 50210 = 1 → c'.nreg 50211 < (chainModel C).W.n ∧
      ProperPos ztc zta P.n ztraz ∧
      Sweep.Arrival (chainModel C).W ztwqb ztdep
        (c'.nreg 50211) ((chainModel C).param zta ztraz)) ∧
    (c'.nreg 50210 ≠ 1 → ∀ p t, ¬ Sweep.Arrival (chainModel C).W
      ztwqb ztdep p t)

/-- Reversing a direction code. -/
theorem neg_dirOf_flip (v : ℕ) : -dirOf (if v = 1 then 0 else 1) = dirOf v := by
  zubqi

/-! ## Mathematics of the answers -/

/-- An arrival position at the point of a proper position. -/
theorem arrival_iff (M : Model) (Q : Polygon) {y : WPos} (hy : y.edge < M.W.n)
    (h0 : 0 ≤ M.param Q y) (h1 : M.param Q y < 1) (σ : ℝ) :
    Sweep.Arrival M.W zttae σ y.edge ztnmv ↔
      sideLeft M.W y.edge ztnmv (Visibility.rayPt zttae (-σ) 1) :=
  ⟨fun h => h.2.2.2.2, fun h => ⟨hy, h0, h1, rfl, h⟩⟩

/-- **The twin edge takes over** when the arriving ray is not in the half-plane of the edge. -/
theorem twin_left (M : Model) (Q : Polygon) {p p' h : ℕ} (hh : 1 ≤ h)
    (h1 : M.wa p' = M.wb p) (h2 : M.wb p' = M.wa p) (ht : 0 < M.param Q ztnk)
    (ht1 : M.param Q ztnk < 1) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hn : ¬ sideLeft M.W p (M.param Q ztnk) (Visibility.rayPt (M.pos Q ztnk) s 1)) :
    sideLeft M.W p' (M.param Q ztcfq) (Visibility.rayPt (M.pos Q ztcfq) s 1) ∧
      M.pos Q ztcfq = M.pos Q ztnk ∧ 0 < M.param Q ztcfq ∧ M.param Q ztcfq < 1 := by
  zubkn
  obtain ⟨hpos, hpar⟩ := twin_pos_param M Q hh h1 h2 hne
  have ht' : 0 < M.param Q ztcfq := by_simp_all
  have ht1' : M.param Q ztcfq < 1 := by_simp_all
  refine ⟨?_, hpos, ht', ht1'⟩
  have hne' : (M.W.vtx p').2 ≠ (M.W.vtx (zttvi % M.W.n)).2 := by
    have := ne_of_param_pos ht'; tauto
  rw [pos_eq_sidePt] at hn ⊢
  rw [sideLeft_interior ht' ht1' hne']
  rw [sideLeft_interior ht ht1 hne] at hn
  have e1 : M.W.vtx p' = M.wa p' := rfl
  have e2 : M.W.vtx _ = M.wb p' := rfl
  have e3 : M.W.vtx p = M.wa p := rfl
  have e4 : M.W.vtx _ = M.wb p := rfl
  rw [e1, e2, h1, h2]
  rw [e3, e4] at hn
  zuhes
  zukmd
  · grind
  grind
variable (C : Chain) {P : Polygon} {W : ℕ} {H : Host} (c : Config)
/-- **No arrival position on a vertical side of the box** when the edge test fails. -/
theorem wall_none (hP : C.P.Simple) {Q : Polygon} {e h : ℕ} (he : e = 1 ∨ e = 3)
    (ht : 0 < (chainModel C).param Q ztcq) (ht1 : (chainModel C).param Q ztcq < 1) {σ : ℝ}
    (hn : ¬ sideLeft (chainModel C).W e ((chainModel C).param Q ztcq)
      (Visibility.rayPt ztwyw (-σ) 1)) :
    ∀ p t, ¬ Sweep.Arrival (chainModel C).W ztwyw σ p t := by
  rintro p t ⟨hp, ht0, ht1', hpt, hl⟩
  rw [pos_eq_sidePt] at hpt hl hn
  obtain ⟨rfl, rfl⟩ := wall_unique C hP he ht ht1 hp ht0 ht1' hpt
  simp_all

/-- **An arrival position at a tour vertex.** -/
theorem arrival_vertex {Q : Polygon} {x : WPos} {i : ℕ} (hi : i ≤ 2 * C.m)
    (hv : (chainModel C).W.vtx ztcy = (chainModel C).pos Q x) {σ : ℝ}
    (hl : sideLeft (chainModel C).W ztcy 0
      ztbans) :
    Sweep.Arrival (chainModel C).W ztte σ ztcy
      ((chainModel C).param Q zteyn) := by
  zqsj
  refine ⟨by_omega, le_refl _, by_positivity, ?_, ?_⟩
  · rw [show (chainModel C).param Q zteyn = 0 from rfl, Chazelle.Chain.sidePt_zero, hv]
  · rw [show (chainModel C).param Q zteyn = 0 from rfl, ← hv]; exact hl

/-- **No arrival position at a chain vertex** when all candidates fail. -/
theorem vertex_none (hP : C.P.Simple) {Q : Polygon} {x : WPos} {k : ℕ}
    (hk : k ≤ C.m) (hv : (chainModel C).pos Q x = C.vertex k) {σ : ℝ}
    (hn : ∀ i, i ≤ 2 * C.m → (i = candIdx C.m ztboi k ∨
        i = candIdx C.m ztboi ztbdr ∨ (i = 2 * C.m ∧ k = C.topIdx)) →
      ¬ sideLeft (chainModel C).W ztcy 0
        ztbans) :
    ∀ p t, ¬ Sweep.Arrival (chainModel C).W ztte σ p t := by
  rintro p t ⟨hp, ht0, ht1, hpt, hl⟩
  zvmyq at hpt hl
  obtain ⟨rfl, i, hi, rfl, hik⟩ := vertex_positions C hP hk hp ht0 ht1 hpt
  have hcand := cand_complete C C.sideBeta hi hik
  refine hn i hi ?_ ?_
  · rcases hcand with h | h | h
    · omega
    · omega
    · refine Or.inr (Or.inr ztcxz)
      zuhnv
  · rw [Chazelle.Chain.sidePt_zero] at hpt
    simp_all

/-- Inside an edge, the edge test is the turning code `1`. -/
theorem interior_iff (M : Model) (Q : Polygon) {x : WPos} (ht : 0 < M.param Q x)
    (ht1 : M.param Q x < 1) (ρ : ℕ) :
    turnCode ztjtx ρ = 1 ↔
      sideLeft M.W x.edge ztbyt (Visibility.rayPt zteng ztern 1) := by
  rw [← interior_bit, pos_eq_sidePt]
  exact (sideLeft_interior ht ht1 (ne_of_param_pos ht)).symm

/-! ## The machine -/

/-- Found at the input position (the flag is already `1`). -/
def foundIn : Stmt := block [.copyN 50211 50201, .copyN 50212 50202]
/-- Found at the up-slit edge `2m + 6`, same height code. -/
def foundTop : Stmt :=
  block [.constN 50210 1, .addN 50211 50053 50053, .addN 50211 50211 50081, .copyN 50212 50202]
/-- Found at the down-slit edge `5`, same height code. -/
def found5 : Stmt := block [.constN 50210 1, .constN 50211 5, .copyN 50212 50202]
/-- Found at the tour edge `50121 + 6`, same height code. -/
def foundT : Stmt := block [.constN 50210 1, .addN 50211 50121 50081, .copyN 50212 50202]
/-- Found at the tour vertex `50121 + 6`. -/
def foundV : Stmt := block [.constN 50210 1, .addN 50211 50121 50081, .constN 50212 0]
/-- No arrival position. -/
def noneS : Stmt := .instr ztsot

/-- Inside an edge of the box block. -/
def boxArr : Stmt := .seq intOut (.ifLtN 50210 50032 (.ifLtN 50201 50085 .skip foundTop) foundIn)

/-- The twin of a tour or up-slit edge. -/
def twinT : Stmt :=
  .seq ztbdp (.seq tvIdx
    (.ifLtN 50120 50058
      (.seq ztirj
        (.seq (.ifLtN 50224 50059 (.instr (.addN 50121 50224 50089))
          (.instr (.subN 50121 50224 50059))) foundT))
      found5))

/-- Inside an edge of the tour or the up-slit edge. -/
def intArr : Stmt := .seq intOut (.ifLtN 50210 50032 twinT foundIn)

/-- The candidate tour step `candIdx m S (r)` into `50121`. -/
def candS (r : ℕ) : Stmt :=
  .ifLtN r 50221 (.instr (.addN 50121 r 50223)) (.instr (.subN 50121 r 50221))

/-- Test the sector of the candidate `50121`; answer or continue. -/
def tryS (rest : Stmt) : Stmt := .seq secAt (.ifLtN 50110 50032 rest foundV)

/-- At a tour vertex: all tour vertices of the same chain vertex. -/
def vtxArr : Stmt :=
  .seq ztbdp (.seq tvIdx
    (.seq (block [.copyN 50220 50091, .copyN 50221 50059, .copyN 50222 50058, .copyN 50223 50089])
      (.seq (candS 50220) (tryS
        (.seq ztnca (.seq ztvlb (tryS
          (.ifLtN 50220 50054 noneS (.ifLtN 50054 50220 noneS
            ztdsg)))))))))

/-- **`arrivalPos`**: the classification of `leftSec`, then the cases. -/
def arrCore : Stmt :=
  .seq ztfex (.seq dirAt
    (.ifLtN 50201 50081 boxArr
      (.ifLtN 50202 50032 vtxArr
        (.ifLtN 10502 50032 vtxArr
          (.seq ztbdp (.seq ztibk
            (.seq ztepm
              (.seq ztilk (.seq ztill
                (.ifLtN 50170 50032 (.ifLtN 50171 50032 vtxArr intArr) intArr))))))))))

/-- **The primitive `arrivalPos`.** -/
def arrivalPos : Stmt := .seq pHead arrCore
theorem wr_arrivalPos : wr Bprim arrivalPos = true := by_decide

/-! ## The vertex case -/

/-- **Testing one candidate tour vertex.** -/
theorem tryS_exec {C : Chain} {rest : Stmt} {K : ℕ}
    (c : Config) (hE : CEnv P W H C c) {e hc ρ i : ℕ} (h03 : c.nreg 50203 = ρ)
    (h121 : c.nreg 50121 = i) (hi : i ≤ 2 * C.m) (hWn : 2 * C.m + 7 ≤ W)
    (hv : (chainModel C).W.vtx ztcy = (chainModel C).pos zta ztev)
    (hrest : ∀ c₁ : Config, CEnv P W H C c₁ → FrameB Bsec c c₁ →
      ¬ sideLeft (chainModel C).W ztcy 0
        (Visibility.rayPt ztwof ztern 1) →
      ∃ c' k, Exec P W rest c₁ c' k ∧ k ≤ K ∧ ArrRes P C e hc ρ c') :
    ∃ c' k, Exec P W (tryS rest) c c' k ∧ k ≤ K + 81 * H.length + 3205 ∧
      ArrRes P C e hc ρ c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hE₁, b₁⟩ := secAt_exec c hE h121 hi
  rw [h03] at b₁
  zud
  by_cases h0 : c₁.nreg 50110 < c₁.nreg 50032
  · rw [hE₁.r32] at h0
    have hn : ¬ sideLeft (chainModel C).W _ 0
        _ := fun h => by
      have := b₁.2.2 h; omega
    obtain ⟨c', k, ex, hk, hr⟩ := hrest c₁ hE₁ f₁ hn
    exact ⟨c', _, .seq e₁ (.ifLtN_true (by rw [hE₁.r32]; exact h0) ex), by_omega, hr⟩
  · have h0' : ¬ c₁.nreg 50110 < 1 := by rw [hE₁.r32] at h0; exact h0
    have hl : sideLeft (chainModel C).W _ 0
        _ :=
      b₁.2.1 (by have := b₁.1; omega)
    have q121 : ztuqi := by rw [f₁.1 _ by_decide, h121]
    obtain ⟨c₂, k₂, e₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W foundV c₁ c₂ k₂ ∧ k₂ = 3 ∧
        (c₂.nreg 50210 = 1 ∧ c₂.nreg 50211 = i + 6 ∧ c₂.nreg 50212 = 0) := by
      unfold foundV
      exec_block
      · omega
      · config_simp; zuopl; omega
      · omega
      · zubee
        config_simp
        zuopl
    zugqn
    zqsj
    refine ⟨c₂, _, .seq e₁ ztnad, by_omega,
      by zunsp, fun _ => ?_, by_omega⟩
    zuopk
    refine ⟨by_omega, ⟨le_refl _, by_positivity, by_simp⟩, ?_⟩
    exact arrival_vertex C hi hv by_simp_all

/-- The candidate computation. -/
theorem candS_exec (hw : WordsBounded W c) {r m S j : ℕ}
    (_hr : r ≠ 50121) (h221 : c.nreg 50221 = S) (h223 : c.nreg 50223 = 2 * m - S)
    (hrj : c.nreg r = j) (hS : S ≤ 2 * m) (_hj : j ≤ 2 * m) (hmW : 2 * m ≤ W) :
    ∃ c' k, Exec P W (candS r) c c' k ∧ k ≤ 3 ∧ c'.nreg 50121 = candIdx m S j ∧
      ∀ r', r' ≠ 50121 → c'.nreg r' = c.nreg r' := by
  unfold candS candIdx
  zujsd
  · refine spec_ifLtN_true by_omega (spec_instr (Exec.addN hw _ _ _
      by_omega) fun _ => ⟨by_omega, ?_, by_simp_all⟩)
    simp_all
  · refine spec_ifLtN_false by_omega (spec_instr ztbbq
      fun _ => ztbfk)
    simp_all

/-- The walk vertex of a candidate is the chain vertex. -/
theorem walk_vtx_cand {i k : ℕ} (hi : i ≤ 2 * C.m) (hk : C.sideIdx C.sideBeta i = k) :
    (chainModel C).W.vtx ztcy = C.vertex k := by
  rw [walk_vtx_tour C hi, hk]

/-- **The vertex case of `arrivalPos`.** -/
theorem vtxArr_exec {C : Chain} (c : Config)
    (hE : CEnv P W H C c) (hP : C.P.Simple) {e hc ρ : ℕ} (h01 : c.nreg 50201 = e)
    (h03 : c.nreg 50203 = ρ) (he6 : 6 ≤ e) (hen : e < 2 * C.m + 7) (hWn : 2 * C.m + 7 ≤ W)
    (hpar : (chainModel C).param zta ztev = 0) :
    ∃ c' k, Exec P W vtxArr c c' k ∧ k ≤ 26000 ∧ ArrRes P C e hc ρ c' := by
  zubgf
  zubb
  zuwi
  zuec
  zubad
  -- the chain vertex
  zuiu
  zudky
  zumz
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, k91, k58, k59, k89, -⟩ := tvIdx_exec c₁ hE₁ (i := e - 6)
    ztirs by_omega
  have hE₂ := hE₁.frame f₂ e₂.wb_right by_decide
  set k := C.sideIdx C.sideBeta _ with hkdef
  have hkm : ztidw := C.sideIdx_le _ _
  have hposx : (chainModel C).pos zta ztev = C.vertex k := by
    rw [pos_eq_sidePt, hpar, Chazelle.Chain.sidePt_zero]
    show (chainModel C).W.vtx e = _
    rw [show e = ztbcs + 6 by omega, walk_vtx_tour C by_omega]
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 50220 50091, .copyN 50221 50059,
      .copyN 50222 50058, .copyN 50223 50089]) c₂ c₃ k₃ ∧ k₃ = 4 ∧
      (c₃.nreg 50220 = k ∧ c₃.nreg 50221 = S ∧ c₃.nreg 50222 = 2 * C.m ∧
        c₃.nreg 50223 = 2 * C.m - S ∧
        ∀ r, r ≠ 50220 → r ≠ 50221 → r ≠ 50222 → r ≠ 50223 → c₃.nreg r = c₂.nreg r) := by
    zuja
    exec_block
    simp_all
  obtain ⟨q20, q21, q22, q23, r₃⟩ := q
  have hE₃ := hE₂.keep e₃.wb_right
    (exec_frameB e₃ (B := fun r => decide (50220 ≤ r ∧ r < 50224)) by_decide).2.2.1
    (fun r hr => r₃ r ztbjp
      ztbjp ztbjp
      ztbjp)
  have s₃ : c₃.nreg 50203 = ρ := by
    rw [r₃ _ by_decide by_decide by_decide by_decide, f₂.1 _ by_decide, hc₁]
    simp_all
  -- the candidates
  obtain ⟨⟨ca1, ca2⟩, ⟨cb1, cb2⟩⟩ := cand_vertex C C.sideBeta hkm
  have hmW : 2 * C.m ≤ W := by_omega
  obtain ⟨c₄, k₄, e₄, hk₄, q121, r₄⟩ := candS_exec (P := P) c₃ e₃.wb_right by_decide q21 q23
    q20 hS by_omega hmW
  have hE₄ := hE₃.keep e₄.wb_right
    (exec_frameB e₄ (B := fun r => r == 50121) by_decide).2.2.1
    (fun r hr => r₄ r ztbjp)
  -- registers kept by the sector procedure
  have kS : ∀ {ca cb : Config}, FrameB Bsec ca cb → ∀ r, 50200 ≤ r → r < 50230 → r ≠ 50210 →
      r ≠ 50211 → r ≠ 50212 → cb.nreg r = ca.nreg r := fun hf r h1 h2 h3 h4 h5 => hf.1 r (by
        interval_cases r <;> first | decide)
  zqsg
  obtain ⟨c', k', ex', hk', res⟩ := tryS_exec (K := 17000) (e := e) (hc := hc) (ρ := ρ)
      (i := candIdx C.m S k) (rest := .seq
      ztnca (.seq ztvlb (tryS
        (.ifLtN 50220 50054 noneS (.ifLtN 50054 50220 noneS
          ztdsg))))) c₄ hE₄
      by_grind q121 ca1 hWn (by rw [walk_vtx_cand C ca1 ca2, hposx]) (by
    intro c₅ hE₅ f₅ hn₁
    have g₅ := kS f₅
    have w₅ := hE₅.wb
    have e₆ := Exec.subN (P := P) w₅ 50224 50222 50220
    set c₆ : Config := { c₅ with nreg := upd c₅.nreg 50224 _ }
      with hc₆
    have hE₆ := hE₅.frame (exec_frameB e₆ (B := fun r => r == 50224)
      by_decide) e₆.wb_right by_decide
    have r₆ : ∀ r, r ≠ 50224 → c₆.nreg r = c₅.nreg r := fun r hr => by zumys; zumwy
    have v20 : c₅.nreg 50220 = k := by
      grind
    have v21 : c₅.nreg 50221 = S := by
      grind
    have v22 : c₅.nreg 50222 = 2 * C.m := by
      grind
    have v23 : c₅.nreg 50223 = 2 * C.m - S := by
      grind
    have v03 : c₅.nreg 50203 = ρ := by
      grind
    obtain ⟨c₇, k₇, e₇, hk₇, q121', r₇⟩ := candS_exec (P := P) (r := 50224) (j := 2 * C.m - k) c₆
      e₆.wb_right by_decide
      (by rw [r₆ _ by_decide, v21]) (by rw [r₆ _ by_decide, v23])
      (by zumys; simp [v22, v20]) hS by_omega hmW
    have hE₇ := hE₆.keep e₇.wb_right
      (exec_frameB e₇ (B := fun r => r == 50121) by_decide).2.2.1
      (fun r hr => r₇ r ztbjp)
    have t7 : ∀ r, r ≠ 50121 → r ≠ 50224 → c₇.nreg r = c₅.nreg r := fun r h1 h2 => by
      rw [r₇ r h1, r₆ r h2]
    obtain ⟨c'', k'', ex'', hk'', res'⟩ := tryS_exec (K := 8500) (e := e) (hc := hc) (ρ := ρ)
        (i := candIdx C.m S ztbdr) (rest := .ifLtN 50220 50054
        noneS (.ifLtN 50054 50220 noneS ztdsg)) c₇
        hE₇ (by rw [t7 _ by_decide by_decide, v03]) q121' cb1 hWn
        (by rw [walk_vtx_cand C cb1 cb2, hposx]) (by
      intro c₈ hE₈ f₈ hn₂
      have g₈ := kS f₈
      have w₈ := hE₈.wb
      have u20 : c₈.nreg 50220 = k := by
        rw [g₈ _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num,
          t7 _ by_decide by_decide, v20]
      have u22 : c₈.nreg 50222 = 2 * C.m := by
        rw [g₈ _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num,
          t7 _ by_decide by_decide, v22]
      have u03 : c₈.nreg 50203 = ρ := by
        rw [g₈ _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num,
          t7 _ by_decide by_decide, v03]
      -- the final answer when no candidate is left
      have none_res : ∀ c₉ : Config, c₉.nreg 50210 = 0 →
          (k = C.topIdx → ¬ sideLeft (chainModel C).W ztcc 0
            (Visibility.rayPt ((chainModel C).W.vtx ztcc) ztern 1)) →
          ArrRes P C e hc ρ c₉ := by
        intro c₉ h10 hn₃
        refine ⟨by_omega, fun h => by_omega, fun _ => ?_⟩
        refine vertex_none C hP hkm hposx ?_
        intro i hi hic
        zuduy
        rcases hic with rfl | rfl | ⟨rfl, hkT⟩
        · omega
        · omega
        grind
      have noneS_exec : ∀ c₉ : Config, WordsBounded W c₉ →
          (k = C.topIdx → ¬ sideLeft (chainModel C).W _ 0
            _) →
          ∃ c' k, Exec P W noneS c₉ c' k ∧ k = 1 ∧ ArrRes P C e hc ρ c' := fun c₉ hw₉ hn₃ =>
        ⟨_, 1, Exec.constN hw₉ _ _ by_omega, rfl, none_res _ by_simp hn₃⟩
      by_cases hk1 : c₈.nreg 50220 < c₈.nreg 50054
      · obtain ⟨c', k', ex, hk, r⟩ := noneS_exec c₈ w₈ (fun h => by
          rw [u20, hE₈.r54] at hk1; omega)
        exact ⟨c', _, .ifLtN_true hk1 ex, by_omega, r⟩
      by_cases hk2 : c₈.nreg 50054 < c₈.nreg 50220
      · obtain ⟨c', k', ex, hk, r⟩ := noneS_exec c₈ w₈ (fun h => by
          rw [u20, hE₈.r54] at hk2; omega)
        exact ⟨c', _, .ifLtN_false hk1 (.ifLtN_true hk2 ex), by_omega, r⟩
      have hkT : ztmwe := by rw [u20, hE₈.r54] at hk1 hk2; omega
      have e₉ := Exec.copyN (P := P) w₈ 50121 50222
      set c₉ : Config := { c₈ with nreg := upd c₈.nreg 50121 _ } with hc₉
      have hE₉ := hE₈.frame (exec_frameB e₉ (B := fun r => r == 50121)
        by_decide) e₉.wb_right by_decide
      have hv₃ : (chainModel C).W.vtx ztcc = (chainModel C).pos zta ztev := by
        rw [walk_vtx_cand C le_rfl (C.sideIdx_two_m _), hposx, hkT]
      obtain ⟨c', k', ex, hk, r⟩ := tryS_exec (K := 1) (rest := noneS) (e := e) (hc := hc)
        (ρ := ρ) (i := 2 * C.m) c₉ hE₉
        (by zungz; simp [u03]) (by zungz; simp [u22]) le_rfl hWn hv₃ (by
          intro c₁₀ hE₁₀ f₁₀ hn₃
          obtain ⟨c', k', ex, hk, r⟩ := noneS_exec c₁₀ hE₁₀.wb (fun _ => hn₃)
          exact ⟨c', k', ex, by_omega, r⟩)
      exact ⟨c', _, .ifLtN_false hk1 (.ifLtN_false hk2 (.seq e₉ ex)), by_omega, r⟩)
    exact ⟨c'', _, .seq e₆ (.seq e₇ ex''), by_omega, res'⟩)
  refine ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ ex'))), by_omega, res⟩

/-! ## The interior cases -/
theorem hgt_pos_of_param_pos {M : Model} {Q : Polygon} {e h : ℕ} (ht : 0 < M.param Q ztcq) :
    1 ≤ h := by
  rcases Nat.eq_zero_or_pos h with rfl | h0
  · exact absurd (show M.param Q ztjy = 0 from rfl) ztkbi
  omega

/-- The answer at the input position. -/
theorem found_here {C : Chain} {e hc ρ : ℕ} (hen : e < (chainModel C).W.n)
    (h0 : 0 ≤ (chainModel C).param zta ztev) (h1 : (chainModel C).param zta ztev < 1)
    (hhn : hc ≤ P.n) (hl : sideLeft (chainModel C).W e ztwtf
      (Visibility.rayPt ztwtg ztern 1))
    {c' : Config} (q10 : c'.nreg 50210 = 1) (q11 : c'.nreg 50211 = e) (q12 : c'.nreg 50212 = hc) :
    ArrRes P C e hc ρ c' := by
  zqsh
  exact ⟨hen, ⟨h0, h1, hhn⟩, (arrival_iff _ _ hen h0 h1 _).2 by_simp_all⟩

/-- The answer at a twin position. -/
theorem found_twin {C : Chain} {e hc ρ p' : ℕ} (hp' : p' < (chainModel C).W.n)
    (hhn : hc ≤ P.n)
    (htw : sideLeft (chainModel C).W p' ((chainModel C).param zta zthnk)
      (Visibility.rayPt ((chainModel C).pos zta zthnk) ztern 1) ∧
      (chainModel C).pos zta zthnk = (chainModel C).pos zta ztev ∧
      0 < (chainModel C).param zta zthnk ∧ (chainModel C).param zta zthnk < 1)
    {c' : Config} (q10 : c'.nreg 50210 = 1) (q11 : c'.nreg 50211 = p') (q12 : c'.nreg 50212 = hc) :
    ArrRes P C e hc ρ c' := by
  obtain ⟨hl, hpos, ht0, ht1⟩ := htw
  zqsh
  refine ⟨hp', ⟨ht0.le, ht1, hhn⟩, ?_⟩
  zulre
  exact (arrival_iff _ _ hp' ht0.le ht1 _).2 by_simp_all
theorem dirOf_cases' (ρ : ℕ) : dirOf ρ = 1 ∨ dirOf ρ = -1 := dirOf_cases ρ

/-- The block `foundTop`. -/
theorem foundTop_exec (hw : WordsBounded W c) {m hc : ℕ}
    (h53 : c.nreg 50053 = m) (h81 : c.nreg 50081 = 6) (h02 : c.nreg 50202 = hc)
    (hmW : 2 * m + 7 ≤ W) :
    ∃ c' k, Exec P W foundTop c c' k ∧ k = 4 ∧
      (c'.nreg 50210 = 1 ∧ c'.nreg 50211 = 2 * m + 6 ∧ c'.nreg 50212 = hc) := by
  unfold foundTop
  exec_block
  all_goals try omega
  all_goals try (config_simp; zunrx; omega)

/-- **Inside an edge of the box block.** -/
theorem boxArr_exec {C : Chain} (c : Config)
    (hE : CEnv P W H C c) (hP : C.P.Simple) {e hc ρ : ℕ} (h01 : c.nreg 50201 = e)
    (h02 : c.nreg 50202 = hc) (h03 : c.nreg 50203 = ρ)
    (hd : c.nreg 10502 = dirCode ztc e) (he : e < 6)
    (ht : 0 < (chainModel C).param zta ztev) (ht1 : (chainModel C).param zta ztev < 1)
    (hhn : hc ≤ P.n) (hWn : 2 * C.m + 7 ≤ W) :
    ∃ c' k, Exec P W boxArr c c' k ∧ k ≤ 30 ∧ ArrRes P C e hc ρ c' := by
  zqsg
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, r₁⟩ := intOut_exec (P := P) c hE.wb by_omega hE.r32
    ztktk
  zqsf
  zuhsk
  · zukye
    have hn : ¬ sideLeft (chainModel C).W e _
        _ := fun h => by
      have := b₁.2.2 h; omega
    zubkn
    have hdir : ztzqd := by
      zuhal
    zuihc
    by_cases h5 : c₁.nreg 50201 < c₁.nreg 50085
    · zqsi
      have he13 : ztpok := by_grind
      refine ⟨c₁, _, .seq e₁ (.ifLtN_true by_omega
        (.ifLtN_true (by zunjf; exact h5)
          ztwd)), by_omega, by_omega, by_simp_all, fun _ => ?_⟩
      exact wall_none C hP he13 ht ht1 by_simp_all
    · zqsi
      have he5 : ztpol := by_omega
      subst he5
      obtain ⟨c₂, k₂, e₂, hk₂, q⟩ := foundTop_exec c₁ w₁
        (by rw [r₁ _ by_decide, hE.r53]) (by rw [r₁ _ by_decide, hE.r81])
        (by rw [r₁ _ by_decide, h02]) hWn
      zugqn
      refine ⟨c₂, _, .seq e₁ (.ifLtN_true ztmdw
        (.ifLtN_false (by zunjf; omega) e₂)),
        by omega, found_twin by_omega hhn ?_ q10 q11 q12⟩
      exact twin_left _ _ (hgt_pos_of_param_pos ht) (slit_twin' C).1 (slit_twin' C).2 ht ht1
        ztqmc hn
  · zufgu
    obtain ⟨c₂, k₂, e₂, hk₂, q11, q12, r₂⟩ : ∃ c₂ k₂, Exec P W foundIn c₁ c₂ k₂ ∧ k₂ = 2 ∧
        c₂.nreg 50211 = e ∧ c₂.nreg 50212 = hc ∧ c₂.nreg 50210 = c₁.nreg 50210 := by
      unfold foundIn
      exec_block
      simp_all
    have q10 : zture := by zunsk; have := b₁.1; omega
    exact ⟨c₂, _, .seq e₁ ztnad, by_omega,
      found_here by_omega ht.le ht1 hhn hl q10 q11 q12⟩

/-- The generic candidate computation `50121 := candIdx` with registers `rs` (`S`) and `rd`
(`2m - S`). -/
theorem candGen_exec (hw : WordsBounded W c) {r rs rd m S j : ℕ}
    (_hr : r ≠ 50121) (hs : c.nreg rs = S) (hd : c.nreg rd = 2 * m - S) (hrj : c.nreg r = j)
    (hS : S ≤ 2 * m) (_hj : j ≤ 2 * m) (hmW : 2 * m ≤ W) :
    ∃ c' k, Exec P W (.ifLtN r rs (.instr (.addN 50121 r rd)) (.instr (.subN 50121 r rs))) c c' k ∧
      k ≤ 3 ∧ c'.nreg 50121 = candIdx m S j ∧ ∀ r', r' ≠ 50121 → c'.nreg r' = c.nreg r' := by
  zumsa
  zujsd
  · refine spec_ifLtN_true by_omega (spec_instr (Exec.addN hw _ _ _
      by_omega) fun _ => ⟨by_omega, ?_, by_simp_all⟩)
    simp_all
  · refine spec_ifLtN_false by_omega (spec_instr ztbbq
      fun _ => ztbfk)
    simp_all

/-- The block `found5`. -/
theorem found5_exec (hw : WordsBounded W c) {hc : ℕ}
    (h02 : c.nreg 50202 = hc) (hW : 5 ≤ W) :
    ∃ c' k, Exec P W found5 c c' k ∧ k = 3 ∧
      (c'.nreg 50210 = 1 ∧ c'.nreg 50211 = 5 ∧ c'.nreg 50212 = hc) := by
  unfold found5
  exec_block
  all_goals try omega
  simp_all

/-- The block `foundT`. -/
theorem foundT_exec (hw : WordsBounded W c) {i hc : ℕ}
    (h121 : c.nreg 50121 = i) (h81 : c.nreg 50081 = 6) (h02 : c.nreg 50202 = hc)
    (hW : i + 6 ≤ W) :
    ∃ c' k, Exec P W foundT c c' k ∧ k = 3 ∧
      (c'.nreg 50210 = 1 ∧ c'.nreg 50211 = i + 6 ∧ c'.nreg 50212 = hc) := by
  unfold foundT
  exec_block
  all_goals try omega
  all_goals try (config_simp; rw [h121, h81]; omega)

/-- The block `foundIn`. -/
theorem foundIn_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W foundIn c c' k ∧ k = 2 ∧ c'.nreg 50211 = c.nreg 50201 ∧
      c'.nreg 50212 = c.nreg 50202 ∧ c'.nreg 50210 = c.nreg 50210 := by
  unfold foundIn
  exec_block
  simp

/-- **Inside an edge of the tour or the up-slit edge.** -/
theorem intArr_exec {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {e hc ρ : ℕ} (h01 : c.nreg 50201 = e)
    (h02 : c.nreg 50202 = hc) (h03 : c.nreg 50203 = ρ)
    (hd : c.nreg 10502 = dirCode ztc e) (he6 : 6 ≤ e) (hen : e < 2 * C.m + 7)
    (ht : 0 < (chainModel C).param zta ztev) (ht1 : (chainModel C).param zta ztev < 1)
    (hhn : hc ≤ P.n) (hWn : 2 * C.m + 7 ≤ W) :
    ∃ c' k, Exec P W intArr c c' k ∧ k ≤ 60 ∧ ArrRes P C e hc ρ c' := by
  zqsg
  zubb
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, r₁⟩ := intOut_exec (P := P) c hE.wb by_omega hE.r32
    ztktk
  zqsf
  have hE₁ := hE.keep w₁
    (exec_frameB e₁ (B := fun r => r == 50210) by_decide).2.2.1
    (fun r hr => r₁ r ztbjp)
  zuhsk
  · zukye
    have hn : ¬ sideLeft (chainModel C).W e _
        _ := fun h => by
      have := b₁.2.2 h; omega
    have hh := hgt_pos_of_param_pos ht
    -- the tour position of the edge
    have e₂ := Exec.subN (P := P) w₁ 50120 50201 50081
    set c₂ : Config := { c₁ with nreg := upd c₁.nreg 50120 _ }
      with hc₂
    have hE₂ := hE₁.step e₂ by_decide
    have q120 : c₂.nreg 50120 = e - 6 := by
      zumxp; zumwv; rw [r₁ _ by_decide, h01, hE₁.r81]
    obtain ⟨c₃, k₃, e₃, hk₃, f₃, -, k58, k59, k89, k77⟩ := tvIdx_exec c₂ hE₂ q120
      by_omega
    have hE₃ := hE₂.frame f₃ e₃.wb_right by_decide
    zubj
    have s₃ : c₃.nreg 50202 = hc := by
      rw [f₃.1 _ by_decide, hc₂]; simp_all
    have i₃ : c₃.nreg 50120 = e - 6 := by rw [f₃.1 _ by_decide, q120]
    by_cases hlt : c₃.nreg 50120 < c₃.nreg 50058
    · zuilb
      zuckk
      zuec
      zubad
      have hjx :=
        (tour_mod hS hlt).symm
      rw [hjx] at k77
      have hjlt := Nat.mod_lt ztbat ztcdw
      obtain ⟨c₄, k₄, e₄, hk₄, q⟩ : ∃ c₄ k₄, Exec P W
          ztirj c₃ c₄ k₄ ∧ k₄ = 2 ∧
          (c₄.nreg 50224 = 2 * C.m - 1 - ztbat % ztbb ∧
            ∀ r, r ≠ 50224 → c₄.nreg r = c₃.nreg r) := by
        exec_block
        refine ⟨rfl, ?_, fun r hr => by zumwy⟩
        config_simp; rw [k58, hE₃.r32, k77]
      obtain ⟨q224, r₄⟩ := q
      obtain ⟨c₅, k₅, e₅, hk₅, q121, r₅⟩ := candGen_exec (rs := 50059)
        (rd := 50089) c₄
        e₄.wb_right by_decide (by rw [r₄ _ by_decide, k59]) (by rw [r₄ _ by_decide, k89])
        q224 hS by_omega by_omega
      obtain ⟨tw1, tw2, tw3⟩ := tour_twin C hlt
      have htw : tourTwin C i = candIdx C.m S _ := rfl
      rw [← htw] at q121
      obtain ⟨c₆, k₆, e₆, hk₆, q10, q11, q12⟩ := foundT_exec c₅ e₅.wb_right q121
        (by rw [r₅ _ by_decide, r₄ _ by_decide, hE₃.r81])
        (by rw [r₅ _ by_decide, r₄ _ by_decide, s₃]) by_omega
      refine ⟨c₆, _, .seq e₁ (.ifLtN_true ztmdw (.seq e₂ (.seq e₃
        (.ifLtN_true (by rw [i₃, k58]; exact hlt) ztxjw)))), by_omega,
        found_twin by_omega hhn ?_ q10 q11 q12⟩
      have he' : ztsig := by_omega
      rw [he'] at hn ht ht1 ⊢
      exact twin_left _ _ hh tw2 tw3 ht ht1 ztqmc hn
    · zuilb
      zufup
      zulta
      obtain ⟨c₄, k₄, e₄, hk₄, q10, q11, q12⟩ := found5_exec c₃ w₃ s₃ by_omega
      refine ⟨c₄, _, .seq e₁ (.ifLtN_true by_omega (.seq e₂ (.seq e₃
        ztsow))), by_omega,
        found_twin by_omega hhn ?_ q10 q11 q12⟩
      exact twin_left _ _ hh (slit_twin C).1 (slit_twin C).2 ht ht1 ztqmc hn
  · zufgu
    obtain ⟨c₂, k₂, e₂, hk₂, q11, q12, q10⟩ := foundIn_exec c₁ w₁
    refine ⟨c₂, _, .seq e₁ ztnad, by_omega,
      found_here by_omega ht.le ht1 hhn hl ?_ ?_ ?_⟩
    · zunsp; have := b₁.1; omega
    · simp_all
    simp_all

/-! ## The contract -/

/-- The input condition of `arrivalPos`: that of `leftSec`, a simple host polygon, and the walk
indices within the word bound. -/
def ArrIn (P : Polygon) (W : ℕ) (C : Chain) (c : Config) : Prop :=
  LeftIn P W C c ∧ C.P.Simple ∧ 2 * C.m + 7 ≤ W

/-- The output condition of `arrivalPos`. -/
def ArrOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  ArrRes P C ztcuv ztjsc ztdzm c'

/-- **Contract of `arrivalPos`** (at most `35000` steps): an arrival position of the point of
`(e, h)` for the ray arriving in direction `-dirOf ρ`, as a proper position, or the flag `0` if
there is none (`ArrRes`). -/
theorem arrivalPos_meets : Meets arrivalPos primBands (PrimPre ArrIn) (PrimPost ArrOut)
    (fun _ _ => 35000) := by
  refine prim_meets by_simp_all wr_arrivalPos ?_
  intro P W H C c₀ c _hC hE ⟨⟨hen, ⟨hp0, hp1, hhn⟩, hy⟩, hP, hWn⟩ hinp
  zuhq

  zucwu
  unfold ArrOut
  zufai
  zucp

  -- the edge direction

  zudkw
  have hE₁ := hE.frame (exec_frameB e₁ (B := fun r => r == 50002)
    by_decide) e₁.wb_right by_decide
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, d₂⟩ := dirAt_exec c₁ hE₁ (e := e)
    by_simp_all by_omega
  zue
  have g₂ : ztdjy := fun r h1 h2 => by
    rw [f₂.1 r ztcpm,
      hc₁]
    zubi
    zubzb
  zugd

  zubta
  · -- the box block
    zugmz
    obtain ⟨c', k, ex, hk, b⟩ := boxArr_exec c₂ hE₂ hP q01 q02 q03 d₂ hsm hpos hp1 hhn hWn
    exact ⟨c', _, .seq e₁ ztcsb,
      by omega, b⟩
  zuxh

  · obtain ⟨c', k, ex, hk, b⟩ := vtxArr_exec (hc := hc) c₂ hE₂ hP q01 q03 by_omega by_omega hWn
      ztlzn
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_true
      ztfpq ex))), by_omega, b⟩
  zuuz

  · have hdir : ztmvm := by_simp_all
    have hhor : ztdjn := by
      zuhqs

    obtain ⟨c', k, ex, hk, b⟩ := vtxArr_exec c₂ hE₂ hP q01 q03 by_omega by_omega hWn
      ztlzn
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_true
      zthes ex)))), by_omega, b⟩
  zuoq
  -- the start vertex of the edge and the height vertex

  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50120 _ }
    with hc₃
  have hE₃ := hE₂.frame (exec_frameB e₃ (B := fun r => r == 50120)
    by_decide) e₃.wb_right by_decide
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, sa, ia, la, va, -⟩ := tvLoad_exec c₃ hE₃ (i := e - 6)
    ztcqt by_omega
    (dst := 50133) by_norm_num
  zucc
  obtain ⟨c₅, k₅, e₅, hk₅, q⟩ : ∃ c₅ k₅, Exec P W (block [.constN 50160 0,
      .subN 50161 50202 50032]) c₄ c₅ k₅ ∧ k₅ = 2 ∧ (c₅.nreg 50160 = 0 ∧
        c₅.nreg 50161 = hc - 1 ∧ ∀ r, r ≠ 50160 → r ≠ 50161 → c₅.nreg r = c₄.nreg r) := by
    exec_block
    · omega
    · refine ⟨rfl, by config_simp, ?_, fun r h1 h2 => by simp [h1, h2]⟩
      config_simp
      rw [f₄.1 50202 by_decide, f₄.1 50032 by_decide, hc₃]
      zubi
      zubcd
  zucxy
  zuef
  zukhx
  zuxe

  have ia₅ : ztumi := symPtIn_of_eq ia by_grind
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, b₆, t₆⟩ := kbit_exec (op := 1) (dst := 50170) hE.hG hW c₅ w₅
    by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num la lh la ia₅ ih ia₅
  zubra

  obtain ⟨c₇, k₇, e₇, hk₇, f₇, b₇, t₇⟩ := kbit_exec (op := 1) (dst := 50171) hE.hG hW c₆
    e₆.wb_right by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num lh la lh
    ih₆ ia₆ ih₆
  zubgp
  have hE₅ := hE₄.keep w₅ (exec_frameB e₅ (B := fun r => r == 50160 ||
    r == 50161) by_decide).2.2.1 (fun r hr => r₅ r (by intro h; subst h; revert hr; decide)
      ztcua)
  zubqr

  -- registers kept since `c₂`
  have g₇ : ∀ r, r = 50201 ∨ r = 50203 ∨ r = 10502 ∨ r = 50202 → c₇.nreg r = c₂.nreg r := by
    zuz
    rw [f₇.1 r (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      f₆.1 r (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      r₅ r by_omega by_omega, f₄.1 r (by rcases hr with rfl | rfl | rfl | rfl <;> decide), hc₃]
    zubi
    zutv
  have b70 : ztfks :=
    BitIs.keep ztomz f₇ by_decide
  have b71 : ztfkt :=
    ⟨b₇, t₇⟩
  zupy

  zujzx
  zublv

  · zugdd
    have n70 : zthow := fun h => by
      have := b70.2.2 h; omega
    zudwy
    · zugde
      have n71 : zthov := fun h => by
        have := b71.2.2 h; omega
      have heq : ztwvl := by
        grind
      obtain ⟨c', k, ex, hk, b⟩ := vtxArr_exec c₇ hE₇ hP by_grind
        ztbvq by_omega by_omega hWn
        zthpz
      exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
        (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.ifLtN_true ztmdl
          (.ifLtN_true (by rw [hE₇.r32]; exact hlt2) ex))))))))))), by_omega, b⟩
    · have p71 : zticu := b71.2.1 (by
        have := b71.1; rw [hE₇.r32] at hlt2; omega)
      have hpos : ztfko := lt_of_le_of_ne hp0 (fun h => by
        zugk
        · grind
        · zufsf
        grind)
      obtain ⟨c', k, ex, hk, b⟩ := intArr_exec c₇ hE₇ by_grind
        by_grind ztbvq
        ztdlu by_omega by_omega hpos hp1 hhn hWn
      exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
        (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.ifLtN_true ztmdl
          ztnae)))))))))), by_omega, b⟩
  · have p70 : ztidb := b70.2.1 (by
      have := b70.1; rw [hE₇.r32] at hlt; omega)
    have hpos : ztfko := lt_of_le_of_ne hp0 (fun h => by
      zugk
      · grind
      · zufsf
      grind)
    obtain ⟨c', k, ex, hk, b⟩ := intArr_exec c₇ hE₇ by_grind
      by_grind ztbvq
      ztdlu by_omega by_omega hpos hp1 hhn hWn
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
      ztbxp)))), by_omega, b⟩
end
end SweepPrim
end Chazelle.Core
end
namespace Chazelle.Core
namespace FuseAsm
@[expose] public section
open Chazelle.Chain (sidePt)

/-- **No departure position: the direction is not free.** -/
theorem not_free_of_none (J : Merge.Junction) (hP : J.P.Simple) (i : ℕ) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hz : z ∈ (sideChain J i).set) (hz2 : z.2 ≤ (sideChain J i).top.2)
    (hnone : ∀ p t, ¬ Sweep.Arrival (chainModel ztgi).W z (-σ) p t) :
    ¬ Merge.FreeAt J.whole z σ := fun hf => by
  obtain ⟨p, t, h⟩ := arrival_of_free J hP i hσ hz hz2 hf
  simp_all
open WalkEmbed
open Chazelle.Chain (sideE)
variable (J : Merge.Junction)
theorem sideE_succ_m {m : ℕ} (hm : 1 ≤ m) : sideE m (ztbl % ztdk) = m - 1 := by
  unfold sideE
  rcases Nat.lt_or_ge ztbl ztdk with h | h
  · rw [Nat.mod_eq_of_lt h, ite_eq_right by_omega]; omega
  grind

/-- The walk vertex after the shared vertex in the walk of `C₁` is `u`. -/
theorem left_next : (chainModel J.left).W.vtx ztnho = sharedU J := by
  zuhfi
  zucmz
  have := walk_tour J.left J.m₁ 1 by_omega
  zujhe
  zubk
  zulch
  simp only [Merge.Junction.left_m]
  rw [sideE_succ_m J.one_le_m₁]
  rfl

/-- The walk vertex after the shared vertex in the walk of `C₂` is `w`. -/
theorem right_next : (chainModel J.right).W.vtx ztnhp = sharedW J := by
  zudhu
  zubau
  have := walk_tour J.right 0 1 by_omega
  zujhe
  zubk
  zulch
  simp only [Merge.Junction.right_m, zero_add]
  have h1 : 1 % ztgyh = 1 := Nat.mod_eq_of_lt (by have := J.one_le_m₂; omega)
  zuwv
  have h2 : sideE J.m₂ 1 = 1 := by unfold sideE; rw [ite_eq_left J.one_le_m₂]
  zuczw
  rfl

/-- The point of a walk position on the edge from `a` to `b` at the height of `h`. -/
theorem pos_edge {M : Model} {Q : Polygon} {e h : ℕ} {a b : Point} (ha : M.W.vtx e = a)
    (hb : M.W.vtx ztzzc = b) (hne : a.2 ≠ b.2) :
    M.pos Q ztgov = Geometry.lerp a b (ztmyg / ztti) := by
  unfold Model.pos Model.param Model.wa Model.wb
  simp_all
end
end FuseAsm
namespace IOrc
open Machine Machine.Stmt Programs SignK
@[expose] public section
def ioBands : Finset ℕ := insert bUp oracleBands
theorem oracleBands_sub_io : oracleBands ⊆ ioBands := Finset.subset_insert _ _

/-- The saved inputs (band `b`, registers `b … b + 9`, `b + 13`). -/
def saveL (b : ℕ) : List ztw :=
  [ztssg, ztpsz, ztpta, ztptb, ztptc,
    ztptd, ztpte, ztptf, ztptg, ztpth,
    ztpti]

/-- Saving the inputs. -/
def saveS (b : ℕ) : Stmt := block (SweepPrim.copies ztwdc)
variable {P : Polygon} {W : ℕ}
theorem saveS_exec (b : ℕ) (hb : b + 13 < 170000) (c : Config)
    (hw : WordsBounded W c) :
    ∃ c', Exec P W (saveS b) c c' 11 ∧ (∀ i, i < 10 → c'.nreg ztner = c.nreg ztbcn) ∧
      c'.nreg 170013 = c.nreg (b + 13) ∧
      (∀ r, ¬ ztgxv → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', e, h1, h2, h3, h4, h5, h6⟩ := SweepPrim.copies_exec (P := P) ztwdc c hw
    (by intro p hp q hq; simp only [saveL, List.mem_cons, List.not_mem_nil, or_false] at hp hq
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp <;> omega)
    ztcuf
  refine ⟨c', e, fun i hi => ?_, h1 ztpti ztcuf, fun r hr => h2 r ?_,
    h3, h4, h5, h6⟩
  · interval_cases i
    · exact h1 ztssg by_tauto
    · exact h1 ztpsz by_tauto
    · exact h1 ztpta by_tauto
    · exact h1 ztptb by_tauto
    · exact h1 ztptc by_tauto
    · exact h1 ztptd ztcuf
    · exact h1 ztpte ztcuf
    · exact h1 ztptf ztcuf
    · exact h1 ztptg ztcuf
    · exact h1 ztpth ztcuf
  · simp only [saveL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    omega

/-- The set-up: constants, the host record, the flag of the running minimum. -/
def initI : Stmt :=
  block [.inputSize 170010, .constN 170011 1, .constN 170012 0, .constN 170018 2,
    .subN 170019 170010 170011,
    .addN 170090 170000 170011, .loadN 170093 170090,
    .addN 170090 170013 170018, .loadN 170016 170090,
    .addN 170090 170090 170011, .loadN 170017 170090,
    .copyN 170015 9999,
    .storeN 170015 170011,
    .addN 170090 170015 170011, .storeN 170090 170012,
    .addN 170090 170090 170011, .storeN 170090 170012,
    .addN 170090 170090 170011, .storeN 170090 170019,
    .constN 170091 8, .addN 9999 9999 170091,
    .constN 170070 0]

/-- The orientation bit from the descriptor word: `1` iff the word is `1`. -/
def bitI : Stmt :=
  .ifLtN 170093 170011 ztott
    (.ifLtN 170011 170093 ztott (.instr (.constN 170014 1)))

/-- The registers written by `initI` and `bitI`. -/
def BinitR (r : ℕ) : Prop :=
  r = 170010 ∨ r = 170011 ∨ r = 170012 ∨ r = 170018 ∨ r = 170019 ∨ r = 170090 ∨ r = 170093 ∨
    r = 170016 ∨ r = 170017 ∨ r = 170015 ∨ r = 170091 ∨ r = 9999 ∨ r = 170070 ∨ r = 170014

/-- The registers written by `initI` and `bitI` (as a Boolean write set). -/
def BinitB (r : ℕ) : Bool :=
  decide (r = 170010 ∨ r = 170011 ∨ r = 170012 ∨ r = 170018 ∨ r = 170019 ∨ r = 170090 ∨
    r = 170093 ∨ r = 170016 ∨ r = 170017 ∨ r = 170015 ∨ r = 170091 ∨ r = 9999 ∨ r = 170070 ∨
    r = 170014)
theorem wrM_initI : BuildRam.wrM BinitB initI = true := by_decide

/-- **The set-up.** -/
theorem initI_exec (c : Config)
    (hw : WordsBounded W c) (hMD : c.nreg 170000 + 1 ≤ W) (hh : c.nreg 170013 + 3 ≤ W)
    (hA : c.nreg ALLOC + 8 ≤ W) (hn : P.n ≤ W) (hn1 : 1 ≤ P.n) :
    ∃ c' k, Exec P W ztncs c c' k ∧ 22 ≤ k ∧ k ≤ 27 ∧
      c'.nreg 170010 = P.n ∧ c'.nreg 170011 = 1 ∧
      c'.nreg 170012 = 0 ∧ c'.nreg 170018 = 2 ∧ c'.nreg 170019 = P.n - 1 ∧
      c'.nreg 170016 = c.nmem ztrlp ∧
      c'.nreg 170017 = c.nmem ztrlq ∧
      (c'.nreg 170014 = 1 ↔ c.nmem ztrlo = 1) ∧ c'.nreg 170014 ≤ 1 ∧
      c'.nreg 170015 = c.nreg ALLOC ∧ c'.nreg ALLOC = c.nreg ALLOC + 8 ∧
      c'.nreg 170070 = 0 ∧
      c'.nmem ztm = 1 ∧ c'.nmem ztccv = 0 ∧
      c'.nmem zteep = 0 ∧ c'.nmem zteeq = P.n - 1 ∧
      zth ∧
      (∀ r, ¬ BinitR r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  zuk
  zudh
  obtain ⟨c₁, k₁, e₁, hk₁, q10, q11, q12, q18, q19, q16, q17, q93, q15, qA, q70, m0, m1, m2, m3,
      mlo, rest, rr, rm, ro⟩ : ∃ c₁ k₁, Exec P W initI c c₁ k₁ ∧ k₁ = 22 ∧
      c₁.nreg 170010 = P.n ∧ c₁.nreg 170011 = 1 ∧
      c₁.nreg 170012 = 0 ∧ c₁.nreg 170018 = 2 ∧ c₁.nreg 170019 = P.n - 1 ∧
      c₁.nreg 170016 = c.nmem ztrlp ∧
      c₁.nreg 170017 = c.nmem ztrlq ∧
      c₁.nreg 170093 = c.nmem ztrlo ∧
      c₁.nreg 170015 = c.nreg 9999 ∧ c₁.nreg 9999 = c.nreg 9999 + 8 ∧
      c₁.nreg 170070 = 0 ∧
      c₁.nmem zterc = 1 ∧ c₁.nmem (c.nreg 9999 + 1) = 0 ∧
      c₁.nmem (c.nreg 9999 + 2) = 0 ∧ c₁.nmem (c.nreg 9999 + 3) = P.n - 1 ∧
      (∀ a, a < c.nreg 9999 → c₁.nmem a = c.nmem a) ∧
      True ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧
      c₁.output = c.output := by
    unfold initI
    exec_block
    all_goals first | omega | (config_simp; omega) | skip
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
      by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
      by config_simp, ?_, ?_, ?_, ?_, fun a ha => ?_, trivial, rfl, rfl, rfl⟩
    · zuhoy
    · simp
    · simp
    · simp
    · zuhoy
  have fM := BuildRam.exec_frameM e₁ wrM_initI
  replace rest : ∀ r, ¬ BinitR r → c₁.nreg r = c.nreg r := fun r hr =>
    fM.1 r (by unfold BinitB; unfold BinitR at hr; simp_all)
  zud
  have hb : ztupz := q11
  -- the orientation bit
  obtain ⟨c₂, k₂, e₂, hk₂, b14, bl, r₂⟩ : ∃ c₂ k₂, Exec P W bitI c₁ c₂ k₂ ∧ k₂ ≤ 5 ∧
      (c₂.nreg 170014 = 1 ↔ c₁.nreg 170093 = 1) ∧ c₂.nreg 170014 ≤ 1 ∧
      c₂ = { c₁ with nreg := upd c₁.nreg 170014 (c₂.nreg 170014) } := by
    unfold bitI
    by_cases h1 : c₁.nreg 170093 < c₁.nreg 170011
    · refine ⟨_, _, .ifLtN_true h1 ztpxx, by_omega, ?_, ?_, ?_⟩
      · simp_all
      · simp
      simp
    by_cases h2 : c₁.nreg 170011 < c₁.nreg 170093
    · refine ⟨_, _, .ifLtN_false h1 (.ifLtN_true h2 ztpxx),
        by omega, ?_, ?_, ?_⟩
      · zucac
      · simp
      simp
    · refine ⟨_, _, .ifLtN_false h1 (.ifLtN_false h2 (Exec.constN w₁ 170014 1 by_omega)),
        by omega, ?_, ?_, ?_⟩
      · zumb
      · simp
      simp
  have k : ∀ r, r ≠ 170014 → c₂.nreg r = c₁.nreg r := fun r hr => by
    zunsk; zunaw
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, by_omega, by_grind,
    by grind, by_grind,
    by grind, by_grind,
    by grind, by_grind,
    by omega, bl, by_grind, by_grind,
    by grind, ?_, ?_, ?_, ?_, fun a ha => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  all_goals first
    | (zunsk; simp only [Config.nmem_mk]; first | exact m0 | exact m1 | exact m2 | exact m3)
    | skip
  · zunsk; grind
  · rw [k r (by unfold BinitR at hr; omega)]; grind
  · grind
  · grind
  grind
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK
@[expose] public section
variable {Q : Polygon}

/-! ## The origin as a symbolic point -/

/-- **The symbolic origin**: a walk position of the interior walk as a symbolic point of `Q`. -/
noncomputable def oSym (Q : Polygon) : Origin → SymPt
  | .sym p => p
  | .walk ⟨e, 0⟩ => .vtx ztfss
  | .walk ⟨e, h + 1⟩ => .onEdge ztfso h

/-- The edge of `Q` carrying the walk edge `e` (as `ShootCut.edgeOf` names it). -/
theorem edgeOf_iv (hn : 3 ≤ Q.n) {e : ℕ} (he : e < Q.n) :
    ShootCut.edgeOf Q.n ztbadn (.vtx ztbame) = iEdge Q e := by
  unfold iv iEdge
  zucla
  · zugzj
  · zugzj
    zuhsm
    · rw [Nat.mod_eq_of_lt h1, ite_eq_left h1]
      zucjw
      · omega
      · zuchg
        rcases (show Q.n - 1 - e + 1 < Q.n ∨ Q.n - 1 - e + 1 = Q.n by omega) with h2 | h2
        · rw [Nat.mod_eq_of_lt h2] at hc; omega
        · rw [h2, Nat.mod_self] at hc; omega
    · rw [show e + 1 = Q.n by omega, Nat.mod_self]
      simp only [lt_irrefl, ↓reduceIte]
      zucjw
      · omega
      · zuchg
        rw [show Q.n - 1 - e = 0 by omega, Nat.zero_add, Nat.mod_eq_of_lt by_omega] at hc
        omega

/-- **The symbolic origin** is in range, evaluates to the origin and lies within the coordinate
bound (so it is an inner point of every chain model of `Q`). -/
theorem oSym_spec (hD : DistinctHeights Q) (hn : 3 ≤ Q.n) {o : Origin}
    (hol : o.Lt Q.n ztd)
    (hof : ztbnv ∨ ((interiorModel Q).InnerPt (o.eval ztd Q) ∧
      ∀ x, o = .walk x → ProperPos ztd Q Q.n x)) :
    (oSym Q o).Lt Q.n ∧ (oSym Q o).eval Q = o.eval ztd Q ∧
      |(o.eval (interiorModel Q) Q).1| ≤ Jordan.coordBound Q ∧
      |(o.eval (interiorModel Q) Q).2| ≤ Jordan.coordBound Q := by
  have hbd : (interiorModel Q).InnerPt _ →
      |(o.eval _ Q).1| ≤ Jordan.coordBound Q ∧
      |(o.eval (interiorModel Q) Q).2| ≤ Jordan.coordBound Q := innerPt_interior_bound
  cases o with
  | sym p =>
    refine ⟨hol, rfl, ?_⟩
    rcases hof with ⟨q, hq⟩ | ⟨hin, -⟩
    · simp_all
    · simp_all
  | walk x =>
    zubkw
    have he : ztsic := by have := hol.1; rw [mi_n] at this; omega
    cases h with
    | zero =>
      have hv : Origin.eval ztd Q (.walk ztjy) = Q.vtx ztfss := by
        show Chazelle.Geometry.lerp _ _ 0 = _
        rw [Chazelle.Geometry.lerp_zero, mi_wa he]
      zueyk
      exact ⟨iv_lt he, rfl, Jordan.abs_fst_vtx_le_coordBound Q zthyl,
        Jordan.abs_snd_vtx_le_coordBound Q zthyl⟩
    | succ h =>
      rcases hof with ⟨q, hq⟩ | ⟨hin, hpp⟩
      · simp_all
      have hpp' := hpp ztgov rfl
      have hh : h < Q.n := by have := hpp'.2.2; simp_all
      have hnh : ztcrb := by
        zudfx

        · zuchg
          zucpa
          · zubym
          · zubpy
        · zuchg
          zucpa
          · zubym
          · zubpy
      have hok : HostEdgeOK Q.n ztbadn (.vtx ztbame) := by
        simp only [HostEdgeOK, iv]
        split_ifs
        · omega
        · right
          zucpa
          · rw [Nat.mod_eq_of_lt h3]; zvmyc; omega
          · rw [h3, Nat.mod_self, show Q.n - 1 - 0 + 1 = Q.n by omega, Nat.mod_self]; omega
      have hpos := ShootCut.pos_eq_onEdge _ hD by_omega (h := h)
        (sp₁ := .vtx _) (sp₂ := .vtx _) (mi_wa he) (mi_wb he)
        zthyl ztyjj hok hnh
      rw [edgeOf_iv hn he] at hpos
      refine ⟨⟨iEdge_lt by_omega he, hh⟩, hpos.symm, hbd hin⟩

/-! ## Index helpers on the RAM (input `170095`, output `170096`, scratch `170092`) -/

/-- `170096 := iv 170095` (the vertex of `Q` at a walk vertex). -/
def ivF : Stmt :=
  .ifLtN 170014 170011 (.instr (.subN 170096 170019 170095)) (.instr (.copyN 170096 170095))

/-- The value `ivF` computes, from the orientation bit `b` and `n - 1`. -/
def ivV (b n1 p : ℕ) : ℕ := if b < 1 then n1 - p else p
theorem ivF_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (h11 : c.nreg 170011 = 1) :
    ∃ c' k, Exec P W ivF c c' k ∧ k ≤ 3 ∧
      c' = { c with nreg := upd c.nreg 170096 (ivV (c.nreg 170014) (c.nreg 170019) (c.nreg 170095)) } := by
  unfold ivF ivV
  zudwv
  · exact ⟨_, _, .ifLtN_true h (Exec.subN hw 170096 170019 170095), by_omega,
      by simp_all⟩
  · exact ⟨_, _, .ifLtN_false h (Exec.copyN hw 170096 170095), by_omega,
      by simp_all⟩
variable {b : ℕ}
/-- `ivV` is `iv` for the orientation bit of `Q`. -/
theorem ivV_eq (hb : b = 1 ↔ Mountain.LeftInside Q) (hb1 : b ≤ 1) (p : ℕ) :
    ivV b ztnv p = iv Q p := by
  unfold ivV iv
  grind

/-- `170096 := iEdge 170095` (the walk edge carrying an edge of `Q`). -/
def iEdgeF : Stmt :=
  .ifLtN 170014 170011
    (.seq (block [.addN 170092 170095 170011])
      (.ifLtN 170092 170010 (block [.subN 170096 170019 170095, .subN 170096 170096 170011])
        (block [.copyN 170096 170019])))
    (block [.copyN 170096 170095])

/-- The value `iEdgeF` computes. -/
def iEdgeV (b n p : ℕ) : ℕ := if b < 1 then (if p + 1 < n then n - 1 - p - 1 else n - 1) else p
theorem iEdgeF_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (h11 : c.nreg 170011 = 1) (h10 : c.nreg 170010 = P.n) (h19 : c.nreg 170019 = P.n - 1)
    (hp : c.nreg 170095 + 1 ≤ W) :
    ∃ c' k, Exec P W iEdgeF c c' k ∧ k ≤ 7 ∧
      c'.nreg 170096 = iEdgeV ztjrv P.n (c.nreg 170095) ∧
      (∀ r, r ≠ 170096 → r ≠ 170092 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold iEdgeF iEdgeV
  zudwv
  · zugss
    refine spec_seq ?_
    exec_block
    · simp_all
    by_cases h2 : c.nreg 170095 + 1 < P.n
    · zuek
      exec_block
      simp_all
    · zudx
      exec_block
      simp_all
  · zumjm
    exec_block
    simp_all

/-- `iEdgeV` is `iEdge` for the orientation bit of `Q`. -/
theorem iEdgeV_eq (hb : b = 1 ↔ Mountain.LeftInside Q) (hb1 : b ≤ 1) (p : ℕ) :
    iEdgeV b Q.n p = iEdge Q p := by
  unfold iEdgeV iEdge
  grind

/-! ## The static environment -/

/-- The static data of an interior query. -/
structure Stat where
  /-- The entry allocator (the host record). -/
  A₀ : ℕ
  /-- The entry memory. -/
  m₀ : ℕ → ℕ
  /-- The context handle. -/
  h : ℕ
  /-- The weight bound. -/
  γ : ℕ
  /-- The subarc ends. -/
  e₁ : ℕ
  h₁ : ℕ
  e₂ : ℕ
  h₂ : ℕ
  /-- The direction code. -/
  dir : ℕ
  /-- The symbolic origin. -/
  o : SymPt

/-- The host record `Host.whole n` at `A`: one run item `0 … n - 1`. -/
theorem hostAt_whole {m : ℕ → ℕ} {A n : ℕ} (h0 : m A = 1) (h1 : m ztbo = 0) (h2 : m ztbcl = 0)
    (h3 : m zttf = n - 1) : HostAt m A ztjja := by
  refine ztomy
  simp only [Host.whole, List.length_cons, List.length_nil] at hi
  obtain rfl : ztfla := by_omega
  tauto

/-- **The static environment** of the adapter at `c`: the saved inputs and constants in band
`17`, the symbolic origin, the entry memory below `A₀`, the host record at `A₀`, the grade
table and the weight bound. -/
structure SEnv (P : Polygon) (W : ℕ) (O : OracleIface) (s : Stat) (c : Config) : Prop where
  good : GoodEnv P
  hW : hostWords P.n ≤ W
  r1 : c.nreg 170001 = s.e₁
  r2 : c.nreg 170002 = s.h₁
  r3 : c.nreg 170003 = s.e₂
  r4 : c.nreg 170004 = s.h₂
  r8 : c.nreg 170008 = s.dir
  r9 : c.nreg 170009 = s.γ
  r13 : c.nreg 170013 = s.h
  r10 : c.nreg 170010 = P.n
  r11 : c.nreg 170011 = 1
  r12 : c.nreg 170012 = 0
  r18 : c.nreg 170018 = 2
  r19 : c.nreg 170019 = P.n - 1
  lb : c.nreg 170014 = 1 ↔ Mountain.LeftInside zta
  lb1 : c.nreg 170014 ≤ 1
  r15 : c.nreg 170015 = s.A₀
  r16 : c.nreg 170016 = s.m₀ ztohm
  r17 : c.nreg 170017 = s.m₀ ztkeo
  org : SymPtIn c 170020 s.o
  mem : ∀ a, a < s.A₀ → c.nmem a = s.m₀ a
  host0 : c.nmem s.A₀ = 1
  host1 : c.nmem (s.A₀ + 1) = 0
  host2 : c.nmem (s.A₀ + 2) = 0
  host3 : c.nmem (s.A₀ + 3) = P.n - 1
  alloc : s.A₀ + 8 ≤ c.nreg ALLOC
  grade : Robust s.A₀ s.m₀ ztfrr
  cap : s.γ ≤ 2 ^ ztbwe
namespace SEnv
variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat} {c c' : Config}

/-- **The static environment survives** every step that keeps the registers `170000 … 170029`,
the memory below the allocator, and does not lower the allocator. -/
theorem keep (h : SEnv P W O s c) (hr : ∀ r, 170000 ≤ r → r < 170030 → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    SEnv P W O s c' := by
  zumfi
  zumcz
  refine ⟨h.good, h.hW, (k _ by_omega by_omega).trans h.r1, (k _ by_omega by_omega).trans h.r2,
    (k _ by_omega by_omega).trans h.r3, (k _ by_omega by_omega).trans h.r4,
    (k _ by_omega by_omega).trans h.r8, (k _ by_omega by_omega).trans h.r9,
    (k _ by_omega by_omega).trans h.r13, (k _ by_omega by_omega).trans h.r10,
    (k _ by_omega by_omega).trans h.r11, (k _ by_omega by_omega).trans h.r12,
    (k _ by_omega by_omega).trans h.r18, (k _ by_omega by_omega).trans h.r19,
    by zuoeq; exact h.lb, by zuoeq; exact h.lb1,
    (k _ by_omega by_omega).trans h.r15, (k _ by_omega by_omega).trans h.r16,
    (k _ by_omega by_omega).trans h.r17,
    NFLoc.symPtIn_copy h.org by_simp_all by_simp_all
      by_simp_all,
    fun a ha => (hm a by_omega).trans (h.mem a ha), (hm _ by_omega).trans h.host0,
    (hm _ by_omega).trans h.host1, (hm _ by_omega).trans h.host2,
    (hm _ by_omega).trans h.host3, by_omega, h.grade, h.cap⟩
theorem n3 (h : SEnv P W O s c) : 3 ≤ P.n := Chazelle.Jordan.simple_three_le h.good.1
theorem nW (h : SEnv P W O s c) : P.n + 3 ≤ W := by have := h.hW; unfold hostWords at this; omega
theorem hostAt (h : SEnv P W O s c) : HostAt c.nmem s.A₀ ztqg :=
  hostAt_whole h.host0 h.host1 h.host2 h.host3
theorem qn : (Qof P).n = P.n := shear_n _ _
theorem ivv (h : SEnv P W O s c) (p : ℕ) :
    ivV ztjrv ztmft p = iv zta p := by
  rw [h.r19, ← qn]; exact ivV_eq h.lb h.lb1 p
theorem iev (h : SEnv P W O s c) (p : ℕ) :
    iEdgeV ztjrv P.n p = iEdge zta p := by
  rw [← qn]; exact iEdgeV_eq h.lb h.lb1 p
end SEnv

/-! ## The origin on the RAM -/

/-- **The symbolic origin** into `170020 … 170022`. -/
def originI : Stmt :=
  .ifLtN 170005 170018
    (block [.copyN 170020 170005, .copyN 170021 170006, .copyN 170022 170007])
    (.ifLtN 170012 170007
      (.seq (block [.constN 170020 1, .subN 170022 170007 170011, .copyN 170095 170006])
        (.seq iEdgeF ztoyq))
      (.seq (block [.constN 170020 0, .copyN 170095 170006])
        (.seq ivF ztoyq)))

/-- The registers `originI` writes. -/
def BorgR (r : ℕ) : Prop :=
  r = 170020 ∨ r = 170021 ∨ r = 170022 ∨ r = 170092 ∨ r = 170095 ∨ r = 170096
theorem originI_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (hn : 3 ≤ P.n) (h11 : c.nreg 170011 = 1) (h10 : c.nreg 170010 = P.n)
    (h12 : c.nreg 170012 = 0) (h18 : c.nreg 170018 = 2) (h19 : c.nreg 170019 = P.n - 1)
    (hlb : c.nreg 170014 = 1 ↔ Mountain.LeftInside zta) (hlb1 : c.nreg 170014 ≤ 1)
    {o : Origin} (ho : OriginIn c 170005 o) (hol : o.Lt P.n ztwiq)
    (hW : P.n + 3 ≤ W) :
    ∃ c' k, Exec P W originI c c' k ∧ k ≤ 14 ∧ SymPtIn c' 170020 (oSym zta o) ∧
      (∀ r, ¬ BorgR r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  zusu
  have hvv : ∀ p, ivV _ ztmft p = iv _ p := fun p => by
    rw [h19, ← hQ]; exact ivV_eq hlb hlb1 p
  have hev : ∀ p, iEdgeV _ P.n p = iEdge _ p := fun p => by
    zvnoq; exact iEdgeV_eq hlb hlb1 p
  unfold originI
  cases o with
  | sym p =>
    have hk : c.nreg 170005 < c.nreg 170018 := by
      rw [h18]; cases p with
      | vtx i => zuoxj; omega
      | onEdge e h => zuoxj; omega
    refine spec_ifLtN_true hk ?_
    exec_block
    refine ztgob
    · tauto
    · zulay
  | walk x =>
    zuich
    obtain ⟨k2, k6, k7⟩ := ho
    have k6' : c.nreg 170006 = e := k6
    have k7' : c.nreg 170007 = hh := k7
    have hk : ¬ c.nreg 170005 < c.nreg 170018 := by_omega
    zumjp
    have he : ztmvo := by have := hol.1; rw [mi_n, hQ] at this; omega
    have hhn : hh ≤ P.n := hol.2
    cases hh with
    | zero =>
      zubv
      refine spec_seq ?_
      exec_block
      zujrq
      zujl
      obtain ⟨c₁, k₁, e₁, hk₁, rfl⟩ := ivF_exec _ ‹_› by_simp_all
      refine zthmi
      zud
      exec_block
      refine ⟨by_omega, ⟨by config_simp, ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      · simp_all
      · zulay
    | succ h =>
      zudd
      refine spec_seq ?_
      exec_block
      zujrq
      zujl
      obtain ⟨c₁, k₁, e₁, hk₁, q96, q, qm, qr, qrm, qo⟩ := iEdgeF_exec (P := P) _ ‹_›
        by_simp_all by_simp_all by_simp_all
        (by config_simp; omega)
      refine zthmi
      zud
      exec_block
      refine ⟨by_omega, ztcg, fun r hr => ?_, by zunsl, by rw [qr], by zuoer,
        by rw [qo]⟩
      · simp_all
      · simp_all
      · simp_all
      · unfold BorgR at hr
        zujnm
        zudlu
        · omega
        · rw [q r by_omega by_omega]; config_simp
          zubd

/-! ## Conditional assignments -/

/-- **A conditional assignment**: both branches assign the register `r`. -/
theorem exec_ite_upd {P : Polygon} {W : ℕ} {a b r : ℕ} {s₁ s₂ : Stmt} {v₁ v₂ K : ℕ} (c : Config)
    (h₁ : c.nreg a < c.nreg b → ∃ k, Exec P W s₁ c { c with nreg := upd c.nreg r v₁ } k ∧ k ≤ K)
    (h₂ : ¬ c.nreg a < c.nreg b → ∃ k, Exec P W s₂ c { c with nreg := upd c.nreg r v₂ } k ∧ k ≤ K) :
    ∃ k, Exec P W (.ifLtN a b s₁ s₂) c
      { c with nreg := upd c.nreg r (if c.nreg a < c.nreg b then v₁ else v₂) } k ∧ k ≤ K + 2 := by
  zubjy
  · obtain ⟨k, e, hk⟩ := h₁ h
    exact ⟨k + 1, by zvnbq; exact .ifLtN_true h e, by_omega⟩
  · obtain ⟨k, e, hk⟩ := h₂ h
    exact ⟨k + 2, by zvnoi; exact .ifLtN_false h e, by_omega⟩
theorem exec_skip_upd {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (r : ℕ) :
    Exec P W .skip c { c with nreg := upd c.nreg r (c.nreg r) } 0 := by
  rw [upd_eq_self]; tauto
theorem exec_constN_upd {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (r v : ℕ)
    (hv : v ≤ W) : Exec P W ztoyj c { c with nreg := upd c.nreg r v } 1 :=
  Exec.block_cons (Exec.constN hw r v hv) (Exec.block_nil (Exec.constN (P := P) hw r v hv).wb_right)
theorem exec_copyN_upd {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (r a : ℕ) :
    Exec P W ztozc c { c with nreg := upd c.nreg r (c.nreg a) } 1 :=
  Exec.block_cons (Exec.copyN hw r a) (Exec.block_nil (Exec.copyN (P := P) hw r a).wb_right)
theorem exec_subN_upd {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (r a b : ℕ) :
    Exec P W ztnsm c { c with nreg := upd c.nreg r (c.nreg a - c.nreg b) } 1 :=
  Exec.block_cons (Exec.subN hw r a b) (Exec.block_nil (Exec.subN (P := P) hw r a b).wb_right)
theorem exec_addN_upd {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (r a b : ℕ)
    (hv : c.nreg a + c.nreg b ≤ W) :
    Exec P W (block [.addN r a b]) c { c with nreg := upd c.nreg r (c.nreg a + c.nreg b) } 1 :=
  Exec.block_cons (Exec.addN hw r a b hv) (Exec.block_nil (Exec.addN (P := P) hw r a b hv).wb_right)
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
@[expose] public section
variable {O : OracleIface} {P : Polygon}

/-- The descriptor handle of the grade chain `(g, b)` in the memory `m`. -/
def blkD (m : ℕ → ℕ) (h g b : ℕ) : ℕ := m (m ztwjz + 3 * b)

/-- **The top of a block of the grade table.**  For a full block `(g, b)` (`g ≥ 1` processed,
`(b + 1) 2^g ≤ n - 1`), the words read lie below the bound of the table, the top index `T` read
from the descriptor is at most `2^g`, and the vertex `b 2^g + T` of `Q` is at least as high as
every vertex of the block. -/
theorem block_top {m : ℕ → ℕ} {h A : ℕ} (hR : Robust A m fun m' => GradeRaw O P m' h A) {g b : ℕ}
    (hg : g < m h) (hb : ztds * 2 ^ g ≤ P.n - 1) :
    h + 2 < A ∧ m zteu + g < A ∧ m ztwjz + 3 * b < A ∧ blkD m h g b + 3 < A ∧
      m ztepg ≤ 2 ^ g ∧
      ∀ k, k ≤ 2 ^ g → ((Qof P).vtx (b * 2 ^ g + k)).2 ≤
        ((Qof P).vtx (b * 2 ^ g + m ztepg)).2 := by
  have hp : ztehr := Nat.two_pow_pos g
  have hbc : b < gradeCount P.n g := by
    zulbt
    have : ztgub := by
      grind
    have := Nat.div_le_div_right (c := 2 ^ g) this
    simp_all
  obtain ⟨h2, hr, hE⟩ := ShootCut.grade_entry hR hg hbc
  obtain ⟨H, C, N, hC, hwf, hP, -, -, hs, hmm, -⟩ := hR.holds.2.2.2 g b hg hbc
  have hD5 : blkD m h g b + 5 ≤ A := hwf.1
  zusu
  have hlen : ztsau := by
    zunke; unfold gradeLen
    grind
  have hsC : C.s = b * 2 ^ g := hs
  have hT : m ztepg = C.topIdx := hC.2.2.2.2.1
  have hx : C.s + C.m < (Qof P).n := by
    grind
  refine ⟨h2, hr, by unfold ShootCut.entryAddr at hE; omega, by_omega, ?_, fun k hk => ?_⟩
  · rw [hT, ← hlen]; exact C.topIdx_le
  · have hk' : ztidw := by_omega
    have h1 := C.vertex_snd_le_top hk'
    rw [ShootCut.grade_vertex hP hx hk', hsC] at h1
    zujik
    show _ ≤ ((Qof P).vtx (b * 2 ^ g + C.topIdx)).2
    have := ShootCut.grade_vertex hP hx C.topIdx_le
    rw [hsC] at this
    zuhnz
    zubvv

/-- **The top of a chain is its unique highest vertex** (distinct heights): a chain vertex at
least as high as all chain vertices is the top. -/
theorem topIdx_of_max {C : Chain} (hD : DistinctHeights C.P) {j : ℕ} (hj : j ≤ C.m)
    (hmax : ∀ k, k ≤ C.m → (C.vertex k).2 ≤ (C.vertex j).2) : C.topIdx = j := by
  have h1 := C.topIdx_min hj hmax
  zulhl
  have h3 := hmax C.topIdx C.topIdx_le
  have heq : (C.vertex j).2 = (C.vertex C.topIdx).2 := le_antisymm h2 h3
  zuct
  have hlt : C.topIdx < j := lt_of_le_of_ne h1 hne
  refine hD _ _ ztdyj (C.edgeIdx_lt C.topIdx) ?_ heq
  zufhz
  have := C.sideEdgeIdx_inj hj C.topIdx_le he
  omega
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim

/-- The copy block into the band `bLocate` writes only band `bLocate`. -/
theorem frame_copies {l : List ztw} {c c₁ : Config} {k : ℕ}
    (hl : ∀ q ∈ l, 50000 ≤ q.1 ∧ q.1 < 60000)
    (h1 : ∀ r, r ∉ l.map Prod.fst → c₁.nreg r = c.nreg r) (h2 : c₁.rreg = c.rreg)
    (h3 : c₁.nmem = c.nmem) (h4 : c₁.rmem = c.rmem) (h5 : c₁.output = c.output) :
    Frame {bLocate} c c₁ k := by
  have hA : ztdc := h1 ALLOC (by
    zuq
    zucoc
    have := hl q hq
    unfold ALLOC at hq'; omega)
  refine ⟨fun r hr _ => h1 r ?_, fun r _ => by zvmxx, fun a _ => by zvncq, fun a _ => by rw [h4],
    h5, by_omega, by_omega⟩
  zuq
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
  zuhbg
  have := hl q hq
  zunfm
  omega

/-- **Calling a chain primitive**: copy the inputs (among them the descriptor address), run the
primitive. -/
theorem callPrim {p : Stmt} {K : ℕ} {Inp : Polygon → ℕ → Chain → Config → Prop}
    {Out : Polygon → Chain → Config → Config → Prop}
    (hp : Meets p primBands ztqbn ztqbm ztgis)
    (l : List ztw) (hd : ∀ q ∈ l, ∀ r ∈ l, q.1 ≠ r.2) (hnd : (l.map Prod.fst).Nodup)
    (hl : ∀ q ∈ l, 50000 ≤ q.1 ∧ q.1 < 60000) {src : ℕ} (hsrc : (50200, src) ∈ l)
    {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (hG : GoodEnv P)
    (hW : hostWords P.n ≤ W) {H : Host} {C : Chain}
    (hwf : ChainWF P ztm c.nmem ztqiz)
    (hC : ChainDescAt c.nmem ztqiz zta H C)
    (hInp : ∀ c₁ : Config, ztdds →
      ztcjk → c₁.nmem = c.nmem → Inp P W C c₁)
    (hroom : c.nreg ALLOC + K ≤ W) :
    ∃ c₁ c' k, ztdds ∧
      ztcjk ∧ c₁.nmem = c.nmem ∧
      Exec P W ztzsg c c' k ∧ k ≤ l.length + K ∧ Out P C c₁ c' ∧
      Frame primBands c c' k := by
  zuug

  have hA₁ : ztdc := h2 ALLOC (by
    zuq
    zucoc
    have := hl q hq
    unfold ALLOC at hq'; omega)
  have h00 : c₁.nreg 50200 = c.nreg src := h1 _ hsrc
  have hpre : PrimPre Inp P W c₁ := by
    refine ⟨hG, hW, ?_, H, C, ?_, hInp c₁ h1 h2 h4⟩
    · grind
    grind
  obtain ⟨c', k, e, hk, hpost, hf⟩ := hp P W c₁ e₁.wb_right hpre by_grind
  refine ⟨c₁, c', l.length + k, h1, h2, h4, .seq e₁ e, by_grind, hpost H C ?_, ?_⟩
  · grind
  · have := hf₁.trans hf
    tauto
open WalkEmbed
theorem chainModel_ne_interior (C : Chain) (Q : Polygon) : chainModel C ≠ interiorModel Q := by
  zuq
  have := congrArg (fun M : Model => M.counted 0) h
  zuckl

/-- The model descriptor of a chain model holds a chain descriptor after its header. -/
theorem chainDesc_of {m : ℕ → ℕ} {B : ℕ} {Q : Polygon} {M : Model} {C : Chain}
    (h : ModelDescAt m B Q M) (hM : M = chainModel C) :
    m B = 0 ∧ ∃ H C', ChainDescAt m ztvf Q H C' ∧ M = chainModel C' := by
  zucim
  · exact ⟨h0, H, C', hC, hM'⟩
  · exact absurd ztmkt (chainModel_ne_interior C Q)

/-! ## Keys as offsets from vertex `0` -/
theorem off_zero {n k : ℝ} (hk : 0 ≤ k) : off n 0 k = k := by
  unfold off; zupay
theorem key_nonneg {M : Model} {Q : Polygon} {n : ℕ} {x : WPos} (hx : ProperPos M Q n x) :
    0 ≤ M.key Q x := by
  unfold Model.key; have := hx.1; positivity

/-- **The input condition of a position** for `offCmp`: a proper position of the walk, not a box
vertex. -/
def PosOK (C : Chain) (Q : Polygon) (n : ℕ) (x : WPos) : Prop :=
  x.edge < (chainModel C).W.n ∧ ProperPos ztc Q n x ∧ (x.hgt = 0 → 6 ≤ x.edge)

/-- A proper position whose point is strictly inside the height band of the box is not a box
vertex. -/
theorem posOK_of {C : Chain} {Q : Polygon} {n : ℕ} {x : WPos} (he : x.edge < (chainModel C).W.n)
    (hx : ProperPos ztc Q n x) (hy : |((chainModel C).pos Q x).2| < C.radius) :
    PosOK C Q n x := by
  refine ⟨he, hx, fun h0 => ?_⟩
  zulwd
  have hp := box_param_pos C by_omega hx.1 hy
  rcases x with ⟨e, h⟩
  zujpd
  zubvi
  simp [Model.param] at hp

/-! ## The comparison call -/

/-- The copies of a key comparison of the positions in `a, b` and `d, e`. -/
def kcL (a b d e : ℕ) : List ztw :=
  [ztgzg, ztdsp, ztfmv, ztnhl, ztnhm, ztnhn]

/-- **Key comparison** of the positions `(a, b)` and `(d, e)`. -/
def keyCmp (a b d e : ℕ) : Stmt := .seq (block (copies ztqsh)) offCmp

/-- A register of band `bRestore`. -/
def InR (r : ℕ) : Prop := 80000 ≤ r ∧ r < 90000
variable {a b d e : ℕ}
theorem kcL_hd (ha : InR a) (hb : InR b) (hd : InR d) (he : InR e) :
    ∀ q ∈ kcL a b d e, ∀ r ∈ kcL a b d e, q.1 ≠ r.2 := by
  unfold InR at *
  simp only [kcL, List.mem_cons, List.not_mem_nil, or_false]
  rintro q (rfl | rfl | rfl | rfl | rfl | rfl) r (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only <;> omega

/-- **Contract of a key comparison** (at most `11006` steps). -/
theorem keyCmp_exec (ha : InR a) (hb : InR b) (hd : InR d) (he : InR e)
    {P : Polygon} {W : ℕ} {c : Config} {H : Host} {C : Chain} (hw : WordsBounded W c)
    (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (hwf : ChainWF P ztm c.nmem ztdms)
    (hC : ChainDescAt c.nmem ztdms zta H C) (h0 : c.nreg 83022 = 0)
    (hx : PosOK C zta P.n ztel)
    (hy : PosOK C zta P.n ztge)
    (hWm : 2 * C.m + 7 ≤ W) (hroom : c.nreg ALLOC + 11000 ≤ W) :
    ∃ c' k, Exec P W ztjzm c c' k ∧ k ≤ 11006 ∧
      BitIs c' 50210 ((chainModel C).key zta ztel <
        (chainModel C).key zta ztge) ∧
      BitIs c' 50211 ((chainModel C).key zta ztge <
        (chainModel C).key zta ztel) ∧
      Frame primBands c c' k := by
  obtain ⟨c₁, c', k, h1, -, -, ex, hk, hout, hf⟩ := callPrim offCmp_meets ztqsh
    (kcL_hd ha hb hd he) ztbeg ztbeg
    (src := 83020) ztbeg hw hG hW hwf hC (fun c₁ h1 _ _ => by
      zuyd

      obtain ⟨hx1, hx2, hx3⟩ := hx
      obtain ⟨hy1, hy2, hy3⟩ := hy
      refine ⟨by zunrs; exact hx1, by zupaz; exact hy1, by rw [q5, h0]; omega,
        by rw [q1, q2]; exact hx2, by rw [q3, q4]; exact hy2, fun h => ?_, fun h => ?_, hWm⟩
      · zunrs; rw [q2] at h; exact hx3 h
      · zupaz; rw [q4] at h; exact hy3 h) hroom
  zuyd

  obtain ⟨o1, o2⟩ := hout
  rw [q1, q2, q3, q4, q5, h0, Nat.cast_zero, off_zero (key_nonneg hx.2.1),
    off_zero (key_nonneg hy.2.1)] at o1 o2
  exact ⟨c', k, ex, by simp [kcL] at hk; omega, o1, o2, hf⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim WalkEmbed

/-! ## Descriptors survive changes above their bound -/
variable {m m' : ℕ → ℕ} {c' : Config} {k : ℕ}
theorem hostAt_agree_r {B E : ℕ} {H : Host} (h : HostAt m B H)
    (hE : B + 3 * H.length + 4 ≤ E) (hm : ∀ a, a < E → m' a = m a) : HostAt m' B H := by
  zuko
theorem chainDesc_agree {bw E : ℕ} {Q : Polygon} {H : Host} {C : Chain}
    (hC : ChainDescAt m bw Q H C) (hb : bw + 5 ≤ E) (hE : m bw + 3 * H.length + 4 ≤ E)
    (he : ∀ a, a < E → m' a = m a) : ChainDescAt m' bw Q H C := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hC
  refine ⟨?_, h1, by_grind, by_grind,
    by grind, by_grind⟩
  zuktz
  exact hostAt_agree_r h0 hE he
theorem chainWF_agree {P : Polygon} {m m' : ℕ → ℕ} {bw E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw zta H C)
    (he : ∀ a, a < E → m' a = m a) (hEE : E ≤ E') : ChainWF P E' m' bw := by
  obtain ⟨hl, hHW, hEb, hs⟩ := hwf.2 H C hC
  have hb := hwf.1
  refine ztgoe
  have c0 : m' bw = m bw := he _ by_omega
  have hH' : ztiyj := hostAt_agree_r hC.1 hEb he
  have hHH : ztiyi := NFLoc.hostAt_unique ztfpx hH'
  zular
  refine zthnc
  have e1 : ztidk := by rw [← hC'.2.2.1, ← hC.2.2.1, he _ by_omega]
  zubvz

/-! ## The fixed data of a run -/

/-- **The fixed data of a run of the candidate test** from `c₀` (model `M`, normal form `N`). -/
structure TGood (P : Polygon) (W : ℕ) (M : Model) (N : NF) (c₀ : Config) : Prop where
  hG : GoodEnv P
  hW : hostWords P.n ≤ W
  hMD : ModelDescAt c₀.nmem ztchn zta M
  hwfMD : ModelDescWF P ztdq c₀.nmem ztchn
  hreg : c₀.nmem ztchn = 0 → ∀ H C, ChainDescAt c₀.nmem ztbvw zta H C →
    HostRegular (Qof P).n H
  hsimp : c₀.nmem ztchn = 0 → ∀ H C,
    ChainDescAt c₀.nmem ztbvw zta H C → C.P.Simple
  hkind : OkModel P M ∨ M = interiorModel zta
  hGM : GoodModel M
  hWm : ∀ C : Chain, M = chainModel C → 2 * C.m + 7 ≤ W
  hN : NFWithin c₀.nmem ztvmg ztdq N
  hNF : IsNF M zta N
  hr : c₀.nreg 83002 < N.nRegions
  hxe : c₀.nreg 83005 < M.W.n
  hxp : ProperPos M zta P.n ztxt
  hxc : c₀.nreg 83006 = 0 ∨ 0 < M.param zta ztxt
  hxC : ∀ C : Chain, M = chainModel C → M.pos zta ztxt ∈ C.set
  hh : c₀.nreg 83007 < P.n
  hy : ((Qof P).vtx ztvmh).2 = (M.pos zta ztxt).2
  hσ : c₀.nreg 83008 ≤ 1

/-- **The run invariant** relative to the start `c₀`. -/
structure TInv (W : ℕ) (c₀ c : Config) : Prop where
  hw : WordsBounded W c
  hin : ∀ q, 80000 ≤ q → q < 83010 → c.nreg q = c₀.nreg q
  hA : c₀.nreg ALLOC ≤ c.nreg ALLOC
  hm : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a
  h20 : c.nreg 83020 = c₀.nreg 83000 + 1
  h21 : c.nreg 83021 = c₀.nmem ztchn
  h22 : c.nreg 83022 = 0
  h23 : c.nreg 83023 = 1

/-- **One step of a run**: the invariant after it, the relative frame, band `bRestore`
unchanged. -/
def TStep (W : ℕ) (c₀ c c' : Config) (k : ℕ) : Prop :=
  TInv W c₀ c' ∧ RF dBands ztdq c c' k ∧
    ∀ q, 80000 ≤ q → q < 90000 → c'.nreg q = c.nreg q
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- The model descriptor, at any configuration of the run. -/
theorem TInv.modelDesc (hE : TGood P W M N c₀) (hI : TInv W c₀ c) :
    ModelDescAt c.nmem ztdcs zta M ∧
      ModelDescWF P ztm c.nmem ztdcs := by
  have h0 := hI.hin 83000 by_norm_num by_norm_num
  have hA6 := hE.hwfMD.1
  rcases hE.hMD with ⟨hz, H, C, hC, hM⟩ | ⟨h1, hbit, hM⟩
  · have hcw : ChainWF P ztdq c₀.nmem ztbvw := hE.hwfMD.2 hz
    zubks
    have hC' := chainDesc_agree hC hcw.1 hEb hI.hm
    have hz' : c.nmem ztchn = 0 := by zunqh; exact hz
    zudty
    exact ⟨Or.inl ⟨hz', H, C, hC', hM⟩, by have := hI.hA; omega,
      fun _ => chainWF_agree hcw hC hI.hm hI.hA⟩
  · have h1' : c.nmem ztchn = 1 := by zunqh; exact h1
    have hb' : c.nmem ztbvw = c₀.nmem ztbvw := hI.hm _ by_omega
    zudty
    exact ⟨Or.inr ⟨h1', by_simp_all, hM⟩, by have := hI.hA; omega,
      fun h => by_omega⟩

/-- **The chain descriptor of a chain model**, at any configuration of the run. -/
theorem TInv.chain (hE : TGood P W M N c₀) (hI : TInv W c₀ c) {C : Chain}
    (hM : M = chainModel C) :
    ∃ H C', ChainDescAt c.nmem ztdms zta H C' ∧ M = chainModel C' ∧
      ChainWF P ztm c.nmem ztdms := by
  zubxo
  zudrm
  rw [hI.h20, ← hI.hin 83000 by_norm_num by_norm_num]
  exact ⟨H, C', hC, hM', hwf.2 hz⟩
theorem TInv.nfWithin (hE : TGood P W M N c₀) (hI : TInv W c₀ c) :
    NFWithin c.nmem ztmgn ztdq N := by
  rw [hI.hin 83001 by_norm_num by_norm_num]
  exact hE.hN.transport hI.hm

/-- The primitive bands are bands of the test. -/
theorem primBands_sub : primBands ⊆ dBands := by_decide

/-- **A primitive step keeps the invariant** and band `bRestore`. -/
theorem TInv.prim (hI : TInv W c₀ c) (hw : WordsBounded W c')
    (hf : Frame primBands c c' k) : TStep W c₀ c c' k := by
  have h8 : ∀ q, 80000 ≤ q → q < 90000 → c'.nreg q = c.nreg q := fun q h1 h2 =>
    hf.1 q (by
      zukqg
      decide) (by unfold ALLOC; omega)
  refine ⟨⟨hw, fun q h1 h2 => (h8 q h1 by_omega).trans ztrrn,
    hI.hA.trans hf.2.2.2.2.2.1, fun a ha => (hf.2.2.1 a (by have := hI.hA; omega)).trans
      ztduw, by zuneb; exact hI.h20,
    by zuneb; exact hI.h21,
    by zuneb; exact hI.h22,
    by zuneb; exact hI.h23⟩,
    (RF.of_frame hf hI.hA).mono primBands_sub le_rfl, h8⟩
theorem TStep.trans {c₁ c₂ : Config} {k₁ k₂ : ℕ} (h₁ : TStep W c₀ c c₁ k₁)
    (h₂ : TStep W c₀ c₁ c₂ k₂) : TStep W c₀ c c₂ ztbct :=
  ⟨h₂.1, h₁.2.1.trans h₂.2.1, fun q h1 h2 => (h₂.2.2 q h1 h2).trans (h₁.2.2 q h1 h2)⟩
theorem TStep.mono {k k' : ℕ} (h : TStep W c₀ c c' k) (hk : k ≤ k') :
    TStep W c₀ c c' k' :=
  ⟨h.1, h.2.1.mono subset_rfl hk, h.2.2⟩

/-- **A step writing only registers of the primitive bands.** -/
theorem TInv.stepB {B : ℕ → Bool} {c' : Config} (hI : TInv W c₀ c) (hw : WordsBounded W c')
    (hf : SignK.FrameB B c c') (hB : ∀ r, B r = true → bandOf r ∈ primBands ∧ r ≠ ALLOC)
    (k : ℕ) : TStep W c₀ c c' k :=
  hI.prim hw (NFLoc.frame_of_frameB hf hB k)

/-- **A register step inside band `bRestore` from `83010` on keeps the invariant.** -/
theorem TInv.regs (hI : TInv W c₀ c) (hw : WordsBounded W c')
    (hr : ∀ r, (r < 83010 ∨ 90000 ≤ r ∨ (83020 ≤ r ∧ r < 83024)) → c'.nreg r = c.nreg r)
    (hrr : c'.rreg = c.rreg) (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) : TInv W c₀ c' ∧ RF dBands ztdq c c' k := by
  zucgg
  refine ⟨⟨hw, fun q h1 h2 => (hr q by_omega).trans ztrrn, by zvmze; exact hI.hA,
    fun a ha => by zvmwi; exact hI.hm a ha, by zunax; exact hI.h20,
    by zunax; exact hI.h21, by zunax; exact hI.h22,
    by zunax; exact hI.h23⟩,
    rf_of_regs (fun r hr' => hr r by_omega) hrr hm hrm ho⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc

/-! ## Addresses of a normal form -/

/-- A word reached through the sum of two pointers (the second one below the bound) that robustly
holds a value lies below the bound. -/
theorem robust_addr3' {E : ℕ} {m : ℕ → ℕ} {b₁ p₂ t v : ℕ} (hp₂ : p₂ < E)
    (h : Robust E m fun m' => m' ztodd = v) : m b₁ + m p₂ + t < E := by
  have hb₁ : b₁ < E := by
    zucux
    zueeg
    have := h ztzkb
      ztxl
    grind
  zucux
  have := h ztzjy (fun a ha => by
    grind)
  grind

/-- **The words of a normal form readable below `E`** lie below `E`. -/
theorem nf_bounds {m : ℕ → ℕ} {B E : ℕ} {N : NF} (h : NFWithin m B E N) :
    B + 7 < E ∧
    ztxhp ∧
    ztxhs ∧
    ztxht ∧
    (∀ r, r < N.nRegions → ∀ t, t < (N.region r).arcs.length →
      m ztlw + m ztxhc + t < E) ∧
    (∀ r, r < N.nRegions → ∀ t, t < (N.region r).chords.length →
      m ztlw + m ztwnp + t < E) := by
  have hB := robust_addr fun m' hm' => (h m' hm').2.2.2.2.1
  have hreg : ∀ r, r < N.nRegions → m zter + 5 * r + 4 < E := fun r hr => by
    have := robust_addr2 (o := 5 * r + 4)
      (fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.1
        omega)
    omega
  refine ⟨by_omega, fun i hi => ?_, fun j hj => ?_, hreg, fun r hr t ht => ?_,
    fun r hr t ht => ?_⟩
  · have := robust_addr2 (o := 5 * i + 4)
      (fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.1 i hi).2.2.2.2
        omega)
    omega
  · have := robust_addr2 (o := 5 * j + 4)
      (fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.2.1 j hj).2.2.2.2
        omega)
    omega
  · zukem
    exact robust_addr3' by_omega
      (v := (N.region r).arcs.getD t 0) (fun m' hm' => by
        zujxa
        have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.2.1 t ht
        simp_all)
  · zukem
    exact robust_addr3' by_omega
      (v := (N.region r).chords.getD t 0) (fun m' hm' => by
        zujxa
        have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.2.2 t ht
        simp_all)

/-! ## Calls of the readers -/

/-- **A copy block followed by a statement of band `bLocate`.** -/
theorem callB {p : Stmt} {K : ℕ} {Pre : Polygon → ℕ → Config → Prop}
    {Post : Polygon → Config → Config → Prop}
    (hp : Meets p {bLocate} Pre Post ztgis)
    (l : List ztw) (hd : ∀ q ∈ l, ∀ r ∈ l, q.1 ≠ r.2) (hnd : (l.map Prod.fst).Nodup)
    (hl : ∀ q ∈ l, 50000 ≤ q.1 ∧ q.1 < 60000)
    {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    (hPre : ∀ c₁ : Config, ztdds →
      ztcjk → c₁.nmem = c.nmem → Pre P W c₁)
    (hroom : c.nreg ALLOC + K ≤ W) :
    ∃ c₁ c' k, ztdds ∧
      ztcjk ∧ c₁.nmem = c.nmem ∧
      Exec P W ztzsg c c' k ∧ k ≤ l.length + K ∧ Post P c₁ c' ∧
      Frame primBands c c' k := by
  zuug

  have hA₁ := h2 ALLOC (by
    zuq
    zucoc
    have := hl q hq
    unfold ALLOC at hq'; omega)
  obtain ⟨c', k, e, hk, hpost, hf⟩ := hp P W c₁ e₁.wb_right (hPre c₁ h1 h2 h4)
    by_grind
  refine ⟨c₁, c', l.length + k, h1, h2, h4, .seq e₁ e, by_grind, hpost, ?_⟩
  exact (hf₁.trans hf).mono by_decide le_rfl
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}
theorem hl_loc {l : List ztw} (h : ∀ q ∈ l, 50200 ≤ q.1 ∧ q.1 < 50210) :
    ∀ q ∈ l, 50000 ≤ q.1 ∧ q.1 < 60000 := by_grind

/-- **The length of a list of region `83002`**: `f = 0` its arcs, `f = 2` its exit chords. -/
def tRegLen (f : ℕ) : Stmt := .seq (block (copies [ztblr, ztdso])) ztwcp
theorem tRegLen_exec {f : ℕ} (hf : f = 0 ∨ f = 2) (hE : TGood P W M N c₀)
    (hI : TInv W c₀ c) (hroom : c.nreg ALLOC + 11 ≤ W) :
    ∃ c' k, Exec P W (tRegLen f) c c' k ∧ k ≤ 13 ∧
      c'.nreg 50210 = rrFld (N.region ztco) f ∧
      TStep W c₀ c c' k := by
  zubkg

  obtain ⟨c₁, c', k, h1, -, hm1, ex, hk, hpost, hf⟩ := callB (regRd_meets (f := f)
    by_omega) [(50200, 83001), (50201, 83002)]
    by_simp by_simp ztmlh hI.hw (fun c₁ h1 _ hm => by
      zubav
      zukim
      zucrc
      unfold NFRdOK
      grind) hroom
  zubav
  zukim
  zucrc
  refine ⟨c', k, ex, by_omega, ?_, hI.prim ex.wb_right hf⟩
  rw [hpost N by_simp_all (by rw [q1, r02]; exact hr), q1, r02]

/-- **Item `t` (register `tr`) of a list of region `83002`**: `f = 1` its arcs, `f = 3` its exit
chords. -/
def tRegItem (f tr : ℕ) : Stmt :=
  .seq (block (copies [ztblr, ztdso, ztgzh])) ztkbl
theorem nfLst_meets (f : ℕ) : Meets ztkbl {bLocate}
    (fun _ W c => NFLstOK f W c)
    (fun _ c c' => c'.nreg 50210 =
      c.nmem ztgre)
    (fun _ _ => 17) := by
  zujaq
  obtain ⟨c', j, e, hj, v, fr⟩ := nfLst_exec (P := P) f c hw h
  exact ztinx
theorem tRegItem_exec {f tr : ℕ} (hf : f = 1 ∨ f = 3) (htr : InR tr) (hE : TGood P W M N c₀)
    (hI : TInv W c₀ c)
    (ht : c.nreg tr < if f = 1 then (N.region ztco).arcs.length
      else (N.region ztco).chords.length)
    (hroom : c.nreg ALLOC + 17 ≤ W) :
    ∃ c' k, Exec P W (tRegItem f tr) c c' k ∧ k ≤ 20 ∧
      c'.nreg 50210 = (if f = 1 then (N.region ztco).arcs
        else (N.region ztco).chords).getD (c.nreg tr) 0 ∧
      TStep W c₀ c c' k := by
  unfold InR at htr
  zubkg

  have hl : [ztblr, ztdso, ztgzh].map Prod.fst = [50200, 50201, 50202] :=
    rfl
  obtain ⟨c₁, c', k, h1, -, hm1, ex, hk, hpost, hf'⟩ := callB (nfLst_meets f)
    [ztblr, ztdso, ztgzh]
    by_grind
    by_simp ztmlh hI.hw (fun c₁ h1 _ hm => by
      zubav
      zuddl

      unfold NFLstOK NFRdOK nfVal
      rw [hm, q0, q1, q2, r02]
      have h5 := hb.2.2.2.1 _ hr
      zuklh
      · grind
      grind) hroom
  zubav
  zuddl

  refine ztdxe
  rw [hpost]
  zumto
  rw [hm1, q0, q1, q2, r02]
  have hR := hNA.2.2.2.2.2.2.2.1 _ hr
  zuklh
  · simp_all
  simp_all

/-- **Field `f` of chord `i` (register `ir`).** -/
def tChordF (f ir : ℕ) : Stmt := .seq (block (copies [ztblr, ztjfz])) ztvli
theorem tChordF_exec {f ir : ℕ} (hf : f < 5) (hir : InR ir) (hE : TGood P W M N c₀)
    (hI : TInv W c₀ c) (hi : c.nreg ir < N.nChords) (hroom : c.nreg ALLOC + 11 ≤ W) :
    ∃ c' k, Exec P W (tChordF f ir) c c' k ∧ k ≤ 13 ∧
      c'.nreg 50210 = crFld (N.chord (c.nreg ir)) f ∧
      TStep W c₀ c c' k := by
  unfold InR at hir
  zudcy

  obtain ⟨c₁, c', k, h1, -, hm1, ex, hk, hpost, hf'⟩ := callB (chordRd_meets hf)
    [ztblr, ztjfz]
    by_grind
    by_simp ztmlh hI.hw (fun c₁ h1 _ hm => by
      zubav
      zukin
      zucrc
      unfold NFRdOK
      grind) hroom
  zubav
  zukin
  zucrc
  refine ztdxe
  rw [hpost N by_simp_all (by rw [q1]; exact hi), q1]

/-- **Field `f` of arc `j` (register `jr`).** -/
def tArcF (f jr : ℕ) : Stmt := .seq (block (copies [ztblr, ztjga])) ztvel
theorem tArcF_exec {f jr : ℕ} (hf : f < 5) (hjr : InR jr) (hE : TGood P W M N c₀)
    (hI : TInv W c₀ c) (hj : c.nreg jr < N.arcs.length) (hroom : c.nreg ALLOC + 11 ≤ W) :
    ∃ c' k, Exec P W (tArcF f jr) c c' k ∧ k ≤ 13 ∧
      c'.nreg 50210 = arFld (N.arc (c.nreg jr)) f ∧
      TStep W c₀ c c' k := by
  unfold InR at hjr
  zudcy

  obtain ⟨c₁, c', k, h1, -, hm1, ex, hk, hpost, hf'⟩ := callB (arcRd_meets hf)
    [ztblr, ztjga]
    by_grind
    by_simp ztmlh hI.hw (fun c₁ h1 _ hm => by
      zubav
      zukio
      zucrc
      unfold NFRdOK
      grind) hroom
  zubav
  zukio
  zucrc
  refine ztdxe
  grind
