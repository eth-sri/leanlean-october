module

public import Chazelle.Core.FuseDegPiece

/-!
# The degree of the revised fusion, part 4: chains of wedges seen from a side chain

Let `R` be a region of `S' = J.fusion S₁ S₂ ∪ glueChords J` and `e` an exit chord of `R`
contained in a chord `c` of `Sᵢ`.  Following the chain of wedges of `R` from `e`
(`FuseDeg.chain_end`), away from the slit of `Cᵢ`, one reaches an exit chord `f` of `R` next to
one of whose attachments `R` is faced; the points just on the side of `R` of the horizontal
segment between them lie in one region of `Sᵢ` (the *strip argument*, `strip_const`), which is
the region `Phi f` of `Sᵢ` on the side of `R` of `f`, and `c` is an exit chord of it
(`parent_touch`).  Hence the chords of `Sᵢ` containing exit chords of `R` are at most `D` times
the number of exit chords of `R` faced next to an attachment (`parents_ncard_le`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft TouchesIn freeIn
  regionsIn)
open Chazelle.Geometry (lerp)
open WalkEmbed FuseMath

namespace FuseDeg

variable (J : Merge.Junction)

/-- A point of the domain of `C` off the slit of a side chain is in the domain of that chain. -/
theorem mem_side_dom {C' : Chain} (hC'P : C'.P = J.P) (hset : C'.set ⊆ J.whole.set) {x : Point}
    (hx : x ∈ J.whole.dom) (hxs : x ∉ C'.slit) : x ∈ C'.dom := by
  rw [Chain.mem_dom_iff] at hx ⊢
  refine ⟨?_, fun h => hx.2.1 (hset h), hxs⟩
  rw [radius_of_P J hC'P]; exact hx.1

/-- **Half-balls transfer to a side chain**: a half-ball of the domain of `C` on the side `τ` of a
point gives a half-ball of the free set of `Sᵢ`, away from the slit of `Cᵢ`. -/
theorem halfIn_side (hP : J.P.Simple) {C' : Chain} (hC'P : C'.P = J.P)
    (hset : C'.set ⊆ J.whole.set) {Si : Set (Set Point)} (hSiA : Si ⊆ (chainModel C').Adm)
    (hSifin : Si.Finite) {τ x h : ℝ} (hgood : HalfIn J.whole.dom τ ((x, h) : Point))
    (hcol : h < C'.top.2 ∨ (τ = -1 ∧ h ≤ C'.top.2) ∨ x ≠ C'.top.1) :
    HalfIn (freeIn C'.dom Si) τ ((x, h) : Point) := by
  have hP' : C'.P.Simple := hC'P ▸ hP
  obtain ⟨r, hr, hsub⟩ := hgood
  obtain ⟨r₂, hr₂, hch⟩ := chords_off_line (walkAx_chainModel hP') hSiA hSifin ((x, h) : Point)
  obtain ⟨r₃, hr₃, hsl⟩ : ∃ r₃ > 0, ∀ y ∈ ball ((x, h) : Point) r₃,
      0 < τ * (y.2 - h) → y ∉ C'.slit := by
    rcases hcol with hc | ⟨hτ1, hc⟩ | hc
    · refine ⟨C'.top.2 - h, by linarith, fun y hy _ hys => ?_⟩
      have h1 := (C'.mem_slit_iff.1 hys).2.1
      rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hy
      have := (abs_lt.1 hy.2).2
      simp only at this
      linarith
    · refine ⟨1, one_pos, fun y _ hy hys => ?_⟩
      have h1 := (C'.mem_slit_iff.1 hys).2.1
      rw [hτ1] at hy
      linarith
    · refine ⟨|x - C'.top.1|, abs_pos.2 (sub_ne_zero.2 hc), fun y hy _ hys => ?_⟩
      have h1 := (C'.mem_slit_iff.1 hys).1
      rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hy
      have h2 := hy.1
      simp only at h2
      rw [h1, abs_sub_comm] at h2
      exact lt_irrefl _ h2
  refine ⟨min r (min r₂ r₃), lt_min hr (lt_min hr₂ hr₃), fun y hy hpos => ?_⟩
  have hy1 := ball_subset_ball (min_le_left _ _) hy
  have hy2 := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hy
  have hy3 := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hy
  have hyD := hsub y hy1 hpos
  refine ⟨mem_side_dom J hC'P hset hyD (hsl y hy3 hpos), fun hyS => hch y hy2 ?_ hyS⟩
  intro heq
  simp only at heq hpos
  rw [heq, sub_self, mul_zero] at hpos
  exact lt_irrefl _ hpos

/-- The points of the domain between two points of the domain on an admissible chord. -/
theorem between_open {M : Model} (hM : WalkAx M) {f : Set Point} (hf : f ∈ M.Adm) {z z' : Point}
    (hz : z ∈ f) (hzD : z ∈ M.D) (hz' : z' ∈ f) (hz'D : z' ∈ M.D) {x : ℝ}
    (hx1 : min z.1 z'.1 ≤ x) (hx2 : x ≤ max z.1 z'.1) :
    ((x, z.2) : Point) ∈ M.D := by
  obtain ⟨w, q, hce, hqy, hqw, hop, hwe, hqD⟩ := sigma_end hM hf (Or.inl rfl)
  have hwD : w ∉ M.D := by
    obtain ⟨⟨p, t, hA, rfl⟩, -⟩ := hwe
    exact hM.trace p hA.1 t hA.2.1 hA.2.2.1.le
  simp only [one_mul] at hqw
  have hstrict : ∀ {y : Point}, y ∈ f → y ∈ M.D → y.2 = w.2 ∧ q.1 < y.1 ∧ y.1 < w.1 := by
    intro y hy hyD
    rw [hce] at hy
    obtain ⟨h1, h2, h3⟩ := mem_seg_sigma hqy (Or.inl rfl) (by simpa using hqw) hy
    simp only [one_mul] at h2 h3
    refine ⟨h1, lt_of_le_of_ne h2 fun h => ?_, lt_of_le_of_ne h3 fun h => ?_⟩
    · have : y = q := Geometry.point_ext h.symm (h1.trans hqy.symm)
      exact hqD (this ▸ hyD)
    · have : y = w := Geometry.point_ext h h1
      exact hwD (this ▸ hyD)
  obtain ⟨hz2, hzq, hzw⟩ := hstrict hz hzD
  obtain ⟨-, hz'q, hz'w⟩ := hstrict hz' hz'D
  rw [hz2]
  refine (open_pt hqy (Or.inl rfl) hop ?_ ?_).2
  · simp only [one_mul]
    rcases le_total z.1 z'.1 with h | h
    · rw [min_eq_left h] at hx1; linarith
    · rw [min_eq_right h] at hx1; linarith
  · simp only [one_mul]
    rcases le_total z.1 z'.1 with h | h
    · rw [max_eq_right h] at hx2; linarith
    · rw [max_eq_left h] at hx2; linarith

/-! ## The region of `Sᵢ` on the side of `R` of a chord -/

open Classical in
/-- The side (`1` above, `-1` below) of the chord `f` on which the region `R` lies. -/
noncomputable def sideOf (M : Model) (R f : Set Point) : ℝ := if SideIn M R f 1 then 1 else -1

open Classical in
/-- A point of the chord `f` in the domain. -/
noncomputable def midOf (M : Model) (f : Set Point) : Point :=
  if h : ∃ z ∈ f, z ∈ M.D then Classical.choose h else 0

open Classical in
/-- **The region of `Sᵢ` on the side of `R` of the chord `f`** (in the side model `M'`): the
region containing the points just on that side of a point of `f` (`∅` if there is none). -/
noncomputable def Phi (M M' : Model) (Si : Set (Set Point)) (R f : Set Point) : Set Point :=
  if h : ∃ U ∈ M'.regions Si, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (((midOf M f).1, (midOf M f).2 + sideOf M R f * δ) : Point) ∈ U then
    Classical.choose h
  else ∅

theorem phi_mem_or_empty (M M' : Model) (Si : Set (Set Point)) (R f : Set Point) :
    Phi M M' Si R f ∈ M'.regions Si ∨ Phi M M' Si R f = ∅ := by
  unfold Phi
  split_ifs with h
  · exact Or.inl (Classical.choose_spec h).1
  · exact Or.inr rfl


/-- The points of an admissible chord have its height. -/
theorem snd_eq_of_mem {M : Model} (hM : WalkAx M) {f : Set Point} (hf : f ∈ M.Adm) {z z' : Point}
    (hz : z ∈ f) (hz' : z' ∈ f) : z'.2 = z.2 := by
  obtain ⟨w, q, hce, hqy, hqw, -, -, -⟩ := sigma_end hM hf (Or.inl rfl)
  rw [hce] at hz hz'
  exact (mem_seg_sigma hqy (Or.inl rfl) hqw hz').1.trans (mem_seg_sigma hqy (Or.inl rfl) hqw hz).1.symm

/-- **`Phi` is the region of `Sᵢ` just on the side of `R` of any point of `f`** (below the top of
`Cᵢ`). -/
theorem phi_eq (hP : J.P.Simple) {C' : Chain} (hC'P : C'.P = J.P) (hset : C'.set ⊆ J.whole.set)
    {Si : Set (Set Point)} (hSiA : Si ⊆ (chainModel C').Adm) (hSifin : Si.Finite)
    {F : Set (Set Point)} (hF : F ⊆ (chainModel J.whole).Adm) (hfin : F.Finite) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions F) {f : Set Point} (hf : f ∈ F) {τ : ℝ}
    (hτ : τ = 1 ∨ τ = -1) (hside : SideIn (chainModel J.whole) R f τ) {z₁ : Point} (hz₁ : z₁ ∈ f)
    (hz₁D : z₁ ∈ J.whole.dom) (hh : z₁.2 ≤ C'.top.2) {V : Set Point}
    (hV : V ∈ (chainModel C').regions Si)
    (hzV : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z₁.1, z₁.2 + τ * δ) : Point) ∈ V) :
    Phi (chainModel J.whole) (chainModel C') Si R f = V := by
  set M := chainModel J.whole with hMdef
  set M' := chainModel C' with hM'def
  have hM : WalkAx M := walkAx_chainModel hP
  have hso : sideOf M R f = τ := by
    unfold sideOf
    rcases hτ with rfl | rfl
    · rw [ite_eq_left hside]
    · rw [ite_eq_right]
      intro h1
      have := side_unique hM hF hfin hf hR hz₁ hz₁D (Or.inl rfl) (Or.inr rfl) (h1 z₁ hz₁ hz₁D)
        (hside z₁ hz₁ hz₁D)
      norm_num at this
  have hex : ∃ z ∈ f, z ∈ M.D := ⟨z₁, hz₁, hz₁D⟩
  have hm : midOf M f ∈ f ∧ midOf M f ∈ M.D := by
    unfold midOf; rw [dite_eq_left hex]; exact Classical.choose_spec hex
  set m := midOf M f with hmdef
  have hm2 : m.2 = z₁.2 := snd_eq_of_mem hM (hF hf) hz₁ hm.1
  have hgood : ∀ x ∈ Icc (min z₁.1 m.1) (max z₁.1 m.1),
      HalfIn (freeIn C'.dom Si) τ ((x, z₁.2) : Point) := by
    intro x hx
    have hxD : ((x, z₁.2) : Point) ∈ M.D := between_open hM (hF hf) hz₁ hz₁D hm.1 hm.2 hx.1 hx.2
    refine halfIn_side J hP hC'P hset hSiA hSifin (halfIn_of_mem J.whole.isOpen_dom τ hxD) ?_
    rcases hh.lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · right; right
      intro hx1
      apply (J.whole.mem_dom_iff.1 hxD).2.1
      have : ((x, z₁.2) : Point) = C'.top := Prod.ext hx1 heq
      rw [this]; exact hset C'.top_mem_set
  obtain ⟨w, hw, h1, h2⟩ := strip_const hτ min_le_max hgood
  set W₀ := connectedComponentIn (freeIn C'.dom Si) w with hW₀
  have hW₀r : W₀ ∈ M'.regions Si := ⟨w, hw, rfl⟩
  have hz₁W : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z₁.1, z₁.2 + τ * δ) : Point) ∈ W₀ := by
    rcases le_total z₁.1 m.1 with h | h
    · rw [min_eq_left h] at h1; exact h1
    · rw [max_eq_left h] at h2; exact h2
  have hmW : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((m.1, m.2 + τ * δ) : Point) ∈ W₀ := by
    rw [hm2]
    rcases le_total z₁.1 m.1 with h | h
    · rw [max_eq_right h] at h2; exact h2
    · rw [min_eq_right h] at h1; exact h1
  have hmeet : ∀ {X Y : Set Point}, X ∈ M'.regions Si → Y ∈ M'.regions Si → ∀ {p : Point},
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), ((p.1, p.2 + τ * δ) : Point) ∈ X) →
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), ((p.1, p.2 + τ * δ) : Point) ∈ Y) → X = Y := by
    intro X Y hX hY p hX' hY'
    obtain ⟨δ, h3, h4⟩ := (hX'.and hY').exists
    exact (Chazelle.Chain.regionsIn_eq_or_disjoint hX hY).resolve_right
      (fun hd => hd.le_bot ⟨h3, h4⟩)
  have hWV : W₀ = V := hmeet hW₀r hV hz₁W hzV
  have hPhi : ∃ U ∈ M'.regions Si, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (((midOf M f).1, (midOf M f).2 + sideOf M R f * δ) : Point) ∈ U := by
    rw [hso]; exact ⟨W₀, hW₀r, hmW⟩
  unfold Phi
  rw [dite_eq_left hPhi]
  obtain ⟨hU, hUm⟩ := Classical.choose_spec hPhi
  have hUm' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((m.1, m.2 + τ * δ) : Point) ∈ Classical.choose hPhi :=
    hUm.mono fun δ h => by rw [show τ * δ = sideOf M R f * δ by rw [hso]]; exact h
  rw [← hWV]
  exact hmeet hU hW₀r hUm' hmW

/-- **The parent of an exit chord of `R` in `Sᵢ` is an exit chord of `Phi f`** for an exit chord
`f` of `R` faced next to an attachment (the end of the chain of wedges of `R`). -/
theorem parent_touch (hP : J.P.Simple) {C' : Chain} (hC'P : C'.P = J.P)
    (hset : C'.set ⊆ J.whole.set) {Q : Polygon} {Si : Set (Set Point)}
    (hSi : (chainModel C').ChordFamily Q Si) {F : Set (Set Point)}
    (hF : F ⊆ (chainModel J.whole).Adm) (hfin : F.Finite)
    (hends : ∀ c ∈ Si, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions F) {e : Set Point} (he : e ∈ F)
    (hRe : TouchesIn J.whole.dom e R) {c : Set Point} (hc : c ∈ Si) (hec : e ⊆ c) :
    ∃ f ∈ F, TouchesIn J.whole.dom f R ∧
      (∃ (p : ℕ) (t : ℝ), SideAttach (chainModel J.whole).W f p t ∧
        Adj (chainModel J.whole) F R p t) ∧
      c ∈ exits (chainModel C') Si (Phi (chainModel J.whole) (chainModel C') Si R f) := by
  set M := chainModel J.whole with hMdef
  set M' := chainModel C' with hM'def
  have hM : WalkAx M := walkAx_chainModel hP
  have hP' : C'.P.Simple := hC'P ▸ hP
  obtain ⟨y, a, b, hH, hy, hceq, hl, hr⟩ := Merge.augChords_spec (hSi.2.1 hc)
  -- the side of `R`
  obtain ⟨τ, hτ, hsideE⟩ : ∃ τ : ℝ, (τ = 1 ∨ τ = -1) ∧ SideIn M R e τ := by
    obtain ⟨Up, Dn, hUp, hDn, -, hside, hiff⟩ := chordSides_of_system (hM.sys F hF hfin) he
    rcases (hiff R hR).1 hRe with rfl | rfl
    · refine ⟨1, Or.inl rfl, fun z hz hzD => ?_⟩
      filter_upwards [hside z hz hzD] with δ hδ
      rw [one_mul]; exact hδ.1
    · refine ⟨-1, Or.inr rfl, fun z hz hzD => ?_⟩
      filter_upwards [hside z hz hzD] with δ hδ
      rw [show z.2 + -1 * δ = z.2 - δ by ring]; exact hδ.2
  -- points of `e` in the domain are open points of `c`
  have hopen : ∀ z ∈ e, z ∈ M.D → z.2 = y ∧ a < z.1 ∧ z.1 < b := by
    intro z hz hzD
    have hzc := hec hz
    rw [hceq] at hzc
    obtain ⟨hz2, hza, hzb⟩ := hzc
    refine ⟨hz2, lt_of_le_of_ne hza fun h => ?_, lt_of_le_of_ne hzb fun h => ?_⟩
    · have : z = Merge.lend c := by rw [hl]; exact Prod.ext h.symm hz2
      exact (hends c hc).1 (this ▸ hzD)
    · have : z = Merge.rend c := by rw [hr]; exact Prod.ext h hz2
      exact (hends c hc).2 (this ▸ hzD)
  -- a direction away from the slit of `Cᵢ`
  obtain ⟨σ, hσ, hcol⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z ∈ e, z ∈ M.D → ∀ x : ℝ,
      σ * z.1 ≤ σ * x → (y < C'.top.2 ∨ (τ = -1 ∧ y ≤ C'.top.2) ∨ x ≠ C'.top.1) := by
    by_cases hcase : y < C'.top.2 ∨ τ = -1
    · refine ⟨1, Or.inl rfl, fun z _ _ x _ => ?_⟩
      rcases hcase with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h, hy⟩)
    · push Not at hcase
      have hyt : y = C'.top.2 := le_antisymm hy hcase.1
      have htop : C'.top.1 ≤ a ∨ b ≤ C'.top.1 := by
        by_contra h
        push Not at h
        have hmem := hH.open_mem C'.top.1 h.1 h.2
        rw [hyt] at hmem
        exact C'.not_mem_set_of_mem_dom hmem C'.top_mem_set
      rcases htop with ht | ht
      · refine ⟨1, Or.inl rfl, fun z hz hzD x hx => Or.inr (Or.inr ?_)⟩
        have := (hopen z hz hzD).2.1
        intro h; simp only [one_mul] at hx; linarith
      · refine ⟨-1, Or.inr rfl, fun z hz hzD x hx => Or.inr (Or.inr ?_)⟩
        have := (hopen z hz hzD).2.2
        intro h; linarith
  obtain ⟨f, hf, hRf, hadjf, hsidef, z₀, hz₀e, hz₀D, z₁, hz₁f, hz₁D, hz₁y, hσ01, hgood⟩ :=
    chain_end hM hF hfin hR hτ hσ _ e he hRe hsideE le_rfl
  obtain ⟨hz₀y, hz₀a, hz₀b⟩ := hopen z₀ hz₀e hz₀D
  -- the strip between `z₀` and `z₁`
  have hgood' : ∀ x : ℝ, σ * z₀.1 ≤ σ * x → σ * x ≤ σ * z₁.1 →
      HalfIn (freeIn C'.dom Si) τ ((x, z₀.2) : Point) := by
    intro x h1 h2
    refine halfIn_side J hP hC'P hset hSi.2.1 hSi.1 (hgood x h1 h2) ?_
    rw [hz₀y]
    exact hcol z₀ hz₀e hz₀D x h1
  obtain ⟨V, hV, hV₀, hV₁⟩ : ∃ V ∈ M'.regions Si,
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z₀.1, z₀.2 + τ * δ) : Point) ∈ V) ∧
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z₁.1, z₀.2 + τ * δ) : Point) ∈ V) := by
    rcases hσ with rfl | rfl
    · simp only [one_mul] at hσ01 hgood'
      obtain ⟨w, hw, h1, h2⟩ := strip_const hτ hσ01 fun x hx => hgood' x hx.1 hx.2
      exact ⟨_, ⟨w, hw, rfl⟩, h1, h2⟩
    · simp only [neg_mul, one_mul, neg_le_neg_iff] at hσ01 hgood'
      obtain ⟨w, hw, h1, h2⟩ := strip_const hτ hσ01 fun x hx => hgood' x hx.2 hx.1
      exact ⟨_, ⟨w, hw, rfl⟩, h2, h1⟩
  have hPhi : Phi M M' Si R f = V := by
    refine phi_eq J hP hC'P hset hSi.2.1 hSi.1 hF hfin hR hf hτ hsidef hz₁f hz₁D
      (by rw [hz₁y, hz₀y]; exact hy) hV ?_
    rw [hz₁y]; exact hV₁
  refine ⟨f, hf, hRf, hadjf, hc, z₀, ⟨hec hz₀e, ?_⟩, ?_⟩
  · show z₀ ∈ C'.dom
    have : z₀ = ((z₀.1, y) : Point) := Prod.ext rfl hz₀y
    rw [this]; exact hH.open_mem z₀.1 hz₀a hz₀b
  · rw [hPhi]
    have htend : Tendsto (fun δ : ℝ => ((z₀.1, z₀.2 + τ * δ) : Point)) (𝓝[>] (0 : ℝ)) (𝓝 z₀) := by
      have : Tendsto (fun δ : ℝ => ((z₀.1, z₀.2 + τ * δ) : Point)) (𝓝 (0 : ℝ))
          (𝓝 ((z₀.1, z₀.2 + τ * 0) : Point)) :=
        ((continuous_const.prodMk (continuous_const.add
          (continuous_const.mul continuous_id))).tendsto 0)
      rw [mul_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact mem_closure_of_tendsto htend hV₀


/-- The exit chords of `R` next to one of whose attachments `R` is faced. -/
def adjExits (M : Model) (F : Set (Set Point)) (R : Set Point) : Set (Set Point) :=
  {f | f ∈ exits M F R ∧ ∃ (p : ℕ) (t : ℝ), SideAttach M.W f p t ∧ Adj M F R p t}

/-- **The parents in `Sᵢ` of the exit chords of `R`** are at most `D` times as many as the exit
chords of `R` faced next to an attachment. -/
theorem parents_ncard_le (hP : J.P.Simple) {C' : Chain} (hC'P : C'.P = J.P)
    (hset : C'.set ⊆ J.whole.set) {Q : Polygon} {Si : Set (Set Point)}
    (hSi : (chainModel C').ChordFamily Q Si) {F : Set (Set Point)}
    (hF : F ⊆ (chainModel J.whole).Adm) (hfin : F.Finite)
    (hends : ∀ c ∈ Si, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions F) {D : ℕ} (hdeg : (chainModel C').DegLe Si D) :
    {c | c ∈ Si ∧ ∃ e ∈ exits (chainModel J.whole) F R, e ⊆ c}.ncard ≤
      D * (adjExits (chainModel J.whole) F R).ncard := by
  set M := chainModel J.whole with hMdef
  set M' := chainModel C' with hM'def
  have hsub : {c | c ∈ Si ∧ ∃ e ∈ exits M F R, e ⊆ c} ⊆
      ⋃ f ∈ adjExits M F R, exits M' Si (Phi M M' Si R f) := by
    rintro c ⟨hc, e, ⟨he, hRe⟩, hec⟩
    obtain ⟨f, hf, hRf, hadj, hcf⟩ :=
      parent_touch J hP hC'P hset hSi hF hfin hends hR he hRe hc hec
    simp only [Set.mem_iUnion]
    exact ⟨f, ⟨⟨hf, hRf⟩, hadj⟩, hcf⟩
  refine (Set.ncard_le_ncard hsub (hSi.1.subset ?_)).trans ?_
  · intro c hc
    simp only [Set.mem_iUnion] at hc
    obtain ⟨f, -, hc, -⟩ := hc
    exact hc
  · refine ncard_biUnion_le_mul (hfin.subset fun f hf => hf.1.1) _ fun f _ => ?_
    rcases phi_mem_or_empty M M' Si R f with h | h
    · exact hdeg _ h
    · have : exits M' Si (Phi M M' Si R f) = ∅ := by
        rw [h]
        ext c
        simp only [exits, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        rintro - ⟨z, -, hz⟩
        rw [closure_empty] at hz
        exact hz
      rw [this, Set.ncard_empty]; omega

end FuseDeg

end

end Chazelle.Core
