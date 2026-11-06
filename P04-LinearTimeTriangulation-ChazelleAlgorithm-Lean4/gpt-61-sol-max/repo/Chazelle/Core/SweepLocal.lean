module

public import Chazelle.Core.SweepHit
public import Chazelle.Core.WalkEmbed

/-!
# The sweep (WP-D), part 2: local shooting

**Local shooting** (p. 502): a point `z` whose horizontal ray starts inside a region `U` of a
submap sees a point of one of the arcs of `U`.  So the first hit of the ray on the boundary of the
domain is the earliest of the first hits on the arcs of `U`, each of which one call of the ray
shooter (`ShooterOK`) answers: this is how the sweep answers every query, in the model of `C₁`
and in the model of `C₂` (tests (i), (ii) and the local shooting of pp. 502–507).

## Generic part (any good model)

* `sector_free`: near a walk position, the points of its open left sector are in the domain, and
  the only chords of a finite admissible family through them are attached at that position.
* `hit_mem_arcSet`: if the points of a horizontal ray approaching a walk position from inside its
  left sector lie in the region `U`, then the point of the position lies on (the closure of) an
  arc of `U` (`Model.arcSet`).  Four cases: inside a walk edge or at a walk vertex, with or
  without a chord of the family attached at the position (then the key is the end of an arc).
* `ray_mem_region_of_arc`, `ray_mem_region_after`, `ray_mem_region_before` (with `sub_sector`):
  conversely, the ray *leaving* a walk position into its left sector starts in the region of the
  arc around the position's key (non-cut key), or, at a cut walk vertex whose chords avoid the
  ray, in the region of the arc beginning (the ray turns counterclockwise from the next walk edge)
  or ending (clockwise from the previous walk edge) there.  This is what double identification
  (`LocateSpec`) gives a query in its own chain.

## Chain models

* `ray_subset_region`: in the chain model, a ray whose initial part is in a region `U` stays in
  `U` up to its first hit (regions are closed under visibility).
* `local_shoot`: the first-hit point of such a ray lies on an arc of `U`
  (coverage of the hit point by a walk position: `Chain.sideSees_chordEnd`).
* `arcSet_subset_compl_dom`: arcs are outside the domain.
* `firstHit_arcs`: **the first hit on the union of the arcs of `U` is the first hit of the
  chain** — the correctness of local shooting through the ray shooter.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft sideLeftOf sideCcw
  sideCross sideDot freeIn regionsIn sideLeft_edge sideLeft_zero sideLeft_not_self sideKey_inj
  sideCcw_smul)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)
open Chazelle.Jordan (offset SectorSide)

namespace Sweep

/-! ## Rays and sectors -/

/-- The displacement of a ray point is a positive multiple of the direction. -/
theorem rayPt_sub (w : Point) (τ s : ℝ) : rayPt w τ s - w = s • ((τ, 0) : Point) := by
  apply point_ext <;> simp [rayPt]; ring

/-- A left sector is a cone: if one point of a horizontal ray from the point of a position is in
it, every point of the ray is. -/
theorem sideLeft_rayPt_iff (W : Polygon) (p : ℕ) (t : ℝ) (τ : ℝ) {s s' : ℝ} (hs : 0 < s)
    (hs' : 0 < s') :
    sideLeft W p t (rayPt (sidePt W p t) τ s) ↔ sideLeft W p t (rayPt (sidePt W p t) τ s') := by
  unfold sideLeft sideLeftOf
  rw [rayPt_sub, rayPt_sub, sideCcw_smul hs, sideCcw_smul hs']

/-! ## The sector near a position -/

section Generic

variable {M : Model}

/-- **The sector near a position is free except for the chords attached there.**  Near the point
of a walk position, the points of its open left sector are in the domain, and a chord of a finite
admissible family through such a point is attached at that position. -/
theorem sector_free (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    ∃ r > 0, ∀ x ∈ ball (sidePt M.W p t) r, sideLeft M.W p t x →
      x ∈ M.D ∧ ∀ c ∈ F, x ∈ c → SideAttach M.W c p t := by
  obtain ⟨r₀, hr₀, hcl⟩ := hM.clean p hp t ht ht1
  set w := sidePt M.W p t with hw
  have hne := hM.nd p hp
  have hwD : w ∉ M.D := hM.trace p hp t ht ht1.le
  have hc : ∀ c ∈ F, ∀ᶠ x in 𝓝 w, sideLeft M.W p t x → x ∈ c → SideAttach M.W c p t := by
    intro c hcF
    obtain ⟨a, b, hab, hcab, hy, hopen, ha, hb⟩ := hM.ends c (hF hcF)
    by_cases hwc : w ∈ c
    · have hwab : w = a ∨ w = b := by
        rw [hcab] at hwc
        obtain ⟨s, hs0, hs1, he⟩ := Geometry.mem_segment_iff_lerp.1 hwc
        rcases hs0.lt_or_eq with hs0 | hs0
        · rcases hs1.lt_or_eq with hs1 | hs1
          · exact absurd (he ▸ hopen s ⟨hs0, hs1⟩) hwD
          · right; rw [he, hs1, Geometry.lerp_one]
        · left; rw [he, ← hs0, Geometry.lerp_zero]
      have hWE : WalkEnd M.W c w := by
        rcases hwab with h | h
        · rw [h]; exact ha
        · rw [h]; exact hb
      obtain ⟨⟨p', t', hA', hpt'⟩, hdisj⟩ := hWE
      by_cases hsame : p' = p ∧ t' = t
      · obtain ⟨rfl, rfl⟩ := hsame
        exact Eventually.of_forall fun _ _ _ => hA'
      · have hne' : p' = p → t' ≠ t := fun h1 h2 => hsame ⟨h1, h2⟩
        obtain ⟨r₁, hr₁, h₁⟩ := hdisj p' p t' t hA'.1 hA'.2.1 hA'.2.2.1 hp ht ht1 hne' hpt' rfl
        obtain ⟨r₂, hr₂, h₂⟩ := hA'.2.2.2.2
        filter_upwards [ball_mem_nhds w (lt_min hr₁ hr₂)] with x hx hxl hxc
        exfalso
        have hxw : x ≠ sidePt M.W p' t' := by
          rw [hpt']
          rintro rfl
          exact sideLeft_not_self hne ht1 hxl
        have hx2 : dist x (sidePt M.W p' t') < r₂ := by
          rw [hpt']; exact lt_of_lt_of_le hx (min_le_right _ _)
        exact h₁ x (ball_subset_ball (min_le_left _ _) hx) (h₂ x hxc hxw hx2) hxl
    · have hcl' : IsClosed c := by rw [hcab]; exact Geometry.isClosed_segment _ _
      filter_upwards [hcl'.isOpen_compl.mem_nhds hwc] with x hx _ hxc
      exact absurd hxc hx
  have hall := (hfin.eventually_all
    (p := fun c x => sideLeft M.W p t x → x ∈ c → SideAttach M.W c p t)).2 hc
  obtain ⟨r, hr, hsub⟩ := Metric.eventually_nhds_iff.1 (hall.and (ball_mem_nhds w hr₀))
  refine ⟨r, hr, fun x hx hxl => ⟨?_, fun c hc hxc => (hsub hx).1 c hc hxl hxc⟩⟩
  by_contra hxD
  exact hcl x (hsub hx).2 hxD hxl

end Generic

/-- A preconnected free set meeting a region lies in it. -/
theorem subset_region {D : Set Point} {F : Set (Set Point)} {U : Set Point}
    (hU : U ∈ regionsIn D F) {H : Set Point} (hH : IsPreconnected H) (hHf : H ⊆ freeIn D F)
    {x : Point} (hxH : x ∈ H) (hxU : x ∈ U) : H ⊆ U := by
  rw [Chazelle.Chain.regionsIn_eq_component hU hxU]
  exact hH.subset_connectedComponentIn hxH hHf

/-- A walk position whose key is in the closed arc `[a, b]` has its point in `arcSet a b`. -/
theorem mem_arcSet_of_key {M : Model} {a b : ℝ} {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht : 0 ≤ t)
    (ht1 : t ≤ 1) (h : sideInArc a b (p + t) ∨ (p : ℝ) + t = a ∨ (p : ℝ) + t = b) :
    sidePt M.W p t ∈ M.arcSet a b :=
  ⟨p, t, hp, ht, ht1, h, rfl⟩

/-- Keys just after a key inside an open cyclic interval are inside it. -/
theorem sideInArc_eventually_add {a b x : ℝ} (h : sideInArc a b x) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), sideInArc a b (x + s) := by
  unfold sideInArc at h ⊢
  split_ifs at h ⊢ with hab
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < b - x by linarith [h.2])]
      with s hs hs'
    have : (0 : ℝ) < s := hs
    exact ⟨by linarith [h.1], by linarith [hs'.2]⟩
  · rcases h with h | h
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have : (0 : ℝ) < s := hs
      left; linarith
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < b - x by linarith)] with s hs
      right; linarith [hs.2]

/-- The keys just before the end of an interval are inside it. -/
theorem sideInArc_before_end {l r : ℝ} (_hlr : l ≠ r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc l r (r - ε) := by
  unfold sideInArc
  split_ifs with h
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < r - l by linarith)]
      with ε hε hε'
    have : (0 : ℝ) < ε := hε
    exact ⟨by linarith [hε'.2], by linarith⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have : (0 : ℝ) < ε := hε
    right; linarith

section Generic2

variable {M : Model}

/-- **A chord attached at the point of a ray's approach goes the other way.**  If a chord of an
admissible family is attached at a walk position `w` and the points of the horizontal ray from
`w` in direction `τ` eventually avoid it, then the chord is the segment from `w` of some length
`d > 0` in direction `-τ`, and its open part is in the domain. -/
theorem attached_opposite (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hav : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p t) τ s ∉ c) :
    ∃ d > (0 : ℝ), (∀ x ∈ c, ∃ s, 0 ≤ s ∧ s ≤ d ∧ x = rayPt (sidePt M.W p t) (-τ) s) ∧
      (∀ s, 0 < s → s < d → rayPt (sidePt M.W p t) (-τ) s ∈ M.D) ∧
      (∀ s, 0 < s → s < d → rayPt (sidePt M.W p t) (-τ) s ∈ c) := by
  set w := sidePt M.W p t with hw
  have hwD : w ∉ M.D := hM.trace p hA.1 t hA.2.1 hA.2.2.1.le
  obtain ⟨a₀, b₀, hab, hcab, hy, hopen, -, -⟩ := hM.ends c hc
  have hwc : w ∈ c := hA.2.2.2.1
  -- the chord is the segment from `w` to its other end `e`
  obtain ⟨e, hce, hey, hwe, hopen'⟩ : ∃ e : Point, c = Chazelle.segment w e ∧ e.2 = w.2 ∧
      w ≠ e ∧ ∀ s ∈ Ioo (0 : ℝ) 1, lerp w e s ∈ M.D := by
    rw [hcab] at hwc
    obtain ⟨s, hs0, hs1, he⟩ := Geometry.mem_segment_iff_lerp.1 hwc
    rcases hs0.lt_or_eq with hs0 | hs0
    · rcases hs1.lt_or_eq with hs1 | hs1
      · exact absurd (he ▸ hopen s ⟨hs0, hs1⟩) hwD
      · have hwb : w = b₀ := by rw [he, hs1, Geometry.lerp_one]
        refine ⟨a₀, by rw [hcab, hwb, Geometry.segment_comm], by rw [hwb, hy], by
          rw [hwb]; exact hab.symm, ?_⟩
        rw [hwb]; exact WalkAx.open_rev hopen
    · have hwa : w = a₀ := by rw [he, ← hs0, Geometry.lerp_zero]
      exact ⟨b₀, by rw [hcab, hwa], by rw [hwa, hy], by rw [hwa]; exact hab, by rw [hwa]; exact hopen⟩
  have hδ : e.1 - w.1 ≠ 0 := by
    intro h; apply hwe; exact point_ext (by linarith) hey.symm
  have hττ : τ * τ = 1 := by rcases hτ with rfl | rfl <;> norm_num
  have hlerp : ∀ u : ℝ, lerp w e u = ((w.1 + u * (e.1 - w.1), w.2) : Point) := by
    intro u; apply point_ext <;> simp [lerp, hey]
  -- the chord does not go in direction `τ`
  have hneg : τ * (e.1 - w.1) < 0 := by
    by_contra hpos
    push Not at hpos
    have hpos' : 0 < τ * (e.1 - w.1) := lt_of_le_of_ne hpos (by
      intro h; apply hδ
      have := congrArg (τ * ·) h
      simp only [mul_zero] at this
      nlinarith)
    obtain ⟨s, hs1, hs2⟩ := (hav.and (Ioo_mem_nhdsGT hpos')).exists
    apply hs1
    rw [hce]
    have e1 : rayPt w τ s = lerp w e (s / (τ * (e.1 - w.1))) := by
      rw [hlerp]
      apply point_ext
      · simp only [rayPt_fst]
        have h2 : s / (τ * (e.1 - w.1)) * (e.1 - w.1) = τ * s := by
          rw [div_mul_eq_mul_div, div_eq_iff (ne_of_gt hpos')]
          linear_combination (-(s * (e.1 - w.1))) * hττ
        rw [h2]
      · simp
    rw [e1]
    exact Geometry.lerp_mem_segment _ _ (div_nonneg hs2.1.le hpos'.le)
      ((div_le_one hpos').2 hs2.2.le)
  set d := -(τ * (e.1 - w.1)) with hd
  have hdpos : 0 < d := by linarith
  have hrel : ∀ u : ℝ, lerp w e u = rayPt w (-τ) (u * d) := by
    intro u
    rw [hlerp]
    apply point_ext
    · simp only [rayPt_fst, hd]
      linear_combination (-u) * (e.1 - w.1) * hττ
    · simp
  refine ⟨d, hdpos, ?_, ?_, ?_⟩
  · intro x hx
    rw [hce] at hx
    obtain ⟨u, hl0, hl1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
    exact ⟨u * d, by positivity, by nlinarith, hrel u⟩
  · intro s hs0 hs1
    have := hopen' (s / d) ⟨div_pos hs0 hdpos, (div_lt_one hdpos).2 hs1⟩
    rwa [hrel, div_mul_cancel₀ _ hdpos.ne'] at this
  · intro s hs0 hs1
    rw [hce]
    have := Geometry.lerp_mem_segment w e (div_pos hs0 hdpos).le ((div_le_one hdpos).2 hs1.le)
    rwa [hrel, div_mul_cancel₀ _ hdpos.ne'] at this

end Generic2

/-! ## Arcs through a position -/

section Arcs

variable {M : Model}

/-- The walk vertex before `p`, followed by one step, is `p`. -/
theorem prev_succ_mod {n p : ℕ} (hp : p < n) : ((p + n - 1) % n + 1) % n = p := by
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · have h1 : (0 + n - 1) % n = n - 1 := by
      rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [h1, Nat.sub_add_cancel (by omega), Nat.mod_self]
  · have h1 : (p + n - 1) % n = p - 1 := by
      rw [show p + n - 1 = (p - 1) + n by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, Nat.sub_add_cancel hp0]
    exact Nat.mod_eq_of_lt hp

/-- For `1 ≤ p`, the walk vertex before `p` is `p - 1`. -/
theorem prev_mod {n p : ℕ} (hp : p < n) (hp0 : 1 ≤ p) : (p + n - 1) % n = p - 1 := by
  rw [show p + n - 1 = (p - 1) + n by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- **A non-cut position inside an edge facing `U`** has its point on an arc of `U`. -/
theorem arc_of_faces_edge (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut F (p + t)) (hf : M.Faces p t U) :
    ∃ a b, M.IsArc F U a b ∧ sidePt M.W p t ∈ M.arcSet a b := by
  have hpos : (0 : ℝ) < p + t := by have := ht.1; positivity
  obtain ⟨X, hX, l, r, harc, hin⟩ := WalkEmbed.exists_arc_around hGM hFam hpos hcut
  have hfX : M.Faces p t X := harc.2.2.2.2.2.2 p t hp ht.1 ht.2 hin
  have hXU : X = U := WalkAx.faces_unique hX hU hfX hf
  subst hXU
  exact ⟨l, r, harc, mem_arcSet_of_key hp ht.1.le ht.2.le (Or.inl hin)⟩

/-- **A non-cut walk vertex whose next positions face `U`** is on an arc of `U`. -/
theorem arc_of_faces_after (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    (hp0 : 0 < p) (hcut : ¬ M.IsCut F p) (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U) :
    ∃ a b, M.IsArc F U a b ∧ sidePt M.W p 0 ∈ M.arcSet a b := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp0
  obtain ⟨X, hX, l, r, harc, hin⟩ := WalkEmbed.exists_arc_around hGM hFam hpos hcut
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hf.and (sideInArc_eventually_add hin)).and (Ioo_mem_nhdsGT one_pos)).exists
  have hfX : M.Faces p s X := harc.2.2.2.2.2.2 p s hp hs3.1 hs3.2 hs2
  have hXU : X = U := WalkAx.faces_unique hX hU hfX hs1
  subst hXU
  exact ⟨l, r, harc, mem_arcSet_of_key hp le_rfl zero_le_one (Or.inl (by rwa [add_zero]))⟩

/-- **A cut walk vertex whose next positions face `U`** starts an arc of `U`. -/
theorem arc_of_attach_after (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {p : ℕ} (hA : SideAttach M.W c p 0)
    {U : Set Point} (hU : U ∈ M.regions F) (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U) :
    ∃ a b, M.IsArc F U a b ∧ sidePt M.W p 0 ∈ M.arcSet a b := by
  obtain ⟨U', V', l, r, hU', -, -, harcU, -, -⟩ := hM.attach_face hF hfin hc hA
  have hne : F.Nonempty := ⟨c, hc⟩
  obtain ⟨-, -, hkr⟩ := WalkAx.arc_cuts hne harcU
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hf.and (WalkAx.eventually_after_start hkr)).and (Ioo_mem_nhdsGT one_pos)).exists
  have hin : sideInArc ((p : ℝ) + 0) r (p + s) := by rw [add_zero] at hs2 ⊢; exact hs2
  have hfU' := harcU.2.2.2.2.2.2 p s hA.1 hs3.1 hs3.2 hin
  have hUU : U' = U := WalkAx.faces_unique hU' hU hfU' hs1
  subst hUU
  exact ⟨_, r, harcU, mem_arcSet_of_key hA.1 le_rfl zero_le_one (Or.inr (Or.inl rfl))⟩

/-- **A cut walk vertex whose previous positions face `U`** ends an arc of `U`. -/
theorem arc_of_attach_before (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {p : ℕ} (hp0 : 1 ≤ p)
    (hA : SideAttach M.W c p 0) {U : Set Point} (hU : U ∈ M.regions F)
    (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces (p - 1) (1 - s) U) :
    ∃ a b, M.IsArc F U a b ∧ sidePt M.W p 0 ∈ M.arcSet a b := by
  obtain ⟨-, V', l, r, -, hV', -, -, harcV, -⟩ := hM.attach_face hF hfin hc hA
  have hne : F.Nonempty := ⟨c, hc⟩
  obtain ⟨-, -, hlk⟩ := WalkAx.arc_cuts hne harcV
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hf.and (sideInArc_before_end hlk)).and (Ioo_mem_nhdsGT one_pos)).exists
  have hcast : ((p - 1 : ℕ) : ℝ) + (1 - s) = (p : ℝ) + 0 - s := by
    rw [Nat.cast_sub hp0]; push_cast; ring
  have hin : sideInArc l ((p : ℝ) + 0) ((p - 1 : ℕ) + (1 - s)) := by rw [hcast]; exact hs2
  have hp1 : p - 1 < M.W.n := by have := hA.1; omega
  have hfV' := harcV.2.2.2.2.2.2 (p - 1) (1 - s) hp1 (by linarith [hs3.2]) (by linarith [hs3.1])
    hin
  have hVV : V' = U := WalkAx.faces_unique hV' hU hfV' hs1
  subst hVV
  exact ⟨l, _, harcV, mem_arcSet_of_key hA.1 le_rfl zero_le_one (Or.inr (Or.inr rfl))⟩

end Arcs

/-! ## The hit point lies on an arc of the region -/

section Hit

variable {M : Model}

/-- The distance from `w` of a point of a horizontal ray from `w`. -/
theorem dist_rayPt (w : Point) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1) {s : ℝ} (hs : 0 ≤ s) :
    dist (rayPt w τ s) w = s := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [rayPt_fst, rayPt_snd, add_sub_cancel_left, sub_self, abs_zero]
  rcases hτ with rfl | rfl
  · rw [one_mul, abs_of_nonneg hs, max_eq_left hs]
  · rw [neg_one_mul, abs_neg, abs_of_nonneg hs, max_eq_left hs]


/-- Unfolding a corner sector. -/
theorem sideLeftOf_iff (a v b x : Point) :
    sideLeftOf a v b x ↔ sideCcw (b - v) (x - v) (a - v) := Iff.rfl

/-- The opposite horizontal direction reverses cross and dot products. -/
theorem sideCross_neg_dir (B : Point) (τ : ℝ) :
    sideCross B ((-τ, 0) : Point) = -sideCross B ((τ, 0) : Point) := by
  unfold sideCross; ring

theorem sideDot_neg_dir (B : Point) (τ : ℝ) :
    sideDot B ((-τ, 0) : Point) = -sideDot B ((τ, 0) : Point) := by
  unfold sideDot; ring

/-- A horizontal direction strictly counterclockwise from `B` (less than a half turn) lies in the
sector from `B` to the opposite direction. -/
theorem ccw_half_left {B : Point} {τ : ℝ} (h : 0 < sideCross B ((τ, 0) : Point)) :
    sideCcw B ((τ, 0) : Point) ((-τ, 0) : Point) := by
  right; left
  refine ⟨?_, Or.inl h⟩
  rw [sideCross_neg_dir]; linarith

/-- A horizontal direction strictly clockwise from `A` (less than a half turn) lies in the sector
from the opposite direction to `A`. -/
theorem ccw_half_right {A : Point} {τ : ℝ} (h : 0 < sideCross ((τ, 0) : Point) A) :
    sideCcw ((-τ, 0) : Point) ((τ, 0) : Point) A := by
  right; left
  refine ⟨?_, Or.inr h⟩
  have e : sideCross ((-τ, 0) : Point) A = -sideCross ((τ, 0) : Point) A := by
    unfold sideCross; ring
  rw [e]; linarith

/-- The full-turn degenerate case of the dichotomy. -/
theorem cross_dir_aux {B A : Point} {τ : ℝ} (h1 : sideCross B A = 0) (h2 : 0 < sideDot B A)
    (h3 : sideCross B ((τ, 0) : Point) < 0) : 0 < sideCross ((τ, 0) : Point) A := by
  unfold sideCross sideDot at *
  simp only at *
  have e : τ * A.2 * (B.1 ^ 2 + B.2 ^ 2) = (τ * B.2) * (B.1 * A.1 + B.2 * A.2) := by
    linear_combination (τ * B.1) * h1
  have hb : 0 < τ * B.2 := by linarith
  have hS : 0 < B.1 ^ 2 + B.2 ^ 2 := by
    have : B.2 ≠ 0 := by rintro h; rw [h] at hb; simp at hb
    positivity
  have hP : 0 < (τ * B.2) * (B.1 * A.1 + B.2 * A.2) := mul_pos hb h2
  rw [← e] at hP
  nlinarith [hP, hS]

/-- **The first-hit point lies on an arc of the region** (generic good model).  Let the points
of the horizontal ray from the point `w` of a walk position `(p, t)` in direction `τ` lie in the
left sector of the position and, near `w`, in the region `U` of an admissible family.  Then `w`
lies on the closure of an arc of `U`.  (Proof: near `w` the sector is free except for the chords
attached at the position; such a chord goes in direction `-τ`, which forces `t = 0` and splits the
sector at the chord; the part containing the ray lies in `U` and contains the offsets of the
positions just after or just before the position, whose arcs then belong to `U`.) -/
theorem hit_mem_arcSet (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hkey : 0 < (p : ℝ) + t) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : ∀ s > 0, sideLeft M.W p t (rayPt (sidePt M.W p t) τ s))
    (happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p t) τ s ∈ U) :
    ∃ a b, M.IsArc F U a b ∧ sidePt M.W p t ∈ M.arcSet a b := by
  have hM := walkAx_of_goodModel hGM
  have hF : F ⊆ M.Adm := hFam.2.1
  have hfin : F.Finite := hFam.1
  obtain ⟨r, hr, hsf⟩ := sector_free hM hF hfin hp ht ht1
  have hUfree : U ⊆ freeIn M.D F := Chazelle.Chain.regionsIn_subset hU
  have hne := hM.nd p hp
  have hball : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p t) τ s ∈ ball (sidePt M.W p t) r := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr] with s hs hs'
    rw [mem_ball, dist_rayPt _ hτ (le_of_lt hs)]
    exact hs'.2
  obtain ⟨s₁, ⟨hs₁U, hs₁B⟩, hs₁pos⟩ := ((happ.and hball).and self_mem_nhdsWithin).exists
  have hs₁pos' : (0 : ℝ) < s₁ := hs₁pos
  -- the chords through the ray near `w` avoid it
  have havoid : ∀ c ∈ F, ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p t) τ s ∉ c := by
    intro c hc
    filter_upwards [happ] with s hs hsc
    exact (hUfree hs).2 ⟨c, hc, hsc⟩
  by_cases hcut : M.IsCut F (p + t)
  · -- a chord is attached at the position
    obtain ⟨c, hcF, p', t', hA', hk⟩ := hcut
    obtain ⟨hpp, htt⟩ := sideKey_inj ht ht1 hA'.2.1 hA'.2.2.1 hk
    rw [← hpp, ← htt] at hA'
    obtain ⟨d, hd, -, hcD, hcmem⟩ := attached_opposite hM (hF hcF) hA' hτ (havoid c hcF)
    obtain ⟨r₃, hr₃, hcl⟩ := hA'.2.2.2.2
    -- a point of the chord near `w`
    set s₂ := min (d / 2) (r₃ / 2) with hs₂
    have hs₂0 : 0 < s₂ := lt_min (by linarith) (by linarith)
    have hs₂d : s₂ < d := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hs₂r : s₂ < r₃ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hx₂ : sideLeft M.W p t (rayPt (sidePt M.W p t) (-τ) s₂) := by
      refine hcl _ (hcmem s₂ hs₂0 hs₂d) ?_ ?_
      · intro h
        have := congrArg Prod.fst h
        simp only [rayPt_fst] at this
        rcases hτ with rfl | rfl <;> linarith
      · rw [dist_rayPt _ (by rcases hτ with rfl | rfl <;> norm_num) hs₂0.le]; exact hs₂r
    -- the position is a walk vertex
    have ht0 : t = 0 := by
      by_contra ht0
      have ht0' : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht (Ne.symm ht0), ht1⟩
      have h1 := (sideLeft_edge hne ht0' _).1 (hsec 1 one_pos)
      have h2 := (sideLeft_edge hne ht0' _).1 hx₂
      have hw0 : det (M.W.vtx p) (M.W.vtx ((p + 1) % M.W.n)) (sidePt M.W p t) = 0 :=
        Geometry.det_lerp_self _ _ _
      unfold det at h1 h2 hw0
      simp only [rayPt_fst, rayPt_snd] at h1 h2
      rcases hτ with rfl | rfl <;> nlinarith
    subst ht0
    have hp1 : 1 ≤ p := by
      have : (0 : ℝ) < p := by simpa using hkey
      exact_mod_cast this
    have hn0 : 0 < M.W.n := by omega
    have hwv : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero _ _
    set v := M.W.vtx p with hv
    set a := M.W.vtx ((p + M.W.n - 1) % M.W.n) with ha
    set b := M.W.vtx ((p + 1) % M.W.n) with hb
    have hbv : b ≠ v := fun h => hne h.symm
    have hav : a ≠ v := by
      have := hM.nd _ (Nat.mod_lt (p + M.W.n - 1) hn0)
      rwa [prev_succ_mod hp] at this
    have hB0 : b - v ≠ 0 := sub_ne_zero.2 hbv
    have hA0 : a - v ≠ 0 := sub_ne_zero.2 hav
    have hsecv : ∀ x, sideLeft M.W p 0 x ↔ sideCcw (b - v) (x - v) (a - v) :=
      fun x => sideLeft_zero _ _ _
    have hττ : τ * τ = 1 := by rcases hτ with rfl | rfl <;> norm_num
    have hdm0 : ((-τ, 0) : Point) ≠ 0 := by
      intro h; have := congrArg Prod.fst h; simp only [Prod.fst_zero] at this
      rcases hτ with rfl | rfl <;> norm_num at this
    have hvdm : v + ((-τ, 0) : Point) ≠ v := by
      intro h; apply hdm0; simpa using h
    have hdp : sideCcw (b - v) ((τ, 0) : Point) (a - v) := by
      have := (hsecv _).1 (hsec 1 one_pos)
      rwa [hwv, rayPt_sub, one_smul] at this
    have hdm : sideCcw (b - v) ((-τ, 0) : Point) (a - v) := by
      have := (hsecv _).1 hx₂
      rwa [hwv, rayPt_sub, sideCcw_smul hs₂0] at this
    -- the edge after the vertex does not go along the chord
    have hBdm : ¬ (sideCross (b - v) ((-τ, 0) : Point) = 0 ∧
        0 < sideDot (b - v) ((-τ, 0) : Point)) := by
      rintro ⟨h1, h2⟩
      simp only [sideCross, sideDot, Prod.fst_sub, Prod.snd_sub] at h1 h2
      have hb2 : b.2 = v.2 := by
        have h1' : (b.2 - v.2) * τ = 0 := by linarith
        rcases mul_eq_zero.1 h1' with h | h
        · linarith
        · rcases hτ with rfl | rfl <;> norm_num at h
      set k := -(τ * (b.1 - v.1)) with hk
      have hk0 : 0 < k := by rw [hk]; nlinarith
      set s := min d k / 2 with hs
      have hmin : 0 < min d k := lt_min hd hk0
      have hs0 : 0 < s := by rw [hs]; linarith
      have hsd : s < d := by rw [hs]; linarith [min_le_left d k]
      have hsk : s ≤ k := by rw [hs]; linarith [min_le_right d k]
      have hmem : rayPt v (-τ) s ∈ M.D := by rw [← hwv]; exact hcD s hs0 hsd
      apply hM.trace p hp (s / k) (div_nonneg hs0.le hk0.le) ((div_le_one hk0).2 hsk)
      have e : sidePt M.W p (s / k) = rayPt v (-τ) s := by
        unfold sidePt
        apply point_ext
        · simp only [lerp_fst, rayPt_fst]
          have h3 : s / k * (b.1 - v.1) = -τ * s := by
            rw [div_mul_eq_mul_div, div_eq_iff hk0.ne', hk]
            linear_combination (-(s * (b.1 - v.1))) * hττ
          rw [← h3]
        · simp only [lerp_snd, rayPt_snd]
          rw [show (M.W.vtx ((p + 1) % M.W.n)).2 = b.2 from rfl, hb2]; ring
      rw [e]; exact hmem
    -- the ray is on one side of the chord
    have hdich : 0 < sideCross (b - v) ((τ, 0) : Point) ∨ 0 < sideCross ((τ, 0) : Point) (a - v) := by
      rcases hdp with ⟨-, h2, -⟩ | ⟨-, h2⟩ | ⟨-, -, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl h2
      · exact h2
      · exact Or.inl h3
      · rcases lt_trichotomy (sideCross (b - v) ((τ, 0) : Point)) 0 with h4 | h4 | h4
        · exact Or.inr (cross_dir_aux h1 h2 h4)
        · exfalso; apply hBdm
          rcases h3 with h3 | h3
          · exact absurd h4 h3
          · rw [sideCross_neg_dir, sideDot_neg_dir, h4]
            exact ⟨by ring, by linarith⟩
        · exact Or.inl h4
    -- chord points through the sector are on the chord's ray
    have hchord : ∀ x ∈ ball v r, sideLeft M.W p 0 x → x ∉ ⋃₀ F →
        x ∈ freeIn M.D F := by
      intro x hx hxl hxF
      exact ⟨(hsf x (by rw [hwv]; exact hx) hxl).1, hxF⟩
    have hray : ∀ x ∈ ball v r, sideLeft M.W p 0 x → x ∈ ⋃₀ F →
        ∃ s' : ℝ, 0 ≤ s' ∧ x - v = s' • ((-τ, 0) : Point) := by
      rintro x hx hxl ⟨c', hc', hxc'⟩
      have hA'' := (hsf x (by rw [hwv]; exact hx) hxl).2 c' hc' hxc'
      obtain ⟨d', -, hpts, -, -⟩ := attached_opposite hM (hF hc') hA'' hτ (havoid c' hc')
      obtain ⟨s', hs'0, -, hxs'⟩ := hpts x hxc'
      refine ⟨s', hs'0, ?_⟩
      rw [hxs', hwv, rayPt_sub]
    have hs₁B' : rayPt v τ s₁ ∈ ball v r := by rw [← hwv]; exact hs₁B
    have hs₁U' : rayPt v τ s₁ ∈ U := by rw [← hwv]; exact hs₁U
    rcases hdich with h | h
    · -- the ray is between the edge after the vertex and the chord
      obtain ⟨-, hHc, hoff⟩ := Chazelle.Chain.sideSector hvdm hbv (S := ∅) hr
        (fun _ _ h => h.elim)
      have hHsec : ∀ x ∈ ball v r ∩ {x | sideLeftOf (v + ((-τ, 0) : Point)) v b x},
          sideCcw (b - v) (x - v) ((-τ, 0) : Point) := by
        intro x hx
        have : sideLeftOf (v + ((-τ, 0) : Point)) v b x := hx.2
        rwa [sideLeftOf_iff, add_sub_cancel_left] at this
      have hHfree : ball v r ∩ {x | sideLeftOf (v + ((-τ, 0) : Point)) v b x} ⊆
          freeIn M.D F := by
        intro x hx
        have hxs : sideLeft M.W p 0 x :=
          (hsecv x).2 (Chazelle.Chain.sideCcw_sub_left hB0 hdm (hHsec x hx))
        refine hchord x hx.1 hxs ?_
        intro hxF
        obtain ⟨s', hs'0, hxs'⟩ := hray x hx.1 hxs hxF
        have h5 := hHsec x hx
        rw [hxs'] at h5
        refine Chazelle.Chain.sideCcw_not_ray_right hdm0 ?_ ?_ h5
        · unfold sideCross; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
        · unfold sideDot; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
          nlinarith [mul_nonneg hs'0 (mul_self_nonneg τ)]
      have hs₁H : rayPt v τ s₁ ∈ ball v r ∩ {x | sideLeftOf (v + ((-τ, 0) : Point)) v b x} := by
        refine ⟨hs₁B', ?_⟩
        show sideLeftOf (v + ((-τ, 0) : Point)) v b (rayPt v τ s₁)
        rw [sideLeftOf_iff, add_sub_cancel_left, rayPt_sub, sideCcw_smul hs₁pos']
        exact ccw_half_left h
      have hHU := subset_region hU hHc hHfree hs₁H hs₁U'
      have hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U := by
        filter_upwards [hoff] with s hs
        filter_upwards [hs] with δ hδ
        have := hHU hδ.2
        rwa [one_mul] at this
      exact arc_of_attach_after hM hF hfin hcF hA' hU hf
    · -- the ray is between the chord and the edge before the vertex
      obtain ⟨-, hHc, hoff⟩ := Chazelle.Chain.sideSector hav hvdm (S := ∅) hr
        (fun _ _ h => h.elim)
      have hHsec : ∀ x ∈ ball v r ∩ {x | sideLeftOf a v (v + ((-τ, 0) : Point)) x},
          sideCcw ((-τ, 0) : Point) (x - v) (a - v) := by
        intro x hx
        have : sideLeftOf a v (v + ((-τ, 0) : Point)) x := hx.2
        rwa [sideLeftOf_iff, add_sub_cancel_left] at this
      have hHfree : ball v r ∩ {x | sideLeftOf a v (v + ((-τ, 0) : Point)) x} ⊆
          freeIn M.D F := by
        intro x hx
        have hxs : sideLeft M.W p 0 x :=
          (hsecv x).2 (Chazelle.Chain.sideCcw_sub_right hB0 hdm0 hA0 hdm (hHsec x hx))
        refine hchord x hx.1 hxs ?_
        intro hxF
        obtain ⟨s', hs'0, hxs'⟩ := hray x hx.1 hxs hxF
        have h5 := hHsec x hx
        rw [hxs'] at h5
        refine Chazelle.Chain.sideCcw_not_ray_left hdm0 ?_ ?_ h5
        · unfold sideCross; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
        · unfold sideDot; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
          nlinarith [mul_nonneg hs'0 (mul_self_nonneg τ)]
      have hs₁H : rayPt v τ s₁ ∈ ball v r ∩ {x | sideLeftOf a v (v + ((-τ, 0) : Point)) x} := by
        refine ⟨hs₁B', ?_⟩
        show sideLeftOf a v (v + ((-τ, 0) : Point)) (rayPt v τ s₁)
        rw [sideLeftOf_iff, add_sub_cancel_left, rayPt_sub, sideCcw_smul hs₁pos']
        exact ccw_half_right h
      have hHU := subset_region hU hHc hHfree hs₁H hs₁U'
      have hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces (p - 1) (1 - s) U := by
        filter_upwards [hoff] with s hs
        filter_upwards [hs] with δ hδ
        have := hHU hδ.1
        rw [one_mul] at this
        show Jordan.offset (M.W.vtx (p - 1)) (M.W.vtx ((p - 1 + 1) % M.W.n)) (1 - s) δ ∈ U
        rw [Nat.sub_add_cancel hp1, Nat.mod_eq_of_lt hp, ← prev_mod hp hp1]
        exact this
      exact arc_of_attach_before hM hF hfin hcF hp1 hA' hU hf
  · -- no chord is attached at the position
    have hfreeS : ∀ x ∈ ball (sidePt M.W p t) r, sideLeft M.W p t x → x ∈ freeIn M.D F := by
      intro x hx hxl
      obtain ⟨hxD, hxc⟩ := hsf x hx hxl
      refine ⟨hxD, ?_⟩
      rintro ⟨c, hcF, hxc'⟩
      exact hcut ⟨c, hcF, p, t, hxc c hcF hxc', rfl⟩
    rcases ht.lt_or_eq with ht0 | ht0
    · -- inside a walk edge
      have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
      have hHc : IsPreconnected (ball (sidePt M.W p t) r ∩
          {x : Point | 0 < 1 * det (M.W.vtx p) (M.W.vtx ((p + 1) % M.W.n)) x}) :=
        ((convex_ball _ r).inter (Chazelle.Jordan.convex_det_pos _ _ 1)).isPreconnected
      have hHfree : ball (sidePt M.W p t) r ∩
          {x : Point | 0 < 1 * det (M.W.vtx p) (M.W.vtx ((p + 1) % M.W.n)) x} ⊆
          freeIn M.D F := fun x hx =>
        hfreeS x hx.1 ((sideLeft_edge hne ht' x).2 (by simpa using hx.2))
      have hs₁H : rayPt (sidePt M.W p t) τ s₁ ∈ ball (sidePt M.W p t) r ∩
          {x : Point | 0 < 1 * det (M.W.vtx p) (M.W.vtx ((p + 1) % M.W.n)) x} :=
        ⟨hs₁B, by simpa using (sideLeft_edge hne ht' _).1 (hsec s₁ hs₁pos')⟩
      have hHU := subset_region hU hHc hHfree hs₁H hs₁U
      have hf : M.Faces p t U := by
        filter_upwards [hM.eventually_offset_left hp ht' hr] with δ hδ
        exact hHU ⟨hδ.1, by simpa using (sideLeft_edge hne ht' _).1 hδ.2⟩
      exact arc_of_faces_edge hGM hFam hU hp ht' hcut hf
    · -- at a walk vertex
      subst ht0
      have hp0 : 0 < p := by
        have : (0 : ℝ) < p := by simpa using hkey
        exact_mod_cast this
      have hn0 : 0 < M.W.n := by omega
      have hwv : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero _ _
      set v := M.W.vtx p with hv
      set a := M.W.vtx ((p + M.W.n - 1) % M.W.n) with ha
      set b := M.W.vtx ((p + 1) % M.W.n) with hb
      have hbv : b ≠ v := fun h => hne h.symm
      have hav : a ≠ v := by
        have := hM.nd _ (Nat.mod_lt (p + M.W.n - 1) hn0)
        rwa [prev_succ_mod hp] at this
      obtain ⟨-, hHc, hoff⟩ := Chazelle.Chain.sideSector hav hbv (S := ∅) hr (fun _ _ h => h.elim)
      have hHfree : ball v r ∩ {x | sideLeftOf a v b x} ⊆ freeIn M.D F := fun x hx =>
        hfreeS x (by rw [hwv]; exact hx.1) ((sideLeft_zero _ _ _).2 hx.2)
      have hs₁H : rayPt v τ s₁ ∈ ball v r ∩ {x | sideLeftOf a v b x} := by
        refine ⟨by rw [← hwv]; exact hs₁B, ?_⟩
        have := hsec s₁ hs₁pos'
        rw [hwv] at this
        exact (sideLeft_zero _ _ _).1 this
      have hHU := subset_region hU hHc hHfree hs₁H (by rw [← hwv]; exact hs₁U)
      have hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U := by
        filter_upwards [hoff] with s hs
        filter_upwards [hs] with δ hδ
        have := hHU hδ.2
        rwa [one_mul] at this
      exact arc_of_faces_after hGM hFam hU hp hp0 (by simpa using hcut) hf

end Hit


/-! ## The region of a ray leaving a walk position -/

section Leave

variable {M : Model}

/-- **The ray leaving a position inside an arc** starts in the region of the arc: if the key of
the walk position `(p, t)` is inside an arc of `U` and the direction `τ` points into the left
sector of the position, the initial part of the ray is in `U`.  (Used after double
identification, `LocateSpec`, for the local shooting of a query in its own chain.) -/
theorem ray_mem_region_of_arc (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) {a b : ℝ} (harc : M.IsArc F U a b)
    (hin : sideInArc a b (p + t)) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p t (rayPt (sidePt M.W p t) τ 1)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p t) τ s ∈ U := by
  have hM := walkAx_of_goodModel hGM
  have hF : F ⊆ M.Adm := hFam.2.1
  have hfin : F.Finite := hFam.1
  have hne := hM.nd p hp
  have hcut : ¬ M.IsCut F (p + t) := harc.2.2.2.2.2.1 _ hin
  obtain ⟨r, hr, hsf⟩ := sector_free hM hF hfin hp ht ht1
  have hfreeS : ∀ x ∈ ball (sidePt M.W p t) r, sideLeft M.W p t x → x ∈ freeIn M.D F := by
    intro x hx hxl
    obtain ⟨hxD, hxc⟩ := hsf x hx hxl
    refine ⟨hxD, ?_⟩
    rintro ⟨c, hcF, hxc'⟩
    exact hcut ⟨c, hcF, p, t, hxc c hcF hxc', rfl⟩
  have hsec' : ∀ s > 0, sideLeft M.W p t (rayPt (sidePt M.W p t) τ s) :=
    fun s hs => (sideLeft_rayPt_iff _ p t τ one_pos hs).1 hsec
  have hball : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p t) τ s ∈ ball (sidePt M.W p t) r ∧
      0 < s := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr] with s hs hs'
    refine ⟨?_, hs⟩
    rw [mem_ball, dist_rayPt _ hτ (le_of_lt hs)]
    exact hs'.2
  -- the sector near the position is a preconnected free set containing faced points
  obtain ⟨H, hHc, hHfree, hHsec, hHU⟩ : ∃ H : Set Point, IsPreconnected H ∧ H ⊆ freeIn M.D F ∧
      (∀ x ∈ ball (sidePt M.W p t) r, sideLeft M.W p t x → x ∈ H) ∧ (∃ x ∈ H, x ∈ U) := by
    rcases ht.lt_or_eq with ht0 | ht0
    · have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
      refine ⟨ball (sidePt M.W p t) r ∩
          {x : Point | 0 < 1 * det (M.W.vtx p) (M.W.vtx ((p + 1) % M.W.n)) x},
        ((convex_ball _ r).inter (Chazelle.Jordan.convex_det_pos _ _ 1)).isPreconnected,
        fun x hx => hfreeS x hx.1 ((sideLeft_edge hne ht' x).2 (by simpa using hx.2)),
        fun x hx hxl => ⟨hx, by simpa using (sideLeft_edge hne ht' x).1 hxl⟩, ?_⟩
      have hf : M.Faces p t U := harc.2.2.2.2.2.2 p t hp ht0 ht1 hin
      obtain ⟨δ, hδU, hδ⟩ := (hf.and (hM.eventually_offset_left hp ht' hr)).exists
      exact ⟨_, ⟨hδ.1, by simpa using (sideLeft_edge hne ht' _).1 hδ.2⟩, hδU⟩
    · subst ht0
      have hn0 : 0 < M.W.n := by omega
      have hwv : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero _ _
      have hbv : M.W.vtx ((p + 1) % M.W.n) ≠ M.W.vtx p := fun h => hne h.symm
      have hav : M.W.vtx ((p + M.W.n - 1) % M.W.n) ≠ M.W.vtx p := by
        have := hM.nd _ (Nat.mod_lt (p + M.W.n - 1) hn0)
        rwa [prev_succ_mod hp] at this
      obtain ⟨-, hHc, hoff⟩ := Chazelle.Chain.sideSector hav hbv (S := ∅) hr (fun _ _ h => h.elim)
      refine ⟨_, hHc, fun x hx => hfreeS x (by rw [hwv]; exact hx.1)
        ((sideLeft_zero _ _ _).2 hx.2), fun x hx hxl => ⟨by rw [← hwv]; exact hx,
        (sideLeft_zero _ _ _).1 hxl⟩, ?_⟩
      obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
        ((hoff.and (sideInArc_eventually_add hin)).and (Ioo_mem_nhdsGT one_pos)).exists
      have hf : M.Faces p s U := harc.2.2.2.2.2.2 p s hp hs3.1 hs3.2 (by
        rw [add_zero] at hs2; exact hs2)
      obtain ⟨δ, hδU, hδ⟩ := (hf.and hs1).exists
      refine ⟨_, hδ.2, ?_⟩
      rw [one_mul]; exact hδU
  obtain ⟨x₀, hx₀H, hx₀U⟩ := hHU
  have hsub := subset_region hU hHc hHfree hx₀H hx₀U
  filter_upwards [hball] with s hs
  exact hsub (hHsec _ hs.1 (hsec' s hs.2))


/-- **The two sides of the chords at a walk vertex.**  At a walk vertex `(p, 0)` where the chords
of `F` attached there avoid the ray from its point in direction `τ` (which lies in the left
sector), and some chord of `F` is attached there, the part of the sector after the chords (the
side of the next walk edge, if `τ` turns counterclockwise from it) or before them (the side of the
previous walk edge) is a preconnected free set containing the ray. -/
theorem sub_sector (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {p : ℕ} (hp : p < M.W.n) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 (rayPt (sidePt M.W p 0) τ 1))
    (hnot : ∀ c ∈ F, SideAttach M.W c p 0 → ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∉ c)
    {c : Set Point} (hc : c ∈ F) (hA : SideAttach M.W c p 0) :
    ∃ r > 0,
      (0 < sideCross (M.W.vtx ((p + 1) % M.W.n) - M.W.vtx p) ((τ, 0) : Point) →
        SectorSide (freeIn M.D F)ᶜ
          (ball (M.W.vtx p) r ∩ {x | sideLeftOf (M.W.vtx p + ((-τ, 0) : Point)) (M.W.vtx p)
            (M.W.vtx ((p + 1) % M.W.n)) x})
          (M.W.vtx p + ((-τ, 0) : Point)) (M.W.vtx p) (M.W.vtx ((p + 1) % M.W.n)) 1 ∧
        ∀ s > 0, s < r → rayPt (M.W.vtx p) τ s ∈ ball (M.W.vtx p) r ∩
          {x | sideLeftOf (M.W.vtx p + ((-τ, 0) : Point)) (M.W.vtx p)
            (M.W.vtx ((p + 1) % M.W.n)) x}) ∧
      (0 < sideCross ((τ, 0) : Point) (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.W.vtx p) →
        SectorSide (freeIn M.D F)ᶜ
          (ball (M.W.vtx p) r ∩ {x | sideLeftOf (M.W.vtx ((p + M.W.n - 1) % M.W.n)) (M.W.vtx p)
            (M.W.vtx p + ((-τ, 0) : Point)) x})
          (M.W.vtx ((p + M.W.n - 1) % M.W.n)) (M.W.vtx p) (M.W.vtx p + ((-τ, 0) : Point)) 1 ∧
        ∀ s > 0, s < r → rayPt (M.W.vtx p) τ s ∈ ball (M.W.vtx p) r ∩
          {x | sideLeftOf (M.W.vtx ((p + M.W.n - 1) % M.W.n)) (M.W.vtx p)
            (M.W.vtx p + ((-τ, 0) : Point)) x}) := by
  obtain ⟨r, hr, hsf⟩ := sector_free hM hF hfin hp le_rfl one_pos
  have hne := hM.nd p hp
  have hn0 : 0 < M.W.n := by omega
  have hwv : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero _ _
  set v := M.W.vtx p with hv
  set a := M.W.vtx ((p + M.W.n - 1) % M.W.n) with ha
  set b := M.W.vtx ((p + 1) % M.W.n) with hb
  have hbv : b ≠ v := fun h => hne h.symm
  have hav : a ≠ v := by
    have := hM.nd _ (Nat.mod_lt (p + M.W.n - 1) hn0)
    rwa [prev_succ_mod hp] at this
  have hB0 : b - v ≠ 0 := sub_ne_zero.2 hbv
  have hA0 : a - v ≠ 0 := sub_ne_zero.2 hav
  have hsecv : ∀ x, sideLeft M.W p 0 x ↔ sideCcw (b - v) (x - v) (a - v) :=
    fun x => sideLeft_zero _ _ _
  have hdm0 : ((-τ, 0) : Point) ≠ 0 := by
    intro h; have := congrArg Prod.fst h; simp only [Prod.fst_zero] at this
    rcases hτ with rfl | rfl <;> norm_num at this
  have hvdm : v + ((-τ, 0) : Point) ≠ v := by
    intro h; apply hdm0; simpa using h
  -- the chord is along `-τ`, so `-τ` is in the sector
  obtain ⟨d, hd, -, -, hcmem⟩ := attached_opposite hM (hF hc) hA hτ (hnot c hc hA)
  obtain ⟨r₃, hr₃, hcl⟩ := hA.2.2.2.2
  set s₂ := min (d / 2) (r₃ / 2) with hs₂
  have hs₂0 : 0 < s₂ := lt_min (by linarith) (by linarith)
  have hx₂ : sideLeft M.W p 0 (rayPt (sidePt M.W p 0) (-τ) s₂) := by
    refine hcl _ (hcmem s₂ hs₂0 (lt_of_le_of_lt (min_le_left _ _) (by linarith))) ?_ ?_
    · intro h
      have := congrArg Prod.fst h
      simp only [rayPt_fst] at this
      rcases hτ with rfl | rfl <;> linarith
    · rw [dist_rayPt _ (by rcases hτ with rfl | rfl <;> norm_num) hs₂0.le]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hdm : sideCcw (b - v) ((-τ, 0) : Point) (a - v) := by
    have := (hsecv _).1 hx₂
    rwa [hwv, rayPt_sub, sideCcw_smul hs₂0] at this
  have hray : ∀ x ∈ ball v r, sideLeft M.W p 0 x → x ∈ ⋃₀ F →
      ∃ s' : ℝ, 0 ≤ s' ∧ x - v = s' • ((-τ, 0) : Point) := by
    rintro x hx hxl ⟨c', hc', hxc'⟩
    have hA'' := (hsf x (by rw [hwv]; exact hx) hxl).2 c' hc' hxc'
    obtain ⟨d', -, hpts, -, -⟩ := attached_opposite hM (hF hc') hA'' hτ (hnot c' hc' hA'')
    obtain ⟨s', hs'0, -, hxs'⟩ := hpts x hxc'
    exact ⟨s', hs'0, by rw [hxs', hwv, rayPt_sub]⟩
  have hsecr : ∀ s > 0, sideLeft M.W p 0 (rayPt v τ s) := by
    intro s hs
    have := (sideLeft_rayPt_iff _ p 0 τ one_pos hs).1 hsec
    rwa [hwv] at this
  refine ⟨r, hr, ?_, ?_⟩
  · intro h
    have hS : ∀ x ∈ ball v r, x ∈ (freeIn M.D F)ᶜ →
        ¬ sideLeftOf (v + ((-τ, 0) : Point)) v b x := by
      intro x hx hxF hxs
      rw [sideLeftOf_iff, add_sub_cancel_left] at hxs
      have hxl : sideLeft M.W p 0 x := (hsecv x).2 (Chazelle.Chain.sideCcw_sub_left hB0 hdm hxs)
      apply hxF
      refine ⟨(hsf x (by rw [hwv]; exact hx) hxl).1, fun hxU => ?_⟩
      obtain ⟨s', hs'0, hxs'⟩ := hray x hx hxl hxU
      rw [hxs'] at hxs
      refine Chazelle.Chain.sideCcw_not_ray_right hdm0 ?_ ?_ hxs
      · unfold sideCross; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      · unfold sideDot; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        nlinarith [mul_nonneg hs'0 (mul_self_nonneg τ)]
    obtain ⟨hS1, hHc, hoff⟩ := Chazelle.Chain.sideSector hvdm hbv hr hS
    refine ⟨⟨hS1, hHc, hoff⟩, fun s hs hsr => ⟨?_, ?_⟩⟩
    · rw [mem_ball, dist_rayPt _ hτ hs.le]; exact hsr
    · show sideLeftOf (v + ((-τ, 0) : Point)) v b (rayPt v τ s)
      rw [sideLeftOf_iff, add_sub_cancel_left, rayPt_sub, sideCcw_smul hs]
      exact ccw_half_left h
  · intro h
    have hS : ∀ x ∈ ball v r, x ∈ (freeIn M.D F)ᶜ →
        ¬ sideLeftOf a v (v + ((-τ, 0) : Point)) x := by
      intro x hx hxF hxs
      rw [sideLeftOf_iff, add_sub_cancel_left] at hxs
      have hxl : sideLeft M.W p 0 x :=
        (hsecv x).2 (Chazelle.Chain.sideCcw_sub_right hB0 hdm0 hA0 hdm hxs)
      apply hxF
      refine ⟨(hsf x (by rw [hwv]; exact hx) hxl).1, fun hxU => ?_⟩
      obtain ⟨s', hs'0, hxs'⟩ := hray x hx hxl hxU
      rw [hxs'] at hxs
      refine Chazelle.Chain.sideCcw_not_ray_left hdm0 ?_ ?_ hxs
      · unfold sideCross; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      · unfold sideDot; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        nlinarith [mul_nonneg hs'0 (mul_self_nonneg τ)]
    obtain ⟨hS1, hHc, hoff⟩ := Chazelle.Chain.sideSector hav hvdm hr hS
    refine ⟨⟨hS1, hHc, hoff⟩, fun s hs hsr => ⟨?_, ?_⟩⟩
    · rw [mem_ball, dist_rayPt _ hτ hs.le]; exact hsr
    · show sideLeftOf a v (v + ((-τ, 0) : Point)) (rayPt v τ s)
      rw [sideLeftOf_iff, add_sub_cancel_left, rayPt_sub, sideCcw_smul hs]
      exact ccw_half_right h

/-- **The ray leaving a cut vertex on the side of the next edge** starts in the region of the arc
beginning at the vertex (the chords attached there avoid the ray). -/
theorem ray_mem_region_after (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {b : ℝ} (harc : M.IsArc F U (p + 0) b) {c : Set Point} (hc : c ∈ F)
    (hA : SideAttach M.W c p 0) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 (rayPt (sidePt M.W p 0) τ 1))
    (hnot : ∀ c ∈ F, SideAttach M.W c p 0 → ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∉ c)
    (hcross : 0 < sideCross (M.W.vtx ((p + 1) % M.W.n) - M.W.vtx p) ((τ, 0) : Point)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∈ U := by
  have hM := walkAx_of_goodModel hGM
  obtain ⟨r, hr, hafter, -⟩ := sub_sector hM hFam.2.1 hFam.1 hp hτ hsec hnot hc hA
  obtain ⟨⟨hS1, hHc, hoff⟩, hrayH⟩ := hafter hcross
  have hne : F.Nonempty := ⟨c, hc⟩
  obtain ⟨-, -, hkb⟩ := WalkAx.arc_cuts hne harc
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hoff.and (WalkAx.eventually_after_start hkb)).and (Ioo_mem_nhdsGT one_pos)).exists
  have hf : M.Faces p s U := harc.2.2.2.2.2.2 p s hp hs3.1 hs3.2 (by
    rw [add_zero] at hs2 ⊢; exact hs2)
  obtain ⟨δ, hδU, hδ⟩ := (hf.and hs1).exists
  have hfree : ball (M.W.vtx p) r ∩ {x | sideLeftOf (M.W.vtx p + ((-τ, 0) : Point)) (M.W.vtx p)
      (M.W.vtx ((p + 1) % M.W.n)) x} ⊆ freeIn M.D F := fun x hx => by
    simpa using hS1 hx
  have hsub := subset_region hU hHc hfree hδ.2 (by rw [one_mul]; exact hδU)
  have hwv : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero _ _
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr] with s hs hsr
  rw [hwv]
  exact hsub (hrayH s hs hsr.2)

/-- **The ray leaving a cut vertex on the side of the previous edge** starts in the region of the
arc ending at the vertex. -/
theorem ray_mem_region_before (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    (hp1 : 1 ≤ p) {a : ℝ} (harc : M.IsArc F U a (p + 0)) {c : Set Point} (hc : c ∈ F)
    (hA : SideAttach M.W c p 0) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 (rayPt (sidePt M.W p 0) τ 1))
    (hnot : ∀ c ∈ F, SideAttach M.W c p 0 → ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∉ c)
    (hcross : 0 < sideCross ((τ, 0) : Point) (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.W.vtx p)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∈ U := by
  have hM := walkAx_of_goodModel hGM
  obtain ⟨r, hr, -, hbefore⟩ := sub_sector hM hFam.2.1 hFam.1 hp hτ hsec hnot hc hA
  obtain ⟨⟨hS1, hHc, hoff⟩, hrayH⟩ := hbefore hcross
  have hne : F.Nonempty := ⟨c, hc⟩
  obtain ⟨-, -, hak⟩ := WalkAx.arc_cuts hne harc
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hoff.and (sideInArc_before_end hak)).and (Ioo_mem_nhdsGT one_pos)).exists
  have hcast : ((p - 1 : ℕ) : ℝ) + (1 - s) = (p : ℝ) + 0 - s := by
    rw [Nat.cast_sub hp1]; push_cast; ring
  have hf : M.Faces (p - 1) (1 - s) U := harc.2.2.2.2.2.2 (p - 1) (1 - s) (by omega)
    (by linarith [hs3.2]) (by linarith [hs3.1]) (by rw [hcast]; exact hs2)
  obtain ⟨δ, hδU, hδ⟩ := (hf.and hs1).exists
  have hfree : ball (M.W.vtx p) r ∩ {x | sideLeftOf (M.W.vtx ((p + M.W.n - 1) % M.W.n))
      (M.W.vtx p) (M.W.vtx p + ((-τ, 0) : Point)) x} ⊆ freeIn M.D F := fun x hx => by
    simpa using hS1 hx
  have hδU' : Jordan.offset (M.W.vtx ((p + M.W.n - 1) % M.W.n)) (M.W.vtx p) (1 - s) (1 * δ) ∈ U := by
    rw [one_mul, prev_mod hp hp1]
    have e : M.W.vtx p = M.W.vtx ((p - 1 + 1) % M.W.n) := by
      rw [Nat.sub_add_cancel hp1, Nat.mod_eq_of_lt hp]
    rw [e]; exact hδU
  have hsub := subset_region hU hHc hfree hδ.1 hδU'
  have hwv : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero _ _
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr] with s hs hsr
  rw [hwv]
  exact hsub (hrayH s hs hsr.2)

end Leave

/-! ## Chain models -/

section ChainModel

/-- **Regions are closed under visibility, along a ray.**  If the open stretch `(0, T)` of a
horizontal ray is in the domain of a chain and its initial part is in the region `U` of an
augmented family, the whole stretch is in `U`. -/
theorem ray_subset_region (C : Chain) {F : Set (Set Point)} (hF : F ⊆ Merge.augChords C)
    {U : Set Point} (hU : U ∈ regionsIn C.dom F) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {T : ℝ} (hT : 0 < T) (hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ C.dom)
    (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U) :
    ∀ t, 0 < t → t < T → rayPt z σ t ∈ U := by
  have hUfree : U ⊆ freeIn C.dom F := Chazelle.Chain.regionsIn_subset hU
  have hIc : IsPreconnected (rayPt z σ '' Ioo 0 T) :=
    isPreconnected_Ioo.image _ (Chazelle.Visibility.continuous_rayPt z σ).continuousOn
  have hIfree : rayPt z σ '' Ioo 0 T ⊆ freeIn C.dom F := by
    rintro _ ⟨t₀, ht₀, rfl⟩
    refine ⟨hdom t₀ ht₀.1 ht₀.2, ?_⟩
    rintro ⟨c, hcF, hxc⟩
    obtain ⟨y, a, b, h, -, rfl, -, -⟩ := Merge.augChords_spec (hF hcF)
    obtain ⟨hy, ha, hb⟩ := hxc
    simp only [rayPt_fst, rayPt_snd] at hy ha hb
    -- every point of the ray before `t₀` is on the chord
    have hall : ∀ t, 0 < t → t ≤ t₀ → rayPt z σ t ∈ Visibility.hseg y a b := by
      intro t ht htt
      refine ⟨by simp [hy], ?_, ?_⟩ <;> simp only [rayPt_fst]
      · rcases hσ with rfl | rfl
        · by_contra hlt
          push Not at hlt
          apply h.left_not
          have := hdom (a - z.1) (by linarith) (by linarith [ht₀.2])
          simpa [rayPt, hy] using this
        · linarith
      · rcases hσ with rfl | rfl
        · linarith
        · by_contra hlt
          push Not at hlt
          apply h.right_not
          have := hdom (z.1 - b) (by linarith) (by linarith [ht₀.2])
          simpa [rayPt, hy] using this
    obtain ⟨t, htU, ht⟩ := (hini.and (Ioo_mem_nhdsGT ht₀.1)).exists
    exact (hUfree htU).2 ⟨_, hcF, hall t ht.1 ht.2.le⟩
  obtain ⟨t₁, ht₁U, ht₁⟩ := (hini.and (Ioo_mem_nhdsGT hT)).exists
  have hsub := subset_region hU hIc hIfree ⟨t₁, ht₁, rfl⟩ ht₁U
  intro t ht0 htT
  exact hsub ⟨t, ⟨ht0, htT⟩, rfl⟩

/-- The walk of a chain model lies outside its domain, so every arc does. -/
theorem arcSet_subset_compl_dom (C : Chain) (hP : C.P.Simple) (a b : ℝ) :
    (chainModel C).arcSet a b ⊆ C.domᶜ := by
  rintro x ⟨p, t, hp, ht0, ht1, -, rfl⟩
  exact (FactsChain.walkAx C hP).trace p hp t ht0 ht1

/-- **Local shooting in a chain model.**  If the initial part of the horizontal ray from `z`
(at a height not above the top of the chain) lies in the region `U` of an admissible family, then
the first-hit point of the ray lies on an arc of `U`. -/
theorem local_shoot (C : Chain) (hP : C.P.Simple) {Q : Polygon} {F : Set (Set Point)}
    (hFam : (chainModel C).ChordFamily Q F) {U : Set Point} (hU : U ∈ (chainModel C).regions F)
    {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U) :
    ∃ a b, (chainModel C).IsArc F U a b ∧
      rayPt z σ (C.hitParam z σ) ∈ (chainModel C).arcSet a b := by
  have hU' : U ∈ regionsIn C.dom F := hU
  have hUfree : U ⊆ freeIn C.dom F := Chazelle.Chain.regionsIn_subset hU'
  have hfree : Merge.FreeAt C z σ := hini.mono fun t ht => (hUfree ht).1
  obtain ⟨hT, hwD, hdom⟩ := Merge.hit_of_freeAt C hz hσ hfree
  set T := C.hitParam z σ with hTdef
  set w := rayPt z σ T with hw
  have hray := ray_subset_region C hFam.2.1 hU' hσ hT hdom hini
  have hnσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  have hback : ∀ s, rayPt w (-σ) s = rayPt z σ (T - s) := by
    intro s; apply point_ext <;> simp [rayPt, hw]; ring
  -- the height is inside the box
  have hzR : |z.2| < C.radius := by
    have := C.dom_subset_box (hdom (T / 2) (by linarith) (by linarith))
    simpa [rayPt] using this.2
  -- the hit point is on the chain or on a vertical side of the box
  have he : w ∈ C.set ∨ (|w.1| = C.radius ∧ |w.2| < C.radius) := by
    rcases (Merge.not_mem_dom_iff C (p := w) (by simpa [hw] using hz)).1 hwD with h | h
    · right
      refine ⟨le_antisymm ?_ ?_, by simpa [hw] using hzR⟩
      · by_contra hgt
        push Not at hgt
        set ε := min (T / 2) ((|w.1| - C.radius) / 2) with hε
        have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
        have hεT : ε < T := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hbox := C.dom_subset_box (hdom (T - ε) (by linarith) (by linarith))
        have h1 : |(rayPt z σ (T - ε)).1| < C.radius := hbox.1
        have h2 : |w.1| ≤ |(rayPt z σ (T - ε)).1| + ε := by
          have e : w.1 = (rayPt z σ (T - ε)).1 + σ * ε := by simp [hw, rayPt]; ring
          rw [e]
          refine (abs_add_le _ _).trans ?_
          rcases hσ with rfl | rfl <;> simp [abs_of_pos hε0]
        have h3 : ε ≤ (|w.1| - C.radius) / 2 := min_le_right _ _
        linarith
      · by_contra hlt
        push Not at hlt
        exact h ⟨hlt, by simpa [hw] using hzR⟩
    · exact Or.inl h
  -- a walk position at the hit point whose sector contains the backward ray
  have hT2 : (0 : ℝ) < T / 2 := by linarith
  have hee : w ≠ rayPt w (-σ) (T / 2) := by
    intro h
    have := congrArg Prod.fst h
    simp only [rayPt_fst] at this
    rcases hσ with rfl | rfl <;> linarith
  have hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp w (rayPt w (-σ) (T / 2)) s ∈ C.dom := by
    intro s hs
    have e : lerp w (rayPt w (-σ) (T / 2)) s = rayPt z σ (T - s * (T / 2)) := by
      apply point_ext <;> simp [lerp, rayPt, hw]; ring
    rw [e]
    exact hdom _ (by nlinarith [hs.2]) (by nlinarith [hs.1])
  obtain ⟨p, t, hp, ht, ht1, hpt, hl⟩ :=
    C.sideSees_chordEnd hP C.sideBeta hee (by simp [rayPt]) hopen he
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  have hpt' : sidePt (chainModel C).W p t = w := hpt
  have hsec : ∀ s > 0, sideLeft (chainModel C).W p t (rayPt (sidePt (chainModel C).W p t) (-σ) s) := by
    intro s hs
    have hl' : sideLeft (chainModel C).W p t (rayPt (sidePt (chainModel C).W p t) (-σ) (T / 2)) := by
      rw [hpt']; exact hl
    exact (sideLeft_rayPt_iff _ p t (-σ) hT2 hs).1 hl'
  have happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt (chainModel C).W p t) (-σ) s ∈ U := by
    filter_upwards [Ioo_mem_nhdsGT hT] with s hs
    rw [hpt', hback]
    exact hray _ (by linarith [hs.2]) (by linarith [hs.1])
  have hkey : 0 < (p : ℝ) + t := by
    by_contra hle
    push Not at hle
    have hp0 : p = 0 := by
      have : (p : ℝ) ≤ 0 := by linarith
      exact_mod_cast le_antisymm (by exact_mod_cast this) (Nat.zero_le p)
    have ht0 : t = 0 := by
      have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      linarith
    subst hp0 ht0
    have h0 : sidePt (chainModel C).W 0 0 = C.slitTop := by
      rw [Chazelle.Chain.sidePt_zero]; rfl
    have := congrArg Prod.snd (hpt.symm.trans h0)
    simp only [hw, rayPt_snd, Chain.slitTop] at this
    rw [this] at hzR
    have hR := C.radius_pos
    rw [abs_of_pos hR] at hzR
    exact lt_irrefl _ hzR
  obtain ⟨a, b, harc, hmem⟩ := hit_mem_arcSet hGM hFam hU hp ht ht1 hkey hnσ hsec happ
  rw [hpt'] at hmem
  exact ⟨a, b, harc, hmem⟩

/-- **The correctness of local shooting through the ray shooter.**  With `z` and `U` as in
`local_shoot`, the first hit of the ray on the union of the arcs of `U` is the first hit of the
chain (`C.hitParam z σ`).  The list `L` must contain every arc of `U`; it may contain any further
pairs (the arcs of other regions, for instance): arcs lie outside the domain, so they are never
hit before the first hit (**safety of extra candidates**). -/
theorem firstHit_arcs (C : Chain) (hP : C.P.Simple) {Q : Polygon} {F : Set (Set Point)}
    (hFam : (chainModel C).ChordFamily Q F) {U : Set Point} (hU : U ∈ (chainModel C).regions F)
    {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U) (L : List (ℝ × ℝ))
    (hL' : ∀ a b, (chainModel C).IsArc F U a b → (a, b) ∈ L) :
    FirstHit (⋃ ab ∈ L, (chainModel C).arcSet ab.1 ab.2) z σ (C.hitParam z σ) := by
  have hU' : U ∈ regionsIn C.dom F := hU
  have hfree : Merge.FreeAt C z σ :=
    hini.mono fun t ht => (Chazelle.Chain.regionsIn_subset hU' ht).1
  obtain ⟨a, b, harc, hmem⟩ := local_shoot C hP hFam hU hz hσ hini
  refine firstHit_of_compl_dom C hz hσ hfree ?_ ?_
  · intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨ab, -, hx⟩ := hx
    exact arcSet_subset_compl_dom C hP _ _ hx
  · simp only [mem_iUnion]
    exact ⟨(a, b), hL' a b harc, hmem⟩

end ChainModel

end Sweep

end

end Chazelle.Core
