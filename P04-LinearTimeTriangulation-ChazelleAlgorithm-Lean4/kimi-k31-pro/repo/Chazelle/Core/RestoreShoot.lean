module

public import Chazelle.Core.SweepLocal
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics

/-!
# WP-E, Lemma 3.2 part 2: local shooting in any good model

The search of Lemma 3.2 shoots horizontal rays from points of the walk of a good model `M` (a
chain model or the interior model of `Q`) into a region `R` of a chord family, and must know
that the first hit of the ray on the (sub)arcs of `R` is the first point where the ray leaves the
domain.  The sweep (`Sweep.local_shoot`) proves this for chain models; here it is proved for any
good model, from the walk axioms.

* `hit_mem_arcSet'`: `Sweep.hit_mem_arcSet` without the restriction to positive keys (the walk
  vertex `0` of an interior model can be hit), with `arc_of_attach_before'` and
  `arc_of_faces_after'` for the wrap-around at key `0`.
* `adm_hchord`, `hchord_adm`: the admissible chords of a good model are its horizontal chords
  (below the top of the chain, for a chain model).
* `ray_open_subset`: a ray whose initial part is in a region stays in it while it is in the
  domain (`Sweep.ray_subset_region` for any good model).
* `exit_exists`: a ray that starts in the domain and reaches a point outside has a first exit.
* `chordOf`, `mem_chordOf`, `attach_start`, `attach_end`: the segment from the origin to the exit
  and its attachments.
* `local_exit`: **local shooting** — the exit point lies on an arc of the region, and the segment
  is an admissible chord inside the region.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft sideLeftOf sideCcw
  sideCross sideDot freeIn regionsIn sideLeft_edge sideLeft_zero sideLeft_not_self sideKey_inj
  sideCcw_smul IsHChordIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)
open Chazelle.Jordan (offset SectorSide)
open Sweep

section Wrap

variable {M : Model}

/-- Keys just before the key `p` (read on the previous walk edge, wrapping around at `p = 0`)
are inside every cyclic interval ending at `p`. -/
theorem before_eventually {n p : ℕ} (hp : p < n) {l : ℝ} (hl0 : 0 ≤ l) (hln : l < n)
    (hlp : l ≠ (p : ℝ) + 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), sideInArc l ((p : ℝ) + 0) ((((p + n - 1) % n : ℕ) : ℝ) + (1 - s)) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · have hq : (0 + n - 1) % n = n - 1 := by
      rwo [Nat.mod_eq_of_lt (by omega)]
    rw [hq]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rws [Nat.cast_sub (by omega)]
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < n - l by linarith)]
      with s hs hs'
    have hs0  := hs
    unfold sideInArc
    simp only [Nat.cast_zero, add_zero]
    rw [ite_eq_right (by linarith), hcast]
    left; linarith [hs'.2]
  · have hq := prev_mod hp (show 1 ≤ p by omega)
    rw [hq]
    have hcast : ((p - 1 : ℕ) : ℝ) + (1 - 0) = (p : ℝ) + 0 := by
      rw [Nat.cast_sub (by omega)]; pcr
    filter_upwards [sideInArc_before_end hlp] with s hs
    have e : ((p - 1 : ℕ) : ℝ) + (1 - s) = (p : ℝ) + 0 - s := by
      rw [Nat.cast_sub (by omega)]; pcr
    rwx [e]

/-- **A cut walk vertex whose previous positions face `U`** ends an arc of `U` (any key; the
previous walk edge of vertex `0` is the last one). -/
theorem arc_of_attach_before' (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {p : ℕ} (hA : SideAttach M.W c p 0)
    {U : Set Point} (hU : U ∈ M.regions F)
    (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces ((p + M.W.n - 1) % M.W.n) (1 - s) U) :
    ∃ a b, M.IsArc F U a b ∧ (sideInArc a b ((p : ℝ) + 0) ∨ (p : ℝ) + 0 = a ∨ (p : ℝ) + 0 = b) := by
  obtain ⟨-, V', l, r, -, hV', -, -, harcV, -⟩ := hM.attach_face hF hfin hc hA
  have hne : F.Nonempty := ⟨c, hc⟩
  obtain ⟨-, -, hlk⟩ := WalkAx.arc_cuts hne harcV
  have hn : 0 < M.W.n := by have := hA.1; omega
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hf.and (before_eventually hA.1 harcV.1 harcV.2.1 hlk)).and (Ioo_mem_nhdsGT one_pos)).exists
  have hq : (p + M.W.n - 1) % M.W.n < M.W.n := Nat.mod_lt _ hn
  have hfV' := harcV.2.2.2.2.2.2 _ (1 - s) hq (by linarith [hs3.2]) (by linarith [hs3.1]) hs2
  have hVV  := WalkAx.faces_unique hV' hU hfV' hs1
  subst hVV
  exact ⟨l, _, harcV, Or.inr (Or.inr rfl)⟩

/-- A non-cut walk vertex lies in the closure of an arc whose interior contains the keys just
after it (any key: for the empty family, the arc of the whole walk starts at key `0`). -/
theorem arc_after_key (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {p : ℕ} (hcut : ¬ M.IsCut F (p : ℝ)) :
    ∃ X ∈ M.regions F, ∃ l r, M.IsArc F X l r ∧ (sideInArc l r p ∨ (p : ℝ) = l) ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), sideInArc l r (p + s) := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨⟨U, hU, a, b, harc⟩, -⟩ := arcCover M Q ∅ hGM hFam
    rcases harc.2.2.2.2.1 with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, rfl, rfl⟩
    · exact absurd hc (Set.notMem_empty c)
    refine ⟨U, hU, 0, 0, harc, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos p with rfl | hp0
      · right; simp
      · left; unfold sideInArc; rw [ite_eq_right (lt_irrefl _)]; left; exact_mod_cast hp0
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs0 : (0 : ℝ) < s := hs
      unfold sideInArc; rw [ite_eq_right (lt_irrefl _)]; left; positivity
  · obtain ⟨X, hX, l, r, harc, hin⟩ :=
      (walkAx_of_goodModel hGM).arc_around hFam.2.1 hFam.1 hne hcut
    exact ⟨X, hX, l, r, harc, Or.inl hin, sideInArc_eventually_add hin⟩

/-- **A non-cut walk vertex whose next positions face `U`** is on an arc of `U` (any key). -/
theorem arc_of_faces_after' (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    (hcut : ¬ M.IsCut F p) (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U) :
    ∃ a b, M.IsArc F U a b ∧ (sideInArc a b ((p : ℝ) + 0) ∨ (p : ℝ) + 0 = a ∨ (p : ℝ) + 0 = b) := by
  obtain ⟨X, hX, l, r, harc, hin, hev⟩ := arc_after_key hGM hFam hcut
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ := ((hf.and hev).and (Ioo_mem_nhdsGT one_pos)).exists
  have hfX  := harc.2.2.2.2.2.2 p s hp hs3.1 hs3.2 hs2
  have hXU  := WalkAx.faces_unique hX hU hfX hs1
  subst hXU
  refine ⟨l, r, harc, ?_⟩
  rcases hin with h | h
  · left; rwa [add_zero]
  · right; left; rwx [add_zero]

/-- `Sweep.arc_of_attach_after` with the key in the closed arc. -/
theorem arc_of_attach_afterK (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {p : ℕ} (hA : SideAttach M.W c p 0)
    {U : Set Point} (hU : U ∈ M.regions F) (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U) :
    ∃ a b, M.IsArc F U a b ∧ (sideInArc a b ((p : ℝ) + 0) ∨ (p : ℝ) + 0 = a ∨ (p : ℝ) + 0 = b) := by
  obtain ⟨U', V', l, r, hU', -, -, harcU, -, -⟩ := hM.attach_face hF hfin hc hA
  have hne : F.Nonempty := ⟨c, hc⟩
  obtain ⟨-, -, hkr⟩ := WalkAx.arc_cuts hne harcU
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hf.and (WalkAx.eventually_after_start hkr)).and (Ioo_mem_nhdsGT one_pos)).exists
  have hin : sideInArc ((p : ℝ) + 0) r (p + s) := by rw [add_zero] at hs2 ⊢; exact hs2
  have hfU' := harcU.2.2.2.2.2.2 p s hA.1 hs3.1 hs3.2 hin
  have hUU  := WalkAx.faces_unique hU' hU hfU' hs1
  subst hUU
  exact ⟨_, r, harcU, Or.inr (Or.inl rfl)⟩

/-- `Sweep.arc_of_faces_edge` with the key in the arc. -/
theorem arc_of_faces_edgeK (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut F (p + t)) (hf : M.Faces p t U) :
    ∃ a b, M.IsArc F U a b ∧ (sideInArc a b ((p : ℝ) + t) ∨ (p : ℝ) + t = a ∨ (p : ℝ) + t = b) := by
  have hpos : (0 : ℝ) < p + t := by have := ht.1; positivity
  obtain ⟨X, hX, l, r, harc, hin⟩ := WalkEmbed.exists_arc_around hGM hFam hpos hcut
  have hfX  := harc.2.2.2.2.2.2 p t hp ht.1 ht.2 hin
  have hXU  := WalkAx.faces_unique hX hU hfX hf
  subst hXU
  exact ⟨l, r, harc, Or.inl hin⟩

end Wrap

/-! ## The hit point lies on an arc of the region (any key) -/

section Hit

variable {M : Model}

/-- **The first-hit point lies on an arc of the region**, for any good model and any key
(`Sweep.hit_mem_arcSet` without `0 < p + t`). -/
theorem hit_key_arc (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : ∀ s > 0, sideLeft M.W p t (rayPt (sidePt M.W p t) τ s))
    (happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p t) τ s ∈ U) :
    ∃ a b, M.IsArc F U a b ∧
      (sideInArc a b ((p : ℝ) + t) ∨ (p : ℝ) + t = a ∨ (p : ℝ) + t = b) := by
  have hM := walkAx_of_goodModel hGM
  have hF  := hFam.2.1
  have hfin  := hFam.1
  obtain ⟨r, hr, hsf⟩ := sector_free hM hF hfin hp ht ht1
  have hUfree  := Chazelle.Chain.regionsIn_subset hU
  have hne := hM.nd p hp
  have hball : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p t) τ s ∈ ball (sidePt M.W p t) r := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr] with s hs hs'
    rw [mem_ball, dist_rayPt _ hτ (le_of_lt hs)]
    exact hs'.2
  obtain ⟨s₁, ⟨hs₁U, hs₁B⟩, hs₁pos⟩ := ((happ.and hball).and self_mem_nhdsWithin).exists
  have hs₁pos'  := hs₁pos
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
      · rwx [dist_rayPt _ (by rcases hτ with rfl | rfl <;> norm_num) hs₂0.le]
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
    have hn0 : 0 < M.W.n := by omega
    have hwv : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero _ _
    set v := M.W.vtx p with hv
    set a := M.W.vtx ((p + M.W.n - 1) % M.W.n) with ha
    set b := M.W.vtx ((p + 1) % M.W.n) with hb
    have hbv : b ≠ v := fun h => hne h.symm
    have hav : a ≠ v := by
      have := hM.nd _ (Nat.mod_lt (p + M.W.n - 1) hn0)
      rwa [prev_succ_mod hp] at this
    have hB0  := sub_ne_zero.2 hbv
    have hA0  := sub_ne_zero.2 hav
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
      have hk0 : 0 < k := by rwnl [hk]
      set s := min d k / 2 with hs
      have hmin  := lt_min hd hk0
      have hs0 : 0 < s := by rwli [hs]
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
          rwring [show (M.W.vtx ((p + 1) % M.W.n)).2 = b.2 from rfl, hb2]
      rwx [e]
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
      exact ⟨(hsf x (by rwx [hwv]) hxl).1, hxF⟩
    have hray : ∀ x ∈ ball v r, sideLeft M.W p 0 x → x ∈ ⋃₀ F →
        ∃ s' : ℝ, 0 ≤ s' ∧ x - v = s' • ((-τ, 0) : Point) := by
      rintro x hx hxl ⟨c', hc', hxc'⟩
      have hA'' := (hsf x (by rwx [hwv]) hxl).2 c' hc' hxc'
      obtain ⟨d', -, hpts, -, -⟩ := attached_opposite hM (hF hc') hA'' hτ (havoid c' hc')
      obtain ⟨s', hs'0, -, hxs'⟩ := hpts x hxc'
      refine ⟨s', hs'0, ?_⟩
      rw [hxs', hwv, rayPt_sub]
    have hs₁B' : rayPt v τ s₁ ∈ ball v r := by rwx [← hwv]
    have hs₁U' : rayPt v τ s₁ ∈ U := by rwx [← hwv]
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
        have hxs  := (hsecv x).2 (Chazelle.Chain.sideCcw_sub_left hB0 hdm (hHsec x hx))
        refine hchord x hx.1 hxs ?_
        intro hxF
        obtain ⟨s', hs'0, hxs'⟩ := hray x hx.1 hxs hxF
        have h5 := hHsec x hx
        rw [hxs'] at h5
        refine Chazelle.Chain.sideCcw_not_ray_right hdm0 ?_ ?_ h5
        · unfold sideCross; sir only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
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
      exact arc_of_attach_afterK hM hF hfin hcF hA' hU hf
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
        have hxs  := (hsecv x).2 (Chazelle.Chain.sideCcw_sub_right hB0 hdm0 hA0 hdm (hHsec x hx))
        refine hchord x hx.1 hxs ?_
        intro hxF
        obtain ⟨s', hs'0, hxs'⟩ := hray x hx.1 hxs hxF
        have h5 := hHsec x hx
        rw [hxs'] at h5
        refine Chazelle.Chain.sideCcw_not_ray_left hdm0 ?_ ?_ h5
        · unfold sideCross; sir only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        · unfold sideDot; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
          nlinarith [mul_nonneg hs'0 (mul_self_nonneg τ)]
      have hs₁H : rayPt v τ s₁ ∈ ball v r ∩ {x | sideLeftOf a v (v + ((-τ, 0) : Point)) x} := by
        refine ⟨hs₁B', ?_⟩
        show sideLeftOf a v (v + ((-τ, 0) : Point)) (rayPt v τ s₁)
        rw [sideLeftOf_iff, add_sub_cancel_left, rayPt_sub, sideCcw_smul hs₁pos']
        exact ccw_half_right h
      have hHU := subset_region hU hHc hHfree hs₁H hs₁U'
      have hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces ((p + M.W.n - 1) % M.W.n) (1 - s) U := by
        filter_upwards [hoff] with s hs
        filter_upwards [hs] with δ hδ
        have := hHU hδ.1
        rw [one_mul] at this
        show Jordan.offset (M.W.vtx ((p + M.W.n - 1) % M.W.n))
          (M.W.vtx (((p + M.W.n - 1) % M.W.n + 1) % M.W.n)) (1 - s) δ ∈ U
        rw [prev_succ_mod hp]
        exact this
      exact arc_of_attach_before' hM hF hfin hcF hA' hU hf
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
      exact arc_of_faces_edgeK hGM hFam hU hp ht' hcut hf
    · -- at a walk vertex
      subst ht0
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
        refine ⟨by rwx [← hwv], ?_⟩
        have := hsec s₁ hs₁pos'
        rw [hwv] at this
        exact (sideLeft_zero _ _ _).1 this
      have hHU := subset_region hU hHc hHfree hs₁H (by rwx [← hwv])
      have hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U := by
        filter_upwards [hoff] with s hs
        filter_upwards [hs] with δ hδ
        have := hHU hδ.2
        rwa [one_mul] at this
      exact arc_of_faces_after' hGM hFam hU hp (by simpa using hcut) hf

/-- **The first-hit point lies on an arc of the region**, for any good model and any key. -/
theorem hit_mem_arcSet' (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : ∀ s > 0, sideLeft M.W p t (rayPt (sidePt M.W p t) τ s))
    (happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p t) τ s ∈ U) :
    ∃ a b, M.IsArc F U a b ∧ sidePt M.W p t ∈ M.arcSet a b := by
  obtain ⟨a, b, h1, h2⟩ := hit_key_arc hGM hFam hU hp ht ht1 hτ hsec happ
  exact ⟨a, b, h1, mem_arcSet_of_key hp ht ht1.le h2⟩

end Hit

/-! ## Rays in a good model -/

section Ray

variable {M : Model}

/-- The admissible chords of a good model are horizontal chords of its domain. -/
theorem adm_hchord (hGM : GoodModel M) {c : Set Point} (hc : c ∈ M.Adm) :
    ∃ y a b, IsHChordIn M.D y a b ∧ c = Visibility.hseg y a b := by
  rcases hGM with ⟨C, -, rfl⟩ | ⟨Q, -, rfl⟩
  · obtain ⟨y, a, b, h, -, rfl, -, -⟩ := Merge.augChords_spec hc
    exact ⟨y, a, b, h, rfl⟩
  · obtain ⟨y, a, b, h, rfl⟩ := hc
    exact ⟨y, a, b, h, rfl⟩

/-- A horizontal chord of the domain of a good model is admissible (for a chain model, if it is
not above the top of the chain). -/
theorem hchord_adm (hGM : GoodModel M) {y a b : ℝ} (h : IsHChordIn M.D y a b)
    (htop : ∀ C : Chain, M = chainModel C → y ≤ C.top.2) : Visibility.hseg y a b ∈ M.Adm := by
  rcases hGM with ⟨C, -, rfl⟩ | ⟨Q, -, rfl⟩
  · exact ⟨y, a, b, h, htop C rfl, rfl⟩
  · exact ⟨y, a, b, h, rfl⟩

/-- **Regions are closed under visibility, along a ray** (any good model): if the open stretch
`(0, T)` of a horizontal ray is in the domain and its initial part is in the region `U` of an
admissible family, the whole stretch is in `U`. -/
theorem ray_open_subset (hGM : GoodModel M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    {U : Set Point} (hU : U ∈ regionsIn M.D F) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {T : ℝ} (hT : 0 < T) (hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ M.D)
    (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U) :
    ∀ t, 0 < t → t < T → rayPt z σ t ∈ U := by
  have hUfree  := Chazelle.Chain.regionsIn_subset hU
  have hIc : IsPreconnected (rayPt z σ '' Ioo 0 T) :=
    isPreconnected_Ioo.image _ (Chazelle.Visibility.continuous_rayPt z σ).continuousOn
  have hIfree : rayPt z σ '' Ioo 0 T ⊆ freeIn M.D F := by
    rintro _ ⟨t₀, ht₀, rfl⟩
    refine ⟨hdom t₀ ht₀.1 ht₀.2, ?_⟩
    rintro ⟨c, hcF, hxc⟩
    obtain ⟨y, a, b, h, rfl⟩ := adm_hchord hGM (hF hcF)
    obtain ⟨hy, ha, hb⟩ := hxc
    simp only [rayPt_fst, rayPt_snd] at hy ha hb
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

/-- **The first exit of a ray**: a ray starting in an open set `D` and reaching a point outside
leaves `D` at a first parameter `T`. -/
theorem exit_exists {D : Set Point} (hD : IsOpen D) {z : Point} {σ : ℝ}
    (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ D) {t₁ : ℝ} (ht₁ : 0 < t₁)
    (hout : rayPt z σ t₁ ∉ D) :
    ∃ T, 0 < T ∧ T ≤ t₁ ∧ rayPt z σ T ∉ D ∧ ∀ t, 0 < t → t < T → rayPt z σ t ∈ D := by
  set S := {t : ℝ | 0 < t ∧ rayPt z σ t ∉ D} with hS
  have hne : S.Nonempty := ⟨t₁, ht₁, hout⟩
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1.le⟩
  obtain ⟨ε, hε, hεD⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hini)
  have hTε : ε ≤ sInf S := by
    refine le_csInf hne fun t ht => ?_
    by_contra h
    push Not at h
    exact ht.2 (hεD (by rwx [Real.dist_eq, sub_zero, abs_of_pos ht.1]) ht.1)
  have hTt  := csInf_le hbdd ⟨ht₁, hout⟩
  have hbelow : ∀ t, 0 < t → t < sInf S → rayPt z σ t ∈ D := fun t ht htT => by
    by_contra h
    exact absurd (csInf_le hbdd ⟨ht, h⟩) (not_le.2 htT)
  refine ⟨sInf S, by linarith, hTt, fun hTD => ?_, hbelow⟩
  have hc  := Chazelle.Visibility.continuous_rayPt z σ
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hD.preimage hc) (sInf S) hTD
  obtain ⟨s, hsS, hs⟩ := exists_lt_of_csInf_lt hne (show sInf S < sInf S + δ by linarith)
  have hTs  := csInf_le hbdd hsS
  exact hsS.2 (hball (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith))

/-- The horizontal segment from `z` to the point of the ray in direction `σ` at parameter `T`. -/
noncomputable def chordOf (z : Point) (σ T : ℝ) : Set Point :=
  Visibility.hseg z.2 (min z.1 (z.1 + σ * T)) (max z.1 (z.1 + σ * T))

/-- The points of `chordOf z σ T` are the ray points up to `T`. -/
theorem mem_chordOf {z : Point} {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 ≤ T) {x : Point} :
    x ∈ chordOf z σ T ↔ ∃ s, 0 ≤ s ∧ s ≤ T ∧ x = rayPt z σ s := by
  unfold chordOf Visibility.hseg
  simp only [mem_ofPred_eq]
  rcases hσ with rfl | rfl
  · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    constructor
    · rintro ⟨hy, h1, h2⟩
      exact ⟨x.1 - z.1, by linarith, by linarith, point_ext (by simp) (by simp [hy])⟩
    · rintro ⟨s, hs0, hsT, rfl⟩
      simp only [rayPt_fst, rayPt_snd]
      exact ⟨trivial, by linarith, by linarith⟩
  · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    constructor
    · rintro ⟨hy, h1, h2⟩
      exact ⟨z.1 - x.1, by linarith, by linarith, point_ext (by simp) (by simp [hy])⟩
    · rintro ⟨s, hs0, hsT, rfl⟩
      simp only [rayPt_fst, rayPt_snd]
      exact ⟨trivial, by linarith, by linarith⟩

theorem rayPt_zero' (z : Point) (σ : ℝ) : rayPt z σ 0 = z := point_ext (by simp) (by simp)

/-- The ray back from the point at parameter `T`. -/
theorem rayPt_back (z : Point) (σ T s : ℝ) : rayPt (rayPt z σ T) (-σ) s = rayPt z σ (T - s) :=
  point_ext (by sir) (by simp)

/-- **The chord is attached at its origin** when the ray leaves the origin's position into its
left sector. -/
theorem attach_start {W : Polygon} {p : ℕ} {t : ℝ} (hp : p < W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T)
    (hsec : sideLeft W p t (rayPt (sidePt W p t) σ 1)) :
    SideAttach W (chordOf (sidePt W p t) σ T) p t := by
  refine ⟨hp, ht0, ht1, (mem_chordOf hσ hT.le).2 ⟨0, le_rfl, hT.le, (rayPt_zero' _ _).symm⟩,
    1, one_pos, fun x hx hxz _ => ?_⟩
  obtain ⟨s, hs0, -, rfl⟩ := (mem_chordOf hσ hT.le).1 hx
  have hs : 0 < s := by
    rcases hs0.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd (rayPt_zero' _ _) hxz
  exact (sideLeft_rayPt_iff W p t σ one_pos hs).1 hsec

/-- **The chord is attached at its far end** when the ray back from it enters the left sector of
the far end's position. -/
theorem attach_end {W : Polygon} {p : ℕ} {t : ℝ} (hp : p < W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {z : Point} {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T)
    (hw : sidePt W p t = rayPt z σ T) (hsec : sideLeft W p t (rayPt (sidePt W p t) (-σ) 1)) :
    SideAttach W (chordOf z σ T) p t := by
  refine ⟨hp, ht0, ht1, by rw [hw]; exact (mem_chordOf hσ hT.le).2 ⟨T, hT.le, le_rfl, rfl⟩,
    1, one_pos, fun x hx hxz _ => ?_⟩
  obtain ⟨s, -, hsT, rfl⟩ := (mem_chordOf hσ hT.le).1 hx
  have hs : s < T := by
    rcases hsT.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd hw.symm hxz
  have e : rayPt z σ s = rayPt (sidePt W p t) (-σ) (T - s) := by rw [hw, rayPt_back]; congr 1; ring
  rw [e]
  exact (sideLeft_rayPt_iff W p t (-σ) one_pos (by linarith)).1 hsec

/-- A point of the chord off the domain is one of its ends, when its open part is in the
domain. -/
theorem chordOf_end {D : Set Point} {z : Point} {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 ≤ T)
    (hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ D) {x : Point} (hx : x ∈ chordOf z σ T)
    (hxD : x ∉ D) : x = z ∨ x = rayPt z σ T := by
  obtain ⟨s, hs0, hsT, rfl⟩ := (mem_chordOf hσ hT).1 hx
  rcases hs0.lt_or_eq with h0 | h0
  · rcases hsT.lt_or_eq with h1 | h1
    · exact absurd (hdom s h0 h1) hxD
    · right; rw [h1]
  · left; rw [← h0, rayPt_zero']

/-- **Local shooting in a good model.**  Let the ray from the point `z` off the domain start in
the region `U` of a chord family and reach a point off the domain at parameter `t₁`.  Then it
leaves the domain first at some `T ≤ t₁`; the open stretch before `T` is in `U`; the segment
`chordOf z σ T` is an admissible chord (for a chain model, if `z` is not above the top); it is
attached at a walk position of its far end; and the far end lies on an arc of `U`. -/
theorem local_exit (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hzD : z ∉ M.D) (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U)
    {t₁ : ℝ} (ht₁ : 0 < t₁) (hout : rayPt z σ t₁ ∉ M.D)
    (htop : ∀ C : Chain, M = chainModel C → z.2 ≤ C.top.2) :
    ∃ T, 0 < T ∧ T ≤ t₁ ∧ rayPt z σ T ∉ M.D ∧ (∀ t, 0 < t → t < T → rayPt z σ t ∈ U) ∧
      chordOf z σ T ∈ M.Adm ∧
      (∃ p t, SideAttach M.W (chordOf z σ T) p t ∧ sidePt M.W p t = rayPt z σ T) ∧
      ∃ a b, M.IsArc F U a b ∧ rayPt z σ T ∈ M.arcSet a b := by
  have hM := walkAx_of_goodModel hGM
  have hUfree : U ⊆ freeIn M.D F := Chazelle.Chain.regionsIn_subset hU
  have hiniD : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ M.D := hini.mono fun t h => (hUfree h).1
  obtain ⟨T, hT, hTt, hTD, hdom⟩ := exit_exists hM.isOpen hiniD ht₁ hout
  have hray := ray_open_subset hGM hFam.2.1 hU hσ hT hdom hini
  -- the segment is a horizontal chord of the domain
  have hH : IsHChordIn M.D z.2 (min z.1 (z.1 + σ * T)) (max z.1 (z.1 + σ * T)) := by
    rcases hσ with rfl | rfl
    · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      refine ⟨by linarith, by simpa using hzD, by simpa [rayPt] using hTD, fun x h1 h2 => ?_⟩
      have := hdom (x - z.1) (by linarith) (by linarith)
      simpa [rayPt] using this
    · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      refine ⟨by linarith, by simpa [rayPt] using hTD, by simpa using hzD, fun x h1 h2 => ?_⟩
      have := hdom (z.1 - x) (by linarith) (by linarith)
      simpa [rayPt] using this
  have hadm : chordOf z σ T ∈ M.Adm := hchord_adm hGM hH htop
  -- a walk position at the far end
  obtain ⟨a, b, hab, -, -, -, ⟨⟨pa, ta, hAa, hpa⟩, -⟩, ⟨⟨pb, tb, hAb, hpb⟩, -⟩⟩ := hM.ends _ hadm
  have hend : ∃ p t, SideAttach M.W (chordOf z σ T) p t ∧ sidePt M.W p t = rayPt z σ T := by
    have ca := chordOf_end hσ hT.le hdom hAa.2.2.2.1 (hM.trace pa hAa.1 ta hAa.2.1 hAa.2.2.1.le)
    have cb := chordOf_end hσ hT.le hdom hAb.2.2.2.1 (hM.trace pb hAb.1 tb hAb.2.1 hAb.2.2.1.le)
    rw [hpa] at ca
    rw [hpb] at cb
    rcases ca with ca | ca
    · rcases cb with cb | cb
      · exact absurd (ca.trans cb.symm) hab
      · exact ⟨pb, tb, hAb, hpb.trans cb⟩
    · exact ⟨pa, ta, hAa, hpa.trans ca⟩
  obtain ⟨p, t, hA, hpt⟩ := hend
  refine ⟨T, hT, hTt, hTD, hray, hadm, ⟨p, t, hA, hpt⟩, ?_⟩
  -- the far end lies on an arc of `U`
  have hnσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨r, hr, hcl⟩ := hA.2.2.2.2
  set s₀ := min T r / 2 with hs₀
  have hmin : 0 < min T r := lt_min hT hr
  have hs₀0 : 0 < s₀ := by rwli [hs₀]
  have hs₀T : s₀ < T := by rw [hs₀]; linarith [min_le_left T r]
  have hs₀r : s₀ < r := by rw [hs₀]; linarith [min_le_right T r]
  have hx₀ : sideLeft M.W p t (rayPt (sidePt M.W p t) (-σ) s₀) := by
    rw [hpt, rayPt_back]
    refine hcl _ ((mem_chordOf hσ hT.le).2 ⟨T - s₀, by linarith, by linarith, rfl⟩) ?_ ?_
    · intro h
      rw [hpt] at h
      have := congrArg Prod.fst h
      simp only [rayPt_fst] at this
      rcases hσ with rfl | rfl <;> linarith
    · rwx [hpt, ← rayPt_back, dist_rayPt _ hnσ hs₀0.le]
  have hsec : ∀ s > 0, sideLeft M.W p t (rayPt (sidePt M.W p t) (-σ) s) := fun s hs =>
    (sideLeft_rayPt_iff M.W p t (-σ) hs₀0 hs).1 hx₀
  have happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p t) (-σ) s ∈ U := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hT] with s hs hsT
    have hs0 : (0 : ℝ) < s := hs
    rw [hpt, rayPt_back]
    exact hray _ (by linarith [hsT.2]) (by linarith)
  obtain ⟨a', b', harc, hmem⟩ :=
    hit_mem_arcSet' hGM hFam hU hA.1 hA.2.1 hA.2.2.1 hnσ hsec happ
  rw [hpt] at hmem
  exact ⟨a', b', harc, hmem⟩

end Ray

end

end Restore

end Chazelle.Core
