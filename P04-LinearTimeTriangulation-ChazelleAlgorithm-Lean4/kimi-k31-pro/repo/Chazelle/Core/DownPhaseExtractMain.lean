module

public import Chazelle.Core.DownPhaseExtractCorr
public import Chazelle.Core.DownPhaseFrontier
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# WP-M (X, part 17): the extraction theorem

For a region `R` of a nonempty interior submap `S` of a simple polygon `Q` (`Ctx`), a chord gap
`g` of its host keys, the host chain `C = hostChain Q S R g` and a chord family `F₁` of
`chainModel C`, let `T = S ∪ kept R F₁` (the chain chords meeting `R` are added):
* (X1) `T` is a chord family of the interior model, and the added chords meet the domain only in
  `R` (`chordFamily_kept`, `kept_local`);
* every region `V ⊆ R` of `T` lies in a region `U` of `F₁` (`exists_chain_region`);
* (X2) its weight is at most the weight of `U` (`weight_kept`): each arc of `V` lies inside an
  arc of `R`, and the arc correspondence `arcCorr` transfers it (`ArcT.arcWt_le`);
* (X3) its degree is at most the degree of `U` plus the degree of `R` (`deg_kept`).
-/

namespace Chazelle.Core

namespace Extract

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn freeIn regionsIn)
open Chazelle.Visibility (hseg)
open DownHost
open ArcT (wrapK)

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point} {g : ℕ}
  {h3 : 3 ≤ nk (interiorModel Q) S R}

/-- **Cyclic betweenness in unwrapped form, wrapping case.** -/
theorem cyc_unwrap' {n l a b y : ℝ} (hl : 0 ≤ l ∧ l < n) (ha : 0 ≤ a ∧ a < n)
    (hb : 0 ≤ b ∧ b < n) (hy : 0 ≤ y ∧ y < n) (hab : unwrapK n l b < unwrapK n l a) :
    sideInArc a b y ↔ unwrapK n l y < unwrapK n l b ∨ unwrapK n l a < unwrapK n l y := by
  unfold unwrapK at *
  unfold sideInArc
  split_ifs at * <;> constructor <;> intro h <;> cyc_close2

/-- **An interval inside an arc, unwrapped.**  If `(a, b)` and `(l, r)` share a key `x₀` and
`(a, b)` contains neither `l` nor `r`, then, unwrapped from `l`, `(a, b)` is an increasing
sub-interval of `(l, r)`. -/
theorem unwrap_sub {n l r a b x₀ : ℝ} (hl : 0 ≤ l ∧ l < n) (hr : 0 ≤ r ∧ r < n)
    (ha : 0 ≤ a ∧ a < n) (hb : 0 ≤ b ∧ b < n) (hx : 0 ≤ x₀ ∧ x₀ < n)
    (hlr : l < unwrapK n l r) (hab : a ≠ b) (hxab : sideInArc a b x₀)
    (hxlr : sideInArc l r x₀) (hla : ¬ sideInArc a b l) (hra : ¬ sideInArc a b r) :
    unwrapK n l a < unwrapK n l b ∧ unwrapK n l b ≤ unwrapK n l r := by
  have e2 := (cyc_unwrap hl hl hr hx (by rwx [unwrapK_self])).1 hxlr
  rw [unwrapK_self] at e2
  have hbx := unwrapK_bounds hl hx
  have hbb := unwrapK_bounds hl hb
  have hba := unwrapK_bounds hl ha
  have hne : unwrapK n l a ≠ unwrapK n l b := fun e => hab (by
    rw [← wrapK_unwrapK (l := l) ha, ← wrapK_unwrapK (l := l) hb, e])
  rcases lt_or_gt_of_ne hne with h | h
  · have e1 := (cyc_unwrap hl ha hb hx h).1 hxab
    refine ⟨h, ?_⟩
    by_contra h'
    push Not at h'
    exact hra ((cyc_unwrap hl ha hb hr h).2 ⟨by linarith [e1.1, e1.2, e2.2], h'⟩)
  · exfalso
    have e1 := (cyc_unwrap' hl ha hb hx h).1 hxab
    have h1 : ¬ (unwrapK n l l < unwrapK n l b ∨ unwrapK n l a < unwrapK n l l) := fun h' =>
      hla ((cyc_unwrap' hl ha hb hl h).2 h')
    have h2 : ¬ (unwrapK n l r < unwrapK n l b ∨ unwrapK n l a < unwrapK n l r) := fun h' =>
      hra ((cyc_unwrap' hl ha hb hr h).2 h')
    rw [unwrapK_self] at h1
    push Not at h1 h2
    rcases e1 with e1 | e1 <;> linarith [e2.1, e2.2, h1.1, h1.2, h2.1, h2.2]

/-- A cut of `S` is a cut of any larger family. -/
theorem isCut_mono {M : Model} {F G : Set (Set Point)} (hFG : F ⊆ G) {x : ℝ} (h : M.IsCut F x) :
    M.IsCut G x := by
  obtain ⟨c, hc, p, t, hA, e⟩ := h
  exact ⟨c, hFG hc, p, t, hA, e⟩

/-- **(X2) for one arc.** -/
theorem arcWt_kept (X : Ctx Q S R) (hg : g < nk (interiorModel Q) S R)
    (hgc : ChordGap (interiorModel Q) S R g) {F₁ : Set (Set Point)}
    (hF₁ : F₁ ⊆ (chainModel (hostChain Q S R g h3)).Adm) (hfin₁ : F₁.Finite)
    {U : Set Point} (hU : U ∈ (chainModel (hostChain Q S R g h3)).regions F₁)
    {V : Set Point} (hVR : V ⊆ R) (hVU : V ⊆ U) {a b : ℝ}
    (harc : (interiorModel Q).IsArc (S ∪ kept R F₁) V a b) :
    (interiorModel Q).arcWt a b ≤ (chainModel (hostChain Q S R g h3)).weight F₁ U := by
  have hM := X.walkAx
  have hF := X.hFam.2.1
  have hfin := X.hFam.1
  have hTne : (S ∪ kept R F₁).Nonempty := X.hne.mono subset_union_left
  obtain ⟨p, hp, t, ht, hxab, hncT, hfV⟩ := WalkAx.exists_pos_in_arc hTne harc
  have hncS : ¬ (interiorModel Q).IsCut S (p + t) := fun h => hncT (isCut_mono subset_union_left h)
  obtain ⟨Y, hY, l, r, harcY, hxlr⟩ := hM.arc_around hF hfin X.hne hncS
  have hfR : (interiorModel Q).Faces p t R := hfV.mono (fun δ h => hVR h)
  have hfY : (interiorModel Q).Faces p t Y := harcY.2.2.2.2.2.2 p t hp ht.1 ht.2 hxlr
  have hYR : Y = R := WalkAx.faces_unique hY X.hR hfY hfR
  rw [hYR] at harcY
  obtain ⟨hcl, hcr, -⟩ := WalkAx.arc_cuts X.hne harcY
  have hla : ¬ sideInArc a b l := fun h =>
    harc.2.2.2.2.2.1 l h (isCut_mono subset_union_left hcl)
  have hra : ¬ sideInArc a b r := fun h =>
    harc.2.2.2.2.2.1 r h (isCut_mono subset_union_left hcr)
  obtain ⟨-, -, hab⟩ := WalkAx.arc_cuts hTne harc
  have ha : 0 ≤ a ∧ a < (interiorModel Q).W.n := ⟨harc.1, harc.2.1⟩
  have hb : 0 ≤ b ∧ b < (interiorModel Q).W.n := ⟨harc.2.2.1, harc.2.2.2.1⟩
  have hlb : 0 ≤ l ∧ l < (interiorModel Q).W.n := ⟨harcY.1, harcY.2.1⟩
  have hrb : 0 ≤ r ∧ r < (interiorModel Q).W.n := ⟨harcY.2.2.1, harcY.2.2.2.1⟩
  have hxb : 0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < (interiorModel Q).W.n := by
    refine ⟨add_nonneg (Nat.cast_nonneg p) ht.1.le, ?_⟩
    have : ((p + 1 : ℕ) : ℝ) ≤ ((interiorModel Q).W.n : ℝ) := by exact_mod_cast hp
    push_cast at this
    linarith [ht.2]
  have hn : (0 : ℝ) < (interiorModel Q).W.n := lt_of_le_of_lt hlb.1 hlb.2
  obtain ⟨i_l, d, hA⟩ := arc_keys hM hF hfin X.hne X.hR harcY
  have hl0 : ukey (interiorModel Q) S R i_l 0 = l := by rw [ukey_zero hA.hil, hA.hl]
  have hlrU : l < unwrapK (interiorModel Q).W.n l r := by
    rw [← hA.hud, ← hl0]
    exact ukey_mono hM hF hfin hA.hil hA.hd0 hA.hdN
  obtain ⟨h1, h2⟩ := unwrap_sub hlb hrb ha hb hxb hlrU hab hxab hxlr hla hra
  have hP : (hostChain Q S R g h3).P.Simple := hostPts_simple X.hQ X.hFam X.hne X.hR
  have corr := arcCorr X hg hgc harcY hA hF₁ hVU
  have hrU := (unwrapK_bounds hlb hrb).2
  refine ArcT.arcWt_le (walkAx_chainModel hP) hF₁ hfin₁ hU corr
    (aa := unwrapK (interiorModel Q).W.n l a) (bb := unwrapK (interiorModel Q).W.n l b)
    ?_ h1 ?_ ?_ ?_ harc.2.2.2.2.2.1 harc.2.2.2.2.2.2
  · rw [hl0]; exact (unwrapK_bounds hlb ha).1
  · rwx [hA.hud]
  · intro x hx0 hxn hx
    exact ⟨unwrapK (interiorModel Q).W.n l x, (cyc_unwrap hlb ha hb ⟨hx0, hxn⟩ h1).1 hx,
      wrapK_unwrapK ⟨hx0, hxn⟩⟩
  · intro xx hxx
    have hlo : l ≤ xx := le_trans (unwrapK_bounds hlb ha).1 hxx.1.le
    have hhi : xx < l + (interiorModel Q).W.n := by linarith [hxx.2]
    have hxx0 : 0 ≤ xx := le_trans hlb.1 hlo
    have hxx2 : xx < 2 * ((interiorModel Q).W.n : ℝ) := by linarith [hlb.2]
    have hy : 0 ≤ wrapK (interiorModel Q).W.n xx ∧
        wrapK (interiorModel Q).W.n xx < (interiorModel Q).W.n :=
      ⟨ArcT.wrapK_nonneg hxx0 hxx2, ArcT.wrapK_lt hn hxx0 hxx2⟩
    have e := unwrapK_wrapK hlb.1 hn hlo hhi
    refine (cyc_unwrap hlb ha hb hy h1).2 ?_
    rwx [e]

/-- **(X2) The weight transfer.** -/
theorem weight_kept (X : Ctx Q S R) (hg : g < nk (interiorModel Q) S R)
    (hgc : ChordGap (interiorModel Q) S R g) {F₁ : Set (Set Point)}
    (hF₁ : F₁ ⊆ (chainModel (hostChain Q S R g h3)).Adm) (hfin₁ : F₁.Finite)
    {U : Set Point} (hU : U ∈ (chainModel (hostChain Q S R g h3)).regions F₁)
    {V : Set Point} (hVR : V ⊆ R) (hVU : V ⊆ U) :
    (interiorModel Q).weight (S ∪ kept R F₁) V ≤
      (chainModel (hostChain Q S R g h3)).weight F₁ U := by
  apply csSup_le'
  rintro _ ⟨⟨a, b⟩, hab, rfl⟩
  exact arcWt_kept X hg hgc hF₁ hfin₁ hU hVR hVU hab

/-- **(X1, localization)** The kept chords are admissible and meet the domain only in `R`. -/
theorem kept_local (X : Ctx Q S R) (hg : g < nk (interiorModel Q) S R)
    (hgc : ChordGap (interiorModel Q) S R g) {F₁ : Set (Set Point)}
    (hF₁ : F₁ ⊆ (chainModel (hostChain Q S R g h3)).Adm) {c : Set Point}
    (hc : c ∈ kept R F₁) :
    c ∈ (interiorModel Q).Adm ∧ c ∩ (interiorModel Q).D ⊆ R :=
  kept_adm X.hQ X.hFam X.hne X.hR hg hgc (hF₁ hc.1) hc.2

/-- The walk vertices of the interior walk are vertices of `Q`. -/
theorem interiorWalk_vtx {k : ℕ} (hk : k < (interiorWalk Q).n) :
    ∃ h, h < Q.n ∧ (interiorWalk Q).vtx k = Q.vtx h := by
  have hWn : (interiorWalk Q).n = Q.n := by
    unfold interiorWalk; split_ifs
    · rfl
    · exact FactsInterior.rev_n Q
  have hk'  := hWn ▸ hk
  unfold interiorWalk
  split_ifs
  · exact ⟨k, hk', rfl⟩
  · exact ⟨Q.n - 1 - k, by omega, FactsInterior.rev_vtx Q k hk'⟩

/-- **Host points lie at vertex heights of `Q`.** -/
theorem host_height (X : Ctx Q S R) {i : ℕ} (hi : i < nk (interiorModel Q) S R) :
    ∃ h, h < Q.n ∧ (hostPt (interiorModel Q).W (hk (interiorModel Q) S R i)).2 = (Q.vtx h).2 := by
  have hM := X.walkAx
  rcases hk_mem hM X.hFam.2.1 X.hFam.1 hi with ⟨c, hc, -, p, t, hA, e⟩ | ⟨k, hk, e, -⟩
  · rw [e, hostPt_eq _ hA.2.1 hA.2.2.1]
    obtain ⟨h, hh, a, b, rfl⟩ := X.hFam.2.2 c hc
    exact ⟨h, hh, hA.2.2.2.1.1⟩
  · rw [e, show ((k : ℕ) : ℝ) = (k : ℝ) + 0 by ring, hostPt_eq _ le_rfl one_pos,
      Chazelle.Chain.sidePt_zero]
    obtain ⟨h, hh, e'⟩ := interiorWalk_vtx (Q := Q) hk
    exact ⟨h, hh, by rwr [← e']⟩

/-- **Every region of the extended family inside `R` lies in a region of `F₁`.** -/
theorem exists_chain_region (X : Ctx Q S R) {F₁ : Set (Set Point)} {V : Set Point}
    (hV : V ∈ (interiorModel Q).regions (S ∪ kept R F₁)) (hVR : V ⊆ R) :
    ∃ U ∈ (chainModel (hostChain Q S R g h3)).regions F₁, V ⊆ U := by
  obtain ⟨v, hv⟩ := Chazelle.Chain.regionsIn_nonempty hV
  have hdom : R ⊆ (hostChain Q S R g h3).dom := region_sub_dom X.hQ X.hFam X.hne X.hR
  have hfree : V ⊆ freeIn (hostChain Q S R g h3).dom F₁ := by
    intro z hz
    refine ⟨hdom (hVR hz), fun ⟨c, hc, hzc⟩ => ?_⟩
    exact (Chazelle.Chain.regionsIn_subset hV hz).2 ⟨c, Or.inr ⟨hc, z, hzc, hVR hz⟩, hzc⟩
  exact ⟨_, ⟨v, hfree hv, rfl⟩,
    (Chazelle.Chain.regionsIn_isPreconnected hV).subset_connectedComponentIn hv hfree⟩

/-- **(X3) The degree bound.** -/
theorem deg_kept (X : Ctx Q S R) (hg : g < nk (interiorModel Q) S R)
    (hgc : ChordGap (interiorModel Q) S R g) {F₁ : Set (Set Point)}
    (hF₁ : F₁ ⊆ (chainModel (hostChain Q S R g h3)).Adm) (hfin₁ : F₁.Finite)
    {U V : Set Point} (hVR : V ⊆ R) (hVU : V ⊆ U) :
    (interiorModel Q).deg (S ∪ kept R F₁) V ≤
      (chainModel (hostChain Q S R g h3)).deg F₁ U + (interiorModel Q).deg S R := by
  unfold Model.deg
  have hdom : R ⊆ (hostChain Q S R g h3).dom := region_sub_dom X.hQ X.hFam X.hne X.hR
  have hsub : {c | c ∈ S ∪ kept R F₁ ∧ TouchesIn (interiorModel Q).D c V} ⊆
      {c | c ∈ F₁ ∧ TouchesIn (chainModel (hostChain Q S R g h3)).D c U} ∪
        {c | c ∈ S ∧ TouchesIn (interiorModel Q).D c R} := by
    rintro c ⟨hc | hc, z, hz, hzV⟩
    · exact Or.inr ⟨hc, z, hz, closure_mono hVR hzV⟩
    · have hzR := (kept_local X hg hgc hF₁ hc).2 hz
      exact Or.inl ⟨hc.1, z, ⟨hz.1, hdom hzR⟩, closure_mono hVU hzV⟩
  refine le_trans (Set.ncard_le_ncard hsub ?_) (Set.ncard_union_le _ _)
  exact (hfin₁.subset fun c hc => hc.1).union (X.hFam.1.subset fun c hc => hc.1)

end

end Extract

end Chazelle.Core
