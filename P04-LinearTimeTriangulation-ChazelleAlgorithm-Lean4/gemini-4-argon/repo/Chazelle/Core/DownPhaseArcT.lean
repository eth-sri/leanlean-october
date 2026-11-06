module

public import Chazelle.Core.DownPhaseDropWt

/-!
# WP-M (X, part 1): arc transfer between two models

The weight bounds of the extraction (X2) and of the transition (T3) compare an interval of the
walk of one model (`M₂`, the interior model) with an interval of the walk of another (`M₁`, a
chain model), along a stretch where the two walks run over the same points with the same left
sides.

`ArcCorr` packages the correspondence: a strictly increasing key map `κ` from an unwrapped key
range `[lo, hi]` of `M₂` onto a key range of `M₁` such that
* vertex keys correspond to vertex keys;
* a cut of `F₁` at `κ x` is a cut of `F₂` at `x` (so the image of a cut-free interval is
  cut-free);
* facing `V` at `x` gives facing `U` at `κ x`;
* the walk edges of `M₁` in the image are counted.

**Main result** (`arcWt_le`): a cut-free interval of `M₂` inside the range facing `V` has at most
the weight of the region `U` of `F₁`.  All interior walk edges met by it map injectively to
counted edges of one arc of `U`.
-/

namespace Chazelle.Core

namespace ArcT

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sideInArc)
open BoxT (edgesIn arcWt_eq' edgesIn_finite arcWt_le_weight)

/-- Wrap an unwrapped key of `[0, 2n)` into `[0, n)`. -/
noncomputable def wrapK (n x : ℝ) : ℝ := if x < n then x else x - n

/-- The key is not a vertex key. -/
def NonVtx (x : ℝ) : Prop := ∀ k : ℕ, x ≠ k

/-- **A key correspondence** between the unwrapped key range `[lo, hi]` of `M₂` and a key range of
`M₁`. -/
structure ArcCorr (M₁ M₂ : Model) (F₁ F₂ : Set (Set Point)) (U V : Set Point) (lo hi : ℝ)
    (κ : ℝ → ℝ) : Prop where
  lo_nonneg : 0 ≤ lo
  lo_lt : lo < M₂.W.n
  hi_le : hi ≤ lo + M₂.W.n
  mono : StrictMonoOn κ (Icc lo hi)
  range : ∀ x ∈ Icc lo hi, 0 ≤ κ x ∧ κ x < M₁.W.n
  onto : ∀ y, κ lo ≤ y → y ≤ κ hi → ∃ x ∈ Icc lo hi, κ x = y
  vtx : ∀ x ∈ Ioo lo hi, NonVtx x → NonVtx (κ x)
  vtx' : ∀ x ∈ Ioo lo hi, ¬ NonVtx x → ¬ NonVtx (κ x)
  cut : ∀ x ∈ Ioo lo hi, M₁.IsCut F₁ (κ x) → M₂.IsCut F₂ (wrapK M₂.W.n x)
  faces : ∀ x ∈ Ioo lo hi, NonVtx x →
    M₂.Faces ⌊wrapK M₂.W.n x⌋₊ (wrapK M₂.W.n x - ⌊wrapK M₂.W.n x⌋₊) V →
      M₁.Faces ⌊κ x⌋₊ (κ x - ⌊κ x⌋₊) U
  counted : ∀ x ∈ Ioo lo hi, NonVtx x → M₁.counted ⌊κ x⌋₊

/-! ## Floors -/

theorem floor_lt_of_nonVtx {x : ℝ} (h0 : 0 ≤ x) (hx : NonVtx x) :
    (⌊x⌋₊ : ℝ) < x ∧ x < ⌊x⌋₊ + 1 := by
  refine ⟨lt_of_le_of_ne (Nat.floor_le h0) (fun e => hx _ e.symm), Nat.lt_floor_add_one x⟩

theorem wrapK_nonneg {n x : ℝ} (hx : 0 ≤ x) (_hx' : x < 2 * n) : 0 ≤ wrapK n x := by
  unfold wrapK; split_ifs with h <;> linarith

theorem wrapK_lt {n x : ℝ} (_hn : 0 < n) (_hx : 0 ≤ x) (hx' : x < 2 * n) : wrapK n x < n := by
  unfold wrapK; split_ifs with h <;> linarith

theorem nonVtx_wrapK {n : ℕ} {x : ℝ} (hx : NonVtx x) : NonVtx (wrapK n x) := by
  intro k e
  unfold wrapK at e
  split_ifs at e
  · exact hx k e
  · exact hx (k + n) (by push_cast; linarith)

theorem nonVtx_of_wrapK {n : ℕ} {x : ℝ} (hx : NonVtx (wrapK n x)) : NonVtx x := by
  intro k e
  unfold wrapK at hx
  split_ifs at hx with h
  · exact hx k e
  · have hk : n ≤ k := by
      have : (n : ℝ) ≤ k := by rw [← e]; exact not_lt.1 h
      exact_mod_cast this
    exact hx (k - n) (by rw [e]; push_cast [hk]; ring)

namespace ArcCorr

variable {M₁ M₂ : Model} {F₁ F₂ : Set (Set Point)} {U V : Set Point} {lo hi : ℝ} {κ : ℝ → ℝ}
variable (h : ArcCorr M₁ M₂ F₁ F₂ U V lo hi κ)
include h

/-- Keys in one walk edge of `M₁` come from keys in one walk edge of `M₂`. -/
theorem floor_eq {x x' : ℝ} (hx : x ∈ Ioo lo hi) (hx' : x' ∈ Ioo lo hi) (hv : NonVtx x)
    (hv' : NonVtx x') (he : ⌊κ x⌋₊ = ⌊κ x'⌋₊) : ⌊x⌋₊ = ⌊x'⌋₊ := by
  have h0 : ∀ z ∈ Ioo lo hi, 0 ≤ z := fun z hz => le_trans h.lo_nonneg hz.1.le
  -- the general statement for `x ≤ x'`
  have key : ∀ z z', z ∈ Ioo lo hi → z' ∈ Ioo lo hi → NonVtx z → NonVtx z' → z ≤ z' →
      ⌊κ z⌋₊ = ⌊κ z'⌋₊ → ⌊z⌋₊ = ⌊z'⌋₊ := by
    intro z z' hz hz' hvz hvz' hle hf
    by_contra hne
    have hlt : ⌊z⌋₊ < ⌊z'⌋₊ := lt_of_le_of_ne (Nat.floor_le_floor hle) hne
    set k : ℕ := ⌊z⌋₊ + 1
    have hz1 := floor_lt_of_nonVtx (h0 z hz) hvz
    have hz2 := floor_lt_of_nonVtx (h0 z' hz') hvz'
    have hk1 : z < k := by push_cast [k]; exact hz1.2
    have hk2 : (k : ℝ) < z' := by
      have : (k : ℝ) ≤ ⌊z'⌋₊ := by exact_mod_cast hlt
      linarith [hz2.1]
    have hkI : (k : ℝ) ∈ Ioo lo hi := ⟨lt_trans hz.1 hk1, lt_trans hk2 hz'.2⟩
    have hkv : ¬ NonVtx (k : ℝ) := fun hn => hn k rfl
    have hkk := h.vtx' _ hkI hkv
    simp only [NonVtx, not_forall, not_not] at hkk
    obtain ⟨K, hK⟩ := hkk
    have hIcc : ∀ w ∈ Ioo lo hi, w ∈ Icc lo hi := fun w hw => ⟨hw.1.le, hw.2.le⟩
    have m1 : κ z < κ k := h.mono (hIcc z hz) (hIcc _ hkI) hk1
    have m2 : κ k < κ z' := h.mono (hIcc _ hkI) (hIcc z' hz') hk2
    have hy0 : 0 ≤ κ z := (h.range z (hIcc z hz)).1
    have f1 : (⌊κ z⌋₊ : ℝ) + 1 ≤ K := by
      have : ⌊κ z⌋₊ < K := by
        rwa [Nat.floor_lt hy0, ← hK]
      exact_mod_cast this
    have f2 : (K : ℝ) ≤ ⌊κ z'⌋₊ := by
      have : K ≤ ⌊κ z'⌋₊ := Nat.le_floor (by rw [← hK]; exact m2.le)
      exact_mod_cast this
    rw [hf] at f1
    linarith
  rcases le_total x x' with hle | hle
  · exact key x x' hx hx' hv hv' hle he
  · exact (key x' x hx' hx hv' hv hle he.symm).symm

/-- A cut-free interval inside the range has a cut-free image. -/
theorem image_free {a b : ℝ} (hlo : lo ≤ a) (hab : a < b) (hhi : b ≤ hi)
    (hfree : ∀ x ∈ Ioo a b, ¬ M₂.IsCut F₂ (wrapK M₂.W.n x)) :
    ∀ y ∈ Ioo (κ a) (κ b), ¬ M₁.IsCut F₁ y := by
  intro y hy hc
  have hIa : a ∈ Icc lo hi := ⟨hlo, le_trans hab.le hhi⟩
  have hIb : b ∈ Icc lo hi := ⟨le_trans hlo hab.le, hhi⟩
  have hlo' : κ lo ≤ κ a := h.mono.monotoneOn ⟨le_rfl, le_trans hlo hIa.2⟩ hIa hlo
  have hhi' : κ b ≤ κ hi := h.mono.monotoneOn hIb ⟨le_trans hIb.1 hIb.2, le_rfl⟩ hhi
  obtain ⟨x, hx, rfl⟩ := h.onto y (by linarith [hy.1]) (by linarith [hy.2])
  have hxa : a < x := by
    by_contra hxa; push Not at hxa
    have := h.mono.monotoneOn hx hIa hxa
    linarith [hy.1]
  have hxb : x < b := by
    by_contra hxb; push Not at hxb
    have := h.mono.monotoneOn hIb hx hxb
    linarith [hy.2]
  exact hfree x ⟨hxa, hxb⟩ (h.cut x ⟨lt_of_le_of_lt hlo hxa, lt_of_lt_of_le hxb hhi⟩ hc)

end ArcCorr

/-! ## A linear cut-free interval lies in the arc around one of its points -/

theorem linear_sub_arc {l r y₀ c d : ℝ} (hy₀ : sideInArc l r y₀) (hc : c < y₀) (hd : y₀ < d)
    (hl : ¬ (c < l ∧ l < d)) (hr : ¬ (c < r ∧ r < d)) :
    ∀ y, c < y → y < d → sideInArc l r y := by
  intro y hcy hyd
  unfold sideInArc at *
  split_ifs at * with hlr
  · constructor
    · by_contra h'; push Not at h'
      exact hl ⟨by linarith, by linarith⟩
    · by_contra h'; push Not at h'
      exact hr ⟨by linarith, by linarith⟩
  · rcases hy₀ with h1 | h1
    · left; by_contra h'; push Not at h'
      exact hl ⟨by linarith, by linarith⟩
    · right; by_contra h'; push Not at h'
      exact hr ⟨by linarith, by linarith⟩

/-! ## The arc transfer -/

variable {M₁ M₂ : Model} {F₁ F₂ : Set (Set Point)} {U V : Set Point} {lo hi : ℝ} {κ : ℝ → ℝ}

/-- **Arc transfer**: a cut-free interval `(a, b)` of `M₂` inside the range of a correspondence,
facing `V`, weighs at most the region `U` of `F₁`. -/
theorem arcWt_le (hM₁ : WalkAx M₁) (hF₁ : F₁ ⊆ M₁.Adm) (hfin₁ : F₁.Finite)
    (hU : U ∈ M₁.regions F₁) (h : ArcCorr M₁ M₂ F₁ F₂ U V lo hi κ)
    {a b aa bb : ℝ} (hlo : lo ≤ aa) (hab : aa < bb) (hhi : bb ≤ hi)
    (hin : ∀ x : ℝ, 0 ≤ x → x < M₂.W.n → sideInArc a b x →
      ∃ xx ∈ Ioo aa bb, wrapK M₂.W.n xx = x)
    (hout : ∀ xx ∈ Ioo aa bb, sideInArc a b (wrapK M₂.W.n xx))
    (hfree : ∀ x : ℝ, sideInArc a b x → ¬ M₂.IsCut F₂ x)
    (hfac : ∀ (p : ℕ) (t : ℝ), p < M₂.W.n → 0 < t → t < 1 → sideInArc a b (p + t) →
      M₂.Faces p t V) :
    M₂.arcWt a b ≤ M₁.weight F₁ U := by
  set n₂ := M₂.W.n
  have hn₂ : (0 : ℝ) < n₂ := lt_of_le_of_lt h.lo_nonneg h.lo_lt
  have hIcc : ∀ w, w ∈ Ioo aa bb → w ∈ Icc lo hi := fun w hw =>
    ⟨le_trans hlo hw.1.le, le_trans hw.2.le hhi⟩
  have hIoo : ∀ w, w ∈ Ioo aa bb → w ∈ Ioo lo hi := fun w hw =>
    ⟨lt_of_le_of_lt hlo hw.1, lt_of_lt_of_le hw.2 hhi⟩
  have hx0 : ∀ w, w ∈ Ioo aa bb → 0 ≤ w := fun w hw => le_trans h.lo_nonneg (hIcc w hw).1
  have hx2 : ∀ w, w ∈ Ioo aa bb → w < 2 * n₂ := fun w hw => by
    have := (hIcc w hw).2; have := h.hi_le; have := h.lo_lt; linarith
  -- the image interval is cut-free
  have hfreeI := h.image_free hlo hab hhi (fun x hx => hfree _ (hout x hx))
  -- the witness function
  classical
  set g : ℕ → ℝ := fun p =>
    if hp : ∃ xx ∈ Ioo aa bb, NonVtx xx ∧ ⌊wrapK n₂ xx⌋₊ = p then hp.choose else 0 with hg
  have hgspec : ∀ p ∈ edgesIn M₂ a b,
      g p ∈ Ioo aa bb ∧ NonVtx (g p) ∧ ⌊wrapK n₂ (g p)⌋₊ = p := by
    rintro p ⟨hp, -, t, ht0, ht1, hx⟩
    have hxn : (0 : ℝ) ≤ p + t := by positivity
    have hxlt : (p : ℝ) + t < n₂ := by
      have : (p : ℝ) + 1 ≤ n₂ := by exact_mod_cast hp
      linarith
    obtain ⟨xx, hxx, hw⟩ := hin _ hxn hxlt hx
    have hvw : NonVtx (wrapK n₂ xx) := by
      rw [hw]; intro k e
      have hk1 : (p : ℝ) < k := by linarith
      have hk2 : (k : ℝ) < ((p + 1 : ℕ) : ℝ) := by push_cast; linarith
      have := Nat.cast_lt.1 hk1; have := Nat.cast_lt.1 hk2; omega
    have hex : ∃ xx ∈ Ioo aa bb, NonVtx xx ∧ ⌊wrapK n₂ xx⌋₊ = p := by
      refine ⟨xx, hxx, nonVtx_of_wrapK hvw, ?_⟩
      rw [hw, Nat.floor_eq_iff hxn]
      exact ⟨by linarith, by linarith⟩
    have e : g p = hex.choose := by rw [hg]; simp only [dite_eq_left hex]
    rw [e]
    exact hex.choose_spec
  by_cases hE : (edgesIn M₂ a b).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hE
    rw [arcWt_eq', hE, Set.ncard_empty]; exact Nat.zero_le _
  obtain ⟨p₀, hp₀⟩ := hE
  obtain ⟨hx₀, hv₀, -⟩ := hgspec p₀ hp₀
  set y₀ := κ (g p₀)
  have hy₀r := h.range _ (hIcc _ hx₀)
  have hy₀v := h.vtx _ (hIoo _ hx₀) hv₀
  have hy₀c : ¬ M₁.IsCut F₁ y₀ := fun hc =>
    hfree _ (hout _ hx₀) (h.cut _ (hIoo _ hx₀) hc)
  have hIa : aa ∈ Icc lo hi := ⟨hlo, le_trans hab.le hhi⟩
  have hIb : bb ∈ Icc lo hi := ⟨le_trans hlo hab.le, hhi⟩
  have hya : κ aa < y₀ := h.mono hIa (hIcc _ hx₀) hx₀.1
  have hyb : y₀ < κ bb := h.mono (hIcc _ hx₀) hIb hx₀.2
  -- the arc of `U` around `y₀`
  obtain ⟨l, r, harc, hlr⟩ : ∃ l r, M₁.IsArc F₁ U l r ∧ ∀ y ∈ Ioo (κ aa) (κ bb), sideInArc l r y := by
    have hfac₀ : ∀ y ∈ Ioo (κ aa) (κ bb), NonVtx y → M₁.Faces ⌊y⌋₊ (y - ⌊y⌋₊) U := by
      intro y hy hvy
      obtain ⟨x, hx, rfl⟩ := h.onto y
        (le_trans (h.mono.monotoneOn ⟨le_rfl, le_trans hlo hIa.2⟩ hIa hlo) hy.1.le)
        (le_trans hy.2.le (h.mono.monotoneOn hIb ⟨le_trans hIb.1 hIb.2, le_rfl⟩ hhi))
      have hxa : aa < x := by
        by_contra hxa; push Not at hxa
        linarith [h.mono.monotoneOn hx hIa hxa, hy.1]
      have hxb : x < bb := by
        by_contra hxb; push Not at hxb
        linarith [h.mono.monotoneOn hIb hx hxb, hy.2]
      have hvx : NonVtx x := by
        intro k e; apply h.vtx' x (hIoo x ⟨hxa, hxb⟩) (fun hn => hn k e) hvy
      refine h.faces x (hIoo x ⟨hxa, hxb⟩) hvx ?_
      have hw0 := wrapK_nonneg (n := (n₂ : ℝ)) (hx0 x ⟨hxa, hxb⟩) (hx2 x ⟨hxa, hxb⟩)
      have hwl := wrapK_lt hn₂ (hx0 x ⟨hxa, hxb⟩) (hx2 x ⟨hxa, hxb⟩)
      have hwv := nonVtx_wrapK (n := n₂) hvx
      have hfl := floor_lt_of_nonVtx hw0 hwv
      apply hfac
      · have : (⌊wrapK n₂ x⌋₊ : ℝ) < n₂ := lt_of_le_of_lt (Nat.floor_le hw0) hwl
        exact_mod_cast this
      · linarith [hfl.1]
      · linarith [hfl.2]
      · rw [add_sub_cancel]; exact hout x ⟨hxa, hxb⟩
    by_cases hF : F₁.Nonempty
    · have hp := (Nat.floor_le hy₀r.1)
      have hy₀p := floor_lt_of_nonVtx hy₀r.1 hy₀v
      obtain ⟨X, hX, l, r, harcX, hin₀⟩ := hM₁.arc_around hF₁ hfin₁ hF hy₀c
      -- `X = U`: both are faced just at `y₀`
      have hXU : X = U := by
        have hpn : ⌊y₀⌋₊ < M₁.W.n := by
          have : (⌊y₀⌋₊ : ℝ) < M₁.W.n := lt_of_le_of_lt hp hy₀r.2
          exact_mod_cast this
        have ht0 : 0 < y₀ - ⌊y₀⌋₊ := by linarith [hy₀p.1]
        have ht1 : y₀ - ⌊y₀⌋₊ < 1 := by linarith [hy₀p.2]
        have hfX := harcX.2.2.2.2.2.2 _ _ hpn ht0 ht1 (by rwa [add_sub_cancel])
        exact WalkAx.faces_unique hX hU hfX (hfac₀ y₀ ⟨hya, hyb⟩ hy₀v)
      subst hXU
      refine ⟨l, r, harcX, ?_⟩
      have hl : ¬ (κ aa < l ∧ l < κ bb) := fun hl =>
        hfreeI l hl (by
          rcases harcX.2.2.2.2.1 with ⟨hl', -⟩ | ⟨hF', -⟩
          · exact hl'
          · exact absurd hF' hF.ne_empty)
      have hr : ¬ (κ aa < r ∧ r < κ bb) := fun hr =>
        hfreeI r hr (by
          rcases harcX.2.2.2.2.1 with ⟨-, hr', -⟩ | ⟨hF', -⟩
          · exact hr'
          · exact absurd hF' hF.ne_empty)
      intro y hy
      exact linear_sub_arc hin₀ hya hyb hl hr y hy.1 hy.2
    · -- the empty family: the pinned arc
      rw [Set.not_nonempty_iff_eq_empty] at hF
      have hn1 : (0 : ℝ) < M₁.W.n := lt_of_le_of_lt (h.range aa hIa).1 (h.range aa hIa).2
      refine ⟨0, 0, ⟨le_rfl, hn1, le_rfl, hn1, Or.inr ⟨hF, rfl, rfl⟩,
        fun x _ hc => by obtain ⟨c, hc, -⟩ := hc; rwa [hF] at hc, ?_⟩, ?_⟩
      · intro p t hp ht0 ht1 _
        obtain ⟨X, hX, hfX⟩ := hM₁.exists_faces_of_not_cut hF₁ hfin₁ hp ⟨ht0, ht1⟩
          (fun hc => by obtain ⟨c, hc, -⟩ := hc; rwa [hF] at hc)
        -- a single region
        have hXU : X = U := by
          obtain ⟨x, hx, rfl⟩ := hX
          obtain ⟨u, hu, rfl⟩ := hU
          have hfr : Chazelle.Chain.freeIn M₁.D F₁ = M₁.D := by
            rw [hF]; unfold Chazelle.Chain.freeIn; simp
          have hpre : IsPreconnected M₁.D := hM₁.preconn
          rw [hfr] at hx hu ⊢
          rw [connectedComponentIn_eq (hpre.subset_connectedComponentIn hx subset_rfl
            (show u ∈ M₁.D from hu) |> fun h' => by exact h')]
        rwa [← hXU]
      · intro y hy
        unfold sideInArc
        rw [ite_eq_right (lt_irrefl _)]
        left
        linarith [hy.1, (h.range aa hIa).1]
  -- the injection of edges
  rw [arcWt_eq']
  refine le_trans ?_ (arcWt_le_weight harc)
  rw [arcWt_eq']
  refine Set.ncard_le_ncard_of_injOn (fun p => ⌊κ (g p)⌋₊) ?_ ?_ (edgesIn_finite l r)
  · intro p hp
    obtain ⟨hx, hv, -⟩ := hgspec p hp
    have hr := h.range _ (hIcc _ hx)
    have hyv := h.vtx _ (hIoo _ hx) hv
    have hfl := floor_lt_of_nonVtx hr.1 hyv
    refine ⟨?_, h.counted _ (hIoo _ hx) hv, κ (g p) - ⌊κ (g p)⌋₊, by linarith [hfl.1],
      by linarith [hfl.2], ?_⟩
    · have : (⌊κ (g p)⌋₊ : ℝ) < M₁.W.n := lt_of_le_of_lt (Nat.floor_le hr.1) hr.2
      exact_mod_cast this
    · rw [add_sub_cancel]
      exact hlr _ ⟨h.mono hIa (hIcc _ hx) hx.1, h.mono (hIcc _ hx) hIb hx.2⟩
  · intro p hp q hq e
    obtain ⟨hx, hv, hpe⟩ := hgspec p hp
    obtain ⟨hy, hw, hqe⟩ := hgspec q hq
    have hfl := h.floor_eq (hIoo _ hx) (hIoo _ hy) hv hw e
    rw [← hpe, ← hqe]
    -- equal floors give equal wrapped floors
    have hx0' := hx0 _ hx; have hy0' := hx0 _ hy
    unfold wrapK
    by_cases h1 : g p < n₂ <;> by_cases h2 : g q < n₂
    · simp only [h1, h2, ↓reduceIte, hfl]
    · exfalso
      have a1 : ⌊g p⌋₊ < n₂ := by
        have := Nat.floor_lt hx0' |>.2 h1; exact_mod_cast this
      have a2 : n₂ ≤ ⌊g q⌋₊ := Nat.le_floor (by push Not at h2; exact_mod_cast h2)
      omega
    · exfalso
      have a1 : ⌊g q⌋₊ < n₂ := by
        have := Nat.floor_lt hy0' |>.2 h2; exact_mod_cast this
      have a2 : n₂ ≤ ⌊g p⌋₊ := Nat.le_floor (by push Not at h1; exact_mod_cast h1)
      omega
    · simp only [h1, h2, ↓reduceIte]
      push Not at h1 h2
      have e1 : ⌊g p - n₂⌋₊ = ⌊g p⌋₊ - n₂ := by
        simp
      have e2 : ⌊g q - n₂⌋₊ = ⌊g q⌋₊ - n₂ := by
        simp
      rw [e1, e2, hfl]

end

end ArcT

end Chazelle.Core
