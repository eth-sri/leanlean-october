module

public import Chazelle.Golf

public import Chazelle.Core.FuseMathCut

/-!
# The weight bound of the revised fusion (`FusionWeightSpec`, WP-D math)

The paper proof of `docs/design-merge-v2.md` §2.4, formalised.  Let `J` be a junction with
`J.P` simple and `SharedGeneric J`, let `S₁`, `S₂` be γ-semigranular admissible families of the
chain models of `C₁ = J.left` and `C₂ = J.right`, and let `S' = J.fusion S₁ S₂ ∪ glueChords J`.

1. **Pieces** (`side_pieces`).  The walk of `C` read from the copy of the shared vertex left
   towards `C₁` agrees with the walk of `C₁` read from the shared vertex, for the whole left tour
   (`WalkEmbed.tourV_left`), up to the boxes: the two boxes sit at the same offset
   (`WalkEmbed.left_box_eq`, case Sh), outside the stretch (case N), or only the box of `C₁` is
   inside (case G) — then the stretch is split at the copy of the top of `C₁`, which is a cut of
   `S'` (`topglue_cut`).  Each piece carries the stretch bound `γ` (`WalkEmbed.arcWt_le_of_stretch`
   with `cut_transfer`).  The same holds on the right.
2. **Covering** (`cover`): every key inside a counted walk edge of `C` lies in a piece.
3. **Assembly** (`arc_bound`): an arc of `S'` avoiding the inner copy of the shared vertex avoids
   every end key of a piece (copies of the shared vertex are cuts, `vkey_cut_or_inner`), so it
   meets at most `γ` counted edges (`WalkEmbed.arcWt_le_of_pieces`); an arc through the inner copy
   `k` is split at `k` (`Model.arcWt_le_split_vertex`), the cap chord bounds one part by one edge
   (`inner_cap_cut`), and the other part avoids all end keys (`inner_unique`).
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft)
open WalkEmbed

namespace FuseMath

variable (J : Merge.Junction)

/-- The end keys of the pieces: walk vertices of `C` at the shared vertex, and cut keys at walk
vertices. -/
def bdryK (S' : Set (Set Point)) : Set ℝ :=
  {x | ∃ k : ℕ, k < (chainModel J.whole).W.n ∧ x = k ∧
    ((chainModel J.whole).W.vtx k = sharedV J ∨ (chainModel J.whole).IsCut S' k)}

theorem radius_of_P {C' : Chain} (h : C'.P = J.P) : C'.radius = J.whole.radius := by
  unfold Chain.radius; rw [h]; rfl

/-- **The stretch bound along an agreement with a side walk.** -/
theorem agree_bound (hP : J.P.Simple) {C' : Chain} (hC'P : C'.P = J.P) {Q : Polygon}
    {Si S' : Set (Set Point)} (hSi : (chainModel C').ChordFamily Q Si) {γ : ℕ}
    (hsg : (chainModel C').Semigranular Si γ)
    (hend : ∀ c ∈ Si, (Merge.lend c ≠ J.shared → ∃ e ∈ S', Merge.lend c ∈ e ∧ e ⊆ c) ∧
      (Merge.rend c ≠ J.shared → ∃ e ∈ S', Merge.rend c ∈ e ∧ e ⊆ c))
    (hshared : J.sharedChords ⊆ S')
    {g₀ g₀' L₀ : ℕ} (hg₀ : g₀ < (chainModel J.whole).W.n) (hg₀' : g₀' < (chainModel C').W.n)
    (hLn : L₀ ≤ (chainModel J.whole).W.n) (hLn' : L₀ ≤ (chainModel C').W.n)
    (hA : Agree (chainModel J.whole).W (chainModel C').W g₀ g₀' L₀) (a b : ℝ)
    (hstr : ∀ x : ℝ, 0 ≤ x → x < (chainModel J.whole).W.n → sideInArc a b x →
      0 < off (chainModel J.whole).W.n g₀ x ∧ off (chainModel J.whole).W.n g₀ x < L₀)
    (hfree : ∀ x, sideInArc a b x → ¬ (chainModel J.whole).IsCut S' x) :
    (chainModel J.whole).arcWt a b ≤ γ := by
  have hP' : C'.P.Simple := hC'P ▸ hP
  have hR := radius_of_P J hC'P
  refine arcWt_le_of_stretch (Or.inl ⟨C', hP', rfl⟩) hSi hsg hg₀ hg₀' hLn hLn' ?_ ?_ hstr hfree
  · intro d hd hc
    Ξ' counted_iff_box _ (Nat.mod_lt _ (⋄)) at hc
    Ξ counted_iff_box _ (Nat.mod_lt _ (⋄))
    Ξ' mod_succ_mod at hc ⊢
    Ξ' hA d hd.le, hA (d + 1) hd at hc
    Ξ hR
    exact hc
  · intro d hd t ht ht1 hdt hc
    exact cut_transfer J hP hP' hSi.2.1 hend hshared hA hd ht ht1 hdt hc

/-- The offset from a later base of the stretch. -/
theorem off_shift {n g s p : ℕ} (hg : g < n) (hp : p < n) (hs : s ≤ dOf n g p) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    off n (((g + s) % n : ℕ) : ℝ) (p + t) = ((dOf n g p - s : ℕ) : ℝ) + t := by
  have hn : 0 < n := ⋄
  have hD := dOf_lt hn g p
  have e : ((g + s) % n + (dOf n g p - s)) % n = p := by
    Ξ Nat.mod_add_mod, show g + s + (dOf n g p - s) = g + dOf n g p by omega, add_dOf hg hp
  have := off_key (g := (g + s) % n) (Nat.mod_lt _ hn) (show dOf n g p - s < n by omega) ht ht1
  rwa [e] at this

/-- **The pieces of one side.**  Every key inside a walk edge of `C` strictly inside the stretch
of one side (read from the copy of the shared vertex left towards that side, of length `ℓ`, or
`ℓ + 7` when the box of `C` is inside it) lies strictly inside a piece. -/
theorem side_pieces (hP : J.P.Simple) (S₁ S₂ : Set (Set Point)) {C' : Chain} (hC'P : C'.P = J.P)
    {J₀ J₀' ℓ : ℕ} (hT : ∀ e, e ≤ ℓ → tourV J.whole J₀ e = tourV C' J₀' e)
    (hv0 : tourV J.whole J₀ 0 = sharedV J) (hvℓ : tourV J.whole J₀ ℓ = sharedV J)
    (hℓ' : ℓ ≤ 2 * C'.m) (hℓ : ℓ < 2 * J.whole.m)
    (hbox : 2 * J.whole.m - tpos J.whole J₀ < ℓ →
      2 * C'.m - tpos C' J₀' = 2 * J.whole.m - tpos J.whole J₀)
    {kt : ℕ} (hkt : kt ∈ topIdxs J) (hktm : kt ≤ J.whole.m) (hvert : J.whole.vertex kt = C'.top)
    {Q : Polygon} {Si : Set (Set Point)} (hSi : (chainModel C').ChordFamily Q Si) {γ : ℕ}
    (hsg : (chainModel C').Semigranular Si γ)
    (hend : ∀ c ∈ Si, (Merge.lend c ≠ J.shared →
        ∃ e ∈ J.fusion S₁ S₂ ∪ glueChords J, Merge.lend c ∈ e ∧ e ⊆ c) ∧
      (Merge.rend c ≠ J.shared → ∃ e ∈ J.fusion S₁ S₂ ∪ glueChords J, Merge.rend c ∈ e ∧ e ⊆ c))
    {p : ℕ} (hp : p < (chainModel J.whole).W.n) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hin : dOf (chainModel J.whole).W.n (6 + tpos J.whole J₀) p <
      (if 2 * J.whole.m - tpos J.whole J₀ < ℓ then ℓ + 7 else ℓ)) :
    ∃ g L, PieceOK (chainModel J.whole) (J.fusion S₁ S₂ ∪ glueChords J)
      (bdryK J (J.fusion S₁ S₂ ∪ glueChords J)) γ g L ∧
      0 < off (chainModel J.whole).W.n g (p + t) ∧ off (chainModel J.whole).W.n g (p + t) < L := by
  set C := J.whole with hC
  set W := (chainModel C).W with hW
  set W' := (chainModel C').W with hW'
  set S' := J.fusion S₁ S₂ ∪ glueChords J with hS'
  have hP' : C'.P.Simple := hC'P ▸ hP
  have hR := radius_of_P J hC'P
  have hn := cm_n C
  have hn' := cm_n C'
  have hshared : J.sharedChords ⊆ S' := fun c hc => Or.inl (Or.inr hc)
  set τ := tpos C J₀ with hτ
  set τ' := tpos C' J₀' with hτ'
  have hτlt := tpos_lt C J₀
  have hτ'lt := tpos_lt C' J₀'
  set g := 6 + τ with hg_def
  set g' := 6 + τ' with hg'_def
  have hg : g < W.n := by rw [hn]; omega
  have hg' : g' < W'.n := by rw [hn']; omega
  set s := 2 * C.m - τ with hs_def
  set s' := 2 * C'.m - τ' with hs'_def
  -- keys at the shared vertex are end keys
  have hK_v : ∀ k : ℕ, k < W.n → W.vtx k = sharedV J → (k : ℝ) ∈ bdryK J S' :=
    fun k hk hv => ⟨k, hk, rfl, Or.inl hv⟩
  have hK_c : ∀ k : ℕ, k < W.n → (chainModel C).IsCut S' k → (k : ℝ) ∈ bdryK J S' :=
    fun k hk hc => ⟨k, hk, rfl, Or.inr hc⟩
  have hstart : (g : ℝ) ∈ bdryK J S' := by
    refine hK_v g hg ?_
    have := walk_tour C J₀ 0 (⋄)
    Ξ' add_zero, Nat.mod_eq_of_lt hg at this
    Ξ this, hv0
  have hoffp : off W.n g (p + t) = dOf W.n g p + t := off_key' hg hp ht.le ht1
  by_cases hsl : s < ℓ
  · -- case Sh: the boxes at the same offset
    Ξ' ite_eq_left hsl at hin
    have hss : s = s' := (hbox hsl).symm
    have hA := agree_Sh hT hR.symm hℓ.le hℓ' hss hsl
    refine ⟨g, ℓ + 7, ⟨hg, by rw [hn]; omega, hstart, ?_, ?_⟩, ?_, ?_⟩
    · refine hK_v _ (Nat.mod_lt _ (⋄)) ?_
      have := walk_after C J₀ (ℓ - s) (⋄)
      rw [show 6 + τ + (2 * C.m - τ) + 7 + (ℓ - s) = g + (ℓ + 7) by omega,
        show 2 * C.m - τ + (ℓ - s) = ℓ by omega] at this
      Ξ this, hvℓ
    · exact agree_bound J hP hC'P hSi hsg hend hshared hg hg' (by rw [hn]; omega) (by rw [hn']; omega) hA
    · rw [hoffp]; positivity
    · Ξ hoffp
      have : (dOf W.n g p : ℝ) + 1 ≤ ℓ + 7 := by exact_mod_cast hin
      push_cast; linarith
  Ξ' ite_eq_right hsl at hin
  push Not at hsl
  -- the end key of the stretch
  have hend_key : (((g + ℓ) % W.n : ℕ) : ℝ) ∈ bdryK J S' := by
    refine hK_v _ (Nat.mod_lt _ (⋄)) ?_
    have := walk_tour C J₀ ℓ (⋄)
    Ξ this, hvℓ
  by_cases hsl' : ℓ ≤ s'
  · -- case N: no box inside the stretch
    have hA := agree_N hT hsl hsl'
    refine ⟨g, ℓ, ⟨hg, by rw [hn]; omega, hstart, hend_key, ?_⟩, ?_, ?_⟩
    · exact agree_bound J hP hC'P hSi hsg hend hshared hg hg' (by rw [hn]; omega) (by rw [hn']; omega) hA
    · rw [hoffp]; positivity
    · Ξ hoffp
      have : (dOf W.n g p : ℝ) + 1 ≤ ℓ := by exact_mod_cast hin
      linarith
  -- case G: only the box of the side chain is inside the stretch
  push Not at hsl'
  have hA1 := agree_G1 hT hsl hsl'
  have hA2 := agree_G2 hT hℓ' hsl hsl'
  have hs'1 : 1 ≤ s' := ⋄
  set k₀ := (g + s') % W.n with hk₀
  have hk₀n : k₀ < W.n := Nat.mod_lt _ (⋄)
  -- the corner at the split key is the slit corner of the side chain
  have hpt : W.vtx k₀ = C'.top := by
    Ξ hA1 s' le_rfl
    have := walk_box C' J₀' 0 (⋄)
    Ξ' add_zero at this
    exact this
  have hprev : sidePrev W k₀ 0 = C'.sideTour C'.sideBeta (2 * C'.m - 1) := by
    unfold sidePrev
    rw [ite_eq_left rfl, hk₀, mod_pred_mod (⋄) g hs'1, hA1 (s' - 1) (⋄),
      show g' + (s' - 1) = (2 * C'.m - 1) + 6 by omega, Nat.mod_eq_of_lt (by rw [hn']; omega)]
    exact C'.sideWalk_vtx_tour _ (⋄)
  have hnext : sideNext W k₀ = C'.sideTour C'.sideBeta 1 := by
    unfold sideNext
    Ξ hk₀, hA2 1 (⋄)
    rw [show (g' + s' + 7) % W'.n = 6 by
        rw [hn', show g' + s' + 7 = 6 + (2 * C'.m + 7) by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (⋄)],
      Nat.mod_eq_of_lt (show 6 + 1 < W'.n by rw [hn']; omega)]
    exact C'.sideWalk_vtx_tour _ (⋄)
  have hcut : (chainModel C).IsCut S' k₀ :=
    topglue_cut J hP S₁ S₂ hP' hkt hktm hvert hk₀n hprev hpt hnext
  have hk₀K : (k₀ : ℝ) ∈ bdryK J S' := hK_c _ hk₀n hcut
  by_cases hD : dOf W.n g p < s'
  · refine ⟨g, s', ⟨hg, by rw [hn]; omega, hstart, hk₀K, ?_⟩, ?_, ?_⟩
    · exact agree_bound J hP hC'P hSi hsg hend hshared hg hg' (by rw [hn]; omega) (by rw [hn']; omega) hA1
    · rw [hoffp]; positivity
    · Ξ hoffp
      have : (dOf W.n g p : ℝ) + 1 ≤ s' := by exact_mod_cast hD
      linarith
  · push Not at hD
    refine ⟨k₀, ℓ - s', ⟨hk₀n, by rw [hn]; omega, hk₀K, ?_, ?_⟩, ?_, ?_⟩
    · rw [hk₀, Nat.mod_add_mod, show g + s' + (ℓ - s') = g + ℓ by omega]; exact hend_key
    · exact agree_bound J hP hC'P hSi hsg hend hshared hk₀n (Nat.mod_lt _ (⋄)) (by rw [hn]; omega) (by rw [hn']; omega) hA2
    · rw [hk₀, off_shift hg hp hD ht.le ht1]; positivity
    · Ξ hk₀, off_shift hg hp hD ht.le ht1
      have h1 : dOf W.n g p - s' + 1 ≤ ℓ - s' := ⋄
      have : ((dOf W.n g p - s' : ℕ) : ℝ) + 1 ≤ ((ℓ - s' : ℕ) : ℝ) := by exact_mod_cast h1
      linarith

/-! ## Covering the walk of `C` by the two sides -/

theorem dOf_six {n τ i : ℕ} (hτ : τ + 7 ≤ n) (hi : i + 7 ≤ n) :
    dOf n (6 + τ) (6 + i) = if τ ≤ i then i - τ else i + n - τ := by
  unfold dOf
  split_ifs with h
  · rw [show 6 + i + n - (6 + τ) = (i - τ) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show i - τ < n by omega)]
  · rw [show 6 + i + n - (6 + τ) = i + n - τ by omega,
      Nat.mod_eq_of_lt (show i + n - τ < n by omega)]

/-- The arithmetic of the covering: every tour edge lies in the left or the right stretch. -/
theorem cover_arith {m₁ m₂ τ τ₂ i : ℕ} (h1 : 1 ≤ m₁) (h2 : 1 ≤ m₂) (hτ : τ < 2 * (m₁ + m₂))
    (hτ₂ : τ₂ = (τ + 2 * m₁) % (2 * (m₁ + m₂))) (hi : i < 2 * (m₁ + m₂)) :
    dOf (2 * (m₁ + m₂) + 7) (6 + τ) (6 + i) <
        (if 2 * (m₁ + m₂) - τ < 2 * m₁ then 2 * m₁ + 7 else 2 * m₁) ∨
      dOf (2 * (m₁ + m₂) + 7) (6 + τ₂) (6 + i) <
        (if 2 * (m₁ + m₂) - τ₂ < 2 * m₂ then 2 * m₂ + 7 else 2 * m₂) := by
  have hτ₂' : τ₂ = τ + 2 * m₁ ∨
      (2 * (m₁ + m₂) ≤ τ + 2 * m₁ ∧ τ₂ = τ + 2 * m₁ - 2 * (m₁ + m₂)) := by
    rcases lt_or_ge (τ + 2 * m₁) (2 * (m₁ + m₂)) with h | h
    · left; Ξ hτ₂, Nat.mod_eq_of_lt h
    · right; refine ⟨h, ?_⟩; rw [hτ₂, Nat.mod_eq_sub_mod h,
        Nat.mod_eq_of_lt (show τ + 2 * m₁ - 2 * (m₁ + m₂) < 2 * (m₁ + m₂) by omega)]
  have hτ₂lt : τ₂ < 2 * (m₁ + m₂) := by rw [hτ₂]; exact Nat.mod_lt _ (⋄)
  have e1 := dOf_six (n := 2 * (m₁ + m₂) + 7) (τ := τ) (i := i) (⋄) (⋄)
  have e2 := dOf_six (n := 2 * (m₁ + m₂) + 7) (τ := τ₂) (i := i) (⋄) (⋄)
  clear hτ₂
  rcases hτ₂' with e | ⟨e0, e⟩ <;> split_ifs at e1 e2 ⊢ <;> omega

theorem tpos_rel : tpos J.whole J.m₁ =
    (tpos J.whole (J.m₁ + 2 * J.m₂) + 2 * J.m₁) % (2 * J.whole.m) := by
  have hb := bS_le J.whole
  unfold tpos
  ϴ' Merge.Junction.whole_m at hb ⊢
  rw [Nat.mod_add_mod, show J.m₁ + 2 * J.m₂ + 2 * (J.m₁ + J.m₂) - bS J.whole + 2 * J.m₁ =
    (J.m₁ + 2 * (J.m₁ + J.m₂) - bS J.whole) + 2 * (J.m₁ + J.m₂) by omega, Nat.add_mod_right]

/-- **Every key inside a counted walk edge of `C` lies inside a piece.** -/
theorem cover (hP : J.P.Simple) {Q : Polygon} {S₁ S₂ : Set (Set Point)}
    (hS₁ : (chainModel J.left).ChordFamily Q S₁) (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    {γ : ℕ} (hsg₁ : (chainModel J.left).Semigranular S₁ γ)
    (hsg₂ : (chainModel J.right).Semigranular S₂ γ) :
    ∀ p : ℕ, p < (chainModel J.whole).W.n → (chainModel J.whole).counted p → ∀ t : ℝ, 0 < t →
      t < 1 → ∃ g L, PieceOK (chainModel J.whole) (J.fusion S₁ S₂ ∪ glueChords J)
        (bdryK J (J.fusion S₁ S₂ ∪ glueChords J)) γ g L ∧
        0 < off (chainModel J.whole).W.n g (p + t) ∧ off (chainModel J.whole).W.n g (p + t) < L := by
  intro p hp hc t ht ht1
  have h1 := J.one_le_m₁
  have h2 := J.one_le_m₂
  have hn := cm_n J.whole
  have hwm : J.whole.m = J.m₁ + J.m₂ := rfl
  obtain ⟨hc1, hc2⟩ : 6 ≤ p ∧ p < 2 * J.whole.m + 6 := hc
  obtain ⟨i, rfl⟩ : ∃ i, p = 6 + i := ⟨p - 6, ⋄⟩
  have hend : ∀ c ∈ S₁ ∪ S₂, (Merge.lend c ≠ J.shared →
        ∃ e ∈ J.fusion S₁ S₂ ∪ glueChords J, Merge.lend c ∈ e ∧ e ⊆ c) ∧
      (Merge.rend c ≠ J.shared → ∃ e ∈ J.fusion S₁ S₂ ∪ glueChords J, Merge.rend c ∈ e ∧ e ⊆ c) := by
    intro c hc
    obtain ⟨hl, hr⟩ := Merge.Junction.end_mem_fusion J hP hS₁.2.1 hS₂.2.1 hc
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨e, he, h'⟩ := hl h; exact ⟨e, Or.inl he, h'⟩
    · obtain ⟨e, he, h'⟩ := hr h; exact ⟨e, Or.inl he, h'⟩
  have hτlt := tpos_lt J.whole (J.m₁ + 2 * J.m₂)
  Ξ' hwm at hτlt
  have hrel := tpos_rel J
  Ξ' hwm at hrel
  rcases cover_arith h1 h2 hτlt hrel (show i < 2 * (J.m₁ + J.m₂) by omega) with hin | hin
  · refine side_pieces J hP S₁ S₂ (C' := J.left) rfl (J₀ := J.m₁ + 2 * J.m₂) (J₀' := J.m₁)
      (ℓ := 2 * J.m₁) (fun e he => tourV_left J he) ?_ ?_ (✓) (by rw [hwm]; omega)
      (left_box_eq J) (kt := J.left.topIdx) (⊚ topIdxs)
      (by have := J.left.topIdx_le; ϴ' Merge.Junction.left_m at this; rw [hwm]; omega)
      rfl hS₁ hsg₁ (fun c hc => hend c (Or.inl hc)) hp ht ht1 ?_
    · rw [tourV_left J (⋄), tourV_left_zero]; rfl
    · rw [tourV_left J le_rfl, tourV_left_end]; rfl
    · rw [hn, hwm]; exact hin
  · refine side_pieces J hP S₁ S₂ (C' := J.right) rfl (J₀ := J.m₁) (J₀' := 0)
      (ℓ := 2 * J.m₂) (fun e he => tourV_right J he) ?_ ?_ (✓) (by rw [hwm]; omega)
      (right_box_eq J) (kt := J.m₁ + J.right.topIdx) (⊚ topIdxs)
      (by have := J.right.topIdx_le; ϴ' Merge.Junction.right_m at this; rw [hwm]; omega)
      (Merge.Junction.whole_vertex_add J _) hS₂ hsg₂ (fun c hc => hend c (Or.inr hc)) hp ht ht1 ?_
    · rw [tourV_right J (⋄), tourV_right_zero]; rfl
    · rw [tourV_right J le_rfl, tourV_right_end]; rfl
    · rw [hn, hwm]; exact hin

/-! ## The weight bound -/

theorem not_sideInArc_end (a k : ℝ) : ¬ sideInArc a k k := by
  unfold sideInArc; split_ifs <;> intro h
  · exact lt_irrefl _ h.2
  · rcases h with h | h
    · linarith
    · exact lt_irrefl _ h

theorem not_sideInArc_start (k b : ℝ) : ¬ sideInArc k b k := by
  unfold sideInArc; split_ifs <;> intro h
  · exact lt_irrefl _ h.1
  · rcases h with h | h
    · exact lt_irrefl _ h
    · linarith

/-- **Every arc of the revised fusion meets at most `γ + 1` counted edges.** -/
theorem arc_bound (hP : J.P.Simple) (hgen : SharedGeneric J) {Q : Polygon}
    {S₁ S₂ : Set (Set Point)}
    (hS₁ : (chainModel J.left).ChordFamily Q S₁) (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    {γ : ℕ} (hsg₁ : (chainModel J.left).Semigranular S₁ γ)
    (hsg₂ : (chainModel J.right).Semigranular S₂ γ) {a b : ℝ}
    (hfree : ∀ x, sideInArc a b x → ¬ (chainModel J.whole).IsCut (J.fusion S₁ S₂ ∪ glueChords J) x) :
    (chainModel J.whole).arcWt a b ≤ γ + 1 := by
  set M := chainModel J.whole with hM
  set S' := J.fusion S₁ S₂ ∪ glueChords J with hS'
  have hcov := cover J hP hS₁ hS₂ hsg₁ hsg₂
  -- an interval free of cuts and of inner copies avoids all end keys
  have hsub : ∀ a' b', (∀ x, sideInArc a' b' x → ¬ M.IsCut S' x) →
      (∀ k : ℕ, k < M.W.n → M.W.vtx k = sharedV J → sideInArc a' b' k → InnerCopy J k → False) →
      M.arcWt a' b' ≤ γ := by
    intro a' b' hf hi
    refine arcWt_le_of_pieces hcov ?_ hf
    rintro x ⟨k, hk, rfl, hv | hc⟩ hx
    · rcases vkey_cut_or_inner J hP hgen S₁ S₂ hk hv with hc | hin
      · exact hf _ hx hc
      · exact hi k hk hv hx hin
    · exact hf _ hx hc
  by_cases hin : ∃ k : ℕ, k < M.W.n ∧ M.W.vtx k = sharedV J ∧ sideInArc a b k ∧ InnerCopy J k
  · obtain ⟨k, hk, hv, hkab, hinner⟩ := hin
    obtain ⟨q, hq, hqk⟩ := inner_cap_cut J hP hgen S₁ S₂ hk hv hinner
    have hqab : ¬ sideInArc a b q := fun h => hfree q h hq
    have hk6 := (vkey_nbrs J hP hk hv).1
    have hsplit := M.arcWt_le_split_vertex hkab
    have honly : ∀ k' : ℕ, k' < M.W.n → M.W.vtx k' = sharedV J → InnerCopy J k' → k' = k :=
      fun k' hk' hv' hi' => inner_unique J hP hk' hk hv' hv hi' hinner
    rcases hqk with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩
    · have hA : M.arcWt a k ≤ γ := hsub a k
        (fun x hx => hfree x (sideInArc_sub_left hkab hx))
        (fun k' hk' hv' hx hi' => by
          Ξ' honly k' hk' hv' hi' at hx; exact not_sideInArc_end _ _ hx)
      have hB : M.arcWt k b ≤ 1 := (M.arcWt_mono fun x hx =>
          sideInArc_before_cut hkab hqab hq1 hx).trans
        (arcWt_le_one_of_within M hq1 le_rfl hq2.le)
      omega
    · have hA : M.arcWt a k ≤ 1 := (M.arcWt_mono fun x hx =>
          sideInArc_after_cut hkab hqab hq2 hx).trans
        (arcWt_le_one_of_within M (k := k - 1) hq2
          (by rw [Nat.cast_sub (⋄)]; push_cast; linarith)
          (by rw [Nat.cast_sub (⋄)]; push_cast; linarith))
      have hB : M.arcWt k b ≤ γ := hsub k b
        (fun x hx => hfree x (sideInArc_sub_right hkab hx))
        (fun k' hk' hv' hx hi' => by
          Ξ' honly k' hk' hv' hi' at hx; exact not_sideInArc_start _ _ hx)
      omega
  · push Not at hin
    have := hsub a b hfree (fun k hk hv hx hi => hin k hk hv hx hi)
    omega

/-- **WP-D (math): the weight bound of the revised fusion** (`FusionWeightSpec`): the fusion of
two γ-semigranular submaps plus the glue chords is `(γ + 1)`-semigranular. -/
theorem fusionWeightSpec : FusionWeightSpec := by
  intro J Q S₁ S₂ γ hP hgen hS₁ hS₂ hsg₁ hsg₂ U hU
  unfold fuseLoss Model.weight
  rcases ((fun ab : ℝ × ℝ => (chainModel J.whole).arcWt ab.1 ab.2) ''
      {ab | (chainModel J.whole).IsArc (J.fusion S₁ S₂ ∪ glueChords J) U ab.1 ab.2}).eq_empty_or_nonempty
    with h | h
  · rw [h, csSup_empty]; exact Nat.zero_le _
  · refine csSup_le h ?_
    rintro _ ⟨ab, hab, rfl⟩
    exact arc_bound J hP hgen hS₁ hS₂ hsg₁ hsg₂ hab.2.2.2.2.2.1

end FuseMath

end

end Chazelle.Core
