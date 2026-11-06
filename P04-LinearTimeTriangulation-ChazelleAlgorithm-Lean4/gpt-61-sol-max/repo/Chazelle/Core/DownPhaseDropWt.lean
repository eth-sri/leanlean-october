module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.FactsAttach
public import Chazelle.Core.FactsL23

/-!
# WP-M (B3′, part 9): weights after dropping a block of chords

Finding M6: dropping the wall-to-wall chords of a chain normal form at most doubles the weights.
This file proves it in key form, for any walk-axiom model (`semigranular_drop`).

Let `F' ⊆ F` and let `I = [lo, hi]` be a key interval such that
* every cut of `F` is a cut of `F'` or lies in `I`;
* no cut of `F'` lies in `I`;
* every counted walk edge lies after `I`.

Then an arc `(a, b)` of a region of `F'` is an arc of a region of `F`, or it contains `I`. In the
second case its counted edges lie in its first piece `(a, f)` or its last piece `(g, b)`, which
are arcs of regions of `F`.  So `F'` is `2γ`-semigranular when `F` is `γ`-semigranular.
-/

namespace Chazelle.Core

namespace BoxT

@[expose] public section

open Set
open Chazelle.Chain (sideInArc)

/-- Closing tactic for cyclic case analyses with nested disjunctions. -/
macro "cyc_close2" : tactic => `(tactic| (
  (try simp only [not_and_or, not_or, not_lt] at *) <;>
  (casesm* _ ∧ _, _ ∨ _) <;>
  first
  | linarith
  | (constructor! <;> linarith)
  | (left; constructor! <;> linarith) | (right; constructor! <;> linarith)
  | (left; linarith) | (right; linarith)
  | (left; left; linarith) | (left; right; linarith)
  | (right; left; linarith) | (right; right; linarith)))

/-! ## Cyclic facts -/

/-- The successor `f` of `a` among keys containing `w ∈ (a, b)` lies in `(a, b)`. -/
theorem cyc_succ_in {a b w f : ℝ} (hw : sideInArc a b w) (hf : ¬ sideInArc a f w) (hfa : f ≠ a) :
    sideInArc a b f := by
  core_grind

/-- The predecessor `g` of `b` among keys containing `w ∈ (a, b)` lies in `(a, b)`. -/
theorem cyc_pred_in {a b w g : ℝ} (hw : sideInArc a b w) (hg : ¬ sideInArc g b w) (hgb : g ≠ b) :
    sideInArc a b g := by
  core_grind

/-- **The two end pieces.**  If `(a, b)` contains points `f, g` of an interval `I = [lo, hi]`
avoiding `a` and `b`, a key of `(a, b)` outside `I` lies in `(a, f)` or in `(g, b)`. -/
theorem cyc_pieces {lo hi a b f g x : ℝ} (hf : lo ≤ f ∧ f ≤ hi) (hg : lo ≤ g ∧ g ≤ hi)
    (ha : a < lo ∨ hi < a) (hb : b < lo ∨ hi < b) (hfin : sideInArc a b f)
    (hgin : sideInArc a b g) (hx : x < lo ∨ hi < x) (hin : sideInArc a b x) :
    sideInArc a f x ∨ sideInArc g b x := by
  core_grind

/-! ## Weights -/

variable {M : Model}

/-- The counted walk edges met by the open key interval `(a, b)`. -/
def edgesIn (M : Model) (a b : ℝ) : Set ℕ :=
  {p : ℕ | p < M.W.n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b (p + t)}

section
variable (a b : ℝ)
theorem arcWt_eq' : M.arcWt a b = (edgesIn M a b).ncard := rfl

theorem edgesIn_finite : (edgesIn M a b).Finite :=
  (Set.finite_lt_nat M.W.n).subset fun _ hp => hp.1

theorem arcWt_le_n : M.arcWt a b ≤ M.W.n := by
  rw [arcWt_eq']
  calc (edgesIn M a b).ncard ≤ ((Finset.range M.W.n : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_le_ncard (fun p hp => by simpa using hp.1) (Finset.finite_toSet _)
    _ = M.W.n := by rw [Set.ncard_coe_finset, Finset.card_range]


end

/-- The weight of an arc is at most the weight of its region. -/
theorem arcWt_le_weight {F : Set (Set Point)} {X : Set Point} {a b : ℝ} (h : M.IsArc F X a b) :
    M.arcWt a b ≤ M.weight F X :=
  le_csSup ⟨M.W.n, by rintro _ ⟨ab, -, rfl⟩; exact arcWt_le_n _ _⟩ ⟨(a, b), h, rfl⟩

theorem arcWt_le_of_sub {a b a' b' : ℝ}
    (h : ∀ p : ℕ, M.counted p → ∀ t : ℝ, 0 < t → t < 1 → sideInArc a b (p + t) →
      sideInArc a' b' (p + t)) : M.arcWt a b ≤ M.arcWt a' b' := by
  rw [arcWt_eq', arcWt_eq']
  refine Set.ncard_le_ncard ?_ (edgesIn_finite a' b')
  rintro p ⟨hp, hc, t, ht0, ht1, hx⟩
  exact ⟨hp, hc, t, ht0, ht1, h p hc t ht0 ht1 hx⟩

theorem arcWt_le_add {a b a₁ b₁ a₂ b₂ : ℝ}
    (h : ∀ p : ℕ, M.counted p → ∀ t : ℝ, 0 < t → t < 1 → sideInArc a b (p + t) →
      sideInArc a₁ b₁ (p + t) ∨ sideInArc a₂ b₂ (p + t)) :
    M.arcWt a b ≤ M.arcWt a₁ b₁ + M.arcWt a₂ b₂ := by
  rw [arcWt_eq', arcWt_eq', arcWt_eq']
  calc (edgesIn M a b).ncard ≤ (edgesIn M a₁ b₁ ∪ edgesIn M a₂ b₂).ncard := by
        refine Set.ncard_le_ncard ?_ ((edgesIn_finite _ _).union (edgesIn_finite _ _))
        rintro p ⟨hp, hc, t, ht0, ht1, hx⟩
        rcases h p hc t ht0 ht1 hx with h' | h'
        · exact Or.inl ⟨hp, hc, t, ht0, ht1, h'⟩
        · exact Or.inr ⟨hp, hc, t, ht0, ht1, h'⟩
    _ ≤ _ := Set.ncard_union_le _ _

theorem isCut_mono {F F' : Set (Set Point)} (hsub : F' ⊆ F) {k : ℝ} (h : M.IsCut F' k) :
    M.IsCut F k := by
  core_grind

/-- **Dropping a block of chords at most doubles the weights.** -/
theorem semigranular_drop (hM : WalkAx M) {F F' : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (hsub : F' ⊆ F) {lo hi : ℝ}
    (hcut : ∀ k, M.IsCut F k → M.IsCut F' k ∨ (lo ≤ k ∧ k ≤ hi))
    (hcut' : ∀ k, M.IsCut F' k → k < lo ∨ hi < k)
    (hcnt : ∀ p : ℕ, M.counted p → hi < p) {γ : ℕ} (hγ : M.Semigranular F γ) :
    M.Semigranular F' (2 * γ) := by
  have key : ∀ X ∈ M.regions F, ∀ a b, M.IsArc F X a b → M.arcWt a b ≤ γ :=
    fun X hX a b h => (arcWt_le_weight h).trans (hγ X hX)
  have hK := hM.finite_cuts hF hfin
  have hkey : ∀ (p : ℕ) (t : ℝ), M.counted p → 0 < t → hi < p + t := fun p t hc ht => by
    grind
  intro W hW
  apply csSup_le'
  rintro _ ⟨⟨a, b⟩, harc, rfl⟩
  show M.arcWt a b ≤ 2 * γ
  rcases harc.2.2.2.2.1 with ⟨hca, hcb, hab⟩ | ⟨hF'e, rfl, rfl⟩
  · have hcaF := isCut_mono hsub hca
    have hcbF := isCut_mono hsub hcb
    by_cases hw : ∃ w, sideInArc a b w ∧ M.IsCut F w
    · obtain ⟨w, hwin, hwc⟩ := hw
      obtain ⟨f, hfK, hfa, hfgap⟩ := exists_succ_gap hK hcaF hcbF hab
      obtain ⟨g, hgK, hgb, hggap⟩ := exists_pred_gap hK hcbF hcaF (Ne.symm hab)
      have hfin' : sideInArc a b f := cyc_succ_in hwin (hfgap w hwc) hfa
      have hgin' : sideInArc a b g := cyc_pred_in hwin (hggap w hwc) hgb
      have hfI : lo ≤ f ∧ f ≤ hi :=
        (hcut f hfK).resolve_left (harc.2.2.2.2.2.1 f hfin')
      have hgI : lo ≤ g ∧ g ≤ hi :=
        (hcut g hgK).resolve_left (harc.2.2.2.2.2.1 g hgin')
      obtain ⟨X₁, hX₁, harc₁⟩ := hM.arc_of_gap hF hfin hcaF hfK (Ne.symm hfa)
        (fun k hk hc => hfgap k hc hk)
      obtain ⟨X₂, hX₂, harc₂⟩ := hM.arc_of_gap hF hfin hgK hcbF hgb
        (fun k hk hc => hggap k hc hk)
      have ha := hcut' a hca
      have hb := hcut' b hcb
      calc M.arcWt a b ≤ M.arcWt a f + M.arcWt g b := arcWt_le_add fun p hc t ht0 _ hx =>
            cyc_pieces hfI hgI ha hb hfin' hgin' (Or.inr (hkey p t hc ht0)) hx
        _ ≤ γ + γ := Nat.add_le_add (key X₁ hX₁ _ _ harc₁) (key X₂ hX₂ _ _ harc₂)
        _ = 2 * γ := by ring
    · push Not at hw
      obtain ⟨X, hX, harcX⟩ := hM.arc_of_gap hF hfin hcaF hcbF hab (fun k hk hc => hw k hk hc)
      grind
  · by_cases hFe : F = ∅
    · grind
    · obtain ⟨k₁, k₂, h₁, h₂, hk⟩ := hM.two_cuts hF (Set.nonempty_iff_ne_empty.2 hFe)
      have hnoF' : ∀ k, ¬ M.IsCut F' k := by
        rintro k ⟨c, hc, -⟩; simp_all
      obtain ⟨f, hfK, hfmin⟩ := Set.exists_min_image {x | M.IsCut F x} id hK ⟨k₁, h₁⟩
      obtain ⟨g, hgK, hgmax⟩ := Set.exists_max_image {x | M.IsCut F x} id hK ⟨k₁, h₁⟩
      simp only [id] at hfmin hgmax
      have hfg : f < g := by
        rcases lt_or_ge f g with h | h
        · exact h
        · exfalso; apply hk
          have e1 := hfmin k₁ h₁; have e2 := hgmax k₁ h₁
          have e3 := hfmin k₂ h₂; grind
      have hgI := (hcut g hgK).resolve_left (hnoF' g)
      obtain ⟨X, hX, harcX⟩ := hM.arc_of_gap hF hfin hgK hfK (ne_of_gt hfg) (by
        intro k hk hc
        unfold sideInArc at hk
        rw [ite_eq_right (not_lt.2 hfg.le)] at hk
        rcases hk with hk | hk
        · linarith [hgmax k hc]
        · linarith [hfmin k hc])
      have := (arcWt_le_of_sub (M := M) (a := 0) (b := 0) (a' := g) (b' := f)
        fun p hc t ht0 _ _ => by
          core_grind).trans (key X hX _ _ harcX)
      omega

end

end BoxT

end Chazelle.Core
