module

public import Chazelle.Core.SweepLabelJL
public import Chazelle.Core.SweepLabelGap

/-!
# The sweep (WP-D): the left correspondence without `TopStrict` (F2)

`corr_left0`: the correspondence of `corr_left` without its gap field `box` (`Corr0`), which is
the only place where `corr_left` uses `TopStrict J.left`.  The side-0 sweep lemmas use only
`sidePt_eq`, `attach_iff`, `faces_iff` and the offsets, which `Corr0` provides.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideLeft sidePrev sideNext)
open Chazelle.Visibility (rayPt)
open WalkEmbed

namespace Sweep

variable (J : Merge.Junction)

theorem corr_left0 (hP : J.P.Simple) {S₁ : Set (Set Point)}
    (hS₁ : S₁ ⊆ Merge.augChords J.left) (hS₁f : S₁.Finite) :
    Corr0 (chainModel J.whole) (chainModel J.left) (F₁plus J S₁) S₁
      (6 + tpos J.whole (J.m₁ + 2 * J.m₂)) (6 + tpos J.left J.m₁) (lL1 J) (lL2 J) (lδ J) := by
  unfold lL1 lL2 lδ
  set C := J.whole with hC
  set C₁ := J.left with hC₁
  set W := (chainModel C).W with hW
  set W₁ := (chainModel C₁).W with hW₁
  have hn : W.n = 2 * C.m + 7 := cm_n C
  have hn₁ : W₁.n = 2 * C₁.m + 7 := cm_n C₁
  have hwm : C.m = J.m₁ + J.m₂ := rfl
  have hm1 : C₁.m = J.m₁ := rfl
  
  have h2 := J.one_le_m₂
  set τ := tpos C (J.m₁ + 2 * J.m₂) with hτ_def
  set τ' := tpos C₁ J.m₁ with hτ'_def
  have hτ : τ < 2 * C.m := tpos_lt C _
  have hτ' : τ' < 2 * C₁.m := tpos_lt C₁ _
  set ℓ := 2 * J.m₁ with hℓ_def
  set s := 2 * C.m - τ with hs_def
  set s' := 2 * C₁.m - τ' with hs'_def
  have hT : ∀ e, e ≤ ℓ → tourV C (J.m₁ + 2 * J.m₂) e = tourV C₁ J.m₁ e :=
    fun e he => tourV_left J he
  have hM := walkAx_chainModel (C := C) hP
  have hM₁ := walkAx_chainModel (C := C₁) hP
  have hR : C₁.radius = C.radius := FuseMath.radius_of_P J rfl
  have hg : 6 + τ < W.n := by omega
  have hg' : 6 + τ' < W₁.n := by omega
  have hv0 : W₁.vtx (6 + τ') = J.shared := by
    have := walk_tour C₁ J.m₁ 0 (by omega)
    rw [add_zero, Nat.mod_eq_of_lt hg', tourV_left_zero] at this
    exact this
  have hnoV : ∀ L : ℝ, (τ' = 0 → L ≤ 2 * C₁.m) → ∀ p < W₁.n, ∀ t : ℝ, 0 ≤ t → t < 1 →
      0 < off W₁.n ((6 + τ' : ℕ) : ℝ) (p + t) → off W₁.n ((6 + τ' : ℕ) : ℝ) (p + t) < L →
      sidePt W₁ p t ≠ W₁.vtx (6 + τ') := by
    intro L hL p hp t ht ht1 hpos hlt heq
    rw [hv0, show J.shared = C₁.vertex C₁.m from rfl] at heq
    have hvx := off_vertexEnd C₁ hP hp ht ht1 heq
    grind
  have htrans : ∀ c ∈ S₁, ∀ q ∈ c, q ∉ (chainModel C₁).D → q ≠ W₁.vtx (6 + τ') →
      ∃ e ∈ F₁plus J S₁, q ∈ e ∧ e ⊆ c := by
    rw [hv0]; exact trans_left J hP hS₁
  have hnest : ∀ e ∈ F₁plus J S₁, ∀ e' ∈ F₁plus J S₁, e ⊆ e' → e = e' :=
    fun e he e' he' h => augChords_nest (F₁plus_subset J hS₁ he) (F₁plus_subset J hS₁ he') h
  have hFs := F₁plus_subset J hS₁
  have hFf := F₁plus_finite J hS₁f
  have hℓ : ℓ < 2 * C.m := by omega
  have hℓ' : ℓ ≤ 2 * C₁.m := by omega
  have hℓ'R : (ℓ : ℝ) ≤ 2 * C₁.m := by grind
  by_cases hsl : s < ℓ
  · -- case Sh
    have hss : s = s' := (left_box_eq J hsl).symm
    have hA := agree_Sh hT hR.symm hℓ.le hℓ' hss hsl
    rw [ite_eq_left hsl, ite_eq_left hsl, ite_eq_left hsl]
    refine ⟨hM, hM₁, hFs, hFf, hS₁, hS₁f, hg, hg', by grind,
      by grind, fun _ => rfl, fun h => absurd h (lt_irrefl 0), hA, ?_,
      hnoV _ (fun h0 => absurd h0 (by omega)), htrans, hnest⟩
    intro d hd
    obtain rfl : d = 0 := by omega
    simpa using hA (ℓ + 7) le_rfl
  push Not at hsl
  by_cases hsl' : ℓ ≤ s'
  · -- case N
    have hA := agree_N hT hsl hsl'
    rw [ite_eq_right (show ¬ s < ℓ by omega), ite_eq_right (show ¬ s < ℓ by omega),
      ite_eq_right (show ¬ s < ℓ by omega), ite_eq_left hsl', ite_eq_left hsl', ite_eq_left hsl']
    refine ⟨hM, hM₁, hFs, hFf, hS₁, hS₁f, hg, hg', by grind,
      by grind, fun _ => rfl, fun h => absurd h (lt_irrefl 0), hA, ?_,
      hnoV _ (fun _ => by grind), htrans, hnest⟩
    grind [Chazelle.Core.WalkEmbed.Agree]
  -- case G
  push Not at hsl'
  have hA1 := agree_G1 hT hsl hsl'
  have hA2 := agree_G2 hT hℓ' hsl hsl'
  
  rw [ite_eq_right (show ¬ s < ℓ by omega), ite_eq_right (show ¬ s < ℓ by omega),
    ite_eq_right (show ¬ s < ℓ by omega), ite_eq_right (show ¬ ℓ ≤ s' by omega),
    ite_eq_right (show ¬ ℓ ≤ s' by omega), ite_eq_right (show ¬ ℓ ≤ s' by omega)]
  refine ⟨hM, hM₁, hFs, hFf, hS₁, hS₁f, hg, hg', by grind,
    by grind, fun h => absurd h (by norm_num), fun _ => by grind, hA1, ?_,
    hnoV _ (fun h0 => absurd h0 (by omega)), htrans, hnest⟩
  · intro d hd
    have := hA2 d hd
    grind

end Sweep

end

end Chazelle.Core
