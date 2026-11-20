/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExpansionUniqueness

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower KnightRealization Value ExtOrd Cardinal

universe w

theorem isNormal_blockLevel : Order.IsNormal blockLevel :=
  (Ordinal.isNormal_add_right Ordinal.omega0).comp
    (Ordinal.isNormal_mul_right Ordinal.omega0_pos)

/-- A label at a limit block is determined by the lower blocks. -/
theorem ExtOrd.eq_of_forall_truncExt_blockLevel_eq {l : Ordinal.{0}} (hl : Order.IsSuccLimit l)
    {x y : ExtOrd} (hx : x < ofOrd (blockLevel l) ∨ x = ⊤) (hy : y < ofOrd (blockLevel l) ∨ y = ⊤)
    (h : ∀ ξ < l, truncExt (blockLevel ξ) x = truncExt (blockLevel ξ) y) : x = y := by
  letI : Nonempty {ξ // ξ < l} := ⟨⟨0, hl.pos⟩⟩
  refine ExtOrd.eq_of_forall_truncExt_eq (c := fun ξ : {ξ // ξ < l} => blockLevel ξ.1)
    (fun γ hγ => ?_) hx hy (fun i => h i.1 i.2)
  obtain ⟨ξ, hξ, hlt⟩ := (isNormal_blockLevel.lt_iff_exists_lt hl).mp hγ
  exact ⟨⟨ξ, hξ⟩, hlt⟩

namespace KnightRealization

variable {M : Type w}

/-- **Limit uniqueness**: realizations at a limit block with equal reducts to every lower block
are equal (no model hypotheses). -/
theorem eq_of_reduct_eq_of_forall_lt {l : Ordinal.{0}} (hl : Order.IsSuccLimit l)
    {N N' : KnightRealization (blockStage l) M}
    (hred : ∀ ξ (h : ξ < l), N.reduct (blockStage_mono h.le) = N'.reduct (blockStage_mono h.le)) :
    N = N' := by
  have h0 : (0 : Ordinal.{0}) < l := hl.pos
  apply Realization.ext
  intro n t
  have hr : ∀ ξ (h : ξ < l), (N.eval t).map (knightTower.reduce (blockStage_mono h.le)) =
      (N'.eval t).map (knightTower.reduce (blockStage_mono h.le)) := fun ξ h =>
    congrArg (fun R : KnightRealization (blockStage ξ) M => R.eval t) (hred ξ h)
  rcases hp' : N.eval t with _ | p' <;> rcases hp'' : N'.eval t with _ | p''
  · rfl
  · grind
  · grind
  · congr 1
    -- the reductions of the two labels agree at every lower block
    have hrt : ∀ ξ (h : ξ < l), reduceType (blockStage ξ).2 (blockStage_mono h.le) p' =
        reduceType (blockStage ξ).2 (blockStage_mono h.le) p'' := by aesop
    have hsch : p'.scheme = p''.scheme :=
      congrArg (fun q : S (blockStage 0).1 n => q.scheme) (hrt 0 h0)
    obtain ⟨sc, lab, bnd, resp⟩ := p'
    obtain ⟨sc', lab', bnd', resp'⟩ := p''
    simp only at hsch
    subst hsch
    refine StageType.ext rfl (heq_of_eq (funext fun Xi => ?_))
    refine ExtOrd.eq_of_forall_truncExt_blockLevel_eq hl (bnd Xi) (bnd' Xi) fun ξ hξ => ?_
    have hh := (StageType.ext_iff.mp (hrt ξ hξ)).2
    have hfun := eq_of_heq hh
    exact congrFun hfun Xi

/-- **Reduction is injective on models**: two models at block `η` with equal reducts to a block
`ξ ≤ η` are equal. -/
theorem eq_of_reduct_eq_of_le (η : Ordinal.{0}) :
    ∀ (ξ : Ordinal.{0}) (hξη : ξ ≤ η) (N N' : KnightRealization (blockStage η) M),
      N.IsModel → N'.IsModel →
      N.reduct (blockStage_mono hξη) = N'.reduct (blockStage_mono hξη) → N = N' := by
  induction η using WellFoundedLT.induction with
  | _ η ih =>
  intro ξ hξη N N' hN hN' hred
  rcases Ordinal.zero_or_succ_or_isSuccLimit η with rfl | ⟨η', rfl⟩ | hlim
  · obtain rfl : ξ = 0 := le_antisymm hξη zero_le
    rwa [Realization.reduct_refl, Realization.reduct_refl] at hred
  · rcases eq_or_lt_of_le hξη with rfl | hlt
    · rwa [Realization.reduct_refl, Realization.reduct_refl] at hred
    · have hξη' : ξ ≤ η' := Order.lt_succ_iff.mp hlt
      have hη' : η' < Order.succ η' := Order.lt_succ η'
      have h1 := ih η' hη' ξ hξη' (N.reduct (blockStage_mono (Order.le_succ η')))
        (N'.reduct (blockStage_mono (Order.le_succ η'))) (hN.reduct _) (hN'.reduct _)
        (by rw [Realization.reduct_reduct, Realization.reduct_reduct]; exact hred)
      exact eq_of_reduct_eq_blockStage hN hN' h1
  · apply eq_of_reduct_eq_of_forall_lt hlim
    intro ζ hζ
    rcases le_or_gt ξ ζ with hξζ | hζξ
    · exact ih ζ hζ ξ hξζ (N.reduct _) (N'.reduct _) (hN.reduct _) (hN'.reduct _)
        (by rw [Realization.reduct_reduct, Realization.reduct_reduct]; exact hred)
    · rw [← Realization.reduct_reduct (blockStage_mono hζξ.le) (blockStage_mono hξη) N, hred,
        Realization.reduct_reduct]

end KnightRealization

end VaughtConjecture.Knight
