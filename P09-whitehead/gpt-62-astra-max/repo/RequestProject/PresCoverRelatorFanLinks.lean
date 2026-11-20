module

public import RequestProject.PresCoverRelatorFan

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

theorem presCoverRelatorFan_circle (p : PresCoverRelator w f) :
    presCoverConeCircleChain w f hf _ _ p.2 (presCoverRelatorFan w f hf p) =
      relatorCircleFundamentalChain w _ := by
  classical
  ext e
  let E := strictOrderEdgeEquiv (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2)
  have he : (presCoverConeCircleHom w f hf _ _ p.2).onE _ = e :=
    E.apply_symm_apply e
  have hc := presCoverConeCircleChain_apply w f hf _ _ p.2
    (presCoverRelatorFan w f hf p) (E.symm e)
  erw [he] at hc
  erw [hc]
  erw [presCoverRelatorFan, strictTopConeEdgeChain_eq_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective
    (strictTopConeEdgeTriangle_injective (presCoverCircleInclusion w f hf p)
      (presCoverCircleInclusion_strictMono w f hf p) p.1.1
      (presCoverCircleInclusion_lt_apex w f hf p) (presCoverCircleInclusion_injective w f hf p))
    _ e

theorem presCoverRelatorFan_circle_off (p q : PresCoverRelator w f) (h : q ≠ p) :
    presCoverConeCircleChain w f hf _ _ q.2 (presCoverRelatorFan w f hf p) = 0 := by
  have hv : q.1.1 ≠ p.1.1 := by
    intro he
    apply h
    apply Subtype.ext
    apply Prod.ext he
    apply Sum.inr_injective
    exact q.2.symm.trans ((congrArg f he).trans p.2)
  ext e
  let E := strictOrderEdgeEquiv (presCoverConeCircleOrderIso w f hf q.1.1 q.1.2 q.2)
  have he : (presCoverConeCircleHom w f hf _ _ q.2).onE _ = e :=
    E.apply_symm_apply e
  have hc := presCoverConeCircleChain_apply w f hf _ _ q.2
    (presCoverRelatorFan w f hf p) (E.symm e)
  erw [he] at hc
  erw [hc, Finsupp.zero_apply]
  apply strictTopConeEdgeChain_eq_zero_off_top <;> assumption

/-- Every finite sum of genuine relator fans has its prescribed actual circle link. -/
theorem presCoverRelatorFanChain_circle (c : PresCoverRelator w f →₀ ℤ)
    (q : PresCoverRelator w f) :
    presCoverConeCircleChain w f hf _ _ q.2 (presCoverRelatorFanChain w f hf c) =
      c q • relatorCircleFundamentalChain w _ := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp [presCoverConeCircleChain]
  | add c d hc hd => simp [map_add, hc, hd, add_smul]
  | single p n =>
    erw [presCoverRelatorFanChain, Finsupp.linearCombination_single, map_smul]
    by_cases h : p = q
    · simp_all [presCoverRelatorFan_circle]
    · erw [presCoverRelatorFan_circle_off w f hf p q (Ne.symm h)] <;> simp_all

end FiniteChains.PresModel
