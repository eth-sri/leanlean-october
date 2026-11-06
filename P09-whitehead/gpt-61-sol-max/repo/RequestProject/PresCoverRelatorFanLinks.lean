import Mathlib.Tactic

import RequestProject.PresCoverRelatorFan

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

theorem presCoverRelatorFan_circle (p : PresCoverRelator w f) :
    presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2 (presCoverRelatorFan w f hf p) =
      relatorCircleFundamentalChain w p.1.2 := by
  classical
  ext e
  let E := strictOrderEdgeEquiv (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2)
  have he : (presCoverConeCircleHom w f hf p.1.1 p.1.2 p.2).onE (E.symm e) = e :=
    E.apply_symm_apply e
  have hc := presCoverConeCircleChain_apply w f hf p.1.1 p.1.2 p.2
    (presCoverRelatorFan w f hf p) (E.symm e)
  rw  [he] at hc
  rw  [hc]
  rw  [presCoverRelatorFan, strictTopConeEdgeChain_eq_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective
    (strictTopConeEdgeTriangle_injective (presCoverCircleInclusion w f hf p)
      (presCoverCircleInclusion_strictMono w f hf p) p.1.1
      (presCoverCircleInclusion_lt_apex w f hf p) (presCoverCircleInclusion_injective w f hf p))
    (relatorCircleFundamentalChain w p.1.2) e

theorem presCoverRelatorFan_circle_off (p q : PresCoverRelator w f) (h : q ≠ p) :
    presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2 (presCoverRelatorFan w f hf p) = 0 := by
  have hv : q.1.1 ≠ p.1.1 := by
    intro he
    apply h
    apply Subtype.ext
    apply Prod.ext he
    apply Sum.inr_injective
    exact q.2.symm.trans ((congrArg f he).trans p.2)
  ext e
  let E := strictOrderEdgeEquiv (presCoverConeCircleOrderIso w f hf q.1.1 q.1.2 q.2)
  have he : (presCoverConeCircleHom w f hf q.1.1 q.1.2 q.2).onE (E.symm e) = e :=
    E.apply_symm_apply e
  have hc := presCoverConeCircleChain_apply w f hf q.1.1 q.1.2 q.2
    (presCoverRelatorFan w f hf p) (E.symm e)
  rw  [he] at hc
  rw  [hc, Finsupp.zero_apply]
  exact strictTopConeEdgeChain_eq_zero_off_top (presCoverCircleInclusion w f hf p)
    (presCoverCircleInclusion_strictMono w f hf p) p.1.1
    (presCoverCircleInclusion_lt_apex w f hf p) (relatorCircleFundamentalChain w p.1.2)
    (strictConeTriangle q.1.1 (E.symm e)) hv

/-- Every finite sum of genuine relator fans has its prescribed actual circle link. -/
theorem presCoverRelatorFanChain_circle (c : PresCoverRelator w f →₀ ℤ)
    (q : PresCoverRelator w f) :
    presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2 (presCoverRelatorFanChain w f hf c) =
      c q • relatorCircleFundamentalChain w q.1.2 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp [presCoverConeCircleChain]
  | add c d hc hd =>
    have ha : presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2
        (presCoverRelatorFanChain w f hf (c + d)) =
        presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2 (presCoverRelatorFanChain w f hf c) +
        presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2 (presCoverRelatorFanChain w f hf d) := by
      simp only [presCoverConeCircleChain, map_add]
    rw  [ha, hc, hd, Finsupp.add_apply, add_smul]
  | single p n =>
    rw  [presCoverRelatorFanChain, Finsupp.linearCombination_single]
    have hs : presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2
        (n • presCoverRelatorFan w f hf p) =
        n • presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2 (presCoverRelatorFan w f hf p) := by
      simp only [presCoverConeCircleChain, map_smul]
    rw  [hs]
    by_cases h : p = q
    · simp_all [presCoverRelatorFan_circle]
    · simp_all [FiniteChains.PresModel.presCoverRelatorFan_circle_off, Ne.symm]

end FiniteChains.PresModel
