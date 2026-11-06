import RequestProject.PresCoverRelatorFan
import RequestProject.Tac


bwd

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

theorem presCoverRelatorFan_circle p :
    presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2 (presCoverRelatorFan w f hf p) =
      relatorCircleFundamentalChain w p.1.2 := by
  classical
  ext e
  let E := strictOrderEdgeEquiv (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2)
  have he : (presCoverConeCircleHom w f hf p.1.1 p.1.2 p.2).onE (E.symm e) = e :=
    E.apply_symm_apply e
  have hc := presCoverConeCircleChain_apply w f hf p.1.1 p.1.2 p.2
    (presCoverRelatorFan w f hf p) (E.symm e)
  rwd [he] at hc
  rwd [hc]
  rwd [presCoverRelatorFan, strictTopConeEdgeChain_eq_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective
    (strictTopConeEdgeTriangle_injective _
      _ p.1.1
      _ (presCoverCircleInclusion_injective w f hf p))
    _ e

theorem presCoverRelatorFan_circle_off p q (h : q ≠ p) :
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
  rwd [he] at hc
  rwd [hc, Finsupp.zero_apply]
  exact strictTopConeEdgeChain_eq_zero_off_top _
    _ p.1.1
    _ _
    _ hv

/-- Every finite sum of genuine relator fans has its prescribed actual circle link. -/
theorem presCoverRelatorFanChain_circle c
    q :
    presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2 (presCoverRelatorFanChain w f hf c) =
      c q • relatorCircleFundamentalChain w q.1.2 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => aesop
  | add c d hc hd =>
    have ha : presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2
        (presCoverRelatorFanChain w f hf (c + d)) =
        presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2 (presCoverRelatorFanChain w f hf c) +
        presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2 (presCoverRelatorFanChain w f hf d) := by
      simp [presCoverConeCircleChain, map_add]
    simp_all [ha, hc, hd, Finsupp.add_apply, add_smul]
  | single p n =>
    rwd [presCoverRelatorFanChain, Finsupp.linearCombination_single]
    have hs : presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2
        (n • presCoverRelatorFan w f hf p) =
        n • presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2 (presCoverRelatorFan w f hf p) := by
      simp [presCoverConeCircleChain, map_smul]
    by_cases h : p = q
    · simp_all [presCoverRelatorFan_circle]
    · simp_all [presCoverRelatorFan_circle_off w f hf p q (Ne.symm h)]
