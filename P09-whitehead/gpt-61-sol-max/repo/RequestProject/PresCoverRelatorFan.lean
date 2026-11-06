import Mathlib.Tactic

import RequestProject.RelatorConeFundamentalChain

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

variable (p : PresCoverRelator w f)
noncomputable def presCoverCircleInclusion 
    (x : RelatorCircle w p.1.2)  :=
  ((presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm x).val

theorem presCoverCircleInclusion_strictMono  :
    StrictMono (presCoverCircleInclusion w f hf p) :=
  fun _ _ h => (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm.strictMono h

theorem presCoverCircleInclusion_injective  :
    Function.Injective (presCoverCircleInclusion w f hf p) := by
  intro x y h
  exact (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm.injective (Subtype.ext h)

theorem presCoverCircleInclusion_lt_apex 
    (x : RelatorCircle w p.1.2) : presCoverCircleInclusion w f hf p x < p.1.1 :=
  ((presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm x).property

/-- The genuine finite triangle fan at an actual lifted relator apex. -/
noncomputable def presCoverRelatorFan  : StrictOrdTri P →₀ ℤ :=
  strictTopConeEdgeChain (presCoverCircleInclusion w f hf p)
    (presCoverCircleInclusion_strictMono w f hf p) p.1.1
    (presCoverCircleInclusion_lt_apex w f hf p) (relatorCircleFundamentalChain w p.1.2)

theorem presCoverRelatorFan_boundary  :
    Comb.bdry2 (strictOrderCx P) (presCoverRelatorFan w f hf p) =
      chain1 (strictOrderCxMap (presCoverCircleInclusion w f hf p)
        (presCoverCircleInclusion_strictMono w f hf p)) (relatorCircleFundamentalChain w p.1.2) :=
  strictTopConeEdgeChain_cycle_boundary _ _ _ _ _
    (relatorCircleFundamentalChain_cycle w p.1.2)

variable (hpos : ∀ j, 0 < (w j).length)
theorem presCoverRelatorFan_first 
    (p : PresCoverRelator w f) :
    presCoverRelatorFan w f hf p (presCoverRelatorTriangle w f hf hpos p) = 1 := by
  rw  [presCoverRelatorFan, strictTopConeEdgeChain_eq_mapDomain]
  have he := Finsupp.mapDomain_apply_of_injective
    (strictTopConeEdgeTriangle_injective (presCoverCircleInclusion w f hf p)
      (presCoverCircleInclusion_strictMono w f hf p) p.1.1
      (presCoverCircleInclusion_lt_apex w f hf p) (presCoverCircleInclusion_injective w f hf p))
    (relatorCircleFundamentalChain w p.1.2)
    (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩)
  exact he.trans (relatorCircleFundamentalChain_edge0 w p.1.2 _)

/-- A genuine lifted fan has precisely the corresponding single relator coordinate. -/
theorem presCoverRelatorChain_fan 
    (p : PresCoverRelator w f) :
    presCoverRelatorChain w f hf hpos (presCoverRelatorFan w f hf p) = Finsupp.single p 1 := by
  classical
  ext q
  rw  [presCoverRelatorChain_apply]
  by_cases h : q = p
  · simp_all [presCoverRelatorFan_first]
  · have hv : q.1.1 ≠ p.1.1 := by
      intro he
      apply h
      apply Subtype.ext
      apply Prod.ext he
      apply Sum.inr_injective
      exact q.2.symm.trans ((congrArg f he).trans p.2)
    have hz := strictTopConeEdgeChain_eq_zero_off_top (presCoverCircleInclusion w f hf p)
      (presCoverCircleInclusion_strictMono w f hf p) p.1.1
      (presCoverCircleInclusion_lt_apex w f hf p) (relatorCircleFundamentalChain w p.1.2)
      (presCoverRelatorTriangle w f hf hpos q) hv
    rw  [show presCoverRelatorFan w f hf p (presCoverRelatorTriangle w f hf hpos q) = 0 from hz]
    simp [h]

/-- A genuine integer-linear realization of finite lifted-relator chains by actual cone fans. -/
noncomputable def presCoverRelatorFanChain  :=
  Finsupp.linearCombination ℤ (presCoverRelatorFan w f hf)

/-- Actual finite cone-fan realization is a section of actual relator coordinates. -/
theorem presCoverRelatorChain_fanChain 
    (c : PresCoverRelator w f →₀ ℤ) :
    presCoverRelatorChain w f hf hpos (presCoverRelatorFanChain w f hf c) = c := by
  induction c using Finsupp.induction_linear <;> simp_all [presCoverRelatorFanChain, presCoverRelatorChain_fan]

end FiniteChains.PresModel
