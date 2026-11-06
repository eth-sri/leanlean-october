import RequestProject.RelatorConeFundamentalChain
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

def presCoverCircleInclusion (p : PresCoverRelator w f)
    (x : RelatorCircle w p.1.2) :=
  ((presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm x).val

theorem presCoverCircleInclusion_strictMono p :
    StrictMono (presCoverCircleInclusion w f hf p) :=
  fun _ _ h => (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm.strictMono h

theorem presCoverCircleInclusion_injective p :
    Function.Injective (presCoverCircleInclusion w f hf p) := by
  intro x y h
  exact (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm.injective (Subtype.ext h)

theorem presCoverCircleInclusion_lt_apex p
    x : presCoverCircleInclusion w f hf p x < p.1.1 :=
  ((presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm x).property

/-- The genuine finite triangle fan at an actual lifted relator apex. -/
def presCoverRelatorFan (p : PresCoverRelator w f) : StrictOrdTri P →₀ ℤ :=
  strictTopConeEdgeChain _
    (presCoverCircleInclusion_strictMono w f hf p) p.1.1
    (presCoverCircleInclusion_lt_apex w f hf p) (relatorCircleFundamentalChain w p.1.2)

theorem presCoverRelatorFan_boundary p :
    Comb.bdry2 (strictOrderCx P) (presCoverRelatorFan w f hf p) =
      chain1 (strictOrderCxMap (presCoverCircleInclusion w f hf p)
        (presCoverCircleInclusion_strictMono w f hf p)) (relatorCircleFundamentalChain w p.1.2) :=
  strictTopConeEdgeChain_cycle_boundary _ _ _ _ _
    (relatorCircleFundamentalChain_cycle w p.1.2)

theorem presCoverRelatorFan_first hpos
    p :
    presCoverRelatorFan w f hf p (presCoverRelatorTriangle w f hf hpos p) = 1 := by
  rwd [presCoverRelatorFan, strictTopConeEdgeChain_eq_mapDomain]
  have he := Finsupp.mapDomain_apply_of_injective
    (strictTopConeEdgeTriangle_injective _
      (presCoverCircleInclusion_strictMono w f hf p) p.1.1
      (presCoverCircleInclusion_lt_apex w f hf p) (presCoverCircleInclusion_injective w f hf p))
    (relatorCircleFundamentalChain w p.1.2)
    (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩)
  exact he.trans (relatorCircleFundamentalChain_edge0 w p.1.2 _)

/-- A genuine lifted fan has precisely the corresponding single relator coordinate. -/
theorem presCoverRelatorChain_fan hpos
    p :
    presCoverRelatorChain w f hf hpos (presCoverRelatorFan w f hf p) = Finsupp.single p 1 := by
  classical
  ext q
  by_cases h : q = p
  · subst q
    rwd [presCoverRelatorFan_first]
    simp
  · have hv : q.1.1 ≠ p.1.1 := by
      intro he
      apply h
      apply Subtype.ext
      apply Prod.ext he
      apply Sum.inr_injective
      exact q.2.symm.trans ((congrArg f he).trans p.2)
    have hz := strictTopConeEdgeChain_eq_zero_off_top _
      (presCoverCircleInclusion_strictMono w f hf p) p.1.1
      (presCoverCircleInclusion_lt_apex w f hf p) (relatorCircleFundamentalChain w p.1.2)
      (presCoverRelatorTriangle w f hf hpos q) hv
    aesop

/-- A genuine integer-linear realization of finite lifted-relator chains by actual cone fans. -/
def presCoverRelatorFanChain :
    (PresCoverRelator w f →₀ ℤ) →ₗ[ℤ] (StrictOrdTri P →₀ ℤ) :=
  Finsupp.linearCombination ℤ (presCoverRelatorFan w f hf)

/-- Actual finite cone-fan realization is a section of actual relator coordinates. -/
theorem presCoverRelatorChain_fanChain hpos
    c :
    presCoverRelatorChain w f hf hpos (presCoverRelatorFanChain w f hf c) = c := by
  lin_ind c p n =>
    simp [presCoverRelatorFanChain, Finsupp.linearCombination_single, map_smul, presCoverRelatorChain_fan]
