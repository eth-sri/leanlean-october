import RequestProject.OrderNerveWithTopCone
import RequestProject.QuotientSameFibersHomeomorph
import RequestProject.BallHomotopyExtension
import Mathlib.Analysis.Normed.Module.FiniteDimension


/-! Radial identification of an actual order-nerve cone with a genuine normed
disk. The input is the boundary homeomorphism; the extension, its inverse,
continuity, and exact boundary restriction are constructed here. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped unitInterval Classical

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem radialPoint_mem_ball (r : I) (x : UnitBoundary E) :
    ‖(r : ℝ) • x.val‖ ≤ 1 := by
  grind [norm_smul, Real.norm_of_nonneg r.property.1, x.property, mul_one]

def ballRadialQuotient : C(I × UnitBoundary E, ClosedUnitBall E) where
  toFun rx := ⟨(rx.1 : ℝ) • rx.2.val, radialPoint_mem_ball E rx.1 rx.2⟩
  continuous_toFun := by
    fun_prop

@[simp] theorem ballRadialQuotient_norm r x :
    ‖(ballRadialQuotient E (r, x)).val‖ = r := by
  change ‖(r : ℝ) • x.val‖ = _
  rw [norm_smul, Real.norm_of_nonneg r.property.1, x.property, mul_one]

@[simp] theorem ballRadialQuotient_one x :
    ballRadialQuotient E (1, x) = unitBoundaryInclusion E x := by
  apply Subtype.ext
  exact one_smul ℝ x.val

theorem ballRadialQuotient_eq_iff a b :
    ballRadialQuotient E a = ballRadialQuotient E b ↔
      a.1 = b.1 ∧ (a.1 = 0 ∨ a.2 = b.2) := by
  constructor
  · intro h
    have hn := (ballRadialQuotient_norm E a.1 a.2).symm.trans
      ((congrArg (‖·.val‖) h).trans
        (ballRadialQuotient_norm E b.1 b.2))
    have hr := Subtype.ext hn
    refine ⟨hr, ?_⟩
    by_cases hz : a.1 = 0
    · exact Or.inl hz
    · right
      apply Subtype.ext
      have he := congrArg (·.val) h
      change (a.1 : ℝ) • a.2.val = (b.1 : ℝ) • b.2.val at he
      simp_all
  · rintro ⟨hr, hz | hx⟩
    · apply Subtype.ext
      change (a.1 : ℝ) • a.2.val = (b.1 : ℝ) • b.2.val
      rw [← hr, hz]
      simp
    grind

theorem ballRadialQuotient_surjective (u : UnitBoundary E) :
    Function.Surjective (ballRadialQuotient E) := by
  intro x
  by_cases hx : x.val = 0
  · exact ⟨(0, u), Subtype.ext (by simp [ballRadialQuotient, hx])⟩
  · have hn := norm_ne_zero_iff.mpr hx
    let r : I := by aesop
    let v : UnitBoundary E := ⟨‖x.val‖⁻¹ • x.val, by
      rw [norm_smul, Real.norm_of_nonneg (by simp),
        inv_mul_cancel₀ hn]⟩
    refine ⟨(r, v), Subtype.ext ?_⟩
    change ‖x.val‖ • (‖x.val‖⁻¹ • x.val) = x.val
    simp_all

omit [NormedSpace ℝ E] in
theorem unitBoundary_isCompact [ProperSpace E] : IsCompact {x : E | ‖x‖ = 1} := by
  simpa [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : E) 1

end FiniteChains.RelativeAttachment

namespace FiniteChains.Comb
open RelativeAttachment
open scoped Classical unitInterval

variable {P : Type} [PartialOrder P] [Fintype P] [Nonempty P]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (e : orderNerveRealization P ≃ₜ UnitBoundary E)

def coneBallQuotient : C(I × orderNerveRealization P, ClosedUnitBall E) :=
  (ballRadialQuotient E).comp
    ⟨fun rx => (rx.1, e rx.2), continuous_fst.prodMk (e.continuous.comp continuous_snd)⟩

omit [Fintype P] [ProperSpace E] in
theorem coneBallQuotient_surjective : Function.Surjective (coneBallQuotient e) := by
  let p₀ : P := Classical.choice inferInstance
  intro x
  obtain ⟨⟨r, u⟩, hu⟩ := ballRadialQuotient_surjective E
    (e (orderNerveRealizationVertex p₀)) x
  exact ⟨(r, e.symm u), by simp_all [coneBallQuotient, ContinuousMap.comp_apply, ContinuousMap.coe_mk, Homeomorph.apply_symm_apply]⟩

omit [Fintype P] [Nonempty P] [ProperSpace E] in
theorem coneBallQuotient_fibers (a b : I × orderNerveRealization P) :
    orderNerveRadialCone P a = orderNerveRadialCone P b ↔
      coneBallQuotient e a = coneBallQuotient e b := by
  rw [orderNerveRadialCone_eq_iff]
  change _ ↔ ballRadialQuotient E (a.1, e a.2) =
    ballRadialQuotient E (b.1, e b.2)
  rw [ballRadialQuotient_eq_iff]
  simp

/-- Extend a boundary homeomorphism radially over the actual order cone. -/
def orderNerveWithTopBallHomeomorph :
    orderNerveRealization (WithTop P) ≃ₜ ClosedUnitBall E := by
  letI : CompactSpace (UnitBoundary E) := isCompact_iff_compactSpace.mp
    (unitBoundary_isCompact E)
  letI : CompactSpace (orderNerveRealization P) := e.isClosedEmbedding.compactSpace
  exact quotientSameFibersHomeomorph _ _
    ((orderNerveRadialCone P).continuous.isClosedMap.isQuotientMap
      (orderNerveRadialCone P).continuous (orderNerveRadialCone_surjective P))
    ((coneBallQuotient e).continuous.isClosedMap.isQuotientMap
      (coneBallQuotient e).continuous (coneBallQuotient_surjective e))
    (coneBallQuotient_fibers e)

theorem orderNerveWithTopBallHomeomorph_radial r x :
    orderNerveWithTopBallHomeomorph e (orderNerveRadialCone P (r, x)) =
      ballRadialQuotient E (r, e x) := quotientSameFibersHomeomorph_apply _ _ _ _ _ _

/-- The boundary restriction is exactly the supplied map, with no reparametrization. -/
theorem orderNerveWithTopBallHomeomorph_boundary x :
    orderNerveWithTopBallHomeomorph e (orderNerveConeBase P x) =
      unitBoundaryInclusion E (e x) := by
  rw [← orderNerveRadialCone_one P x, orderNerveWithTopBallHomeomorph_radial,
    ballRadialQuotient_one]
