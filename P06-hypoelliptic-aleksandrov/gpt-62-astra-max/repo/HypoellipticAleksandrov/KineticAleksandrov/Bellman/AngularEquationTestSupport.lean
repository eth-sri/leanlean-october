module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationTest
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-! # Compact support of the zero-extended source angular tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set

variable (ζ φ : ℝ → ℝ) (hcζ : HasCompactSupport ζ) (hcφ : HasCompactSupport φ)
    (hs : tsupport ζ ⊆ Ioi (0 : ℝ))
include hcζ hcφ hs

/-- A compact positive radial support times a compact angular support stays away from the
origin. -/
theorem bellmanAngularTest_support_data :
    HasCompactSupport (bellmanAngularTest ζ φ) ∧
      tsupport (bellmanAngularTest ζ φ) ⊆ {q : ℝ × ℝ | 0 < q.1} := by
  let K : Set (BellmanPositiveTime × ℝ) :=
    (Subtype.val ⁻¹' tsupport ζ) ×ˢ tsupport φ
  let P := fun w => (bellmanAngularPoint w).val
  have hk : IsCompact K := by
    apply IsCompact.prod _ hcφ
    apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hcζ
    aesop
  have hPK := hk.image (continuous_subtype_val.comp continuous_bellmanAngularPoint)
  have hin : Function.support (bellmanAngularTest ζ φ) ⊆ P '' K := by
    intro q hq
    have hx : 0 < q.1 := by
      by_contra hn
      exact hq (ite_eq_right hn)
    let w := bellmanAngularHomeomorph.symm ⟨q, hx⟩
    have he := bellmanAngularPoint_inverse q hx
    have hm : ζ (bellmanTestRadius q) * φ (bellmanTestAngle q) ≠ 0 := by
      simpa [bellmanAngularTest, ite_eq_left hx, bellmanSeparatedExpression] using hq
    refine ⟨w, ?_, he⟩
    constructor
    · exact subset_tsupport ζ ((mul_ne_zero_iff.mp hm).1)
    · exact subset_tsupport φ ((mul_ne_zero_iff.mp hm).2)
  have hts :=
    closure_minimal hin hPK.isClosed
  refine ⟨hPK.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans ?_⟩
  rintro q ⟨w, _, rfl⟩
  exact pow_pos w.1.property 3

/-- Compact angular tests with positive radial support satisfy the punctured-test support
rule. -/
theorem bellmanAngularTest_support_punctured :
    tsupport (bellmanAngularTest ζ φ) ⊆ {q : ℝ × ℝ | q ≠ (0, 0)} := by
  intro q hq he
  have hx := (bellmanAngularTest_support_data ζ φ hcζ hcφ hs).2 hq
  grind

end HypoellipticAleksandrov.KineticAleksandrov
