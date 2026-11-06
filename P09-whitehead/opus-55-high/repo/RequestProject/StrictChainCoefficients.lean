import RequestProject.StrictOrderChains
import RequestProject.OrderNerveDictionary
import RequestProject.Tac


/-! Normalization preserves the coefficients of all genuine order simplices. -/

bwd

namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

noncomputable def ordTriangleCoefficient (t : OrdTri P) : Nerve.Ch P →+ ℤ := by
  classical
  exact FreeAbelianGroup.lift (fun l =>
    if l = [t.1.1, t.1.2.1, t.1.2.2] then 1 else 0)

/-- Reading a flag coefficient in the full nerve agrees with reading its cellular coordinate. -/
theorem ordTriangleCoefficient_encode t (c : OrdTri P →₀ ℤ) :
    ordTriangleCoefficient t (ordNerveChain2 c) = c t := by
  classical
  lin_ind c w n =>
    have he : [w.1.1, w.1.2.1, w.1.2.2] = [t.1.1, t.1.2.1, t.1.2.2] ↔ w = t := by
      constructor
      · intro h
        apply Subtype.ext
        grind
      simp_all
    simp [ordNerveChain2, ordTriangleCoefficient, FreeAbelianGroup.lift_apply_of,
      Finsupp.single_apply, he]

theorem normalizeOrdChain2_apply c t :
    normalizeOrdChain2 c t = c ((strictOrderIncl P).onF t) := by
  classical
  lin_ind c w n =>
    by_cases hw : w.1.1 < w.1.2.1 ∧ w.1.2.1 < w.1.2.2
    · have he : ⟨w.1, hw⟩ = t ↔ w = (strictOrderIncl P).onF t := by
        aesop
      simp [normalizeOrdTriangle, hw, Finsupp.single_apply, he]
    · have he : w ≠ (strictOrderIncl P).onF t := by
        intro h
        apply hw
        simpa [h, strictOrderIncl] using t.2
      simp [normalizeOrdTriangle, hw, he]
