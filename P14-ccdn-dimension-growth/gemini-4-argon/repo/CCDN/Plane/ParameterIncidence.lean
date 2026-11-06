/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.UniversalPlaneSpecialization

/-! Exact incidence averaging over every affine-plane parameter triple,
including degenerate triples. No divisibility correction for plane charts
is needed because points and directions are kept as coordinates. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- All plane coordinates whose image lies on the hypersurface. -/
def PlaneSectionPoints {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (v : PlaneParameters σ → K) :=
  {t : Fin 2 → K // bivariateEval (t 0) (t 1) (universalPlaneSection f v) = 0}

/-- The section counts sum to the exact incidence count. -/
theorem sum_planeSectionPoints_card {K σ : Type*} [CommRing K] [Fintype K] [Fintype σ]
    [DecidableEq σ] (f : MvPolynomial σ K) :
    ∑ v : PlaneParameters σ → K, Nat.card (PlaneSectionPoints f v) =
      Nat.card {z : σ → K // eval z f = 0} * Fintype.card K ^ (2 * Fintype.card σ + 2) := by
  classical
  let e₁ : {vt : (PlaneParameters σ → K) × (Fin 2 → K) //
      bivariateEval (vt.2 0) (vt.2 1) (universalPlaneSection f vt.1) = 0} ≃
      Σ v, PlaneSectionPoints f v :=
    ⟨fun vt => ⟨vt.val.1, ⟨vt.val.2, vt.property⟩⟩,
     fun vt => ⟨(vt.1, vt.2.val), vt.2.property⟩, fun _ => rfl, fun _ => rfl⟩
  let e₂ : {vt : (PlaneParameters σ → K) × (Fin 2 → K) //
      bivariateEval (vt.2 0) (vt.2 1) (universalPlaneSection f vt.1) = 0} ≃
      ({z : σ → K // eval z f = 0} × (σ → K) × (σ → K) × (Fin 2 → K)) :=
    { toFun vt :=
        (⟨fun i => vt.val.1 (i,0) + vt.val.1 (i,1) * vt.val.2 0 + vt.val.1 (i,2) * vt.val.2 1,
          by rw [← universalPlaneSection_eval]; exact vt.property⟩,
          fun i => vt.val.1 (i,1), fun i => vt.val.1 (i,2), vt.val.2)
      invFun z :=
        ⟨(fun i => ![z.1.val i.1 - z.2.1 i.1 * z.2.2.2 0 - z.2.2.1 i.1 * z.2.2.2 1,
            z.2.1 i.1, z.2.2.1 i.1] i.2, z.2.2.2), by
          rw [universalPlaneSection_eval]
          convert z.1.property using 1
          congr 2; funext i; simp; ring⟩
      left_inv vt := Subtype.ext <| Prod.ext
        (funext fun ⟨i, j⟩ => by fin_cases j <;> simp; ring) rfl
      right_inv z := Prod.ext (Subtype.ext <| funext fun i => by simp; ring) rfl }
  let (v : PlaneParameters σ → K) : Fintype (PlaneSectionPoints f v) :=
    inferInstanceAs (Fintype {t : Fin 2 → K //
      bivariateEval (t 0) (t 1) (universalPlaneSection f v) = 0})
  have h := Nat.card_congr (e₁.symm.trans e₂)
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin] at h ⊢
  rw [h, ← pow_add, ← pow_add]
  congr 2
  omega

end
end CCDN
