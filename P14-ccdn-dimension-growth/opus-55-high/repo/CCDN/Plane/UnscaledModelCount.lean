/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Plane.ScaledModelCoordinates
import CCDN.Plane.ScaledPlaneCount
import CCDN.Algebra.HomogeneousSlice
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.AuxiliaryPolynomial.PolynomialMapAuxiliary
import CCDN.Plane.ScaledModelPosition

/-! The unit-scaled model gives a coefficient-uniform 2/d fallback and a
large-coefficient O(d^4) count, without requiring a scaling prime. -/

namespace CCDN
open MvPolynomial Real

/-- The homogenization (with scaling factor `1`) of a primitive integer polynomial is
primitive. -/
lemma PrimitiveIntegerPolynomial.scaledHomogenize_one {n : ℕ}
    {f : MvPolynomial (Fin n) ℤ} (hf : PrimitiveIntegerPolynomial f) (d : ℕ) :
    PrimitiveIntegerPolynomial (CCDN.scaledHomogenize d 1 f) := by
  intro c hc
  apply hf c
  intro m
  have h := hc (homogenizedExponent d m)
  simpa [scaledHomogenize_coefficient, one_pow, one_mul] using h

lemma unscaled_positioned_points_card_le {M t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f))
    (a : Fin 2 → ℤ) (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    (hz : ∀ i, eval (z i) f = 0) (g : MvPolynomial (Fin 3) ℤ)
    (hg : IsPointAuxiliary (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree 1 f))
      g M (fun i j => eval (z i) (scaledModelCoordinates 1 a j))) :
    t ≤ f.totalDegree * M := by
  obtain ⟨g', hg', he, hnd'⟩ := scaledModelCoordinates_auxiliary_transport 1 a f g
    hg.isHomogeneous hg.not_dvd
  have hf0 : f ≠ 0 := fun h => hir.ne_zero (by grind)
  have hchart : affineChart 2 (scaledHomogenize f.totalDegree 1 f) = f := by
    change homogeneousSlice 2 1 (scaledHomogenize f.totalDegree 1 f) = f
    simp [homogeneousSlice_scaledHomogenize 1 f le_rfl, one_pow, map_one, one_mul]
  have hh := plane_chart_points_card_le_auxiliary_degree (scaledHomogenize f.totalDegree 1 f) g'
    (scaledHomogenize_homogeneous _ _ le_rfl) (scaledHomogenize_ne_zero _ one_ne_zero hf0)
    hg' (hprim.scaledHomogenize_one _) (by grind) (by grind) hnd' z hinj
    (by grind) (fun i => (he (z i)).trans (hg.eval_eq_zero i))
  exact hh

