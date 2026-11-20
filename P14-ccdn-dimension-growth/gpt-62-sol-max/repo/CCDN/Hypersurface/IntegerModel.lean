/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import CCDN.Height.Box
public import CCDN.Algebra.PolynomialPredicates
import CCDN.Algebra.PrimitiveNormalization
import CCDN.ForMathlib.MvPolynomial
import CCDN.Surface.TopFormIrreducibility

/-! Integer models for rational equations with absolutely irreducible top form. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
local notation "Qbar" => AlgebraicClosure ℚ

/-- A rational polynomial whose top-degree form is absolutely irreducible has an integer model of
the same total degree, also with absolutely irreducible top-degree form, that has the same
integer zeros. -/
theorem exists_integer_model_absolute_top {n : ℕ} (f : MvPolynomial (Fin n) ℚ)
    (hir : Irreducible (map (algebraMap ℚ Qbar) (homogeneousComponent f.totalDegree f))) :
    ∃ g : MvPolynomial (Fin n) ℤ,
      g.totalDegree = f.totalDegree ∧
      Irreducible (map (Int.castRingHom Qbar) (homogeneousComponent g.totalDegree g)) ∧
      ∀ x : Fin n → ℤ, eval x g = 0 ↔ eval (fun i => (x i : ℚ)) f = 0 := by
  have hf : f ≠ 0 := by
    aesop
  obtain ⟨g, hg⟩ := exists_integer_model f
  obtain ⟨r, hr, he⟩ := rational_model_eq_C_mul hg
  have hdegree := rational_model_degree hg hf
  let φ := algebraMap ℚ Qbar
  have hφ : φ.comp (Int.castRingHom ℚ) = Int.castRingHom Qbar := by
    ext z
    simp
  have hmodel : map (Int.castRingHom Qbar) g = C (φ r) * map φ f := by
    have hh := congrArg (map φ) he
    simpa [map_mul, map_C, map_map, hφ] using hh
  have htop : map (Int.castRingHom Qbar) (homogeneousComponent g.totalDegree g) =
      C (φ r) * map φ (homogeneousComponent f.totalDegree f) := by
    rw [map_homogeneousComponent, hmodel, homogeneousComponent_C_mul,
      hdegree, ← map_homogeneousComponent]
  refine ⟨g, hdegree, ?_, ?_⟩
  · rw [htop]
    exact (irreducible_isUnit_mul ((hr.map φ).map C)).mpr hir
  · intro x
    have hh := rational_model_zero_iff hg (fun i => (x i : ℚ))
    exact (eval_rationalPoint_map_eq_zero x g).symm.trans hh

end
end CCDN
