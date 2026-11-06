module

public import QPBT.Algebra.LowDegreeCode

/-! # Decoding maps for the low-degree code

This file supplies `def:decoding-map` and the Boolean cube embedding from
`def:decoding-map`, paper
`references/qpbt-paper/04_preliminaries.tex:917-924`.  The specialization to
polynomial representatives is `decodeFqRep`; its restriction to the bounded
class `Poly` is defined in `Algebra/Decoding`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.LDT.Preliminaries

variable {K : Type*} [Field K]

/-- The formalization-only embedding of Boolean coordinates into a field used by
blueprint `def:decoding-map`, paper
`04_preliminaries.tex:917-924`. -/
def boolToScalar : Bool → K
  | false => 0
  | true => 1

/-- The coordinatewise Boolean-cube embedding used by
blueprint `def:decoding-map`, paper
`04_preliminaries.tex:917-924`. -/
def cubeEmbed {m : ℕ} : Cube m → (Fin m → K) :=
  fun y i => boolToScalar (y i)

/-- On the Boolean cube, an indicator polynomial evaluates to the corresponding
Kronecker delta.  This is the interpolation observation at paper lines 880-891. -/
theorem eval_indicatorPoly_cubeEmbed {m : ℕ}
    (y z : Cube m) :
    MvPolynomial.eval (cubeEmbed (K := K) z) (indicatorPoly (K := K) y) =
      if y = z then 1 else 0 := by
  rw [indicatorPoly, MvPolynomial.eval_prod]
  simp only [apply_ite, MvPolynomial.eval_X, MvPolynomial.eval_sub, map_one]
  have hfactor (i : Fin m) :
      (if y i then cubeEmbed (K := K) z i else 1 - cubeEmbed (K := K) z i) =
        if y i = z i then 1 else 0 := by
    cases hy : y i <;> cases hz : z i <;> simp_all [cubeEmbed, boolToScalar]
  simp_rw [hfactor]
  simp [Fintype.prod_boole, funext_iff]

/-- Evaluating a low-degree encoding at an embedded Boolean point recovers its
coefficient at that point, as stated at paper line 891. -/
theorem lowDegreeEnc_cubeEmbed {m : ℕ}
    (a : Cube m → K) (z : Cube m) :
    lowDegreeEnc a (cubeEmbed z) = a z := by
  simp [lowDegreeEnc_eq_dotProduct, dotProduct, indicatorVec, eval_indicatorPoly_cubeEmbed]

/-- The decoding map blueprint
`def:decoding-map`, paper `04_preliminaries.tex:917-924`. -/
noncomputable def decodeAt [DecidableEq K] {m : ℕ}
    (H : Finset K) (g : (Fin m → K) → K) : Cube m → K :=
  fun y => if g (cubeEmbed y) ∈ H then g (cubeEmbed y) else 0

/-- The restricted decoding identity in blueprint
`def:decoding-map`, paper `04_preliminaries.tex:917-924`. -/
theorem decodeAt_lowDegreeEnc [DecidableEq K] {m : ℕ}
    (H : Finset K) (a : Cube m → K) (ha : ∀ y, a y ∈ H) :
    decodeAt H (lowDegreeEnc a) = a := by
  grind [decodeAt, lowDegreeEnc_cubeEmbed]

end MIPStarRE.QPBT
