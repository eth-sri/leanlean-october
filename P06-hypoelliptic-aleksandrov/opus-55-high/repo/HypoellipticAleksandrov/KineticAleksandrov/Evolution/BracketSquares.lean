module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketLie

/-!
# The sum-of-squares identity `Lop = X_0 + ∑ X_i²`

For `u` of class `C²` at `x`, the first-order operators `X_0, X_i` (and `Y_l`) satisfy, in the
packed coordinates `x = (σ, v, z)`,

`X_0 u + ∑_i X_i (X_i u) = ∂_σ u + B(σ,v,z) : D_v² u + b(v) · ∇_z u`

(Proposition 2.1), and, adding the constant fields `Y_l = √ε ∂_{z_l}`,
`X_0 u + ∑ X_i² u + ∑ Y_l² u = Lop u + ε Δ_z u` (Proposition 2.1).
No `z`-derivative falls on `β` in `X_i`, so the identity holds also when `B` depends on `z`.
-/

@[expose] public section

noncomputable section

open scoped MatrixOrder Matrix

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

variable {n : ℕ}

/-- The unit time direction `∂_σ`. -/
def basisT : EvolutionVec n := packPoint 1 0 0

/-- The unit diffused direction `∂_{v_j}`. -/
def basisV (j : Fin n) : EvolutionVec n := packPoint 0 (Pi.single j 1) 0

/-- The unit transported direction `∂_{z_l}`. -/
def basisZ (l : Fin n) : EvolutionVec n := packPoint 0 0 (Pi.single l 1)

section Algebra

variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}

/-- `∑_i β_ij β_ik = B_jk`: the square-root factorisation (uses symmetry of `β`). -/
theorem sum_sqrtCoeffAt_mul {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : HasEverywhereLoewnerBounds lam Lam B) (x : EvolutionVec n) (j k : Fin n) :
    ∑ i, sqrtCoeffAt B x i j * sqrtCoeffAt B x i k =
      B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) j k := by
  set A := B _ _ _ with hA
  have hApd : A.PosDef := posDef_of_smul_one_le hlam (hell _ _ _).1
  have hsq : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hApd.posSemidef.nonneg
  have hsymm : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq
  have hsymm' : ∀ i j, CFC.sqrt A i j = CFC.sqrt A j i := fun i j => by
    have := congrFun (congrFun hsymm j) i
    simp_all
  have := congrFun (congrFun hsq j) k
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [sqrtCoeffAt]
  simp_all

/-- The transported operator `Lop = ∂_σ + B(σ,v,z) : D_v² + b(v) · ∇_z` in packed
coordinates (`B_ij ∂_{v_i} ∂_{v_j} u`, with the same index convention as
`transportedForwardOperator`). -/
def transportedOperator (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (u : EvolutionVec n → ℝ) (x : EvolutionVec n) : ℝ :=
  fderiv ℝ u x basisT +
    ∑ i, ∑ j, B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j *
      fderiv ℝ (fun y => fderiv ℝ u y (basisV j)) x (basisV i) +
    ∑ l, b (diffusedCoord n x) l * fderiv ℝ u x (basisZ l)

/-- The regularised operator `L_ε = Lop + ε Δ_z` in packed coordinates. -/
def regularizedOperator (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (ε : ℝ)
    (u : EvolutionVec n → ℝ) (x : EvolutionVec n) : ℝ :=
  transportedOperator B b u x +
    ε * ∑ l, fderiv ℝ (fun y => fderiv ℝ u y (basisZ l)) x (basisZ l)

end Algebra

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
