module

public import GS.UnitaryLocalModel.PolarTwo
public import GS.UnitaryLocalModel.ChartFibres

@[expose] public section


/-!
# Exact fibres including the normalized outer unitary factors

Positive first-row and first-column middle blocks determine every outer unitary
factor, once the right anchor is fixed to the identity. The residual equality
is exactly equality of the complete middle family. These statements retain
all outer factors and do not restrict the image to a selected middle slice.
-/
noncomputable section
open Matrix
open scoped ComplexOrder
namespace GS.UnitaryLocalModel

variable {q : ℕ}

/-- Reconstruct the entire block array from normalized factors. -/
def normalizedBlockImage (L R : Fin q → CMat 2)
    (N : Fin q → Fin q → CMat 2) : Fin q → Fin q → CMat 2 :=
  fun i j => L i * N i j * R j

/-- Positivity is measured relative to the reference anchor entries. -/
def NormalizedPositiveAnchors (Q : CMat q) (o : Fin q)
    (N : Fin q → Fin q → CMat 2) : Prop :=
  (∀ i, ((Q i o)⁻¹ • N i o).PosDef) ∧
  (∀ j, ((Q o j)⁻¹ • N o j).PosDef)

section
variable (Q : CMat q) (o : Fin q) (L R L' R' : Fin q → CMat 2) (N N' : Fin q → Fin q → CMat 2)
/-- The full normalized fibre relation, including all outer coordinates. -/
theorem normalized_outer_fibres_iff (hL : ∀ i, GS.Unitary (L i)) (hR : ∀ j, GS.Unitary (R j))
    (hL' : ∀ i, GS.Unitary (L' i)) (hR' : ∀ j, GS.Unitary (R' j))
    (hRo : R o = 1) (hRo' : R' o = 1)
    (hN : NormalizedPositiveAnchors Q o N)
    (hN' : NormalizedPositiveAnchors Q o N') :
    normalizedBlockImage L R N = normalizedBlockImage L' R' N' ↔
      L = L' ∧ R = R' ∧ N = N' := by
  refine ⟨fun he => ?_, by grind⟩
  have hb (i j : Fin q) : L i * N i j * R j = L' i * N' i j * R' j := congrFun₂ he i j
  have cl {U A B : CMat 2} (hU : GS.Unitary U) (he : U*A = U*B) : A = B := by
    simpa only [← Matrix.mul_assoc, hU.1, Matrix.one_mul] using congrArg (Uᴴ * ·) he
  have cr {U A B : CMat 2} (hU : GS.Unitary U) (he : A*U = B*U) : A = B := by
    simpa only [Matrix.mul_assoc, hU.2, Matrix.mul_one] using congrArg (· * Uᴴ) he
  obtain rfl : L = L' := funext fun i => (positive_polar_unique _ _ _ _ (hL i) (hL' i) (hN.1 i) (hN'.1 i)
    (by have := hb i o; simp_all)).1
  obtain rfl : R = R' := funext fun j => (positive_polar_unique_right _ _ _ _ (hR j) (hR' j) (hN.2 j)
    (hN'.2 j) (by have := cl (hL o) (by simpa [Matrix.mul_assoc] using hb o j); simp_all)).1
  exact ⟨rfl, rfl, funext₂ fun i j => cl (hL i) (cr (hR j) (hb i j))⟩

end

/-- Exact outer-plus-cone coordinates after any injective local middle chart. -/
theorem normalized_chart_fibres_on {d : ℕ}
    (Q : CMat q) (o : Fin q)
    (ψ : (Fin d → ℝ) → (Fin q × Fin q → ℂ))
    (U : Set (Fin d → ℝ)) (hψ : Set.InjOn ψ U)
    (L R L' R' : Fin q → CMat 2) (c z c' z' : Fin d → ℝ)
    (u v : AxisVector)
    (hL : ∀ i, GS.Unitary (L i)) (hR : ∀ j, GS.Unitary (R j))
    (hL' : ∀ i, GS.Unitary (L' i)) (hR' : ∀ j, GS.Unitary (R' j))
    (hRo : R o = 1) (hRo' : R' o = 1)
    (hcp : c+z ∈ U) (hcm : c-z ∈ U)
    (hcp' : c'+z' ∈ U) (hcm' : c'-z' ∈ U)
    (hu : OnSphere u) (hv : OnSphere v)
    (hN : NormalizedPositiveAnchors Q o (fun i j => chartMiddle ψ c z u (i,j)))
    (hN' : NormalizedPositiveAnchors Q o (fun i j => chartMiddle ψ c' z' v (i,j))) :
    normalizedBlockImage L R (fun i j => chartMiddle ψ c z u (i,j)) =
        normalizedBlockImage L' R' (fun i j => chartMiddle ψ c' z' v (i,j)) ↔
      L = L' ∧ R = R' ∧ c = c' ∧ sphereOuter u z = sphereOuter v z' := by
  rw [normalized_outer_fibres_iff Q o L R L' R' _ _ hL hR hL' hR' hRo hRo' hN hN',
    ← chartMiddle_fibres_on ψ U hψ c z c' z' hcp hcm hcp' hcm' hu hv]
  simp [funext_iff]

end GS.UnitaryLocalModel
