module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import PottsDiscontinuity.Torus.DiamondGraph

/-!
# Indexed primal chains on the torus

The incidence matrix retains each indexed open edge, including parallel edges and
edges with identified endpoints. Its kernel is the actual space of conserved flows.
This is the chain model for the forthcoming winding-based net characterization.
-/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

section
variable (A : RCConfig N M)
/-- The full indexed open-edge carrier; no quotient by endpoint pairs is taken. -/
abbrev OpenDiamondEdge  := {v : Fin N × Fin M // A v = true}

theorem card_openDiamondEdge  :
    Fintype.card (OpenDiamondEdge A) = openCount A :=
  Fintype.card_subtype _
end

section
variable (hN : Even N) (hM : Even M) (A : RCConfig N M)
/-- Signed incidence: each indexed edge points from endpoint false to endpoint true. -/
def diamondIncidence  :
    Matrix (FaceVertex N M true) (OpenDiamondEdge A) ℚ :=
  fun u e => (if faceEndpoint hN hM true e.val true = u then 1 else 0) -
    if faceEndpoint hN hM true e.val false = u then 1 else 0

/-- Boundary of an indexed rational one-chain. -/
def diamondBoundary  :
    (OpenDiamondEdge A → ℚ) →ₗ[ℚ] (FaceVertex N M true → ℚ) :=
  Matrix.toLin' (diamondIncidence hN hM A)

/-- The potential difference across each open indexed edge. -/
def diamondCoboundary  :
    (FaceVertex N M true → ℚ) →ₗ[ℚ] (OpenDiamondEdge A → ℚ) where
  toFun f e := f (faceEndpoint hN hM true e.val true) - f (faceEndpoint hN hM true e.val false)
  map_add' f g := by ext e; simp only [Pi.add_apply]; ring
  map_smul' c f := by ext e; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem diamondCoboundary_apply (f : FaceVertex N M true → ℚ) (e : OpenDiamondEdge A) :
    diamondCoboundary hN hM A f e =
      f (faceEndpoint hN hM true e.val true) - f (faceEndpoint hN hM true e.val false) := rfl

/-- Conserved indexed flows on the actual open primal subgraph. -/
def diamondCycleSpace  :
    Submodule ℚ (OpenDiamondEdge A → ℚ) := LinearMap.ker (diamondBoundary hN hM A)
end

end PottsDiscontinuity.Torus
