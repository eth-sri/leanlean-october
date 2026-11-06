module

public import GS.UnitaryLocalModel.TopologyOuter
public import GS.UnitaryLocalModel.AxisConjugation
public import GS.UnitaryLocalModel.FactorSpace

@[expose] public section


/-!
# Feasibility and the distinguished point of the full local model

Every point of the compact normalized model is in the original scalar-shuffle
unitary family. The proof uses simultaneous diagonalization of the Pauli axis
and does not change the ambient matrix indexing or topology.
-/
noncomputable section
open Matrix GS GS.UnitaryManifold GS.UnitaryNonmanifold GS.NonmanifoldCompletion
namespace GS.UnitaryLocalModel

/-- The scalar-block point associated with a middle unitary matrix. -/
def scalarBlockBase {q : ℕ} (Q : CMat q) : CMat (q*2) :=
  flattenBlockFamily (fun i j => Q i j • (1 : CMat 2))

section
variable (q : ℕ)
/-- All outer factors at the scalar-block point are identities. -/
def identityOuter (o : Fin q) : OuterFactors q o :=
  (fun _ => 1,fun _ => 1)

@[simp] theorem identityOuter_left (o i : Fin q) :
    outerLeft (identityOuter q o) i = 1 := rfl

@[simp] theorem identityOuter_right (o j : Fin q) :
    outerRight (identityOuter q o) j = 1 := by
  unfold outerRight identityOuter
  simp

end

section
variable (d : ℕ)
/-- A fixed sphere representative of the collapsed central fibre. -/
def parameterZero : LocalParameters d := (0,0,![1,0,0])

theorem parameterZero_mem (r : ℝ) : parameterZero d ∈ localParameterBox d r := by
  simp [parameterZero,localParameterBox,localEnergy,OnSphere,sq_nonneg]

@[simp] theorem parameterCone_zero :
    parameterCone (parameterZero d) = coneCoordinatesZero d := by
  refine Prod.ext ?_ ?_
  · rfl
  · ext i j
    simp [parameterCone,parameterZero,coneCoordinatesZero,sphereOuter]

end

def fullParameterZero (q d : ℕ) (o : Fin q) (r : ℝ) : FullCompactParameters q o d r :=
  (identityOuter q o,⟨parameterZero d,parameterZero_mem d r⟩)

section
variable {q d : ℕ}
@[simp] theorem fullCompactMiddle_zero (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ) :
    fullCompactMiddle ψ o r (fullParameterZero q d o r) = scalarBlockBase (ψ 0) := by
  unfold fullCompactMiddle fullBlockImage scalarBlockBase
  simp [fullParameterZero,chartBlockFamily,parameterMiddle,chartMiddle,parameterZero,
    middleBlock_equal]

theorem fullBlockImage_mem_localFamily {o : Fin q}
    (ψ : (Fin d → ℝ) → CMat q) (g : OuterFactors q o) (p : LocalParameters d)
    (hp : GS.Unitary (ψ (p.1+p.2.1))) (hm : GS.Unitary (ψ (p.1-p.2.1)))
    (hu : OnSphere p.2.2) :
    fullBlockImage ψ g p ∈ sFamily ℂ q := by
  obtain ⟨S,hS,hdiag⟩ := middleBlock_unitary_diagonalization p.2.2 hu
  let v : SmallBlockParameters ℂ q :=
    (fun i => outerLeft g i*Sᴴ, ψ (p.1+p.2.1), ψ (p.1-p.2.1),
      fun j => S*outerRight g j)
  have hv : v ∈ smallFactorSet ℂ q :=
    ⟨fun i => (outerLeft_unitary g i).mul hS.conjTranspose,hp,hm,
      fun j => hS.mul (outerRight_unitary g j)⟩
  have he : smallFactorMap v = fullBlockImage ψ g p := by
    apply (blockFamilyHomeomorph q).symm.injective
    change extractBlockFamily (smallFactorMap v) = extractBlockFamily (fullBlockImage ψ g p)
    unfold fullBlockImage
    simp
    funext i j a b
    change smallFactorMap v (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b)) = _
    rw [smallFactorMap_block]
    change ((outerLeft g i*Sᴴ)*diagTwo (ψ (p.1+p.2.1) i j) (ψ (p.1-p.2.1) i j)*
      (S*outerRight g j)) a b =
      (outerLeft g i*middleBlock (ψ (p.1+p.2.1) i j) (ψ (p.1-p.2.1) i j) p.2.2*
        outerRight g j) a b
    rw [← hdiag]
    simp only [Matrix.mul_assoc]
  rw [← he, ← image_smallFactorMap]
  grind

end

end GS.UnitaryLocalModel
