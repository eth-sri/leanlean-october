
import GS.UnitaryLocalModel.TopologyOuter
import GS.UnitaryLocalModel.AxisConjugation
import GS.UnitaryLocalModel.FactorSpace




/-!
# Feasibility and the distinguished point of the full local model

Every point of the compact normalized model is in the original scalar-shuffle
unitary family. The proof uses simultaneous diagonalization of the Pauli axis
and does not change the ambient matrix indexing or topology.
-/
noncomputable section
open Matrix GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel

variable (Q : CMat q)

/-- The scalar-block point associated with a middle unitary matrix. -/
def scalarBlockBase  : CMat (q*2) :=
  flattenBlockFamily (fun i j => Q i j • (1 : CMat 2))

/-- All outer factors at the scalar-block point are identities. -/
def identityOuter (q : ℕ) (o : Fin q) : OuterFactors q o :=
  (fun _ => 1,fun _ => 1)





/-- A fixed sphere representative of the collapsed central fibre. -/
def parameterZero (d : ℕ) : LocalParameters d := (0,0,![1,0,0])

theorem parameterZero_mem (d : ℕ) (r : ℝ) : parameterZero d ∈ localParameterBox d r := by
  simp [parameterZero,localParameterBox,localEnergy,OnSphere,sq_nonneg]

@[simp] theorem parameterCone_zero (d : ℕ) :
    parameterCone (parameterZero d) = coneCoordinatesZero d := by aesop (add norm [sphereOuter,parameterCone,parameterZero])

def fullParameterZero (q d : ℕ) (o : Fin q) (r : ℝ) : FullCompactParameters q o d r :=
  (identityOuter q o,⟨parameterZero d,parameterZero_mem d r⟩)

@[simp] theorem fullCompactMiddle_zero (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ) :
    fullCompactMiddle ψ o r (fullParameterZero q d o r) = scalarBlockBase (ψ 0) := by simp_all [chartMiddle,middleBlock_equal,parameterMiddle,fullParameterZero,identityOuter,parameterZero,scalarBlockBase,chartBlockFamily,fullBlockImage,fullCompactMiddle,outerLeft,outerRight]

theorem fullBlockImage_mem_localFamily {o : Fin q}
    (ψ : (Fin d → ℝ) → CMat q) (g : OuterFactors q o) (p : LocalParameters d)
    (hp : GS.Unitary (ψ (p.1+p.2.1))) (hm : GS.Unitary (ψ (p.1-p.2.1)))
    (hu : OnSphere p.2.2) :
    fullBlockImage ψ g p ∈ GS.UnitaryNonmanifold.localFamily q := by
  obtain ⟨S,hS,hdiag⟩ := middleBlock_unitary_diagonalization p.2.2 hu
  let v :=
    (fun i => outerLeft g i*Sᴴ, ψ (p.1+p.2.1), ψ (p.1-p.2.1),
      fun j => S*outerRight g j)
  have hv : v ∈ smallFactorSet q :=
    ⟨fun i => (outerLeft_unitary g i).mul hS.conjTranspose,hp,hm,
      fun j => hS.mul (outerRight_unitary g j)⟩
  have he : smallFactorMap v = fullBlockImage ψ g p := by
    apply (blockFamilyHomeomorph q).symm.injective
    change extractBlockFamily (smallFactorMap v) = extractBlockFamily (fullBlockImage ψ g p)
    unfold fullBlockImage
    rw [extract_flattenBlockFamily]
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
  exact ⟨v,hv,rfl⟩

theorem scalarBlockBase_mem_localFamily  (hQ : GS.Unitary Q)
    (o : Fin q) : scalarBlockBase Q ∈ GS.UnitaryNonmanifold.localFamily q := by
  have h := fullBlockImage_mem_localFamily (d := 0) (fun _ => Q)
    (identityOuter q o) (parameterZero 0) hQ hQ (by simp [parameterZero,OnSphere])
  have he := fullCompactMiddle_zero (d := 0) (fun _ => Q) o 0
  
  exact he ▸ h

end GS.UnitaryLocalModel
