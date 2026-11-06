import Mathlib.Tactic

import GS.UnitaryLocalModel.TopologyCompact
import GS.UnitaryManifold.BlockGroup




/-!
# Compact outer coordinates for the unitary local model

All outer unitary factors are retained. Only the right anchor factor is fixed
to the identity. Their product with the compact middle-coordinate box is
compact, and the output is an actual scalar-indexed matrix in the original
ambient topology.
-/

noncomputable section
open GS.UnitaryManifold
namespace GS.UnitaryLocalModel

abbrev BlockFamily (q : ℕ) := Fin q → Fin q → CMat 2

def flattenBlockFamily (N : BlockFamily q) := fun i j =>
    let x := finProdFinEquiv.symm i
    let y := finProdFinEquiv.symm j
    N x.1 y.1 x.2 y.2

def extractBlockFamily (M : CMat (q*2)) := fun i j a b => M (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b))

@[simp] theorem extract_flattenBlockFamily (N : BlockFamily q) :
    extractBlockFamily (flattenBlockFamily N) = N := by grind [extractBlockFamily,flattenBlockFamily]

@[simp] theorem flatten_extractBlockFamily (M : CMat (q*2)) :
    flattenBlockFamily (extractBlockFamily M) = M := by
  ext i j
  change M (finProdFinEquiv (finProdFinEquiv.symm i))
    (finProdFinEquiv (finProdFinEquiv.symm j)) = M i j
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem continuous_flattenBlockFamily (q : ℕ) : Continuous (@flattenBlockFamily q) := by
  unfold flattenBlockFamily
  fun_prop

theorem continuous_extractBlockFamily (q : ℕ) : Continuous (@extractBlockFamily q) := by
  unfold extractBlockFamily
  fun_prop

/-- The block array and scalar matrix spaces have their unchanged topologies. -/
def blockFamilyHomeomorph (q : ℕ) : BlockFamily q ≃ₜ CMat (q*2) where
  toFun := flattenBlockFamily
  invFun := extractBlockFamily
  left_inv := extract_flattenBlockFamily
  right_inv := flatten_extractBlockFamily
  continuous_toFun := continuous_flattenBlockFamily q
  continuous_invFun := continuous_extractBlockFamily q

def asFullUnitary {n : ℕ} (U : CMat n) (hU : GS.Unitary U) :
    BlockU (fun _ : Fin n => 0) :=
  ⟨U,by tauto,hU⟩

abbrev OuterFactors (q : ℕ) (o : Fin q) :=
  (Fin q → BlockU (fun _ : Fin 2 => 0)) ×
    ({j : Fin q // j ≠ o} → BlockU (fun _ : Fin 2 => 0))

def outerLeft {o : Fin q} (g : OuterFactors q o) (i : Fin q) := (g.1 i).val

def outerRight {o : Fin q} (g : OuterFactors q o) (j : Fin q) := if h : j = o then 1 else (g.2 ⟨j,h⟩).val

theorem outerLeft_unitary {o : Fin q} (g : OuterFactors q o) (i : Fin q) :
    GS.Unitary (outerLeft g i) := (g.1 i).property.2

theorem outerRight_unitary {o : Fin q} (g : OuterFactors q o) (j : Fin q) :
    GS.Unitary (outerRight g j) := by
  unfold outerRight
  split
  · exact GS.MatrixBase.Unitary.one
  · exact (g.2 _).property.2

@[simp] theorem outerRight_anchor {o : Fin q} (g : OuterFactors q o) :
    outerRight g o = 1 := by simp [outerRight]

def outerOfMatrices {o : Fin q} (L R : Fin q → CMat 2)
    (hL : ∀ i, GS.Unitary (L i)) (hR : ∀ j, GS.Unitary (R j)) : OuterFactors q o :=
  (fun i => asFullUnitary (L i) (hL i), fun j => asFullUnitary (R j.val) (hR j.val))





theorem continuous_outerLeft (q : ℕ) (o : Fin q) :
    Continuous (@outerLeft q o) := by
  unfold outerLeft
  fun_prop

theorem continuous_outerRight (q : ℕ) (o : Fin q) :
    Continuous (@outerRight q o) := by
  apply continuous_pi
  intro j
  by_cases hj : j = o
  · continuity
  · simp only [outerRight,dif_neg hj]
    fun_prop

def chartBlockFamily (ψ : (Fin d → ℝ) → CMat q)
    (p : LocalParameters d) := fun i j => parameterMiddle (fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2) p (i,j)

def fullBlockImage {o : Fin q} (ψ : (Fin d → ℝ) → CMat q)
    (g : OuterFactors q o) (p : LocalParameters d) := flattenBlockFamily (fun i j => outerLeft g i * chartBlockFamily ψ p i j * outerRight g j)

abbrev FullCompactParameters (q : ℕ) (o : Fin q) (d : ℕ) (r : ℝ) :=
  OuterFactors q o × localParameterBox d r

def fullCompactMiddle (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ)
    (p : FullCompactParameters q o d r) := fullBlockImage ψ p.1 p.2.val

abbrev FullCompactImage (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ) :=
  Set.range (fullCompactMiddle ψ o r)

instance fullCompactParameters_compactSpace (q : ℕ) (o : Fin q) (d : ℕ) (r : ℝ) :
    CompactSpace (FullCompactParameters q o d r) := by
  letI :=
    isCompact_iff_compactSpace.mp (isCompact_localParameterBox d r)
  exact inferInstance

end GS.UnitaryLocalModel
