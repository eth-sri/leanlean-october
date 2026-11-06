module

public import GS.UnitaryLocalModel.TopologyCompact
public import GS.UnitaryManifold.BlockGroup

@[expose] public section


/-!
# Compact outer coordinates for the unitary local model

All outer unitary factors are retained. Only the right anchor factor is fixed
to the identity. Their product with the compact middle-coordinate box is
compact, and the output is an actual scalar-indexed matrix in the original
ambient topology.
-/

noncomputable section
open Matrix GS GS.UnitaryManifold
namespace GS.UnitaryLocalModel

abbrev BlockFamily (q : ℕ) := Fin q → Fin q → CMat 2

section
variable {q : ℕ}
def flattenBlockFamily (N : BlockFamily q) : CMat (q*2) :=
  fun i j =>
    let x := finProdFinEquiv.symm i
    let y := finProdFinEquiv.symm j
    N x.1 y.1 x.2 y.2

def extractBlockFamily (M : CMat (q*2)) : BlockFamily q :=
  fun i j a b => M (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b))

@[simp] theorem extract_flattenBlockFamily (N : BlockFamily q) :
    extractBlockFamily (flattenBlockFamily N) = N := by
  funext i j a b
  simp [extractBlockFamily,flattenBlockFamily]

end

/-- The block array and scalar matrix spaces have their unchanged topologies. -/
def blockFamilyHomeomorph (q : ℕ) : BlockFamily q ≃ₜ CMat (q*2) where
  toFun := flattenBlockFamily
  invFun := extractBlockFamily
  left_inv := extract_flattenBlockFamily
  right_inv M := funext₂ fun i j => by simp only [extractBlockFamily,flattenBlockFamily, Prod.mk.eta, Equiv.apply_symm_apply]
  continuous_toFun := by unfold flattenBlockFamily; fun_prop
  continuous_invFun := by unfold extractBlockFamily; fun_prop

abbrev OuterFactors (q : ℕ) (o : Fin q) :=
  (Fin q → BlockU (fun _ : Fin 2 => 0)) ×
    ({j : Fin q // j ≠ o} → BlockU (fun _ : Fin 2 => 0))

section
variable {q : ℕ} {o : Fin q} (g : OuterFactors q o)
def outerLeft (i : Fin q) : CMat 2 :=
  (g.1 i).val

def outerRight (j : Fin q) : CMat 2 :=
  if h : j = o then 1 else (g.2 ⟨j,h⟩).val

theorem outerLeft_unitary (i : Fin q) :
    GS.Unitary (outerLeft g i) := (g.1 i).property.2

theorem outerRight_unitary (j : Fin q) :
    GS.Unitary (outerRight g j) := by
  unfold outerRight
  split <;> grind [GS.Unitary.one]

@[simp] theorem outerRight_anchor :
    outerRight g o = 1 := by simp [outerRight]

end

section
variable {q : ℕ} {o : Fin q} (L R : Fin q → CMat 2) (hL : ∀ i, GS.Unitary (L i)) (hR : ∀ j, GS.Unitary (R j))
def outerOfMatrices : OuterFactors q o :=
  (fun i => ⟨L i, by tauto, hL i⟩, fun j => ⟨R j, by tauto, hR j⟩)

theorem outerRight_ofMatrices (ho : R o = 1) :
    outerRight (outerOfMatrices (o := o) L R hL hR) = R := by
  funext j
  by_cases hj : j = o <;> simp_all [outerRight,outerOfMatrices]

end

section
variable (q : ℕ) (o : Fin q)
theorem continuous_outerLeft :
    Continuous (@outerLeft q o) := by
  unfold outerLeft
  fun_prop

theorem continuous_outerRight :
    Continuous (@outerRight q o) := by
  refine continuous_pi fun j => ?_
  by_cases hj : j = o <;> simp [outerRight, hj] <;> fun_prop

end

section
variable {q d : ℕ}
def chartBlockFamily (ψ : (Fin d → ℝ) → CMat q)
    (p : LocalParameters d) : BlockFamily q :=
  fun i j => parameterMiddle (fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2) p (i,j)

def fullBlockImage {o : Fin q} (ψ : (Fin d → ℝ) → CMat q)
    (g : OuterFactors q o) (p : LocalParameters d) : CMat (q*2) :=
  flattenBlockFamily (fun i j => outerLeft g i * chartBlockFamily ψ p i j * outerRight g j)

end

abbrev FullCompactParameters (q : ℕ) (o : Fin q) (d : ℕ) (r : ℝ) :=
  OuterFactors q o × localParameterBox d r

section
variable {q d : ℕ} (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ)
def fullCompactMiddle (p : FullCompactParameters q o d r) : CMat (q*2) :=
  fullBlockImage ψ p.1 p.2.val

abbrev FullCompactImage :=
  Set.range (fullCompactMiddle ψ o r)

end

instance fullCompactParameters_compactSpace (q : ℕ) (o : Fin q) (d : ℕ) (r : ℝ) :
    CompactSpace (FullCompactParameters q o d r) := by
  let : CompactSpace (localParameterBox d r) :=
    isCompact_iff_compactSpace.mp (isCompact_localParameterBox d r)
  exact inferInstance

theorem continuous_fullCompactMiddle {q d : ℕ}
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ)) (o : Fin q) (r : ℝ)
    (hψ : ContinuousOn ψ U)
    (hargs : ∀ p ∈ localParameterBox d r, p.1+p.2.1 ∈ U ∧ p.1-p.2.1 ∈ U) :
    Continuous (fullCompactMiddle ψ o r) := by
  have hm := continuous_parameterMiddle_on_box _ U (by fun_prop : ContinuousOn (fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2) U) r hargs
  exact (blockFamilyHomeomorph q).continuous.comp (continuous_pi fun i => continuous_pi fun j =>
    ((((continuous_apply i).comp (continuous_outerLeft q o)).comp continuous_fst).matrix_mul
      (((continuous_apply (i,j)).comp hm).comp continuous_snd)).matrix_mul
      (((continuous_apply j).comp (continuous_outerRight q o)).comp continuous_fst))

end GS.UnitaryLocalModel
