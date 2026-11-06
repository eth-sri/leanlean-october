module
public import OAI.NumberTheory.DirichletL.Descent.FirstBlocks
public import OAI.NumberTheory.DirichletL.Descent.FirstActualEnergy

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic RayFourExpansion
open MeasureTheory
noncomputable section
open scoped EisensteinEis
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstBlockOuterWeight (selector : Finset ι → ℂ)
    (r : RayCharacter × RayCharacter) (D : Finset ι) (h : Eis) : ℂ :=
  crossCoeff r.1 r.2 * selector D * supportMobius (fun i => Ideal.span {p i}) D *
    rowCoprimeMask (fun i => Ideal.span {p i}) D h

section
variable (F : Finset ι) (selector : Finset ι → ℂ)
    (C : Finset ι → ℂ) (negative : Bool) (ω : ℝ → ℂ) (X t : ℝ) (h : Eis)
include F selector C negative ω X t h

def firstBlockEnergy  : ℝ :=
  ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖firstBlockOuterWeight p selector r D h‖ *
      ‖firstCommonColumn p hg F D C negative (if negative then r.1 else r.2) ω X t h‖^2

theorem firstBlockEnergy_nonneg  :
    0 ≤ firstBlockEnergy p hg F selector C negative ω X t h := by
  unfold firstBlockEnergy
  positivity
end






