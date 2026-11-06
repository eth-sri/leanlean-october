module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.PrimeRows.MarkedContinuation
public import OAI.NumberTheory.DirichletL.PrimeRows.SelectedHolomorphic

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical


def physicalCompensatedRow (S ) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ)  :=
  continuedCompensatedRow S hS T hT η u x w z
    (fun P=>star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x)
    (fun P=>(P.val.absNorm:ℂ)^(-w))

theorem unselectedCorrection_first_subpower (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀ (eps : ℝ) (S : Finset (Ideal HeckeFamily.O)) (hS : SourceExclusions S)
      (_hfirst : FirstTail eps S) (T : Finset PrimeIdeal) (η : Character) (u : FreeRow) (x w z : ℂ),
      (51/100:ℝ)≤x.re → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re → 1+eps≤x.re+w.re →
      ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤
        C*((Ideal.span {u.val}:Ideal HeckeFamily.O).absNorm:ℝ)^δ := Exists.casesOn (OAI.SevenEighths.ProbeHighRowFamily.continuedCorrection_first_subpower δ hδ) fun C h => And.casesOn h fun hC hbound => Exists.intro C ⟨hC, fun eps S hS hfirst T => hbound eps (OAI.SevenEighths.ProbeHighRowFamily.markExclusions S T) (OAI.SevenEighths.ProbeHighRowFamily.markedSourceExclusions S hS T) (OAI.SevenEighths.ProbeHighRowFamily.marked_firstTail eps S hfirst T)⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
