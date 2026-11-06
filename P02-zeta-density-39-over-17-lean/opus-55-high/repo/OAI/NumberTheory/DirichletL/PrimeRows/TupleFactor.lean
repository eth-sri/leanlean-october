module
public import OAI.NumberTheory.DirichletL.PrimeRows.MarkedHolomorphic

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem physicalCompensatedRow_indexed {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ) :
    let hT : ∀Q∈Finset.univ.image P,Q.val∉S := by grind
    physicalCompensatedRow S hS (Finset.univ.image P) hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i,continuedCompensatedLocal η u (P i)
          (outside_prime_supported S hS.bad (P i) (hPS i)) x w z
          (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
          (((P i).val.absNorm:ℂ)^(-w))) := by
  dsimp only
  unfold physicalCompensatedRow continuedCompensatedRow
  congr 2
  symm
  apply Finset.prod_bij (fun i _=>⟨P i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
  grind
  grind
  grind
  grind

end SevenEighths.ProbeHighRowFamily
end

end OAI
