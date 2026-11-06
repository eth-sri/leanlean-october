module

public import OAI.NumberTheory.DirichletL.RowCompletion.RowAmplitudes

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
 
open Filter    
open ActualEisensteinCubic
 
open   RationalPrimeExtraction ShortDraftLatticeCount
 
 
 
open EisensteinEmbedding ConcreteTraceCRT  
 
 
open scoped LSeries.notation ArithmeticFunction.Moebius
 
 
 
 
 
 
 
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal      
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
open scoped ContDiff    
 
 
 
 
 
 
 
 
 
 
 
 
 
open   Set
 
 
 
 
 
 
 
 

 

namespace CompletedGauss
open   CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

namespace CubicEisenstein
open   CompletedGauss CompletedDyadic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

end FixedFourierGeometry
end CubicEisenstein

namespace CompletedGauss.FreeReflection
open   CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss.FreeReflection
namespace CubicEisenstein.FixedFourierGeometry
open   CompletedGauss CompletedGauss.FreeReflection CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein.FixedFourierGeometry

 

namespace CompletedGauss.FreeReflection
 
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss.FreeReflection

namespace CanonicalRowCompletion.ActualFiber
open   CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
    (J:RowIndex q m rows R F)

end CanonicalRowCompletion.ActualFiber

namespace CubicEisenstein
open     CompletedGauss LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

noncomputable local instance inactiveField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P
noncomputable local instance inactiveFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

lemma finiteAdditiveFourierCoeff_zero {R:Type*} [Field R] [Fintype R]
    (ψ:AddChar R ℂ)  χ   j  :
    finiteAdditiveFourierCoeff ψ (fun x=>(χ^j) x) 0=zeroFourierCoefficient χ j := by
  simp only [finiteAdditiveFourierCoeff,zeroFourierCoefficient,neg_zero,zero_mul,
    AddChar.map_zero_eq_one,mul_one,div_eq_mul_inv]
  ring

lemma prime_zeroFourier_norm_formula  p  [(Ideal.span {p}).IsMaximal]
     hp  (hg:lambda∉Ideal.span {p}) (hodd:ringChar (Eis⧸Ideal.span {p})≠2)
     j  (hj:j<6) :
    finiteAdditiveFourierCoeff (quotientTrace p hp)
      (fun x=>(actualSextic (Ideal.span {p}) hg^j) x) 0=
      if j=0 then 1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹ else 0 := by
  rw [finiteAdditiveFourierCoeff_zero]
  have he:=canonical_zeroFourierCoefficient (Ideal.span {p}) hg hodd j hj
  convert he using 1
  exact congrArg (fun n:ℕ=>(if j=0 then 1-(n:ℂ)⁻¹ else 0)) (by rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card])

end CubicEisenstein

namespace CompletedGauss.FreeReflection
open   CubicEisenstein LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O




end CompletedGauss.FreeReflection

namespace CanonicalRowCompletion
open   CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)
variable (R I F Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hF:Squarefree F)
    (hm:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
include R I F Q0 hR hI hF hm hf hz hbad hcop hA hT

end GoodMaskRowData
end CanonicalRowCompletion

 

namespace CubicEisenstein
 
local notation "Eis" => ActualEisensteinCubic.O


end CubicEisenstein

end

end OAI
