module

public import OAI.NumberTheory.DirichletL.RowCompletion.RowAmplitudes

@[expose] public section

namespace OAI

noncomputable section


open MulChar AddChar Filter Asymptotics MeasureTheory

open MeasureTheory Real

open Finset Complex

open Filter Real Asymptotics ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Filter Asymptotics

open MeasureTheory Set ActualEisensteinCubic UniqueFactorizationMonoid




namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss CompletedDyadic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

end FixedFourierGeometry
end CubicEisenstein

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss.FreeReflection
namespace CubicEisenstein.FixedFourierGeometry
open ActualEisensteinCubic CompletedGauss CompletedGauss.FreeReflection CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein.FixedFourierGeometry

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss.FreeReflection

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
    (J:RowIndex q m rows R F)

end CanonicalRowCompletion.ActualFiber

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

noncomputable local instance inactiveField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P
noncomputable local instance inactiveFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

lemma finiteAdditiveFourierCoeff_zero {R:Type*} [Field R] [Fintype R]
    (ψ:AddChar R ℂ) (χ:MulChar R ℂ) (j:ℕ) :
    finiteAdditiveFourierCoeff ψ (fun x=>(χ^j) x) 0=zeroFourierCoefficient χ j := by
  simp only [finiteAdditiveFourierCoeff,zeroFourierCoefficient,neg_zero,zero_mul,
    AddChar.map_zero_eq_one,mul_one,div_eq_mul_inv]
  ring

lemma prime_zeroFourier_norm_formula (p:Eis) [(Ideal.span {p}).IsMaximal]
    (hp:p≠0) (hg:lambda∉Ideal.span {p}) (hodd:ringChar (Eis⧸Ideal.span {p})≠2)
    (j:ℕ) (hj:j<6) :
    finiteAdditiveFourierCoeff (quotientTrace p hp)
      (fun x=>(actualSextic (Ideal.span {p}) hg^j) x) 0=
      if j=0 then 1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹ else 0 := by
  rw [finiteAdditiveFourierCoeff_zero]
  have he:=canonical_zeroFourierCoefficient (Ideal.span {p}) hg hodd j hj
  convert he using 1
  exact congrArg (fun n:ℕ=>(if j=0 then 1-(n:ℂ)⁻¹ else 0)) (by rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card])

end CubicEisenstein

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss.FreeReflection

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
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
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
