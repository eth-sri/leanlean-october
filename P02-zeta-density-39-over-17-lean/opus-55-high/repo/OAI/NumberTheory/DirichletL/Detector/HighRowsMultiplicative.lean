module
public import OAI.NumberTheory.DirichletL.Detector.HighEulerGeneral
public import OAI.NumberTheory.DirichletL.Detector.SixthFrequency
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

section
variable (η : HeckeFamily.Character) (u : O)
include η u
theorem bareSourceCoefficient_product_row_frequency (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryGenerator I})) (hd : Supported (Ideal.span {primaryGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : goodLambda^2∣primaryGenerator I-1) (hpd : goodLambda^2∣primaryGenerator J-1)
    (hpn : goodLambda^2∣n-1) (hpm : goodLambda^2∣m-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime ((primaryGenerator I*n^3)*s) ((primaryGenerator J*m^3)*r)) (a b : O)
    (hba : IsCoprime b ((primaryGenerator I*n^3)*s))
    (hab : IsCoprime a ((primaryGenerator J*m^3)*r)) :
    let A := primaryGenerator I*n^3
    let B := primaryGenerator J*m^3
    let hA := supportedElement_ne_zero A (supported_completed _ _ hc hn)
    let hB := supportedElement_ne_zero B (supported_completed _ _ hd hm)
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) (u*(a*b)^6) =
      bareSourceCoefficient η I hI.2 A s hA (u*a^6) * bareSourceCoefficient η J hJ.2 B r hB (u*b^6) := by
  have he := bareSourceCoefficient_product η I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop (u*(a*b)^6)
  dsimp only at he ⊢
  have hi := bareSourceCoefficient_sixth_frequency η I hI.2 (primaryGenerator I*n^3) s
    (supported_completed _ _ hc hn) hs b (u*a^6) hba
  have hj := bareSourceCoefficient_sixth_frequency η J hJ.2 (primaryGenerator J*m^3) r
    (supported_completed _ _ hd hm) hr a (u*b^6) hab
  rw [show b^6*(u*a^6)=u*(a*b)^6 by ring] at hi
  rw [show a^6*(u*b^6)=u*(a*b)^6 by ring] at hj
  rw [hi,hj] at he
  exact he

theorem bareIdealHighCoefficient_row_mul
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighCoefficient η u (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighCoefficient η u I J K L * bareIdealHighCoefficient η u I' J' K' L' := by
  pm_3906
  · have hprod := (highSupport_mul I J K L I' J' K' L' hII).mpr h
    pm_3904
    have he := bareSourceCoefficient_product_row_frequency η u I I'
      ⟨h.1,supported_primaryGenerator_ne_zero I h.2.1⟩
      ⟨h'.1,supported_primaryGenerator_ne_zero I' h'.2.1⟩
      ⟨hprod.1,supported_primaryGenerator_ne_zero (I*I') hprod.2.1⟩ hII
      (primaryGenerator J) (primaryGenerator J') (primaryGenerator K) (primaryGenerator K')
      ((supported_span_primaryGenerator_iff I).mpr h.2.1)
      ((supported_span_primaryGenerator_iff I').mpr h'.2.1)
      ((supported_span_primaryGenerator_iff J).mpr h.2.2.1)
      ((supported_span_primaryGenerator_iff J').mpr h'.2.2.1)
      ((supported_span_primaryGenerator_iff K).mpr h.2.2.2.1)
      ((supported_span_primaryGenerator_iff K').mpr h'.2.2.2.1)
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I h.2.1)).2
      (primaryGenerator_spec I' (supported_primaryGenerator_ne_zero I' h'.2.1)).2
      (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J h.2.2.1)).2
      (primaryGenerator_spec J' (supported_primaryGenerator_ne_zero J' h'.2.2.1)).2
      (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K h.2.2.2.1)).2
      (primaryGenerator_spec K' (supported_primaryGenerator_ne_zero K' h'.2.2.2.1)).2
      hab (primaryGenerator L) (primaryGenerator L') hba hab'
    unfold highSupport at hprod h h'
    unfold bareIdealHighCoefficient
    rw [dite_eq_left hprod,dite_eq_left h,dite_eq_left h']
    simp only [primaryGenerator_mul]
    pm_8388
  · have hprod := mt (highSupport_mul I J K L I' J' K' L' hII).mp h
    unfold highSupport at hprod
    unfold bareIdealHighCoefficient
    pm_3905

theorem bareIdealHighSummand_row_mul (x w z : ℂ)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighSummand η u x w z (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighSummand η u x w z I J K L * bareIdealHighSummand η u x w z I' J' K' L' := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_row_mul η u I J K L I' J' K' L' hcop,
    fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul]
  ring
end

end SevenEighths.ProbePhysical

end OAI
