module

public import OAI.NumberTheory.DirichletL.PrimeRows.MarkedHolomorphic
public import OAI.NumberTheory.DirichletL.PrimeRows.SelectedFirstBounds

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

/-- The product over the individually marked primes in a physical row. -/
def rowLocalProduct (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (η : Character) (u : FreeRow)
    (x w z : ℂ) : ℂ :=
  ∏ P ∈ T.attach, continuedCompensatedLocal η u P.val
    (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
    (star (idealCoeff η P.val.val) * (P.val.val.absNorm : ℂ) ^ x)
    ((P.val.val.absNorm : ℂ) ^ (-w))

/-- Bound the continued row by multiplying the bounds on its analytic factors. -/
theorem physicalRow_norm_le (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (η : Character) (u : FreeRow)
    (x w z c : ℂ) {A B C D E : ℝ}
    (hA : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖ ≤ A)
    (hB : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖ ≤ B)
    (hC : ‖c * HeckeOrigin.continued (rowCharacter S hS.prime u) w‖ ≤ C)
    (hD : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖ ≤ D)
    (hE : ‖rowLocalProduct S hS T hT η u x w z‖ ≤ E) :
    ‖c * physicalCompensatedRow S hS T hT η u x w z‖ ≤ A * B * C * D * E := by
  have hf : c * physicalCompensatedRow S hS T hT η u x w z =
    LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x *
    (c * HeckeOrigin.continued (rowCharacter S hS.prime u) w) *
    continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z *
    rowLocalProduct S hS T hT η u x w z := by
      unfold physicalCompensatedRow continuedCompensatedRow rowLocalProduct
      ring
  rw [hf, norm_mul, norm_mul, norm_mul, norm_mul]
  have ha := (norm_nonneg _).trans hA
  have hb := (norm_nonneg _).trans hB
  have hc := (norm_nonneg _).trans hC
  have hd := (norm_nonneg _).trans hD
  gcongr

/-- Uniform product bound in the first-frequency range. -/
theorem rowLocalProduct_first_bound (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (R : ℝ) (hx : (51/100 : ℝ) ≤ x.re) (hR : x.re ≤ R)
    (hw : -(1/100 : ℝ) ≤ w.re) (hz : (17/50 : ℝ) ≤ z.re) (hxw : 1 ≤ x.re + w.re)
    (A : T → ℝ) (hA : ∀ P : T, selectedFirstBound P.val.val.absNorm R ≤ A P) :
    ‖rowLocalProduct S hS T hT η u x w z‖ ≤ ∏ P : T, A P := by
  rw [rowLocalProduct, norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro P _
  exact (continuedCompensatedLocal_first_bound η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) R x w z hx hR hw hz hxw).trans (hA P)

end SevenEighths.ProbeHighRowFamily

end

end OAI
