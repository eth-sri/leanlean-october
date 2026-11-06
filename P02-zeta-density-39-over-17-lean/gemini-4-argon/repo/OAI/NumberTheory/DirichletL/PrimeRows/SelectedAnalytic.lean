module
public import OAI.NumberTheory.DirichletL.PrimeRows.SelectedAgreement

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler CanonicalQuadraticSieve CompletedGauss

theorem continuedMarkedLocal_eq_quotient (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hV : 1-coordV P.val.absNorm z≠0) :
    continuedMarkedLocal η u P hs x w z=(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z) := by
  rw [ramifiedCorrection_eq_marked]
  field_simp
  ring

theorem selected_V_ne_zero (P : PrimeIdeal) (hQ : (4:ℝ)≤P.val.absNorm) (z : ℂ)
    (hz : (4/25:ℝ)≤z.re) : 1-coordV P.val.absNorm z≠0 := by
  apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
  rw [coordV_norm _ (by linarith : (0:ℝ)<P.val.absNorm)]
  apply rpow_le_half _ _ hQ
  linarith
