module

public import OAI.NumberTheory.DirichletL.PrimeRows.ZGrowth
public import OAI.NumberTheory.DirichletL.PrimeRows.ReciprocalGrowth

public import OAI.NumberTheory.DirichletL.PrimeRows.PhysicalProductBounds

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem physicalRow_first_x_growth (e eps : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (w z : ℂ) (l r : ℝ)
    (hl : (51/100:ℝ)≤l) (hlβ : HeckeZeroSupremum.beta+8*e≤l)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hlw : 1+eps≤l+w.re) :
    ∃C : ℝ,0≤C ∧ ∀x : ℂ,l≤x.re → x.re≤r →
      ‖physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|x.im|)^2 := by
  obtain ⟨Cr,hCr,hr⟩ := targetRow_reciprocal_growth e 1 he he' (by norm_num) (by norm_num) S hS.prime
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm r
  let L : ℝ := ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖*
    ‖HeckeOrigin.continued (rowCharacter S hS.prime u) w‖
  let B : ℝ := Cr*(η.modulus.absNorm:ℝ)*N
  have hL : 0≤L := by dsimp [L];positivity
  have hA (P : T)  := selectedFirstBound_nonneg (P.val.val.absNorm : ℝ) r (Nat.cast_nonneg _)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*B*(Ch*N)*(∏P:T,A P),by positivity,?_⟩
  intro x hxl hxr
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤B*(3+|x.im|)^2 := by
    simpa only [Real.rpow_one] using hr η u x (hlβ.trans hxl)
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh eps S hS hfirst T η u x w z (hl.trans hxl) hw hz (by linarith)
  have hg : ‖rowLocalProduct S hS T hT η u x w z‖ ≤ ∏ P : T, A P :=
    rowLocalProduct_first_bound S hS T hT η u x w z r (hl.trans hxl) hxr hw hz (by linarith [hfirst.positive]) A (fun _ => le_rfl)
  simpa only [one_mul] using
    (physicalRow_norm_le S hS T hT η u x w z 1 le_rfl hrec (le_of_eq (by rw [one_mul])) hh' hg).trans_eq
      (show _ = L*B*(Ch*N)*(∏P:T,A P)*(3+|x.im|)^2 by dsimp [L]; ring)

end SevenEighths.ProbeHighRowFamily

end

end OAI
