module

public import OAI.NumberTheory.DirichletL.PrimeRows.FirstWGrowth
public import OAI.NumberTheory.DirichletL.Hecke.StripActual

public import OAI.NumberTheory.DirichletL.PrimeRows.PhysicalProductBounds

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem physicalRow_first_z_bounded (eps : ℝ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (x w : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re)
    (hxw : 1+eps≤x.re+w.re) :
    ∃C : ℝ,0≤C ∧ ∀z : ℂ,(17/50:ℝ)≤z.re →
      ‖physicalCompensatedRow S hS T hT η u x w z‖≤C := by
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm x.re
  let L : ℝ := HeckeReciprocalBound.bound 2*
    ‖HeckeOrigin.continued (rowCharacter S hS.prime u) w‖*
    ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖
  have hLb : 0≤HeckeReciprocalBound.bound 2 := by unfold HeckeReciprocalBound.bound; positivity
  have hL : 0≤L := by dsimp [L];positivity
  have hA (P : T)  := selectedFirstBound_nonneg (P.val.val.absNorm : ℝ) x.re (Nat.cast_nonneg _)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*(Ch*N)*(∏P:T,A P),by positivity,?_⟩
  intro z hz
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh eps S hS hfirst T η u x w z hx hw hz hxw
  have hg : ‖rowLocalProduct S hS T hT η u x w z‖ ≤ ∏ P : T, A P :=
    rowLocalProduct_first_bound S hS T hT η u x w z x.re hx le_rfl hw hz (by linarith [hfirst.positive]) A (fun _ => le_rfl)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖ ≤ HeckeReciprocalBound.bound 2 :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  simpa only [one_mul] using
    (physicalRow_norm_le S hS T hT η u x w z 1 hl le_rfl (le_of_eq (by rw [one_mul])) hh' hg).trans_eq
      (show _ = L*(Ch*N)*(∏P:T,A P) by dsimp [L]; ring)

end SevenEighths.ProbeHighRowFamily

end

end OAI
