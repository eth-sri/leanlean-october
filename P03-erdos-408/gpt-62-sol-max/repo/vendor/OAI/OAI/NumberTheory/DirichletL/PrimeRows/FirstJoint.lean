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

theorem calibrated_physicalRow_first_joint_growth
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (1/4) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) :
    ∃C : ℝ,0≤C ∧ ∀x w z : ℂ,x.re=2 → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm 2
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  have hA (P : T)  := selectedFirstBound_nonneg (P.val.val.absNorm : ℝ) 2 (Nat.cast_nonneg _)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*L*Cn*(Ch*N)*(∏P:T,A P),by positivity,?_⟩
  intro x w z hx hw hz
  have hn' := hn w hw
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (1/4) S hS hfirst T η u x w z (by rw [hx];norm_num) hw hz
      (by rw [hx];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hg : ‖rowLocalProduct S hS T hT η u x w z‖ ≤ ∏ P : T, A P :=
    rowLocalProduct_first_bound S hS T hT η u x w z 2 (by rw [hx]; norm_num) hx.le hw hz (by rw [hx]; linarith) A (fun _ => le_rfl)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖ ≤ L :=
    HeckeReciprocalBound.reciprocal_norm_le _ (by norm_num) (by rw [hx])
  exact (physicalRow_norm_le S hS T hT η u x w z (star ((calibrationForSet S hmax).residueMonoid u.val)) hl hrec hn' hh' hg).trans_eq (by ring)

end SevenEighths.ProbeHighRowFamily

end

end OAI
