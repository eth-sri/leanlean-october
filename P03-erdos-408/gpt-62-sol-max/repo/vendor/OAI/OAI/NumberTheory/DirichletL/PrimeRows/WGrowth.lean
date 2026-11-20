module

public import OAI.NumberTheory.DirichletL.PrimeRows.TupleGrowth
public import OAI.NumberTheory.DirichletL.PrimeRows.SelectedBounds

public import OAI.NumberTheory.DirichletL.PrimeRows.PhysicalProductBounds

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem calibrated_physicalRow_w_growth (eps : ℝ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+1/2) :
    ∃C : ℝ,0<C ∧ ∀w : ℂ,(1/2:ℝ)≤w.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_positive_growth (1/2) 1 (by norm_num) (by norm_num) S hS hmax
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>961*((P.val.val.absNorm:ℝ)^(1/2:ℝ)+1)
  let L : ℝ := ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖*
    ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖
  let C : ℝ := L*(Cn*N^(3/5+1:ℝ))*(Ch*N)*∏P:T,A P
  have hC : 0≤C := by dsimp [C,L,A,N];positivity
  refine ⟨1+C,by linarith,?_⟩
  intro w hw
  have hn' := hn u hu w hw
  have hh' := hh eps S hS hfirst T η u x w z (by linarith) (by linarith) hz (by linarith)
  have hg : ‖rowLocalProduct S hS T hT η u x w z‖ ≤ ∏ P : T, A P := by
    rw [rowLocalProduct, norm_prod]
    change (∏P:T,‖continuedCompensatedLocal η u P.val _ x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖)≤_
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P _
    have hQ : (4:ℝ)≤P.val.val.absNorm := by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)
    apply (continuedCompensatedLocal_bound η u P.val _ hQ x w z hx hw hz).trans
    dsimp [A]
    by_cases hp : P.val.val∣Ideal.span {u.val}
    · rw [ite_eq_left hp]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤P.val.val.absNorm)
        (max_le (by linarith) (by norm_num) : max (1-w.re) 0≤(1/2:ℝ))).trans
      linarith
    · rw [ite_eq_right hp]
      have hnq := Real.rpow_nonneg (show (0:ℝ)≤P.val.val.absNorm by positivity) (1/2:ℝ)
      nlinarith
  have hh'' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh'
  calc
    _ ≤ L*(Cn*N^(3/5+1:ℝ)*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := physicalRow_norm_le S hS T hT η u x w z (star ((calibrationForSet S hmax).residueMonoid u.val))
      le_rfl le_rfl hn' hh'' hg
    _ = C*(3+|w.im|)^2 := by ring
    _ ≤ (1+C)*(3+|w.im|)^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

end SevenEighths.ProbeHighRowFamily
end

end OAI
