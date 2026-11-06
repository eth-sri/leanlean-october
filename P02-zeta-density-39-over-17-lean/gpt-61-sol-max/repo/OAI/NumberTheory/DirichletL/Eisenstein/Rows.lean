module
import Mathlib
public import OAI.NumberTheory.DirichletL.CubicSieve.RayCoefficients

@[expose] public section

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar
                        
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
                     
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
                          
                          
           
                    
open ConcreteTraceCRT ActualEisensteinCubic
            
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
           
            
            
                                                       
                                     
                    
                       
open NumberField
                
                
                
                
                       
                                     
                    
open Filter Asymptotics NumberField
           
                                     
                    
                                     
                    
                                     
                    
                       
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
                                  
                                  
open scoped BigOperators Classical SchwartzMap ContDiff
                                                       
                                  
                                                       
                                  
                                                       
                                                       
                                                       
                                  
                                                       
open MeasureTheory
                        
                                  
                                  
                          

section
open scoped BigOperators Classical MatrixGroups

section
abbrev K := ActualEisensteinCubic.K
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def row (M : levelThree) : Fin 2 → O := (M : SL(2,O)) 1

lemma row_mul (M N : levelThree) :
    row (M*N) = Matrix.vecMul (row M) (N : SL(2,O)) := by rfl

lemma row_ne_zero (M : levelThree) : row M ≠ 0 := by
  intro hz
  have hc : (M : SL(2,O)) 1 0 = 0 := congrFun hz 0
  have hd : (M : SL(2,O)) 1 1 = 0 := congrFun hz 1
  have h : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
  simp_all

lemma character_eq_of_row_eq (M N : levelThree) (hr : row M = row N) :
    complexCharacter M = complexCharacter N := by
  have hrow : row (M*N⁻¹) = row 1 := by
    rw [row_mul, hr, ← row_mul]
    simp
  have hc : ((M*N⁻¹ : levelThree) : SL(2,O)) 1 0 = 0 := by
    simpa [row, Matrix.one_apply] using congrFun hrow 0
  have hchar : complexCharacter (M*N⁻¹) = 1 := by
    change eisEmbedding (value (M*N⁻¹)) = 1
    rw [value_zero_lower_left _ hc, map_one]
  calc
    complexCharacter M = complexCharacter ((M*N⁻¹)*N) := by congr 1; group
    _ = complexCharacter (M*N⁻¹) * complexCharacter N := map_mul _ _ _
    _ = complexCharacter N := by rw [hchar, one_mul]

lemma row_eq_one_of_lower_left_zero (M : levelThree)
    (hc : (M : SL(2,O)) 1 0 = 0) : row M = row 1 := by
  have hdet : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 = 1 := by
    have hd : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
        (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
    simpa only [hc, mul_zero, sub_zero] using hd
  have ha := A3_primary_unit_eq_one _ (IsUnit.of_mul_eq_one _ hdet)
    (levelThree_primary M)
  have hd : (M : SL(2,O)) 1 1 = 1 := by simpa only [ha, one_mul] using hdet
  funext j
  fin_cases j <;> simp [row, hc, hd]

def cuspStabilizer : Subgroup levelThree where
  carrier := {M | row M = row 1}
  one_mem' := rfl
  mul_mem' := by
    intro M N hM hN
    change row (M*N) = row 1
    rw [row_mul, hM, ← row_mul]
    simpa using hN
  inv_mem' := by
    intro M hM
    have h : row (M*M⁻¹) = row 1 := by simp
    rw [row_mul, hM, ← row_mul] at h
    simpa using h

lemma mem_cuspStabilizer_iff (M : levelThree) :
    M ∈ cuspStabilizer ↔ (M : SL(2,O)) 1 0 = 0 := by
  constructor
  · intro h
    simpa [row, Matrix.one_apply] using congrFun h 0
  · exact row_eq_one_of_lower_left_zero M

lemma row_eq_iff_left_cusp (M N : levelThree) : row M = row N ↔
    ∃ T : levelThree, T ∈ cuspStabilizer ∧ M = T*N := by
  constructor
  · intro h
    refine ⟨M*N⁻¹, ?_, by group⟩
    change row (M*N⁻¹) = row 1
    rw [row_mul, h, ← row_mul]
    simp
  · rintro ⟨T,hT,rfl⟩
    change row T = row 1 at hT
    rw [row_mul, hT, ← row_mul, one_mul]

def cuspRelation : Setoid levelThree := Setoid.ker row

abbrev CuspCosets := Quotient cuspRelation

def cosetOf (M : levelThree) : CuspCosets := Quotient.mk _ M

lemma cosetOf_eq_iff (M N : levelThree) : cosetOf M = cosetOf N ↔
    ∃ T : levelThree, T ∈ cuspStabilizer ∧ M = T*N := by
  rw [← row_eq_iff_left_cusp]
  exact Quotient.eq

def cosetRow : CuspCosets → (Fin 2 → O) :=
  Quotient.lift row (fun _ _ h => h)

@[simp] lemma cosetRow_cosetOf (M : levelThree) : cosetRow (cosetOf M) = row M := rfl

lemma cosetRow_injective : Function.Injective cosetRow := by
  intro x y
  induction x using Quotient.inductionOn with | _ M =>
    induction y using Quotient.inductionOn with | _ N =>
      intro h
      exact Quotient.sound h

lemma cosetRow_ne_zero (x : CuspCosets) : cosetRow x ≠ 0 := by
  induction x using Quotient.inductionOn with | _ M => exact row_ne_zero M

def cosetCharacter : CuspCosets → ℂ :=
  Quotient.lift complexCharacter (fun M N h => character_eq_of_row_eq M N h)



lemma norm_cosetCharacter (x : CuspCosets) : ‖cosetCharacter x‖ = 1 := by
  induction x using Quotient.inductionOn with | _ M => exact norm_complexCharacter M

def rightTranslate (M : levelThree) : CuspCosets → CuspCosets :=
  Quotient.map (fun N => N*M) (by
    intro A B h
    change row (A*M) = row (B*M)
    rw [row_mul, row_mul, show row A = row B from h])



lemma rightTranslate_mul (M N : levelThree) (x : CuspCosets) :
    rightTranslate N (rightTranslate M x) = rightTranslate (M*N) x := by
  induction x using Quotient.inductionOn with | _ A =>
    change cosetOf ((A*M)*N) = cosetOf (A*(M*N))
    rw [mul_assoc]

@[simp] lemma rightTranslate_one (x : CuspCosets) : rightTranslate 1 x = x := by
  induction x using Quotient.inductionOn with | _ A =>
    change cosetOf (A*1) = cosetOf A
    rw [mul_one]

section
variable (M : levelThree)
include M

def rightEquiv  : CuspCosets ≃ CuspCosets where
  toFun := rightTranslate M
  invFun := rightTranslate M⁻¹
  left_inv x := by rw [rightTranslate_mul]; simp
  right_inv x := by rw [rightTranslate_mul]; simp

lemma cosetRow_rightEquiv  (x : CuspCosets) :
    cosetRow (rightEquiv M x) = Matrix.vecMul (cosetRow x) (M : SL(2,O)) := by
  induction x using Quotient.inductionOn with | _ N => exact row_mul N M

lemma cosetCharacter_rightEquiv  (x : CuspCosets) :
    cosetCharacter (rightEquiv M x) = cosetCharacter x * complexCharacter M := by
  induction x using Quotient.inductionOn with | _ N => exact map_mul _ _ _
end


def complexMatrix : levelThree →* SL(2,ℂ) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2) eisEmbedding).comp levelThree.subtype

lemma complexMatrix_apply (M : levelThree) (i j : Fin 2) :
    complexMatrix M i j = eisEmbedding ((M : SL(2,O)) i j) := rfl

def embeddedRow (x : CuspCosets) : Fin 2 → ℂ := eisEmbedding ∘ cosetRow x

lemma embeddedRow_ne_zero (x : CuspCosets) : embeddedRow x ≠ 0 := by
  intro hz
  apply cosetRow_ne_zero x
  funext i
  apply eisEmbedding_injective
  simpa only [embeddedRow, Function.comp_apply, Pi.zero_apply, map_zero] using congrFun hz i

lemma embeddedRow_rightEquiv (M : levelThree) (x : CuspCosets) :
    embeddedRow (rightEquiv M x) = Matrix.vecMul (embeddedRow x) (complexMatrix M : SL(2,ℂ)) := by
  funext j
  simp only [embeddedRow, Function.comp_apply, cosetRow_rightEquiv,
    Matrix.vecMul, dotProduct, map_sum, map_mul, complexMatrix_apply]

end

section
open ActualEisensteinCubic ConcreteTraceCRT

def integerLattice : Submodule ℤ ((Fin 2 × Fin 2) → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2 × Fin 2)))

instance : DiscreteTopology integerLattice := by
  unfold integerLattice
  infer_instance

instance : IsZLattice ℝ integerLattice := by
  unfold integerLattice
  infer_instance

def integerPoint (n : (Fin 2 × Fin 2) → ℤ) : integerLattice :=
  ⟨fun i => (n i : ℝ), by
    rw [integerLattice, (Pi.basisFun ℝ (Fin 2 × Fin 2)).mem_span_iff_repr_mem ℤ]
    simp⟩

lemma integerPoint_injective : Function.Injective integerPoint := by
  intro a b hab
  funext i
  have h := congrArg (fun x : integerLattice => (x : (Fin 2 × Fin 2) → ℝ) i) hab
  change (a i : ℝ) = (b i : ℝ) at h
  exact_mod_cast h



lemma summable_integer_four_rpow (k : ℝ) (hk : 4 < k) :
    Summable (fun n : (Fin 2 × Fin 2) → ℤ => ‖n‖ ^ (-k)) := by
  have hf : Module.finrank ℤ integerLattice = 4 := by
    rw [ZLattice.rank ℝ integerLattice]
    simp
  have hs := ZLattice.summable_norm_rpow integerLattice (-k) (by rw [hf]; norm_num; linarith)
  apply (hs.comp_injective integerPoint_injective).congr
  bound

def rowCoordinates (v : Fin 2 → O) : (Fin 2 × Fin 2) → ℤ :=
  fun i => if i.2 = 0 then (ActualEisensteinCoordinates.coords (v i.1)).1
    else (ActualEisensteinCoordinates.coords (v i.1)).2

lemma rowCoordinates_injective : Function.Injective rowCoordinates := by
  intro v w hvw
  funext i
  apply latticeCoordEquiv.injective
  apply Prod.ext
  · exact congrFun hvw (i,0)
  · exact congrFun hvw (i,1)

lemma coordinates_norm_bound (v : Fin 2 → O) :
    ‖rowCoordinates v‖ ≤ 2 * ‖fun i => eisEmbedding (v i)‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hi := norm_le_pi_norm (fun j => eisEmbedding (v j)) i.1
  have hq := eisEmbedding_eval_norm_sq
    (ActualEisensteinCoordinates.coords (v i.1)).1
    (ActualEisensteinCoordinates.coords (v i.1)).2
  rw [ActualEisensteinCoordinates.eval_coords] at hq
  push_cast at hq
  have hcoord (a b : ℝ) (t : ℝ) (ht : 0 ≤ t)
      (heq : t ^ 2 = a*a-a*b+b*b) : |a| ≤ 2*t ∧ |b| ≤ 2*t := by
    constructor <;> apply (abs_le).mpr <;> constructor <;>
      nlinarith [sq_nonneg (a-b), sq_nonneg (a+b), sq_nonneg (a-2*b), sq_nonneg (b-2*a)]
  have hh := hcoord _ _ ‖eisEmbedding (v i.1)‖ (norm_nonneg _) hq
  dsimp only [rowCoordinates]
  split_ifs
  · simpa only [Int.norm_eq_abs] using hh.1.trans (mul_le_mul_of_nonneg_left hi (by norm_num))
  · simpa only [Int.norm_eq_abs] using hh.2.trans (mul_le_mul_of_nonneg_left hi (by norm_num))

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

section
variable (v : Fin 2 → ℂ)
include v

def rowEnergy  : ℝ := ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2

lemma rowEnergy_nonneg  : 0 ≤ rowEnergy v := by
  unfold rowEnergy; positivity

lemma norm_le_sqrt_rowEnergy  : ‖v‖ ≤ Real.sqrt (rowEnergy v) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  apply Real.le_sqrt_of_sq_le
  fin_cases i <;> dsimp [rowEnergy] <;> nlinarith [sq_nonneg ‖v 0‖, sq_nonneg ‖v 1‖]

lemma rowEnergy_pos  (hv : v ≠ 0) : 0 < rowEnergy v := by
  have h := norm_le_sqrt_rowEnergy v
  have hn := norm_pos_iff.mpr hv
  exact Real.sqrt_pos.mp (lt_of_lt_of_le hn h)
end


section
variable (g : SL(2,ℂ))
include g

def rowOperator  : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLinearMapRight' (g : Matrix (Fin 2) (Fin 2) ℂ)).toContinuousLinearMap

@[simp] lemma rowOperator_apply  (v : Fin 2 → ℂ) :
    rowOperator g v = Matrix.vecMul v (g : Matrix (Fin 2) (Fin 2) ℂ) := rfl
end


lemma rowOperator_mul (g h : SL(2,ℂ)) (v : Fin 2 → ℂ) :
    rowOperator h (rowOperator g v) = rowOperator (g*h) v := by simp

@[simp] lemma rowOperator_one (v : Fin 2 → ℂ) : rowOperator 1 v = v := by
  simp only [rowOperator_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

section
variable (g : SL(2,ℂ))
include g

lemma rowOperator_ne_zero  (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    rowOperator g v ≠ 0 := by
  intro hz
  have h := congrArg (rowOperator g⁻¹) hz
  rw [rowOperator_mul, mul_inv_cancel, rowOperator_one, map_zero] at h
  exact hv h

def rowBound  : ℝ := 2 * (1 + ‖rowOperator g⁻¹‖)

lemma rowBound_pos  : 0 < rowBound g := by unfold rowBound; positivity

lemma coordinates_le_transformed_energy  (v : Fin 2 → O) :
    ‖rowCoordinates v‖ ≤ rowBound g *
      Real.sqrt (rowEnergy (rowOperator g (fun i => eisEmbedding (v i)))) := by
  have hi := (rowOperator g⁻¹).le_opNorm (rowOperator g (fun i => eisEmbedding (v i)))
  rw [rowOperator_mul, mul_inv_cancel, rowOperator_one] at hi
  have hb := coordinates_norm_bound v
  have he := norm_le_sqrt_rowEnergy (rowOperator g (fun i => eisEmbedding (v i)))
  have hm := mul_le_mul_of_nonneg_left he (norm_nonneg (rowOperator g⁻¹))
  dsimp only [rowBound]
  nlinarith [Real.sqrt_nonneg (rowEnergy (rowOperator g (fun i => eisEmbedding (v i))))]
end


lemma norm_coordinates_ne_zero (x : CuspCosets) : 0 < ‖rowCoordinates (cosetRow x)‖ := by
  apply norm_pos_iff.mpr
  intro hz
  apply cosetRow_ne_zero x
  apply rowCoordinates_injective
  have hz0 : rowCoordinates (0 : Fin 2 → O) = 0 := by
    apply norm_le_zero_iff.mp
    have he : (fun i : Fin 2 => eisEmbedding ((0 : Fin 2 → O) i)) =
        (0 : Fin 2 → ℂ) := by
      funext i
      exact map_zero _
    have hh := coordinates_norm_bound (0 : Fin 2 → O)
    simp_all
  simp_all

section
variable (g : SL(2,ℂ)) (s : ℂ)
include g s

def summand  (x : CuspCosets) : ℂ :=
  (cosetCharacter x)⁻¹ *
    (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s)

lemma norm_summand  (x : CuspCosets) :
    ‖summand g s x‖ = rowEnergy (rowOperator g (embeddedRow x)) ^ (-s.re) := by
  rw [summand, norm_mul, norm_inv, norm_cosetCharacter, inv_one, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos
      (rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x)))]
  rfl

lemma norm_summand_bound  (hs : 0 < s.re) (x : CuspCosets) :
    ‖summand g s x‖ ≤ (rowBound g) ^ (2*s.re) *
      ‖rowCoordinates (cosetRow x)‖ ^ (-(2*s.re)) := by
  rw [norm_summand]
  have hn := norm_coordinates_ne_zero x
  have hb := rowBound_pos g
  have he := rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x))
  have hbd := coordinates_le_transformed_energy g (cosetRow x)
  change ‖rowCoordinates (cosetRow x)‖ ≤ rowBound g *
    Real.sqrt (rowEnergy (rowOperator g (embeddedRow x))) at hbd
  have hle : (‖rowCoordinates (cosetRow x)‖ / rowBound g) ^ 2 ≤
      rowEnergy (rowOperator g (embeddedRow x)) := by
    have hd : ‖rowCoordinates (cosetRow x)‖ / rowBound g ≤
        Real.sqrt (rowEnergy (rowOperator g (embeddedRow x))) :=
      (div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hbd)
    have hsq := Real.sq_sqrt he.le
    nlinarith [div_pos hn hb, Real.sqrt_nonneg (rowEnergy (rowOperator g (embeddedRow x)))]
  have hp := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (div_pos hn hb)) hle (by linarith : -s.re ≤ 0)
  convert hp using 1
  rw [← Real.rpow_natCast_mul (div_nonneg hn.le hb.le) 2 (-s.re),
    Real.div_rpow hn.le hb.le]
  simp only [Nat.cast_ofNat, mul_neg, Real.rpow_neg hb.le, div_eq_mul_inv, inv_inv]
  exact mul_comm _ _

section
variable (hs : 2 < s.re)
include hs

theorem summable_norm_summand  :
    Summable (fun x : CuspCosets => ‖summand g s x‖) := by
  have hsum := summable_integer_four_rpow (2*s.re) (by linarith)
  have hinj :=
    rowCoordinates_injective.comp cosetRow_injective
  have hcomp : Summable (fun x : CuspCosets => ‖rowCoordinates (cosetRow x)‖ ^ (-(2*s.re))) := by
    apply (hsum.comp_injective hinj).congr
    intro x
    rfl
  exact (hcomp.mul_left ((rowBound g) ^ (2*s.re))).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun x => norm_summand_bound g s (by linarith) x)

theorem summable_summand  :
    Summable (summand g s) := (summable_norm_summand g s hs).of_norm
end


def eisenstein  : ℂ := ∑' x : CuspCosets, summand g s x
end


section
variable (M : levelThree) (g : SL(2,ℂ))
include M g

lemma transformedRow_rightEquiv  (x : CuspCosets) :
    rowOperator g (embeddedRow (rightEquiv M x)) =
      rowOperator (complexMatrix M * g) (embeddedRow x) := by
  rw [embeddedRow_rightEquiv, ← rowOperator_apply, rowOperator_mul]

lemma summand_automorphy  (s : ℂ) (x : CuspCosets) :
    summand (complexMatrix M * g) s x =
      complexCharacter M * summand g s (rightEquiv M x) := by
  have hM : complexCharacter M ≠ 0 := by
    intro h
    have hn := norm_complexCharacter M
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  simp only [summand, cosetCharacter_rightEquiv, transformedRow_rightEquiv,
    mul_inv_rev]
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hM, one_mul]

theorem eisenstein_automorphy  (s : ℂ) (hs : 2 < s.re) :
    eisenstein (complexMatrix M * g) s = complexCharacter M * eisenstein g s := by
  have hleft := summable_summand (complexMatrix M * g) s hs
  have hright := summable_summand g s hs
  have hreindex := (rightEquiv M).hasSum_iff.mpr hright.hasSum
  have hscale := hreindex.mul_left (complexCharacter M)
  exact hleft.hasSum.unique (hscale.congr_fun (fun x => summand_automorphy M g s x))
end


lemma norm_summand_strip (g : SL(2,ℂ)) (a b : ℝ) (s : ℂ)
    (ha : a ≤ s.re) (hb : s.re ≤ b) (x : CuspCosets) :
    ‖summand g s x‖ ≤ ‖summand g (a : ℂ) x‖ + ‖summand g (b : ℂ) x‖ := by
  simp only [norm_summand, Complex.ofReal_re]
  have hq := rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x))
  by_cases hq1 : 1 ≤ rowEnergy (rowOperator g (embeddedRow x))
  · exact (Real.rpow_le_rpow_of_exponent_le hq1 (neg_le_neg ha)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hq.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge hq (le_of_not_ge hq1)
        (neg_le_neg hb)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hq.le _))

end

open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

section
variable (z : ℂ) (v : ℝ)
include z v

section
variable (hv : 0 < v)
include hv

def upperSection  : SL(2,ℂ) :=
  ⟨!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹], by
    have hr := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hv).ne'
    simp [Matrix.det_fin_two, hr]⟩

section
variable (u : Fin 2 → ℂ)
include u

lemma rowOperator_upperSection_zero  :
    rowOperator (upperSection z v hv) u 0 = u 0 * (Real.sqrt v : ℂ) := by
  change Matrix.vecMul u (!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹]) _ = _
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

lemma rowOperator_upperSection_one  :
    rowOperator (upperSection z v hv) u 1 = (u 0*z + u 1) / (Real.sqrt v : ℂ) := by
  change Matrix.vecMul u (!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹]) _ = _
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring
end
end


def heightDenominator  (u : Fin 2 → ℂ) : ℝ :=
  ‖u 0*z + u 1‖ ^ 2 + ‖u 0‖ ^ 2 * v ^ 2

section
variable (hv : 0 < v) (u : Fin 2 → ℂ)
include hv u

lemma rowEnergy_upperSection  :
    rowEnergy (rowOperator (upperSection z v hv) u) = heightDenominator z v u / v := by
  rw [rowEnergy, rowOperator_upperSection_zero, rowOperator_upperSection_one,
    norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg v),
    mul_pow, div_pow, Real.sq_sqrt hv.le]
  unfold heightDenominator
  field_simp
  ring

lemma heightDenominator_pos  (hu : u ≠ 0) : 0 < heightDenominator z v u := by
  have h := rowEnergy_pos _ (rowOperator_ne_zero (upperSection z v hv) u hu)
  rw [rowEnergy_upperSection] at h
  exact ((div_pos_iff.mp h).resolve_right (by rintro ⟨_,hneg⟩; linarith)).1
end


def transformedHeight  (u : Fin 2 → ℂ) : ℝ :=
  v / heightDenominator z v u

section
variable (hv : 0 < v) (s : ℂ)
include hv s

lemma summand_upperSection  (x : CuspCosets) :
    summand (upperSection z v hv) s x = (cosetCharacter x)⁻¹ *
      (transformedHeight z v (embeddedRow x) : ℂ) ^ s := by
  rw [summand, rowEnergy_upperSection]
  congr 1
  have hq := heightDenominator_pos z v hv (embeddedRow x) (embeddedRow_ne_zero x)
  have hinv : (transformedHeight z v (embeddedRow x) : ℂ) =
      ((heightDenominator z v (embeddedRow x) / v : ℝ) : ℂ)⁻¹ := by
    simp only [transformedHeight, Complex.ofReal_div, inv_div]
  rw [hinv, Complex.inv_cpow_ofReal_nonneg (div_nonneg hq.le hv.le), Complex.cpow_neg]

def upperEisenstein  : ℂ :=
  eisenstein (upperSection z v hv) s
end
end


lemma ofReal_rowEnergy (u : Fin 2 → ℂ) :
    (rowEnergy u : ℂ) = dotProduct u (star u) := by
  simp only [rowEnergy, Complex.ofReal_add, ← Complex.normSq_eq_norm_sq, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, Complex.mul_conj]

lemma rowEnergy_unitary (k : SL(2,ℂ))
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (u : Fin 2 → ℂ) : rowEnergy (rowOperator k u) = rowEnergy u := by
  apply Complex.ofReal_injective
  rw [ofReal_rowEnergy, ofReal_rowEnergy, rowOperator_apply, Matrix.star_vecMul,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  have hu := Matrix.mem_unitaryGroup_iff.mp hk
  change (k : Matrix (Fin 2) (Fin 2) ℂ) *
    Matrix.conjTranspose (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 at hu
  rw [hu, Matrix.vecMul_one]

theorem eisenstein_right_unitary (g k : SL(2,ℂ)) (s : ℂ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    eisenstein (g*k) s = eisenstein g s := by
  apply tsum_congr
  intro x
  simp only [summand, ← rowOperator_mul, rowEnergy_unitary k hk]






