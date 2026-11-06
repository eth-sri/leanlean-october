module

public import OAI.NumberTheory.DirichletL.Descent.SecondSourceEncoding
public import OAI.NumberTheory.DirichletL.Descent.SecondCauchy

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers IdealMobiusDivisorSum
open InverseInitialArithmetic (sourceIdeal sourceIdeal_ne_zero)
noncomputable section

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def actualSecondChild {Jo Jn } (u v : ActualEisensteinCubic.Oˣ) (x : MarkedSecondSource ι Jo Jn)  :=
  secondChild (originalSecondTuple p u v (markedSecondOriginal p x))

def actualSecondTriples {Jo Jn } (u v : ActualEisensteinCubic.Oˣ)
    (source : Finset (MarkedSecondSource ι Jo Jn))  :=
  source.image (fun x => (actualSecondChild p u v x).1)

theorem actualSecondChild_nonzero (hp : ∀ i, p i ≠ 0)
    {Jo Jn : ℕ}  u v  (x : MarkedSecondSource ι Jo Jn) (ht : x.quotient ≠ 0) :
    (actualSecondChild p u v x).2.1 ≠ 0 ∧
    (actualSecondChild p u v x).1.q0 ≠ 0 ∧
    (actualSecondChild p u v x).1.quotient ≠ 0 ∧
    (actualSecondChild p u v x).1.residual ≠ 0 := by
  have hj : Ideal.span {(jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)} ≠ (0 : Ideal ActualEisensteinCubic.O) :=
    Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)
  have hb : Ideal.span {(b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)} ≠ (0 : Ideal ActualEisensteinCubic.O) :=
    Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)
  change _ ≠ 0 ∧ _ ≠ 0 ∧ x.quotient ≠ 0 ∧ _ ≠ 0
  refine ⟨?_,hb,ht,sourceIdeal_ne_zero p hp _⟩
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hj (sourceIdeal_ne_zero p hp _))
    (sourceIdeal_ne_zero p hp _)) (sourceIdeal_ne_zero p hp _)

structure ActualSecondSourceConditions {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) : Prop where
  admissible : ∀ x ∈ source, x.cube.Admissible
  common_disjoint : ∀ x ∈ source, Disjoint x.firstCommon x.cube.support
  first_divisor : ∀ x ∈ source, x.firstDivisor ⊆ x.firstCommon∪x.cube.support
  second_divisor : ∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon
  old_support : ∀ x ∈ source, ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient
  new_support : ∀ x ∈ source, ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap
  quotient_nonzero : ∀ x ∈ source, x.quotient ≠ 0

section
variable (hp : ∀ i, p i ≠ 0) (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1) (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (hinj : Function.Injective (fun i => Ideal.span {p i})) {Jo Jn : ℕ} (u v : ActualEisensteinCubic.Oˣ) (source : Finset (MarkedSecondSource ι Jo Jn)) (hs : ActualSecondSourceConditions p source) (c : SecondChild) (labels : Finset (Ideal ActualEisensteinCubic.O)) (rows : Finset ActualEisensteinCubic.O) (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows) (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) (w : MarkedSecondSource ι Jo Jn → ℝ) (hw : ∀ x ∈ source, w x ≤ 1)

include hp hpr hcop hinj hs ho hn hw in
theorem actual_second_fiber_weight  
     
     
     
         
       
         
        :
    ∑ x ∈ source with actualSecondChild p u v x = c, w x ≤ secondDivisorWeight K c := by
  by_cases he : (source.filter (fun x => actualSecondChild p u v x = c)).Nonempty
  · obtain ⟨x,hx⟩ := he
    obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
    obtain ⟨hf,hq,ht,hr⟩ := actualSecondChild_nonzero p hp u v x (hs.quotient_nonzero x hx)
    rw [he] at hf hq ht hr
    have hcard := actual_marked_second_source_fiber p hp hpr hcop hinj u v source
      hs.admissible hs.common_disjoint hs.first_divisor hs.second_divisor hs.old_support hs.new_support
      c.1 c.2.1 c.2.2 hf hq ht hr K ho hn
    calc
      _ ≤ ∑ _x ∈ source with actualSecondChild p u v _x = c, (1 : ℝ) :=
        Finset.sum_le_sum (fun x hx => hw x (Finset.mem_filter.mp hx).1)
      _ = ((source.filter (fun x => actualSecondChild p u v x = c)).card : ℝ) := by simp
      _ ≤ _ := by
        dsimp only [secondDivisorWeight,actualSecondChild]
        exact_mod_cast hcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simp only [Finset.sum_empty]
    unfold secondDivisorWeight
    positivity

include hp hpr hcop hinj hs hchild ho hn hw in
theorem actual_second_energy_projection  
     
     
     
         
     
       
     
         
         F  :
    ∑ x ∈ source, w x * ‖F (actualSecondChild p u v x)‖^2 ≤
      ∑ γ ∈ actualSecondTriples p u v source,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ := by
  have hm : ∀ x ∈ source, actualSecondChild p u v x ∈
      actualSecondTriples p u v source ×ˢ (labels ×ˢ rows) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x,hx,rfl⟩,Finset.mem_product.mpr (hchild x hx)⟩
  have hb := fiber_energy_bound source (actualSecondTriples p u v source ×ˢ (labels ×ˢ rows))
    (actualSecondChild p u v) w (secondDivisorWeight K) (fun c => ‖F c‖^2) hm
    (fun _ _ => sq_nonneg _) (fun c _ => actual_second_fiber_weight p hp hpr hcop hinj u v source hs c K ho hn w hw)
  apply hb.trans_eq
  simp only [Finset.sum_product,secondDivisorWeight,tripleDivisorWeight,secondLabelEnergy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro k hk
  ring

include hp hpr hcop hinj hs hchild ho hn in
theorem actual_second_weighted_count  
     
     
     
         
     
       
     
         
    (w : MarkedSecondSource ι Jo Jn → ℂ) (hw : ∀ x ∈ source, ‖w x‖ ≤ 1)
     F G  :
    ‖∑ x ∈ source, w x * F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v source,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v source,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows G γ) := by
  apply (DescentWeightedCauchy.weighted_cauchy source w (F ∘ actualSecondChild p u v)
    (G ∘ actualSecondChild p u v)).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (actual_second_energy_projection p hp hpr hcop hinj u v source hs labels rows hchild K ho hn (fun x => ‖w x‖) hw F))
    (Real.sqrt_le_sqrt (actual_second_energy_projection p hp hpr hcop hinj u v source hs labels rows hchild K ho hn (fun x => ‖w x‖) hw G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end

end
end SevenEighths.InverseMoment

end OAI
