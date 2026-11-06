module
public import OAI.NumberTheory.DirichletL.Descent.CompletedReopening
public import OAI.NumberTheory.DirichletL.Descent.ReopenedPriority
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

section
variable {σ : Type*} [DecidableEq σ]
include σ
theorem complete_pool_whole_cube_mark
    (F : Finset (Ideal O)) (hF : ∀ I∈F,Admissible I)
    (slots : Finset σ) (lists : σ→ Finset (primePool F)) (a : σ→ primePool F→ℂ)
    (T : Finset (primePool F)) (v : primePool F→₀ℕ) :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a
      ((∏i∈T,i.val)*cubeIdeal F v^3) = primeMark slots lists a (T∪v.support) := by
  pm_3763
  pm_3731
  have he := reopened_whole_mark_divisibility (poolPrimary F) hinj slots lists a T v
  pm_3732
  rw [hspan,cubeIdeal_eq_primeProduct_span F hF v] at he
  simpa only [indexedIdealMark,poolPrimary_span F hF] using he.symm

theorem reopened_marked_global_column
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (b X : ℝ) (hb : 0≤b) (hX : 0<X)
    (hW : ∀ t,W t≠0→ t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→ Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→ primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let Y := X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3
    (∑' I:Ideal O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I*W ((Ideal.absNorm I:ℝ)/Y)*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3)) =
    fixedChildRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ Ψ m
      (fun T=>primeMark slots lists a (T∪v.support)*W (primeProductNorm (poolPrimary F) T/Y)) f z := by
  pm_3764
  pm_3763
  let Y := X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3
  have hN := norm_at_least_one (cubeIdeal F v) (cubeIdeal_ne_zero F v)
  pm_3693 hY Y
  have hYD : b*Y≤D := (mul_le_mul_of_nonneg_left
    (div_le_self hX.le (one_le_pow₀ hN)) hb).trans hD
  have he := marked_complete_pool_eq_global S D hbad hSp Ψ m f z W b Y hY hW hYD
    (fun I=>indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3))
  dsimp only at he ⊢
  rw [←he]
  congr 1
  funext T
  rw [complete_pool_whole_cube_mark F hF slots lists a T v,mul_comm]
end

end
end SevenEighths.InverseMoment

end OAI
