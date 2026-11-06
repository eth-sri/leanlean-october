module
public import OAI.NumberTheory.DirichletL.Foundation
public import OAI.NumberTheory.DirichletL.Descent.Marks
public import OAI.NumberTheory.DirichletL.Descent.LocalReflection
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open FirstPassCubeLabels
open SecondPassArithmetic

noncomputable local instance markedQuotientField (P : Ideal ActualEisensteinCubic.O)
    [P.IsMaximal] : Field (ActualEisensteinCubic.O ⧸ P) := Ideal.Quotient.field P

noncomputable local instance markedQuotientFintype (P : Ideal ActualEisensteinCubic.O)
    [P.IsMaximal] : Fintype (ActualEisensteinCubic.O ⧸ P) := Fintype.ofFinite _

section
variable (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
include P hg
theorem actual_marked_active_eq
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (σ ε : (ActualEisensteinCubic.O ⧸ P)ˣ) (x : ActualEisensteinCubic.O ⧸ P) :
    localReflectionActive zeroMark (CompletedGauss.actualSextic P hg) ψ σ ε x =
      -LocalReflectionBrackets.activeRow (CompletedGauss.actualSextic P hg) ψ 0 σ ε x := by
  simpa only [localReflectionActive, localFourier,
    LocalReflectionBrackets.activeRow, pow_zero] using
    marked_active_eq_neg_trivial (CompletedGauss.actualSextic P hg) ψ hψ σ ε x

theorem actual_marked_active_formula
    (hchar : ringChar (ActualEisensteinCubic.O ⧸ P) ≠ 2)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (σ ε : (ActualEisensteinCubic.O ⧸ P)ˣ) (x : ActualEisensteinCubic.O ⧸ P) :
    localReflectionActive zeroMark (CompletedGauss.actualSextic P hg) ψ σ ε x =
      (LocalReflectionBrackets.rootCard (ActualEisensteinCubic.O ⧸ P) : ℂ)⁻¹ *
        LocalReflectionBrackets.tau (CompletedGauss.actualSextic P hg) ψ 2 *
        (((CompletedGauss.actualSextic P hg) ^ 2)⁻¹)
          ((σ : ActualEisensteinCubic.O ⧸ P) * (ε : ActualEisensteinCubic.O ⧸ P) * x) := by
  rw [actual_marked_active_eq P hg ψ hψ σ ε x,
    LocalReflectionBrackets.canonical_A5_normalized P hg hchar ψ hψ 0 (by norm_num)]
  simp only [LocalReflectionBrackets.phase, LocalReflectionBrackets.bracket,
    show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, inv_pow, map_mul]
  ring
end

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hcop

omit [DecidableEq ι] in
theorem row_slot_cross_phase
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k) :
    MixedCrossSeparation.crossSymbol p hg i k ^ 4 *
      MixedCrossSeparation.crossSymbol p hg k i ^ 2 = 1 := by
  have hs : MixedCrossSeparation.crossSymbol p hg i k ^ 2 =
      MixedCrossSeparation.crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary (Ideal.span {p i}) (Ideal.span {p k})
      (hg i) (hg k) (p i) (p k) rfl rfl (hpr i) (hpr k)
  pm_3791
  have h6 : MixedCrossSeparation.crossSymbol p hg i k ^ 6 = 1 := by
    pm_5427 MixedCrossSeparation.crossSymbol
  grind

omit [DecidableEq ι] in
theorem row_slot_product_phase
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1) (R P : Finset ι) (hRP : Disjoint R P) :
    (∏ i ∈ R, ∏ k ∈ P,
      MixedCrossSeparation.crossSymbol p hg i k ^ 4 *
        MixedCrossSeparation.crossSymbol p hg k i ^ 2) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  apply Finset.prod_eq_one
  intro k hk
  exact row_slot_cross_phase p hcop hg hpr i k (fun h =>
    (Finset.disjoint_left.mp hRP) hi (h.symm ▸ hk))

end

end SevenEighths.InverseMoment

end OAI
