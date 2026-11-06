module

public import OAI.NumberTheory.PrimeGaps.PatternMoments
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set MeasureTheory








open scoped Convolution Pointwise

@[simp] theorem weightedBlock_zero (X h a m : ℕ)
    (F : (Fin 0 → ℝ) → ℝ) (k : Setoid (Fin 0) → ℝ) :
    weightedBlock X h a F k m=k ⊥*F 0 := by
  unfold weightedBlock
  simp only [divisorSum_fin_zero]
  have he (b : Fin 0 → Fin h) : Setoid.ker b=⊥ := by
    apply Setoid.ext
    intro i
    exact Fin.elim0 i
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,pow_zero,one_nsmul]

noncomputable def matchedPattern {n : ℕ} (e : Equiv.Perm (Fin n)) : Setoid (Fin (n+n)) :=
  Setoid.ker (permutedLabels e)

@[simp] theorem matchedPattern_left {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Setoid.comap (Fin.castAdd n) (matchedPattern e)=⊥ := by
  apply Setoid.ext
  intro i j
  change permutedLabels e (i.castAdd n)=permutedLabels e (j.castAdd n) ↔ i=j
  simp [permutedLabels]

@[simp] theorem matchedPattern_right {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Setoid.comap (Fin.natAdd n) (matchedPattern e)=⊥ := by
  apply Setoid.ext
  intro i j
  change permutedLabels e (i.natAdd n)=permutedLabels e (j.natAdd n) ↔ i=j
  simp [permutedLabels]

@[simp] theorem cumulativeProfile_fin_zero {tau : ℝ} (f : (Fin 0 → ℝ) → ℝ)
    (hsf : tsupport f⊆positiveSimplex 0 tau) (v : Fin 0 → ℝ) :
    cumulativeProfile tau f v=f 0 := by
  rw [cumulativeProfile_tail tau f hsf v (by simp)]
  rw [Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  have he : Ici v=(Set.univ : Set (Fin 0 → ℝ)) := by
    ext x
    simp only [Set.mem_Ici,Set.mem_univ,iff_true]
    exact by simp
  simp_all

@[simp] theorem l2Mass_fin_zero (f : (Fin 0 → ℝ) → ℝ) : l2Mass f=f 0^2 := by
  unfold l2Mass
  have he : (fun x => f x^2)=(fun _ : Fin 0 → ℝ => f 0^2) := by
    funext x
    rw [Subsingleton.elim x 0]
  simp [he,Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]

end LargePrimeGaps

end OAI
