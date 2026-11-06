module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Foundation
public import OAI.NumberTheory.DirichletL.Descent.IdealMasks

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss



def markedCompletedT (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal ActualEisensteinCubic.O → ℂ)  :=
  ∑' I : Ideal ActualEisensteinCubic.O, ∑' J : Ideal ActualEisensteinCubic.O, summand Ψ W X I J * d (I * J ^ 3)

section
variable (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (c : ℂ) (d : Ideal ActualEisensteinCubic.O → ℂ)

include hW hX in
theorem markedCompletedT_summable    
            :
    Summable (fun p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O =>
      summand Ψ W X p.1 p.2 * d (p.1 * p.2 ^ 3)) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp hz
  exact hp (by simp only [hz, zero_mul])

include hW hX in
theorem markedCompletedT_eq_tsum    
            :
    markedCompletedT Ψ W X d = ∑' p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O,
      summand Ψ W X p.1 p.2 * d (p.1 * p.2 ^ 3) :=
  (markedCompletedT_summable Ψ W hW X hX d).tsum_prod.symm

theorem markedCompletedT_const_mul      
        :
    markedCompletedT Ψ W X (fun A => c * d A) = c * markedCompletedT Ψ W X d := by
  simp only [markedCompletedT, mul_left_comm _ c, tsum_mul_left]

end

theorem markedCompletedT_finset_sum {ι : Type*} (s : Finset ι)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) (d : ι → Ideal ActualEisensteinCubic.O → ℂ) :
    markedCompletedT Ψ W X (fun A => ∑ i ∈ s, d i A) =
      ∑ i ∈ s, markedCompletedT Ψ W X (d i) := by
  simp only [markedCompletedT_eq_tsum Ψ W hW X hX, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i _ => markedCompletedT_summable Ψ W hW X hX (d i))

def markedExpandedTerm (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal ActualEisensteinCubic.O → ℂ) (I H J : Ideal ActualEisensteinCubic.O)  :=
  expandedTerm Ψ W X I H J * d (I * (H * J) ^ 3)

section
variable (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal ActualEisensteinCubic.O → ℂ) (I H J : Ideal ActualEisensteinCubic.O)

include hW hX in
theorem markedExpandedTerm_finite_support    
            :
    (Function.support (fun p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O =>
      markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite := by
  apply (finite_support_expandedTerm Ψ W hW X hX).subset
  simp_all [markedExpandedTerm]

theorem markedExpandedTerm_scale      
        :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      (summand Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) I J * d (H ^ 3 * (I * J ^ 3))) =
      markedExpandedTerm Ψ W X d I H J := by
  rw [← mul_assoc, expandedTerm_scale]
  unfold markedExpandedTerm
  congr 2
  ring

theorem weighted_markedCompletedT_reopen      
        :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A)) =
      ∑' I : Ideal ActualEisensteinCubic.O, ∑' J : Ideal ActualEisensteinCubic.O, markedExpandedTerm Ψ W X d I H J := by
  simp only [markedCompletedT, ← tsum_mul_left, markedExpandedTerm_scale]

include hW hX in
theorem marked_cube_inner_inverse    
         
        :
    (∑' H : Ideal ActualEisensteinCubic.O, ∑' J : Ideal ActualEisensteinCubic.O, markedExpandedTerm Ψ W X d I H J) =
      (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
        Vstar W ((Ideal.absNorm I : ℝ) / X)) * d I := by
  let f : Ideal ActualEisensteinCubic.O → ℂ := fun B =>
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm B : ℝ) ^ 3 / X) * d (I * B ^ 3)
  have heq (H J : Ideal ActualEisensteinCubic.O) :
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) * f (H * J) =
        markedExpandedTerm Ψ W X d I H J := by
    simp only [f, markedExpandedTerm, expandedTerm, map_mul, Nat.cast_mul, mul_pow,
      mul_assoc]
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  have hp : (Function.support (fun p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O =>
      markedExpandedTerm Ψ W X d I p.1 p.2)).Finite := by
    change ((fun p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O => (I, p)) ⁻¹'
      Function.support (fun p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O =>
        markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hgeneric := ideal_cube_convolution (cubeWeight Ψ) (cubeWeight_zero Ψ) f
    (by simpa only [heq] using hp)
  simpa only [heq, f, map_one, Nat.cast_one, one_pow, mul_one] using hgeneric

include hW hX in
theorem marked_cube_inverse_vstar    
            :
    (∑' H : Ideal ActualEisensteinCubic.O, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A))) =
    ∑' I : Ideal ActualEisensteinCubic.O, (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X)) * d I := by
  let F : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O → ℂ :=
    fun p => markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2
  have hF : Summable F :=
    summable_of_hasFiniteSupport (markedExpandedTerm_finite_support Ψ W hW X hX d)
  let e : (Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) ≃ (Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) := {
    toFun := fun p => (p.2.1, p.1, p.2.2)
    invFun := fun p => (p.2.1, p.1, p.2.2)
    left_inv := by rintro ⟨I, H, J⟩; rfl
    right_inv := by rintro ⟨I, H, J⟩; rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal ActualEisensteinCubic.O, ∑' I : Ideal ActualEisensteinCubic.O, ∑' J : Ideal ActualEisensteinCubic.O,
        markedExpandedTerm Ψ W X d I H J := by
      simp only [weighted_markedCompletedT_reopen]
    _ = ∑' p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O, F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O, F p := e.tsum_eq F
    _ = ∑' I : Ideal ActualEisensteinCubic.O, ∑' H : Ideal ActualEisensteinCubic.O, ∑' J : Ideal ActualEisensteinCubic.O,
        markedExpandedTerm Ψ W X d I H J := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (marked_cube_inner_inverse Ψ W hW X hX d)

include hW hX in
theorem marked_cube_inverse    
            :
    (Real.sqrt X : ℂ)⁻¹ *
      (∑' I : Ideal ActualEisensteinCubic.O, columnWeight Ψ I * d I * W ((Ideal.absNorm I : ℝ) / X)) =
    ∑' H : Ideal ActualEisensteinCubic.O, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A)) := by
  rw [marked_cube_inverse_vstar Ψ W hW X hX d, ← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [vstar_source_normalization Ψ W X hX I]
  ring

end

end

end SevenEighths.InverseMoment

end OAI
