module
public import OAI.NumberTheory.DirichletL.Foundation
public import OAI.NumberTheory.DirichletL.Descent.IdealMasks
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped Classical
open CompletedGauss

local notation "Eis" => ActualEisensteinCubic.O

def markedCompletedT (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) : ℂ :=
  ∑' I : Ideal Eis, ∑' J : Ideal Eis, summand Ψ W X I J * d (I * J ^ 3)

section
variable (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ)
include Ψ W hW X hX d
theorem markedCompletedT_summable :
    Summable (fun p : Ideal Eis × Ideal Eis =>
      summand Ψ W X p.1 p.2 * d (p.1 * p.2 ^ 3)) := by
  pm_1371
  intro p hp hz
  simp_all

theorem markedCompletedT_eq_tsum :
    markedCompletedT Ψ W X d = ∑' p : Ideal Eis × Ideal Eis,
      summand Ψ W X p.1 p.2 * d (p.1 * p.2 ^ 3) :=
  (markedCompletedT_summable Ψ W hW X hX d).tsum_prod.symm
end

theorem markedCompletedT_const_mul (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (c : ℂ) (d : Ideal Eis → ℂ) :
    markedCompletedT Ψ W X (fun A => c * d A) = c * markedCompletedT Ψ W X d := by
  simp only [markedCompletedT, mul_left_comm _ c, tsum_mul_left]

theorem markedCompletedT_finset_sum {ι : Type*} (s : Finset ι)
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) (d : ι → Ideal Eis → ℂ) :
    markedCompletedT Ψ W X (fun A => ∑ i ∈ s, d i A) =
      ∑ i ∈ s, markedCompletedT Ψ W X (d i) := by
  simp only [markedCompletedT_eq_tsum Ψ W hW X hX, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i _ => markedCompletedT_summable Ψ W hW X hX (d i))

def markedExpandedTerm (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (I H J : Ideal Eis) : ℂ :=
  expandedTerm Ψ W X I H J * d (I * (H * J) ^ 3)

section
variable (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
include Ψ W
theorem markedExpandedTerm_finite_support
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (Function.support (fun p : Ideal Eis × Ideal Eis × Ideal Eis =>
      markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite := by
  apply (finite_support_expandedTerm Ψ W hW X hX).subset
  intro p hp hz
  apply hp
  simp only [markedExpandedTerm, hz, zero_mul]

theorem markedExpandedTerm_scale (X : ℝ)
    (d : Ideal Eis → ℂ) (I H J : Ideal Eis) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      (summand Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) I J * d (H ^ 3 * (I * J ^ 3))) =
      markedExpandedTerm Ψ W X d I H J := by
  rw [← mul_assoc, expandedTerm_scale]
  unfold markedExpandedTerm
  congr 2
  ring

theorem weighted_markedCompletedT_reopen (X : ℝ)
    (d : Ideal Eis → ℂ) (H : Ideal Eis) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A)) =
      ∑' I : Ideal Eis, ∑' J : Ideal Eis, markedExpandedTerm Ψ W X d I H J := by
  simp only [markedCompletedT, ← tsum_mul_left, markedExpandedTerm_scale]

theorem marked_cube_inner_inverse
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X)
    (d : Ideal Eis → ℂ) (I : Ideal Eis) :
    (∑' H : Ideal Eis, ∑' J : Ideal Eis, markedExpandedTerm Ψ W X d I H J) =
      (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
        Vstar W ((Ideal.absNorm I : ℝ) / X)) * d I := by
  let f : Ideal Eis → ℂ := fun B =>
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm B : ℝ) ^ 3 / X) * d (I * B ^ 3)
  have heq (H J : Ideal Eis) :
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) * f (H * J) =
        markedExpandedTerm Ψ W X d I H J := by
    simp only [f, markedExpandedTerm, expandedTerm, map_mul, Nat.cast_mul, mul_pow,
      mul_assoc]
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  have hp : (Function.support (fun p : Ideal Eis × Ideal Eis =>
      markedExpandedTerm Ψ W X d I p.1 p.2)).Finite := by
    change ((fun p : Ideal Eis × Ideal Eis => (I, p)) ⁻¹'
      Function.support (fun p : Ideal Eis × Ideal Eis × Ideal Eis =>
        markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite
    pm_6496
  have hgeneric := ideal_cube_convolution (cubeWeight Ψ) (cubeWeight_zero Ψ) f
    (by simpa only [heq] using hp)
  pm_546 heq f map_one Nat.cast_one one_pow mul_one hgeneric

theorem marked_cube_inverse_vstar
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (∑' H : Ideal Eis, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A))) =
    ∑' I : Ideal Eis, (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X)) * d I := by
  let F : Ideal Eis × Ideal Eis × Ideal Eis → ℂ :=
    fun p => markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2
  have hF : Summable F :=
    summable_of_hasFiniteSupport (markedExpandedTerm_finite_support Ψ W hW X hX d)
  let e : (Ideal Eis × Ideal Eis × Ideal Eis) ≃ (Ideal Eis × Ideal Eis × Ideal Eis) := {
    toFun := fun p => (p.2.1, p.1, p.2.2)
    invFun := fun p => (p.2.1, p.1, p.2.2)
    left_inv := by rintro ⟨I, H, J⟩; rfl
    right_inv := by rintro ⟨I, H, J⟩; rfl }
  pm_6497
  calc
    _ = ∑' H : Ideal Eis, ∑' I : Ideal Eis, ∑' J : Ideal Eis,
        markedExpandedTerm Ψ W X d I H J := by
      simp only [weighted_markedCompletedT_reopen]
    _ = ∑' p : Ideal Eis × Ideal Eis × Ideal Eis, F (e p) := by
      pm_7238
    _ = ∑' p : Ideal Eis × Ideal Eis × Ideal Eis, F p := e.tsum_eq F
    _ = ∑' I : Ideal Eis, ∑' H : Ideal Eis, ∑' J : Ideal Eis,
        markedExpandedTerm Ψ W X d I H J := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (marked_cube_inner_inverse Ψ W hW X hX d)

theorem marked_cube_inverse
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (Real.sqrt X : ℂ)⁻¹ *
      (∑' I : Ideal Eis, columnWeight Ψ I * d I * W ((Ideal.absNorm I : ℝ) / X)) =
    ∑' H : Ideal Eis, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
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
