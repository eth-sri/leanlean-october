module

public import OAI.NumberTheory.DirichletL.Descent.Completion

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped Classical
open CompletedGauss

theorem marked_cube_inverse_finite_support (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal ActualEisensteinCubic.O → ℂ) :
    (Function.support (fun H : Ideal ActualEisensteinCubic.O =>
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
        markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H^3*A)))).Finite := by
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  apply (hf.image (fun p => p.2.1)).subset
  intro H hH
  by_contra hn
  have hzero : ∀ I J, markedExpandedTerm Ψ W X d I H J = 0 := by
    intro I J
    by_contra hz
    exact hn ⟨(I, H, J), hz, rfl⟩
  apply hH
  dsimp only
  rw [weighted_markedCompletedT_reopen]
  simp_all

theorem marked_large_cube_inner_reopen (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (d : Ideal ActualEisensteinCubic.O → ℂ) (I : Ideal ActualEisensteinCubic.O) :
    (∑' H : Ideal ActualEisensteinCubic.O,∑' J : Ideal ActualEisensteinCubic.O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0) =
    ∑' B : Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let f : Ideal ActualEisensteinCubic.O → ℂ := fun B =>
    columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I : ℝ) : ℂ)*
      Vstar W ((Ideal.absNorm I : ℝ)*(Ideal.absNorm B : ℝ)^3/X)*d (I*B^3)
  have heq (H J : Ideal ActualEisensteinCubic.O) :
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ (H*J)*f (H*J)=markedExpandedTerm Ψ W X d I H J := by
    simp only [f,markedExpandedTerm,expandedTerm,map_mul,Nat.cast_mul,mul_pow,mul_assoc]
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  have hp : (Function.support (fun p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O => markedExpandedTerm Ψ W X d I p.1 p.2)).Finite := by
    change ((fun p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O => (I,p)) ⁻¹'
      Function.support (fun p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O => markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (by simp) hf
  have hg := large_cube_convolution H₀ (cubeWeight Ψ) (cubeWeight_zero Ψ) f (by simp_all)
  rw [show (∑' H : Ideal ActualEisensteinCubic.O, ∑' J : Ideal ActualEisensteinCubic.O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0)=
      ∑' B : Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*cubeWeight Ψ B*f B by simp_all]
  apply tsum_congr
  intro B
  dsimp [f,summand]
  ring

theorem marked_large_cube_reopen (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (d : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑' H : Ideal ActualEisensteinCubic.O, if H₀ ≤ (Ideal.absNorm H : ℝ) then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        markedCompletedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) (fun A => d (H^3*A)) else 0) =
    ∑' I : Ideal ActualEisensteinCubic.O,∑' B : Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let F : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O → ℂ := fun p =>
    if H₀ ≤ (Ideal.absNorm p.2.1 : ℝ) then markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2 else 0
  have hF : Summable F := summable_of_hasFiniteSupport
    ((markedExpandedTerm_finite_support Ψ W hW X hX d).subset (by
      intro p hp
      by_contra hn
      have he : markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2=0 := not_ne_iff.mp hn
      exact hp (by grind)))
  let e : (Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) ≃ (Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) := {
    toFun := fun p => (p.2.1,p.1,p.2.2)
    invFun := fun p => (p.2.1,p.1,p.2.2)
    left_inv := by grind
    right_inv := by grind }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal ActualEisensteinCubic.O,∑' I : Ideal ActualEisensteinCubic.O,∑' J : Ideal ActualEisensteinCubic.O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0 := by
      apply tsum_congr
      intro H
      by_cases h : H₀ ≤ (Ideal.absNorm H : ℝ)
      · simp only [ite_eq_left h,weighted_markedCompletedT_reopen]
      · simp only [ite_eq_right h,tsum_zero]
    _ = ∑' p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O,F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O,F p := e.tsum_eq F
    _ = ∑' I : Ideal ActualEisensteinCubic.O,∑' H : Ideal ActualEisensteinCubic.O,∑' J : Ideal ActualEisensteinCubic.O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0 := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (marked_large_cube_inner_reopen Ψ W hW X H₀ hX d)

theorem marked_completed_cube_inverse_split (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (d : Ideal ActualEisensteinCubic.O → ℂ) :
    (Real.sqrt X : ℂ)⁻¹*(∑' I : Ideal ActualEisensteinCubic.O,columnWeight Ψ I*d I*W ((Ideal.absNorm I : ℝ)/X)) =
    (∑' H : Ideal ActualEisensteinCubic.O, if (Ideal.absNorm H : ℝ)<H₀ then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        markedCompletedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) (fun A => d (H^3*A)) else 0) +
    ∑' I : Ideal ActualEisensteinCubic.O,∑' B : Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let f := fun H : Ideal ActualEisensteinCubic.O => (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
    markedCompletedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) (fun A => d (H^3*A))
  have hf := marked_cube_inverse_finite_support Ψ W hW X hX d
  have hs : Summable (fun H : Ideal ActualEisensteinCubic.O => if (Ideal.absNorm H : ℝ)<H₀ then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      simp_all))
  have hl : Summable (fun H : Ideal ActualEisensteinCubic.O => if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      simp_all))
  rw [marked_cube_inverse Ψ W hW X hX d,←marked_large_cube_reopen Ψ W hW X H₀ hX d]
  change (∑' H,f H)=(∑' H,if (Ideal.absNorm H : ℝ)<H₀ then f H else 0)+
    ∑' H,if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0
  rw [← hs.tsum_add hl]
  grind

end
end SevenEighths.InverseMoment

end OAI
