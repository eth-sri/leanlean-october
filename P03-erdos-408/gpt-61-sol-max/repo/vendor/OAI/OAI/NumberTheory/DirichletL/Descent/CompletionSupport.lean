module

public import OAI.NumberTheory.DirichletL.Descent.CompletionSplit

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge


section
variable (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P) (W : ℝ → ℂ) (hW hWc : HasCompactSupport W) (b X H₀ : ℝ) (hX : 0<X) (B : Ideal ActualEisensteinCubic.O) (hB : B≠0) (d : Ideal ActualEisensteinCubic.O → ℂ)

include hW hX in
theorem marked_large_cube_sum_comm    
            :
    (∑'I:Ideal ActualEisensteinCubic.O,∑'B:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3)) =
      ∑'B:Ideal ActualEisensteinCubic.O,∑'I:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let a : Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O → ℂ := fun p=>largeCubeCoefficient H₀ p.2*summand Ψ W X p.1 p.2*d (p.1*p.2^3)
  have hf : (Function.support a).Finite :=
    (completedT_finite_support Ψ W hW X hX).subset (by
      intro p hp
      exact fun h=>hp (by simp only [a,h,mul_zero,zero_mul]))
  have hs : Summable a := summable_of_hasFiniteSupport hf
  let e := Equiv.prodComm (Ideal ActualEisensteinCubic.O) (Ideal ActualEisensteinCubic.O)
  have ht : Summable (fun p=>a (e p)) := e.summable_iff.mpr hs
  calc
    _ = ∑'p:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O,a p := hs.tsum_prod.symm
    _ = ∑'p:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O,a (e p) := (e.tsum_eq a).symm
    _ = _ := ht.tsum_prod

include hSp hm hWc hX in
theorem marked_large_cube_sum_finite    
           
           
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) (d : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑'I:Ideal ActualEisensteinCubic.O,∑'B:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand (rowTwist Ψ m f z) W X I B*d (I*B^3)) =
      ∑B∈outsideIdealsUpTo S D,largeCubeCoefficient H₀ B*
        ∑'I:Ideal ActualEisensteinCubic.O,summand (rowTwist Ψ m f z) W X I B*d (I*B^3) := by
  rw [marked_large_cube_sum_comm _ W hWc X H₀ hX d]
  simp only [mul_assoc, tsum_mul_left]
  apply tsum_eq_sum
  intro B hB
  have hz : ∀I:Ideal ActualEisensteinCubic.O,summand (rowTwist Ψ m f z) W X I B=0 := by
    intro I
    by_contra hn
    exact hB (summand_cube_support S D hSp Ψ m f z hm W b X hX hW hD I B hn)
  simp only [hz,tsum_zero,mul_zero,zero_mul]

include hX hB in
theorem marked_inner_completed_sum        
          :
    (∑'I:Ideal ActualEisensteinCubic.O,summand Ψ W X I B*d (I*B^3)) =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        ∑'I:Ideal ActualEisensteinCubic.O,columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))*d (I*B^3) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := div_pos hX (pow_pos hN _)
  have ht (I:Ideal ActualEisensteinCubic.O) : summand Ψ W X I B =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        (columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
    have harg : (Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X =
        (Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3) := by
      rw [div_div_eq_mul_div]
    have hn := vstar_source_normalization Ψ W (X/(Ideal.absNorm B:ℝ)^3) hY I
    calc
      _ = cubeWeight Ψ B * (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ) *
          Vstar W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
        rw [summand,harg]
        ring
      _ = _ := by rw [hn]; ring
  simp_rw [ht]
  simp only [mul_assoc, tsum_mul_left]

end


end SevenEighths.InverseMoment

end OAI
