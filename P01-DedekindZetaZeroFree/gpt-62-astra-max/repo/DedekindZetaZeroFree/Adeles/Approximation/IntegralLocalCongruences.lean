module

public import DedekindZetaZeroFree.Adeles.Approximation.IntegralProductCRTDensity
public import DedekindZetaZeroFree.Arithmetic.LocalFields.ValuationBallsAndIntegrality

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

open NumberField IsDedekindDomain

theorem sIntegral_crt
    (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (y : (v : S) → v.val.adicCompletionIntegers F)
    (n : S → ℕ) :
    ∃ a : RingOfIntegers F, ∀ v : S,
      (Valued.v (y v - algebraMap F (v.val.adicCompletion F) (a : F)) :
        WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-(n v : ℤ)) := by
  classical

  set x : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletionIntegers F :=
    fun w => if hw : w ∈ S then y ⟨w, hw⟩ else 0 with hx
  set m : HeightOneSpectrum (𝓞 F) → ℕ :=
    fun w => if hw : w ∈ S then n ⟨w, hw⟩ else 0 with hm

  set U : (w : HeightOneSpectrum (𝓞 F)) → Set (w.adicCompletionIntegers F) :=
    fun w => {z | (z -
      ((x w : w.adicCompletionIntegers F) : w.adicCompletion F)) ∈
        PoissonSLocalBalls.ball F w (m w)} with hU
  obtain ⟨a, ha⟩ := exists_ringOfIntegers_integralDiagonal_mem_finite_open F S x U
    (fun w _ => ⟨by
        rw [hU]
        exact (PoissonSLocalBalls.ball_isOpen F w (m w)).preimage (continuous_subtype_val.sub continuous_const)
      , by
        rw [hU]
        simp only [Set.mem_setOf_eq, sub_self]
        exact (PoissonSLocalBalls.ball F w (m w)).zero_mem⟩)
  refine ⟨a, fun v => ?_⟩
  have hv := ha v v.property
  rw [hU] at hv
  simp only [Set.mem_setOf_eq] at hv
  rw [PoissonSLocalBalls.mem_ball] at hv

  have hxv : x v = y v := by
    rw [hx]
    simp
  have hmv : m v = n v := by
    rw [hm]
    simp

  have hB : (algebraMap (𝓞 F) (v.val.adicCompletionIntegers F) a :
        v.val.adicCompletion F) =
      algebraMap F (v.val.adicCompletion F) (a : F) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    exact congrFun (HeightOneSpectrum.algebraMap_adicCompletion (𝓞 F) F v.val) a
  rw [hB, hxv, hmv] at hv
  rw [Valuation.map_sub_swap]
  exact hv

end DedekindZetaZeroFree

end
