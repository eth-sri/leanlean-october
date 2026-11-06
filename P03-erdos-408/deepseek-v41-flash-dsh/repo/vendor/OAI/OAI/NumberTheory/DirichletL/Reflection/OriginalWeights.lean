module

public import OAI.NumberTheory.DirichletL.Reflection.ActualSelected

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase

open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def frozenInactiveWeight (J F Q Q₀ : Ideal Eis) (A : Finset (FreeReflection.pool J Q Q₀)) : ℂ :=
  ∏ b∈(Finset.univ:Finset (FreeReflection.pool J Q Q₀))\A,
    if completedLocalExponent J F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0

lemma one_sub_inverse_norm_le_one (I : Ideal Eis) (hI : I≠0) :
    ‖1-(Ideal.absNorm I:ℂ)⁻¹‖≤1 := by
  have hn : (1:ℝ)≤Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hi : (Ideal.absNorm I:ℝ)⁻¹≤1 := inv_le_one_of_one_le₀ hn
  have he : (1-(Ideal.absNorm I:ℂ)⁻¹)=((1-(Ideal.absNorm I:ℝ)⁻¹):ℝ) := by push_cast;rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  have hp : 0≤(Ideal.absNorm I:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  linarith

lemma frozenInactiveWeight_norm (J F Q Q₀ : Ideal Eis) (A : Finset (FreeReflection.pool J Q Q₀)) :
    ‖frozenInactiveWeight J F Q Q₀ A‖≤1 := by
  unfold frozenInactiveWeight
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro b hb
    exact norm_nonneg _
  · intro b hb
    split_ifs
    · exact one_sub_inverse_norm_le_one b.val
        (NeZero.ne ((poolPrimeFamily J Q Q₀).ideal b))
    · simp

end
end SevenEighths.InverseReflectedPhase

end OAI
