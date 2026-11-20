module

public import DedekindZetaZeroFree.LFunctions.Hecke.NonprincipalRayContinuation
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalRayContinuation

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField

section

variable (F : Type*) [Field F] [NumberField F]

def heckeConductorScale
    (𝔪 : Ideal (𝓞 F)) : ℝ :=
  (|NumberField.discr F| : ℤ) * (Ideal.absNorm 𝔪 : ℝ)

theorem one_le_heckeConductorScale
    (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥) :
    1 ≤ heckeConductorScale F 𝔪 := by
  unfold heckeConductorScale
  have hd : (1 : ℝ) ≤ ((|NumberField.discr F| : ℤ) : ℝ) := by
    have h : (0 : ℤ) < |NumberField.discr F| := by
      rw [abs_pos]
      exact NumberField.discr_ne_zero F
    exact_mod_cast h
  have hm' : (1 : ℝ) ≤ (Ideal.absNorm 𝔪 : ℝ) := by
    have h : 1 ≤ Ideal.absNorm 𝔪 := by
      rw [Nat.one_le_iff_ne_zero]
      exact fun h0 => hm (Ideal.absNorm_eq_zero_iff.mp h0)
    exact_mod_cast h
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ ((|NumberField.discr F| : ℤ) : ℝ) * (Ideal.absNorm 𝔪 : ℝ) := by gcongr

theorem one_le_nrComplexPlaces_of_totallyComplex (hF : NumberField.IsTotallyComplex F) :
    1 ≤ NumberField.InfinitePlace.nrComplexPlaces F := by
  haveI := hF
  have hrank := NumberField.IsTotallyComplex.finrank F
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  omega

def heckeReciprocalCompletionFactor
    (𝔪 : Ideal (𝓞 F)) (s : ℂ) : ℂ :=
  (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) *
    ((Complex.Gammaℂ s)⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces F

end

section Helpers

section

variable (F : Type*) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F))

private lemma heckeConductorScale_cast_eq :
    (heckeConductorScale F 𝔪 : ℂ) =
      ((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm 𝔪 : ℂ) := by
  unfold heckeConductorScale
  rw [Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_natCast]

private lemma heckeConductorScale_ne_zero (hm : 𝔪 ≠ ⊥) : (heckeConductorScale F 𝔪 : ℂ) ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_heckeConductorScale F 𝔪 hm)))

end

private alias Gammaℂ_ne_zero_of_re_pos := CompletionFactor.Gammaℂ_ne_zero_of_re_pos

section

variable (F : Type*) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F))

private lemma heckeCompletionFactor_eq_scale (s : ℂ) :
    heckeCompletionFactor F 𝔪 s =
      (heckeConductorScale F 𝔪 : ℂ) ^ (s / 2) *
        Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F := by
  rw [heckeCompletionFactor, heckeConductorScale_cast_eq F 𝔪]

private lemma reciprocalCompletion_mul_completion (hm : 𝔪 ≠ ⊥) (s : ℂ) (hs : 0 < s.re) :
    heckeReciprocalCompletionFactor F 𝔪 s * heckeCompletionFactor F 𝔪 s = 1 := by
  rw [heckeReciprocalCompletionFactor, heckeCompletionFactor_eq_scale F 𝔪 s]
  have hpow : (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) *
      (heckeConductorScale F 𝔪 : ℂ) ^ (s / 2) = 1 := by
    rw [← Complex.cpow_add (-s / 2) (s / 2) (heckeConductorScale_ne_zero F 𝔪 hm),
      show -s / 2 + s / 2 = 0 by ring_nf, Complex.cpow_zero]
  have hgam : ((Complex.Gammaℂ s)⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces F *
      Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (Gammaℂ_ne_zero_of_re_pos hs), one_pow]
  calc (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) *
        ((Complex.Gammaℂ s)⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces F *
        ((heckeConductorScale F 𝔪 : ℂ) ^ (s / 2) *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F)
      = ((heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) *
          (heckeConductorScale F 𝔪 : ℂ) ^ (s / 2)) *
        (((Complex.Gammaℂ s)⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces F *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F) := by ring
    _ = 1 := by rw [hpow, hgam, mul_one]

end

private lemma inv_pow_mul_pow_sub_one (r : ℕ) (hr : 1 ≤ r) {g : ℂ} (hg : g ≠ 0) :
    (g⁻¹) ^ (r - 1) * g ^ r = g := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  simp only [Nat.succ_eq_add_one, add_tsub_cancel_right]
  rw [pow_succ, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hg, one_pow, one_mul]

private lemma gamma_shift_inv_mul {s : ℂ} (hs : 0 < s.re) :
    s * (((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s + 1))⁻¹ * Complex.Gammaℂ s = 1 := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hG := Gammaℂ_ne_zero_of_re_pos hs
  have hc : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    positivity
  have hrec : Complex.Gammaℂ (s + 1) = Complex.Gammaℂ s * s * (((2 * Real.pi : ℝ) : ℂ))⁻¹ := by
    rw [Complex.Gammaℂ_add_one hs0, div_eq_mul_inv, div_eq_mul_inv, Complex.ofReal_mul, mul_inv]
    norm_num
    ring
  rw [hrec, mul_inv, mul_inv, inv_inv]
  field_simp

private lemma principal_prefactor_mul (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥)
    (s : ℂ) (hs : 0 < s.re) :
    (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) * (((2 * Real.pi : ℝ) : ℂ))⁻¹ *
      (Complex.Gammaℂ (s + 1))⁻¹ *
      ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
      (s * heckeCompletionFactor F 𝔪 s) = 1 := by
  rw [heckeCompletionFactor_eq_scale F 𝔪 s]
  have hpow : (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) *
      (heckeConductorScale F 𝔪 : ℂ) ^ (s / 2) = 1 := by
    rw [← Complex.cpow_add (-s / 2) (s / 2) (heckeConductorScale_ne_zero F 𝔪 hm),
      show -s / 2 + s / 2 = 0 by ring_nf, Complex.cpow_zero]
  have hshift' : Complex.Gammaℂ s *
      ((((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s + 1))⁻¹ * s) = 1 := by
    calc _
        = s * (((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s + 1))⁻¹ *
            Complex.Gammaℂ s := by ac_rfl
      _ = 1 := (gamma_shift_inv_mul hs)
  calc _
      = ((heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) *
          (heckeConductorScale F 𝔪 : ℂ) ^ (s / 2)) *
        (((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F) *
        ((((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s + 1))⁻¹ * s) := by ac_rfl
    _ = 1 := by rw [hpow, (inv_pow_mul_pow_sub_one (NumberField.InfinitePlace.nrComplexPlaces F) (one_le_nrComplexPlaces_of_totallyComplex F hF) (Gammaℂ_ne_zero_of_re_pos hs)), one_mul, hshift']

end Helpers

theorem heckeReciprocalCompletionFactor_differentiable
    (F : Type*) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥) :
    Differentiable ℂ (heckeReciprocalCompletionFactor F 𝔪) := by
  unfold heckeReciprocalCompletionFactor
  refine Differentiable.mul ?_ ?_
  · exact ((differentiable_id).neg.div_const (2 : ℂ)).const_cpow (Or.inl (heckeConductorScale_ne_zero F 𝔪 hm))
  · exact Complex.differentiable_Gammaℂ_inv.pow _

def nonprincipalHeckeEntireContinuation
    (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F))
    (η : RayClassCharacter F 𝔪) (D : NonprincipalRayHeckeData F 𝔪 η)
    (s : ℂ) : ℂ :=
  heckeReciprocalCompletionFactor F 𝔪 s * D.Λ s

section

variable (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F) (𝔪 : Ideal (𝓞 F))
    (hm : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪) (D : NonprincipalRayHeckeData F 𝔪 η)

include hF hm in
theorem nonprincipalHeckeEntireContinuation_differentiable :
    Differentiable ℂ (nonprincipalHeckeEntireContinuation F 𝔪 η D) := by
  refine (heckeReciprocalCompletionFactor_differentiable F 𝔪 hm).mul D.Λ_entire

include hF hm in
theorem nonprincipalHeckeEntireContinuation_eq (s : ℂ) (hs : 0 < s.re) :
    nonprincipalHeckeEntireContinuation F 𝔪 η D s = D.L s := by
  rw [nonprincipalHeckeEntireContinuation, D.completed s hs, ← mul_assoc,
    reciprocalCompletion_mul_completion F 𝔪 hm s hs, one_mul]

end

def principalHeckeEntireRegularization
    (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F))
    (η : RayClassCharacter F 𝔪) (D : PrincipalRayHeckeData F 𝔪 η)
    (s : ℂ) : ℂ :=
  (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) *
    (((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s + 1))⁻¹ *
    ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) * D.E s

variable (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F) (𝔪 : Ideal (𝓞 F))
    (hm : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪) (D : PrincipalRayHeckeData F 𝔪 η)

include hF hm in
theorem principalHeckeEntireRegularization_differentiable :
    Differentiable ℂ (principalHeckeEntireRegularization F 𝔪 η D) := by
  unfold principalHeckeEntireRegularization
  exact ((((((differentiable_id).neg.div_const (2 : ℂ)).const_cpow (Or.inl (heckeConductorScale_ne_zero F 𝔪 hm))).mul (differentiable_const _)).mul (Complex.differentiable_Gammaℂ_inv.comp ((differentiable_id).add_const 1))).mul (Complex.differentiable_Gammaℂ_inv.pow _)).mul D.E_entire

include hF hm in
theorem principalHeckeEntireRegularization_eq (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    principalHeckeEntireRegularization F 𝔪 η D s = (s - 1) * D.L s := by
  rw [principalHeckeEntireRegularization, D.E_eq s hs, D.regularized s hs hs1]
  calc _
      = ((heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) * (((2 * Real.pi : ℝ) : ℂ))⁻¹ *
          (Complex.Gammaℂ (s + 1))⁻¹ *
          ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
          (s * heckeCompletionFactor F 𝔪 s)) * ((s - 1) * D.L s) := by ac_rfl
    _ = (s - 1) * D.L s := by rw [(principal_prefactor_mul F hF 𝔪 hm s hs), one_mul]

include hF hm in
theorem principalHeckeEntireRegularization_eq_bridge (s : ℂ) (hs : 0 < s.re) :
    principalHeckeEntireRegularization F 𝔪 η D s = D.R s := by
  rw [principalHeckeEntireRegularization, D.E_eq s hs]
  calc _
      = ((heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) * (((2 * Real.pi : ℝ) : ℂ))⁻¹ *
          (Complex.Gammaℂ (s + 1))⁻¹ *
          ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
          (s * heckeCompletionFactor F 𝔪 s)) * D.R s := by ac_rfl
    _ = D.R s := by rw [(principal_prefactor_mul F hF 𝔪 hm s hs), one_mul]

end
end DedekindZetaZeroFree
