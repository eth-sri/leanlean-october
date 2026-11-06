module
public import GuthMaynard.AffineSource.LargeValuesAffineHeight
public import GuthMaynard.Improvement.CompactNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap FourierTransform Convolution ContDiff
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- The verified height-family endpoint extended to all T>=2 using its actual
finite affine baseline on the bounded initial height interval. -/
theorem sparse_affine_all_heights (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (f : 𝓢(ℝ, ℝ)) (M : ℕ),
      2 ≤ T → (∀ x, 0 ≤ f x) → GMAffineSupportedOn (1/4:ℝ) (9/4) f →
      GMAffineHeightFourierMassFamilyAtDepth T D 0 f → 0 < M → (M:ℝ) ≤ T^4 →
      gmAffineJ f M ≤ C*T^ε*((M:ℝ)^6*(∫ x, f x)^2+(M:ℝ)^4*(∫ x, f x^2)) := by
  obtain ⟨C,T₀,hC,hT₀,h⟩ := gmAffine_proposition9_1_height_family_native D hD hε
  refine ⟨C+36992*T₀^8,by positivity,?_⟩
  intro T f M hT hf hs hp hM hMT
  have hL2 : 0 ≤ ∫ x, f x^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hW : 0 ≤ (M:ℝ)^6*(∫ x, f x)^2+(M:ℝ)^4*(∫ x, f x^2) := by positivity
  have hTp : 0 < T := by linarith
  have hTe : 1 ≤ T^ε := Real.one_le_rpow (by linarith) hε.le
  by_cases hlarge : T₀ ≤ T
  · exact (h hlarge f hf hs hp hM hMT).trans (by gcongr; exact le_add_of_nonneg_right (by positivity))
  · have hsmall : T ≤ T₀ := le_of_lt (lt_of_not_ge hlarge)
    have hf2 : Integrable (fun x => f x^2) :=
      (memLp_two_iff_integrable_sq f.continuous.aestronglyMeasurable).1 (f.memLp 2)
    have hm2 : (M:ℝ)^2 ≤ T₀^8 := by
      calc
        _ ≤ (T₀^4)^2 := by gcongr; exact hMT.trans (by gcongr)
        _ = _ := by ring
    calc
      _ ≤ 36992*(M:ℝ)^6*(∫ x, f x^2) := gmAffineJ_le_crude hf2 hM
      _ = (36992*(M:ℝ)^2)*((M:ℝ)^4*(∫ x, f x^2)) := by ring
      _ ≤ (36992*T₀^8)*((M:ℝ)^4*(∫ x, f x^2)) := by gcongr
      _ ≤ (36992*T₀^8)*((M:ℝ)^6*(∫ x, f x)^2+(M:ℝ)^4*(∫ x, f x^2)) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
      _ ≤ (C+36992*T₀^8)*T^ε*((M:ℝ)^6*(∫ x, f x)^2+(M:ℝ)^4*(∫ x, f x^2)) := by
        apply mul_le_mul_of_nonneg_right _ hW
        have hbase : 0 ≤ 36992*T₀^8 := by positivity
        nlinarith

