module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Continuation
public import Mathlib.NumberTheory.LSeries.AbstractFuncEq

@[expose] public section

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace SevenEighths.HeckeMellinIdentity

def regularized (P : WeakFEPair ℂ) (s : ℂ)  :=
  s * (s - 1) * P.Λ₀ s - (s - 1) * P.f₀ + s * P.ε * P.g₀

section
variable (P : WeakFEPair ℂ) (hk : P.k = 1) (Q : WeakFEPair ℂ) (hP : P.k = 1) (hQ : Q.k = 1) (A : ℝ) (hA : 0 < A) (hright : ∀ s : ℂ, 1 < s.re → P.Λ s = (A : ℂ)^(-s) * Q.Λ s) (hf : ∀ t : ℝ, 0 < t → P.f t = Q.f t) (hf₀ : P.f₀ = Q.f₀) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1)

theorem regularized_entire   : Differentiable ℂ (regularized P) := by
  unfold regularized
  have hd := P.differentiable_Λ₀
  fun_prop

include hk h0 h1 in
theorem regularized_eq      
        : regularized P s = s * (s-1) * P.Λ s := by
  unfold regularized WeakFEPair.Λ
  rw [hk]
  simp only [smul_eq_mul, Complex.ofReal_one]
  field_simp <;> ring

include hP hQ hA hright h0 h1 in
theorem scaled_eq      
       
     
          :
    P.Λ s = (A : ℂ)^(-s) * Q.Λ s := by
  have hd : Differentiable ℂ (fun z : ℂ => (A : ℂ)^(-z) * regularized Q z) :=
    ((differentiable_id.neg).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))).mul (regularized_entire Q)
  have he : regularized P = fun z : ℂ => (A : ℂ)^(-z) * regularized Q z := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr (regularized_entire P)).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hd) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hz1 : z ≠ 1 := by intro h; norm_num [h] at hz
    grind [regularized_eq]
  have heq := congr_fun he s
  grind [regularized_eq]

include hP hQ hf hf₀ h0 h1 in
theorem eq_of_f      
       
          : P.Λ s = Q.Λ s := by
  have h := scaled_eq P Q hP hQ 1 zero_lt_one (fun z hz => by
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
    rw [← (P.hasMellin (by rwa [hP])).2, ← (Q.hasMellin (by rwa [hQ])).2]
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [hf t ht, hf₀]) h0 h1
  simpa only [Complex.ofReal_one, Complex.one_cpow, one_mul] using h

end

end SevenEighths.HeckeMellinIdentity

end

end OAI
