module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Descent.Hybrid
public import OAI.NumberTheory.DirichletL.CubicSieve.Gcd

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section


def quotientSupport (D : Ideal ActualEisensteinCubic.O) (S : Finset (Ideal ActualEisensteinCubic.O))  :=
  (S.filter (fun I => D ∣ I)).image (idealQuotient D)

section
variable (D J : Ideal ActualEisensteinCubic.O) (hD : D ≠ 0) (R r h t : Ideal ActualEisensteinCubic.O) (hR : R ≠ 0) (S : Finset (Ideal ActualEisensteinCubic.O)) (N L : ℝ) (hS0 : ∀ I ∈ S, I ≠ 0)

include hD in
@[simp] theorem mem_quotientSupport    
      :
    J ∈ quotientSupport D S ↔ D * J ∈ S := by
  constructor
  · intro hJ
    obtain ⟨I, hI, he⟩ := Finset.mem_image.mp hJ
    obtain ⟨hIS, hDI⟩ := Finset.mem_filter.mp hI
    rw [← he, idealQuotient_mul hDI]
    exact hIS
  · intro hJ
    refine Finset.mem_image.mpr ⟨D * J, Finset.mem_filter.mpr ⟨hJ, dvd_mul_right _ _⟩, ?_⟩
    exact mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right D J))

theorem sum_quotientSupport {A : Type*} [AddCommMonoid A]
    (D : Ideal ActualEisensteinCubic.O) (S : Finset (Ideal ActualEisensteinCubic.O)) (f : Ideal ActualEisensteinCubic.O → A) :
    (∑ I ∈ S with D ∣ I, f I) = ∑ J ∈ quotientSupport D S, f (D * J) := by
  rw [quotientSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    rw [idealQuotient_mul (Finset.mem_filter.mp hI).2]
  · intro I hI J hJ he
    exact idealQuotient_injective_on D (Finset.mem_filter.mp hI).2
      (Finset.mem_filter.mp hJ).2 he

include hD in
theorem quotientSupport_nonzero    
      (hS : ∀ I ∈ S, I ≠ 0)
     J  (hJ : J ∈ quotientSupport D S) : J ≠ 0 := by
  have h := hS (D * J) ((mem_quotientSupport D J hD S).mp hJ)
  exact (mul_ne_zero_iff.mp h).2

include hD in
theorem quotientSupport_quadratic_admissible    
      (hS : ∀ I ∈ S, CanonicalQuadraticSieve.Admissible I)
     J  (hJ : J ∈ quotientSupport D S) :
    CanonicalQuadraticSieve.Admissible J :=
  admissible_of_dvd (hS (D * J) ((mem_quotientSupport D J hD S).mp hJ))
    (dvd_mul_left _ _)

include hD in
theorem quotientSupport_cubic_admissible    
      (hS : ∀ I ∈ S, CubicSieve.Admissible I)
     J  (hJ : J ∈ quotientSupport D S) :
    CubicSieve.Admissible J :=
  CubicSieve.cubic_admissible_of_dvd
    (hS (D * J) ((mem_quotientSupport D J hD S).mp hJ)) (dvd_mul_left _ _)

include hD hS0 in
theorem quotientSupport_norm_le    
       
      (hS : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ N)
    (J : Ideal ActualEisensteinCubic.O) (hJ : J ∈ quotientSupport D S) :
    (Ideal.absNorm J : ℝ) ≤ N := by
  have hDJ := (mem_quotientSupport D J hD S).mp hJ
  have hn : Ideal.absNorm J ≤ Ideal.absNorm (D * J) := by
    apply Nat.le_of_dvd
    · exact Nat.pos_of_ne_zero (fun hz => hS0 _ hDJ (Ideal.absNorm_eq_zero_iff.mp hz))
    · exact map_dvd Ideal.absNorm (dvd_mul_left J D)
  exact (Nat.cast_le.mpr hn).trans (hS _ hDJ)

include hD hS0 in
theorem quotientSupport_shell    
       
     
    (hS : ∀ I ∈ S, L ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ 2 * L)
    (J : Ideal ActualEisensteinCubic.O) (hJ : J ∈ quotientSupport D S) :
    max 1 (L / (Ideal.absNorm D : ℝ)) ≤ (Ideal.absNorm J : ℝ) ∧
      (Ideal.absNorm J : ℝ) ≤ 2 * max 1 (L / (Ideal.absNorm D : ℝ)) := by
  have hDJ := (mem_quotientSupport D J hD S).mp hJ
  have hnD : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hD (Ideal.absNorm_eq_zero_iff.mp hz))
  have hJ0 := quotientSupport_nonzero D hD S hS0 J hJ
  have hnJ : 1 ≤ (Ideal.absNorm J : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hJ0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs := hS (D * J) hDJ
  simp only [map_mul, Nat.cast_mul] at hs
  constructor
  · refine max_le hnJ ((div_le_iff₀ hnD).mpr ?_)
    simpa only [mul_comm] using hs.1
  · have hj : (Ideal.absNorm J : ℝ) ≤ 2 * (L / (Ideal.absNorm D : ℝ)) := by
      have hj := (le_div_iff₀ hnD).mpr (show
          (Ideal.absNorm J : ℝ) * (Ideal.absNorm D : ℝ) ≤ 2 * L by
        simpa only [mul_comm] using hs.2)
      simpa only [mul_div_assoc] using hj
    exact hj.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))

include hR hS0 in
theorem quotient_hybridCubicCoefficient_energy
           
     
    (hS : ∀ I ∈ S, L ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ 2 * L)
     a  (ha : ∀ I ∈ S, ‖a I‖ ≤ 1) :
    (∑ P ∈ quotientSupport R S, ‖hybridCubicCoefficient R r h t a P‖ ^ 2) ≤ 256 := by
  apply hybridCubicCoefficient_energy R r h t (quotientSupport R S)
    (max 1 (L / (Ideal.absNorm R : ℝ))) (le_max_left _ _)
  · exact quotientSupport_shell R hR S L hS0 hS
  simp_all

end

end
end SevenEighths.InverseMoment

end OAI
