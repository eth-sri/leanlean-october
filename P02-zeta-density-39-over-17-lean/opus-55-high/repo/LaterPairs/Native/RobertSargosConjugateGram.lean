module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.SargosSymmetricAveraging
public import LaterPairs.Native.TriangularShiftBounds
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                 

noncomputable section
open scoped BigOperators InnerProductSpace
namespace TaoTrudgianYang2025

def robertSargosCenteredCorrelation (a : ℤ → ℂ) (M : ℕ) (h : ℤ) : ℝ :=
  ∑ m ∈ Finset.Ico (0:ℤ) M,
    ⟪sargosPaddedSequence a M (m+h),sargosPaddedSequence a M (m-h)⟫_ℝ

section
variable (a : ℤ → ℂ)
include a
theorem robertSargos_centered_correlation_neg (M : ℕ) (h : ℤ) :
    robertSargosCenteredCorrelation a M (-h) = robertSargosCenteredCorrelation a M h := by
  unfold robertSargosCenteredCorrelation
  simp only [sub_neg_eq_add,← sub_eq_add_neg]
  apply Finset.sum_congr rfl
  intro m _
  exact real_inner_comm _ _

theorem robertSargos_centered_correlation_zero (M : ℕ) :
    robertSargosCenteredCorrelation a M 0 =
      ∑ m ∈ Finset.Ico (0:ℤ) M, ‖a m‖^2 := by
  unfold robertSargosCenteredCorrelation
  pm_335 add_zero sub_zero real_inner_self_eq_norm_sq
  intro m hm
  rw [sargosPaddedSequence_eq a M hm]

theorem robertSargos_even_gram_term (M H s t : ℕ)
    (hs : s < H) (ht : t < H) :
    (∑ n ∈ Finset.Ico (-(2*(H:ℤ))) M,
      ⟪sargosPaddedSequence a M (n+2*s),sargosPaddedSequence a M (n+2*t)⟫_ℝ) =
      robertSargosCenteredCorrelation a M ((s:ℤ)-t) := by
  classical
  let B := Finset.Ico (-(2*(H:ℤ))) (M:ℤ)
  let P : ℤ → Prop := fun n => n+(s:ℤ)+t ∈ Finset.Ico (0:ℤ) M
  let F : ℤ → ℝ := fun n =>
    ⟪sargosPaddedSequence a M (n+2*s),sargosPaddedSequence a M (n+2*t)⟫_ℝ
  have hfilt : (∑ n ∈ B.filter P, F n) = ∑ n ∈ B, F n := by
    apply Finset.sum_filter_of_ne
    intro n _ hn
    have hsupp : n+2*s ∈ Finset.Ico (0:ℤ) M ∧
        n+2*t ∈ Finset.Ico (0:ℤ) M := by
      constructor
      · by_contra hn'
        simp only [F,sargosPaddedSequence,ite_eq_right hn',inner_zero_left] at hn
        grind
      pm_7921 hn' sargosPaddedSequence
    change n+(s:ℤ)+t ∈ Finset.Ico (0:ℤ) M
    pm_5911 Finset.mem_Ico hsupp
  pm_7666 n
  unfold robertSargosCenteredCorrelation
  apply Finset.sum_bij (fun n _ => n+(s:ℤ)+t)
  · intro n hn
    exact (Finset.mem_filter.mp hn).2
  · intro n _ k _ he
    omega
  · intro m hm
    have hm' := Finset.mem_Ico.mp hm
    refine ⟨m-(s:ℤ)-t,?_,?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · dsimp only [B]
        apply Finset.mem_Ico.mpr
        constructor <;> omega
      · dsimp only [P]
        have he : m-(s:ℤ)-t+s+t = m := by omega
        simpa only [he] using hm
    · omega
  grind

theorem robertSargos_even_gram (M H : ℕ) :
    (∑ n ∈ Finset.Ico (-(2*(H:ℤ))) M,
      ‖∑ s ∈ Finset.range H, sargosPaddedSequence a M (n+2*s)‖^2) =
      ∑ h ∈ Finset.Ioo (-(H:ℤ)) H,
        ((H-h.natAbs:ℕ):ℝ)*robertSargosCenteredCorrelation a M h := by
  calc
    _ = ∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        ∑ n ∈ Finset.Ico (-(2*(H:ℤ))) M,
          ⟪sargosPaddedSequence a M (n+2*s),sargosPaddedSequence a M (n+2*t)⟫_ℝ := by
      pm_1655
      intro n _
      exact real_inner_comm _ _
    _ = ∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        robertSargosCenteredCorrelation a M ((s:ℤ)-t) := by
      pm_90 Finset.sum_congr s hs t ht
      exact robertSargos_even_gram_term a M H s t
        (Finset.mem_range.mp hs) (Finset.mem_range.mp ht)
    _ = _ := sum_signed_shift_differences H (robertSargosCenteredCorrelation a M)
end

end TaoTrudgianYang2025
