module
public import CenteredShortReflection
public import RationalDilatedDifference
import WeylPort.Analytic.RealLaplace

public section

open Finset MeasureTheory
namespace Montgomery.RationalMoment

section
variable {K : ℕ} (hK : 1 ≤ K) {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B)
include K hK η B hη hB
theorem reflection_complete_pair_dilated_short_range :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ : ℝ), 1 < T → ∀ M : ℕ, 0 < M → ∀ U : ℝ, 0 ≤ U → (M:ℝ) ≤ B*U →
      ∀ W : Finset ℝ,
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → U^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.completePairEnergy M W ≤ C*T^η*U*(W.card : ℝ)^2 := by
  pm_114 C hC hbound dilated_dyadic_dirichlet_difference hK hη hB
  refine ⟨C,hC,?_⟩
  intro T t₀ hT M hM U hU hMU W hR hUR hW hsep
  pm_2704
  have hh := hbound T t₀ ((M:ℝ)-1/2) U hT hm hU (by linarith) (Ico M (2*M)) hA W hR hUR
    hW hsep (fun _ => 1) (by simp)
  pm_2705
  exact hh

/-- Fixed dilations in the reflected band are absorbed in the constant,
not imposed on the cardinality threshold. -/
theorem reflection_local_energy_dilated_short_range :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L H : ℝ, 1 < T → 0 < L → 0 < H →
      ∀ W : Finset ℝ,
      T^(((K:ℝ)+1)/(2*K+1)) ≤ W.card → (H/(B*L))^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.localReflectionEnergy L H W ≤
        C*T^η*(H/L)*(W.card:ℝ)^2 := by
  pm_5975 reflection_complete_pair_dilated_short_range
  have hBp : 0 < B := by linarith
  refine ⟨30*C,by positivity,?_⟩
  intro T t₀ L H hT hL hH W hR hlen hW hsep
  let U : ℝ := H/(B*L)
  pm_61 hU U
  have hUL : U ≤ H/L := by
    dsimp [U]
    exact div_le_div_of_nonneg_left hH.le hL (by nlinarith)
  open MathCollab.Density in
  have hb (M : ℕ) (hM : M ∈ reflectionBlocks L H) :
      (∑' j : ℤ, completePairEnergy M (localSet W H j)) ≤
        3*(C*T^η*(H/L)*(W.card:ℝ)^2) := by
    pm_5763 hL
    have hMU : (M:ℝ) ≤ (2*B)*U := by
      have hpi : 4*H/(Real.pi*L) ≤ 2*H/L := by
        pm_5963 hL
      have he : (2*B)*U=2*H/L := by dsimp [U]; field_simp
      rw [he]
      exact hMhi.trans hpi
    refine (reflection_local_pair_le_three hH M W).trans ?_
    pm_6930
    exact (hbound T t₀ hT M hM0 U hU hMU W hR hlen hW hsep).trans (by gcongr)
  open MathCollab.Density in
  calc
    localReflectionEnergy L H W ≤ ∑ _M ∈ reflectionBlocks L H,
        3*(C*T^η*(H/L)*(W.card:ℝ)^2) := sum_le_sum hb
    _ = ((reflectionBlocks L H).card:ℝ)*(3*(C*T^η*(H/L)*(W.card:ℝ)^2)) := by simp
    _ ≤ 10*(3*(C*T^η*(H/L)*(W.card:ℝ)^2)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast reflectionBlocks_card_le hL hH
    _ = _ := by ring
end

theorem centered_shell_dilated_short_range (w : MathCollab.Density.ReflectionCutoff)
    {K A : ℕ} (hK : 1 ≤ K) (hA : 1 < A) {η D : ℝ} (hη : 0 < η) (hD : 1 ≤ D) :
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ T t₀ L H : ℝ,
      1 < T → 0 < L → 0 < H → ∀ W : Finset ℝ,
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card →
      (H/(D*L))^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.shellEnergy w L H W ≤
        C*T^η*L*(W.card : ℝ)^2 + B*(W.card : ℝ)^2*L^(2-2*(A:ℝ)) := by
  pm_114 C hC hbound reflection_local_energy_dilated_short_range hK hη hD
  pm_2706
  refine ⟨1+F*C,4*B^2,by positivity,by positivity,?_⟩
  intro T t₀ L H hT hL hH W hR hlen hW hsep
  have he := (href L H W hL hH).1
  have hb := hbound T t₀ L H hT hL hH W hR hlen hW hsep
  have hm : F*(L^2/H)*MathCollab.Density.localReflectionEnergy L H W ≤
      (F*C)*T^η*L*(W.card : ℝ)^2 := by
    calc
      _ ≤ F*(L^2/H)*(C*T^η*(H/L)*(W.card : ℝ)^2) := by gcongr
      _ = _ := by field_simp
  exact he.trans (add_le_add (hm.trans (by gcongr; linarith)) le_rfl)


end Montgomery.RationalMoment
