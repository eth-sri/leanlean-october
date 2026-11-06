module
public import GuthMaynard.Improvement.AmplifierArithmetic
import WeylPort.Analytic.RealLaplace

@[expose] public section
noncomputable section
open Finset
namespace GuthMaynard.Improvement

def amplifierFiber (N L : ℝ) (m : ℤ) : Finset (ℕ × ℕ) :=
  ((amplifierColumns N L) ×ˢ (amplifierSource N)).filter
    (fun p => ((p.1*p.2:ℕ):ℤ)=m)

theorem amplifier_action_fiber (N L : ℝ) (a z : ℕ → ℂ) (m : ℤ) :
    (∑ q ∈ amplifierColumns N L, amplifierMatrix N a m q*z q) =
      ∑ p ∈ amplifierFiber N L m, a p.2*z p.1 := by
  classical
  pm_94 amplifierMatrix amplifierFiber sum_filter sum_product sum_mul
  pm_156 sum_congr q n
  grind

/-- Row Cauchy--Schwarz retains the actual product multiplicity. -/
theorem amplifier_fiber_norm {N L : ℝ} (a z : ℕ → ℂ)
    (ha : ∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) (m : ℤ) :
    ‖∑ p ∈ amplifierFiber N L m, a p.2*z p.1‖^2 ≤
      ((amplifierFiber N L m).card:ℝ)*
        ∑ p ∈ amplifierFiber N L m, ‖z p.1‖^2 := by
  have hn : ‖∑ p ∈ amplifierFiber N L m, a p.2*z p.1‖ ≤
      ∑ p ∈ amplifierFiber N L m, ‖z p.1‖ := by
    pm_244 sum_le_sum p hp
    have hpn := (mem_product.mp (mem_filter.mp hp).1).2
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha p.2 hpn) (norm_nonneg _)
  calc
    _ ≤ (∑ p ∈ amplifierFiber N L m, ‖z p.1‖)^2 :=
      (sq_le_sq₀ (norm_nonneg _) (sum_nonneg (fun _ _ => norm_nonneg _))).mpr hn
    _ ≤ _ := by
      simpa using sum_mul_sq_le_sq_mul_sq (amplifierFiber N L m)
        (fun _ => (1:ℝ)) (fun p => ‖z p.1‖)

section
variable {η : ℝ} (hη : 0 < η)
include η hη
/-- Actual integer product fibers obey a divisor bound chosen before all
lengths, rows and coefficient vectors. No upper bound on L is imposed. -/
theorem amplifier_fiber_subpower :
    ∃ C : ℝ, 0 < C ∧ ∀ N L : ℝ, 0 < N → N ≤ L → ∀ m : ℤ,
      ((amplifierFiber N L m).card:ℝ) ≤ C*(1+L)^η := by
  obtain ⟨C,hC,hd⟩ := MathCollab.Density.divisor_card_subpower hη
  refine ⟨C*4^η,by positivity,?_⟩
  intro N L hN hNL m
  have hL : 0 < L := hN.trans_le hNL
  by_cases hp : (amplifierFiber N L m).Nonempty
  · obtain ⟨p,hp⟩ := hp
    obtain ⟨hpair,hprod⟩ := mem_filter.mp hp
    obtain ⟨hq,hn⟩ := mem_product.mp hpair
    have hq0 := (amplifier_column_bounds hN hNL hq).1
    have hn0 : 0 < p.2 := by
      exact_mod_cast (hN.trans (amplifier_source_bounds hN hn).1)
    have hm0 : 0 < m := by rw [← hprod]; exact_mod_cast Nat.mul_pos hq0 hn0
    have hcard : (amplifierFiber N L m).card ≤ m.natAbs.divisors.card := by
      apply product_fiber_card_le_divisors _ (by omega)
      intro r hr
      have he := (mem_filter.mp hr).2
      have hh := congrArg Int.natAbs he
      simpa only [Int.natCast_mul,Int.natAbs_mul,Int.natAbs_natCast] using hh
    have hsize : (m.natAbs:ℝ) ≤ 4*L := by
      have hb := (amplifier_product_plateau hN hNL hq hn).2
      have he : (m.natAbs:ℝ)=((p.1*p.2:ℕ):ℝ) := by
        rw [← hprod]
        simp
      rw [he]
      exact (div_le_iff₀ hL).mp hb
    calc
      _ ≤ (m.natAbs.divisors.card:ℝ) := by exact_mod_cast hcard
      _ ≤ C*(m.natAbs:ℝ)^η := hd m.natAbs (by omega)
      _ ≤ C*(4*(1+L))^η := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith) hη.le) (by linarith)
      _ = (C*4^η)*(1+L)^η := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
  pm_257 hp card_empty

/-- Raw finite matrix estimate. The divisor loss depends on L, with the
source count bounded by N+1; no coefficient or source-height premise is hidden. -/
theorem amplifier_matrix_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ N L : ℝ, 0 < N → N ≤ L →
      ∀ (a z : ℕ → ℂ) (M : Finset ℤ),
      (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      (∑ m ∈ M, ‖∑ q ∈ amplifierColumns N L, amplifierMatrix N a m q*z q‖^2) ≤
        C*(1+L)^η*(N+1)*(∑ q ∈ amplifierColumns N L, ‖z q‖^2) := by
  pm_102 C hC hcard amplifier_fiber_subpower hη
  intro N L hN hNL a z M ha
  have hL : 0 < L := hN.trans_le hNL
  have hD : 0 ≤ C*(1+L)^η := by positivity
  have hsum : (∑ m ∈ M, ∑ p ∈ amplifierFiber N L m, ‖z p.1‖^2) ≤
      ((amplifierSource N).card:ℝ)*(∑ q ∈ amplifierColumns N L, ‖z q‖^2) := by
    calc
      _ ≤ ∑ p ∈ (amplifierColumns N L) ×ˢ (amplifierSource N), ‖z p.1‖^2 :=
        sum_fiberwise_le_sum_of_sum_fiber_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))
      _ = _ := by
        simp only [sum_product,sum_const,nsmul_eq_mul]
        rw [← mul_sum]
  calc
    _ ≤ ∑ m ∈ M, C*(1+L)^η*(∑ p ∈ amplifierFiber N L m, ‖z p.1‖^2) := by
      apply sum_le_sum
      intro m hm
      rw [amplifier_action_fiber]
      exact (amplifier_fiber_norm a z ha m).trans
        (mul_le_mul_of_nonneg_right (hcard N L hN hNL m) (sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = C*(1+L)^η*(∑ m ∈ M, ∑ p ∈ amplifierFiber N L m, ‖z p.1‖^2) := by rw [mul_sum]
    _ ≤ C*(1+L)^η*(((amplifierSource N).card:ℝ)*(∑ q ∈ amplifierColumns N L, ‖z q‖^2)) :=
      mul_le_mul_of_nonneg_left hsum hD
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (amplifier_source_card hN.le) hD)
        (sum_nonneg (fun _ _ => sq_nonneg _))
end

end GuthMaynard.Improvement
