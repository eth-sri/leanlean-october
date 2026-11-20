module
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxCover
import Mathlib

/-! # A compact classical test of box capacity

Subtract the same translates of a second, wider profile. Since both scales agree
with the same homogeneous field at infinity, the resulting test is compact, with
controlled size and controlled generator loss at the outer scale.
-/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxBarrier
open Finset Set

private lemma compact_sum {ι : Type*} (S : Finset ι) (g : ι → Z → ℝ) (hg : ∀ i, HasCompactSupport (g i)) : HasCompactSupport (∑ i ∈ S, g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [sum_empty] using (HasCompactSupport.zero : HasCompactSupport (0 : Z → ℝ))
  | insert i S h ih => rw [sum_insert h]; exact (hg i).add ih

private theorem coord_box {A r Y : ℝ} (hr : 0 < r) (q : Z) : coord r Y q ∈ box A 1 0 ↔ q ∈ box A r Y := by
  simp only [coord, box, mem_ofPred_eq, sub_zero, one_pow, mul_one, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hr 3)),
    abs_of_pos (inv_pos.mpr hr), inv_pow, inv_mul_le_iff₀ (pow_pos hr 3), inv_mul_le_iff₀ hr]
  rw [mul_comm r, mul_comm (r^3)]

variable {lam Lam α : ℝ} (B : Exterior lam Lam α)

include B in
theorem compact_test (hα : 0 < α) (ha : α < 1) (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ r > (0:ℝ), ∀ Y s : ℝ, 1 ≤ s → ∃ f : Z → ℝ, C2 f ∧ HasCompactSupport f ∧
      (∀ q, |f q| ≤ 2*C*r^2*s^α) ∧ ∀ b ∈ Icc lam Lam, ∀ q,
      (box A r Y).indicator (fun _ => (1:ℝ)) q ≤ P b f q + C*s^(α-2) := by
  classical
  obtain ⟨N,hN⟩ := cover B hα ha A
  have c0 := B.cost_nonneg
  refine ⟨N*B.cost,by positivity,fun r hr Y s hs => ?_⟩
  have hs0 := zero_lt_one.trans_le hs
  let g := B.profile 1 - B.profile s
  have hg : C2 g := (B.regular 1 one_pos).sub (B.regular s hs0)
  have gc : HasCompactSupport g := by
    have H := (B.compact 1 one_pos).sub (B.compact s hs0)
    rwa [sub_sub_sub_cancel_right] at H
  have gb q : |g q| ≤ 2*B.cost*s^α := by
    change |B.profile 1 q - B.profile s q| ≤ _
    have h := (abs_sub_le (B.profile 1 q) (B.large q) (B.profile s q)).trans (add_le_add (B.size 1 one_pos q) (by simpa only [abs_sub_comm (B.large q) (B.profile s q)] using B.size s hs0 q : |B.large q-B.profile s q| ≤ B.cost*s^α))
    simp only [Real.one_rpow,mul_one] at h
    linarith only [h, le_mul_of_one_le_right c0 (Real.one_le_rpow hs hα.le)]
  let u (i : ℕ) := resize 1 1 (5*i) g
  let F := ∑ i ∈ range N, u i
  have e (q : Z) (i : ℕ) : coord 1 (5*i) q = shifted i q := by simp [coord,shifted]
  have us i : C2 (u i) := smooth_resize hg ..
  have fc : HasCompactSupport F := compact_sum (range N) u fun i => compact_resize gc 1 1 (5*i) one_pos
  refine ⟨resize (r^2) r Y F, smooth_resize (smooth_sum (range N) u us) _ _ _, compact_resize fc _ _ _ hr, ?_, ?_⟩
  · intro q; let z := coord r Y q
    have h := (abs_sum_le_sum_abs (fun i => u i z) (range N)).trans (sum_le_sum fun i _ => (by simpa [u,resize,e] using gb (shifted i z) : |u i z| ≤ 2*B.cost*s^α))
    simp only [sum_const,card_range,nsmul_eq_mul] at h
    simpa only [resize,F,Finset.sum_apply,abs_mul,abs_of_nonneg (sq_nonneg r),mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left h (sq_nonneg r)
  · intro b hb q; let z := coord r Y q
    have Pui i : P b (u i) z = P b (B.profile 1) (shifted i z) - P b (B.profile s) (shifted i z) := by
      rw [show u i = resize 1 1 (5*i) g from rfl,P_resize _ _ _ _ _ one_pos, e, show (1:ℝ)/1^2 = 1 by norm_num, one_mul, P_sub (B.regular 1 one_pos) (B.regular s hs0)]
    have upper := sum_le_sum (s := range N) fun i _ => (le_abs_self _).trans (B.bound s hs0 b hb (shifted i z))
    simp only [sum_const,card_range,nsmul_eq_mul] at upper
    have ind : (box A r Y).indicator (fun _ => (1:ℝ)) q = (box A 1 0).indicator (fun _ => (1:ℝ)) z := by simp [Set.indicator,z,coord_box hr]
    rw [ind,P_resize _ _ _ _ _ hr,div_self (pow_ne_zero _ hr.ne'),one_mul]
    change _ ≤ P b (∑ i ∈ range N, u i) z + _
    rw [P_sum _ _ us]
    simp_rw [Pui]
    rw [sum_sub_distrib]
    linarith only [hN b hb z,upper]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxBarrier
