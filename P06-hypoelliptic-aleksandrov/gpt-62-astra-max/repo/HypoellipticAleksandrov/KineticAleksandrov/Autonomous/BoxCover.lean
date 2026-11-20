module
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxExterior
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationGeometry
import Mathlib

/-! # A finite cover by translated barriers

In a sum over equally spaced position translates, at most one summand is evaluated
in its flattened core. Over `k³ + 1` translates the nearby gauges are `O(k)`, so
the other `k³` summands contribute at least `k³ c/(Kk)²`. This absorbs the loss
on the core. No limiting singular test, or assumption about its pole mass, is needed.
-/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxBarrier
open Set Finset

def shifted (i : ℕ) (q : Z) : Z := (q.1-5*i,q.2)
private def bad (i : ℕ) (q : Z) := |(shifted i q).1| ≤ 2 ∧ |q.2| ≤ 2

private theorem separated {i j : ℕ} {q : Z} (hi : bad i q) (hj : bad j q) : i = j := by
  obtain ⟨I,J⟩ := abs_le.mp hi.1
  obtain ⟨U,V⟩ := abs_le.mp hj.1
  unfold shifted at I J U V; dsimp only at I J U V
  rcases lt_trichotomy i j with l|e|l
  · have h : (i:ℝ)+1 ≤ j := by exact_mod_cast l
    linarith
  · exact e
  · have h : (j:ℝ)+1 ≤ i := by exact_mod_cast l
    linarith

variable {lam Lam α : ℝ} (B : Exterior lam Lam α)

private lemma outside_good {i : ℕ} {q : Z} (h : ¬ bad i q) {b : ℝ} (hb : b ∈ Icc lam Lam) :
    B.pos * bellmanGauge (shifted i q) ^ (α-2) ≤ P b (B.profile 1) (shifted i q) := by
  apply B.good 1 one_pos _ hb; simpa [bad,shifted] using h

/-- Freeze the coefficient at a single point; the number of translates is independent
of that point and of the coefficient. -/
theorem cover (hα : 0 < α) (ha : α < 1) (A : ℝ) : ∃ N : ℕ,
    ∀ b ∈ Icc lam Lam, ∀ q, (box A 1 0).indicator (fun _ => (1:ℝ)) q ≤
      ∑ i ∈ range N, P b (B.profile 1) (shifted i q) := by
  classical
  let D := max 2 A
  have d : 2 ≤ D := le_max_left ..
  have dA : A ≤ D := le_max_right ..
  let K := max 1 (((D+5)^2+(D+5)^6)^(1/6:ℝ))
  have hK : 1 ≤ K := le_max_left ..
  obtain ⟨k,hk⟩ := exists_nat_gt (max 1 ((1+B.cost)*K^2/B.pos))
  have hk1 : 1 ≤ (k:ℝ) := (le_max_left ..).trans hk.le
  have hk0 : 0 < (k:ℝ) := by linarith
  have hK0 : 0 < K := by linarith
  have hlarge := (div_lt_iff₀ B.positive).1 ((le_max_right ..).trans_lt hk)
  let S := range (k^3+1)
  refine ⟨k^3+1, fun b hb q => ?_⟩
  let L i := P b (B.profile 1) (shifted i q)
  change _ ≤ ∑ i ∈ S, L i
  have H i (hi : i ∈ S) : (i:ℝ) ≤ (k:ℝ)^3 := by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hi)
  have Z0 : 0 ∈ S := by simp [S]
  by_cases near : ∃ j ∈ S, |(shifted j q).1| ≤ D ∧ |q.2| ≤ D
  · obtain ⟨j,hj,hx,hv⟩ := near
    have upper i (hi : i ∈ S) : bellmanGauge (shifted i q) ≤ K*k := by
      have hi' := H i hi; have hj' := H j hj
      have hbox : shifted i q ∈ box (D+5) k 0 := by
        constructor
        · change |q.1-5*i-0| ≤ _; rw [sub_zero,abs_le]; change |q.1-5*j| ≤ D at hx
          have hh := le_mul_of_one_le_right (by linarith : 0 ≤ D) (one_le_pow₀ hk1 (n := 3)); obtain ⟨a,b⟩ := abs_le.mp hx
          constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i, Nat.cast_nonneg (α := ℝ) j]
        · exact hv.trans ((by linarith : D ≤ D+5).trans (le_mul_of_one_le_right (by linarith) hk1))
      have hh := box_rho_le (by linarith : 0 < D+5) hk0 hbox
      simpa only [sub_zero] using hh.trans (mul_le_mul_of_nonneg_right (le_max_right 1 _) hk0.le)
    obtain ⟨l,hl,ho⟩ : ∃ l ∈ S, ∀ i ∈ S, i ≠ l → ¬ bad i q := by
      by_cases e : ∃ l ∈ S, bad l q
      · obtain ⟨l,hl,h⟩ := e; exact ⟨l,hl,fun _ _ ne bi => ne (separated bi h)⟩
      · exact ⟨0,Z0,fun i hi _ h => e ⟨i,hi,h⟩⟩
    have low i (hi : i ∈ S.erase l) : B.pos/(K*k)^2 ≤ L i := by
      obtain ⟨ne,mem⟩ := mem_erase.mp hi
      have g := ho i mem ne
      have yn : shifted i q ≠ (0,0) := by
        intro eq; apply g; change |(shifted i q).1| ≤ 2 ∧ |(shifted i q).2| ≤ 2; norm_num [eq]
      have hp := bellmanGauge_pos _ yn
      have p := (Real.rpow_le_rpow_of_exponent_le (one_le_mul_of_one_le_of_one_le hK hk1) (show (-2:ℝ) ≤ α-2 by linarith)).trans (Real.rpow_le_rpow_of_nonpos hp (upper _ mem) (by linarith))
      rw [Real.rpow_neg (by positivity),Real.rpow_two] at p
      exact (mul_le_mul_of_nonneg_left p B.positive.le).trans (outside_good B g hb)
    have hsum := sum_le_sum low
    have hc : (S.erase l).card = k^3 := by simp [card_erase_of_mem hl,S]
    simp only [sum_const,hc,nsmul_eq_mul,Nat.cast_pow] at hsum
    have hbnd := (neg_le_abs (L l)).trans (by simpa [L] using B.bound 1 one_pos b hb (shifted l q))
    have hlower : 1+B.cost ≤ (k:ℝ)^3*(B.pos/(K*k)^2) := by
      rw [← mul_div_assoc,le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hlarge.le (sq_nonneg (k:ℝ))]
    rw [← sum_erase_add _ _ hl]
    apply le_trans (b := 1) _ (by linarith); by_cases e : q ∈ box A 1 0 <;> simp [e]
  · have nmem : q ∉ box A 1 0 := by
      intro h; apply near; refine ⟨0,Z0,?_⟩; simpa [shifted] using (show |q.1| ≤ D ∧ |q.2| ≤ D from ⟨(by simpa using h.1 : |q.1| ≤ A) |>.trans dA,(by simpa using h.2 : |q.2| ≤ A) |>.trans dA⟩)
    rw [indicator_of_notMem nmem]
    apply sum_nonneg; intro i hi
    apply le_trans _ (outside_good B (fun e => near ⟨i,hi,e.1.trans d,e.2.trans d⟩) hb)
    exact mul_nonneg B.positive.le (Real.rpow_nonneg (Real.rpow_nonneg (bellmanGaugePower_nonneg _) _) _)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxBarrier
