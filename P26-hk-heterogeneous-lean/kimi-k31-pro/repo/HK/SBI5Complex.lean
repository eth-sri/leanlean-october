module

public import HK.Basic

/-!
# Five SBI agents with a constant digraph and oscillatory convergence

The averaging map on the three moving agents' offsets has a complex conjugate pair of modes; the
initial offset cancels its real mode. A four-step consequence of the second-order recurrence gives
both signs in every five consecutive times, with no trigonometry and no density argument.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- The first coefficient of the recurrence `z(t+2) = α z(t+1) − β z(t)` of the offsets. -/
noncomputable def sbi5Alpha (ρ : ℝ) : ℝ := 47 / 60 - ρ

/-- The second coefficient; at the root of the cubic, `60 ρ β = 1`. -/
noncomputable def sbi5Beta (ρ : ℝ) : ℝ := ρ ^ 2 - 47 / 60 * ρ + 3 / 20

theorem sbi5_r_pos : ∀ i, 0 < sbi5_r i := by
  intro i
  fin_cases i <;> norm_num [sbi5_r]

theorem sbi5Offset_zero (ρ : ℝ) : sbi5Offset ρ 0 = ![1 / 3 - ρ, 1 / 5, 0] := rfl

theorem sbi5Offset_succ (ρ : ℝ) (t : ℕ) :
    sbi5Offset ρ (t + 1) = sbi5LinearStep (sbi5Offset ρ t) :=
  Function.iterate_succ_apply' _ _ _

theorem sbi5_root_exists : ∃ ρ : ℝ, 57 / 100 < ρ ∧ ρ < 29 / 50 ∧
    60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1 = 0 := by
  obtain ⟨ρ, ⟨hρlo, hρhi⟩, hp⟩ := intermediate_value_Ioo
    (a := (57 / 100 : ℝ)) (b := 29 / 50)
    (f := fun ρ : ℝ => 60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1)
    (by norm_num) (by fun_prop) (show (0 : ℝ) ∈ Set.Ioo _ _ by norm_num)
  exact ⟨ρ, hρlo, hρhi, hp⟩

theorem sbi5_offset_bound (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (t : ℕ) : ∀ i, |sbi5Offset ρ t i| ≤ (2 / 3 : ℝ) ^ t / 3 := by
  induction t with
  | zero =>
    intro i
    fin_cases i <;> simp [sbi5Offset_zero, abs_le] <;> (try constructor) <;> linarith
  | succ t ih =>
    have h : ∀ i, |sbi5LinearStep (sbi5Offset ρ t) i| ≤ (2 / 3) * ((2 / 3 : ℝ) ^ t / 3) := by
      intro i
      fin_cases i <;> simp [sbi5LinearStep, abs_div] <;>
        linarith [ih 0, ih 1, ih 2, (by positivity : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ t / 3),
          abs_add_le (sbi5Offset ρ t 0) (sbi5Offset ρ t 1),
          abs_add_le (sbi5Offset ρ t 0) (sbi5Offset ρ t 2),
          abs_add_le (sbi5Offset ρ t 1) (sbi5Offset ρ t 2),
          abs_add_le (sbi5Offset ρ t 0 + sbi5Offset ρ t 1) (sbi5Offset ρ t 2)]
    intro i
    have heq : (2 / 3 : ℝ) ^ (t + 1) / 3 = (2 / 3) * ((2 / 3 : ℝ) ^ t / 3) := by
      rw [pow_succ]; ring
    simpa only [sbi5Offset_succ, heq] using h i

theorem sbi5_offset_small (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (t : ℕ) (i : Fin 3) : |sbi5Offset ρ t i| ≤ 1 / 3 := by
  have h := sbi5_offset_bound ρ hlo hhi t i
  have hp : (2 / 3 : ℝ) ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

theorem sbi5_table (z : Fin 3 → ℝ) (hz : ∀ i, |z i| ≤ 1 / 3) :
    neighbors .sbi sbi5_r (sbi5_lim + sbi5Lift z) =
      ![{0}, {0, 1, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4}, {4}] := by
  have h0 := abs_le.mp (hz 0)
  have h1 := abs_le.mp (hz 1)
  have h2 := abs_le.mp (hz 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, sbi5_r, sbi5_lim, sbi5Lift, abs_le] <;>
    (try constructor) <;> (try intro) <;> linarith

theorem sbi5_step (z : Fin 3 → ℝ) (hz : ∀ i, |z i| ≤ 1 / 3) :
    step .sbi sbi5_r (sbi5_lim + sbi5Lift z) = sbi5_lim + sbi5Lift (sbi5LinearStep z) := by
  funext i
  rw [step_apply, sbi5_table z hz]
  fin_cases i <;> simp [Finset.sum_insert, sbi5_lim, sbi5Lift, sbi5LinearStep] <;> ring

theorem sbi5_trajectory (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (t : ℕ) : traj .sbi sbi5_r (sbi5_x0 ρ) t = sbi5_lim + sbi5Lift (sbi5Offset ρ t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [traj_succ, ih, sbi5_step _ (sbi5_offset_small ρ hlo hhi t), sbi5Offset_succ]

theorem sbi5_neighbors (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (t : ℕ) : neighbors .sbi sbi5_r (traj .sbi sbi5_r (sbi5_x0 ρ) t) =
      ![{0}, {0, 1, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4}, {4}] := by
  rw [sbi5_trajectory ρ hlo hhi, sbi5_table _ (sbi5_offset_small ρ hlo hhi t)]

theorem sbi5_linear (a b : ℝ) (u v : Fin 3 → ℝ) :
    sbi5LinearStep (fun i => a * u i - b * v i) =
      fun i => a * sbi5LinearStep u i - b * sbi5LinearStep v i := by
  funext i
  fin_cases i <;> simp [sbi5LinearStep] <;> ring

theorem sbi5_offset_recurrence (ρ : ℝ)
    (hp : 60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1 = 0) (t : ℕ) :
    sbi5Offset ρ (t + 2) = fun i =>
      sbi5Alpha ρ * sbi5Offset ρ (t + 1) i - sbi5Beta ρ * sbi5Offset ρ t i := by
  induction t with
  | zero =>
    change sbi5LinearStep (sbi5LinearStep ![1 / 3 - ρ, 1 / 5, 0]) =
      fun i => sbi5Alpha ρ * sbi5LinearStep ![1 / 3 - ρ, 1 / 5, 0] i -
        sbi5Beta ρ * (![1 / 3 - ρ, 1 / 5, 0] : Fin 3 → ℝ) i
    funext i
    fin_cases i <;> simp [sbi5LinearStep, sbi5Alpha, sbi5Beta] <;> nlinarith [hp]
  | succ t ih =>
    rw [show t + 1 + 2 = t + 2 + 1 from rfl, sbi5Offset_succ]
    conv_rhs => simp only [sbi5Offset_succ]
    rw [← sbi5_linear, ih, sbi5Offset_succ]

theorem sbi5_tendsto (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50) :
    Tendsto (traj .sbi sbi5_r (sbi5_x0 ρ)) atTop (𝓝 sbi5_lim) := by
  have hpow : Tendsto (fun t : ℕ => (2 / 3 : ℝ) ^ t / 3) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      (by norm_num : |(2 / 3 : ℝ)| < 1)).div_const 3
  have hz : ∀ i : Fin 3, Tendsto (fun t => sbi5Offset ρ t i) atTop (𝓝 0) := by
    intro i
    exact squeeze_zero_norm (fun t => by
      simpa only [Real.norm_eq_abs] using sbi5_offset_bound ρ hlo hhi t i) hpow
  apply tendsto_pi_nhds.2
  intro i
  fin_cases i
  · simp [sbi5_trajectory ρ hlo hhi, sbi5_lim, sbi5Lift]
  · simpa [sbi5_trajectory ρ hlo hhi, sbi5_lim, sbi5Lift] using (hz 0).const_add 10
  · simpa [sbi5_trajectory ρ hlo hhi, sbi5_lim, sbi5Lift] using (hz 1).const_add 18
  · simpa [sbi5_trajectory ρ hlo hhi, sbi5_lim, sbi5Lift] using (hz 2).const_add 20
  · simp [sbi5_trajectory ρ hlo hhi, sbi5_lim, sbi5Lift]

theorem sbi5_digraph_constant (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (t : ℕ) : proximityDigraph .sbi sbi5_r (traj .sbi sbi5_r (sbi5_x0 ρ) t) =
      proximityDigraph .sbi sbi5_r (sbi5_x0 ρ) :=
  digraph_constant_of_neighbors _ _ _ _ (sbi5_neighbors ρ hlo hhi) t

/-- The five-window property for the moving agents, indexed by `Fin 3` (`i` is agent `i + 1`). -/
theorem sbi5_oscillates_fin3 (ρ : ℝ)
    (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (hp : 60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1 = 0) (t : ℕ) (i : Fin 3) :
    (∃ k, t ≤ k ∧ k ≤ t + 4 ∧
      traj .sbi sbi5_r (sbi5_x0 ρ) k i.succ.castSucc < sbi5_lim i.succ.castSucc) ∧
    (∃ k, t ≤ k ∧ k ≤ t + 4 ∧
      sbi5_lim i.succ.castSucc < traj .sbi sbi5_r (sbi5_x0 ρ) k i.succ.castSucc) := by
  have hw : (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ sbi5Offset ρ k i < 0) ∧
      (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ 0 < sbi5Offset ρ k i) := by
    have hsq : (57 / 100 : ℝ) ^ 2 < ρ ^ 2 := by nlinarith
    have ha : 0 < sbi5Alpha ρ := by dsimp [sbi5Alpha]; linarith
    have hb : 0 < sbi5Beta ρ := by dsimp [sbi5Beta]; nlinarith
    have hba : sbi5Beta ρ < sbi5Alpha ρ ^ 2 := by dsimp [sbi5Alpha, sbi5Beta]; nlinarith
    have hab : sbi5Alpha ρ ^ 2 < 2 * sbi5Beta ρ := by dsimp [sbi5Alpha, sbi5Beta]; nlinarith
    have hnz : ¬ (sbi5Offset ρ t i = 0 ∧ sbi5Offset ρ (t + 1) i = 0) := by
      induction t with
      | zero =>
        fin_cases i <;> simp [sbi5Offset_zero, sbi5Offset_succ, sbi5LinearStep]
        linarith
      | succ t ih =>
        rintro ⟨h1, h2⟩
        have hr := congrFun (sbi5_offset_recurrence ρ hp t) i
        have hz : sbi5Offset ρ t i = 0 := by
          have hm : sbi5Beta ρ * sbi5Offset ρ t i = 0 := by
            rw [h1, h2] at hr
            linarith
          exact (mul_eq_zero.mp hm).resolve_left hb.ne'
        exact ih ⟨hz, h1⟩
    have hc : sbi5Alpha ρ * (sbi5Alpha ρ ^ 2 - 2 * sbi5Beta ρ) < 0 :=
      mul_neg_of_pos_of_neg ha (by linarith)
    have hd : sbi5Beta ρ * (sbi5Beta ρ - sbi5Alpha ρ ^ 2) < 0 :=
      mul_neg_of_pos_of_neg hb (by linarith)
    have hrec : sbi5Offset ρ (t + 4) i =
        sbi5Alpha ρ * (sbi5Alpha ρ ^ 2 - 2 * sbi5Beta ρ) * sbi5Offset ρ (t + 1) i +
        sbi5Beta ρ * (sbi5Beta ρ - sbi5Alpha ρ ^ 2) * sbi5Offset ρ t i := by
      have h0 := congrFun (sbi5_offset_recurrence ρ hp t) i
      have h1 := congrFun (sbi5_offset_recurrence ρ hp (t + 1)) i
      have h2 := congrFun (sbi5_offset_recurrence ρ hp (t + 2)) i
      simp only [Nat.add_assoc] at h0 h1 h2
      rw [h2, h1, h0]
      ring
    constructor
    · by_contra! hn
      apply hnz
      have h0 := hn t le_rfl (by omega)
      have h1 := hn (t + 1) (by omega) (by omega)
      have h4 := hn (t + 4) (by omega) le_rfl
      constructor <;> nlinarith [mul_nonpos_of_nonpos_of_nonneg hc.le h1,
        mul_nonpos_of_nonpos_of_nonneg hd.le h0]
    · by_contra! hn
      apply hnz
      have h0 := hn t le_rfl (by omega)
      have h1 := hn (t + 1) (by omega) (by omega)
      have h4 := hn (t + 4) (by omega) le_rfl
      constructor <;> nlinarith [mul_nonneg_of_nonpos_of_nonpos hc.le h1,
        mul_nonneg_of_nonpos_of_nonpos hd.le h0]
  obtain ⟨⟨k, hk0, hk4, hk⟩, ⟨l, hl0, hl4, hl⟩⟩ := hw
  fin_cases i <;> simp_all [sbi5_trajectory ρ hlo hhi, sbi5_lim, sbi5Lift] <;>
    exact ⟨⟨k, hk0, hk4, hk⟩, ⟨l, hl0, hl4, hl⟩⟩

theorem sbi5_oscillates_every_five (ρ : ℝ)
    (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (hp : 60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1 = 0) (t : ℕ) (i : Fin 5)
    (hi : i ∈ ({1, 2, 3} : Finset (Fin 5))) :
    (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ traj .sbi sbi5_r (sbi5_x0 ρ) k i < sbi5_lim i) ∧
    (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ sbi5_lim i < traj .sbi sbi5_r (sbi5_x0 ρ) k i) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · exact sbi5_oscillates_fin3 ρ hlo hhi hp t 0
  · exact sbi5_oscillates_fin3 ρ hlo hhi hp t 1
  · exact sbi5_oscillates_fin3 ρ hlo hhi hp t 2

theorem sbi5_not_fixedFrom (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (hp : 60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1 = 0) (τ : ℕ) :
    ¬ FixedFrom (traj .sbi sbi5_r (sbi5_x0 ρ)) τ := by
  intro hf
  obtain ⟨⟨k, hk0, -, hk⟩, ⟨l, hl0, -, hl⟩⟩ :=
    sbi5_oscillates_every_five ρ hlo hhi hp τ 1 (by simp)
  linarith [congrFun (hf k hk0) (1 : Fin 5), congrFun (hf l hl0) (1 : Fin 5)]

theorem sbi5_not_pseudoStableAfter (ρ : ℝ)
    (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (hp : 60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1 = 0) (xinf : Fin 5 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbi sbi5_r (sbi5_x0 ρ)) xinf τ := by
  intro hps
  have he : xinf = sbi5_lim := tendsto_nhds_unique hps.1 (sbi5_tendsto ρ hlo hhi)
  rw [he] at hps
  obtain ⟨⟨k, hk0, -, hk⟩, ⟨l, hl0, -, hl⟩⟩ :=
    sbi5_oscillates_every_five ρ hlo hhi hp τ 1 (by simp)
  obtain ⟨-, F, C, -, -, -, hFC, h⟩ := hps
  have hi : (1 : Fin 5) ∈ F ∨ (1 : Fin 5) ∈ C := by
    rw [← Finset.mem_union, hFC]
    exact Finset.mem_univ 1
  rcases hi with hi | hi
  · linarith [(h k hk0).1 1 hi]
  · rcases (h τ le_rfl).2 1 hi with hbelow | habove
    · have hs : ∀ t, τ ≤ t → traj .sbi sbi5_r (sbi5_x0 ρ) t 1 < sbi5_lim 1 := by
        intro t ht
        induction t, ht using Nat.le_induction with
        | base => linarith [hbelow.1, hbelow.2]
        | succ t ht ih =>
          rcases (h t ht).2 1 hi with hb | ha
          · exact hb.2
          · exfalso; linarith
      linarith [hs l hl0]
    · have hs : ∀ t, τ ≤ t → sbi5_lim 1 < traj .sbi sbi5_r (sbi5_x0 ρ) t 1 := by
        intro t ht
        induction t, ht using Nat.le_induction with
        | base => linarith [habove.1, habove.2]
        | succ t ht ih =>
          rcases (h t ht).2 1 hi with hb | ha
          · exfalso; linarith
          · exact ha.2
      linarith [hs k hk0]

theorem not_conjecture23_sbi_five : ¬ Conjecture23ForAgents .sbi 5 := by
  obtain ⟨ρ, hlo, hhi, hp⟩ := sbi5_root_exists
  exact not_conjecture23_of .sbi sbi5_r (sbi5_x0 ρ) sbi5_r_pos
    (sbi5_not_fixedFrom ρ hlo hhi hp) (sbi5_not_pseudoStableAfter ρ hlo hhi hp)

theorem not_theorem64iv_sbi_five : ¬ Theorem64ivForAgents .sbi 5 := by
  obtain ⟨ρ, hlo, hhi, hp⟩ := sbi5_root_exists
  exact not_theorem64iv_of .sbi sbi5_r (sbi5_x0 ρ) sbi5_r_pos
    (sbi5_digraph_constant ρ hlo hhi) (sbi5_not_fixedFrom ρ hlo hhi hp)
    (sbi5_not_pseudoStableAfter ρ hlo hhi hp)

end HK
