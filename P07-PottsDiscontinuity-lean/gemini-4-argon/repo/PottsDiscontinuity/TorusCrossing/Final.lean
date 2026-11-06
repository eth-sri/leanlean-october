module

public import PottsDiscontinuity.TorusCrossing.Mixture
public import PottsDiscontinuity.TorusCrossing.TorusBarrier
public import PottsDiscontinuity.TorusCrossing.TorusTranslate
public import PottsDiscontinuity.TorusRC.IndexedOpening
public import PottsDiscontinuity.TorusRC.TiltDuality

/-!
# The crossing estimate (3.19)

For every `q ≥ 1` there is `c > 0` such that for all even periods `N, M ≥ 4` and all `n ≥ 1`
with `3n ≤ min(N, M)`, the torus random-cluster measure at `p_c(q)` gives probability at least
`c` to a vertical open crossing of the rectangle `[0,3n] × [0,n]`.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open PottsDiscontinuity.TorusRC Torus CorrLength
open scoped Classical

variable {N M : ℕ}

theorem prob_cover (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E1 E2 E3 : Set (RCConfig N M)) (h : ∀ A, A ∈ E1 ∨ A ∈ E2 ∨ A ∈ E3) :
    1 ≤ torusRCProbability hN hM q E1 + torusRCProbability hN hM q E2 +
      torusRCProbability hN hM q E3 := by
  rw [torusRCProbability_eq_sum, torusRCProbability_eq_sum, torusRCProbability_eq_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← sum_torusRCMass hN hM q]
  refine Finset.sum_le_sum fun A _ => ?_
  have n1 := Set.indicator_nonneg (fun x _ => (torusRCMass_pos hN hM q x).le) A (s := E1)
  have n2 := Set.indicator_nonneg (fun x _ => (torusRCMass_pos hN hM q x).le) A (s := E2)
  have n3 := Set.indicator_nonneg (fun x _ => (torusRCMass_pos hN hM q x).le) A (s := E3)
  rcases h A with h1 | h2 | h3
  · rw [Set.indicator_of_mem h1]; linarith
  · rw [Set.indicator_of_mem h2]; linarith
  · rw [Set.indicator_of_mem h3]; linarith

theorem prob_dual_le (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (RCConfig N M)) :
    torusRCProbability hN hM q {A | translatedDualConfig A ∈ E} ≤
      q.val ^ 2 * torusRCProbability hN hM q E := by
  have h := torusRCProbability_translatedDual_lower hN hM q E
  rw [div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one q.property) _)] at h
  change torusRCProbability hN hM q (translatedDualConfig ⁻¹' E) ≤ _
  linarith

theorem core_bound (q : Set.Ici (1 : ℝ)) (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (n s : ℕ) (hn : 0 < n) (hs : s % 2 = 1) (hs1 : s + 1 ≤ 3 * n)
    (hs2 : 2 * n < s) (hN3 : 3 * n ≤ N) (hM3 : 3 * n ≤ M)
    (ρF : ℤ) (hρFe : Even ρF) (hρF1 : (n : ℤ) - 1 ≤ ρF) (hρF2 : ρF + n ≤ (s : ℤ) - n + 1)
    (aT : ℤ) (haT : aT = 0 ∨ aT = 1) (hρTe : Even (aT + ((s : ℤ) - n))) :
    1 / (1 + q.val + 2 * q.val ^ 2) ≤
      torusRCProbability hN hM q {A | vCross hNp hMp n 0 0 A} := by
  set Q : Rect := ⟨0, 0, s, s⟩ with hQ
  have hg : Q.Geo n n := ⟨by simp [hQ]; omega, hn, hn, by simp [hQ]; omega⟩
  set p₀ := torusRCProbability hN hM q {A | vCross hNp hMp n 0 0 A}
  have hq0 : 0 < q.val := lt_of_lt_of_le zero_lt_one q.property
  have hF : torusRCProbability hN hM q {A | Q.crossEv n n (boardOf Q hNp hMp A)} ≤ p₀ :=
    (torusRCProbability_mono hN hM q (F := {A | vCross hNp hMp n 0 ρF A})
      fun A => cross_to_vCross hNp hMp Q A n hn 0 ρF
        ⟨by simp [hQ], by simp [hQ]; omega⟩ (by simp [hQ]; omega) (by simp [hQ]; omega)).trans
      (prob_vCross_le hN hM hNp hMp q n 0 ρF (by simpa using hρFe))
  have hB : torusRCProbability hN hM q {A | ¬ Q.barB n (boardOf Q hNp hMp A)} ≤ q.val ^ 2 * p₀ :=
    (torusRCProbability_mono hN hM q (F := {A | translatedDualConfig A ∈ {A | vCross hNp hMp n 0 0 A}})
      fun A => notBarB_to_vCross hNp hMp Q A hg n hn 0 0
        ⟨by simp [hQ], by simp [hQ]; omega⟩ (by simp [hQ]) (by simp [hQ])).trans (prob_dual_le hN hM q _)
  have hT : torusRCProbability hN hM q {A | ¬ Q.barT n (boardOf Q hNp hMp A)} ≤ q.val ^ 2 * p₀ :=
    ((torusRCProbability_mono hN hM q
      (F := {A | translatedDualConfig A ∈ {A | vCross hNp hMp n aT ((s : ℤ) - n) A}})
      fun A => notBarT_to_vCross hNp hMp Q A hg n hn aT ((s : ℤ) - n)
        ⟨by simp [hQ]; omega, by simp [hQ]; omega⟩ (by simp [hQ]) (by simp [hQ])).trans
      (prob_dual_le hN hM q _)).trans
      (mul_le_mul_of_nonneg_left (prob_vCross_le hN hM hNp hMp q n aT ((s : ℤ) - n) hρTe) (sq_nonneg _))
  have hcov := prob_cover hN hM q {A | Q.barAll n n (boardOf Q hNp hMp A)}
    {A | ¬ Q.barB n (boardOf Q hNp hMp A)} {A | ¬ Q.barT n (boardOf Q hNp hMp A)} fun A => by
      by_cases h1 : Q.barB n (boardOf Q hNp hMp A) <;> by_cases h2 : Q.barT n (boardOf Q hNp hMp A) <;>
        [exact Or.inl ⟨h1, h2⟩; exact Or.inr (Or.inr h2); exact Or.inr (Or.inl h1); exact Or.inr (Or.inl h1)]
  have hbl := torus_bl q hN hM hNp hMp hN4 hM4 Q hg (by simp [hQ]; omega) (by simp [hQ]; omega)
  have hκ : 1 / (1 + q.val) ≤ (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal :=
    Rect.crossing_ge Q q rfl hs (by simp [hQ]; omega)
  set κ := (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal
  set Pbar := torusRCProbability hN hM q {A | Q.barAll n n (boardOf Q hNp hMp A)}
  have hPbar : 1 - 2 * (q.val ^ 2 * p₀) ≤ Pbar := by linarith
  have hmain : κ * Pbar ≤ p₀ := hbl.trans hF
  have hp0nn : 0 ≤ p₀ := torusRCProbability_nonneg hN hM q _
  have hc0 : 0 < 1 / (1 + q.val) := by positivity
  rw [div_le_iff₀ (by positivity)]
  by_cases hcase : 1 - 2 * (q.val ^ 2 * p₀) ≤ 0
  · nlinarith [sq_nonneg q.val]
  · push Not at hcase
    have h2 : 1 / (1 + q.val) * (1 - 2 * (q.val ^ 2 * p₀)) ≤ p₀ :=
      ((mul_le_mul_of_nonneg_right hκ hcase.le).trans
        (mul_le_mul_of_nonneg_left hPbar (hc0.le.trans hκ))).trans hmain
    have := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 1 + q.val by positivity)
    field_simp at this
    nlinarith

theorem one_bound (q : Set.Ici (1 : ℝ)) (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) :
    fkOpenEnergy (torusRCBridgeParameters q) ≤
      torusRCProbability hN hM q {A | vCross hNp hMp 1 0 0 A} := by
  have h := torusRCProbability_allOpen_ge hN hM hN4 hM4 q
    {(periodicCoordinate hNp 1, periodicCoordinate hMp 1)}
  rw [Finset.card_singleton, pow_one] at h
  refine h.trans (torusRCProbability_mono hN hM q fun A hA => ?_)
  let u : RotatedVertex := ⟨(0, 0), ⟨0, rfl⟩⟩
  let v : RotatedVertex := ⟨(1, 1), ⟨1, rfl⟩⟩
  have hadj : (liftedStripGraph hNp hMp A 0 (0 + 3 * ((1 : ℕ) : ℤ))).Adj u v :=
    ⟨by change |(0 : ℤ) - 1| = 1 ∧ |(0 : ℤ) - 1| = 1; norm_num,
     by change A (periodicCoordinate hNp (max 0 1), periodicCoordinate hMp (max 0 1)) = true
        simpa using hA (periodicCoordinate hNp 1, periodicCoordinate hMp 1) (Finset.mem_singleton_self _),
     ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  refine ⟨u, v, rfl, rfl, SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, fun z hz => ?_⟩
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl <;> constructor <;> norm_num [u, v]

theorem h319_proved (q : Set.Ici (1 : ℝ)) : h319 q := by
  have hq0 : 0 < q.val := lt_of_lt_of_le zero_lt_one q.property
  refine ⟨min (fkOpenEnergy (torusRCBridgeParameters q)) (1 / (1 + q.val + 2 * q.val ^ 2)),
    lt_min (fkOpenEnergy_pos _) (by positivity), ?_⟩
  intro N M n hN hM hN4 hM4 hn h3N h3M hNpos hMpos
  show _ ≤ torusRCProbability hN hM q {A | torusRCVerticalRectangleCrossing hNpos hMpos n A}
  rw [show {A | torusRCVerticalRectangleCrossing hNpos hMpos n A} =
      {A | vCross hNpos hMpos n 0 0 A} by ext A; exact (vCross_zero_iff hNpos hMpos n A).symm]
  by_cases hn1 : n = 1
  · subst hn1; exact (min_le_left _ _).trans (one_bound q hN hM hNpos hMpos hN4 hM4)
  · refine (min_le_right _ _).trans ?_
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact core_bound q hN hM hNpos hMpos hN4 hM4 (k + k) (3 * (k + k) - 1) hn (by omega)
        (by omega) (by omega) h3N h3M (k + k : ℕ) ⟨k, by push_cast; ring⟩ (by omega) (by omega) 1
        (Or.inr rfl) ⟨k + k, by omega⟩
    · exact core_bound q hN hM hNpos hMpos hN4 hM4 (2 * k + 1) (3 * (2 * k + 1) - 2) hn (by omega)
        (by omega) (by omega) h3N h3M ((2 * k + 1 : ℕ) - 1) ⟨k, by omega⟩ (by omega) (by omega)
        0 (Or.inl rfl) ⟨2 * k, by omega⟩

end PottsDiscontinuity.TorusCrossing
