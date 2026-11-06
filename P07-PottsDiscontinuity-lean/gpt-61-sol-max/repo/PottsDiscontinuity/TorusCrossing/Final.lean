module
public import Mathlib

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


open PottsDiscontinuity.TorusRC Torus CorrLength
open scoped Classical

variable {N M : ℕ}

section

variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
include hN hM q

theorem prob_cover 
    (E1 E2 E3 : Set (RCConfig N M)) (h : ∀ A, A ∈ E1 ∨ A ∈ E2 ∨ A ∈ E3) :
    1 ≤ torusRCProbability hN hM q E1 + torusRCProbability hN hM q E2 +
      torusRCProbability hN hM q E3 := by
  rw [torusRCProbability_eq_sum, torusRCProbability_eq_sum, torusRCProbability_eq_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc  1  = ∑ A, torusRCMass hN hM q A := (sum_torusRCMass hN hM q).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro A _
      
      have n1 : 0 ≤ E1.indicator (torusRCMass hN hM q) A := by
                                                              solve_by_elim [_root_.Set.indicator_nonneg, _root_.LT.lt.le, _root_.PottsDiscontinuity.TorusRC.torusRCMass_pos]
      have n2 : 0 ≤ E2.indicator (torusRCMass hN hM q) A := by
                                                              solve_by_elim [_root_.Set.indicator_nonneg, _root_.LT.lt.le, _root_.PottsDiscontinuity.TorusRC.torusRCMass_pos]
      have n3 : 0 ≤ E3.indicator (torusRCMass hN hM q) A := by
                                                              solve_by_elim [_root_.Set.indicator_nonneg, _root_.LT.lt.le, _root_.PottsDiscontinuity.TorusRC.torusRCMass_pos]
      rcases h A with h1 | h2 | h3
      · rw [Set.indicator_of_mem h1]; linarith
      · rw [Set.indicator_of_mem h2]; linarith
      · rw [Set.indicator_of_mem h3]; linarith

theorem prob_dual_le 
    (E : Set (RCConfig N M)) :
    torusRCProbability hN hM q {A | translatedDualConfig A ∈ E} ≤
      q.val ^ 2 * torusRCProbability hN hM q E := by
  have h := torusRCProbability_translatedDual_lower hN hM q E
  
  rw [div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one q.property) _)] at h
  change torusRCProbability hN hM q (translatedDualConfig ⁻¹' E) ≤ _
  linarith

end

section

variable (q : Set.Ici (1 : ℝ)) (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
include hN4 hM4

/-- The core estimate, for suitable parameters of the board. -/
theorem core_bound  (n s : ℕ) (hn : 0 < n) (hs : s % 2 = 1) (hs1 : s + 1 ≤ 3 * n)
    (hs2 : 2 * n < s) (hN3 : 3 * n ≤ N) (hM3 : 3 * n ≤ M)
    (ρF : ℤ) (hρFe : Even ρF) (hρF1 : (n : ℤ) - 1 ≤ ρF) (hρF2 : ρF + n ≤ (s : ℤ) - n + 1)
    (aT : ℤ) (haT : aT = 0 ∨ aT = 1) (hρTe : Even (aT + ((s : ℤ) - n))) :
    1 / (1 + q.val + 2 * q.val ^ 2) ≤
      torusRCProbability hN hM q {A | vCross hNp hMp n 0 0 A} := by
  set Q : Rect := ⟨0, 0, s, s⟩ with hQ
  have hg : Q.Geo n n := ⟨by simp [hQ]; omega, hn, hn, by simp [hQ]; omega⟩
  
  have hodd  := hs
  
  
  set p₀ := torusRCProbability hN hM q {A | vCross hNp hMp n 0 0 A} with hp₀
  have hq1  := q.property
  have hq0  := lt_of_lt_of_le zero_lt_one hq1
  -- crossing event
  
  -- the barriers
  have hB : torusRCProbability hN hM q {A | ¬ Q.barB n (boardOf Q hNp hMp A)} ≤ q.val ^ 2 * p₀ := (torusRCProbability_mono hN hM q (by
                                                                                                                                      intro A hA
                                                                                                                                      exact notBarB_to_vCross hNp hMp Q A hg n hn 0 0 ⟨by simp [hQ], by simp [hQ]; omega⟩
                                                                                                                                        (by simp [hQ]) (by simp [hQ]) hA)).trans (prob_dual_le hN hM q _)
  have hT : torusRCProbability hN hM q {A | ¬ Q.barT n (boardOf Q hNp hMp A)} ≤ q.val ^ 2 * p₀ := by
    
    calc _ ≤ _ := torusRCProbability_mono hN hM q (by
                                                     intro A hA
                                                     refine notBarT_to_vCross hNp hMp Q A hg n hn aT ( s  - n)
                                                       ⟨by simp [hQ]; omega, by simp [hQ]; omega⟩ (by simp [hQ]) (by simp [hQ]) hA)
      _ ≤ q.val ^ 2 * torusRCProbability hN hM q {A | vCross hNp hMp n aT ( s  - n) A} :=
          prob_dual_le hN hM q _
      _ ≤ q.val ^ 2 * p₀ := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact prob_vCross_le hN hM hNp hMp q n aT ( s  - n) hρTe
  -- covering
  have hcov := prob_cover hN hM q {A | Q.barAll n n (boardOf Q hNp hMp A)}
    {A | ¬ Q.barB n (boardOf Q hNp hMp A)} {A | ¬ Q.barT n (boardOf Q hNp hMp A)}  fun A =>
                                                                                     if h1 : Q.barB n (boardOf Q hNp hMp A) then
                                                                                       if h2 : Q.barT n (boardOf Q hNp hMp A) then Or.inl ⟨h1, h2⟩ else Or.inr (Or.inr h2)
                                                                                     else Or.inr (Or.inl h1) 
  -- the board estimate
  
  have hκ  :=
    Rect.crossing_ge Q q  rfl  hodd (by simp [hQ]; omega)
  set κ := (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal with hκd
  set Pbar := torusRCProbability hN hM q {A | Q.barAll n n (boardOf Q hNp hMp A)} with hPbar
  
  
  
  have hp0nn : 0 ≤ p₀ := torusRCProbability_nonneg hN hM q _
  -- final algebra
  
  rw [div_le_iff₀ (by positivity)]
  by_cases hcase : 1 - 2 * (q.val ^ 2 * p₀) ≤ 0
  · nlinarith [sq_nonneg q.val]
  · push Not at hcase
    
    have h2  := (Trans.trans (mul_le_mul_of_nonneg_right hκ (LT.lt.le hcase))
                                                                                        (mul_le_mul_of_nonneg_left (by linarith) (LE.le.trans (LT.lt.le (by positivity)) hκ))).trans ((torus_bl q hN hM hNp hMp hN4 hM4 Q hg (by simp [hQ]; omega) (by simp [hQ]; omega)).trans (by
                                                                                                                                                                               
                                                                                                                                                                               exact (torusRCProbability_mono hN hM q (by
                                                                                                                                                                                                                         intro A hA
                                                                                                                                                                                                                         refine cross_to_vCross hNp hMp Q A n hn 0 ρF ⟨by simp [hQ], by simp [hQ]; omega⟩ ?_ ?_ hA
                                                                                                                                                                                                                         all_goals grind)).trans
                                                                                                                                                                                 (prob_vCross_le hN hM hNp hMp q n 0 ρF (by simpa using hρFe))))
    have h3 : 1 - 2 * (q.val ^ 2 * p₀) ≤ (1 + q.val) * p₀ := by
      have := mul_le_mul_of_nonneg_left h2 (show  0  ≤ 1 + q.val by positivity)
      field_simp at this
      linarith
    nlinarith

/-- The case `n = 1`: a single open edge. -/
theorem one_bound  :
    fkOpenEnergy (torusRCBridgeParameters q) ≤
      torusRCProbability hN hM q {A | vCross hNp hMp 1 0 0 A} := by
  have h := torusRCProbability_allOpen_ge hN hM hN4 hM4 q
    {(periodicCoordinate hNp 1, periodicCoordinate hMp 1)}
  rw [Finset.card_singleton, pow_one] at h
  refine h.trans (torusRCProbability_mono hN hM q ?_)
  intro A hA
  have hA'  :=
    hA _ (Finset.mem_singleton_self _)
  let u : RotatedVertex := ⟨(0, 0), ⟨0, rfl⟩⟩
  let v : RotatedVertex := ⟨(1, 1), ⟨1, rfl⟩⟩
  have hadj : (liftedStripGraph hNp hMp A 0 (0 + 3 *  1 )).Adj u v := by
    refine ⟨?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · change |(0 ) - 1| = 1 ∧ |(0 ) - 1| = 1
      norm_num
    · assumption
    all_goals norm_num
  refine ⟨u, v, rfl, rfl, SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
  intro z hz
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl <;> constructor <;> norm_num 

end

/-- **Equation (3.19)**: the crossing estimate for the torus. -/
theorem h319_proved (q : Set.Ici (1 : ℝ)) : h319 q := by
  have hq1  := q.property
  have hq0  := lt_of_lt_of_le zero_lt_one hq1
  refine ⟨min (fkOpenEnergy (torusRCBridgeParameters q)) (1 / (1 + q.val + 2 * q.val ^ 2)),
    lt_min (fkOpenEnergy_pos _) (by positivity), ?_⟩
  intro N M n hN hM hN4 hM4 hn h3N h3M hNpos hMpos
  
  have heq : {A | torusRCVerticalRectangleCrossing hNpos hMpos n A} =
      {A | vCross hNpos hMpos n 0 0 A} := by
                                            solve_by_elim [_root_.Set.ext, _root_.Iff.symm, _root_.PottsDiscontinuity.TorusCrossing.vCross_zero_iff]
  rw [heq]
  by_cases hn1 : n = 1
  · simp_all [one_bound]
  · refine (min_le_right _ _).trans ?_
    
    rcases Nat.even_or_odd n with he | ho
    · refine core_bound q hN hM hNpos hMpos hN4 hM4 n (3 * n - 1) hn (by grind)
        (by omega) (by omega) h3N h3M  n  (by exact_mod_cast he) (by omega) (by omega) 1
        (Or.inr rfl) ?_
      grind
    · have hn3 : 3 ≤ n := by grind
      refine core_bound q hN hM hNpos hMpos hN4 hM4 n (3 * n - 2) hn (by grind)
        (by omega) (by omega) h3N h3M ( n  - 1) ?_ (by omega) (by omega) 0 (Or.inl rfl) ?_
      
      all_goals grind

end PottsDiscontinuity.TorusCrossing
