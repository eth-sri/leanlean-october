module

public import Chazelle.Golf

public import Chazelle.Core.OracleCostB
public import Chazelle.Core.OracleCost
public import Chazelle.Cost.Oracle

/-!
# Lemma 3.6 (WP-H), part 27: the query fits its budget

`qcost_le`: the cost of the query (loading, the top test, the chord search, the scan of `D*`,
four locations and cluster scans) is at most `κq (γ^{1/3} (m + 1)^{2/3} + 1)`.  The ingredients:
Lemma 2.3 (`K γ ≤ 60 (2 m + 7)` chords, degree cap `4`), at most `5 (K + 1)` arcs, the book of
`μ ≤ A + 3` nodes with `k` minimal (`OracleQ.scan_le_gen`), and `⌈log₂ x⌉ ≤ 8 x^{2/3}`
(`Chazelle.Cost.clog_le_eight_rpow`) for the binary searches.
-/

namespace Chazelle.Core

namespace OracleR

open OracleQ OracleBook

@[expose] public section

variable {P : Polygon} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain} {N : NF}
  {B : BookData} {k : ℕ}

/-- The chord family has one chord per record. -/
theorem chords_ncard {Q : Polygon} (hN : IsNF (chainModel C) Q N) :
    (N.F (chainModel C) Q).ncard = N.chords.length := by
  classical
  obtain ⟨-, hinj, -⟩ := hN
  have hFn : N.F (chainModel C) Q = (fun i => (N.chord i).toSet (chainModel C) Q) ''
      Set.Iio N.chords.length := by
    ext c; constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
      refine ⟨i, hi, ?_⟩
      show (N.chord i).toSet _ _ = _
      unfold NF.chord; rw [NFLoc.getD_of_lt _ hi]
    · rintro ⟨i, hi, rfl⟩
      refine ⟨N.chord i, ?_, rfl⟩
      unfold NF.chord; rw [NFLoc.getD_of_lt _ hi]; exact List.getElem_mem hi
  rw [hFn, Set.InjOn.ncard_image (s := Set.Iio N.chords.length)
    (f := fun i => (N.chord i).toSet (chainModel C) Q) (fun a ha b hb h => hinj a b ha hb h),
    ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

/-- **Lemma 2.3 for the structure**: `K γ ≤ 60 (2 m + 7)`. -/
theorem QAt.chords_le (h : QAt P m O E V H C N B k) :
    V.K * m (O + 2) ≤ 60 * (2 * V.m + 7) := by
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, h.simple, rfl⟩
  have hM := walkAx_of_goodModel hGM
  have hC := h.canon
  have hF := hC.1.1
  have := hM.lemma23_walk hF.2.1 hF.1 hC.2.1 hC.2.2.1
  rw [chords_ncard hC.1, walk_n] at this
  have hVm : V.m = C.m := by
    obtain ⟨-, -, -, hd2, -⟩ := h.desc; rw [← h.dm, hd2]
  rw [h.hK, hVm]; linarith

/-- The cost constant of the query. -/
def κq : ℕ := 2 * 10 ^ 12

/-- **The query fits its budget.** -/
theorem QAt.qcost_le (h : QAt P m O E V H C N B k) :
    ((100 + (715 * V.L + 700 + dstarCost m V +
      4 * candCost V (NCof (min (m (O + 2)) (2 * V.m + 7))) (8 * k ^ 2) + 500) : ℕ) : ℝ) ≤
      (κq : ℝ) * ((m (O + 2) : ℝ) ^ ((1 : ℝ) / 3) * ((V.m : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1) := by
  have hP := h.simple
  have hC := h.canon
  have hVm : V.m = C.m := by
    obtain ⟨-, -, -, hd2, -⟩ := h.desc; rw [← h.dm, hd2]
  set γ := m (O + 2) with hγdef
  set w := min γ (2 * V.m + 7) with hwdef
  have hγ1 : 1 ≤ γ := gamma_pos hP hC
  have hKγ : V.K * γ ≤ 60 * (2 * V.m + 7) := h.chords_le
  have hK : V.K ≤ 60 * (2 * V.m + 7) := le_trans (Nat.le_mul_of_pos_right _ hγ1) hKγ
  have hA5 : V.A ≤ 5 * (V.K + 1) := by
    have := arcs_le_regions hP hC
    rw [regions_eq hP hC.1] at this
    rw [h.hA, h.hK]; exact this
  have hμ := h.μ_A
  have hL : V.L ≤ Nat.clog 2 (V.A + V.K) + 1 := h.L_le
  have hds : dstarCost m V ≤ 7 * k ^ 2 * (NCof w + 6) + 4 := h.dstarCost_le hP
  have hk1 := h.k_pos
  -- the scans
  have hμγ : V.μ * (γ + 1) ≤ 4200 * (2 * V.m + 1) + 8 * (γ + 1) := by
    have h1 : V.μ ≤ 5 * V.K + 8 := by omega
    have h2 : V.K * (γ + 1) ≤ 2 * (V.K * γ) := by nlinarith
    calc V.μ * (γ + 1) ≤ (5 * V.K + 8) * (γ + 1) := Nat.mul_le_mul_right _ h1
      _ = 5 * (V.K * (γ + 1)) + 8 * (γ + 1) := by ring
      _ ≤ 4200 * (2 * V.m + 1) + 8 * (γ + 1) := by omega
  have hscan := scan_le_gen (c := 4200) (d := 8) (w := w) hγ1 hμγ h.k_min
    (min_le_left _ _) (min_le_right _ _)
  set G := (γ : ℝ) ^ ((1 : ℝ) / 3) * ((V.m : ℝ) + 1) ^ ((2 : ℝ) / 3) with hG
  have hG1 : ((V.m : ℝ) + 1) ^ ((2 : ℝ) / 3) ≤ G := by
    have : (1 : ℝ) ≤ (γ : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.one_le_rpow (by exact_mod_cast hγ1) (by norm_num)
    have h0 : (0 : ℝ) ≤ ((V.m : ℝ) + 1) ^ ((2 : ℝ) / 3) := by positivity
    rw [hG]; nlinarith
  have hG0 : (0 : ℝ) ≤ G := by positivity
  -- the binary searches
  have hAK : V.A + V.K ≤ 2525 * (V.m + 1) := by omega
  have hlog := Chazelle.Cost.clog_le_eight_rpow (V.A + V.K)
  have hpow : ((V.A + V.K : ℕ) : ℝ) ^ ((2 : ℝ) / 3) ≤ 2525 * G := by
    have e1 : ((V.A + V.K : ℕ) : ℝ) ^ ((2 : ℝ) / 3) ≤ ((2525 : ℝ) * ((V.m : ℝ) + 1)) ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hAK) (by norm_num)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at e1
    have e2 : (2525 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2525 := by
      have := Real.rpow_le_rpow_of_exponent_le (x := (2525 : ℝ)) (by norm_num)
        (show (2 : ℝ) / 3 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have e3 : (0 : ℝ) ≤ ((V.m : ℝ) + 1) ^ ((2 : ℝ) / 3) := by positivity
    nlinarith
  have hLR : (V.L : ℝ) ≤ 20200 * G + 1 := by
    have : (V.L : ℝ) ≤ (Nat.clog 2 (V.A + V.K) : ℝ) + 1 := by exact_mod_cast hL
    linarith
  -- the scans in reals
  set X : ℕ := k ^ 2 with hX
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ hk1
  have hscan' : ((w : ℝ) + 1) * (X : ℝ) ≤ 134688 * G := by
    rw [hX]; push_cast; norm_num at hscan ⊢; linarith
  -- the cost in naturals
  have hNC : NCof w = 5660 * w + 62500 := by unfold NCof; ring
  have hcost : 100 + (715 * V.L + 700 + dstarCost m V + 4 * candCost V (NCof w) (8 * X) + 500) ≤
      23424 + 22715 * V.L + 7947142 * ((w + 1) * X) := by
    unfold candCost
    rw [hNC] at hds ⊢
    have hXw : w ≤ w * X := Nat.le_mul_of_pos_right _ hX1
    have e1 : (8 * X + 2) * (5660 * w + 62500 + 80) =
        45280 * (w * X) + 500640 * X + 11320 * w + 125160 := by ring
    have e2 : 7 * X * (5660 * w + 62500 + 6) = 39620 * (w * X) + 437542 * X := by ring
    have e3 : (w + 1) * X = w * X + X := by ring
    rw [e1, e3]; rw [e2] at hds
    omega
  have hcR : ((100 + (715 * V.L + 700 + dstarCost m V + 4 * candCost V (NCof w) (8 * X) + 500) :
      ℕ) : ℝ) ≤ 23424 + 22715 * (V.L : ℝ) + 7947142 * (((w : ℝ) + 1) * (X : ℝ)) := by
    exact_mod_cast hcost
  have hκ : (κq : ℝ) = 2 * 10 ^ 12 := by unfold κq; norm_num
  rw [hκ]
  have hwX : (0 : ℝ) ≤ ((w : ℝ) + 1) * (X : ℝ) := by positivity
  linarith

end

end OracleR

end Chazelle.Core
