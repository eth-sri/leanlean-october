module

public import Chazelle.Cost.Oracle

/-!
# Lemma 3.6 (WP-H), part 2: the query budget of the cluster scan

The query of Lemma 3.6 scans naively the regions of `D*` and of one cluster: with a cluster
decomposition for `k` (`ClusterSpec`: `μ ≤ k³` regions, `|D*| ≤ 7 k²`, clusters of `≤ k²`
regions), at most `8 k²` regions, each at a cost proportional to the number `w + 1` of walk edges
of one of its arcs (`w ≤ γ` by granularity, `w ≤ 2 m + 7` since the walk has `2 m + 7` edges).
Choosing `k` minimal (`(k - 1)³ < μ`) and bounding `μ` by Lemma 2.3 (`K (γ + 1) ≤ c (2 m + 1)`
chords, `μ = K + 1` regions), this file proves that the scan fits the budget
`γ^{1/3} (m + 1)^{2/3}` of `OracleIface.Valid` **as intended** (granularity `γ` and number of
edges `m`; see the report on the query cost term of `OracleIface.Valid`).

## Main result
* `scan_le`: `(w + 1) k² ≤ (32 c + 48) γ^{1/3} (m + 1)^{2/3}`.
-/

namespace Chazelle.Core

public section

namespace OracleQ

/-- `min(g, M) ≤ g^{1/3} M^{2/3}` for nonnegative reals, in the form: a quantity bounded by both
`8 g` and `8 M` is at most `8 g^{1/3} M^{2/3}`. -/
theorem le_of_le_min {x g M : ℝ} (hg : 0 ≤ g) (hM : 0 ≤ M) (hxg : x ≤ 8 * g) (hxM : x ≤ 8 * M) :
    x ≤ 8 * (g ^ ((1 : ℝ) / 3) * M ^ ((2 : ℝ) / 3)) := by
  rcases le_total g M with h | h
  · have e : g = g ^ ((1 : ℝ) / 3) * g ^ ((2 : ℝ) / 3) := by
      rcases hg.lt_or_eq with hg' | hg'
      · rw [← Real.rpow_add hg']; norm_num
      · subst hg'; rw [Real.zero_rpow (by norm_num)]; ring
    have : g ^ ((2 : ℝ) / 3) ≤ M ^ ((2 : ℝ) / 3) := Real.rpow_le_rpow hg h (by norm_num)
    calc x ≤ 8 * g := hxg
      _ = 8 * (g ^ ((1 : ℝ) / 3) * g ^ ((2 : ℝ) / 3)) := by rw [← e]
      _ ≤ 8 * (g ^ ((1 : ℝ) / 3) * M ^ ((2 : ℝ) / 3)) := by gcongr
  · have e : M = M ^ ((1 : ℝ) / 3) * M ^ ((2 : ℝ) / 3) := by
      rcases hM.lt_or_eq with hM' | hM'
      · rw [← Real.rpow_add hM']; norm_num
      · subst hM'; rw [Real.zero_rpow (by norm_num)]; ring
    have : M ^ ((1 : ℝ) / 3) ≤ g ^ ((1 : ℝ) / 3) := Real.rpow_le_rpow hM h (by norm_num)
    calc x ≤ 8 * M := hxM
      _ = 8 * (M ^ ((1 : ℝ) / 3) * M ^ ((2 : ℝ) / 3)) := by rw [← e]
      _ ≤ 8 * (g ^ ((1 : ℝ) / 3) * M ^ ((2 : ℝ) / 3)) := by gcongr

/-- The minimal `k` with `μ ≤ k³` satisfies `k² ≤ 2 μ^{2/3} + 2`. -/
theorem sq_le_of_min {μ k : ℕ} (hk : k = 1 ∨ (k - 1) ^ 3 < μ) :
    ((k : ℝ)) ^ 2 ≤ 2 * (μ : ℝ) ^ ((2 : ℝ) / 3) + 2 := by
  have hμ0 : (0 : ℝ) ≤ μ := Nat.cast_nonneg μ
  have h13 : 0 ≤ (μ : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hμ0 _
  have hsq : ((μ : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (μ : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμ0]; norm_num
  have hk1 : (k : ℝ) ≤ (μ : ℝ) ^ ((1 : ℝ) / 3) + 1 := by
    rcases hk with rfl | hk
    · push_cast; linarith
    · rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0; push_cast; linarith
      · have hc : (((k - 1 : ℕ) : ℝ)) ^ 3 < μ := by exact_mod_cast hk
        have hkm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        have hroot : ((k - 1 : ℕ) : ℝ) ≤ (μ : ℝ) ^ ((1 : ℝ) / 3) := by
          have h0 : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          have e : ((k - 1 : ℕ) : ℝ) = ((((k - 1 : ℕ) : ℝ)) ^ 3) ^ ((1 : ℝ) / 3) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
          rw [e]
          exact Real.rpow_le_rpow (by positivity) hc.le (by norm_num)
        linarith
  calc ((k : ℝ)) ^ 2 ≤ ((μ : ℝ) ^ ((1 : ℝ) / 3) + 1) ^ 2 := by gcongr
    _ ≤ 2 * ((μ : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 + 2 := by nlinarith [sq_nonneg ((μ : ℝ) ^ ((1 : ℝ) / 3) - 1)]
    _ = 2 * (μ : ℝ) ^ ((2 : ℝ) / 3) + 2 := by rw [hsq]

/-- **The query scan fits the budget, general form**: with `μ (γ + 1) ≤ c (2 m + 1) + d (γ + 1)`
(e.g. `μ ≤ 3 K + 4` nodes for `K` chords with `K (γ + 1) ≤ c₀ (2 m + 1)`), scanning `k²` nodes of
cost `w + 1` costs `(w + 1) k² ≤ (32 c + 32 d + 32) γ^{1/3} (m + 1)^{2/3}`. -/
theorem scan_le_gen {c d γ m μ k w : ℕ} (hγ : 1 ≤ γ)
    (hμ : μ * (γ + 1) ≤ c * (2 * m + 1) + d * (γ + 1))
    (hk : k = 1 ∨ (k - 1) ^ 3 < μ) (hwγ : w ≤ γ) (hwm : w ≤ 2 * m + 7) :
    ((w : ℝ) + 1) * (k : ℝ) ^ 2 ≤
      (32 * (c : ℝ) + 32 * d + 32) * ((γ : ℝ) ^ ((1 : ℝ) / 3) * ((m : ℝ) + 1) ^ ((2 : ℝ) / 3)) := by
  set g : ℝ := (γ : ℝ) with hg
  set M : ℝ := (m : ℝ) + 1 with hM
  set A : ℝ := g ^ ((1 : ℝ) / 3) * M ^ ((2 : ℝ) / 3)
  have hg1 : (1 : ℝ) ≤ g := by rw [hg]; exact_mod_cast hγ
  have hA0 : 0 ≤ A := by positivity
  have hwγR : (w : ℝ) ≤ g := by rw [hg]; exact_mod_cast hwγ
  have hwmR : (w : ℝ) ≤ 2 * (m : ℝ) + 7 := by exact_mod_cast hwm
  have hw1 : (w : ℝ) + 1 ≤ 8 * A :=
    le_of_le_min (by linarith) (by linarith) (by linarith) (by rw [hM]; linarith)
  have hμR : (μ : ℝ) * (g + 1) ≤ (c : ℝ) * (2 * (m : ℝ) + 1) + d * (g + 1) := by
    rw [hg]; exact_mod_cast hμ
  have hμ0 : (0 : ℝ) ≤ μ := Nat.cast_nonneg μ
  have hμ23 : 0 ≤ (μ : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hμ0 _
  set e : ℝ := 2 * (c : ℝ) + 2 * d + 1 with he
  have he1 : 1 ≤ e := by rw [he]; linarith
  have hmain : ((w : ℝ) + 1) * (μ : ℝ) ^ ((2 : ℝ) / 3) ≤ 8 * e * A := by
    rcases le_total g M with hgM | hMg
    · have hgpos : 0 < g := by linarith
      have hμb : (μ : ℝ) ≤ e * (M / g) := by
        have h1 : (μ : ℝ) * g ≤ (c : ℝ) * (2 * (m : ℝ) + 1) + d * (g + 1) := by nlinarith
        have h2 : (c : ℝ) * (2 * (m : ℝ) + 1) ≤ 2 * c * M := by rw [hM]; nlinarith
        have h3 : (d : ℝ) * (g + 1) ≤ 2 * d * M := by nlinarith
        rw [mul_div_assoc', le_div_iff₀ hgpos, he]
        nlinarith
      have hpow : (μ : ℝ) ^ ((2 : ℝ) / 3) ≤ (e * (M / g)) ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow hμ0 hμb (by norm_num)
      have hsplit : (e * (M / g)) ^ ((2 : ℝ) / 3) =
          e ^ ((2 : ℝ) / 3) * (M ^ ((2 : ℝ) / 3) / g ^ ((2 : ℝ) / 3)) := by
        rw [Real.mul_rpow (by linarith) (by positivity), Real.div_rpow (by linarith) hgpos.le]
      have hc23 : e ^ ((2 : ℝ) / 3) ≤ e := Real.rpow_le_self_of_one_le he1 (by norm_num)
      have hg23 : 0 < g ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hgpos _
      have hg13 : g / g ^ ((2 : ℝ) / 3) = g ^ ((1 : ℝ) / 3) := by
        rw [div_eq_iff hg23.ne', ← Real.rpow_add hgpos]; norm_num
      have hw2 : (w : ℝ) + 1 ≤ 2 * g := by linarith
      calc ((w : ℝ) + 1) * (μ : ℝ) ^ ((2 : ℝ) / 3)
          ≤ (2 * g) * (e * (M ^ ((2 : ℝ) / 3) / g ^ ((2 : ℝ) / 3))) := by
            apply mul_le_mul hw2 _ hμ23 (by linarith)
            calc (μ : ℝ) ^ ((2 : ℝ) / 3) ≤ _ := hpow
              _ = _ := hsplit
              _ ≤ _ := by gcongr
        _ = 2 * e * ((g / g ^ ((2 : ℝ) / 3)) * M ^ ((2 : ℝ) / 3)) := by ring
        _ = 2 * e * A := by rw [hg13]
        _ ≤ 8 * e * A := by nlinarith
    · have hgpos : 0 < g := by linarith
      have hμb : (μ : ℝ) ≤ e := by
        have h1 : (μ : ℝ) * g ≤ (c : ℝ) * (2 * (m : ℝ) + 1) + d * (g + 1) := by nlinarith
        have h2 : (c : ℝ) * (2 * (m : ℝ) + 1) ≤ 2 * c * g := by
          have : 2 * (m : ℝ) + 1 ≤ 2 * g := by rw [hM] at hMg; linarith
          nlinarith
        have h3 : (d : ℝ) * (g + 1) ≤ 2 * d * g := by nlinarith
        by_contra hcon
        push Not at hcon
        rw [he] at hcon
        nlinarith
      have hμ23b : (μ : ℝ) ^ ((2 : ℝ) / 3) ≤ e := by
        rcases le_total (μ : ℝ) 1 with h1 | h1
        · have := Real.rpow_le_one hμ0 h1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
          linarith
        · have := Real.rpow_le_self_of_one_le h1 (by norm_num : (2 : ℝ) / 3 ≤ 1)
          linarith
      calc ((w : ℝ) + 1) * (μ : ℝ) ^ ((2 : ℝ) / 3) ≤ (8 * A) * e :=
            mul_le_mul hw1 hμ23b hμ23 (by positivity)
        _ = 8 * e * A := by ring
  have hk2 := sq_le_of_min hk
  calc ((w : ℝ) + 1) * (k : ℝ) ^ 2 ≤ ((w : ℝ) + 1) * (2 * (μ : ℝ) ^ ((2 : ℝ) / 3) + 2) :=
        mul_le_mul_of_nonneg_left hk2 (by linarith)
    _ = 2 * (((w : ℝ) + 1) * (μ : ℝ) ^ ((2 : ℝ) / 3)) + 2 * ((w : ℝ) + 1) := by ring
    _ ≤ 2 * (8 * e * A) + 2 * (8 * A) := by gcongr
    _ = (32 * (c : ℝ) + 32 * d + 32) * A := by rw [he]; ring

end OracleQ

end

end Chazelle.Core
