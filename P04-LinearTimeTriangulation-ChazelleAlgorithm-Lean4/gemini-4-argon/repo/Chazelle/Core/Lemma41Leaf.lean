module

public import Chazelle.Core.Lemma41Pro

/-!
# WP-J, part 24: the leaves of the merge tree

The leaves are the pieces of the greedy cover, in shape `(start, 2^g, γ'_g)` (`leafShp`): they are
consecutive, start at `a`, have total length `b - a` and there are at least two of them when
`2^(λ-1) < b - a` (`leafShp_consec`, `leafShp_first`, `leafShp_sum`, `two_le_cover`).
`leaves_levelAt`: the records written by the cover loop, their level array and the whole host
form a level of nodes (`LevelAt`), from the grade table.
-/

namespace Chazelle.Core.L41

open Machine Chazelle

@[expose] public section

/-- The shapes of the leaves. -/
noncomputable def leafShp (lam b a : ℕ) : List Shp :=
  (cover lam b a).map fun q => (q.2, 2 ^ q.1, gradeGran q.1)

theorem nd_map_of_lt {l : List (ℕ × ℕ)} {f : ℕ × ℕ → Shp} {k : ℕ} (hk : k < l.length) :
    nd (l.map f) k = f (l.getD k (0, 0)) := by
  unfold nd
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk,
    List.getElem_map]

theorem cover_getD_zero {lam b x : ℕ} (h : x < b) : ((cover lam b x).getD 0 (0, 0)).2 = x := by
  rw [cover_of_lt h]; rfl

theorem cover_getD_succ {lam b : ℕ} (x : ℕ) : ∀ k, k + 1 < (cover lam b x).length →
    ((cover lam b x).getD (k + 1) (0, 0)).2 =
      ((cover lam b x).getD k (0, 0)).2 + 2 ^ ((cover lam b x).getD k (0, 0)).1 := by
  induction x using cover_ind (b := b) with
  | h x ih =>
    intro k hk
    by_cases hx : x < b
    · rw [cover_of_lt hx] at hk ⊢
      rcases k with _ | k
      · have hx' : x + 2 ^ nextG lam b x < b := by
          by_contra hc
          rw [cover_of_ge (by omega)] at hk; simp at hk
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        exact cover_getD_zero hx'
      · simp only [List.getD_cons_succ]
        simp only [List.length_cons] at hk
        exact ih _ (step_lt hx) k (by omega)
    · rw [cover_of_ge (by omega)] at hk; simp at hk

theorem leafShp_length (lam b a : ℕ) : (leafShp lam b a).length = (cover lam b a).length := by
  simp [leafShp]

theorem leafShp_consec (lam b a : ℕ) : Consec (leafShp lam b a) := by
  intro k hk
  rw [leafShp_length] at hk
  unfold leafShp
  rw [nd_map_of_lt hk, nd_map_of_lt (by omega)]
  exact cover_getD_succ a k hk

theorem leafShp_first {lam b a : ℕ} (h : a < b) : (nd (leafShp lam b a) 0).1 = a := by
  have hl : 0 < (cover lam b a).length := by rw [cover_of_lt h]; simp
  unfold leafShp
  rw [nd_map_of_lt hl]
  exact cover_getD_zero h

theorem leafShp_sum (lam b a : ℕ) :
    ((leafShp lam b a).map fun x => x.2.1).sum = b - a := by
  rw [← cover_sum (lam := lam) (b := b) a, leafShp, List.map_map]; rfl

/-- **At least two leaves.** -/
theorem two_le_cover {lam b a : ℕ} (_hl : 1 ≤ lam) (h : 2 ^ (lam - 1) < b - a) :
    2 ≤ (cover lam b a).length := by
  by_contra hc
  have hab : a < b := by have := Nat.one_le_two_pow (n := lam - 1); omega
  have hsum := cover_sum (lam := lam) (b := b) a
  rw [cover_of_lt hab] at hsum hc
  simp only [List.length_cons] at hc
  have h0 : (cover lam b (a + 2 ^ nextG lam b a)).length = 0 := by omega
  rw [List.length_eq_zero_iff] at h0
  rw [h0] at hsum
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsum
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (nextG_le lam b a)
  omega

/-- The leaves' granularities are at most `γ'_{λ-1}` and at least `1`. -/
theorem leafShp_gran {lam b a : ℕ} : ∀ k, k < (leafShp lam b a).length →
    (nd (leafShp lam b a) k).2.2 ≤ gradeGran (lam - 1) ∧ 1 ≤ (nd (leafShp lam b a) k).2.2 := by
  intro k hk
  rw [leafShp_length] at hk
  unfold leafShp
  rw [nd_map_of_lt hk]
  have hq := mem_cover (lam := lam) (b := b) a ((cover lam b a).getD k (0, 0)) (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)
  refine ⟨gradeGran_mono hq.1, ?_⟩
  exact le_trans (Nat.one_le_two_pow) (two_pow_ceilBeta_le_gradeGran _)

set_option maxHeartbeats 8000000 in
/-- **The leaves form a level.** -/
theorem leaves_levelAt {O : OracleIface} {P : Polygon} {m0 m5 m6 m8 : ℕ → ℕ}
    {A h lam a b : ℕ} (hR : Robust A m0 fun m' => GradeRaw O P m' h A) (hn : 2 ≤ P.n)
    (hlΛ : lam ≤ m0 h) (hl : 1 ≤ lam) (_hab : a < b) (hbn : b + 1 ≤ P.n)
    (h5 : ∀ x, x < A → m5 x = m0 x) (hhost : HostAt m5 A (Host.whole P.n))
    (h6rec : ∀ k, k < (cover lam b a).length →
      RecAt m6 m5 (A + 7) A (m0 (h + 2)) ((cover lam b a).getD k (0, 0)) k)
    (h65 : ∀ x, x < A + 7 → m6 x = m5 x)
    (h8ent : ∀ k, k < (cover lam b a).length →
      m8 (A + 7 + 6 * (cover lam b a).length + 2 * k) = A + 7 + 6 * k ∧
      m8 (A + 7 + 6 * (cover lam b a).length + 2 * k + 1) = m6 (A + 7 + 6 * k + 5))
    (h86 : ∀ x, x < A + 7 + 6 * (cover lam b a).length → m8 x = m6 x) :
    LevelAt P m8 (A + 7 + 8 * (cover lam b a).length) (A + 7 + 6 * (cover lam b a).length) A
      (leafShp lam b a) := by
  set j := (cover lam b a).length
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hΛ : 1 ≤ m0 h := by omega
  obtain ⟨-, -, -, -, -, -, hent⟩ := tab_lt hR hn hΛ
  have hG := hR.holds
  intro k hk
  rw [leafShp_length] at hk
  unfold leafShp
  rw [nd_map_of_lt hk]
  have hmem0 : (cover lam b a).getD k (0, 0) ∈ cover lam b a := by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  set q := (cover lam b a).getD k (0, 0) with hq
  have hmem := mem_cover (lam := lam) (b := b) a q hmem0
  obtain ⟨hg, hdvd, hax, hxb⟩ := hmem
  set g := q.1
  set x := q.2
  obtain ⟨i, hi⟩ := hdvd
  have hpos : 0 < 2 ^ g := by positivity
  have hxi : x / 2 ^ g = i := by rw [hi, Nat.mul_div_cancel_left _ hpos]
  have hgΛ : g < m0 h := by omega
  have hic : i < gradeCount P.n g := by
    unfold gradeCount
    have : i * 2 ^ g ≤ P.n - 2 := by
      have := Nat.one_le_two_pow (n := g); rw [hi] at hxb; rw [mul_comm]; omega
    have := (Nat.le_div_iff_mul_le hpos).mpr this
    omega
  obtain ⟨H, C, N, hd, hwf, hCP, -, -, hCs, hCm, hN, hc, -⟩ := hG.2.2.2 g i hgΛ hic
  obtain ⟨hT, hO, -, -⟩ := hent g i hgΛ hic
  have hCs' : C.s = x := by rw [hCs]; unfold gradeStart; rw [hi]; ring
  have hCm' : C.m = 2 ^ g := by
    rw [hCm]; unfold gradeLen
    have : x + 2 ^ g ≤ P.n - 1 := by omega
    rw [hi] at this
    apply min_eq_left; rw [mul_comm]; omega
  set R := m0 (m0 (h + 2) + g)
  set B := m0 (R + 3 * i)
  have hB5 : B + 5 ≤ A := hwf.1
  have hR3 : R + 3 * i + 1 < A := by omega
  -- the record, read in `m0`
  obtain ⟨r0, rj, r5⟩ := h6rec k hk
  rw [← hq, hxi] at rj r5
  have e5 : m5 (m0 (h + 2) + g) = R := h5 _ hT
  have eR : m5 (R + 3 * i) = B := h5 _ (by omega)
  have eF : m5 (R + 3 * i + 1) = m0 (R + 3 * i + 1) := h5 _ hR3
  have hwords : ∀ t, 1 ≤ t → t ≤ 4 → m8 (A + 7 + 6 * k + t) = m0 (B + t) := fun t t1 t4 => by
    rw [h86 _ (by omega), rj t t1 t4, e5, eR, h5 _ (by omega)]
  have hd0 : m8 (A + 7 + 6 * k) = A := by rw [h86 _ (by omega), r0]
  have hf : m8 (A + 7 + 6 * j + 2 * k + 1) = m0 (R + 3 * i + 1) := by
    rw [(h8ent k hk).2, r5, e5, eF]
  have h8m0 : ∀ y, y < A → m8 y = m0 y := fun y hy => by
    rw [h86 _ (by omega), h65 _ (by omega), h5 _ hy]
  refine ⟨C, hCs', hCm', ?_⟩
  rw [(h8ent k hk).1, hf]
  obtain ⟨-, -, d1, d2, d3, d4⟩ := hd
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hCP, hd0, by omega, by omega, by omega, N,
    (hN.transport h8m0).mono (by omega), hc⟩
  · rw [hd0]
    exact hostAt_agree (A := A + 7) hhost rfl (by omega) fun y hy => by
      rw [h86 _ (by omega), h65 _ (by omega)]
  · rw [hCP]; have := poly_whole (Qof P) (by omega); rw [hQn] at this; exact this.symm
  · rwa [hwords 1 le_rfl (by norm_num)]
  · rwa [hwords 2 (by norm_num) (by norm_num)]
  · rwa [hwords 3 (by norm_num) (by norm_num)]
  · rwa [hwords 4 (by norm_num) le_rfl]

end

end Chazelle.Core.L41
