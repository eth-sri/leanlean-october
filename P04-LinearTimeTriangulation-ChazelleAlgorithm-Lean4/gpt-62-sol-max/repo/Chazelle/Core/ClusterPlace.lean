module

public import Chazelle.Core.ClusterStageD1

/-!
# WP-I, part 54: the placement of the items (combinatorics)

The items `v < μ` with `bo v < μ` (the block of `v`; `bo v = μ` for the light ones) are placed
block after block, and inside a block by increasing key `key v` (injective). The final position
of `v` is `plPos v = start (bo v) + rk v`, where `start b = cntLt bo μ b` and the rank `rk v` is
the number of items of the block of `v` of smaller key. After `j` steps of the scan by key, the
block `b` holds `cB j b` items.
-/

namespace Chazelle.Core.Cluster

open Machine

@[expose] public section

/-- The items of the block `b` of key `< j`. -/
noncomputable def cB (μ : ℕ) (bo key : ℕ → ℕ) (j b : ℕ) : ℕ :=
  ((Finset.range μ).filter (fun w => bo w = b ∧ key w < j)).card

/-- The rank of `v` in its block. -/
noncomputable def rk (μ : ℕ) (bo key : ℕ → ℕ) (v : ℕ) : ℕ :=
  ((Finset.range μ).filter (fun w => bo w = bo v ∧ key w < key v)).card

/-- The final position of an item. -/
noncomputable def plPos (μ : ℕ) (bo key : ℕ → ℕ) (v : ℕ) : ℕ := cntLt bo μ (bo v) + rk μ bo key v

theorem cntLt_succ (f : ℕ → ℕ) (n b : ℕ) : cntLt f n (b + 1) = cntLt f n b + cntBelow f n b := by
  rw [← sum_cntBelow, ← sum_cntBelow, Finset.sum_range_succ]

theorem cntLt_mono (f : ℕ → ℕ) (n : ℕ) {b b' : ℕ} (h : b ≤ b') : cntLt f n b ≤ cntLt f n b' := by
  unfold cntLt; apply Finset.card_le_card; intro v hv
  simp only [Finset.mem_filter] at hv ⊢; exact ⟨hv.1, by omega⟩

variable {μ : ℕ} {bo key : ℕ → ℕ}

theorem rk_lt {v : ℕ} (hv : v < μ) : rk μ bo key v < cntBelow bo μ (bo v) := by
  unfold rk cntBelow
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (fun w hw => by
    simp only [Finset.mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.1⟩)]
  exact ⟨v, by simp [hv], by simp⟩

theorem rk_lt_rk {v w : ℕ} (hw : w < μ) (hb : bo w = bo v) (hk : key w < key v) :
    rk μ bo key w < rk μ bo key v := by
  unfold rk
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by rw [hx.2.1, hb], by omega⟩)]
  exact ⟨w, by simp [hw, hb, hk], by simp⟩

theorem rk_eq_cB {v : ℕ} : rk μ bo key v = cB μ bo key (key v) (bo v) := rfl

theorem plPos_ge (v : ℕ) : cntLt bo μ (bo v) ≤ plPos μ bo key v := Nat.le_add_right _ _

theorem plPos_lt {v : ℕ} (hv : v < μ) : plPos μ bo key v < cntLt bo μ (bo v + 1) := by
  have := rk_lt (bo := bo) (key := key) hv; unfold plPos; rw [cntLt_succ]; omega

/-- **The positions are distinct.** -/
theorem plPos_inj (hinj : ∀ v w, v < μ → w < μ → key v = key w → v = w) {v w : ℕ} (hv : v < μ)
    (hw : w < μ) (h : plPos μ bo key v = plPos μ bo key w) : v = w := by
  rcases lt_trichotomy (bo v) (bo w) with hb | hb | hb
  · have h1 := plPos_lt (bo := bo) (key := key) hv; have h2 := plPos_ge (μ := μ) (bo := bo) (key := key) w
    have h3 := cntLt_mono bo μ (show bo v + 1 ≤ bo w by omega); omega
  · rcases lt_trichotomy (key v) (key w) with hk | hk | hk
    · have := rk_lt_rk (bo := bo) (key := key) hv hb hk; unfold plPos at h; rw [hb] at h; omega
    · exact hinj v w hv hw hk
    · have := rk_lt_rk (bo := bo) (key := key) hw hb.symm hk; unfold plPos at h; rw [hb] at h; omega
  · have h1 := plPos_lt (bo := bo) (key := key) hw; have h2 := plPos_ge (μ := μ) (bo := bo) (key := key) v
    have h3 := cntLt_mono bo μ (show bo w + 1 ≤ bo v by omega); omega

/-- **The positions are in key order** inside a block. -/
theorem key_le_of_plPos {v w : ℕ} (hw : w < μ) (hb : bo w = bo v)
    (h : plPos μ bo key v ≤ plPos μ bo key w) : key v ≤ key w := by
  by_contra hk
  have := rk_lt_rk (bo := bo) (key := key) hw hb (by omega); unfold plPos at h; rw [hb] at h; omega

/-- **The block `b` fills its segment.** -/
theorem exists_plPos (hinj : ∀ v w, v < μ → w < μ → key v = key w → v = w) {b i : ℕ}
    (h1 : cntLt bo μ b ≤ i) (h2 : i < cntLt bo μ (b + 1)) :
    ∃ v, v < μ ∧ bo v = b ∧ plPos μ bo key v = i := by
  set T := (Finset.range μ).filter (fun v => bo v = b) with hT
  have hsub : T.image (plPos μ bo key) ⊆ Finset.Ico (cntLt bo μ b) (cntLt bo μ (b + 1)) := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    simp only [hT, Finset.mem_filter, Finset.mem_range] at hv
    have := plPos_lt (bo := bo) (key := key) hv.1; have := plPos_ge (μ := μ) (bo := bo) (key := key) v
    rw [hv.2] at *; simp only [Finset.mem_Ico]; omega
  have hcard : (T.image (plPos μ bo key)).card = cntBelow bo μ b := by
    rw [Finset.card_image_of_injOn (fun v hv w hw h => by
      simp only [hT, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hv hw
      exact plPos_inj hinj hv.1 hw.1 h)]
    rfl
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Nat.card_Ico, cntLt_succ]; omega)
  have hi : i ∈ Finset.Ico (cntLt bo μ b) (cntLt bo μ (b + 1)) := by simp [h1, h2]
  rw [← heq] at hi
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
  simp only [hT, Finset.mem_filter, Finset.mem_range] at hv
  exact ⟨v, hv.1, hv.2, rfl⟩

/-- One step of the scan: the item of key `j`. -/
theorem cB_succ_of (hinj : ∀ v w, v < μ → w < μ → key v = key w → v = w) {v j b : ℕ}
    (hv : v < μ) (hk : key v = j) :
    cB μ bo key (j + 1) b = cB μ bo key j b + if bo v = b then 1 else 0 := by
  unfold cB
  split_ifs with hb
  · rw [← Finset.card_insert_of_notMem (s := (Finset.range μ).filter _) (a := v) (by simp; omega)]
    apply congrArg Finset.card; ext w; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases Nat.lt_or_ge (key w) j with h | h
      · exact Or.inr ⟨h1, h2, h⟩
      · exact Or.inl (hinj w v h1 hv (by omega))
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · exact ⟨hv, hb, by omega⟩
      · exact ⟨h1, h2, by omega⟩
  · refine (congrArg Finset.card ?_).trans (Nat.add_zero _).symm; ext w; simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases Nat.lt_or_ge (key w) j with h | h
      · exact ⟨h1, h2, h⟩
      · have := hinj w v h1 hv (by omega); subst this; exact absurd h2 hb
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by omega⟩

/-- One step of the scan without an item of block `b`. -/
theorem cB_succ_none {j b : ℕ} (h : ∀ w, w < μ → key w = j → bo w ≠ b) :
    cB μ bo key (j + 1) b = cB μ bo key j b := by
  unfold cB; apply congrArg Finset.card; ext w; simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases Nat.lt_or_ge (key w) j with h' | h'
    · exact ⟨h1, h2, h'⟩
    · exact absurd h2 (h w h1 (by omega))
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by omega⟩

theorem cB_full {n b : ℕ} (h : ∀ w, w < μ → key w < n) : cB μ bo key n b = cntBelow bo μ b := by
  unfold cB cntBelow; apply congrArg Finset.card; ext w; simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, h w h1⟩

theorem plPos_lt_μ {v : ℕ} (hv : v < μ) (_hb : bo v < μ) : plPos μ bo key v < μ := by
  have := plPos_lt (bo := bo) (key := key) hv; have := cntLt_le bo μ (bo v + 1); omega

/-- **The invariant of the placement scan** (counters at `a1`, items at `a2`, positions at
`a3`; `m0` the memory before the scan). -/
structure PlInv (μ : ℕ) (bo key : ℕ → ℕ) (a1 a2 a3 : ℕ) (m0 : ℕ → ℕ) (j : ℕ) (m : ℕ → ℕ) :
    Prop where
  cnt : ∀ b, b < μ → m (a1 + b) = cntLt bo μ b + cB μ bo key j b
  pos : ∀ v, v < μ → m (a3 + v) = if bo v < μ ∧ key v < j then plPos μ bo key v else m0 (a3 + v)
  act : ∀ v, v < μ → bo v < μ → key v < j → m (a2 + plPos μ bo key v) = v

theorem PlInv.zero {a1 a2 a3 : ℕ} {m : ℕ → ℕ} (h : ∀ b, b < μ → m (a1 + b) = cntLt bo μ b) :
    PlInv μ bo key a1 a2 a3 m 0 m :=
  ⟨fun b hb => by rw [h b hb]; simp [cB], fun v _ => by simp, fun v _ _ h => by omega⟩

/-- **A placing step.** -/
theorem PlInv.step (hinj : ∀ v w, v < μ → w < μ → key v = key w → v = w) {a1 a2 a3 : ℕ}
    (h12 : a1 + μ ≤ a2) (h23 : a2 + μ ≤ a3) {m0 m : ℕ → ℕ} {j : ℕ}
    (hI : PlInv μ bo key a1 a2 a3 m0 j m) {v : ℕ} (hv : v < μ) (hk : key v = j) (hb : bo v < μ) :
    PlInv μ bo key a1 a2 a3 m0 (j + 1) (upd (upd (upd m (a2 + plPos μ bo key v) v) (a3 + v)
      (plPos μ bo key v)) (a1 + bo v) (plPos μ bo key v + 1)) := by
  have hq := plPos_lt_μ (key := key) hv hb
  have hqe : plPos μ bo key v = cntLt bo μ (bo v) + cB μ bo key j (bo v) := by
    unfold plPos; rw [rk_eq_cB, hk]
  refine ⟨fun b hb' => ?_, fun w hw => ?_, fun w hw hbw hkw => ?_⟩
  · rw [cB_succ_of hinj hv hk]
    by_cases hbb : bo v = b
    · subst hbb; rw [Machine.upd_same, ite_eq_left rfl, hqe]; omega
    · rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega), hI.cnt b hb', ite_eq_right hbb, Nat.add_zero]
  · rw [Machine.upd_other _ _ _ (by omega)]
    by_cases hwv : w = v
    · subst hwv; rw [Machine.upd_same, ite_eq_left ⟨hb, by omega⟩]
    · rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega), hI.pos w hw]
      have : key w ≠ j := fun h => hwv (hinj w v hw hv (by omega))
      by_cases hc : bo w < μ ∧ key w < j
      · rw [ite_eq_left hc, ite_eq_left ⟨hc.1, by omega⟩]
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨h.1, by omega⟩)]
  · have hqw := plPos_lt_μ (key := key) hw hbw
    rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]
    by_cases hwv : w = v
    · subst hwv; rw [Machine.upd_same]
    · have hne : plPos μ bo key w ≠ plPos μ bo key v := fun h => hwv (plPos_inj hinj hw hv h)
      rw [Machine.upd_other _ _ _ (by omega)]
      exact hI.act w hw hbw (by
        have : key w ≠ j := fun h => hwv (hinj w v hw hv (by omega))
        omega)

/-- **A step without placement.** -/
theorem PlInv.skip {a1 a2 a3 : ℕ} {m0 m : ℕ → ℕ} {j : ℕ}
    (hI : PlInv μ bo key a1 a2 a3 m0 j m) (hn : ∀ w, w < μ → key w = j → ¬ bo w < μ) :
    PlInv μ bo key a1 a2 a3 m0 (j + 1) m := by
  refine ⟨fun b hb => ?_, fun w hw => ?_, fun w hw hbw hkw => ?_⟩
  · rw [cB_succ_none (fun w hw hk h => hn w hw hk (by omega))]; exact hI.cnt b hb
  · rw [hI.pos w hw]
    by_cases hc : bo w < μ ∧ key w < j
    · rw [ite_eq_left hc, ite_eq_left ⟨hc.1, by omega⟩]
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨h.1, by
        rcases Nat.lt_or_ge (key w) j with h' | h'
        · exact h'
        · exact absurd h.1 (hn w hw (by omega))⟩)]
  · exact hI.act w hw hbw (by
      rcases Nat.lt_or_ge (key w) j with h' | h'
      · exact h'
      · exact absurd hbw (hn w hw (by omega)))

/-- The end of the scan. -/
theorem PlInv.full {a1 a2 a3 : ℕ} {m0 m : ℕ → ℕ} {n : ℕ}
    (hI : PlInv μ bo key a1 a2 a3 m0 n m) (h : ∀ w, w < μ → key w < n) {b : ℕ} (hb : b < μ) :
    m (a1 + b) = cntLt bo μ (b + 1) := by
  rw [hI.cnt b hb, cB_full h, cntLt_succ]

end

end Chazelle.Core.Cluster
