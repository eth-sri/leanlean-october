module

public import Chazelle.Core.ClusterStageD4
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics

/-!
# WP-I, part 57: the initial invariant of the work stack

After the placement, the block `b < μ` occupies the segment `seg b = (cntLt b, cntLt (b + 1))`;
the large blocks are on the stack `segL`, the others are finished (`finL`). With no separator
vertex yet, this is an `SInv` state (`SInv.init`).
-/

namespace Chazelle.Core.Cluster

open Machine

@[expose] public section

/-- The segment of the block `b`. -/
noncomputable def seg (μ : ℕ) (bo : ℕ → ℕ) (b : ℕ) : ℕ × ℕ := (cntLt bo μ b, cntLt bo μ (b + 1))

/-- The finished (small) blocks. -/
noncomputable def finL (s μ : ℕ) (bo : ℕ → ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range μ).filter (fun b => cntBelow bo μ b ≤ s)).image (seg μ bo)

variable {s μ : ℕ} {bo : ℕ → ℕ}

theorem len_seg (b : ℕ) : len (seg μ bo b) = cntBelow bo μ b := by
  uro len seg [cntLt_succ]

theorem mem_segL {j : ℕ} {p : ℕ × ℕ} :
    p ∈ segL s μ bo j ↔ ∃ b, b < j ∧ s < cntBelow bo μ b ∧ p = seg μ bo b := by
  induction j with
  | zero => simp [segL]
  | succ j ih =>
    simp only [segL, List.mem_append, ih, optSeg]
    constructor
    · rintro (h | ⟨b, h1, h2, h3⟩)
      · split_ifs at h with hs
        · simp only [List.mem_singleton] at h
          exact ⟨j, by omega, by rwo [cntLt_succ] at hs, h⟩
        · simp at h
      · exact ⟨b, by omega, h2, h3⟩
    · rintro ⟨b, h1, h2, h3⟩
      rcases Nat.lt_or_ge b j with h | h
      · exact Or.inr ⟨b, h, h2, h3⟩
      · have hb : b = j := by omega
        subst hb
        left; rw [ite_eq_left (by rwo [cntLt_succ])]; simp [h3, seg]

theorem mem_finL {p : ℕ × ℕ} :
    p ∈ finL s μ bo ↔ ∃ b, b < μ ∧ cntBelow bo μ b ≤ s ∧ p = seg μ bo b := by
  unfold finL
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨b, ⟨h1, h2⟩, h3⟩; exact ⟨b, h1, h2, h3.symm⟩
  · rintro ⟨b, h1, h2, h3⟩; exact ⟨b, ⟨h1, h2⟩, h3.symm⟩

theorem lv_iff {p : ℕ × ℕ} :
    Lv (segL s μ bo μ) (finL s μ bo) p ↔ ∃ b, b < μ ∧ p = seg μ bo b := by
  unfold Lv; rw [mem_segL, mem_finL]
  constructor
  · rintro (⟨b, h1, -, h3⟩ | ⟨b, h1, -, h3⟩) <;> exact ⟨b, h1, h3⟩
  · rintro ⟨b, h1, h3⟩
    rcases Nat.lt_or_ge s (cntBelow bo μ b) with h | h
    · exact Or.inl ⟨b, h1, h, h3⟩
    · exact Or.inr ⟨b, h1, h, h3⟩

theorem seg_disj {b b' : ℕ} (h : b < b') : (seg μ bo b).2 ≤ (seg μ bo b').1 :=
  cntLt_mono bo μ (by omega)

theorem segL_nodup (j : ℕ) : (segL s μ bo j).Nodup := by
  induction j with
  | zero => simp [segL]
  | succ j ih =>
    simp only [segL, optSeg]
    split_ifs with hs
    · refine List.nodup_cons.mpr ⟨fun hm => ?_, ih⟩
      obtain ⟨b, h1, h2, h3⟩ := mem_segL.mp hm
      have := seg_disj (μ := μ) (bo := bo) h1
      rw [← h3] at this; sio only [seg] at this
    · simpa using ih

/-- The potential of the initial stack. -/
theorem sum_segL (j : ℕ) :
    ∑ p ∈ (segL s μ bo j).toFinset, (2 * len p - s) ≤ 2 * cntLt bo μ j := by
  induction j with
  | zero => simp [segL, cntLt]
  | succ j ih =>
    rw [cntLt_succ]
    simp only [segL, optSeg]
    split_ifs with hs
    · have hn := segL_nodup (s := s) (μ := μ) (bo := bo) (j + 1)
      simp only [segL, optSeg, ite_eq_left hs] at hn
      rw [List.singleton_append, List.toFinset_cons, Finset.sum_insert (by
        rw [List.mem_toFinset]; exact (List.nodup_cons.mp hn).1)]
      have : len (cntLt bo μ j, cntLt bo μ (j + 1)) = cntBelow bo μ j := len_seg j
      rwo [this]
    · sio only [List.nil_append]

/-- The items of a block segment. -/
theorem items_seg {key act : ℕ → ℕ} (hinj : ∀ v w, v < μ → w < μ → key v = key w → v = w)
    (hact : ∀ v, v < μ → bo v < μ → act (plPos μ bo key v) = v) {b : ℕ} (hb : b < μ) :
    items act (seg μ bo b) = (Finset.range μ).filter (fun v => bo v = b) := by
  ext v
  rw [mem_items]; simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨i, h1, h2, rfl⟩
    obtain ⟨w, hw, hbw, rfl⟩ := exists_plPos (key := key) hinj h1 h2
    rw [hact w hw (by omega)]; exact ⟨hw, hbw⟩
  · rintro ⟨hv, hbv⟩
    refine ⟨plPos μ bo key v, ?_, ?_, hact v hv (by omega)⟩
    · have := plPos_ge (μ := μ) (bo := bo) (key := key) v; rw [hbv] at this; exact this
    · have := plPos_lt (μ := μ) (bo := bo) (key := key) hv; rw [hbv] at this; exact this

theorem inj_seg {key act : ℕ → ℕ} (hinj : ∀ v w, v < μ → w < μ → key v = key w → v = w)
    (hact : ∀ v, v < μ → bo v < μ → act (plPos μ bo key v) = v) {b : ℕ} (hb : b < μ) :
    Set.InjOn act (Finset.Ico (seg μ bo b).1 (seg μ bo b).2) := by
  intro i hi i' hi' h
  simp only [Finset.coe_Ico, Set.mem_Ico] at hi hi'
  obtain ⟨w, hw, hbw, rfl⟩ := exists_plPos (key := key) hinj hi.1 hi.2
  obtain ⟨w', hw', hbw', rfl⟩ := exists_plPos (key := key) hinj hi'.1 hi'.2
  rw [hact w hw (by omega), hact w' hw' (by omega)] at h
  rw [h]

/-- **The initial state of the work stack.** -/
theorem SInv.init {k : ℕ} {H : Finset ℕ} {slab : ℕ → ℕ} {Adj : ℕ → ℕ → Prop} {key act : ℕ → ℕ}
    (hinj : ∀ v w, v < μ → w < μ → key v = key w → v = w)
    (hact : ∀ v, v < μ → bo v < μ → act (plPos μ bo key v) = v)
    (hH : ∀ v, v < μ → (v ∈ H ↔ ¬ bo v < μ)) (_hHμ : ∀ v ∈ H, v < μ)
    (hslab : ∀ v w, v < μ → w < μ → bo v < μ → bo v = bo w → slab v = slab w)
    (hedge : ∀ x y, Adj x y → x ∉ H → y ∉ H → x < μ ∧ y < μ ∧ bo x = bo y) :
    SInv μ k s H slab Adj act (segL s μ bo μ) (finL s μ bo) ∅ 0 := by
  have hit : ∀ p, Lv (segL s μ bo μ) (finL s μ bo) p → ∃ b, b < μ ∧ p = seg μ bo b ∧
      items act p = (Finset.range μ).filter (fun v => bo v = b) := fun p hp => by
    obtain ⟨b, hb, rfl⟩ := lv_iff.mp hp
    exact ⟨b, hb, rfl, items_seg hinj hact hb⟩
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp v hv => ?_, segL_nodup μ, fun p hp hf => ?_,
    fun p q hp hq hpq => ?_, fun p q hp hq hpq => ?_, fun p hp => ?_, fun p hp => ?_,
    fun v hv hvH _ => ?_, fun p hp v hv => ?_, fun p hp v hv w hw => ?_,
    fun x y hxy hx _ hy _ => ?_, by simp, ?_, ?_⟩
  · obtain ⟨b, hb, rfl⟩ := lv_iff.mp hp; exact cntLt_mono bo μ (by omega)
  · obtain ⟨b, hb, rfl⟩ := lv_iff.mp hp; exact inj_seg hinj hact hb
  · obtain ⟨b, hb, rfl, hi⟩ := hit p hp; rw [hi] at hv; simp at hv; exact hv.1
  · obtain ⟨b, -, h2, rfl⟩ := mem_segL.mp hp
    obtain ⟨b', -, h2', h3'⟩ := mem_finL.mp hf
    have := congrArg len h3'; rwo [len_seg, len_seg] at this
  · obtain ⟨b, hb, rfl⟩ := lv_iff.mp hp; obtain ⟨b', hb', rfl⟩ := lv_iff.mp hq
    unfold RDisj
    rcases lt_trichotomy b b' with h | h | h
    · exact Or.inl (seg_disj h)
    · exact absurd (by rw [h]) hpq
    · exact Or.inr (Or.inl (seg_disj h))
  · obtain ⟨b, hb, rfl, hi⟩ := hit p hp; obtain ⟨b', hb', rfl, hi'⟩ := hit q hq
    rw [hi, hi', Finset.disjoint_left]
    intro v h1 h2; simp only [Finset.mem_filter] at h1 h2
    exact hpq (by rw [← h1.2, ← h2.2])
  · obtain ⟨b, -, h2, rfl⟩ := mem_segL.mp hp; rwx [len_seg]
  · obtain ⟨b, -, h2, rfl⟩ := mem_finL.mp hp; rwx [len_seg]
  · have hb : bo v < μ := by by_contra h; exact hvH ((hH v hv).mpr h)
    refine ⟨seg μ bo (bo v), lv_iff.mpr ⟨bo v, hb, rfl⟩, ?_⟩
    rw [items_seg hinj hact hb]; simp [hv]
  · obtain ⟨b, hb, rfl, hi⟩ := hit p hp; rw [hi] at hv; simp only [Finset.mem_filter,
      Finset.mem_range] at hv
    exact ⟨by simp, fun h => ((hH v hv.1).mp h) (by omega)⟩
  · obtain ⟨b, hb, rfl, hi⟩ := hit p hp; rw [hi] at hv hw
    simp only [Finset.mem_filter, Finset.mem_range] at hv hw
    exact hslab v w hv.1 hw.1 (by omega) (by omega)
  · obtain ⟨hxμ, hyμ, hb⟩ := hedge x y hxy hx hy
    have hbx : bo x < μ := by by_contra h; exact hx ((hH x hxμ).mpr h)
    refine ⟨seg μ bo (bo x), lv_iff.mpr ⟨bo x, hbx, rfl⟩, ?_, ?_⟩ <;>
      rw [items_seg hinj hact hbx] <;> simp [hxμ, hyμ, hb]
  · have h1 := sum_segL (s := s) (μ := μ) (bo := bo) μ
    have h2 := cntLt_le bo μ μ
    rw [Finset.card_empty, Nat.mul_zero, Nat.zero_add, ← Finset.mul_sum]
    have : 3 * k * ∑ p ∈ (segL s μ bo μ).toFinset, (2 * len p - s) ≤ 3 * k * (2 * μ) :=
      Nat.mul_le_mul_left _ (by omega)
    calc _ ≤ 3 * k * (2 * μ) := this
      _ = 6 * k * μ := by ring
  · have h1 := sum_segL (s := s) (μ := μ) (bo := bo) μ
    have h2 := cntLt_le bo μ μ
    rwo [Nat.zero_mul, Nat.zero_add]

end

end Chazelle.Core.Cluster
