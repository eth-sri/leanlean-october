module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ClusterStageD4

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
  core_grind [cntLt_succ]

theorem mem_segL {j : ℕ} {p : ℕ × ℕ} :
    p ∈ segL s μ bo j ↔ ∃ b, b < j ∧ s < cntBelow bo μ b ∧ p = seg μ bo b := by
  induction j with
  | zero => simp [segL]
  | succ j ih =>
    grind [segL, List.mem_append, optSeg, List.mem_singleton, cntLt_succ, seg]

section
variable {p : ℕ × ℕ}
theorem mem_finL :
    p ∈ finL s μ bo ↔ ∃ b, b < μ ∧ cntBelow bo μ b ≤ s ∧ p = seg μ bo b := by
  core_grind

theorem lv_iff :
    Lv (segL s μ bo μ) (finL s μ bo) p ↔ ∃ b, b < μ ∧ p = seg μ bo b := by
  grind [Lv, mem_segL, mem_finL]


end

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
      simp_all [seg] 
    simp_all

/-- The potential of the initial stack. -/
theorem sum_segL (j : ℕ) :
    ∑ p ∈ (segL s μ bo j).toFinset, (2 * len p - s) ≤ 2 * cntLt bo μ j := by
  induction j with
  | zero => positivity
  | succ j ih =>
    rw [cntLt_succ]
    simp only [segL, optSeg]
    split_ifs with hs
    · have hn := segL_nodup (s := s) (μ := μ) (bo := bo) (j + 1)
      simp only [segL, optSeg, ite_eq_left hs] at hn
      rw [List.singleton_append, List.toFinset_cons, Finset.sum_insert (by
        simp_all)]
      have : len (cntLt bo μ j, cntLt bo μ (j + 1)) = cntBelow bo μ j := len_seg j
      omega
    grind

section
variable {key act : ℕ → ℕ} (hinj : ∀ v w, v < μ → w < μ → key v = key w → v = w) (hact : ∀ v, v < μ → bo v < μ → act (plPos μ bo key v) = v) {b : ℕ} (hb : b < μ)
include key hinj hact hb
/-- The items of a block segment. -/
theorem items_seg :
    items act (seg μ bo b) = (Finset.range μ).filter (fun v => bo v = b) := by
  ext v
  rw [mem_items]; simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨i, h1, h2, rfl⟩
    obtain ⟨w, hw, hbw, rfl⟩ := exists_plPos (key := key) hinj h1 h2
    ram_grind
  · rintro ⟨hv, hbv⟩
    refine ⟨plPos μ bo key v, ?_, ?_, hact v hv (by omega)⟩
    · have := plPos_ge (μ := μ) (bo := bo) (key := key) v; rw [hbv] at this; exact this
    · have := plPos_lt (μ := μ) (bo := bo) (key := key) hv; rw [hbv] at this; exact this

theorem inj_seg :
    Set.InjOn act (Finset.Ico (seg μ bo b).1 (seg μ bo b).2) := by
  intro i hi i' hi' h
  simp only [Finset.coe_Ico, Set.mem_Ico] at hi hi'
  obtain ⟨w, hw, hbw, rfl⟩ := exists_plPos (key := key) hinj hi.1 hi.2
  obtain ⟨w', hw', hbw', rfl⟩ := exists_plPos (key := key) hinj hi'.1 hi'.2
  grind


end

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
  · grind
  · obtain ⟨b, -, h2, rfl⟩ := mem_segL.mp hp
    obtain ⟨b', -, h2', h3'⟩ := mem_finL.mp hf
    grind [len_seg]
  · obtain ⟨b, hb, rfl⟩ := lv_iff.mp hp; obtain ⟨b', hb', rfl⟩ := lv_iff.mp hq
    grind [Chazelle.Core.Cluster.seg_disj, RDisj]
  · obtain ⟨b, hb, rfl, hi⟩ := hit p hp; obtain ⟨b', hb', rfl, hi'⟩ := hit q hq
    grind [Finset.disjoint_left, Finset.mem_filter]
  · obtain ⟨b, -, h2, rfl⟩ := mem_segL.mp hp; grind [len_seg]
  · obtain ⟨b, -, h2, rfl⟩ := mem_finL.mp hp; grind [len_seg]
  · have hb : bo v < μ := by grind
    refine ⟨seg μ bo (bo v), lv_iff.mpr ⟨bo v, hb, rfl⟩, ?_⟩
    rw [items_seg hinj hact hb]; simp [hv]
  · obtain ⟨b, hb, rfl, hi⟩ := hit p hp; ram_grind
  · obtain ⟨b, hb, rfl, hi⟩ := hit p hp; grind
  · obtain ⟨hxμ, hyμ, hb⟩ := hedge x y hxy hx hy
    have hbx : bo x < μ := by grind
    refine ⟨seg μ bo (bo x), lv_iff.mpr ⟨bo x, hbx, rfl⟩, ?_, ?_⟩ <;>
      rw [items_seg hinj hact hbx] <;> grind
  · have h1 := sum_segL (s := s) (μ := μ) (bo := bo) μ
    have h2 := cntLt_le bo μ μ
    rw [Finset.card_empty, Nat.mul_zero, Nat.zero_add, ← Finset.mul_sum]
    have : 3 * k * ∑ p ∈ (segL s μ bo μ).toFinset, (2 * len p - s) ≤ 3 * k * (2 * μ) :=
      Nat.mul_le_mul_left _ (by omega)
    grind
  · have h1 := sum_segL (s := s) (μ := μ) (bo := bo) μ
    have h2 := cntLt_le bo μ μ
    omega

end

end Chazelle.Core.Cluster
