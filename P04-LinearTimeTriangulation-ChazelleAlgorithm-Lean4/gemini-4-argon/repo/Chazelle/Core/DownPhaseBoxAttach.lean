module

public import Chazelle.Core.DownPhaseBoxChord

/-!
# WP-M (B3′, part 6): attachment of twin chords

The side-aware attachment (`Chazelle.Chain.SideAttach`) of a horizontal chord transfers from the
walk of a chain `C` to the walk of a twin chain `C'` under the box stretch `φ`:

* the sector test `sideCcw` is invariant under positive scalings of its three vectors
  (`sideCcw_smul`);
* `φ` maps every walk edge of `C` to a positive multiple of itself (`edge_scale`: walk edges are
  horizontal, vertical, or between fixed chain vertices), so the corner vectors of a walk position
  scale positively (`sector_scale`);
* `φ` moves the points of a horizontal line monotonically (`scale_pt`).
-/

namespace Chazelle.Core

namespace BoxT

@[expose] public section

open Set Chazelle.Chain Chazelle.Visibility

/-! ## Scaling the sector test -/

theorem pos_mul_iff {p c : ℝ} (hp : 0 < p) :
    (0 < p * c ↔ 0 < c) ∧ (p * c < 0 ↔ c < 0) ∧ (p * c = 0 ↔ c = 0) := by
  refine ⟨⟨fun h => ?_, fun h => mul_pos hp h⟩,
    ⟨fun h => ?_, fun h => mul_neg_of_pos_of_neg hp h⟩, ⟨fun h => ?_, fun h => by rw [h, mul_zero]⟩⟩
  · by_contra h'; nlinarith
  · by_contra h'; nlinarith
  · rcases mul_eq_zero.1 h with h | h
    · linarith
    · exact h

theorem sideCross_smul (a b : ℝ) (u v : Point) :
    sideCross (a • u) (b • v) = (a * b) * sideCross u v := by
  unfold sideCross; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem sideDot_smul (a b : ℝ) (u v : Point) :
    sideDot (a • u) (b • v) = (a * b) * sideDot u v := by
  unfold sideDot; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- **The sector test is invariant under positive scalings.** -/
theorem sideCcw_smul {l k m : ℝ} (hl : 0 < l) (hk : 0 < k) (hm : 0 < m) (B X A : Point) :
    sideCcw (l • B) (k • X) (m • A) ↔ sideCcw B X A := by
  unfold sideCcw
  rw [sideCross_smul, sideCross_smul, sideCross_smul, sideDot_smul, sideDot_smul]
  obtain ⟨a1, a2, a3⟩ := pos_mul_iff (c := sideCross B A) (mul_pos hl hm)
  obtain ⟨b1, -, b3⟩ := pos_mul_iff (c := sideCross B X) (mul_pos hl hk)
  obtain ⟨c1, -, -⟩ := pos_mul_iff (c := sideCross X A) (mul_pos hk hm)
  obtain ⟨d1, d2, -⟩ := pos_mul_iff (c := sideDot B A) (mul_pos hl hm)
  obtain ⟨-, e2, -⟩ := pos_mul_iff (c := sideDot B X) (mul_pos hl hk)
  simp only [a1, a2, a3, b1, b3, c1, d1, d2, e2, ne_eq]

/-- The left sector test at a walk position, in terms of the corner vectors. -/
theorem sideLeft_eq (W : Polygon) (p : ℕ) (t : ℝ) (x : Point) :
    sideLeft W p t x ↔ sideCcw (sideNext W p - sidePt W p t) (x - sidePt W p t)
      (sidePrev W p t - sidePt W p t) := Iff.rfl

theorem next_sub_pt (W : Polygon) (p : ℕ) (t : ℝ) :
    sideNext W p - sidePt W p t = (1 - t) • (W.vtx ((p + 1) % W.n) - W.vtx p) := by
  unfold sideNext sidePt
  apply Prod.ext <;> simp [Geometry.lerp] <;> ring

theorem prev_sub_pt (W : Polygon) (p : ℕ) {t : ℝ} (ht : t ≠ 0) :
    sidePrev W p t - sidePt W p t = (-t) • (W.vtx ((p + 1) % W.n) - W.vtx p) := by
  unfold sidePrev sidePt
  rw [ite_eq_right ht]
  apply Prod.ext <;> simp [Geometry.lerp]

theorem prev_sub_pt_zero (W : Polygon) (p : ℕ) :
    sidePrev W p 0 - sidePt W p 0 =
      (-1 : ℝ) • (W.vtx p - W.vtx ((p + W.n - 1) % W.n)) := by
  unfold sidePrev sidePt
  rw [ite_eq_left rfl]
  apply Prod.ext <;> simp [Geometry.lerp]

theorem prev_succ {n p : ℕ} (hp : p < n) : ((p + n - 1) % n + 1) % n = p := by
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · subst h0
    have e : (0 + n - 1) % n = n - 1 := by rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [e, Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
  · have e : (p + n - 1) % n = p - 1 := by
      rw [show p + n - 1 = (p - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e, Nat.sub_add_cancel h0, Nat.mod_eq_of_lt hp]

/-! ## Twin chains -/

variable {C C' : Chain}

/-- The stretch has positive slopes. -/
theorem sig_slope (a b : ℝ) :
    ∃ l : ℝ, 0 < l ∧ stretch (bnd C C') (kk C C') b - stretch (bnd C C') (kk C C') a = l * (b - a) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · have h1 : stretch (bnd C C') (kk C C') a < stretch (bnd C C') (kk C C') b := sig_lt_iff.2 hab
    refine ⟨(stretch (bnd C C') (kk C C') b - stretch (bnd C C') (kk C C') a) / (b - a),
      div_pos (by linarith) (by linarith), ?_⟩
    field_simp [show b - a ≠ 0 by linarith]
  · exact ⟨1, one_pos, by ring⟩
  · have h1 : stretch (bnd C C') (kk C C') b < stretch (bnd C C') (kk C C') a := sig_lt_iff.2 hab
    refine ⟨(stretch (bnd C C') (kk C C') b - stretch (bnd C C') (kk C C') a) / (b - a),
      div_pos_of_neg_of_neg (by linarith) (by linarith), ?_⟩
    field_simp [show b - a ≠ 0 by linarith]

namespace Twin

variable (h : Twin C C')
include h

/-- **The stretch scales horizontal, vertical and chain segments positively.** -/
theorem scale_pt {u v : Point} (hk : u.2 = v.2 ∨ u.1 = v.1 ∨ (u ∈ C.set ∧ v ∈ C.set)) :
    ∃ l : ℝ, 0 < l ∧ phi C C' v - phi C C' u = l • (v - u) := by
  rcases hk with hk | hk | ⟨hu, hv⟩
  · obtain ⟨l, hl, e⟩ := sig_slope (C := C) (C' := C') u.1 v.1
    refine ⟨l, hl, Prod.ext ?_ ?_⟩
    · simpa [phi, stretchPt] using e
    · simp [phi, stretchPt, hk]
  · obtain ⟨l, hl, e⟩ := sig_slope (C := C) (C' := C') u.2 v.2
    refine ⟨l, hl, Prod.ext ?_ ?_⟩
    · simp [phi, stretchPt, hk]
    · simpa [phi, stretchPt] using e
  · exact ⟨1, one_pos, by rw [h.phi_fix hu, h.phi_fix hv, one_smul]⟩

/-- **Walk edges scale positively.** -/
theorem edge_scale {q : ℕ} (hq : q < (C.sideWalk C.sideBeta).n) :
    ∃ l : ℝ, 0 < l ∧ (C'.sideWalk C'.sideBeta).vtx ((q + 1) % (C.sideWalk C.sideBeta).n) -
        (C'.sideWalk C'.sideBeta).vtx q =
      l • ((C.sideWalk C.sideBeta).vtx ((q + 1) % (C.sideWalk C.sideBeta).n) -
        (C.sideWalk C.sideBeta).vtx q) := by
  rw [h.phi_walk_vtx, h.phi_walk_vtx]
  exact h.scale_pt (edge_kind C hq)

/-- **The corner vectors of corresponding walk positions scale positively.** -/
theorem sector_scale {p : ℕ} {t t' : ℝ} (hp : p < (C.sideWalk C.sideBeta).n)
    (ht : 0 ≤ t ∧ t < 1) (ht' : 0 ≤ t' ∧ t' < 1) (h0 : t = 0 ↔ t' = 0) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧
      sideNext (C'.sideWalk C'.sideBeta) p - sidePt (C'.sideWalk C'.sideBeta) p t' =
          α • (sideNext (C.sideWalk C.sideBeta) p - sidePt (C.sideWalk C.sideBeta) p t) ∧
        sidePrev (C'.sideWalk C'.sideBeta) p t' - sidePt (C'.sideWalk C'.sideBeta) p t' =
          β • (sidePrev (C.sideWalk C.sideBeta) p t - sidePt (C.sideWalk C.sideBeta) p t) := by
  set W := C.sideWalk C.sideBeta
  set W' := C'.sideWalk C'.sideBeta
  have hn : W'.n = W.n := h.walk_n
  obtain ⟨l, hl, e⟩ := h.edge_scale hp
  have hα : 0 < (1 - t') * l / (1 - t) := div_pos (mul_pos (by linarith) hl) (by linarith)
  have eN : sideNext W' p - sidePt W' p t' =
      ((1 - t') * l / (1 - t)) • (sideNext W p - sidePt W p t) := by
    rw [next_sub_pt, next_sub_pt, hn, e, smul_smul, smul_smul]
    congr 1
    field_simp [show 1 - t ≠ 0 by linarith]
  refine ⟨_, hα, ?_⟩
  by_cases ht0 : t = 0
  · have ht0' : t' = 0 := h0.1 ht0
    subst ht0 ht0'
    set q := (p + W.n - 1) % W.n
    have hnpos : 0 < W.n := by omega
    have hq : q < W.n := Nat.mod_lt _ hnpos
    obtain ⟨l', hl', e'⟩ := h.edge_scale hq
    have hqp : (q + 1) % W.n = p := prev_succ hp
    rw [hqp] at e'
    refine ⟨l', hl', eN, ?_⟩
    rw [prev_sub_pt_zero, prev_sub_pt_zero, hn, e', smul_smul, smul_smul, mul_comm]
  · have ht0' : t' ≠ 0 := fun e0 => ht0 (h0.2 e0)
    have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have htp' : 0 < t' := lt_of_le_of_ne ht'.1 (Ne.symm ht0')
    refine ⟨t' * l / t, div_pos (mul_pos htp' hl) htp, eN, ?_⟩
    rw [prev_sub_pt _ _ ht0, prev_sub_pt _ _ ht0', hn, e, smul_smul, smul_smul]
    congr 1
    field_simp

/-- **Attachment transfers.**  A set on a horizontal line attached to the walk of `C` at `(p, t)`
has its stretch attached to the walk of `C'` at the corresponding position `(p, t')`. -/
theorem attach_transfer {d : Set Point} {y : ℝ} (hdy : ∀ z ∈ d, z.2 = y) {p : ℕ} {t t' : ℝ}
    (hpt : sidePt (C'.sideWalk C'.sideBeta) p t' = phi C C' (sidePt (C.sideWalk C.sideBeta) p t))
    (ht' : 0 ≤ t' ∧ t' < 1) (h0 : t = 0 ↔ t' = 0)
    (hA : SideAttach (C.sideWalk C.sideBeta) d p t) :
    SideAttach (C'.sideWalk C'.sideBeta) (phi C C' '' d) p t' := by
  obtain ⟨hp, ht0, ht1, hmem, r, hr, hnear⟩ := hA
  refine ⟨h.walk_n ▸ hp, ht'.1, ht'.2, hpt ▸ mem_image_of_mem _ hmem, ?_⟩
  obtain ⟨α, hα, β, hβ, eN, eP⟩ := h.sector_scale hp ⟨ht0, ht1⟩ ht' h0
  set ψ := (stretchHomeo (bnd_nonneg (C := C) (C' := C')) (kk_pos (C := C) (C' := C'))).symm
  have hψ : ∀ z, ψ (phi C C' z) = z := fun z =>
    (stretchHomeo (bnd_nonneg (C := C) (C' := C')) (kk_pos (C := C) (C' := C'))).symm_apply_apply z
  obtain ⟨r', hr', hball⟩ := Metric.continuous_iff.1 ψ.continuous
    (sidePt (C'.sideWalk C'.sideBeta) p t') r hr
  refine ⟨r', hr', ?_⟩
  rintro x' ⟨z, hz, rfl⟩ hne hdist
  set s := sidePt (C.sideWalk C.sideBeta) p t
  have hzd : dist z s < r := by
    have := hball _ hdist
    rwa [hψ z, hpt, hψ s] at this
  have hzne : z ≠ s := fun e => hne (by rw [e, hpt])
  have hL := hnear z hz hzne hzd
  have hz2 : s.2 = z.2 := (hdy s hmem).trans (hdy z hz).symm
  obtain ⟨κ, hκ, eX⟩ := h.scale_pt (Or.inl hz2)
  rwa [sideLeft_eq, eN, eP, hpt, eX, sideCcw_smul hα hκ hβ]

end Twin

end

end BoxT

end Chazelle.Core
