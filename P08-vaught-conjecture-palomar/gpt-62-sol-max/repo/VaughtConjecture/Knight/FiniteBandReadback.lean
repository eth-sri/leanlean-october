/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.VisibilityBandArithmetic
public import VaughtConjecture.Knight.ProvisionalUniqueness
public import VaughtConjecture.Knight.Reduction

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

namespace Value

theorem limitPart_of_succLimit {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) :
    limitPart α = α :=
  le_antisymm (limitPart_le α) (succLimit_le_limitPart hα le_rfl)

theorem limitPart_succLimit_add_nat {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) (i : ℕ) :
    limitPart (α + i) = α := by
  have h := limitPart_limitPart_add_nat α i
  rwa [limitPart_of_succLimit hα] at h

theorem finitePart_succLimit_add_nat {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) (i : ℕ) :
    finitePart (α + i) = i := by
  have h := finitePart_limitPart_add_nat α i
  rwa [limitPart_of_succLimit hα] at h

theorem exists_nat_of_lt_add_omega {α μ : Ordinal.{0}} (hle : α ≤ μ)
    (hlt : μ < α + Ordinal.omega0) : ∃ k : ℕ, μ = α + k := by
  obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp ((Ordinal.sub_lt_of_le hle).mpr hlt)
  exact ⟨k, by rw [← hk, Ordinal.add_sub_cancel_of_le hle]⟩

/-- `visibilityReplace` below the threshold: `μ ⊔_K i = limitPart μ + i` when `fp μ < K`. -/
theorem visibilityReplace_of_finitePart_lt {μ : Ordinal.{0}} {K i : ℕ} (h : finitePart μ < K) :
    visibilityReplace μ K i = limitPart μ + i := by
  unfold visibilityReplace ordinalReplace
  simp_all

/-- `limitPart μ + K ≤ μ ⊔_K K` always. -/
theorem limitPart_add_le_visibilityReplace (μ : Ordinal.{0}) (K : ℕ) :
    limitPart μ + K ≤ visibilityReplace μ K K := by
  unfold visibilityReplace ordinalReplace
  by_cases h : finitePart μ < K
  · simp_all
  · rw [ite_eq_right h]
    calc limitPart μ + K ≤ limitPart μ + finitePart μ :=
          by simp_all
      _ = μ := decomposition μ

/-- Every visible band has the same replacement arithmetic. -/
theorem replace_band {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) {i K : ℕ} (hi : i < K) (j : ℕ) :
    extVisibilityReplace (ofOrd (α + i)) K j = ofOrd (α + j) := by
  rw [extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt,
    limitPart_succLimit_add_nat hα]
  rwa [finitePart_succLimit_add_nat hα]

/-- A map commuting with replacement at a low band value maps all its rungs. -/
theorem lift_visibility_band {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) {i K : ℕ} (hi : i < K)
    {σ : ExtOrd → ExtOrd} {u : ExtOrd} (hu : σ u = ofOrd (α + i))
    (hc : ∀ j ≤ K, σ (extVisibilityReplace u K j) = extVisibilityReplace (σ u) K j) :
    ∃ μ, u = ofOrd μ ∧ finitePart μ < K ∧
      ∀ j ≤ K, σ (ofOrd (limitPart μ + j)) = ofOrd (α + j) := by
  have hn : extVisibilityReplace u K K ≠ u := by
    intro h
    have he := hc K le_rfl
    rw [h, hu, replace_band hα hi] at he
    simp_all
  rcases ExtOrd.cases u with rfl | rfl | ⟨μ, rfl⟩
  · simp at hn
  · simp at hn
  · have hm : finitePart μ < K := by simpa [visibilityReplace_self_iff] using hn
    refine ⟨μ, rfl, hm, fun j hj => ?_⟩
    have h := hc j hj
    rw [hu, replace_band hα hi, extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt hm] at h
    exact h

theorem extVisibilityReplace_ge_add {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    {u : ExtOrd} (hu : ofOrd α ≤ u) (K : ℕ) :
    ofOrd (α + K) ≤ extVisibilityReplace u K K := by
  rcases ExtOrd.cases u with rfl | rfl | ⟨μ, rfl⟩
  · simp at hu
  · simp
  · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at ⊢
    exact (add_le_add (succLimit_le_limitPart hα (ofOrd_le_ofOrd.mp hu)) le_rfl).trans
      (limitPart_add_le_visibilityReplace μ K)

end Value

namespace ExtOrd

theorem exists_nat_of_mem_band {α : Ordinal.{0}} {x : ExtOrd} (hle : ofOrd α ≤ x)
    (hlt : x < ofOrd (α + Ordinal.omega0)) : ∃ k : ℕ, x = ofOrd (α + k) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨μ, rfl⟩
  · trivial
  · trivial
  · obtain ⟨k, hk⟩ := Value.exists_nat_of_lt_add_omega (ofOrd_le_ofOrd.mp hle)
      (ofOrd_lt_ofOrd.mp hlt)
    tauto

theorem le_of_lt_ofOrd_add_one {u : ExtOrd} {δ : Ordinal.{0}} (hu : u < ofOrd (δ + 1)) :
    u ≤ ofOrd δ := by
  rcases ExtOrd.cases u with rfl | rfl | ⟨μ, rfl⟩
  · exact bot_le
  · simp at hu
  · rwa [ofOrd_lt_ofOrd, ← Order.succ_eq_add_one, Order.lt_succ_iff, ← ofOrd_le_ofOrd] at hu

end ExtOrd

namespace StageType

variable {α β : Ordinal.{0}} {n : ℕ}

/-- **Orderliness pins the band of an `∞`-cell**: a label `≥ α` (`α` a limit) at a cell of
grade `K` is `≥ α + K` (self-visibility at `K` means finite part `≥ K`). -/
theorem label_ge_add_grade (hα : Order.IsSuccLimit α) {q : S β n} (Θ : Cell q.scheme.scheme)
    (hge : ofOrd α ≤ q.label Θ) :
    ofOrd (α + q.scheme.scheme.grade Θ) ≤ q.label Θ := by
  simpa only [← q.respects.orderly Θ] using extVisibilityReplace_ge_add hα hge (q.scheme.scheme.grade Θ)

/-- The top witness: a full-scope `∞`-cell of grade `K^q` above any `∞`-cell. -/
theorem exists_top_witness {q : S β n} {Xi : Cell q.scheme.scheme} (htop : q.label Xi = ⊤) :
    ∃ Θ : Cell q.scheme.scheme, GradedLe (q.scheme.scheme.cell Xi) (q.scheme.scheme.cell Θ) ∧
      q.scheme.scheme.scope Θ = Finset.univ ∧ q.scheme.scheme.grade Θ = q.topGrade ∧
      q.label Θ = ⊤ := by
  have hmem := grade_mem_topGrades htop
  have hbdd := q.topGrades_bddAbove
  obtain ⟨Θ, hsc, hgr, hΘtop⟩ : q.topGrade ∈ q.topGrades := Nat.sSup_mem ⟨_, hmem⟩ hbdd
  refine ⟨Θ, ⟨?_, ?_⟩, hsc, hgr, hΘtop⟩
  · simp_all
  · change q.scheme.scheme.grade Xi ≤ q.scheme.scheme.grade Θ
    rw [hgr]
    exact le_csSup hbdd hmem

/-- Any `∞`-cell has grade `≤ K^q`. -/
theorem grade_le_topGrade_of_top {q : S β n} {Xi : Cell q.scheme.scheme}
    (htop : q.label Xi = ⊤) : q.scheme.scheme.grade Xi ≤ q.topGrade :=
  le_csSup q.topGrades_bddAbove (grade_mem_topGrades htop)

/-- The locality data of the labelling of `q` at `Θ` (Def. 2.5.4(1)), spelled out. -/
theorem locality_label_data (q : S β n) (Θ : Cell q.scheme.scheme) :
    ∃ (g : ℕ → ExtOrd) (σ : ExtOrd → ExtOrd),
      (∀ n m : ℕ, n < m → g m ≤ g n) ∧ σ ⊥ = ⊥ ∧ Monotone σ ∧
      (∀ (a : ExtOrd) (k : ℕ), σ a ≤ g k → ∀ i : ℕ, i ≤ k →
        σ (extVisibilityReplace a k i) = extVisibilityReplace (σ a) k i) ∧
      (∀ d : q.scheme.scheme.below (q.scheme.scheme.cell Θ),
        min (q.label d.1) (q.label Θ) =
          min (σ (q.scheme.rows.E Θ d)) (g (q.scheme.scheme.grade d.1))) ∧
      q.label Θ ≤ g (q.scheme.scheme.grade Θ) := by
  obtain ⟨g, σ, hganti, -, hσbot, hσmono, hσ5, hloc⟩ := q.respects.locality Θ
  refine ⟨g, σ, hganti, hσbot, hσmono, hσ5, fun d => hloc d, ?_⟩
  have h : min (q.label Θ) (q.label Θ) =
      min (σ (q.scheme.rows.E Θ ⟨Θ, GradedLe.refl _⟩)) (g (q.scheme.scheme.grade Θ)) :=
    hloc ⟨Θ, GradedLe.refl _⟩
  simp_all

theorem g_le_of_le {g : ℕ → ExtOrd} (hganti : ∀ n m : ℕ, n < m → g m ≤ g n) {k K : ℕ}
    (h : k ≤ K) : g K ≤ g k := by grind

/-- **Pinning**: below a top cell, the transform reproduces every label strictly below the
label of the top cell: `σ (E(Θ)(d)) = q(d) ≤ g (grade Θ)`. -/
theorem sigma_eq_of_lt_label {q : S β n} {Θ : Cell q.scheme.scheme} {g : ℕ → ExtOrd}
    {σ : ExtOrd → ExtOrd} (hganti : ∀ n m : ℕ, n < m → g m ≤ g n)
    (hΘg : q.label Θ ≤ g (q.scheme.scheme.grade Θ))
    {d : q.scheme.scheme.below (q.scheme.scheme.cell Θ)}
    (hd : min (q.label d.1) (q.label Θ) =
      min (σ (q.scheme.rows.E Θ d)) (g (q.scheme.scheme.grade d.1)))
    (hlt : q.label d.1 < q.label Θ) :
    σ (q.scheme.rows.E Θ d) = q.label d.1 ∧
      σ (q.scheme.rows.E Θ d) ≤ g (q.scheme.scheme.grade Θ) := by
  have hgd : g (q.scheme.scheme.grade Θ) ≤ g (q.scheme.scheme.grade d.1) :=
    g_le_of_le hganti d.2.2
  grind

theorem reduced_label_ge_add_grade (hα : Order.IsSuccLimit α) (hαβ : α ≤ β) {q : S β n}
    {Θ : Cell q.scheme.scheme} (hΘ : (reduceType hα hαβ q).label Θ = ⊤) :
    ofOrd (α + q.scheme.scheme.grade Θ) ≤ q.label Θ :=
  label_ge_add_grade hα Θ (truncExt_eq_top_iff.mp hΘ)

/-- **Lemma 5.5.2, band case**: if `N(Ξ) = α + i` with `i < K^q` (top grade of the reduct),
then the reduct's provisional value at `Ξ` is `α + i`. -/
theorem isProvisionalValue_band_of_expansion (hα : Order.IsSuccLimit α) (hαβ : α ≤ β)
    {q : S β n} (Xi : Cell q.scheme.scheme) {i : ℕ} (hXi : q.label Xi = ofOrd (α + i))
    (hK : i < (reduceType hα hαβ q).topGrade) :
    (reduceType hα hαβ q).IsProvisionalValue Xi (ofOrd (α + i)) := by
  set p := reduceType hα hαβ q with hp
  have hptop : p.label Xi = ⊤ := truncExt_eq_top_iff.mpr (by simp [hXi])
  have hiK : ofOrd (α + i) < ofOrd (α + p.topGrade) := by simp [hK]
  have hgeK (Θ : Cell q.scheme.scheme) (hgr : q.scheme.scheme.grade Θ = p.topGrade)
      (ht : p.label Θ = ⊤) : ofOrd (α + p.topGrade) ≤ q.label Θ :=
    hgr ▸ reduced_label_ge_add_grade hα hαβ ht
  -- no cap
  have hncap : ¬ p.ProvisionalCap Xi := by
    rintro ⟨Θ, hXiΘ, Sg, hsc, hgr, hΘtop, hSgtop, hle⟩
    have hgr' : q.scheme.scheme.grade Θ = p.topGrade := hgr
    obtain ⟨g, σ, hganti, hσbot, hσmono, hσ5, hloc, hΘg⟩ := locality_label_data q Θ
    have hΘK : ofOrd (α + p.topGrade) ≤ q.label Θ := hgeK Θ hgr' hΘtop
    obtain ⟨ha, haK⟩ := sigma_eq_of_lt_label hganti hΘg (hloc ⟨Xi, hXiΘ⟩) (by grind)
    rw [hgr'] at haK
    change σ (q.scheme.rows.E Θ ⟨Xi, hXiΘ⟩) = q.label Xi at ha
    rw [hXi] at ha
    rw [ha] at haK
    let u := q.scheme.rows.E Θ Sg
    have hu : σ u ≤ ofOrd (α + i) := ha ▸ hσmono ((le_extVisibilityReplace_self _ _).trans hle)
    have hu' : ofOrd α ≤ σ u := by
      have hd := hloc Sg
      have hg : ofOrd α ≤ q.label Sg.1 := truncExt_eq_top_iff.mp hSgtop
      have ht : ofOrd α ≤ q.label Θ := (ofOrd_le_ofOrd.mpr le_self_add).trans hΘK
      exact (le_min hg ht).trans (hd.trans_le (min_le_left _ _))
    have hcomm := hσ5 u p.topGrade (hu.trans haK) p.topGrade le_rfl
    have hbig := (extVisibilityReplace_ge_add hα hu' p.topGrade).trans_eq hcomm.symm
    exact (not_le_of_gt hiK) (hbig.trans (ha ▸ hσmono hle))
  -- band witness
  obtain ⟨Θ, hXiΘ, hsc, hgr, hΘtop⟩ := exists_top_witness hptop
  have hgr' : q.scheme.scheme.grade Θ = p.topGrade := hgr
  obtain ⟨g, σ, hganti, hσbot, hσmono, hσ5, hloc, hΘg⟩ := locality_label_data q Θ
  have hΘK : ofOrd (α + p.topGrade) ≤ q.label Θ := hgeK Θ hgr' hΘtop
  obtain ⟨hσa, hσaK⟩ := sigma_eq_of_lt_label hganti hΘg (hloc ⟨Xi, hXiΘ⟩)
    (by grind)
  rw [hgr'] at hσaK
  set a := q.scheme.rows.E Θ ⟨Xi, hXiΘ⟩ with ha
  rw [hXi] at hσa
  obtain ⟨ν, hν, hf, hband⟩ := lift_visibility_band hα hK hσa (hσ5 a _ hσaK)
  have he : (i : Ordinal.{0}) = finitePart ν := by
    have h := hband (finitePart ν) hf.le
    rw [decomposition, ← hν, hσa, ofOrd_inj] at h
    exact add_left_cancel h
  have hi : i = finitePart ν := by exact_mod_cast he
  refine Or.inr (Or.inr ⟨hptop, hncap, i, ⟨Θ, hXiΘ, hsc, hgr, hΘtop, ?_⟩, rfl⟩)
  change a = extVisibilityReplace a p.topGrade i
  rw [hν, extVisibilityReplace_ofOrd, hi, visibilityReplace_of_finitePart_lt hf, decomposition]

end StageType

end VaughtConjecture.Knight
