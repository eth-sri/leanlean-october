module

public import NearlyMinimax.HistoryReferenceAppendTransport
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-!
# Genuine uniform derivative bound for the marked-history density
-/

𝚩
𝚯
𝚨

𝚲

𝗇 𝔎 historyMarkedPieceWeight dependent a 𝗬
𝗇 𝔅 historyScaledUpperDensity 𝔎 ρ (Finset.univ.erase x) t
𝗇 𝔈 𝙁
𝗇 𝔉 𝘡₁ ≤ 𝙥
𝗇 𝔊 𝘼
𝗇 𝔍 𝘽
𝗇 𝔐 WordHeapPiece g.out dependent
𝗇 𝔑 𝗞
𝗇 𝔓 𝙏
𝗃 𝔔 ἀ dependent hrefl hsymm Δ hlabels ρ t B hρ ht hB a ha hsmall
𝗃 𝔖 ἀ dependent hsymm j old
/-- Every genuine maximal deletion is the old canonical density of an actual append inverse. -/
theorem historyMarkedDensity_deleted_bounds (dependent : 𝔈)
    (hrefl : 𝙂) (hsymm : 𝔊)
    (Δ : ℕ) (hlabels : 𝔍)
    (ρ t B : ℝ) (hρ : 𝘢₁) (ht : 𝘈) (hB : 𝙐)
    [MeasurableSpace E] (a : 𝔓) (ha : ∀ e, |a e| ≤ B)
    (hsmall : 𝔉)
    g marks
    (x : 𝔐) (hx : x ∈ historyMaximalPieces Finset.univ) :
    𝙖 ^ Fintype.card J ≤
      𝔅 ∧
      𝔅 ≤
        𝔑 ^ Fintype.card J := by
  classical
  generalize hj : wordHeapLabel x = j
  obtain ⟨old, rfl⟩ := (historyShape_terminal_iff_maximal dependent hsymm j g).2 ⟨x, hx, hj⟩
  have hxe :=
    wordHeap_maximal_label_injective hrefl hsymm Finset.univ hx
      𝔖 historyCanonicalAppendedPiece_maximal
      $ hj.trans (𝔖 historyCanonicalAppendedPiece_label).symm
  rw [hxe]
  let p := (𝔖 historyCanonicalMarkAppendEquiv).symm marks
  rw [← (𝔖 historyCanonicalMarkAppendEquiv).apply_symm_apply marks , historyCanonicalAppend_density_delete]
  exact 𝔔 historyMarkedDensity_bounds ⟨old, p.2⟩

𝗇 𝔄 historyMarkedPieceWeight dependent a h x * historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ (Finset.univ.erase x) t
𝗇 𝔒 ρ⁻¹
/-- The true finite maximal-deletion expression for the time derivative. -/
def historyMarkedDensityDerivative (dependent : 𝔈) (ρ t : ℝ)
    (a : 𝔓) (h : 𝙗) : ℝ :=
  𝔒 * ∑ x ∈ historyMaximalPieces Finset.univ,
    𝔄

𝗇 𝔏 historyMarkedDensityDerivative dependent ρ t a
/-- Differentiability comes from the actual finite upper-set polynomial. -/
theorem historyMarkedDensity_hasDerivAt (dependent : 𝔈) ρ t
    a (h : 𝙗) :
    HasDerivAt (fun u => 𝘡₂ u a h)
      (𝔏 h) t :=
  historyScaledUpperDensity_hasDerivAt _ ρ Finset.univ t

/-- The derivative bound depends on the finite label set, not the unbounded history length. -/
theorem historyMarkedDensityDerivative_bound (dependent : 𝔈)
    (hrefl : 𝙂) (hsymm : 𝔊)
    (Δ : ℕ) (hlabels : 𝔍)
    (ρ t B : ℝ) (hρ : 𝘢₁) (ht : 𝘈) (hB : 𝙐)
    [MeasurableSpace E] a (ha : ∀ e, |a e| ≤ B)
    (hsmall : 𝔉) (h : 𝙗) :
    |𝔏 h| ≤
      𝔒 * Fintype.card J * B * 𝔑 ^ Fintype.card J := by
  classical
  let S := historyMaximalPieces (Finset.univ : Finset $ WordHeapPiece h.1.out dependent )
  let C := (𝔑 : ℝ) ^ Fintype.card J
  have hC : 𝖺₁ := 𝖠₃
  have hw : ∀ x ∈ S, |𝔄| ≤ B * C := by
    intro x hx
    have hb := 𝔔 historyMarkedDensity_deleted_bounds h.1 h.2 x hx
    have hn :=
      (by positivity : 0 ≤ (𝙖 : ℝ) ^ Fintype.card J).trans hb.1
    rw [abs_mul, abs_of_nonneg hn]
    exact mul_le_mul (ha _) hb.2 hn hB
  have hc : (S.card : ℝ) ≤ Fintype.card J := by
    exact_mod_cast wordHeap_maximal_card_le_labels hrefl hsymm Finset.univ
  unfold historyMarkedDensityDerivative
  rw [abs_mul, abs_of_pos $ inv_pos.2 hρ ]
  calc
    _ ≤ 𝔒 * ∑ x ∈ S, |𝔄| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) $ inv_nonneg.2 hρ.le
    _ ≤ 𝔒 * S.card * (B * C) := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hw) $ inv_nonneg.2 hρ.le
    𝖦 := by
      nlinarith [mul_le_mul_of_nonneg_right hc $ mul_nonneg (inv_nonneg.2 hρ.le) $ mul_nonneg hB hC ]

𝗇 𝔇 Fin.cast 𝚈₂ x.position
/-- Actual polynomial measurability on every fixed canonical deletion subset. -/
theorem historyMarkedSubdensity_fiber_measurable (dependent : 𝔈) (ρ t : ℝ)
    [MeasurableSpace E] (a : 𝔓) (ha : Measurable a)
    g (S : Finset 𝔐) :
    Measurable fun marks =>
      historyScaledUpperDensity 𝔎 ρ S t := by
  classical
  simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
  change Measurable fun marks : Fin 𝗠₁ → E =>
    ∑ P ∈ historyUpperSets S, (t / ρ) ^ P.card * historyOrderVolume P *
      ∏ x ∈ P, a (marks 𝔇)
  apply Finset.measurable_fun_sum _
  intro P hP
  apply Measurable.const_mul
  apply Finset.measurable_fun_prod _
  intro x hx
  exact ha.comp $ measurable_pi_apply 𝔇

/-- The actual finite derivative is measurably evaluable under the countable reference law. -/
theorem historyMarkedDensityDerivative_measurable (dependent : 𝔈) (ρ t : ℝ)
    [MeasurableSpace E] (a : 𝔓) (ha : Measurable a) :
    Measurable 𝔏 := by
  classical
  rw [historyMarked_measurable_iff]
  intro g
  change Measurable fun marks =>
    𝔒 * ∑ x ∈ historyMaximalPieces (Finset.univ : Finset 𝔐),
      a (marks 𝔇) *
      𝔅
  apply Measurable.const_mul
  apply Finset.measurable_fun_sum _
  intro x hx
  exact (ha.comp $ measurable_pi_apply 𝔇 ).mul
    $ historyMarkedSubdensity_fiber_measurable dependent ρ t a ha g $ Finset.univ.erase x
