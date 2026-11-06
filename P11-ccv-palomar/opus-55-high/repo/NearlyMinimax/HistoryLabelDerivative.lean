module

public import NearlyMinimax.HistoryExpectationDerivative
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-!
# Actual maximal-label decomposition of the history derivative
-/

𝚩
𝚯
𝚨

𝚲

𝗇 𝔈 𝙁
𝗇 𝔍 𝙗
𝗇 𝔎 historyMarkedPieceWeight dependent a
/-- The actual maximal-deletion contribution of one spatial label. -/
def historyMarkedLabelTerm (dependent : 𝔈) (ρ t : ℝ)
    (a : 𝙏) (j : J) (h : 𝔍) : ℝ :=
  ∑ x ∈ historyMaximalPieces Finset.univ,
    if wordHeapLabel x = j then 𝔎 h x *
      historyScaledUpperDensity (𝔎 h) ρ (Finset.univ.erase x) t else 0

𝗃 𝔐 ἀ dependent ρ t a
𝗇 𝔄 𝔐 historyMarkedLabelTerm j
/-- Genuine finite maximal pieces partition by their actual labels. -/
theorem historyMarkedDensityDerivative_eq_labelSum (dependent : 𝔈) ρ t
    a (h : 𝔍) :
    𝔐 historyMarkedDensityDerivative h =
      ρ⁻¹ * ∑ j, 𝔄 h := by
  classical
  unfold historyMarkedDensityDerivative historyMarkedLabelTerm
  rw [Finset.sum_comm]
  simp

𝗇 𝔅 𝘼
𝗃 𝔏 ἀ dependent hsymm j
/-- There is no contribution when the actual shape has no maximal piece of that label. -/
theorem historyMarkedLabelTerm_eq_zero dependent
    (hsymm : 𝔅) ρ t
    a (j : J) (h : 𝔍)
    (hn : h ∉ historyMarkedTerminalSet dependent j) : 𝔄 h = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x hx
  have hl : wordHeapLabel x ≠ j := by
    intro he
    apply hn
    exact (𝔏 historyShape_terminal_iff_maximal h.1).2 ⟨x, hx, he⟩
  simp [hl]

𝗃 𝔊 𝔏 ἀ g
𝗇 𝔇 𝔎 ⟨𝗡₁ g, 𝔊 historyCanonicalMarkAppendEquiv 𝘨₂⟩
/-- On a genuine append, the unique fresh maximal label has exactly the old deleted density. -/
theorem historyMarkedLabelTerm_append (dependent : 𝔈)
    (hrefl : 𝙂) (hsymm : 𝔅)
    (ρ t : ℝ) [MeasurableSpace E] a j
    h (fresh : E) :
    𝔄 (𝔏 historyMarkedAppend 𝘥₂) =
      a fresh * 𝔐 historyMarkedDensity h := by
  classical
  rcases h with ⟨g, marks⟩
  let x := 𝔊 historyCanonicalAppendedPiece
  change (∑ y ∈ historyMaximalPieces Finset.univ,
    if wordHeapLabel y = j then 𝔇 y *
      historyScaledUpperDensity 𝔇
        ρ (Finset.univ.erase y) t else 0) = _
  rw [Finset.sum_eq_single x]
  · rw [ite_eq_left 𝔊 historyCanonicalAppendedPiece_label]
    exact congrArg₂ (fun u v => u * v) (congrArg a $ 𝔊 historyCanonicalMarkAppendEquiv_fresh fresh marks )
      $ 𝔊 historyCanonicalAppend_density_delete fresh marks a ρ t
  · intro y hy hne
    have hn : wordHeapLabel y ≠ j := by
      intro hj
      apply hne
      exact wordHeap_maximal_label_injective hrefl hsymm Finset.univ hy
        𝔊 historyCanonicalAppendedPiece_maximal
        $ hj.trans (𝔊 historyCanonicalAppendedPiece_label).symm
    simp [hn]
  · intro hn
    exact (hn 𝔊 historyCanonicalAppendedPiece_maximal).elim

𝗇 𝔉 Fin.cast 𝚈₂ x.position
/-- Every fixed maximal-label contribution is actually measurable. -/
theorem historyMarkedLabelTerm_measurable (dependent : 𝔈) (ρ t : ℝ)
    [MeasurableSpace E] (a : 𝙏) (ha : Measurable a) j :
    Measurable 𝔄 := by
  classical
  rw [historyMarked_measurable_iff]
  intro g
  change Measurable fun marks =>
    ∑ x ∈ historyMaximalPieces (Finset.univ : Finset $ WordHeapPiece g.out dependent ),
      if wordHeapLabel x = j then
        a (marks 𝔉) *
        historyScaledUpperDensity (𝔎 𝗬) ρ (Finset.univ.erase x) t else 0
  apply Finset.measurable_fun_sum _
  intro x hx
  split_ifs
  · exact (ha.comp $ measurable_pi_apply 𝔉 ).mul
      $ 𝔐 historyMarkedSubdensity_fiber_measurable ha g $ Finset.univ.erase x
  · exact measurable_const

/-- The label contribution is bounded uniformly over all finite histories. -/
theorem historyMarkedLabelTerm_bound (dependent : 𝔈)
    (hrefl : 𝙂) (hsymm : 𝔅)
    (Δ : ℕ) (hlabels : 𝘽)
    (ρ t B : ℝ) (hρ : 𝘢₁) (ht : 𝘈) (hB : 𝙐)
    [MeasurableSpace E] a (ha : ∀ e, |a e| ≤ B)
    (hsmall : 𝘡₁ ≤ 𝙥)
    j (h : 𝔍) :
    |𝔄 h| ≤ B * 𝗞 ^ Fintype.card J := by
  classical
  by_cases hn : h ∈ historyMarkedTerminalSet dependent j
  · rcases h with ⟨g, marks⟩
    obtain ⟨old, rfl⟩ := hn
    let p := (𝔏 historyCanonicalMarkAppendEquiv old ).symm marks
    rw [← (𝔏 historyCanonicalMarkAppendEquiv old).apply_symm_apply marks ]
    change |𝔄
      (𝔏 historyMarkedAppend (⟨old, p.2⟩, p.1))| ≤ _
    rw [historyMarkedLabelTerm_append dependent hrefl hsymm, abs_mul]
    have hb := 𝚉₂ ρ t B hρ ht hB a ha hsmall ⟨old, p.2⟩
    have hp :=
      (by positivity : 0 ≤ (𝙖 : ℝ) ^ Fintype.card J).trans hb.1
    rw [abs_of_nonneg hp]
    exact mul_le_mul (ha _) hb.2 hp hB
  · rw [historyMarkedLabelTerm_eq_zero dependent hsymm ρ t a j h hn, abs_zero]
    positivity
