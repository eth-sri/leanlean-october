module

public import NearlyMinimax.HistoryCanonicalDeletion
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-!
# Actual marked reference append change of variables
-/

𝚯
𝚮
𝚨

𝚲

omit [Fintype J] [LinearOrder J] in
theorem historyMeasure_smul_sum [MeasurableSpace X]
    (c : 𝙉₁) (μ : I → Measure X) : c • Measure.sum μ = Measure.sum fun i => c • μ i := by
  ext s hs
  simp only [Measure.smul_apply, Measure.sum_apply _ hs, smul_eq_mul]
  exact ENNReal.tsum_mul_left.symm

𝗇 𝔄 𝘼
𝗇 𝔅 fun marks => (𝗬 : 𝙗)
𝗇 𝔇 𝙁
𝗇 𝔈 𝘰
𝗃 𝔚 ἀ dependent hsymm j
𝗇 𝔉 𝔚 historyMarkedAppend
𝗇 𝔊 𝗡₁ g
𝗇 𝔙 𝗠₁
𝗇 𝔍 Fin 𝔙 → E
𝗇 𝔓 𝙗
𝗇 𝔗 historyMarked_measurable_mk dependent g
𝗃 𝔛 (Measure.map (Sigma.mk g) ἀ).prod π
/-- The actual marked reference law on the canonical append fiber is a fresh-mark pushforward. -/
theorem historyMarkedAppend_fiber_map (dependent : 𝔇)
    (hsymm : 𝔄)
    j (g : HistoryShape 𝖴)
    [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    Measure.map 𝔉
      𝔛 𝔈 =
      Measure.map (Sigma.mk 𝔊)
        𝔈 := by
  let ν := Measure.pi fun _ : Fin 𝔙 => π
  let f : 𝔍 × E → 𝔓 :=
    fun p => 𝔚 historyMarkedAppend (⟨g, p.1⟩, p.2)
  have hm : 𝔛 ν =
      Measure.map (Prod.map 𝔅 id) (ν.prod π) := by
    simpa only [Measure.map_id] using
      Measure.map_prod_map ν π 𝔗 measurable_id
  rw [hm, Measure.map_map 𝔚 historyMarkedAppend_measurable
    $ (𝔗).prodMap measurable_id ]
  let m := fun p : 𝔍 × E =>
    𝔚 historyCanonicalMarkAppendEquiv g (p.2, p.1)
  have hp : MeasurePreserving m (ν.prod π)
      𝔈 :=
    (𝔚 historyCanonicalMarkAppendEquiv_preserving g π).comp Measure.measurePreserving_swap
  change Measure.map ((fun marks =>
    (⟨𝔊, marks⟩ : 𝔓)) ∘ m) (ν.prod π) = _
  rw [← Measure.map_map (historyMarked_measurable_mk dependent _) hp.measurable, hp.map_eq]

/-- The actual countable reference component consisting of appended shapes. -/
def historyMarkedTerminalReferenceRaw (dependent : 𝔇)
    (Δ : ℕ) (j : J) [MeasurableSpace E] (π : Measure E) :
    Measure 𝔓 :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ 𝔊) •
    Measure.map (Sigma.mk 𝔊)
      (Measure.pi fun _ : Fin $ historyShapeLength dependent 𝔊 => π )

𝗇 𝔏 𝚊₂
𝗇 𝔑 ENNReal.ofReal $ historyReferenceRho Δ
𝗇 𝔒 (𝔚 historyMarkedAppend_measurable).aemeasurable
𝗃 𝔜 𝔑 • Measure.map 𝔉 ((ἀ).prod π)
𝗇 𝔖 𝔜 𝔏
/-- Exact source rho factor for the actual marked append, derived from both finite mark and shape laws. -/
theorem historyMarkedReferenceRaw_append (dependent : 𝔇)
    (hsymm : 𝔄)
    (Δ : ℕ) j [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    𝔖 =
      historyMarkedTerminalReferenceRaw dependent Δ j π := by
  unfold historyMarkedReferenceRaw historyMarkedTerminalReferenceRaw
  rw [Measure.prod_sum_left, Measure.map_sum 𝔒]
  rw [historyMeasure_smul_sum]
  congr 1
  funext g
  rw [Measure.prod_smul_left, Measure.map_smul, smul_smul,
    historyMarkedAppend_fiber_map, historyShapeReferenceWeight_append,
    ENNReal.ofReal_mul 𝘤]
  exact 𝔒

𝗇 𝔐 𝗡₁
/-- Shapes with a true appended maximal label, including all of their marks. -/
def historyMarkedTerminalSet (dependent : 𝔇) (j : J) :
    Set 𝔓 := {h | h.1 ∈ Set.range 𝔐}

theorem historyMarkedTerminalSet_measurable (dependent : 𝔇) j
    [MeasurableSpace E] : MeasurableSet $ historyMarkedTerminalSet dependent j (E := E) := by
  rw [MeasurableSpace.measurableSet_iInf]
  intro g
  change MeasurableSet {marks : 𝔍 |
    g ∈ Set.range 𝔐}
  simp

omit [Fintype J] [LinearOrder J] in
/-- Reindex a sum of measures on an actual subtype, with zero outside it. -/
theorem historyMeasure_sum_subtype [MeasurableSpace X]
    (S : Set I) [DecidablePred fun i => 𝚒₁ ] (μ : I → Measure X) :
    Measure.sum (fun i => if 𝚒₁ then μ i else 0) = Measure.sum fun i : S => μ i.val := by
  classical
  ext s hs
  simp only [Measure.sum_apply _ hs]
  calc
    _ = ∑' i, if 𝚒₁ then μ i s else 0 := by
      apply tsum_congr
      intro i
      split_ifs <;> rfl
    𝘿 := by simpa [Set.indicator_apply] using (tsum_subtype S fun i => μ i s ).symm

𝗇 𝔎 historyMarkedTerminalSet dependent j
𝗇 𝔔 𝙂
𝗇 𝔘 historyMarkedTerminalSet_measurable dependent j
/-- The append component is exactly the actual reference measure restricted to appended shapes. -/
theorem historyMarkedTerminalReferenceRaw_eq_restrict (dependent : 𝔇)
    (hrefl : 𝔔) (hsymm : 𝔄)
    (Δ : ℕ) j [MeasurableSpace E] (π : Measure E) :
    historyMarkedTerminalReferenceRaw dependent Δ j π =
      (𝔏).restrict 𝔎 := by
  classical
  let G := Set.range 𝔐
  let μ := fun g =>
    ENNReal.ofReal 𝘎₁ •
      Measure.map 𝔅 𝔈
  have hr : ∀ g, (μ g).restrict 𝔎 =
      if g ∈ G then μ g else 0 := by
    intro g
    rw [Measure.restrict_smul, Measure.restrict_map 𝔗
      𝔘]
    have hp : 𝔅 ⁻¹' 𝔎 =
        if g ∈ G then Set.univ else ∅ := by
      ext marks
      aesop
    aesop
  change _ = (Measure.sum μ).restrict _
  rw [Measure.restrict_sum _ 𝔘]
  simp_rw [hr]
  rw [historyMeasure_sum_subtype]
  let e := Equiv.ofInjective 𝔐
    $ historyShapeAppend_injective dependent hrefl hsymm j
  exact Measure.sum_comp_equiv e fun g => μ g.val

𝗃 𝔞 ἀ dependent hrefl hsymm Δ j π
/-- Full marked append/delete change of variables for the actual reference measure. -/
theorem historyMarkedReferenceRaw_append_restrict (dependent : 𝔇)
    (hrefl : 𝔔) (hsymm : 𝔄)
    (Δ : ℕ) j [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    𝔖 =
      (𝔏).restrict 𝔎 :=
  (historyMarkedReferenceRaw_append dependent hsymm Δ j π).trans
    𝔞 historyMarkedTerminalReferenceRaw_eq_restrict

/-- The same exact append change of variables holds for the normalized reference probability. -/
theorem historyMarkedReference_append_restrict (dependent : 𝔇)
    (hrefl : 𝔔) (hsymm : 𝔄)
    (Δ : ℕ) j [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    𝔜 𝙤 =
      (𝙤).restrict 𝔎 := by
  let c := (𝚊₂ Set.univ)⁻¹
  change 𝔑 •
      Measure.map 𝔉 ((c • 𝔏).prod π) =
        (c • 𝔏).restrict _
  rw [Measure.prod_smul_left, Measure.map_smul, Measure.restrict_smul]
  swap
  · exact 𝔒
  rw [smul_smul, mul_comm, ← smul_smul,
    𝔞 historyMarkedReferenceRaw_append_restrict]
