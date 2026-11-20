module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalFields.ValuationShellMeasure

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain ValuativeRel
open KPLocalExceptionalConstruction KPLocalPrincipalSeries
variable (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))

local notation "LocalCompletion" => LocalField F q

private theorem abs_bound (m : ℤ) (x : LocalCompletion) :
    KPCubicHaar.abs LocalCompletion x ≤ (residueCardinality LocalCompletion : ℝ) ^ m ↔
    valuation LocalCompletion x ≤
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion).symm (WithZero.exp m) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion
  have hq : (1 : ℝ) < residueCardinality LocalCompletion := by
    exact_mod_cast (Finite.one_lt_card)
  by_cases hx : x = 0
  · simp [hx, (zpow_pos (lt_trans zero_lt_one hq) m).le]
  simp only [KPCubicHaar.abs, if_neg hx]
  change (residueCardinality LocalCompletion : ℝ) ^ WithZero.log (e (valuation LocalCompletion x)) ≤
    (residueCardinality LocalCompletion : ℝ) ^ m ↔ _
  rw [zpow_le_zpow_iff_right₀ hq]
  rw [← e.toOrderIso.le_iff_le]
  change _ ↔ e (valuation LocalCompletion x) ≤ e (e.symm (WithZero.exp m))
  rw [e.apply_symm_apply]
  conv_rhs => rw [← WithZero.exp_log ((map_ne_zero e).mpr ((valuation LocalCompletion).ne_zero_iff.mpr hx))]
  exact WithZero.exp_le_exp.symm

private theorem core_compact (m : ℤ) : IsCompact {x : LocalCompletion | KPCubicHaar.abs LocalCompletion x ≤
    (residueCardinality LocalCompletion : ℝ) ^ m} := by
  simp_rw [abs_bound]
  exact IsNonarchimedeanLocalField.isCompact_closedBall _ _

private theorem outer_closed (m : ℤ) : IsClosed {x : LocalCompletion | (residueCardinality LocalCompletion : ℝ) ^ (m - 1) < KPCubicHaar.abs LocalCompletion x} := by
  have he : {x : LocalCompletion | (residueCardinality LocalCompletion : ℝ) ^ (m - 1) < KPCubicHaar.abs LocalCompletion x} =
      {x : LocalCompletion | valuation LocalCompletion x ≤
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion).symm (WithZero.exp (m - 1))}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le, ← abs_bound F q]
  rw [he]
  apply IsOpen.isClosed_compl
  obtain ⟨a, ha⟩ := valuation_surjective
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion).symm (WithZero.exp (m - 1)))
  rw [← ha]
  simp_rw [← (valuation LocalCompletion).restrict_le_iff]
  apply Valuation.isOpen_closedBall
  have hnon : valuation LocalCompletion a ≠ 0 := by rw [ha]; simp
  exact (map_ne_zero (valuation LocalCompletion).restrict).mpr
    ((valuation LocalCompletion).ne_zero_iff.mp hnon)

theorem actual_shell_compact_partition (M : ℕ) :
    let B : Set LocalCompletion :=
      {x | KPCubicHaar.abs LocalCompletion x ≤
        (residueCardinality LocalCompletion : ℝ) ^ ((M : ℤ) - 1)}
    IsCompact B ∧ MeasurableSet B ∧
      (∀ m : ℤ, IsCompact (actualShell F q m) ∧ MeasurableSet (actualShell F q m)) ∧
      Disjoint B (⋃ n : ℕ, actualShell F q ((M + n : ℕ) : ℤ)) ∧
      B ∪ (⋃ n : ℕ, actualShell F q ((M + n : ℕ) : ℤ)) = Set.univ := by
  dsimp only
  have hq : (1 : ℝ) < residueCardinality LocalCompletion := by
    exact_mod_cast (Finite.one_lt_card)
  have hB := core_compact F q ((M : ℤ) - 1)
  refine ⟨hB, hB.measurableSet, ?_, ?_, ?_⟩
  · intro m
    have hc : IsCompact (actualShell F q m) := by
      simpa only [actualShell, Set.setOf_and, Set.inter_comm] using
        (core_compact F q m).inter_right (outer_closed F q m)
    exact ⟨hc, hc.measurableSet⟩
  · rw [Set.disjoint_left]
    intro x hx ht
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ht
    exact (not_lt_of_ge (hx.trans ((zpow_le_zpow_right₀ hq.le (by omega))))) hn.1
  · apply Set.eq_univ_of_forall
    intro x
    by_cases hx : KPCubicHaar.abs LocalCompletion x ≤
        (residueCardinality LocalCompletion : ℝ) ^ ((M : ℤ) - 1)
    · exact Or.inl hx
    · apply Or.inr
      have hx0 : x ≠ 0 := by
        intro he
        apply hx
        simp [he, (zpow_pos (lt_trans zero_lt_one hq) ((M : ℤ) - 1)).le]
      let j := WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion
        (valuation LocalCompletion x))
      have habs : KPCubicHaar.abs LocalCompletion x =
          (residueCardinality LocalCompletion : ℝ) ^ j := by
        simp only [KPCubicHaar.abs, if_neg hx0]
        rfl
      have hj : (M : ℤ) ≤ j := by
        rw [habs, zpow_le_zpow_iff_right₀ hq] at hx
        omega
      let n := (j - M).toNat
      have hn : ((M + n : ℕ) : ℤ) = j := by
        dsimp [n]
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      apply Set.mem_iUnion.mpr
      refine ⟨n, ?_⟩
      change _ < KPCubicHaar.abs LocalCompletion x ∧ KPCubicHaar.abs LocalCompletion x ≤ _
      rw [hn, habs]
      exact ⟨(zpow_lt_zpow_iff_right₀ hq).mpr (by omega), le_rfl⟩

end DedekindZetaZeroFree.KPRankOneShellRepair

end
