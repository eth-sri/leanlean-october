module

public import NearlyMinimax.DesignCounts
public import NearlyMinimax.HighObservationLaw
public import NearlyMinimax.HighUnionFieldScore
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual iid membership-cell and normalized-design transfers. The
independent count law and unused-observation factors are derived from the
actual product probability experiment. -/
𝚴
𝚳
𝚨
𝚩
𝚭
𝚬

𝗇 𝔙 {i : Fin n // i ∉ S}
𝗇 𝔄 fun _ : 𝔙 => μ.restrict Aᶜ
𝗇 𝔛 𝘫
𝗇 𝔅 Measure.pi 𝔛
𝗇 𝔇 𝘯₁
𝗃 𝔟 if ἀ ∈ S then A else Aᶜ
𝗇 𝔚 𝔟 i
𝗇 𝔈 fun i => μ.restrict 𝔚
𝗇 𝔉 fun i => 𝚒₁
𝗇 𝔊 designMembershipCell n A S
𝗇 𝔍 fun i => x i.val
𝗇 𝔎 fun _ : S => μ.restrict A
𝗇 𝔐 𝙍
𝗇 𝔑 𝔙
𝗇 𝔒 μ.real Aᶜ ^ (n - S.card)
𝗇 𝔓 (𝔅).restrict 𝔊
𝗇 𝔔 ∫ z, H z ∂𝔇
𝗇 𝔖 fun i => μi i.val
𝗇 𝔗 (S → α) → ℝ
𝗇 𝔘 Subtype.fintype 𝔉 = Finset.Subtype.fintype S
𝗃 𝔜 ∫ x in 𝔊, H ἀ ∂𝔅
/-- Exact selected-coordinate integral on an actual membership cell.
No independence or binomial-weight premise is supplied. -/
theorem iid_selected_membership_integral [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] n A
    (S : 𝔐) (H : 𝔗) :
    𝔜 𝔍 =
      𝔒 *
        𝔔 := by
  let μi := 𝔈
  have hm : 𝔓 = Measure.pi μi :=
    Measure.restrict_pi_pi 𝔛 fun i => 𝔚
  have hs := measurePreserving_piEquivPiSubtypeProd μi 𝔉
  have hι : 𝔘 := Subsingleton.elim ..
  rw [hι] at hs
  have he := hs.integral_comp' fun z => H z.1
  change ∫ x, H 𝔍 ∂Measure.pi μi = _ at he
  rw [hm, he]
  have hin : 𝔖 = 𝔎 := by
    grind
  have hout : 𝔖 =
      𝔄 := by
    grind
  rw [hin, hout]
  have hint := integral_prod_mul (μ := 𝔇)
    (ν := Measure.pi 𝔄) H 𝙃
  simp only [mul_one] at hint
  have hcard : Fintype.card 𝔑 = n - S.card := by
    simp
  calc
    _ = 𝔔 *
       ∫ z : 𝔑 → α, 1 ∂Measure.pi fun _ => μ.restrict Aᶜ := hint
    𝘿 := by
      rw [integral_const, smul_eq_mul, mul_one]
      simp only [Measure.real, Measure.pi_univ, Measure.restrict_apply_univ,
        Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow, hcard]
      ring

𝗃 𝔞 ∫ x, ἀ x ∂𝔅
/-- Every measurable iid patch admits the true disjoint membership-cell
partition of an integrable data function. -/
theorem iid_integral_eq_membership_sum [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] n A (hA : MeasurableSet A)
    (H : 𝚅₁ → ℝ) (hH : Integrable H 𝔅) :
    𝔞 H =
      ∑ S : 𝔐, 𝔜 x := by
  have hcover : ⋃ S : 𝔐, 𝔊 = univ := by
    apply Set.eq_univ_of_forall
    intro x
    apply Set.mem_iUnion.mpr
    refine ⟨Finset.univ.filter fun i => x i ∈ A , ?_⟩
    rw [design_membership_cell_iff]
    simp
  rw [← setIntegral_univ, ← hcover]
  exact integral_iUnion_fintype ( design_membership_cell_measurable n A hA )
    (design_membership_cells_disjoint n A) fun S => hH.integrableOn

𝗇 𝔏 fun i => μ.restrict 𝔟 i.val
/-- Conditional iid energy is bounded by the actual selected-observation
energies; the unused-observation probability is bounded by one. -/
theorem iid_local_energy_le_selected_sum [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] n A (hA : MeasurableSet A)
    E (hE : Integrable E 𝔅)
    (H : (S : 𝔐) → 𝔗)
    (hH : ∀ S, Integrable (H S) 𝔇)
    (hHn : ∀ S z, 0 ≤ H S z)
    (hdom : ∀ S x, x ∈ 𝔊 → E x ≤ H S 𝔍) :
    𝔞 E ≤
      ∑ S : 𝔐, ∫ z, H S z ∂Measure.pi 𝔎 := by
  rw [iid_integral_eq_membership_sum μ n A hA E hE]
  apply Finset.sum_le_sum
  intro S hS
  have hm : 𝔓 =
      Measure.pi 𝔈 :=
    Measure.restrict_pi_pi ..
  have hs := measurePreserving_piEquivPiSubtypeProd
    𝔈 𝔉
  have hι : 𝔘 := Subsingleton.elim ..
  rw [hι] at hs
  have hp : Integrable (fun z => H S z.1)
      $ (𝔇).prod
        $ Measure.pi 𝔄 := by
    have hh := (hH S).mul_prod $ integrable_const 1
      (μ := Measure.pi 𝔄)
    simp_all
  have hselected : Integrable (fun x => H S 𝔍)
      𝔓 := by
    rw [hm]
    have hin : 𝔏 =
        𝔎 := by
      simp
    have hout : 𝔏 =
        𝔄 := by
      grind
    rw [hin, hout] at hs
    have hh := (hs.integrable_comp_emb (MeasurableEquiv.piEquivPiSubtypeProd (fun _ => α)
      𝔉).measurableEmbedding).mpr hp
    assumption

  calc
    _ ≤ ∫ x in 𝔊, H S 𝔍 ∂𝔅 := by
      apply integral_mono_ae hE.integrableOn hselected
      filter_upwards [ae_restrict_mem $ design_membership_cell_measurable n A hA S ] with x hx
      simp_all
    _ = 𝔒 * ∫ z, H S z ∂𝔇 :=
      iid_selected_membership_integral μ n A S $ H S
    𝖦 := by
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ measureReal_nonneg measureReal_le_one) $ integral_nonneg $ hHn S ).trans_eq $ one_mul _
