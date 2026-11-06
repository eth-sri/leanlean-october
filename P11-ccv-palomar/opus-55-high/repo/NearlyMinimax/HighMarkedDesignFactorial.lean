module

public import NearlyMinimax.HighMarkedResponseEnergy
public import NearlyMinimax.SpatialSubsetEnergy
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The complete marked generator under its actual iid normalized design.
The factorial series contains genuine raw numerator integrals over the
selected patch observations; no local or global target budget is assumed. -/
𝚴
𝚮
𝚨
𝚩
𝚭
𝚬

𝗇 𝔈 𝙍
𝗇 𝔊 𝘯₁
𝗇 𝔔 designMembershipCell n A S
section

variable [MeasurableSpace α]
    (μ : Measure α)
    [IsProbabilityMeasure μ]
    (n)
    (A)

𝗇 𝔎 Measure.pi 𝘫
𝗃 𝔮 fun i => μ.restrict $ if ἀ ∈ S then A else Aᶜ
𝗇 𝔏 𝔮 i.val
𝗇 𝔛 fun i => 𝚒₁
𝗇 𝔦 fun i => x i.val
𝗇 𝔬 (S → α) → ℝ
theorem iid_cell_selected_integrable (S : 𝔈) (H : 𝔬)
    (hH : Integrable H 𝔊) :
    IntegrableOn (fun x => H 𝔦)
      𝔔 𝔎 := by
  rw [IntegrableOn, designMembershipCell, Measure.restrict_pi_pi]
  have hs := measurePreserving_piEquivPiSubtypeProd
    𝔮 i 𝔛
  have hι : Subtype.fintype 𝔛 = Finset.Subtype.fintype S := Subsingleton.elim ..
  rw [hι] at hs
  have hin : 𝔏 =
       fun _ : S => μ.restrict A := by
    simp
  have hout : 𝔏 =
       fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ := by
    grind
  rw [hin, hout] at hs
  have hh := hs.integrable_comp_of_integrable $ hH.comp_fst _
  exact hh

𝗇 𝔟 ⋃ S : 𝔈, 𝔔
theorem iid_energy_integrable_of_selected (hA : MeasurableSet A)
    E (H : (S : 𝔈) → 𝔬)
    (hH : ∀ S, Integrable (H S) 𝔊)
    (he : ∀ S x, x ∈ 𝔔 → E x = H S 𝔦) :
    Integrable E 𝔎 := by
  have hcover : 𝔟 = univ := by
    apply Set.eq_univ_of_forall
    intro x
    apply Set.mem_iUnion.mpr
    refine ⟨Finset.univ.filter fun i => x i ∈ A , ?_⟩
    rw [design_membership_cell_iff]
    simp
  have hi : IntegrableOn E 𝔟
      𝔎 := by
    apply integrableOn_finite_iUnion.mpr
    intro S
    have hsel := iid_cell_selected_integrable μ n A S (H S) $ hH S
    apply hsel.congr
    filter_upwards [ae_restrict_mem $ design_membership_cell_measurable n A hA S ] with x hx
    grind
  simp_all

end

section
𝛣

𝗇 𝔍 𝙛
𝗇 𝔐 𝘬
def highMarkedResponseMass (a V η : ℝ) (g w : 𝔐) (φ : α → 𝔍)
    (c : 𝔍) (x : α) (y : Fin 3) : ℝ :=
  ternaryMass a (g x + η * w x * ∑ γ, φ x γ * c γ) V y

𝗃 𝔥 ἀ ∘ x
𝗇 𝔖 𝔥 g
𝗇 𝔗 𝔥 w
𝗇 𝔘 𝔥 φ
𝗇 𝔭 fun z => pReset z ∘ x
𝗇 𝔚 𝔭
𝗃 𝔤 ἀ $ x i
def highMarkedSampleNumerator (r : ℕ) (π : Measure E) (activation : 𝙏)
    (a V η : ℝ) (p : 𝔐) (pReset : E → 𝔐) (cReset : E → 𝔍)
    (g w : 𝔐) (φ : α → 𝔍) (c : 𝔍)
    (x : Fin r → α) (y : Fin r → Fin 3) : ℝ :=
  highMarkedResponseAction π activation a V η 𝔚 cReset
    𝔖 𝔗 𝔘 y - 𝙎 * (∏ i, 𝔤 p) *
      ∑ i, 𝔤 w ^ 2 * highResponseVarianceTerm a V η 𝔖 𝔗 𝔘 c y i

𝗃 𝔣 ἀ r π activation a V η p pReset cReset g w φ c
𝗇 𝔢 𝔣 highMarkedSampleNumerator
𝗇 𝔄 𝔢
𝗇 𝔡 highMarkedResponseMass a V η g w φ c
𝗇 𝔉 𝔡
def highMarkedSampleConditionalEnergy (r : ℕ) (π : Measure E) (activation : 𝙏)
    (a V η : ℝ) (p : 𝔐) (pReset : E → 𝔐) (cReset : E → 𝔍)
    (g w : 𝔐) (φ : α → 𝔍) (c : 𝔍) (x : Fin r → α) : ℝ :=
  selectedConditionalScoreEnergy p 𝔉
    𝔄 x

𝗇 𝔇 highMarkedLocalScore π activation a V η 𝔥 p 𝔭 cReset 𝔥 g 𝔥 w 𝔥 φ c y
𝗇 𝔒 𝔢 x y
theorem high_marked_sample_score_eq_ratio r (π : Measure E) activation
    a V η p pReset cReset
    (g w : 𝔐) φ (c : 𝔍) x y :
    𝔇 =
    𝔒 /
      selectedRawLikelihood p 𝔉 x y := rfl

𝗇 𝔓 ∀ z y, 0 < 𝔡 z y
𝗇 𝔞 𝔣 highMarkedSampleConditionalEnergy
theorem high_marked_sample_energy_integral r (π : Measure E) activation
    a V η ha p pReset cReset
    (g w : 𝔐) φ (c : 𝔍) x
    (hp : 𝔓) :
    (∫ y, 𝔇 ^ 2
      ∂Measure.pi fun i => ternaryIndexMeasure a
        (coefficientRegression η 𝔖 𝔗 𝔘 c i) V ha fun y => (𝔤 hp y).le ) =
    𝔞 x := by
  rw [ternary_index_product_integral]
  unfold highMarkedSampleConditionalEnergy selectedConditionalScoreEnergy
  simp_rw [← 𝔣 high_marked_sample_score_eq_ratio x]
  apply Finset.sum_congr 𝖤₃
  bound

def selectedDesignEnumeration (S : 𝔈) : Fin S.card ≃ S :=
  (S.orderIsoOfFin rfl).toEquiv

def selectedDesignEmbedding (S : 𝔈) : Fin S.card ↪ Fin n :=
  (S.orderEmbOfFin rfl).toEmbedding

𝗇 𝔧 Finset.univ.map $ selectedDesignEmbedding S
theorem selected_design_embedding_map (S : 𝔈) :
    𝔧 = S := Finset.map_orderEmbOfFin_univ S rfl

𝗃 𝔰 highMarkedSampleConditionalEnergy ἀ π activation a V η p pReset cReset g w φ c
𝗇 𝔠 𝔰 n
𝗇 𝔙 𝔠 x
𝗇 𝔩 x ∘ selectedDesignEmbedding S
𝗃 𝔯 high_marked_sample_energy_integral ἀ π activation a V η ha p pReset cReset g w φ c
theorem high_marked_sample_energy_cell_selected (A : Set α)
    S x (hx : x ∈ 𝔔)
    (π : Measure E) activation a V η (ha : 𝙞)
    p pReset cReset
    g w φ (c : 𝔍)
    (hpd : ∀ z, p z ≠ 0) (hp : 𝔓)
    (hw : ∀ z, z ∉ A → w z = 0) (hReset : ∀ e z, z ∉ A → pReset e z = p z) :
    𝔙 =
      𝔰 S.card
        𝔩 := by
  have hmem := design_membership_cell_iff n A S x |>.mp hx
  have hwo i (hi : i ∉ 𝔧) : 𝔤 w = 0 := by
    rw [selected_design_embedding_map] at hi
    simp_all
  have hro e i (hi : i ∉ 𝔧) :
      pReset e (x i) = 𝔤 p := by
    rw [selected_design_embedding_map] at hi
    simp_all
  have he := high_marked_selected_response_energy (selectedDesignEmbedding S) π activation a V η ha
    𝔥 p 𝔚 cReset 𝔖 𝔗 𝔘 c
    (fun i => 𝔤 hpd) (fun i y => 𝔤 hp y) hwo hro
  rw [𝔯 n x hp] at he
  have hs := 𝔯 S.card 𝔩 hp
  aesop

𝗇 𝔅 ν.withDensity fun x => ENNReal.ofReal $ p x / m
𝗇 𝔑 Measure.pi fun _ => ν.restrict A
𝗇 𝔜 𝔡 x y
𝗇 𝔨 Measure.pi fun _ => 𝔅
𝗇 𝔪 ∫ x, selectedRawSquareEnergy 𝔄 x ∂ 𝔑
𝗇 𝔫 F S.card $ z ∘ selectedDesignEnumeration S
𝗃 𝔱 ἀ (μ.restrict A) (selectedDesignEnumeration S).symm $ F S.card
𝗃 𝔲 ἀ μ n A hA $ F n
theorem high_marked_design_raw_factorial_series (ν : Measure α) [IsProbabilityMeasure ν]
    n A (hA : MeasurableSet A) m pMinus cMass
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hm : pMinus ≤ m)
    (π : Measure E) activation a V η (ha : 𝙞)
    p (hpMeas : Measurable p) pReset cReset
    g w φ (c : 𝔍)
    (hqMeas : ∀ y, Measurable fun x => 𝔜 )
    (hprob : IsProbabilityMeasure 𝔅)
    (hpd : ∀ x, pMinus ≤ p x)
    (hp : ∀ x y, cMass ≤ 𝔜)
    (hw : ∀ x, x ∉ A → w x = 0) (hReset : ∀ e x, x ∉ A → pReset e x = p x)
    (hRMeas : ∀ r y, Measurable fun x => 𝔒 )
    (hRaw : ∀ r, Integrable (selectedRawSquareEnergy
      𝔄)
        𝔑) :
    Integrable 𝔠
      𝔨 ∧
     ∫ x, 𝔙
      ∂𝔨 ≤
      ∑ r ∈ Finset.range 𝗉,
        (n * highFixedScoreDenominator pMinus cMass) ^ r / r.factorial *
          𝔪 := by
  let μ := 𝔅
  let _ := hprob
  let F r := 𝔞
  let H (S : 𝔈) z := 𝔫
  let J r := 𝔪
  have hp0 x := (hpMinus.trans_le $ hpd x ).ne'
  have hq0 x y := hcMass.trans_le $ hp x y
  have hFI r := normalized_selected_score_energy_integrable_bound ν A hA m pMinus cMass
    hpMinus hcMass hm p hpMeas 𝔉 hqMeas
    𝔄 (hRMeas r) hprob
    (fun x _ => hpd x) (fun x _ y => hp x y) $ hRaw r
  have hHI (S : 𝔈) :=
    𝔱 finite_pi_reindex_integrable (hFI S.card).1
  have hEq S (x : 𝚅₁) hx :=
    high_marked_sample_energy_cell_selected A S x hx π activation a V η ha p pReset cReset
      g w φ c hp0 hq0 hw hReset
  have hFn :=
    𝔲 iid_energy_integrable_of_selected H hHI hEq
  refine ⟨hFn, ?_⟩
  apply 𝔲 iid_local_energy_le_factorial_spatial_series hFn H hHI
    (fun S z => selected_conditional_score_energy_nonneg p 𝔉
      (fun x y => (hq0 x y).le) ..) (fun S x hx => (hEq S x hx).le)
    (highFixedScoreDenominator pMinus cMass) (high_fixed_score_denominator_pos hpMinus hcMass).le J
     fun r => integral_nonneg fun x => Finset.sum_nonneg fun y _ => sq_nonneg _
  intro S
  have he : ∫ z, 𝔫 ∂ 𝔊 =
      ∫ z, F S.card z ∂ 𝔊 :=
    𝔱 finite_pi_reindex_integral
  rw [he]
  have hs := (hFI S.card).2
  simp at hs
  assumption
