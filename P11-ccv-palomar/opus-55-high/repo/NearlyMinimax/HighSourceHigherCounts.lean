module

public import NearlyMinimax.HighSourceCountCancellation
public import RoughRegime.Macro
public import RoughRegime.Notation

public section

/-! The complete source's higher-count first action: ordinary pair and
singleton selectors vanish, leaving the actual higher family plus the
fine-pair alias and even field actions. -/
𝚫
𝚨
𝚬

𝗇 𝔍 𝙔
𝗇 𝔑 𝖬₂
𝗇 𝔒 𝖠₁
section Pair
variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]

𝗇 𝔓 ψ ζ i
𝗇 𝔅 fun ζ z eps => ∏ i, localDensityReset a b 2 z eps p (fun i _ => 𝔓) i
𝗃 𝔖 ἀ σ a b m 2 D q C A
theorem ordinaryPairPacket_zero_other_count (hn : 𝔑)
    (σ : Measure Z) [IsFiniteMeasure σ] a b (ha : 𝙆) (hab : 𝙭)
    m D q (hnm : n ≤ m) (hnD : 𝔒) C
    A (hA : 𝙚)
    (hcost : 𝙧) (c : 𝙛)
    p (hp : ∀ i, p i ∈ 𝘔₂) (ψ : Z → 𝔍)
    (hmψ : ∀ i, Measurable fun ζ => 𝔓 ) (hbψ : ∀ ζ i, |𝔓| ≤ 1)
    Φ :
     ∫ᵛ e, highPacketObservable a b m 2 D q C c
      𝔅 Φ e
      ∂<•𝔖 highPacketSignedMeasure = 0 := by
  rw [𝔖 highPacketSignedMeasure_factor_integral hA hcost c
    𝔅
    (fun z eps => Finset.measurable_fun_prod _ fun i _ => ordinaryPairReset_measurable a b p ψ hmψ z eps i )
    (b^n) (pow_nonneg 𝙬₁ n)
    (fun ζ e => finite_density_product_abs_bound _ b 𝙬₁
      $ ordinaryPairReset_atom_abs_le a b ha hab m D p hp (ψ ζ) (hbψ ζ) e )
    Φ (finePairResponseAtomBound q C c Φ) $ finePairResponseAtomBound_le q C c Φ ]
  have hh := highSeparatedPacketAction_count_selector σ a b ha hab m 2 D q
     𝖡₃   𝖡₃  Finset.univ (by simpa using hnD)
    (by simpa using hnm) (by simpa using 𝖡₃ ) p
    (fun ζ i _ => 𝔓) (fun i _ => hmψ i) (fun ζ i _ => hbψ ζ i) C A hA hcost c Φ
  aesop

end Pair

𝗃 𝔔 ἀ ad bd ℓ N M q C U p c
𝗇 𝔇 𝔔 finePairPairAliasAction
𝗇 𝔈 𝔔 finePairEvenFieldAction
𝗇 𝔉 𝖳
𝗇 𝔐 𝙮 → ℝ
theorem finePairThreeRowFirstAction_higher [NeZero d]
    (hn : 𝔑) (hnD : 𝔒) ad bd ℓ N (ha : 𝖼) (hab : 𝖽)
    M q C U (p : 𝔍)
    (hp : 𝔉) (c : 𝔐)
    Φ :
    finePairThreeRowFirstAction ad bd ℓ N D M q C U p c Φ =
      𝔇 Φ +
        𝔈 Φ := by
  have hu : finePairUnitFirstAction ad bd D q C p c Φ = 0 :=
    ordinaryPairPacket_zero_other_count hn 𝖶₁ ad bd ha hab D D q hnD hnD C
      𝗻 𝗱 (integrable_const _) c p hp
      𝘞 (fun _ => measurable_const)  𝖢₄  Φ
  have hc : finePairCoarseFirstAction ad bd ℓ D q C U p c Φ = 0 :=
    ordinaryPairPacket_zero_other_count hn _ ad bd ha hab D D q hnD hnD C _
      𝖼₂ (finePairTimeMatrix_cost_integrable d 0 ℓ _) c p hp
      (fun ζ i => finePairTimeFieldValue ζ $ U i )
      (fun i => 𝖻₂)
      𝗀₁ Φ
  rw [finePairThreeRowFirstAction, hu, hc,
    finePairFineFirstAction_alias_even_field ad bd ℓ N ha hab M q C U p hp c Φ]
  ring

𝗃 𝔏 ἀ ad bd lam ℓ N μ D M q C
𝗇 𝔊 𝔏 higherBandFamilyFirstAction U p c
theorem completeSourceSignedFirstAction_higher [NeZero d]
    (ad bd lam ℓ N μ : ℝ) (ha : 𝖼) (hab : 𝖽)
    (D M q : ℕ) (hn : 𝔑) (hnD : 𝔒) C
    U (p : 𝔍) (hp : 𝔉)
    (c : 𝔐) Φ :
    𝔏 completeSourceSignedFirstAction U p c Φ =
      𝔊 Φ +
        𝔇 Φ +
        𝔈 Φ := by
  rw [completeSourceSignedFirstAction_eq_family,
    singletonFirstAction_zero_other_count ad bd ha hab D q  𝖡₃  hnD  𝖡₃  C p hp c Φ,
    finePairThreeRowFirstAction_higher hn hnD ad bd ℓ N ha hab M q C U p hp c Φ]
  ring

𝗇 𝔎 𝙬
𝗇 𝔄 fun v => 𝖨 𝔎 v y
theorem completeSourceRawNumerator_higher [NeZero d]
    (ad bd lam ℓ N μ : ℝ) (ha : 𝖼) (hab : 𝖽)
    (D M q : ℕ) (hn : 𝔑) (hnD : 𝔒) C a V η
    U (p g w : 𝔍) (hp : 𝔉)
    (c : 𝔐) y :
    𝔏 completeSourceRawNumerator a V η U p g w c y =
      𝔊
        𝔄 +
      𝔇
        𝔄 +
      𝔈
        𝔄 -
      𝙎 * 𝗊 * ∑ i, 𝖩 *
        𝖷 𝔎 c y i := by
  unfold completeSourceRawNumerator
  rw [completeSourceSignedFirstAction_higher ad bd lam ℓ N μ ha hab D M q hn hnD C U p hp c]
