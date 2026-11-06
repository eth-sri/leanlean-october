module

public import Mathlib
public import RoughRegime.Macro

@[expose] public section

open scoped MeasureTheory ENNReal ProbabilityTheory Topology Matrix RealInnerProductSpace NNReal BigOperators
set_option hygiene false
𝗀 𝔸 ∀ ⦃i j⦄, dependent i j → dependent j i
𝗀 𝔹 ∀ j, (dependentLabelFinset dependent j).card ≤ Δ
𝗀 𝔺 historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i) (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)
𝗀 𝔻 _ = _
notation "𝙀" => Covariate d → ℝ
𝗀 𝔽 J → J → Prop
𝗀 𝔾 ∀ j, dependent j j
𝗀 𝔿 fun _ => 1
𝗀 𝕀 ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw
𝗀 𝕁 ternaryMass a (F ω x)
𝗀 𝕂 0 < a
𝗀 𝕃 Fin n → Covariate d
𝗀 𝕄 Fin n → Fin 3
𝗀 𝕆 (d : ℝ)
𝗀 𝕇 (0 : ℝ)
𝗀 𝕈 Fin n → Observation d
𝗀 𝕉 Finset (Fin n)
𝗀 𝕊 η^2
𝗀 𝕋 E → ℝ
𝗀 𝕌 0 ≤ B
𝗀 𝕍 0 ≤ Ba
𝗀 𝕎 (n : ℝ)
𝗀 𝕏 0 < aRaw
𝗀 𝕐 Fin n → ℝ
𝗀 𝕑 highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw (Eventually.of_forall (hraw ω))
𝗀 𝕒 1 / 2
𝗀 𝕓 HistoryMarked dependent E
𝗀 𝕔 1 ≤ Δ
𝗀 𝕕 fun ω => highRawDensityMass (p ω)
𝗀 𝕖 ∀ i j, Measurable (fun ζ => A ζ i j)
𝗀 𝕗 ι → ℝ
𝗀 𝕘 ℕ → ℝ
𝗀 𝕙 J → ℝ
𝗀 𝕚 a ≠ 0
𝗀 𝕜 (1 : ℝ)
𝗀 𝕝 -(t * lam * spatialSquaredDistance x y)
𝗀 𝕞 ((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
𝗀 𝕟 MvPolynomial (Fin d) ℝ
𝗀 𝕠 historyMarkedReference dependent Δ π
𝗀 𝕡 1 / (2 + 8 * Δ ^ 2)
𝗀 𝕣 Integrable (separatedMatrixCost A) σ
𝗀 𝕤 highRawDensityMass_joint_measurable p hp
𝗀 𝕅 (2 : ℝ)
𝗀 𝕛 Admissible C θ
𝗀 𝕢 (k : ℝ)
𝗀 𝕥 Covariate d × Covariate d
𝗀 𝕦 ∀ i, MeasurableSpace (E i)
𝗀 𝕧 (Real.exp_pos _).le
𝗀 𝕨 fun i => highFrameFeature (U i)
𝗀 𝕩 a < b
𝗀 𝕪 HighFrameIndex d D
𝗀 𝕫 HighWindowLabels d k
𝗀 𝒜 completeSourceRows_guards C k D M q hD hq hM Cfr lam
𝗀 𝒝 ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b
𝗀 𝒞 fun _ _ => abs_nonneg _
𝗀 𝒠 T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)
𝗀 𝒡 (2) ^ d
𝗀 𝒢 _ ≤ _
𝗀 𝒣 (M : ℝ)
𝗀 𝒤 highResponseProduct a V η g w
𝗀 𝒥 (w i)^2
𝗀 𝒦 volume.restrict (spatialPatchBox d)
𝗀 𝒧 fun i j => j ∈ highNeighborLabels d k i
𝗀 𝒨 (a + b) / (b - a)
𝗀 𝒩 ∀ i, StandardBorelSpace (E i)
𝗀 𝒪 (x, y)
notation "𝖯" => (highUnionSourceState C R h).2
𝗀 𝒬 0 < k
𝗀 𝒭 (designLaw θ).prod (designLaw θ)
𝗀 𝒮 HighFrameIndex d F → ℝ
𝗀 𝒯 ∀ i, p i ∈ Icc ad bd
𝗀 𝒰 fun a b => ¬ dependent a b
𝗀 𝒱 2 * q + 2
𝗀 𝒲 (observationLaw θ).prod (observationLaw θ)
𝗀 𝒳 highResponseVarianceTerm a V η g w
𝗀 𝒴 fun _ => sq_nonneg _
𝗀 𝒵 1 ≤ T
𝗀 𝒶 0 ≤ lam
𝗀 𝒷 completeSourceRows C k D M q Cfr
𝗀 𝒸 0 < ad
𝗀 𝒹 ad < bd
𝗀 𝒺 fun _ => 0
𝗀 𝒻 cf*k^(-C.smoothness)
𝗀 𝒼 I → Type*
𝗀 𝒾 pow_le_pow_left₀ (abs_nonneg _)
𝗀 𝒿 Icc (0) 1
𝗀 𝓀 (2/k)^d
𝗀 𝓁 a ^ 2
𝗀 𝓂 0 < d
𝗀 𝓄 n - 1
𝗀 𝓅 n+1
𝗀 𝓆 ∏ i, p i
𝗀 𝓇 k ^ d
𝗀 𝓈 x ∈ unitCube d
𝗀 𝓉 ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b
𝗀 𝓊 AnchoredIndex d ℓ
𝗀 𝓋 2 ≤ n
𝗀 𝓌 N*Real.exp (-c0*D)
𝗀 𝓍 4 ≤ k
𝗀 𝓎 lintegral_prod_eq_prod_lintegral_of_indepFun _ _ (iIndepFun_pi (fun i => (hG i).aemeasurable)) (fun i => (hG i).comp (measurable_pi_apply i))
𝗀 𝓏 Fin p → ℝ
𝗀 𝓐 responseMatrixAction q C
𝗀 𝓑 3 ≤ D
𝗀 𝓒 (r : ℕ) → (Fin r → Covariate d) → ℝ
𝗀 𝓓 HighUnionSourceGuards C M Cfr R
𝗀 𝓔 1 ≤ q
𝗀 𝓕 1/M
𝗀 𝓖 1 ≤ n
𝗀 𝓗 highUnionLaw R (highCenterMix C)
𝗀 𝓘 (2) ^ j
𝗀 𝓙 2 ^ d
𝗀 𝓚 3 / 2
𝗀 𝓛 (2 : ℕ)
𝗀 𝓜 2*ρ+a
notation "𝗡" => coefficientRegression η g w
𝗀 𝓞 Fin r → ℝ
𝗀 𝓟 anchoredDimension d C.order
𝗀 𝓠 abs_of_nonneg (sq_nonneg _)
𝗀 𝓡 n - 2
𝗀 𝓢 (4 : ℝ)
𝗀 𝓣 ∀ i, μ.real (label ⁻¹' {i}) ≤ cap
𝗀 𝓤 ∀ x y, 0 ≤ ternaryMass a (F x) V y
𝗀 𝓥 η^4
𝗀 𝓦 abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))
𝗀 𝓧 lowerSaddleM m x
𝗀 𝓨 ⟨g, marks⟩
𝗀 𝓩 ∀ᵐ w ∂cubeVolume d, a ≤ q w ∧ q w ≤ b
𝗀 𝓪 1 ≤ D
𝗀 𝓫 J + 1
𝗀 𝓬 Observation d × Observation d
𝗀 𝓭 fun _ _ => measurable_const
𝗀 𝓮 Matrix (Fin r) (Fin r)
𝗀 𝓯 C⁻¹
𝗀 𝓰 Measurable (Function.uncurry F)
𝗀 𝓲 1+Real.log T
𝗀 𝓳 sampleLaw θ n
𝗀 𝓴 eta^4
𝗀 𝓵 1 ≤ Cfr
𝗀 𝓶 Icc 0 T
𝗀 𝓷 fun _ => finePairUnitMatrix d D
𝗀 𝓸 0 ≤ η
𝗀 𝓹 HighUnionRowData d k F I E
𝗀 𝓺 highUnionActivation R (highCenterMix C)
𝗀 𝓻 ∀ i, MeasurePreserving (X i) ν μ
𝗀 𝓼 ∀ y, 0 ≤ ternaryMass a f V y
𝗀 𝓽 finePairResponseActionBudget d q C a ρ
𝗀 𝓾 fun _ : Fin n => cubeVolume d
𝗀 𝓿 ∀ u, 0 ≤ ternaryMass a f V u
𝗀 𝔀 Ω → ℝ
𝗀 𝔁 b - a
𝗀 𝔂 k + 1
𝗀 𝔃 (γ i).val
𝗀 𝔄 0 ≤ t
𝗀 𝔅 sq_le_sq₀ (abs_nonneg _)
𝗀 𝔆 4*C.smoothness
𝗀 𝔇 highTorusPatch d k j
𝗀 𝔈 x - y
𝗀 𝔉 Measurable (Function.uncurry p)
𝗀 𝔊 1 < C.smoothness
𝗀 𝔋 zero_lt_one.trans_le (le_max_left ..)
𝗀 𝔌 D-2
𝗀 𝔍 Finset.sum_nonneg (fun i _ => abs_nonneg _)
𝗀 𝔎 (((((separatedMatrix_entry_integrable σ A hA hcost h.2.1.1 h.2.1.2).const_mul (C ^ 2 / 2)).mul_const (fairSign h.2.2.1.1)).mul_const (fairSign h.2.2.1.2)).const_mul (responseWeight q h.2.2.2)).const_mul
𝗀 𝔏 ℝ → ℝ
𝗀 𝔐 D ^ 2
𝗀 𝔑 fun _ => ENNReal.ofReal_lt_top
𝗀 𝔒 2 * C ^ 2
𝗀 𝔓 1 ≤ r
𝗀 𝔔 AnchoredIndex d C.order
𝗀 𝔕 pairResponseVector (θ.regression w.1) (θ.regression w.2)
𝗀 𝔖 5 ≤ d
𝗀 𝔗 Fin d → Fin (ℓ + 1)
𝗀 𝔘 (measurable_pi_apply i).comp
𝗀 𝔙 0 < c
𝗀 𝔚 fun _ _ => 1
𝗀 𝔛 dyadicPilotScale d j
𝗀 𝔜 j = 0
𝗀 𝔝 (Finset.abs_sum_le_sum_abs ..).trans
𝗀 𝔞 fun v hv i => highFrameProfile_abs_le_one C hC (U i) (hU i) v hv
𝗀 𝔟 mul_le_mul (hHb _)
𝗀 𝔠 (historyReferenceRho_pos Δ).le
𝗀 𝔡 ∀ j i, Measurable (fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2)
𝗀 𝔢 fun _ => rfl
𝗀 𝔣 highCenterResolutionThreshold C ≤ M
𝗀 𝔤 0 ≤ L
𝗀 𝔥 A i j
𝗀 𝔦 0 < A
𝗀 𝔧 fun _ => μ
𝗀 𝔨 α → ℝ
𝗀 𝔩 completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ell N mu M R q C a rho eta U
𝗀 𝔪 j - 1
𝗀 𝔫 regularGridCell k hk
𝗀 𝔬 Measure.pi (fun _ => π)
𝗀 𝔭 highSampleReference d n
𝗀 𝔮 ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l)
𝗀 𝔯 historyMarkedPrior dependent Δ
𝗀 𝔰 (div_le_iff₀ (Real.rpow_pos_of_pos (euclideanNorm_pos_of_ne_zero (x.val - y.val) (sub_ne_zero.mpr hxy)) α)).mpr
𝗀 𝔱 1+Real.log N
𝗀 𝔲 Set (Covariate d)
𝗀 𝔳 2 ^ j
𝗀 𝔴 0 ≤ b
𝗀 𝔵 0 < N
𝗀 𝔶 b^2
𝗀 𝔷 m + 1
𝗀 𝕬 effectiveVarianceUpper C - C.varianceLower
𝗀 𝕭 observationLaw_isProbability C θ hθ
𝗀 𝕮 shrunkDensityExponent C.densityLower C.densityUpper
𝗀 𝕯 j.val+3
𝗀 𝕰 0 < C
𝗀 𝕱 lowerSaddleD d m x
𝗀 𝕲 (d+8)/4
𝗀 𝕳 0 ≤ M
𝗀 𝕴 ρ/2
𝗀 𝕵 exactEuclideanDistance (U 0) (U 1)
𝗀 𝕶 fun z eps => Finset.measurable_fun_prod _ (fun i _ => hm z eps i)
𝗀 𝕷 (ad+bd)/(bd-ad)
𝗀 𝕸 normalizedDensityTernaryParameter (p ω) (F ω) a
𝗀 𝕹 higherBandFamilyUpper d ℓ N μ i.val
𝗀 𝕺 highUnionSourceDensity C R h
𝗀 𝕻 ternaryVarianceDerivative a (y i)
𝗀 𝕼 WordHeapPiece u dependent ≃o WordHeapPiece v dependent
𝗀 𝕽 higherBandFamilyGuardDegree M i.val
𝗀 𝕾 2 ≤ k
𝗀 𝕿 anchoredDimension d ℓ
𝗀 𝖀 4 * s
𝗀 𝖁 U i l
𝗀 𝖂 C ≠ 0
𝗀 𝖃 fun z : W × H => B z.1 z.2
𝗀 𝖄 0 ≤ δ
𝗀 𝖅 0 < H
𝗀 𝖆 (ζ, h)
𝗀 𝖇 Real.sqrt (Real.log x)
𝗀 𝖈 0 < M
𝗀 𝖉 n^2
𝗀 𝖊 Ω × Ω
𝗀 𝖋 0 ≤ P
𝗀 𝖌 3^d
𝗀 𝖍 ℝ×ℝ
𝗀 𝖎 1 ≤ ell ∧ (∀ r , 0 < higherBandTargetScale d r N mu) ∧ (∀ r , ell < higherBandTargetScale d r N mu → r ≤ M)
𝗀 𝖏 fun _ => E
𝗀 𝖐 (List.finRange d).flatMap (fun i => List.replicate (γ i) i)
𝗀 𝖑 Fin (Fintype.card (incrementVariables r))
𝗀 𝖒 abs_of_pos (Real.exp_pos _)
𝗀 𝖓 P^n
𝗀 𝖔 MvPolynomial.eval₂Hom (RingHom.id ℝ)
𝗀 𝖕 ∀ j k, ¬ dependent j k → ∀ e f state, update k f (update j e state) = update j e (update k f state)
𝗀 𝖖 ∏ j : Fin q, if h : j ∈ Set.range a then v (a.toEquivRange.symm ⟨j, h⟩) (σ j) else m (σ j)
𝗀 𝖗 Covariate d × ℝ
𝗀 𝖘 Finset.measurable_fun_sum _ (fun l _ => (he l).mul ((hB l).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
𝗀 𝖙 (threeBlockSize n : ℝ)
𝗀 𝖚 0 ≤ T
𝗀 𝖛 fun _ => ℝ
𝗀 𝖜 Estimator d n
𝗀 𝖝 1 / 4
𝗀 𝖞 minimaxRMS C n
𝗀 𝖟 ∀ i, 0 < R.rowMass i
𝗀 𝕅₁ ℝ≥0∞
𝗀 𝕛₁ u ^ 2
𝗀 𝕢₁ ℕ → ℕ
𝗀 𝕥₁ MvPolynomial (Fin p) ℝ
𝗀 𝕦₁ y-x
𝗀 𝕧₁ 0 < lo
𝗀 𝕨₁ (ha.trans hab).le
𝗀 𝕩₁ HighUnionRowData d k D
𝗀 𝕪₁ fun _ => cubeVolume d
𝗀 𝕫₁ historyMarkedAppend dependent hsymm j
𝗀 𝒜₁ n ≤ D
𝗀 𝒝₁ massPowerNormalizer ν m n
𝗀 𝒞₁ fun b => (hp i b).le
𝗀 𝒠₁ highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw (Filter.Eventually.of_forall (hraw ω))
𝗀 𝒡₁ ∀ i, i ∉ S → w i = 0
𝗀 𝒢₁ M + 1
𝗀 𝒣₁ mul_nonneg (sq_nonneg _)
𝗀 𝒤₁ Fin d →₀ ℕ
𝗀 𝒥₁ 2 * d
𝗀 𝒦₁ Fintype.card (SpatialScaleIndex i)
𝗀 𝒧₁ T ^ 2
𝗀 𝒨₁ spatialSquaredDistance x y
𝗀 𝒩₁ (j : ℝ)
𝗀 𝒪₁ fullSpatialPatchDesign d n
notation "𝖯₁" => integratedCardinalMatrix lam T U
𝗀 𝒬₁ j ≠ i
𝗀 𝒭₁ κ → ℝ
𝗀 𝒮₁ 0 ≤ A
𝗀 𝒯₁ (μ.prod μ).prod
𝗀 𝒰₁ 0 < eta0
𝗀 𝒱₁ ((β₀,β₀),(false,false),0)
𝗀 𝒲₁ Measure.dirac ()
𝗀 𝒳₁ (h,e)
𝗀 𝒵₁ 0 ≤ H
𝗀 𝒶₁ 0 ≤ C
𝗀 𝒷₁ integral_add (integrable_const _)
𝗀 𝒸₁ anchoredFinTransport d C.order
𝗀 𝒹₁ (k.factorial : ℝ)
𝗀 𝒺₁ ∀ i, U i ∈ hyperplaneCube d
𝗀 𝒻₁ Fin 2 → Covariate d
𝗀 𝒼₁ fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le
𝗀 𝒾₁ 0 ≤ c
𝗀 𝒿₁ p ω x
𝗀 𝓀₁ StandardBorelSpace (HighUnionMark E)
𝗀 𝓁₁ (γ r).val
𝗀 𝓂₁ (z : ZMod k) = j
𝗀 𝓄₁ Finset.prod_eq_zero (Finset.mem_univ i)
𝗀 𝓅₁ Finsupp.prod_fintype _ _ (fun _ => pow_zero _)
𝗀 𝓆₁ ordinaryFineAliasTargetSet d D ell N mu
𝗀 𝓇₁ Sum.inl ⟨i,e⟩
𝗀 𝓈₁ high_source_interval_numeric C M hM
𝗀 𝓊₁ highPacketMarkMass σ a b m r D q C A
𝗀 𝓋₁ fun l => highFramePolynomial (c l)
𝗀 𝓌₁ ∀ r, (z r) = j r
𝗀 𝓍₁ ρ⁻¹ * (Fintype.card J) * B
𝗀 𝓏₁ a + b
𝗀 𝓐₁ fun _ => abs_nonneg _
𝗀 𝓑₁ spatialScaleDomain i T
𝗀 𝓒₁ SpatialScaleIndex i → Covariate d
𝗀 𝓓₁ d - 4
𝗀 𝓔₁ fun {_ _} h => highNeighborLabels_symmetric d k _ _ h
𝗀 𝓕₁ r.val + 1
𝗀 𝓖₁ Fin n → E
𝗀 𝓗₁ 0 ≤ ρ
𝗀 𝓘₁ 2 ≤ M
𝗀 𝓙₁ measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd)
𝗀 𝓚₁ d + 1
𝗀 𝓛₁ encodeDesignResponse a z
𝗀 𝓜₁ historyShapeLength dependent g
notation "𝗡₁" => historyShapeAppend dependent j
𝗀 𝓞₁ MemLp (fun z => η z.1 z.2) 2 (μ.prod M)
𝗀 𝓟₁ Finset.sum_le_sum (s := Finset.univ)
𝗀 𝓠₁ incrementGlobalVector j (z i)
𝗀 𝓡₁ ternary_mean_derivative_abs_bound a _ ρ ha hρ
𝗀 𝓢₁ mu ≤ 1
𝗀 𝓣₁ 0 < n
𝗀 𝓤₁ fun j hj => hP j (Finset.mem_insert_of_mem hj)
𝗀 𝓥₁ pow_le_pow_left₀ (norm_nonneg _)
𝗀 𝓦₁ regularPairDesignMeasure θ k hk
𝗀 𝓧₁ Finset.sum_nonneg (fun r _ => sq_nonneg _)
𝗀 𝓨₁ (100*d)^2*16*spatialScaleIntegralConstant d
𝗀 𝓩₁ 1 ≤ N
𝗀 𝓪₁ volume.real (spatialPatchBox d)
𝗀 𝓫₁ ∀ i, MeasurePreserving (X i) ν (observationLaw θ)
𝗀 𝓬₁ highRowTotalMass R.rowMass/highCenterMix C
𝗀 𝓭₁ .inr (.inr i)
𝗀 𝓮₁ 1 ≤ ell
𝗀 𝓯₁ Fin q → Fin d
𝗀 𝓰₁ fun w hw => ⟨C.densityLower_pos.le.trans hw.1, hw.2⟩
𝗀 𝓱₁ (dyadicKnownGram j x)⁻¹
𝗀 𝓲₁ Ω × W
𝗀 𝓴₁ iteratedFDeriv ℝ k
𝗀 𝓵₁ 0 < T
𝗀 𝓶₁ finePairDensityCoefficientBudget ad bd M n
𝗀 𝓷₁ (highResponseMarkAtom C q e.2.2).2
𝗀 𝓸₁ (highResponseMarkAtom 0 q e.2.2).1
𝗀 𝓹₁ 1 ≤ k
𝗀 𝓺₁ Cfr⁻¹
𝗀 𝓻₁ highHistoryLikelihoodDerivative dependent hsymm π activation n a
𝗀 𝓼₁ ∫ e, activation e ∂π = 0
𝗀 𝓽₁ 0 < t
𝗀 𝓾₁ highRawSampleLikelihood n a V (p z.1) (F z.1) z.2
𝗀 𝓿₁ ne_of_gt (Finset.prod_pos (fun k _ => hp k))
𝗀 𝔀₁ highUnionSourceDensity_interval C R G h (x i)
𝗀 𝔁₁ eta^(4*q)*N^d ≤ 1
𝗀 𝔂₁ ∀ ⦃a b⦄, dependent a b → dependent b a
𝗀 𝔃₁ W → H →L[ℝ] H
𝗀 𝔄₁ (i, j)
𝗀 𝔅₁ Matrix n n
𝗀 𝔆₁ .inr (.inl ())
𝗀 𝔇₁ fun _ => (1)
𝗀 𝔈₁ dyadicPolynomialPilot C n j x y m row
𝗀 𝔉₁ (ternaryMass_joint_measurable a V (Function.uncurry F) hF).comp ((hx i).prodMk (hy i))
𝗀 𝔊₁ historyShapeReferenceWeight dependent Δ g
𝗀 𝔋₁ ⟨(hp i).aemeasurable, (hp t).aemeasurable, (hp i).map_eq.trans (hp t).map_eq.symm⟩
𝗀 𝔌₁ responseWeight q h
𝗀 𝔍₁ j + 1
𝗀 𝔎₁ spatialScaleExtend i t
𝗀 𝔏₁ spatialPatchDesignMeasure i d
𝗀 𝔐₁ 2*cardinalRawTaylorCoefficient n q bd C a ρ η^2
𝗀 𝔑₁ 2 * n
𝗀 𝔒₁ highUnionSourceResetDensity C R j h
𝗀 𝔓₁ (highCenterMix_mem C).1
𝗀 𝔔₁ k * x
𝗀 𝔕₁ π.prod (μ.prod μ)
𝗀 𝔖₁ i ≠ j
𝗀 𝔗₁ highUnionSourceState_coefficient_ball C R G h
𝗀 𝔘₁ ∀ γ, Measurable (fun x => φ x γ)
𝗀 𝔙₁ ∀ γ, Measurable (fun e => cReset e γ)
𝗀 𝔚₁ List.ofFn (fun i => i)
𝗀 𝔛₁ fun i => y i
𝗀 𝔜₁ 2 ≤ r
𝗀 𝔝₁ t * B / ρ
𝗀 𝔞₁ 0 < ρ
𝗀 𝔟₁ fun x => MvPolynomial.eval x F
𝗀 𝔠₁ fun z : W × H => A z.1 z.2
𝗀 𝔢₁ (∫ x, η x w ∂μ) = 0
𝗀 𝔣₁ dyadicAnchoredFeature j x z
𝗀 𝔤₁ u ∈ unitCube d
𝗀 𝔥₁ t ∈ Ici 0
𝗀 𝔦₁ designLaw_isProbability C θ hθ
𝗀 𝔧₁ ∀ i, Measurable (X i)
𝗀 𝔨₁ regularGridCollisionMass θ k hk
𝗀 𝔩₁ Finset.measurable_sum _ (fun y _ => (hL ξ y).mul ((hR y).pow_const 2))
𝗀 𝔪₁ (40 : ℝ) ^ d * ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 * Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c)
𝗀 𝔫₁ Measure.pi (fun _ => μ.restrict A)
𝗀 𝔬₁ massPowerNormalizer_pos ν m hm n aRaw bRaw haRaw
𝗀 𝔭₁ (x : Covariate d) = y
𝗀 𝔯₁ if pri.2.1 then Sum.inr (Sum.inr (anchoredFinIndex pri.2.2)) else Sum.inr (Sum.inl (anchoredFinIndex pri.2.2))
𝗀 𝔰₁ r ^ 2
𝗀 𝔱₁ 0 ≤ r
𝗀 𝔲₁ 0 < B
𝗀 𝔳₁ HighPacketMarkIndex ι m r D q
𝗀 𝔴₁ b / densityMargin a b 0
𝗀 𝔵₁ Measure (Covariate d)
𝗀 𝔶₁ dyadicPopulationCoefficients C θ J m
𝗀 𝔷₁ (2) ^ L
𝗀 𝕬₁ (anchoredMonomial_continuous γ).comp
𝗀 𝕭₁ 0 < D
𝗀 𝕮₁ 0 < ℓ
𝗀 𝕯₁ 4 ≤ j
𝗀 𝕰₁ 0 < b
𝗀 𝕱₁ integratedCardinalWeight lam T U i
𝗀 𝕲₁ volume.restrict (Ici 0)
𝗀 𝕳₁ d ^ 2
𝗀 𝕴₁ Icc C.varianceLower (effectiveVarianceUpper C)
𝗀 𝕵₁ 2*tau*M
𝗀 𝕶₁ mu^2
𝗀 𝕷₁ 0 < cf
𝗀 𝕸₁ lowerSaddleGrid d m theta Cω n
𝗀 𝕹₁ rawCostConstant CB C5 C6 C7 cf ch
𝗀 𝕺₁ d+4
𝗀 𝕻₁ finePairRowMass_positive d D hD M q hq a b ha hab
𝗀 𝕼₁ highCenterResolution_guards C M
𝗀 𝕽₁ 0 < ell
𝗀 𝕾₁ le_max_left _ _
𝗀 𝕿₁ measure_ne_top _ _
𝗀 𝖀₁ (z i).1
𝗀 𝖁₁ Fin n → α
𝗀 𝖂₁ incrementGlobalMean θ j
𝗀 𝖃₁ A ^ k
𝗀 𝖄₁ Real.exp (-(T * exactEuclideanDistance xy.1 xy.2))
𝗀 𝖅₁ Measure.dirac_apply_of_mem (Set.mem_univ _)
𝗀 𝖆₁ 1 < s
𝗀 𝖇₁ D ≤ K*M
𝗀 𝖈₁ label z.1 = label z.2
𝗀 𝖉₁ mul_nonneg (Nat.cast_nonneg _)
𝗀 𝖊₁ 3*Chi^2
𝗀 𝖋₁ fun u => highLocalFrameFeature k j (x u)
𝗀 𝖌₁ 0 ≤ cf
𝗀 𝖍₁ highUnionSourceResetCoefficient C R j h
𝗀 𝖎₁ i ∈ S
𝗀 𝖏₁ abs_of_nonneg (sq_nonneg η)
𝗀 𝖐₁ (k : ℤ)
𝗀 𝖑₁ (le_abs_self _).trans
𝗀 𝖒₁ Fin r ↪ Fin n
𝗀 𝖓₁ hp i (y i)
𝗀 𝖔₁ integral_sub (hi u hu) (hi v hv)
𝗀 𝖕₁ ite_eq_right_iff.mpr (fun h => False.elim (hxy h))
𝗀 𝖖₁ div_nonneg (sq_nonneg _)
𝗀 𝖗₁ i = l
𝗀 𝖘₁ higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine
𝗀 𝖙₁ (D : ℝ)
𝗀 𝖚₁ Relation.EqvGen (IndependentHistoryExchange independent)
𝗀 𝖛₁ (e x).position
𝗀 𝖜₁ ∀ x, wordHeapLabel (e x) = wordHeapLabel x
𝗀 𝖝₁ ‖v‖
𝗀 𝖞₁ g k + η * w k * z
𝗀 𝖟₁ ternaryValue 1 (ξ j)
𝗀 𝕅₂ shrunkDensityExponent a b
𝗀 𝕛₂ Ω → W → H
𝗀 𝕢₂ (tau-2*c0)*D
𝗀 𝕥₂ paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H
𝗀 𝕦₂ highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
𝗀 𝕧₂ Sum.inl (γ, δ)
𝗀 𝕨₂ finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U p g w c y
𝗀 𝕩₂ ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫
𝗀 𝕪₂ 0 < δ
𝗀 𝕫₂ Fin d → Fin k
𝗀 𝒜₂ 0 < Λ
𝗀 𝒝₂ 0 ≤ R
𝗀 𝒞₂ 0 ≤ a
𝗀 𝒠₂ fun r => u r - v r
𝗀 𝒡₂ 0 ≤ t j
𝗀 𝒢₂ 16*spatialUnaryIntegralConstant d
𝗀 𝒣₂ BoundedEstimator C n
𝗀 𝒤₂ pairFluctuationScale (d := d) n
𝗀 𝒥₂ S z ^ 2
𝗀 𝒦₂ pairPilotNoiseKernel k hk bar η
𝗀 𝒧₂ Cs*mu
𝗀 𝒨₂ 3 ≤ n
𝗀 𝒩₂ 0 ≤ K
𝗀 𝒪₂ V-Q.v
notation "𝖯₂" => 2 ≤ q
𝗀 𝒬₂ ℓ < N
𝗀 𝒭₂ L ^ 2
𝗀 𝒮₂ Measure.pi (fun _ : Fin n => μ)
𝗀 𝒯₂ dyadicIncrementKernel C θ j
𝗀 𝒰₂ (∫ z, g z.1 ∂observationLaw θ) = ∫ x, g x ∂designLaw θ
𝗀 𝒱₂ (2) ^ J
𝗀 𝒲₂ ∀ᵐ w ∂M, w.1 ∈ unitCube d
𝗀 𝒳₂ Fin 2 → ℝ
𝗀 𝒴₂ E × E
𝗀 𝒵₂ spatialSubsetConfiguration S U
𝗀 𝒶₂ finePairDistanceMatrix d F
𝗀 𝒷₂ (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd
𝗀 𝒸₂ finePairTimeMatrix_measurable d _
𝗀 𝒹₂ T0 ≤ N
𝗀 𝒺₂ 4 * b
𝗀 𝒻₂ bd^n
𝗀 𝒼₂ finePairDistanceMatrix d D
𝗀 𝒾₂ highLocalCoordinates d k j x
𝗀 𝒿₂ label ⁻¹' {label x}
𝗀 𝓀₂ (Finset.measurable_prod _ (fun l _ => hq ξ l (y l))).const_mul _
𝗀 𝓁₂ ∀ x, initial.1 x = 1
𝗀 𝓂₂ c^2
𝗀 𝓄₂ C.order + 1
𝗀 𝓅₂ highMarkedResponseMass_measurable a V η g w hg hw φ hφ
𝗀 𝓆₂ 0 ≤ pPlus
𝗀 𝓇₂ k * x r - z r
𝗀 𝓈₂ η*w i
𝗀 𝓉₂ Ioo_mem_nhds ht htT
𝗀 𝓊₂ ∀ i, p i ≠ 0
𝗀 𝓋₂ Ioo 0 T
𝗀 𝓌₂ ternaryValue a y
𝗀 𝓍₂ Finset.mul_prod_erase _ _ (Finset.mem_univ i)
𝗀 𝓎₂ U i j
𝗀 𝓏₂ fun _ _ => rfl
𝗀 𝓐₂ WordHeapPiece word dependent
𝗀 𝓒₂ b ^ 4
𝗀 𝓓₂ InnerProductSpace ℝ H
𝗀 𝓕₂ stretchConstant C.smoothness d (paperTau C)
𝗀 𝓖₂ rateExponent C.smoothness d
𝗀 𝓗₂ Finset.measurable_prod _ (fun l _ => poissonCellFieldValue_measurable_fixed ρ hρ (U l))
𝗀 𝓘₂ ∀ i, MemLp (ε i) 4 μ
𝗀 𝓙₂ variableKernelSeries lo hi
𝗀 𝓚₂ x ∈ cube d
𝗀 𝓛₂ holderBall_coordinate_modulus f t H hH hf (fun i => Fin.elim0 ((hk ▸ i)))
𝗀 𝓜₂ ∀ l, Measurable (fun zx : Z × Covariate d => B zx.1 zx.2 l)
notation "𝗡₂" => (highRawSampleLikelihood_hasDerivAt_path n a v η u (p ω) (F ω) z).const_mul
𝗀 𝓞₂ coefficientRegression η (g j) (w j) (φ j) (c j)
𝗀 𝓟₂ ∀ i, (∫ e, R.rowActivation i e ∂(R.rowLaw i)) = 0
𝗀 𝓠₂ higherBandRowMass d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q a b C lam ℓ
𝗀 𝓡₂ (r : ℝ)
𝗀 𝓢₂ I → ℝ
𝗀 𝓣₂ HighResponseMarkIndex ι q
𝗀 𝓤₂ highResponseMarkWeight C q
𝗀 𝓥₂ k - 1
𝗀 𝓦₂ x ≤ y
𝗀 𝓧₂ PolynomialBox d ℓ
𝗀 𝓨₂ LocalPilotIndex d ℓ
𝗀 𝓩₂ 2 * ℓ
𝗀 𝓪₂ (γ.val i).val
𝗀 𝓫₂ (MvPolynomial.totalDegree_mul ..).trans
𝗀 𝓬₂ anchoredTransport d ℓ
𝗀 𝓭₂ anchoredFeature u w
𝗀 𝓮₂ Fin j → Covariate d
𝗀 𝓯₂ 2 * C.holderBound ^ 2 + 1
𝗀 𝓰₂ 1 + t j
𝗀 𝓱₂ y r - x r
𝗀 𝓲₂ 2*cardinalRawAliasCoefficient n bd a η^2
𝗀 𝓳₂ ⟨j, h⟩
𝗀 𝓴₂ 0 < lam
𝗀 𝓵₂ (measurable_pi_apply j).comp
𝗀 𝓶₂ fun β _ => Finset.sum_nonneg (fun β' _ => abs_nonneg _)
𝗀 𝓷₂ T.val z - θ.variance
𝗀 𝓸₂ abs_of_nonneg (C.varianceLower_pos.le.trans (T.property z).1)
𝗀 𝓹₂ Cp ^ 2 * W / n
𝗀 𝓺₂ fullSpatialPatchDesign d r
𝗀 𝓻₂ fullSpatialPatchDesign d 2
𝗀 𝓼₂ D-M
𝗀 𝓽₂ densityIntervalExponent C.densityLower C.densityUpper
𝗀 𝓾₂ (lowerSaddleM_tendsto_atTop hm).eventually
𝗀 𝓿₂ 0 ≤ E
𝗀 𝔀₂ 1+Bl^2
𝗀 𝔁₂ R.rowIntercept i e
𝗀 𝔂₂ (e.1,e.2.1)
𝗀 𝔃₂ singletonRowMass_positive d D q hq a b ha hab
𝗀 𝔄₂ ell < N
𝗀 𝔅₂ cm ≤ 1/C.densityUpper
𝗀 𝔆₂ measurable_fst.prodMk ((hθ.2.1.comp measurable_fst).add measurable_snd)
𝗀 𝔇₂ fun i => hm.comp (measurable_pi_apply i)
𝗀 𝔈₂ ‖u‖
𝗀 𝔉₂ holderNorm U F
𝗀 𝔊₂ dyadicNormalizedAnchor j x
𝗀 𝔋₂ (m : ℝ)
𝗀 𝔌₂ (designLaw θ).real
𝗀 𝔍₂ pow_nonneg (Nat.cast_nonneg d) _
𝗀 𝔎₂ C.smoothness ≤ 1
𝗀 𝔏₂ Finset (Fin k)
𝗀 𝔐₂ Icc a b
𝗀 𝔑₂ (ζ,e)
𝗀 𝔒₂ fun y _ => hy y
𝗀 𝔓₂ 0 < aD
𝗀 𝔔₂ spatialSquaredDistance (U 0) (U 1)
𝗀 𝔕₂ (measurable_fst.comp measurable_fst).prodMk measurable_snd
𝗀 𝔖₂ N^2
𝗀 𝔗₂ ∀ e, ‖F e‖ ≤ L
𝗀 𝔘₂ r + 1
𝗀 𝔙₂ (abs_add_le ..).trans
𝗀 𝔚₂ fun y _ => hp y
𝗀 𝔛₂ (Finset.mul_sum ..).symm
𝗀 𝔜₂ ⟨hu.1.le,hu.2.le⟩
𝗀 𝔝₂ historyMarkedDensity dependent ρ
𝗀 𝔞₂ marks i = marks' i
𝗀 𝔟₂ (cubeVolume d).real
𝗀 𝔠₂ historyShapeCanonicalLabels dependent g
𝗀 𝔡₂ (h,fresh)
𝗀 𝔢₂ densityIntervalExponent a b
𝗀 𝔣₂ i.val + 1 = j.val
𝗀 𝔤₂ (fresh, marks)
𝗀 𝔥₂ j.val + 1
𝗀 𝔦₂ (k : WithTop ℕ∞) ≤ ⊤
𝗀 𝔧₂ lowerAliasSpatialL d R c0 K * M
𝗀 𝔨₂ q w * ‖A w‖ ^ 2
𝗀 𝔩₂ η z.1 z.2
𝗀 𝔪₂ (y, x)
𝗀 𝔫₂ ∀ w, ‖B w‖ ≤ C
𝗀 𝔬₂ lo < hi
𝗀 𝔭₂ intervalRho_pos lo hi hlo hlt
𝗀 𝔮₂ ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ
𝗀 𝔯₂ (Measure.quasiMeasurePreserving_fst ).ae
𝗀 𝔰₂ (Measure.quasiMeasurePreserving_snd ).ae
𝗀 𝔱₂ (eventually_paper_allocated_grid_guard C hreg hH).mono fun _ h => h.2
𝗀 𝔲₂ lt_of_lt_of_le zero_lt_one (le_max_left ..)
𝗀 𝔳₂ (spatial_scale_domain_isClosed i L).measurableSet
𝗀 𝔴₂ x ∈ spatialPatchBox d
𝗀 𝔵₂ 0 ≤ spatialInterpolationLambda d
𝗀 𝔶₂ t j * lam
𝗀 𝔷₂ (spatial_scale_domain_isClosed i T).measurableSet
𝗀 𝕬₂ lowerSaddleMu d m theta
𝗀 𝕭₂ completeSourceGeometryEnvelope D M Rbound q C.densityLower C.densityUpper c0 ell N mu Cfr Q.a Q.ρ eta Chi
𝗀 𝕮₂ E ≤ lowerSaddleRawEnergyBound C.smoothness d m theta Cω cf C5 C6 C7 ch Bl tauM n
𝗀 𝕯₂ measurable_inl.comp ((rowSigmaMk_measurable i).comp (hlift i))
𝗀 𝕰₂ sourceRowData d k D M q
𝗀 𝕱₂ highWindowHolderConstant C*cf ≤ C.holderBound
𝗀 𝕲₂ dyadicResponseMoment θ j x - θ.regression x • dyadicConstantMoment θ j x
𝗀 𝕳₂ taylorErrorFactor C * C.holderBound
𝗀 𝕴₂ EuclideanSpace ℝ (Fin d)
𝗀 𝕵₂ (MeasurableEquiv.toLp 2 _).measurableEmbedding
𝗀 𝕶₂ ℝ × FinePairFieldMark d
𝗀 𝕷₂ -(∑ l, (w l) ^ 2) / 2
𝗀 𝕸₂ indexedGridField_abs_bound d k η hη ξ
𝗀 𝕹₂ H (encodeDesignResponse a z.2)
𝗀 𝕺₂ highAppendLikelihoodAction_measurable dependent hsymm π activation ham n a V p F hp hF j
𝗀 𝕻₂ integrated_cardinal_response_heat hnF q C a V η lam T hC hT U g w c y
𝗀 𝕼₂ completeSourceGeometryEnvelope D M R q aD bD c0 ell N mu C a rho eta Chi
𝗀 𝕽₂ Fin d → ℤ
𝗀 𝕾₂ highHistoryLikelihoodDerivative_measurable dependent hsymm π activation ham n a V η p F hp hF
𝗀 𝕿₂ ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b
𝗀 𝖀₂ historyMarkedPriorGenerator dependent hsymm Δ t π
𝗀 𝖁₂ T * B / historyReferenceRho Δ
𝗀 𝖂₂ (-1 : ℝ)
𝗀 𝖃₂ historyMarkedDensity dependent (historyReferenceRho Δ)
𝗀 𝖄₂ (historyShapeLength_out dependent g).symm
𝗀 𝖅₂ historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels
𝗀 𝖆₂ historyMarkedReferenceRaw dependent Δ π
𝗀 𝖇₂ ∫ x, ‖η x w‖ ^ 2 ∂μ
𝗀 𝖈₂ ‖v w‖ ^ 2
𝗀 𝖉₂ eLpNorm (fun z => T.val z - θ.val.variance) 2 (sampleLaw θ.val n)
𝗀 𝖊₂ ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ q w ∧ q w ≤ C.densityUpper
𝗀 𝖋₂ y ∈ cube d
𝗀 𝖌₂ ((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹
𝗀 𝖍₂ allocationWidth a C x
𝗀 𝖎₂ withDensity_apply _ MeasurableSet.univ
𝗀 𝖏₂ C₀ * C_D
𝗀 𝖐₂ S ^ 2
𝗀 𝖑₂ {c}
𝗀 𝖒₂ 1 / k
𝗀 𝖓₂ J ≤ L
𝗀 𝖔₂ _ = 1
𝗀 𝖕₂ d ≠ 0
𝗀 𝖖₂ U l r
𝗀 𝖗₂ 1 ≤ L
𝗀 𝖘₂ 4 - d
𝗀 𝖙₂ N^d
𝗀 𝖚₂ spatialScaleLogSum i t
𝗀 𝖛₂ Fin q → ℝ
𝗀 𝖜₂ cardinalSeparatedMeasure d n T
𝗀 𝖝₂ worstCaseRisk C T.val
𝗀 𝖞₂ 1 + W
𝗀 𝖟₂ 1 ≤ Cfr0
𝗀 𝒜₃ by positivity
𝗀 𝒜₄ by norm_num
𝗀 𝒝₃ by omega
𝗀 𝒝₄ by linarith
𝗀 𝒞₃ by ring
𝗀 𝒞₄ by simp
𝗀 𝒠₃ by grind
𝗀 𝒠₄ by simp_all
𝗀 𝒡₃ by nlinarith
𝗀 𝒡₄ by bound
𝗀 𝒢₃ by fun_prop
𝗀 𝒢₄ by rfl
𝗀 𝒣₃ by field_simp
𝗀 𝒣₄ by simpa
𝗀 𝒤₃ by decide
𝗀 𝒤₄ by aesop
𝗀 𝒥₃ by gcongr
macro "𝚲" : command => `(variable {J : Type*} [Fintype J] [LinearOrder J])
macro "𝛂" : command => `(variable {Ω : Type*} [MeasurableSpace Ω])
macro "𝛐" : command => `(variable (r : ℕ) [NeZero r])
macro "𝛑" : command => `(variable {ι : Type*} [Fintype ι] [DecidableEq ι])
macro "𝛒" : command => `(variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω})
macro "𝛓" : command => `(variable [NormedAddCommGroup H] [𝗗₂])
macro "𝛕" : command => `(variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M])
macro "𝛖" : command => `(variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W])
macro "𝛗" : command => `(variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : 𝙟))
macro "𝛘" : command => `(variable (k : ℕ) (hk : 𝖰))
macro "𝛙" : command => `(variable {E : Type*} [MeasurableSpace E])
macro "𝛚" : command => `(variable {α : Type*} [PartialOrder α] [DecidableEq α])
macro "𝛜" : command => `(variable {J : Type*})
macro "𝛝" : command => `(variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X])
macro "𝛞" : command => `(variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n])
macro "𝛟" : command => `(variable (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν])
macro "𝛠" : command => `(variable {m : ℕ} (hm : 2 ≤ m) (X : Fin m → Ξ → Observation d))
macro "𝛡" : command => `(variable {P Ω E : Type*} [MeasurableSpace P] [MeasurableSpace Ω] [MeasurableSpace E])
macro "𝛢" : command => `(variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E])
macro "𝛣" : command => `(variable {α ι E : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι] [MeasurableSpace E])
macro "𝛤" : command => `(variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E])
macro "𝛥" : command => `(variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ])
