module

public import NearlyMinimax.OrdinaryFineAliasGeometryEnvelope
public import NearlyMinimax.OrdinaryFineAliasFactorialTail
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Canonical rounded-saddle deterministic ordinary-alias envelope and its
actual spatial/factorial moments. No nuisance functions or chart inverses
occur in this universal geometry envelope. -/
𝛅
open scoped BigOperators Topology
𝚨
𝚩
𝛆
𝚬

𝗃 𝔗 ἀ s d ad bd
𝗇 𝔄 𝔗 ordinaryFineAliasSaddleCoefficient
𝗇 𝔎 shrunkDensityExponent ad bd
𝗃 𝔘 ἀ s d m theta Cw
𝗇 𝔈 𝔘 lowerSaddleN 𝔎 x
𝗇 𝔉 𝔗 ordinaryFineAliasSaddleTheta
𝗇 𝔊 𝔘 lowerSaddleEta cf x
𝗇 𝔍 𝙰₂ Cw x
𝗇 𝔓 𝙵
def ordinaryFineAliasSaddleGeometryEnvelope (s : ℝ) (d q : ℕ)
    (ad bd Cw cf C a rho x : ℝ) (n F : ℕ) (U : 𝙇) : ℝ :=
  let m := 𝔄
  let theta := 𝔉
  let c0 := densityIntervalExponent ad bd+1
  let M := 𝗫
  let D := 𝔓
  let N := 𝔈
  let mu := 𝔍
  let L := 𝔘 lowerAliasCutoff c0 𝔎 x
  let R := 𝔗 ordinaryFineAliasSaddleTargetBound
  let eta := 𝔊
  ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) (ordinaryFineAliasTargetSet d D L N mu)
    M R q ad bd c0 C a rho eta L (fun r => higherBandTargetScale d r N mu) U

𝗇 𝔏 lowerSaddleM 𝔄 x
𝗇 𝔐 4-𝙊
𝗃 𝔙 ἀ s d q ad bd
𝗇 𝔑 𝔙 ordinaryFineAliasSaddleGeometryEnvelope Cw cf C a rho x
𝗇 𝔒 𝔙 ordinaryFineAliasSaddleTailPrefactor C a rho
𝗇 𝔔 𝖮₁
/-- True universal Q^n envelope moment, at all counts and frame degrees.
The fixed constant is chosen before x, n, F or nuisance data. -/
theorem eventually_ordinaryFineAliasSaddleGeometryEnvelope_integrable_and_scale_le
    {s ad bd : ℝ} {d : ℕ} (hs : 𝚊₁) (hd : 𝚄 < d)
    (haD : 𝖼) (hab : 𝖽) Cw cf q C a rho :
    ∀ᶠ x in atTop, ∀ n F,
      Integrable (𝔑 n F)
        𝔔 ∧
       ∫ U, 𝔑 n F U
        ∂𝔔 ≤
        𝔒 *
           lowerSaddleEta s d 𝔄
            𝔉 Cw cf x ^4 *
          Real.exp (2*shrunkDensityExponent ad bd
            𝔏*
            𝔏) *
           lowerSaddleN s d 𝔄
            𝔉 Cw 𝔎 x ^𝔐 *
          Real.exp (𝔗 ordinaryFineAliasSaddleTailExponent*
            𝔏) *
           ordinaryAliasSpatialResponseBase d bd ^n := by
  filter_upwards [eventually_ordinaryFineAlias_saddle_guards hs hd haD hab Cw] with x G
  intro n F
  exact ordinaryFineAliasFamilyResponseSquareEnvelope_integrable_and_scale_le G.dimension _ G.targets
    ad bd _ C a rho _ _ _ _ (haD.trans hab).le (Nat.cast_nonneg _)  𝖠₃ 
    (by linarith [densityIntervalExponent_pos haD hab]) G.degree (lowerSaddleN_positive ..)
    G.cutoff G.logarithm _ (fun r hr => (Finset.mem_filter.mp hr).2.2.le) q

𝗇 𝔅 𝖦₁+j
𝗇 𝔇 𝗸 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^𝔐
𝗇 𝔖 𝘀₂
/-- The deterministic geometry envelope has the actual factorial-tail
moment, at the paper's rounded M/D/N/mu and eta=cf*h^s. No nuisance or
conditional pointwise norm premise is needed. -/
theorem eventually_ordinaryFineAliasSaddleGeometryEnvelope_factorial_tail
    {s ad bd : ℝ} {d : ℕ} (hs : 𝚊₁) (hd : 𝚄 < d)
    (haD : 𝖼) (hab : 𝖽) Cw cf q
    C a rho Csharp (hCs : 0 ≤ Csharp) :
    ∀ᶠ x in atTop,
      let m := 𝔄
      let theta := 𝔉
      let M := 𝗫
      let D := 𝔓
      let N := 𝔈
      let mu := 𝔍
      let eta := 𝔊
      let C6 := 𝔙 ordinaryFineAliasFactorialConstant C a rho Csharp
      ∀ F : 𝙦₁,
         ∑ j ∈ Finset.range 𝔖, poissonCountWeight (Csharp*mu) 𝔅 *
           ∫ U, 𝔑
            𝔅 (F 𝔅) U ∂fullSpatialPatchDesign d 𝔅 ≤
        C6 * 𝔇 *
          poissonCountWeight (C6*mu) 𝖦₁ := by
  let tau := densityIntervalExponent ad bd
  let m := 𝔄
  let theta := 𝔉
  have htau := densityIntervalExponent_pos haD hab
  have hm := lowerSaddleCoefficient_pos hs hd htau
  have htheta := lowerSaddleTheta_pos hs hd htau
  have hd0 : 𝙋<d := 𝖡₄
  have hd4 : 4 ≤ d := by
    have h : 𝗦<d := 𝖡₄
    have h' : 4<d := by exact_mod_cast h
    omega
  filter_upwards [eventually_ordinaryFineAliasSaddleGeometryEnvelope_integrable_and_scale_le hs hd haD hab Cw cf q C a rho,
    (lowerSaddleMu_tends_zero hd0 hm htheta Cw).eventually $ gt_mem_nhds (by norm_num : 𝙋<1) ,
    eventually_gt_atTop 0] with x henergy hmu1 hx
  dsimp
  intro F
  let M := 𝗫
  let D := 𝔓
  let N := 𝔈
  let mu := 𝔍
  let eta := 𝔊
  let A := 𝔒
  let L := 𝔗 ordinaryFineAliasSaddleTailExponent
  let B := ordinaryAliasSpatialResponseBase d bd
  let P := 𝔇
  have hmu0 : 0 ≤ mu := by dsimp [mu]; rw [lowerSaddleMu_eq_exp hx]; positivity
  have hA : 𝖲₁ := ordinaryAliasFamilySpatialPrefactor_nonneg ..
  have hP : 𝚏 := by
    exact mul_nonneg (mul_nonneg  𝖠₃  𝙫)
      $ Real.rpow_nonneg (lowerSaddleN_positive ..).le _
  have hB : 𝙐 := by unfold B ordinaryAliasSpatialResponseBase ordinaryAliasSpatialCountBase; positivity
  have hL : 𝘨 := lowerAliasSpatialFixedL_nonneg hd4 _ 𝖡₄
  apply finite_alias_energy_tail_le hA hP hCs hB hL hmu0 hmu1.le M 𝔖
     fun n => ∫ U, 𝔑
      n (F n) U ∂𝔔
  intro j hj
  have he := (henergy 𝔅 $ F 𝔅 ).2
  linarith
