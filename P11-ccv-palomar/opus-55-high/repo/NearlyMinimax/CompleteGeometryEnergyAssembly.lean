module

public import NearlyMinimax.HigherGeometryEnergyAssembly
public import NearlyMinimax.CompleteGeometryExteriorEnergy
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Finite full-count energy assembly for the genuine spatial envelope.
The canonical statistical construction supplies the higher block from its
actual cardinal, ordinary alias, pair alias and field integrals. -/
𝚯
𝚪
𝚨
𝚩
𝚭

def completeGeometryDefectConstant (d q : ℕ) (B C a rho Cs : ℝ) : ℝ :=
  1+|completeGeometryRadialConstant d B a rho Cs|+
    4*|cardinalGeometryFactorialConstant d q B C a rho Cs|

𝗇 𝔨 3*Cs
𝗇 𝔏 𝔨
𝗃 𝔡 ἀ d q aD bD C a rho c0
𝗇 𝔚 𝔡 finePairFieldFactorialConstant 𝔏
def completeGeometryFieldConstant (d q : ℕ) (aD bD C a rho c0 Cs : ℝ) : ℝ :=
  1+4*|𝔚|

𝗇 𝔟 𝔡 finePairSaddleAliasFactorialConstant K
𝗇 𝔘 𝔟 𝔏
def completeGeometryAliasConstant (d q : ℕ) (aD bD C a rho c0 K Cs Cord : ℝ) : ℝ :=
  1+4*|Cord|+4*|𝔘|

theorem completeGeometryDefectConstant_pos d q B C a rho Cs :
    0 < completeGeometryDefectConstant d q B C a rho Cs := by
  unfold completeGeometryDefectConstant
  positivity

𝗇 𝔓 𝔡 completeGeometryFieldConstant Cs
theorem completeGeometryFieldConstant_pos d q aD bD C a rho c0 Cs :
    0 < 𝔓 := by
  unfold completeGeometryFieldConstant
  positivity

𝗇 𝔍 𝔡 completeGeometryAliasConstant K Cs Cord
theorem completeGeometryAliasConstant_pos d q aD bD C a rho c0 K Cs Cord :
    0 < 𝔍 := by
  unfold completeGeometryAliasConstant
  positivity

𝗃 𝔢 ἀ+1
𝗇 𝔉 𝔢 M
𝗃 𝔣 poissonCountWeight $ ἀ*mu
𝗃 𝔭 mul_nonneg ἀ hmu
𝗇 𝔦 𝔭 hAp
𝗃 𝔬 0 ≤ ἀ
theorem four_component_raw_energy_algebra
    (hmu : 𝔬 mu) (hPd : 𝔬 Pdef) (hPal : 𝔬 Pal) (hPlo : 𝔬 Plo)
    (hPloPal : Plo ≤ Pal) (hAo : 𝔬 Ao) (hAp : 𝔬 Ap) M :
    A2*Pdef+4*(Ad*Pdef+Ao*Pal*𝔣 Ao 𝔉+
      Ap*Plo*𝔣 Ap 𝔉+Af*Pdef) ≤
      3*( 1+|A2|+4*|Ad| +(1+4*|Af|))*Pdef+
      3*(1+4*|Ao|+4*|Ap|)*Pal*poissonCountWeight ((1+4*|Ao|+4*|Ap|)*mu) 𝔉 := by
  let C6 := 1+4*|Ao|+4*|Ap|
  have hC6 : 𝔬 C6 := 𝖠₃
  have hAoC : Ao ≤ C6 := by
    grind
  have hApC : Ap ≤ C6 := by
    grind
  have hoW := poissonCountWeight_mono 𝔭 hAo
    (mul_le_mul_of_nonneg_right hAoC hmu) 𝔉
  have hpW := poissonCountWeight_mono 𝔦
    (mul_le_mul_of_nonneg_right hApC hmu) 𝔉
  have ho := mul_le_mul_of_nonneg_left hoW $ mul_nonneg hAo hPal
  have hp := mul_le_mul (mul_le_mul_of_nonneg_left hPloPal hAp) hpW (poissonCountWeight_nonneg 𝔦 _)
    $ mul_nonneg hAp hPal
  have hcoef : 4*(Ao+Ap) ≤ 3*C6 := by
    grind
  have hAli := mul_le_mul_of_nonneg_right hcoef
    $ mul_nonneg hPal $ poissonCountWeight_nonneg 𝔭 hC6 𝔉
  have hDef : A2+4*Ad+4*Af ≤ 3*( 1+|A2|+4*|Ad| +(1+4*|Af|)) := by
    grind
  nlinarith

𝗇 𝔇 3+j
𝗇 𝔎 𝘭
𝗃 𝔠 ἀ D M R q aD bD c0 ell N mu C a rho eta Chi Bl
𝗇 𝔛 𝔠 completeSourceGeometryEnvelope
𝗇 𝔥 ∫ U, 𝔎 ∂fullSpatialPatchDesign d 𝔇
theorem completeSourceGeometryEnvelope_refined_integral
    D M R q j (hj : 𝔇 ≤ D) aD bD c0 ell N mu C a rho eta Chi Bl :
     ∫ U, 𝔛 𝔇 U
      ∂fullSpatialPatchDesign d 𝔇 =
      𝔥 := by
  have hcast : 𝔇=j+3 := 𝖡₃
  rw [hcast] at hj ⊢
  simp only [completeSourceGeometryEnvelope,if_pos hj]

𝗇 𝔖 𝙊
𝗇 𝔗 𝔟 𝔨
𝗇 𝔙 𝗸
𝗇 𝔜 N^(4-𝔖)
𝗇 𝔞 N^(-𝔖)
𝗇 𝔩 𝙹₁
𝗇 𝔪 cardinalGeometryFactorialConstant d q bD C a rho Cs
𝗇 𝔫 𝙺₁
𝗇 𝔄 4*(𝔪*𝔙*𝔞*𝔫 + Cord*(𝔙*Real.exp 𝔩*𝔜)*𝔣 Cord 𝔢 M + 𝔗 * (𝔙*𝔜) * 𝔣 𝔗 𝔢 M + 𝔡 finePairFieldFactorialConstant 𝔨*𝔙*𝔫*𝔞)
𝗇 𝔅 Real.exp (completeGeometryExteriorConstant d Cs Chi)*𝔙*𝔢 Bl^2* poissonCountWeight (completeGeometryExteriorConstant d Cs Chi*mu) 𝔢 D
𝗇 𝔈 𝔜
𝗇 𝔊 ∫ U, 𝔛 r U ∂𝗾₂
𝗇 𝔐 Real.exp 𝔩
𝗇 𝔑 𝖫₂
𝗇 𝔒 𝔙
𝗇 𝔔 𝔞
𝗇 𝔤 bD-𝖧⁻¹
𝗇 𝔧 𝘐
theorem completeSourceGeometryEnvelope_factorial_from_higher (hd : 𝗆)
    (D M R q n : ℕ) (hD : 𝗕)
    aD bD c0 K ell N mu C a rho eta Chi Bl Cs Cord tau
    (hN : 𝘹) (hCs : 𝔬 Cs) (hmu : 𝔬 mu) (hmu1 : 𝗦₁)
    (hbd : 𝔬 𝔤) (hbdB : 𝔤 ≤ bD)
    (hCord : 𝔬 Cord)
    (hCal : 𝔬 𝔘)
    (htau : 𝔬 tau)
    (hhigher : ∑ j ∈ Finset.range 𝔧, poissonCountWeight 𝔑 𝔇 *
      𝔥 ≤
      𝔄) :
     ∑ r ∈ Finset.range 𝔢 n, poissonCountWeight 𝔑 r *
      𝔊 ≤
      3*(completeGeometryDefectConstant d q bD C a rho Cs+
        𝔓)*𝔒*𝔫*𝔔 +
      3*𝔍*𝔒*
        (𝔐*𝔈)*
          𝔣 𝔍 𝔉 +
      𝔅 := by
  let e := fun r => 𝔊
  have he r : 0 ≤ e r := integral_nonneg
    $ 𝔠 completeSourceGeometryEnvelope_nonneg r
  have he1 : e 1=0 := by simp [e,completeSourceGeometryEnvelope]
  have hp := 𝔠 completeSourceGeometryEnvelope_pair_factorial_le Cs bD
    hd hN hCs hmu hbd hbdB
  have ht := completeSourceGeometryEnvelope_exterior_factorial_le (d := d) D M R q 𝔢 n  𝖡₃ 
    aD bD c0 ell N mu C a rho eta Chi Bl Cs hCs hmu hmu1
  have hh : ∑ j ∈ Finset.range 𝔧, poissonCountWeight 𝔑 𝔇*e 𝔇 ≤
      𝔄 := by
    apply le_trans (le_of_eq ?_) hhigher
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [e]
    rw [completeSourceGeometryEnvelope_refined_integral D M R q j $ by
      grind ]
  have hblocks := finite_count_energy_from_blocks 𝔭 hCs n D  𝖡₃ 
    e he (by simp [e,completeSourceGeometryEnvelope]) he1 _ _ _ hp hh ht
  have hPloPal : 𝔒*𝔈 ≤ 𝔒*𝔐*𝔈 := by
    have heone : 1 ≤ 𝔐 := Real.one_le_exp 𝖠₃
    have h := mul_le_mul_of_nonneg_left heone (by positivity : 0 ≤ 𝔒*𝔈)
    linarith
  have ha := four_component_raw_energy_algebra hmu
    (by positivity : 0 ≤ 𝔒*𝔫*𝔔)
     𝖠₃ 
     𝖠₃  hPloPal hCord hCal M
    (A2 := completeGeometryRadialConstant d bD a rho Cs)
    (Ad := 𝔪)
    (Af := 𝔚)
  apply hblocks.trans
  have h := add_le_add_right ha
    𝔅
  convert h using 1 <;> (try dsimp [completeGeometryDefectConstant,completeGeometryFieldConstant,completeGeometryAliasConstant]) <;> ring
