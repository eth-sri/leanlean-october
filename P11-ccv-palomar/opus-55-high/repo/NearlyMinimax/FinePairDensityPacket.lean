module

public import NearlyMinimax.ActualSeparatedPacket
public import NearlyMinimax.PacketAbsoluteMoments
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The genuine fine-pair three-point modulation rule and exterior density
packet from (new-pair-packet). The field mark is retained explicitly. -/
open Set MeasureTheory Polynomial
𝚮
𝚨
𝚰
𝚩

def fineModulationNode (i : Fin 3) : ℝ := if i = 0 then -1 else if i = 1 then 0 else 1
def fineModulationWeight (i : Fin 3) : ℝ := if i = 1 then -1 else 𝙖

theorem fineModulation_eval (f : 𝘓) :
     ∑ i : Fin 3, fineModulationWeight i * f (fineModulationNode i) =
      f (-1) / 2 - f 0 + f 1 / 2 := by
  simp [Fin.sum_univ_succ, fineModulationWeight, fineModulationNode]
  ring

theorem fineModulationNode_bound i : |fineModulationNode i| ≤ 1 := by
  fin_cases i <;> norm_num [fineModulationNode]

theorem fineModulationWeight_variation : ∑ i : Fin 3, |fineModulationWeight i| = 2 := by
  norm_num [Fin.sum_univ_succ, fineModulationWeight]

theorem fineModulation_moment_zero :
     ∑ i : Fin 3, fineModulationWeight i * fineModulationNode i ^ 0 = 0 := by
  rw [fineModulation_eval fun z => z ^ 0 ]
  norm_num

𝗇 𝔎 ∑ i : Fin 3, fineModulationWeight i * fineModulationNode i ^ n
𝗇 𝔛 fun z => z ^ n
theorem fineModulation_moment_odd n (hn : Odd n) :
    𝔎 = 0 := by
  rw [fineModulation_eval 𝔛]
  have hn0 : n ≠ 0 := 𝖤₃
  simp [hn.neg_one_pow, zero_pow hn0]
  norm_num

theorem fineModulation_moment_even n (hn : Even n) (hn0 : n ≠ 0) :
    𝔎 = 1 := by
  rw [fineModulation_eval 𝔛]
  simp [hn.neg_one_pow, zero_pow hn0]
  norm_num

𝗃 𝕮 if Even ἀ then 1 else 0
theorem fineModulation_moment n :
    𝔎 =
      if n = 0 then 0 else 𝕮 n := by
  by_cases hn0 : n = 0
  · subst n; exact fineModulation_moment_zero
  · rw [ite_eq_right hn0]
    rcases Nat.even_or_odd n with hn | hn
    · rw [ite_eq_left hn]; exact fineModulation_moment_even n hn hn0
    · rw [ite_eq_right $ Nat.not_even_iff_odd.mpr hn ]; exact fineModulation_moment_odd n hn

𝗇 𝔏 Fin $ M + 3
abbrev FinePairDensityIndex (M : ℕ) := 𝔏 × Fin 3

𝗃 𝔬 ἀ a b
𝗇 𝔤 𝔬 densityMargin
def finePairDensityPrefactor (a b : ℝ) : ℝ := 𝘺 / 𝔤 0 ^ 2

𝗇 𝔄 M + 2
𝗇 𝔠 𝔬 exteriorNode 𝔄
def finePairDensityAtom (a b : ℝ) (M : ℕ) (i : FinePairDensityIndex M) : 𝚑 :=
  (𝔠 i.1, fineModulationNode i.2)

𝗇 𝔓 𝔬 finePairDensityPrefactor
𝗇 𝔢 𝔬 exteriorWeight 𝔄
def finePairDensityWeight (a b : ℝ) (M : ℕ) (i : FinePairDensityIndex M) : ℝ :=
  𝔓 * 𝔢 i.1 * fineModulationWeight i.2

𝗇 𝔯 𝔬 finePairDensityAtom M
𝗇 𝔰 𝔬 finePairDensityWeight M
def finePairDensitySignedRule (a b : ℝ) (M : ℕ) : SignedMeasure 𝚑 :=
  atomicSignedRule 𝔯 𝔰

𝗇 𝔶 𝘅
𝗇 𝔅 exteriorTau $ 𝗓₁ / 𝔶
𝗇 𝔐 𝙆
𝗇 𝔑 𝙭
𝗇 𝔡 (𝔄 : ℕ) * 𝔅
𝗃 𝕭 𝔬 ἀ ha hab
𝗇 𝔥 𝕭 exterior_rule_variation 𝔄
theorem finePairDensityWeight_variation a b (ha : 𝔐) (hab : 𝔑) M :
     ∑ i : FinePairDensityIndex M, |𝔰 i| =
      2 * |𝔓| *
        Real.cosh 𝔡 := by
  simp only [finePairDensityWeight, abs_mul, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, fineModulationWeight_variation]
  rw [← Finset.sum_mul, ← Finset.mul_sum, 𝔥 𝖡₃ ]
  ring

𝗇 𝔊 𝔬 densityMargin z / b
𝗇 𝔱 U → ℝ
def finePairDensityReset {U : Type*} (a b : ℝ) (z eps : ℝ) (p ψ : 𝔱) (u : U) : ℝ :=
  z + 𝔊 * p u * eps * ψ u

𝗇 𝔈 𝔬 finePairDensityReset z eps p ψ u
𝗇 𝔖 𝔬 Icc
𝗇 𝔜 fun u _ => ψ u
𝗃 𝔭 fun _ => ἀ
𝗇 𝔲 p u ∈ 𝔖
theorem finePairDensityReset_mem_interval {U } a b (ha : 𝔐) (hab : 𝔑)
    z eps (hz : z ∈ 𝔖) (heps : |eps| ≤ 1)
    p ψ (u : U) (hp : 𝔲) (hψ : |ψ u| ≤ 1) :
    𝔈 ∈ 𝔖 := by
  have hh := 𝕭 localDensityReset_mem_interval 1  𝖡₃  z hz 𝔭 eps
    𝔭 heps p 𝔜 u hp 𝔭 hψ
  simpa [localDensityReset, finePairDensityReset, mul_comm, mul_left_comm, mul_assoc] using hh

𝗇 𝔪 𝔶 / 𝖾₂
𝗇 𝔚 𝔪
theorem finePairDensityReset_slope_bound {U : Type*} a b (ha : 𝔐) (hab : 𝔑)
    z eps (hz : z ∈ 𝔖) (heps : |eps| ≤ 1)
    (ψ : 𝔱) u (hψ : |ψ u| ≤ 1) :
    |𝔊 * eps * ψ u| ≤ 𝔚 := by
  have hh := 𝕭 localDensityReset_slope_bound 1  𝖡₃  z hz 𝔭 eps
    𝔭 heps 𝔜 u 𝔭 hψ
  simpa [mul_assoc] using hh

𝗇 𝔞 z + c * fineModulationNode i
𝗃 𝕯 z + ἀ * eps
𝗇 𝔳 𝕯 c
theorem fineModulation_affine_zero z c :
     ∑ i : Fin 3, fineModulationWeight i * 𝔞 = 0 := by
  rw [fineModulation_eval fun eps => 𝔳 ]
  ring

theorem fineModulation_quadratic z c c' :
     ∑ i : Fin 3, fineModulationWeight i *
      (𝔞 * (z + c' * fineModulationNode i)) = c * c' := by
  rw [fineModulation_eval fun eps => 𝔳 * 𝕯 c' ]
  ring

𝗇 𝔒 ∏ i ∈ U, c i
𝗇 𝔗 z ^ (S.card - U.card)
theorem fineModulation_product [DecidableEq ι] S z (c : 𝙛) :
     ∑ h : Fin 3, fineModulationWeight h * ∏ i ∈ S, (z + c i * fineModulationNode h) =
      ∑ U ∈ S.powerset, 𝔗 * 𝔒 *
         if U.card = 0 then 0 else 𝕮 U.card := by
  simp_rw [add_comm z, Finset.prod_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  simp only [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_sdiff_of_subset $ Finset.mem_powerset.mp hU ]
  have he h : fineModulationWeight h *
      (𝔒 * fineModulationNode h ^ U.card * 𝔗) =
      𝔗 * 𝔒 *
        (fineModulationWeight h * fineModulationNode h ^ U.card) := 𝖢₃
  simp_rw [he]
  rw [← Finset.mul_sum, fineModulation_moment]

𝗇 𝔟 𝔬 densityMargin (𝔬 exteriorNode 𝔄 h) / b
𝗇 𝔷 k - j
𝗇 𝔩 𝔠 h ^ 𝔷 * 𝔟 ^ j
def finePairCountCoefficient (a b : ℝ) (M k j : ℕ) : ℝ :=
  𝔓 * ∑ h : 𝔏, 𝔢 h *
    𝔩

𝗇 𝔧 𝔬 finePairCountCoefficient M
theorem finePairCountCoefficient_two a b (ha : 𝔐) (hab : 𝔑) M k :
    𝔧 k 2 = 𝔬 densityCountCoefficient M 2 k := by
  unfold finePairCountCoefficient finePairDensityPrefactor densityCountCoefficient
  rw [Finset.mul_sum, Finset.sum_div]
  grind

theorem finePairCountCoefficient_two_exact a b (ha : 𝔐) (hab : 𝔑)
    M k (hk : 𝚂) (hM : k ≤ M) :
    𝔧 k 2 = if k = 2 then 1 else 0 := by
  rw [𝕭 finePairCountCoefficient_two M k]
  exact 𝕭 densityCountCoefficient_exact M 2 k  𝖡₃  hk hM

𝗇 𝔇 b ^ 𝔷 * 𝔪 ^ j
theorem finePairCountCoefficient_abs_bound a b (ha : 𝔐) (hab : 𝔑)
    M k j :
    |𝔧 k j| ≤
      |𝔓| * 𝔇 *
        Real.cosh 𝔡 := by
  have hb := ha.trans hab
  have hterm h :
      |𝔩| ≤
      𝔇 := by
    have hz := 𝔬 exteriorNode_mem hab.le 𝔄 h
    have ht := 𝔬 densityMargin_bounds hab _ hz
    have htle : 𝔟 ≤ 𝔚 := (div_le_div_of_nonneg_right ht.2.2.2 hb.le).trans_eq 𝖢₃
    rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg $ ha.le.trans hz.1 , abs_of_nonneg $ div_nonneg ht.1 hb.le ]
    bound
  unfold finePairCountCoefficient
  rw [abs_mul]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) $ abs_nonneg _ ).trans
  calc
    _ ≤ |𝔓| *
        ∑ h : 𝔏, |𝔢 h| *
          𝔇 := by
      apply mul_le_mul_of_nonneg_left _ $ abs_nonneg _
      apply Finset.sum_le_sum
      intro h _
      rw [abs_mul]
      bound
    𝘿 := by
      rw [← Finset.sum_mul, 𝔥 𝖡₃ ]
      ring

theorem finePairDensityWeight_exponential_cost a b (ha : 𝔐) (hab : 𝔑) M :
     ∑ h : FinePairDensityIndex M, |𝔰 h| ≤
       2 * |𝔓| * Real.exp (2 * 𝔅) *
        Real.exp (M * 𝔅) := by
  rw [𝕭 finePairDensityWeight_variation M]
  have he : Real.cosh 𝔡 ≤
      Real.exp 𝔡 := by
    rw [← 𝔥 𝖡₃ ]
    exact 𝕭 exterior_rule_variation_le_exp 𝔄 𝖡₃
  apply (mul_le_mul_of_nonneg_left he 𝖠₃ ).trans_eq
  rw [Nat.cast_add, Nat.cast_ofNat, add_mul, Real.exp_add]
  ring

𝗇 𝔘 𝔬 finePairDensitySignedRule M
theorem finePairDensitySignedRule_integral a b M (f : ℝ → 𝘓) :
     ∫ᵛ e, f e.1 e.2 ∂<• 𝔘 =
      𝔓 * ∑ j : 𝔏, 𝔢 j *
        ∑ i : Fin 3, fineModulationWeight i * f (𝔠 j) (fineModulationNode i) := by
  rw [finePairDensitySignedRule, atomicSignedRule_integral]
  simp only [finePairDensityAtom, finePairDensityWeight, Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← Finset.mul_sum]

𝗇 𝕬 p u * ψ u
𝗇 𝔉 ∏ u ∈ W, 𝕬
𝗇 𝔍 if W.card = 0 then 0 else 𝕮 W.card
𝗇 𝔔 𝔬 finePairDensityReset e.1 e.2 p ψ u
𝗇 𝔦 𝔊 * 𝕬
𝗇 𝔨 𝔬 finePairDensitySignedRule_integral M
𝗇 𝔮 𝔠 h ^ (S.card - W.card)
theorem finePairDensitySignedRule_product_expansion [DecidableEq U]
    a b M (S : Finset U) p ψ :
     ∫ᵛ e, ∏ u ∈ S, 𝔔
      ∂<• 𝔘 =
      ∑ W ∈ S.powerset, 𝔧 S.card W.card * 𝔉 *
        𝔍 := by
  rw [𝔨 fun z eps => ∏ u ∈ S, 𝔈 ]
  have he z eps u : 𝔈 =
      𝕯 𝔦 := by
    unfold finePairDensityReset
    ring
  have hprod z W :
       ∏ u ∈ W, 𝔦 =
      𝔊 ^ W.card * 𝔉 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [he, fineModulation_product, hprod]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro W hW
  unfold finePairCountCoefficient
  have hterm h : 𝔓 *
      (𝔢 h *
       (𝔮 *
        (𝔟 ^ W.card * 𝔉) *
        𝔍)) =
      𝔓 *
        (𝔢 h * (𝔮 *
          𝔟 ^ W.card)) *
        (𝔉 * 𝔍) := 𝖢₃
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem finePairDensitySignedRule_mass_zero a b M :
     ∫ᵛ _e, 𝙠 ∂<• 𝔘 = 0 := by
  rw [𝔨 𝘞]
  have hw : ∑ i : Fin 3, fineModulationWeight i = 0 := by
    simpa only [pow_zero, mul_one] using fineModulation_moment_zero
  simp_all

𝗇 𝔣 𝔈 = z + 𝔊 * p u * ψ u * eps
theorem finePairDensitySignedRule_linear_zero a b M
    p ψ (u : U) :
     ∫ᵛ e, 𝔔
      ∂<• 𝔘 = 0 := by
  rw [𝔨 fun z eps => 𝔈 ]
  have he z eps : 𝔣 := by
    unfold finePairDensityReset
    ring
  simp_rw [he, fineModulation_affine_zero]
  simp

𝗇 𝔙 p u * p v * ψ u * ψ v
𝗇 𝔫 𝔤 $ 𝔠 j
theorem finePairDensitySignedRule_pair_exact a b (ha : 𝔐) (hab : 𝔑)
    M (hM : 𝗜₁) p ψ (u v : U) :
     ∫ᵛ e, 𝔔 * 𝔬 finePairDensityReset e.1 e.2 p ψ v
      ∂<• 𝔘 = 𝔙 := by
  rw [𝔨
     fun z eps => 𝔈 * 𝔬 finePairDensityReset z eps p ψ v ]
  have he z eps u : 𝔣 := by
    unfold finePairDensityReset
    ring
  simp_rw [he, fineModulation_quadratic]
  have hc := 𝕭 densityCountCoefficient_exact M 2 2  𝖡₃   𝖡₃  hM
  simp only [densityCountCoefficient] at hc
  have hs : ∑ j : 𝔏, 𝔢 j *
      𝔫 ^ 2 = 𝔤 0 ^ 2 := by
    grind
  have hterm (j : 𝔏) : 𝔢 j *
      ( 𝔫 / b * p u * ψ u *
       (𝔫 / b * p v * ψ v)) =
      𝔢 j * 𝔫 ^ 2 *
      (𝔙 / 𝘺) := 𝖢₃
  simp_rw [hterm]
  rw [← Finset.sum_mul, hs]
  unfold finePairDensityPrefactor
  field_simp [ pow_ne_zero _ 𝕭 densityMargin_zero_ne , 𝕭 densityMargin_zero_ne, (ha.trans hab).ne']

section Field
variable {Z : Type*} [MeasurableSpace Z]

𝗇 𝔴 Z × FinePairDensityIndex M
def finePairFieldReset {U : Type*} (a b : ℝ) (M : ℕ) (p : 𝔱) (ψ : Z → 𝔱)
    (e : 𝔴) (u : U) : ℝ :=
  𝔬 finePairDensityReset (𝔯 e.2).1
    (𝔯 e.2).2 p (ψ e.1) u

𝗇 𝔵 𝔬 finePairFieldReset M p ψ e u
theorem finePairFieldReset_mem_interval {U } a b (ha : 𝔐) (hab : 𝔑)
    M p (hp : ∀ u, 𝔲) ψ
    (hψ : ∀ ζ u, |ψ ζ u| ≤ 1) (e : 𝔴) (u : U) :
    𝔵 ∈ 𝔖 :=
  𝕭 finePairDensityReset_mem_interval _ _
    (𝔬 exteriorNode_mem hab.le 𝔄 e.2.1) (fineModulationNode_bound e.2.2)
    p (ψ e.1) u (hp u) $ hψ e.1 u

theorem finePairFieldReset_abs_le {U } a b (ha : 𝔐) (hab : 𝔑)
    M p (hp : ∀ u, 𝔲) ψ
    (hψ : ∀ ζ u, |ψ ζ u| ≤ 1) (e : 𝔴) (u : U) :
    |𝔵| ≤ b := by
  have hh := 𝕭 finePairFieldReset_mem_interval M p hp ψ hψ e u
  grind
