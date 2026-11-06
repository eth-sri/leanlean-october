module

public import NearlyMinimax.HighLocalScores
public import NearlyMinimax.ScoreSupport
public import NearlyMinimax.HighWindowGeometry
public import NearlyMinimax.Risk
public import NearlyMinimax.ActualSeparatedPacket
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Locality and disjoint-patch orthogonality of the actual high-regime
density-response score. Density resets need not be independent: conditioning
on the design leaves independent response coordinates, and the outside
response likelihood cancels from each true signed-packet ratio. -/
𝚴
𝚪
𝚨
𝚩
𝚭
𝚬

𝗃 𝔑 ∀ i ∈ ἀ, y i = y' i
𝗇 𝔈 𝔑 S
𝗇 𝔉 𝙈
𝗇 𝔍 𝙍
section FinitePacket
𝛢

𝗇 𝔄 𝖨 φ
𝗇 𝔅 𝗡 φ
𝗇 𝔎 ternaryMass a (𝔅 c i) V
𝗇 𝔐 hw i (Finset.mem_sdiff.mp hi).2
theorem high_response_ratio_depends_on_support a V η
    g w φ (c v : 𝙛)
    (S : 𝔍) (hw : 𝖥₁)
    y y' (hyy : 𝔈)
    (hp : ∀ i b, 0 < 𝔎 b) :
    𝔄 v y / 𝔄 c y =
      𝔄 v y' / 𝔄 c y' := by
  let outside (z : 𝔉) :=
    ∏ i ∈ Finset.univ \ S, ternaryMass a (g i) V (z i)
  let inside (z : 𝔉) u :=
    ∏ i ∈ S, ternaryMass a (𝔅 u i) V (z i)
  have hfactor z u :
      𝔄 u z = outside z * inside z u := by
    unfold highResponseProduct
    rw [← Finset.prod_sdiff $ Finset.subset_univ S ]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    simp [coefficientRegression, 𝔐]
  have hout z : outside z ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro i hi
    simpa [coefficientRegression, 𝔐] using hp i $ z i
  have hin z : inside z c ≠ 0 :=
    ne_of_gt $ Finset.prod_pos fun i _ => hp i $ z i
  have hs u : inside y u = inside y' u := by
    aesop
  rw [hfactor y v, hfactor y c, hfactor y' v, hfactor y' c, hs v, hs c]
  field_simp [hout y, hout y', hin y']

𝗇 𝔊 ternaryMass a (𝔅 c k) V $ y k
theorem high_response_variance_ratio a V η
    g w φ (c : 𝙛)
    y (i : Fin n)
    (hp : ∀ k, 0 < 𝔊) :
    𝖷 φ c y i / 𝔄 c y =
      𝙿 /
        𝔎 (y i) := by
  unfold highResponseVarianceTerm highResponseProduct
  rw [← 𝗑₂]
  have hrest : ∏ k ∈ Finset.univ.erase i,
      𝔊 ≠ 0 :=
    𝘃₁
  field_simp

end FinitePacket

𝗇 𝔇 𝘟₁
/-- Product-law orthogonality from local response dependence and actual
conditional centering. This helper is used below only with properties proved
from the explicit signed density-response packet. -/
theorem local_response_scores_orthogonal
    (μ : Fin n → Measure (Fin 3)) [∀ i, IsProbabilityMeasure $ μ i ]
    (r s : 𝔉 → ℝ) (S T : 𝔍) (hST : Disjoint S T)
    (hr : ∀ y y', 𝔈 → r y = r y')
    (hs : ∀ y y', 𝔑 T → s y = s y')
    (hc : ∫ y, r y ∂Measure.pi μ = 0) :
     ∫ y, r y * s y ∂Measure.pi μ = 0 := by
  let R y := r $ extendPatchResponses n S y
  let Q y := s $ extendPatchResponses n T y
  have hR y : r y = R 𝔇 := by
    apply hr
    intro i hi
    simp [extendPatchResponses, hi]
  have hQ y : s y = Q 𝔇 := by
    apply hs
    intro i hi
    simp [extendPatchResponses, hi]
  have hcenter : ∫ y, R 𝔇 ∂Measure.pi μ = 0 := by
    simp_all
  simp_rw [hR, hQ]
  exact finite_product_local_scores_orthogonal n μ S T hST R Q hcenter

section IntegratedPacket
variable {ι E Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [MeasurableSpace Z]

end IntegratedPacket

section Family
variable {J ι E Z : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]
  [Fintype E] [MeasurableSpace Z]

end Family

𝗃 𝔒 ἀ d k j
/-- The actual observation indices in a torus patch. -/
def highPatchSampleIndices (d k n : ℕ) (j : 𝙯)
    (x : 𝙇) : 𝔍 :=
  Finset.univ.filter fun i => x i ∈ 𝔒 highTorusPatch

𝗇 𝔏 highPatchSampleIndices d k n j x
theorem highPatchSampleIndices_disjoint (d k n : ℕ) [NeZero k]
    x j l
    (hjl : l ∉ 𝔒 highNeighborLabels) :
    Disjoint 𝔏 $ highPatchSampleIndices d k n l x := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact Set.disjoint_left.mp (𝔒 highTorusPatch_disjoint_of_not_neighbor l hjl)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem highPeriodicTensor_sample_zero_outside_patch d k n
    j x i
    (hi : i ∉ 𝔏) :
    𝔒 highPeriodicTensor (x i) = 0 := by
  by_contra h
  exact hi $ Finset.mem_filter.mpr ⟨Finset.mem_univ i, 𝔒 highPeriodicTensor_supported_patch h ⟩
