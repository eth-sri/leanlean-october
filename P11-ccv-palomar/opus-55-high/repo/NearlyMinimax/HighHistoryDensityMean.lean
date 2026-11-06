module

public import NearlyMinimax.FiniteAffineHistoryMean
public import NearlyMinimax.HighPacketBalancing
public import NearlyMinimax.HighRawUpdates
public import NearlyMinimax.HighRawDensityLocality
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The actual balanced packet retains the representation mark in its
spatial density reset. Its finite canonical histories have pointwise mean
one under their genuine independent reference mark laws. -/
𝛋
𝚳
𝚨
𝚰
𝚩
𝚬

𝗃 𝔉 ἀ $ labels i
𝗇 𝔇 𝔉 patch
𝗇 𝔈 X → ℝ
𝗃 𝔄 ἀ (labels i) $ marks i
𝗇 𝔍 J → E → V → V
𝗇 𝔎 𝔈 × (J → V)
theorem affinePatchFold_density_eq [DecidableEq J]
    (patch : J → Set X) (slope offset : J → E → 𝔈)
    (response : 𝔍) (labels : I → J) (marks : I → E)
    (indices : List I) (initial : 𝔎) x :
    (indices.foldl (fun θ i => 𝔉 rawPatchUpdate 𝔉 patch
      𝔄 slope 𝔄 offset
      𝔄 response θ) initial).1 x =
      indices.foldl (fun v i =>
        (if x ∈ 𝔇 then 𝔄 slope x else 1) * v +
         if x ∈ 𝔇 then 𝔄 offset x else 0 ) (initial.1 x) := by
  induction indices generalizing initial with
  | nil => rfl
  | cons i indices ih =>
    simp only [List.foldl_cons]
    rw [ih]
    by_cases hx : x ∈ 𝔇 <;>
      simp only [rawPatchUpdate, affinePatchUpdate, hx, ite_true, ite_false, one_mul, add_zero]

𝗇 𝔅 𝗚₁
𝗃 𝔊 ∀ j, Measurable fun ex : E × X => ἀ j ex.1 ex.2
𝗃 𝔏 𝔉 ἀ $ mx.1 i
theorem affinePatchFold_density_joint_measurable [DecidableEq J]
    [MeasurableSpace X] [MeasurableSpace E]
    (patch : J → Set X) (hpatch : ∀ j, MeasurableSet $ patch j )
    (slope offset : J → E → 𝔈)
    (hs : 𝔊 slope)
    (ho : 𝔊 offset)
    (response : 𝔍) n (labels : Fin n → J) (indices : List $ Fin n )
    (initial : 𝔅 → 𝔎)
    (hi : Measurable fun mx : 𝔅 × X => (initial mx.1).1 mx.2 ) :
    Measurable fun mx : 𝔅 × X =>
      (indices.foldl (fun θ i => 𝔉 rawPatchUpdate 𝔇
        𝔏 slope 𝔏 offset
        𝔏 response θ) $ initial mx.1 ).1 mx.2 := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i indices ih =>
    apply ih fun marks => 𝔉 rawPatchUpdate 𝔉 patch
      𝔄 slope 𝔄 offset
      𝔄 response $ initial marks
    have hcoord : Measurable fun mx : 𝔅 × X => (mx.1 i, mx.2) :=
      (𝘜 measurable_fst).prodMk measurable_snd
    exact Measurable.ite ((hpatch _).preimage measurable_snd)
      (((𝔉 hs).comp hcoord).mul hi |>.add ((𝔉 ho).comp hcoord)) hi

section Packet
variable {Z : Type*} [MeasurableSpace Z] (d k F m r D q : ℕ)
