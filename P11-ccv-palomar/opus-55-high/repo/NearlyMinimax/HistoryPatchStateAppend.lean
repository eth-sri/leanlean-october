module

public import NearlyMinimax.HistoryMarkedStateAppend
public import NearlyMinimax.HighWindowGeometry
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Canonical append for genuine mark-dependent patch resets. Slopes and
intercepts may depend on the entire source mark, including its spatial mark. -/
𝚨
𝚰
𝚩
𝚲

𝗃 𝔅 ἀ j e
𝗃 𝔊 ἀ j fresh
theorem historyMarkedRawState_patch_append [DecidableEq J] [MeasurableSpace E]
    (dependent : 𝙁)
    (hsymm : 𝘼)
    (patch : J → Set Z) (slope intercept : J → E → Z → ℝ)
    (response : J → E → R → R)
    (hdistinct : ∀ i j, ¬ dependent i j → 𝘚₁)
    (hdisjoint : ∀ i j, ¬ dependent i j → Disjoint (patch i) (patch j))
    initial j h fresh :
    historyMarkedRawState dependent
      (fun j e => rawPatchUpdate j (patch j) 𝔅 slope 𝔅 intercept 𝔅 response) initial
      (𝙯₁ 𝘥₂) =
    rawPatchUpdate j (patch j) 𝔊 slope 𝔊 intercept 𝔊 response
      (historyMarkedRawState dependent
        (fun j e => rawPatchUpdate j (patch j) 𝔅 slope 𝔅 intercept 𝔅 response) initial h) := by
  apply historyMarkedRawState_append
  intro i j h e f state
  exact rawPatchUpdate_commute _ _ _ _ _ _ _ _ (hdistinct i j h) (hdisjoint i j h) state

𝗃 𝔐 ἀ d k
𝗇 𝔉 fun i j => j ∈ 𝔐 highNeighborLabels i
𝗇 𝔏 𝔐 highTorusPatch j
𝗇 𝔄 historyMarkedRawState 𝔉 (fun j e => rawPatchUpdate j 𝔏 𝔅 slope 𝔅 intercept 𝔅 response) initial
𝗇 𝔇 fun {_ _} h => 𝔐 highNeighborLabels_symmetric _ _ h
𝗇 𝔈 𝔉
𝗇 𝔎 𝔐 HighWindowLabels
/-- The torus-neighbour dependency gives canonical append compatibility
for arbitrary full-mark density and coefficient resets. -/
theorem highMarkedRawState_patch_append (d k : ℕ) [NeZero k]
    [LinearOrder 𝔎]
    [MeasurableSpace E]
    (slope intercept : 𝔎 → E → 𝙀)
    (response : 𝔎 → E → R → R)
    initial
    j
    h fresh :
    𝔄
      (historyMarkedAppend 𝔈
        𝔇 j 𝘥₂) =
    rawPatchUpdate j 𝔏 𝔊 slope 𝔊 intercept 𝔊 response
      (𝔄 h) := by
  have hi : ∀ i j , j ∉ 𝔐 highNeighborLabels i → 𝘚₁ := by
    intro i j h he
    subst j
    exact h $ 𝔐 highNeighborLabels_self_mem i
  exact historyMarkedRawState_patch_append
    𝔈
    𝔇
    𝔐 highTorusPatch slope intercept response hi (fun i j h => 𝔐 highTorusPatch_disjoint_of_not_neighbor i j h) initial j h fresh
