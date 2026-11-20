module

public import NearlyMinimax.HistoryMarkedStateAppend
public import NearlyMinimax.HighWindowGeometry

@[expose] public section

/-! Canonical append for genuine mark-dependent patch resets. Slopes and
intercepts may depend on the entire source mark, including its spatial mark. -/
noncomputable section
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedRawState_patch_append {Z E R : Type*} [DecidableEq J] [MeasurableSpace E]
    (dependent : J → J → Prop)
    [Std.Symm dependent]
    (patch : J → Set Z) (slope intercept : J → E → Z → ℝ)
    (response : J → E → R → R)
    (hdistinct : ∀ i j, ¬ dependent i j → i ≠ j)
    (hdisjoint : ∀ i j, ¬ dependent i j → Disjoint (patch i) (patch j))
    (initial : (Z → ℝ) × (J → R)) (j : J) (h : HistoryMarked dependent E) (fresh : E) :
    historyMarkedRawState
      (fun j e => rawPatchUpdate j (patch j) (slope j e) (intercept j e) (response j e)) initial
      (historyMarkedAppend j (h, fresh)) =
    rawPatchUpdate j (patch j) (slope j fresh) (intercept j fresh) (response j fresh)
      (historyMarkedRawState
        (fun j e => rawPatchUpdate j (patch j) (slope j e) (intercept j e) (response j e)) initial h) := by
  apply historyMarkedRawState_append
  intro i j h e f state
  solve_by_elim [rawPatchUpdate_commute]

/-- The torus-neighbour dependency gives canonical append compatibility
for arbitrary full-mark density and coefficient resets. -/
theorem highMarkedRawState_patch_append {d k : ℕ} [NeZero k]
    [LinearOrder (HighWindowLabels d k)]
    {E R : Type*} [MeasurableSpace E]
    (slope intercept : HighWindowLabels d k → E → Covariate d → ℝ)
    (response : HighWindowLabels d k → E → R → R)
    (initial : (Covariate d → ℝ) × (HighWindowLabels d k → R))
    (j : HighWindowLabels d k)
    (h : HistoryMarked (windowDepends d k) E) (fresh : E) :
    let state := historyMarkedRawState (fun j e => rawPatchUpdate j (highTorusPatch j) (slope j e) (intercept j e) (response j e)) initial
    state
      (historyMarkedAppend j (h, fresh)) =
    rawPatchUpdate j (highTorusPatch j) (slope j fresh) (intercept j fresh) (response j fresh)
      (state h) := by
  have hi : ∀ i j : HighWindowLabels d k, j ∉ highNeighborLabels i → i ≠ j := by
    intro i j h he
    grind [highNeighborLabels_self_mem d k i]
  have hd  :=
    fun i j h => highTorusPatch_disjoint_of_not_neighbor (d := d) (k := k) (j := i) (l := j) h
  solve_by_elim [historyMarkedRawState_patch_append]

end NearlyMinimax
