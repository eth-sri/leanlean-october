module

public import NearlyMinimax.FiniteAffineHistoryMean
public import NearlyMinimax.HighPacketBalancing
public import NearlyMinimax.HighRawUpdates
public import NearlyMinimax.HighRawDensityLocality

@[expose] public section

/-! The actual balanced packet retains the representation mark in its
spatial density reset. Its finite canonical histories have pointwise mean
one under their genuine independent reference mark laws. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators ENNReal
namespace NearlyMinimax
attribute [local instance] Classical.propDecidable

theorem affinePatchFold_density_eq {J X E V I : Type*} [DecidableEq J]
    (patch : J → Set X) (slope offset : J → E → X → ℝ)
    (response : J → E → V → V) (labels : I → J) (marks : I → E)
    (indices : List I) (initial : (X → ℝ) × (J → V)) (x : X) :
    (indices.foldl (fun θ i => rawPatchUpdate (labels i) (patch (labels i))
      (slope (labels i) (marks i)) (offset (labels i) (marks i))
      (response (labels i) (marks i)) θ) initial).1 x =
      indices.foldl (fun v i =>
        (if x ∈ patch (labels i) then slope (labels i) (marks i) x else 1) * v +
        (if x ∈ patch (labels i) then offset (labels i) (marks i) x else 0)) (initial.1 x) := by
  induction indices generalizing initial with
  | nil => rfl
  | cons i indices ih =>
    simp only [List.foldl_cons]
    rw [ih]
    by_cases hx : x ∈ patch (labels i) <;>
      simp only [rawPatchUpdate, affinePatchUpdate, hx, ite_true, ite_false, one_mul, add_zero]

theorem affinePatchFold_density_joint_measurable {J X E V : Type*} [DecidableEq J]
    [MeasurableSpace X] [MeasurableSpace E]
    (patch : J → Set X) (hpatch : ∀ j, MeasurableSet (patch j))
    (slope offset : J → E → X → ℝ)
    (hs : ∀ j, Measurable (fun ex : E × X => slope j ex.1 ex.2))
    (ho : ∀ j, Measurable (fun ex : E × X => offset j ex.1 ex.2))
    (response : J → E → V → V) (n : ℕ) (labels : Fin n → J) (indices : List (Fin n))
    (initial : (Fin n → E) → (X → ℝ) × (J → V))
    (hi : Measurable (fun mx : (Fin n → E) × X => (initial mx.1).1 mx.2)) :
    Measurable (fun mx : (Fin n → E) × X =>
      (indices.foldl (fun θ i => rawPatchUpdate (labels i) (patch (labels i))
        (slope (labels i) (mx.1 i)) (offset (labels i) (mx.1 i))
        (response (labels i) (mx.1 i)) θ) (initial mx.1)).1 mx.2) := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i indices ih =>
    simp only [List.foldl_cons]
    apply ih (fun marks => rawPatchUpdate (labels i) (patch (labels i))
      (slope (labels i) (marks i)) (offset (labels i) (marks i))
      (response (labels i) (marks i)) (initial marks))
    change Measurable (fun mx : (Fin n → E) × X =>
      if mx.2 ∈ patch (labels i) then slope (labels i) (mx.1 i) mx.2 *
        (initial mx.1).1 mx.2 + offset (labels i) (mx.1 i) mx.2 else (initial mx.1).1 mx.2)
    have hcoord : Measurable (fun mx : (Fin n → E) × X => (mx.1 i, mx.2)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
    exact Measurable.ite ((hpatch _).preimage measurable_snd)
      (((hs (labels i)).comp hcoord).mul hi |>.add ((ho (labels i)).comp hcoord)) hi

section Packet
variable {Z : Type*} [MeasurableSpace Z] (d k F m r D q : ℕ)

end Packet
end NearlyMinimax
