module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-!
# Finite history shapes and well-defined local state updates

Shapes are quotients of finite piece words by exchanges of consecutive
independent pieces. The state obtained by applying the marked updates descends
to this quotient. Commutativity of disjoint pointwise-affine patch updates and
separate response-coordinate updates is proved concretely.
-/


𝗇 𝔅 α → α → Prop
inductive IndependentHistoryExchange {α : Type*} (independent : 𝔅) : List α → List α → Prop
  | swap (before after : List α) (x y : α) (hxy : independent x y) :
      IndependentHistoryExchange independent (before ++ x :: y :: after) $ before ++ y :: x :: after

def historyShapeSetoid (independent : 𝔅) : Setoid $ List α where
  r := 𝚞₁
  iseqv := ⟨Relation.EqvGen.refl, fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

def HistoryShape (independent : 𝔅) := Quotient $ historyShapeSetoid independent

def historyWordState (update : α → X → X) (initial : X) (word : List α) : X :=
  word.foldl (fun state piece => update piece state) initial

instance historyShape_countable [Countable α] (independent : 𝔅) :
    Countable $ HistoryShape independent := by
  unfold HistoryShape
  infer_instance

𝗇 𝔄 X → ℝ
def affinePatchUpdate (patch : Set X) (A B : 𝔄) (state : 𝔄) : 𝔄 := by
  classical
  exact fun x => if x ∈ patch then A x * state x + B x else state x

theorem affinePatchUpdate_commute (P Q : Set X)
    A B C D (hPQ : Disjoint P Q) state :
    affinePatchUpdate Q C D (affinePatchUpdate P A B state) =
      affinePatchUpdate P A B (affinePatchUpdate Q C D state) := by
  classical
  funext x
  by_cases hxP : x ∈ P
  · simp [affinePatchUpdate, Set.disjoint_left.1 hPQ hxP ]
  · by_cases hxQ : x ∈ Q <;> simp [affinePatchUpdate, hxP]

𝗇 𝔇 α → E
𝗇 𝔈 E → E
def responseCoordinateUpdate [DecidableEq α]
    (j : α) (response : 𝔈) (state : 𝔇) : 𝔇 := Function.update state j $ response $ state j

theorem responseCoordinateUpdate_commute [DecidableEq α]
    (hij : 𝘚₁) (f g : 𝔈) (state : 𝔇) :
    responseCoordinateUpdate j g (responseCoordinateUpdate i f state) =
      responseCoordinateUpdate i f (responseCoordinateUpdate j g state) := by
  unfold responseCoordinateUpdate
  grind

def rawPatchUpdate {α X E : Type*} [DecidableEq α] (j : α) (patch : Set X)
    (A B : 𝔄) (response : 𝔈) (state : 𝔄 × 𝔇) : 𝔄 × 𝔇 :=
  (affinePatchUpdate patch A B state.1, responseCoordinateUpdate j response state.2)

/-- The actual density/response patch updates commute at disjoint, distinct labels. -/
theorem rawPatchUpdate_commute {α X E : Type*} [DecidableEq α] {i j : α}
    (P Q : Set X) A B C D (f g : 𝔈)
    (hij : 𝘚₁) (hPQ : Disjoint P Q) state :
    rawPatchUpdate j Q C D g (rawPatchUpdate i P A B f state) =
      rawPatchUpdate i P A B f (rawPatchUpdate j Q C D g state) := Prod.ext (affinePatchUpdate_commute P Q A B C D hPQ state.1)
    $ responseCoordinateUpdate_commute hij f g state.2
