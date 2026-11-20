module

public import RequestProject.SquareBoundary
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Tactic

@[expose] public section

/-! The four closed sides give an actual compact quotient presentation
of the square boundary. Maps and homotopies on the sides descend whenever
their values agree at the corners. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true

namespace FiniteChains.RelativeAttachment
open scoped Topology unitInterval Classical
open Topology

abbrev SquareSide := Fin 2 × Bool
abbrev SquareBoundary := (Cube.boundary (Fin 2))

def boolEndpoint (b : Bool) : I := if b then 1 else 0

theorem boolEndpoint_injective : Function.Injective boolEndpoint := by
  simp [boolEndpoint]

theorem boolEndpoint_zero_or_one (b : Bool) : boolEndpoint b = 0 ∨ boolEndpoint b = 1 := by
  simp [boolEndpoint]

def squareSideMap (s : SquareSide) : C(I, SquareBoundary) where
  toFun t := ⟨Whitehead.squareEdge s.1 (boolEndpoint s.2) t, s.1, by
    rcases boolEndpoint_zero_or_one s.2 with h | h
    · simp [Whitehead.squareEdge, h]
    · simp [Whitehead.squareEdge, h]⟩
  continuous_toFun := (Whitehead.squareEdge_continuous _ _).subtype_mk _

def squareSideQuotient : C((Σ _ : SquareSide, I), SquareBoundary) :=
  ⟨fun st => squareSideMap st.1 st.2, continuous_sigma (fun s => (squareSideMap s).continuous)⟩

theorem squareSideQuotient_surjective : Function.Surjective squareSideQuotient := by
  intro x
  obtain ⟨i, hi⟩ := x.property
  rcases hi with hi | hi
  · refine ⟨⟨(i, false), x.val (if i = 0 then 1 else 0)⟩, ?_⟩
    apply Subtype.ext
    funext j
    fin_cases i <;> fin_cases j <;> simp_all [squareSideQuotient, squareSideMap,
      Whitehead.squareEdge, boolEndpoint]
  · refine ⟨⟨(i, true), x.val (if i = 0 then 1 else 0)⟩, ?_⟩
    apply Subtype.ext
    funext j
    fin_cases i <;> fin_cases j <;> simp_all [squareSideQuotient, squareSideMap,
      Whitehead.squareEdge, boolEndpoint]

/-- Two different sides meet only at their prescribed endpoints. -/
theorem squareSideMap_fiber {s r : SquareSide} {t u : I}
    (h : squareSideMap s t = squareSideMap r u) :
    (s = r ∧ t = u) ∨ (t = boolEndpoint r.2 ∧ u = boolEndpoint s.2) := by
  have hv : Whitehead.squareEdge s.1 _ t =
      Whitehead.squareEdge r.1 _ u := congrArg Subtype.val h
  by_cases hi : s.1 = r.1
  · have hb : boolEndpoint s.2 = boolEndpoint r.2 := by
      have he := congrFun hv s.1
      simp_all [Whitehead.squareEdge, hi]
    have hs := Prod.ext hi (boolEndpoint_injective hb)
    have ht : t = u := by
      have he := congrFun hv (if s.1 = 0 then 1 else 0)
      grind [Whitehead.squareEdge]
    simp_all
  · refine Or.inr ⟨?_, ?_⟩
    · have he := congrFun hv r.1
      simp_all [Whitehead.squareEdge, hi, Ne.symm]
    · have he := congrFun hv s.1
      simp_all [Whitehead.squareEdge, hi, Ne.symm]

theorem squareSideQuotient_isQuotientMap : IsQuotientMap squareSideQuotient :=
  squareSideQuotient.continuous.isClosedMap.isQuotientMap
    squareSideQuotient.continuous squareSideQuotient_surjective

variable {X : Type} [TopologicalSpace X]

variable (f : C((Σ _ : SquareSide, I), X))
    (hf : ∀ a b, squareSideQuotient a = squareSideQuotient b → f a = f b)

def squareBoundaryDesc :
    C(SquareBoundary, X) where
  toFun x := f (Function.surjInv squareSideQuotient_surjective x)
  continuous_toFun := by
    apply squareSideQuotient_isQuotientMap.continuous_iff.mpr
    have he : (fun x => f (Function.surjInv squareSideQuotient_surjective x)) ∘
        squareSideQuotient = f := by
      funext a
      exact hf _ a (Function.surjInv_eq squareSideQuotient_surjective _)
    rw [he]
    exact f.continuous

@[simp] theorem squareBoundaryDesc_side
    (s : SquareSide) (t : I) :
    squareBoundaryDesc f hf (squareSideMap s t) = f ⟨s, t⟩ :=
  hf _ _ (Function.surjInv_eq squareSideQuotient_surjective _)

variable (f : SquareSide → C(I, X))
    (V : SquareBoundary → X)
    (hV : ∀ s t, t = 0 ∨ t = 1 → f s t = V (squareSideMap s t))

def squareBoundaryPasting :
    C(SquareBoundary, X) := by
  apply squareBoundaryDesc (⟨fun st => f st.1 st.2, continuous_sigma (fun s => (f s).continuous)⟩)
  rintro ⟨s, t⟩ ⟨r, u⟩ he
  change f s t = f r u
  rcases squareSideMap_fiber he with ⟨rfl, rfl⟩ | ⟨ht, hu⟩
  · rfl
  · rw [hV s t (by grind [boolEndpoint_zero_or_one]),
      hV r u (by grind [boolEndpoint_zero_or_one])]
    exact congrArg V he

@[simp] theorem squareBoundaryPasting_side
    (s : SquareSide) (t : I) :
    squareBoundaryPasting f V hV (squareSideMap s t) = f s t := squareBoundaryDesc_side _ _ s t

variable (H : SquareSide → C(I × I, X))
    (V : I → SquareBoundary → X)
    (hV : ∀ s τ t, t = 0 ∨ t = 1 → H s (τ, t) = V τ (squareSideMap s t))

/-- Jointly continuous side homotopies paste to a jointly continuous
boundary homotopy. Only corner values of `V` are used, so no continuity
of a chosen family of vertex paths over the whole boundary is required. -/
def squareBoundaryHomotopyPasting :
    C(I × SquareBoundary, X) := by
  let F : C((Σ _ : SquareSide, I), C(I, X)) :=
    ⟨fun st => ((H st.1).comp ⟨Prod.swap, continuous_swap⟩).curry st.2,
      continuous_sigma (fun s => ((H s).comp ⟨Prod.swap, continuous_swap⟩).curry.continuous)⟩
  have hF : ∀ a b, squareSideQuotient a = squareSideQuotient b → F a = F b := by
    rintro ⟨s, t⟩ ⟨r, u⟩ he
    apply ContinuousMap.ext
    intro τ
    change H s (τ, t) = H r (τ, u)
    rcases squareSideMap_fiber he with ⟨rfl, rfl⟩ | ⟨ht, hu⟩
    · rfl
    · rw [hV s τ t (by grind [boolEndpoint_zero_or_one]),
        hV r τ u (by grind [boolEndpoint_zero_or_one])]
      solve_by_elim
  exact (squareBoundaryDesc F hF).uncurry.comp ⟨Prod.swap, continuous_swap⟩

@[simp] theorem squareBoundaryHomotopyPasting_side
    (s : SquareSide) (τ t : I) :
    squareBoundaryHomotopyPasting H V hV (τ, squareSideMap s t) = H s (τ, t) := by
  dsimp only [squareBoundaryHomotopyPasting, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, ContinuousMap.uncurry_apply, Function.uncurry, Prod.swap]
  rw [squareBoundaryDesc_side]
  rfl

end FiniteChains.RelativeAttachment
