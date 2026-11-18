module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Tactic
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib

@[expose] public section
noncomputable section
namespace Homeomorph

abbrev toContinuousMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : C(X, Y) := ⟨e, e.continuous⟩

end Homeomorph

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u v
variable (E : Type u) [NormedAddCommGroup E]

abbrev ClosedUnitBall := {x : E // ‖x‖ ≤ 1}
abbrev UnitBoundary := {x : E // ‖x‖ = 1}

def unitBoundaryInclusion : C(UnitBoundary E, ClosedUnitBall E) :=
  ⟨fun x => ⟨x.val, x.property.le⟩, continuous_subtype_val.subtype_mk _⟩

abbrev BallCylinderBoundary :=
  {z : I × ClosedUnitBall E // z.1 = 0 ∨ ‖z.2.val‖ = 1}

variable {E}

def cylinderDenominator (z : I × ClosedUnitBall E) : ℝ :=
  max (2 - (z.1 : ℝ)) (2 * ‖z.2.val‖)

theorem cylinderDenominator_pos (z : I × ClosedUnitBall E) :
    0 < cylinderDenominator z := by
  have h := z.1.2.2
  have hle : 2 - z.1 ≤ cylinderDenominator z := le_max_left _ _
  linarith

theorem cylinderDenominator_le_two (z : I × ClosedUnitBall E) :
    cylinderDenominator z ≤ 2 := by
  apply max_le
  · grind
  · grind

def cylinderScale (z : I × ClosedUnitBall E) : ℝ :=
  2 / cylinderDenominator z

theorem cylinderScale_nonneg (z : I × ClosedUnitBall E) :
    0 ≤ cylinderScale z :=
  div_nonneg (by norm_num) (cylinderDenominator_pos z).le

theorem cylinderScale_mul_denominator (z : I × ClosedUnitBall E) :
    cylinderScale z * cylinderDenominator z = 2 :=
  div_mul_cancel₀ _ (ne_of_gt (cylinderDenominator_pos z))


theorem cylinderScale_continuous :
    Continuous (cylinderScale : I × ClosedUnitBall E → ℝ) := by
  apply continuous_const.div
  · unfold cylinderDenominator
    fun_prop
  · exact fun z => ne_of_gt (cylinderDenominator_pos z)

def cylinderTime (z : I × ClosedUnitBall E) : I :=
  ⟨2 - cylinderScale z * (2 - (z.1 : ℝ)), by
    have hscale := cylinderScale_nonneg z
    have hmul := cylinderScale_mul_denominator z
    have hden : 2 - (z.1 : ℝ) ≤ cylinderDenominator z := le_max_left _ _
    have hbound := mul_le_mul_of_nonneg_left hden hscale
    constructor
    · linarith
    · have hone := (show 1 ≤ cylinderScale z by
      apply (le_div_iff₀ (cylinderDenominator_pos z)).mpr
      simpa using cylinderDenominator_le_two z)
      have ht : 1 ≤ 2 - (z.1 : ℝ) := by linarith [z.1.2.2]
      have hlower := mul_le_mul_of_nonneg_left ht hscale
      linarith⟩

theorem cylinderTime_continuous :
    Continuous (cylinderTime : I × ClosedUnitBall E → I) :=
  (continuous_const.sub (cylinderScale_continuous.mul
    (continuous_const.sub continuous_fst.subtype_val))).subtype_mk _

variable [NormedSpace ℝ E]

def cylinderPoint (z : I × ClosedUnitBall E) : ClosedUnitBall E :=
  ⟨cylinderScale z • z.2.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cylinderScale_nonneg z)]
    have hden : 2 * ‖z.2.val‖ ≤ cylinderDenominator z := le_max_right _ _
    have hm := mul_le_mul_of_nonneg_left hden (cylinderScale_nonneg z)
    have he := cylinderScale_mul_denominator z
    nlinarith⟩



/-- The actual cylinder retraction, valid for every real normed vector space. -/
def ballCylinderRetraction : C(I × ClosedUnitBall E, BallCylinderBoundary E) :=
  ⟨fun z => ⟨(cylinderTime z, cylinderPoint z), (show cylinderTime z = 0 ∨ ‖(cylinderPoint z).val‖ = 1 by
    by_cases h : 2 * ‖z.2.val‖ ≤ 2 - (z.1 : ℝ)
    · left
      apply Subtype.ext
      have he := cylinderScale_mul_denominator z
      rw [cylinderDenominator, max_eq_left h] at he
      change 2 - cylinderScale z * (2 - (z.1 : ℝ)) = 0
      linarith
    · right
      have he := cylinderScale_mul_denominator z
      rw [cylinderDenominator, max_eq_right (le_of_not_ge h)] at he
      change ‖cylinderScale z • z.2.val‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cylinderScale_nonneg z)]
      nlinarith)⟩,
    (cylinderTime_continuous.prodMk ((cylinderScale_continuous.smul continuous_snd.subtype_val).subtype_mk _)).subtype_mk _⟩

omit [NormedSpace ℝ E] in
theorem cylinderScale_eq_one (z : I × ClosedUnitBall E)
    (hz : z.1 = 0 ∨ ‖z.2.val‖ = 1) : cylinderScale z = 1 := by
  have hden : cylinderDenominator z = 2 := by
    apply le_antisymm (cylinderDenominator_le_two z)
    rcases hz with ht | hx
    · have h : 2 - z.1 ≤ cylinderDenominator z := le_max_left _ _
      rw [ht] at h
      simpa using h
    · have h : 2 * ‖z.2.val‖ ≤ cylinderDenominator z := le_max_right _ _
      simpa only [hx, mul_one] using h
  simp only [cylinderScale, hden, div_self (by norm_num : (2 : ℝ) ≠ 0)]

theorem ballCylinderRetraction_fixed (z : BallCylinderBoundary E) :
    ballCylinderRetraction z.val = z := by
  apply Subtype.ext
  apply Prod.ext
  · ext
    change 2 - cylinderScale z.val * (2 - z.val.1) = z.val.1
    rw [cylinderScale_eq_one z.val z.property]
    ring
  · ext
    change cylinderScale z.val • z.val.2.val = z.val.2.val
    rw [cylinderScale_eq_one z.val z.property, one_smul]

variable {Z : Type v} [TopologicalSpace Z]

def ballBoundaryPastingFun (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z)) (z : BallCylinderBoundary E) : Z :=
  if ht : z.val.1 = 0 then f z.val.2
  else H (z.val.1, ⟨z.val.2.val, z.property.resolve_left ht⟩)

omit [NormedSpace ℝ E] in
theorem ballBoundaryPastingFun_bottom (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z)) (z : BallCylinderBoundary E) (hz : z.val.1 = 0) :
    ballBoundaryPastingFun f H z = f z.val.2 := by
  simp only [ballBoundaryPastingFun]; rw [dite_eq_left hz]

omit [NormedSpace ℝ E] in
theorem ballBoundaryPastingFun_side (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z))
    (h₀ : ∀ x, H (0, x) = f (unitBoundaryInclusion E x))
    (z : BallCylinderBoundary E) (hz : ‖z.val.2.val‖ = 1) :
    ballBoundaryPastingFun f H z = H (z.val.1, ⟨z.val.2.val, hz⟩) := by
  by_cases ht : z.val.1 = 0
  · rw [ballBoundaryPastingFun_bottom f H z ht, ht, h₀]
    rfl
  · simp only [ballBoundaryPastingFun]; rw [dite_eq_right ht]

/-- The supplied disk map and its boundary homotopy paste continuously on
the closed bottom and side of the cylinder. -/
def ballBoundaryPasting (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z))
    (h₀ : ∀ x, H (0, x) = f (unitBoundaryInclusion E x)) :
    C(BallCylinderBoundary E, Z) where
  toFun := ballBoundaryPastingFun f H
  continuous_toFun := by
    let B : Set (BallCylinderBoundary E) := {z | z.val.1 = 0}
    let S : Set (BallCylinderBoundary E) := {z | ‖z.val.2.val‖ = 1}
    have hB : IsClosed B := isClosed_eq (by fun_prop) continuous_const
    have hS : IsClosed S := isClosed_eq (by fun_prop) continuous_const
    have hcover : B ∪ S = Set.univ := by
      apply Set.eq_univ_of_forall
      exact fun z => z.property
    have hf : ContinuousOn (ballBoundaryPastingFun f H) B := by
      apply ((f.continuous.comp (continuous_snd.comp continuous_subtype_val)).continuousOn).congr
      intro z hz
      exact ballBoundaryPastingFun_bottom f H z hz
    have hh : ContinuousOn (ballBoundaryPastingFun f H) S := by
      rw [continuousOn_iff_continuous_domRestrict]
      let k : C(S, I × UnitBoundary E) := {
        toFun := fun z => (z.val.val.1, ⟨z.val.val.2.val, z.property⟩)
        continuous_toFun := by fun_prop }
      have he : S.domRestrict (ballBoundaryPastingFun f H) = H ∘ k := by
        funext z
        exact ballBoundaryPastingFun_side f H h₀ z.val z.property
      rw [he]
      exact H.continuous.comp k.continuous
    rw [← continuousOn_univ, ← hcover]
    exact hf.union_of_isClosed hh hB hS

/-- Explicit homotopy extension across a closed disk. -/
def ballHomotopyExtension (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z))
    (h₀ : ∀ x, H (0, x) = f (unitBoundaryInclusion E x)) :
    C(I × ClosedUnitBall E, Z) :=
  (ballBoundaryPasting f H h₀).comp ballCylinderRetraction

@[simp] theorem ballHomotopyExtension_zero (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z))
    (h₀ : ∀ x, H (0, x) = f (unitBoundaryInclusion E x)) (x : ClosedUnitBall E) :
    ballHomotopyExtension f H h₀ (0, x) = f x := by
  change ballBoundaryPasting f H h₀ (ballCylinderRetraction (0, x)) = f x
  rw [ballCylinderRetraction_fixed ⟨(0, x), Or.inl rfl⟩]
  exact ballBoundaryPastingFun_bottom f H _ rfl

@[simp] theorem ballHomotopyExtension_boundary (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z))
    (h₀ : ∀ x, H (0, x) = f (unitBoundaryInclusion E x))
    (t : I) (x : UnitBoundary E) :
    ballHomotopyExtension f H h₀ (t, unitBoundaryInclusion E x) = H (t, x) := by
  change ballBoundaryPasting f H h₀
    (ballCylinderRetraction (t, unitBoundaryInclusion E x)) = H (t, x)
  rw [ballCylinderRetraction_fixed
    ⟨(t, unitBoundaryInclusion E x), Or.inr x.property⟩]
  exact ballBoundaryPastingFun_side f H h₀ _ x.property

end FiniteChains.RelativeAttachment

section
open scoped unitInterval Topology
namespace Whitehead

/-- A side of the unit square. -/
def squareEdge (i : Fin 2) (v : I) (s : I) : Fin 2 → I :=
  fun j => if j = i then v else s

theorem squareEdge_continuous (i : Fin 2) (v : I) : Continuous (squareEdge i v) := by
  apply continuous_pi
  intro j
  by_cases h : j = i
  · simpa [squareEdge, h] using continuous_const
  · exact continuous_id.congr fun s => by simp [squareEdge, h]

theorem square_boundary_eq : Cube.boundary (Fin 2) =
    ((Set.range (squareEdge 0 0) ∪ Set.range (squareEdge 1 0)) ∪
      Set.range (squareEdge 0 1)) ∪ Set.range (squareEdge 1 1) := by
  ext t
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · rcases hi with hi | hi
      · exact Or.inl (Or.inl (Or.inl ⟨t 1, by apply funext; intro j; fin_cases j; exact hi.symm; rfl⟩))
      · exact Or.inl (Or.inr ⟨t 1, by apply funext; intro j; fin_cases j; exact hi.symm; rfl⟩)
    · rcases hi with hi | hi
      · exact Or.inl (Or.inl (Or.inr ⟨t 0, by apply funext; intro j; fin_cases j; rfl; exact hi.symm⟩))
      · exact Or.inr ⟨t 0, by apply funext; intro j; fin_cases j; rfl; exact hi.symm⟩
  · rintro (((⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨s, rfl⟩) | ⟨s, rfl⟩)
    · exact ⟨0, Or.inl (by simp [squareEdge])⟩
    · exact ⟨1, Or.inl (by simp [squareEdge])⟩
    · exact ⟨0, Or.inr (by simp [squareEdge])⟩
    · exact ⟨1, Or.inr (by simp [squareEdge])⟩

/-- The boundary of the two-dimensional cube is preconnected. -/
theorem square_boundary_isPreconnected : IsPreconnected (Cube.boundary (Fin 2)) := by
  rw [square_boundary_eq]
  have he i v : IsPreconnected (Set.range (squareEdge i v)) :=
    isPreconnected_range (squareEdge_continuous i v)
  have h00 : squareEdge 0 0 0 = squareEdge 1 0 0 := by
    ext j; fin_cases j <;> simp [squareEdge]
  have h10 : squareEdge 0 1 0 = squareEdge 1 0 1 := by
    ext j; fin_cases j <;> simp [squareEdge]
  have h01 : squareEdge 1 1 0 = squareEdge 0 0 1 := by
    ext j; fin_cases j <;> simp [squareEdge]
  have hleft : IsPreconnected (Set.range (squareEdge 0 0) ∪ Set.range (squareEdge 1 0)) := (he 0 0).union' ⟨squareEdge 0 0 0, ⟨0, rfl⟩, ⟨0, h00.symm⟩⟩ (he 1 0)
  have hthree : IsPreconnected ((Set.range (squareEdge 0 0) ∪ Set.range (squareEdge 1 0)) ∪ Set.range (squareEdge 0 1)) := hleft.union'
    ⟨squareEdge 0 1 0, Or.inr ⟨1, h10.symm⟩, ⟨0, rfl⟩⟩ (he 0 1)
  exact hthree.union'
    ⟨squareEdge 1 1 0, Or.inl (Or.inl ⟨1, h01.symm⟩), ⟨0, rfl⟩⟩ (he 1 1)

end Whitehead
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.RelativeAttachment
open scoped Topology unitInterval Classical
open Topology

abbrev SquareSide := Fin 2 × Bool
abbrev SquareBoundary := (Cube.boundary (Fin 2) : Set (Fin 2 → I))

def boolEndpoint (b : Bool) : I := if b then 1 else 0

theorem boolEndpoint_injective : Function.Injective boolEndpoint := by simp_all [boolEndpoint]

theorem boolEndpoint_zero_or_one (b : Bool) : boolEndpoint b = 0 ∨ boolEndpoint b = 1 := by
  cases b <;> simp [boolEndpoint]

def squareSideMap (s : SquareSide) : C(I, SquareBoundary) where
  toFun t := ⟨Whitehead.squareEdge s.1 (boolEndpoint s.2) t, s.1, by
    rcases boolEndpoint_zero_or_one s.2 with h | h
    · exact Or.inl (by simp [Whitehead.squareEdge, h])
    · exact Or.inr (by simp [Whitehead.squareEdge, h])⟩
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
  have hv : Whitehead.squareEdge s.1 (boolEndpoint s.2) t =
      Whitehead.squareEdge r.1 (boolEndpoint r.2) u := congrArg Subtype.val h
  by_cases hi : s.1 = r.1
  · have hb : boolEndpoint s.2 = boolEndpoint r.2 := by
      have he := congrFun hv s.1
      simpa [Whitehead.squareEdge, hi] using he
    have hs  := Prod.ext hi (boolEndpoint_injective hb)
    subst r
    have ht : t = u := by
      have he := congrFun hv (if s.1 = 0 then 1 else 0)
      rcases s with ⟨i, b⟩
      fin_cases i <;> simpa [Whitehead.squareEdge] using he
    exact Or.inl ⟨rfl, ht⟩
  · refine Or.inr ⟨?_, ?_⟩
    · have he := congrFun hv r.1
      simpa [Whitehead.squareEdge, hi, Ne.symm hi] using he
    · have he := congrFun hv s.1
      simpa [Whitehead.squareEdge, hi, Ne.symm hi] using he.symm

theorem squareSideQuotient_isQuotientMap : IsQuotientMap squareSideQuotient :=
  squareSideQuotient.continuous.isClosedMap.isQuotientMap
    squareSideQuotient.continuous squareSideQuotient_surjective

variable {X : Type} [TopologicalSpace X]

def squareBoundaryDesc (f : C((Σ _ : SquareSide, I), X))
    (hf : ∀ a b, squareSideQuotient a = squareSideQuotient b → f a = f b) :
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

@[simp] theorem squareBoundaryDesc_side (f : C((Σ _ : SquareSide, I), X))
    (hf : ∀ a b, squareSideQuotient a = squareSideQuotient b → f a = f b)
    (s : SquareSide) (t : I) :
    squareBoundaryDesc f hf (squareSideMap s t) = f ⟨s, t⟩ :=
  hf _ _ (Function.surjInv_eq squareSideQuotient_surjective _)

def squareBoundaryPasting (f : SquareSide → C(I, X))
    (V : SquareBoundary → X)
    (hV : ∀ s t, t = 0 ∨ t = 1 → f s t = V (squareSideMap s t)) :
    C(SquareBoundary, X) := by
  let F : C((Σ _ : SquareSide, I), X) :=
    ⟨fun st => f st.1 st.2, continuous_sigma (fun s => (f s).continuous)⟩
  apply squareBoundaryDesc F
  rintro ⟨s, t⟩ ⟨r, u⟩ he
  change f s t = f r u
  rcases squareSideMap_fiber he with ⟨rfl, rfl⟩ | ⟨ht, hu⟩
  · rfl
  · change t = boolEndpoint r.2 at ht
    change u = boolEndpoint s.2 at hu
    rw [hV s t (by rw [ht]; exact boolEndpoint_zero_or_one r.2),
      hV r u (by rw [hu]; exact boolEndpoint_zero_or_one s.2)]
    exact congrArg V he

@[simp] theorem squareBoundaryPasting_side (f : SquareSide → C(I, X))
    (V : SquareBoundary → X)
    (hV : ∀ s t, t = 0 ∨ t = 1 → f s t = V (squareSideMap s t))
    (s : SquareSide) (t : I) :
    squareBoundaryPasting f V hV (squareSideMap s t) = f s t := by
  unfold squareBoundaryPasting
  exact squareBoundaryDesc_side _ _ s t

/-- Jointly continuous side homotopies paste to a jointly continuous
boundary homotopy. Only corner values of `V` are used, so no continuity
of a chosen family of vertex paths over the whole boundary is required. -/
def squareBoundaryHomotopyPasting (H : SquareSide → C(I × I, X))
    (V : I → SquareBoundary → X)
    (hV : ∀ s τ t, t = 0 ∨ t = 1 → H s (τ, t) = V τ (squareSideMap s t)) :
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
    · change t = boolEndpoint r.2 at ht
      change u = boolEndpoint s.2 at hu
      rw [hV s τ t (by rw [ht]; exact boolEndpoint_zero_or_one r.2),
        hV r τ u (by rw [hu]; exact boolEndpoint_zero_or_one s.2)]
      exact congrArg (V τ) he
  exact (squareBoundaryDesc F hF).uncurry.comp ⟨Prod.swap, continuous_swap⟩

@[simp] theorem squareBoundaryHomotopyPasting_side
    (H : SquareSide → C(I × I, X)) (V : I → SquareBoundary → X)
    (hV : ∀ s τ t, t = 0 ∨ t = 1 → H s (τ, t) = V τ (squareSideMap s t))
    (s : SquareSide) (τ t : I) :
    squareBoundaryHomotopyPasting H V hV (τ, squareSideMap s t) = H s (τ, t) := by simp_all [squareBoundaryHomotopyPasting, ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.uncurry_apply, Function.uncurry, Prod.swap, SquareSide]

end FiniteChains.RelativeAttachment
end

section
open scoped Classical
open Set Topology TopologicalSpace
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FiniteChains.RelativeAttachment

universe u
variable {A X D : Type u}

/-- The old points and the interior points are distinct summands. The base
map is retained in the type because it determines the attachment topology. -/
def Space (_r : A → X) (i : A → D) : Type u :=
  X ⊕ {d : D // d ∉ Set.range i}

def old (r : A → X) (i : A → D) : X → Space r i := Sum.inl

def cell (r : A → X) (i : A → D) (d : D) : Space r i :=
  if h : d ∈ Set.range i then Sum.inl (r (Classical.choose h))
  else Sum.inr ⟨d, h⟩

def quotientMap (r : A → X) (i : A → D) : X ⊕ D → Space r i :=
  Sum.elim (old r i) (cell r i)

/-- The genuinely added interior points. -/
def fresh (r : A → X) (i : A → D) : {d : D // d ∉ Set.range i} → Space r i :=
  Sum.inr

theorem old_injective (r : A → X) (i : A → D) : Function.Injective (old r i) :=
  Sum.inl_injective

@[simp] theorem cell_of_not_mem (r : A → X) (i : A → D) (d : D)
    (hd : d ∉ Set.range i) : cell r i d = Sum.inr ⟨d, hd⟩ := by
  unfold cell
  rw [dite_eq_right hd]

theorem cell_boundary (r : A → X) (i : A → D) (hi : Function.Injective i) (a : A) :
    cell r i (i a) = old r i (r a) := by
  have h : i a ∈ Set.range i := ⟨a, rfl⟩
  simp only [cell, old]
  grind

theorem quotientMap_surjective (r : A → X) (i : A → D) :
    Function.Surjective (quotientMap r i) := by
  rintro (x | d)
  · exact ⟨Sum.inl x, rfl⟩
  · exact ⟨Sum.inr d.val, cell_of_not_mem r i d.val d.property⟩

variable [TopologicalSpace X] [TopologicalSpace D]

/-- The topology is exactly the quotient topology for adjoining the disks
along their boundaries; it is not the disjoint-sum topology on `Space`. -/
instance topology (r : A → X) (i : A → D) : TopologicalSpace (Space r i) :=
  TopologicalSpace.coinduced (quotientMap r i) inferInstance

theorem quotientMap_continuous (r : A → X) (i : A → D) :
    Continuous (quotientMap r i) := continuous_coinduced_rng

theorem old_continuous (r : A → X) (i : A → D) : Continuous (old r i) :=
  (quotientMap_continuous r i).comp continuous_inl

theorem cell_continuous (r : A → X) (i : A → D) : Continuous (cell r i) :=
  (quotientMap_continuous r i).comp continuous_inr




/-- The new interiors have their original topology and form an open subset
of the attachment whenever the boundary is closed. -/
theorem fresh_isOpenEmbedding (r : A → X) (i : A → D)
    (hi : IsClosed (Set.range i)) : IsOpenEmbedding (fresh r i) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (show Continuous (fresh r i) by
      have he : fresh r i = cell r i ∘ Subtype.val := by
        funext d
        exact (cell_of_not_mem r i d.val d.property).symm
      rw [he]
      exact (cell_continuous r i).comp continuous_subtype_val) Sum.inr_injective
  intro S hS
  apply isOpen_coinduced.mpr
  apply isOpen_sum_iff.mpr
  constructor
  · change IsOpen ((old r i) ⁻¹' ((fresh r i) '' S))
    rw [(show (old r i) ⁻¹' ((fresh r i) '' S) = ∅ by
      ext x
      constructor
      · rintro ⟨d, _, he⟩
        exact Sum.inr_ne_inl he
      · simp)]
    exact isOpen_empty
  · change IsOpen ((cell r i) ⁻¹' ((fresh r i) '' S))
    rw [(show (cell r i) ⁻¹' ((fresh r i) '' S) = Subtype.val '' S by
      ext d
      constructor
      · rintro ⟨v, hv, he⟩
        by_cases hd : d ∈ Set.range i
        · have he' : Sum.inr v = Sum.inl (r (Classical.choose hd)) := by
            simp only [fresh, cell] at he
            rw [dite_eq_left hd] at he
            exact he
          exact (Sum.inr_ne_inl he').elim
        · have hvd : v = ⟨d, hd⟩ := by
            apply Sum.inr_injective
            simp only [fresh, cell] at he
            rw [dite_eq_right hd] at he
            exact he
          exact ⟨v, hv, congrArg Subtype.val hvd⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v, hv, (cell_of_not_mem r i v.val v.property).symm⟩)]
    exact hi.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap _ hS

omit [TopologicalSpace X] [TopologicalSpace D] in
theorem old_fresh_disjoint (r : A → X) (i : A → D) :
    Disjoint (Set.range (old r i)) (Set.range (fresh r i)) := by simp_all [Set.disjoint_left.mpr, old, fresh]

variable {Z : Type u} [TopologicalSpace Z]

def descFun (r : A → X) (i : A → D) (f : C(X, Z)) (g : C(D, Z)) :
    Space r i → Z := Sum.elim f (fun d => g d.val)

theorem descFun_cell (r : A → X) (i : A → D) (f : C(X, Z)) (g : C(D, Z))
    (h : ∀ a, f (r a) = g (i a)) (d : D) : descFun r i f g (cell r i d) = g d := by
  simp only [cell, descFun]
  grind

/-- The actual continuous pushout map determined by compatible maps on the
base and the disks. -/
def desc (r : A → X) (i : A → D) (f : C(X, Z)) (g : C(D, Z))
    (h : ∀ a, f (r a) = g (i a)) : C(Space r i, Z) where
  toFun := descFun r i f g
  continuous_toFun := by
    apply continuous_coinduced_dom.mpr
    have he : descFun r i f g ∘ quotientMap r i = Sum.elim f g := by
      funext z
      cases z with
      | inl x => rfl
      | inr d => exact descFun_cell r i f g h d
    rw [he]
    exact f.continuous.sumElim g.continuous

@[simp] theorem desc_old (r : A → X) (i : A → D) (f : C(X, Z)) (g : C(D, Z))
    (h : ∀ a, f (r a) = g (i a)) (x : X) : desc r i f g h (old r i x) = f x := rfl

@[simp] theorem desc_cell (r : A → X) (i : A → D) (f : C(X, Z)) (g : C(D, Z))
    (h : ∀ a, f (r a) = g (i a)) (d : D) : desc r i f g h (cell r i d) = g d :=
  descFun_cell r i f g h d

theorem hom_ext (r : A → X) (i : A → D) {f g : C(Space r i, Z)}
    (hOld : ∀ x, f (old r i x) = g (old r i x))
    (hCell : ∀ d, f (cell r i d) = g (cell r i d)) : f = g := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨z, rfl⟩ := quotientMap_surjective r i z
  cases z with
  | inl x => exact hOld x
  | inr d => exact hCell d

variable [TopologicalSpace A]

omit [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace D] in
/-- Pulling an old subset back to the disks gives exactly its attached
boundary points. No old point is identified with another old point. -/
theorem cell_preimage_old_image (r : A → X) (i : A → D)
    (hi : Function.Injective i) (S : Set X) :
    (cell r i) ⁻¹' ((old r i) '' S) = i '' (r ⁻¹' S) := by
  ext d
  constructor
  · rintro ⟨x, hx, he⟩
    by_cases hd : d ∈ Set.range i
    · refine ⟨Classical.choose hd, ?_, Classical.choose_spec hd⟩
      have hr : x = r (Classical.choose hd) := by
        apply Sum.inl_injective
        simp only [old, cell] at he
        rw [dite_eq_left hd] at he
        exact he
      change r (Classical.choose hd) ∈ S
      rwa [← hr]
    · have he' := he
      rw [cell_of_not_mem r i d hd] at he'
      exact (Sum.inl_ne_inr he').elim
  · rintro ⟨a, ha, rfl⟩
    exact ⟨r a, ha, (cell_boundary r i hi a).symm⟩

/-- The literal original space embeds as a closed subspace of the actual
attachment, provided the boundary inclusion is a closed embedding. -/
theorem old_isClosedEmbedding (r : A → X) (i : A → D)
    (hr : Continuous r) (hi : IsClosedEmbedding i) : IsClosedEmbedding (old r i) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (old_continuous r i) (old_injective r i)
  intro S hS
  apply isClosed_coinduced.mpr
  apply isClosed_sum_iff.mpr
  constructor
  · change IsClosed ((old r i) ⁻¹' ((old r i) '' S))
    rw [Set.preimage_image_eq S (old_injective r i)]
    exact hS
  · change IsClosed ((cell r i) ⁻¹' ((old r i) '' S))
    rw [cell_preimage_old_image r i hi.injective]
    exact hi.isClosedMap _ (hS.preimage hr)

end FiniteChains.RelativeAttachment
end

section
open scoped Classical
open Set Topology Metric
namespace FiniteChains.ClosedEmbeddingCW

universe u
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
  [CWComplex (Set.univ : Set X)] (f : X → Y) (hf : IsClosedEmbedding f)

def basePartial : PartialEquiv X Y :=
  hf.injective.injOn.toPartialEquiv f Set.univ

def imageCharacteristic (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set X) n) :
    PartialEquiv (Fin n → ℝ) Y :=
  (RelCWComplex.map (C := (Set.univ : Set X)) n j).trans (basePartial f hf)

theorem imageCharacteristic_image (n : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set X) n) (S : Set (Fin n → ℝ)) :
    imageCharacteristic f hf n j '' S =
      f '' (RelCWComplex.map (C := (Set.univ : Set X)) n j '' S) := by
  change (f ∘ RelCWComplex.map n j) '' S = _
  exact Set.image_comp _ _ _

theorem imageCharacteristic_source (n : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set X) n) :
    (imageCharacteristic f hf n j).source = ball 0 1 := by
  rw [imageCharacteristic, PartialEquiv.trans_source]
  change (RelCWComplex.map n j).source ∩
    (RelCWComplex.map n j) ⁻¹' Set.univ = _
  simp only [Set.preimage_univ, Set.inter_univ, RelCWComplex.source_eq]

theorem imageCharacteristic_continuousOn (n : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set X) n) :
    ContinuousOn (imageCharacteristic f hf n j) (closedBall 0 1) :=
  hf.continuous.comp_continuousOn (RelCWComplex.continuousOn n j)

theorem imageCharacteristic_continuousOn_symm (n : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set X) n) :
    ContinuousOn (imageCharacteristic f hf n j).symm
      (imageCharacteristic f hf n j).target := by
  rw [imageCharacteristic, PartialEquiv.trans_target'']
  change ContinuousOn
    ((RelCWComplex.map n j).symm ∘ (basePartial f hf).symm)
    (f '' (Set.univ ∩ (RelCWComplex.map n j).target))
  rw [Set.univ_inter]
  apply hf.isEmbedding.isInducing.continuousOn_image_iff.mpr
  have he : ((RelCWComplex.map n j).symm ∘
      (basePartial f hf).symm) ∘ f =
      (RelCWComplex.map n j).symm := by
    funext x
    exact congrArg (RelCWComplex.map n j).symm
      ((basePartial f hf).left_inv (show x ∈ (basePartial f hf).source from trivial))
  rw [he]
  exact RelCWComplex.continuousOn_symm n j

variable [T2Space X]

end FiniteChains.ClosedEmbeddingCW

namespace FiniteChains.RelativeAttachment

universe u
variable {A X D : Type u} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace D]
  [T2Space X] [Nonempty X] [CWComplex (Set.univ : Set X)]

end FiniteChains.RelativeAttachment
end

section
open scoped Classical
open Set Topology
namespace FiniteChains.RelativeAttachment

universe u
variable (J E : Type u) [NormedAddCommGroup E]

abbrev DiskFamily := Σ _ : J, ClosedUnitBall E
abbrev BoundaryFamily := Σ _ : J, UnitBoundary E

def boundaryFamilyInclusion : BoundaryFamily J E → DiskFamily J E :=
  fun a => ⟨a.1, unitBoundaryInclusion E a.2⟩

theorem boundaryFamilyInclusion_range (d : DiskFamily J E) :
    d ∈ Set.range (boundaryFamilyInclusion J E) ↔ ‖d.2.val‖ = 1 := by
  constructor
  · rintro ⟨⟨j, a⟩, rfl⟩
    exact a.property
  · intro hd
    exact ⟨⟨d.1, ⟨d.2.val, hd⟩⟩, by cases d; rfl⟩

theorem boundaryFamilyInclusion_isClosedEmbedding :
    IsClosedEmbedding (boundaryFamilyInclusion J E) := by
  constructor
  · change IsEmbedding (Sigma.map
      (β₁ := fun _ : J => UnitBoundary E) (β₂ := fun _ : J => ClosedUnitBall E) id
      (fun _ : J => (unitBoundaryInclusion E : UnitBoundary E → ClosedUnitBall E)))
    apply (isEmbedding_sigmaMap Function.injective_id).mpr
    intro j
    exact IsEmbedding.inclusion (fun _ h => h.le)
  · apply isClosed_sigma_iff.mpr
    intro j
    have he : (Sigma.mk j) ⁻¹' Set.range (boundaryFamilyInclusion J E) =
        {x : ClosedUnitBall E | ‖x.val‖ = 1} := by
      ext x
      exact boundaryFamilyInclusion_range J E ⟨j, x⟩
    rw [he]
    exact isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const

variable {J E}
variable {X : Type u} [TopologicalSpace X]
  (r : BoundaryFamily J E → X) (x₀ : X)

abbrev DiskAttachment := Space r (boundaryFamilyInclusion J E)

/-- A total characteristic function; only its values on the closed ball
are used. Outside the disk it takes the chosen old value. -/
def diskCharacteristicFun (j : J) (x : E) : DiskAttachment r :=
  if hx : ‖x‖ ≤ 1 then cell r (boundaryFamilyInclusion J E) ⟨j, ⟨x, hx⟩⟩
  else old r (boundaryFamilyInclusion J E) x₀

omit [TopologicalSpace X] in
theorem diskCharacteristicFun_closed (j : J) (x : E) (hx : ‖x‖ ≤ 1) :
    diskCharacteristicFun r x₀ j x =
      cell r (boundaryFamilyInclusion J E) ⟨j, ⟨x, hx⟩⟩ := by
  simp only [diskCharacteristicFun, dif_pos hx]

def interiorDiskPoint (j : J) (x : {x : E // ‖x‖ < 1}) :
    {d : DiskFamily J E // d ∉ Set.range (boundaryFamilyInclusion J E)} :=
  ⟨⟨j, ⟨x.val, x.property.le⟩⟩, fun h =>
    (ne_of_lt x.property) ((boundaryFamilyInclusion_range J E _).mp h)⟩


theorem interiorDiskPoint_isOpenEmbedding (j : J) :
    IsOpenEmbedding (interiorDiskPoint (E := E) j) := by
  apply IsOpenEmbedding.of_comp (interiorDiskPoint (E := E) j)
    (boundaryFamilyInclusion_isClosedEmbedding J E).isClosed_range.isOpen_compl.isOpenEmbedding_subtypeVal
  exact IsOpenEmbedding.sigmaMk.comp (IsOpenEmbedding.inclusion
    (fun (x : E) (h : ‖x‖ < 1) => le_of_lt h)
    (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const))

omit [TopologicalSpace X] in
theorem diskCharacteristicFun_interior (j : J) (x : {x : E // ‖x‖ < 1}) :
    diskCharacteristicFun r x₀ j x.val =
      fresh r (boundaryFamilyInclusion J E) (interiorDiskPoint j x) := by
  rw [diskCharacteristicFun_closed r x₀ j x.val x.property.le]
  exact cell_of_not_mem r _ _ (interiorDiskPoint j x).property

theorem diskCharacteristicFun_restrict_isEmbedding (j : J) :
    IsEmbedding (fun x : {x : E // ‖x‖ < 1} => diskCharacteristicFun r x₀ j x.val) := by
  have he : (fun x : {x : E // ‖x‖ < 1} => diskCharacteristicFun r x₀ j x.val) =
      fresh r (boundaryFamilyInclusion J E) ∘ interiorDiskPoint j := by
    funext x
    exact diskCharacteristicFun_interior r x₀ j x
  rw [he]
  exact (fresh_isOpenEmbedding r (boundaryFamilyInclusion J E)
    (boundaryFamilyInclusion_isClosedEmbedding J E).isClosed_range).isEmbedding.comp
      (by
        apply IsEmbedding.subtypeVal.of_comp_iff.mp
        exact IsEmbedding.sigmaMk.comp (IsEmbedding.inclusion
          (fun (x : E) (h : ‖x‖ < 1) => le_of_lt h)))


/-- The partial equivalence required by the classical CW definition. -/
def diskCharacteristic (j : J) : PartialEquiv E (DiskAttachment r) :=
  (show Set.InjOn (diskCharacteristicFun r x₀ j) {x : E | ‖x‖ < 1} by
    intro x hx y hy hxy
    exact congrArg Subtype.val
      ((diskCharacteristicFun_restrict_isEmbedding r x₀ j).injective
        (show diskCharacteristicFun r x₀ j (⟨x, hx⟩ : {x : E // ‖x‖ < 1}).val =
          diskCharacteristicFun r x₀ j (⟨y, hy⟩ : {x : E // ‖x‖ < 1}).val from hxy))).toPartialEquiv
    (diskCharacteristicFun r x₀ j) {x : E | ‖x‖ < 1}

theorem diskCharacteristic_source (j : J) :
    (diskCharacteristic r x₀ j).source = Metric.ball 0 1 := by
  ext x
  simp only [diskCharacteristic, Set.InjOn.toPartialEquiv,
    Set.BijOn.toPartialEquiv, Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq]

theorem diskCharacteristic_continuousOn (j : J) :
    ContinuousOn (diskCharacteristic r x₀ j) (Metric.closedBall 0 1) := by
  apply continuousOn_iff_continuous_restrict.mpr
  change Continuous (fun x : Metric.closedBall (0 : E) 1 => diskCharacteristic r x₀ j x.val)
  have he : (fun x : Metric.closedBall (0 : E) 1 => diskCharacteristic r x₀ j x.val) =
      fun x : Metric.closedBall 0 1 =>
        cell r (boundaryFamilyInclusion J E)
          ⟨j, ⟨x.val, by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property⟩⟩ := by
    funext x
    exact diskCharacteristicFun_closed r x₀ j x.val
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property)
  rw [he]
  exact (cell_continuous r (boundaryFamilyInclusion J E)).comp
    (continuous_sigmaMk.comp (continuous_subtype_val.subtype_mk _))

theorem diskCharacteristic_continuousOn_symm (j : J) :
    ContinuousOn (diskCharacteristic r x₀ j).symm (diskCharacteristic r x₀ j).target := by
  have ht : (diskCharacteristic r x₀ j).target =
      (fun x : {x : E // ‖x‖ < 1} => diskCharacteristicFun r x₀ j x.val) '' Set.univ := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hx⟩, trivial, hxy⟩
    · rintro ⟨x, _, hxy⟩
      exact ⟨x.val, x.property, hxy⟩
  rw [ht]
  apply (diskCharacteristicFun_restrict_isEmbedding r x₀ j).isInducing.continuousOn_image_iff.mpr
  have he : (diskCharacteristic r x₀ j).symm ∘
      (fun x : {x : E // ‖x‖ < 1} => diskCharacteristicFun r x₀ j x.val) =
      Subtype.val := by
    funext x
    exact (diskCharacteristic r x₀ j).left_inv x.property
  rw [he]
  exact continuous_subtype_val.continuousOn

theorem diskCharacteristic_boundary (j : J) (x : E) (hx : ‖x‖ = 1) :
    diskCharacteristic r x₀ j x =
      old r (boundaryFamilyInclusion J E) (r ⟨j, ⟨x, hx⟩⟩) := by
  rw [show diskCharacteristic r x₀ j x =
      cell r (boundaryFamilyInclusion J E) ⟨j, ⟨x, hx.le⟩⟩ from
        diskCharacteristicFun_closed r x₀ j x hx.le]
  exact cell_boundary r (boundaryFamilyInclusion J E)
    (boundaryFamilyInclusion_isClosedEmbedding J E).injective ⟨j, ⟨x, hx⟩⟩

theorem diskCharacteristic_openCell (j : J) :
    diskCharacteristic r x₀ j '' Metric.ball 0 1 =
      Set.range (fresh r (boundaryFamilyInclusion J E) ∘ interiorDiskPoint j) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖x‖ < 1 := by
      simpa using hx
    exact ⟨⟨x, hx'⟩, (diskCharacteristicFun_interior r x₀ j ⟨x, hx'⟩).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨x.val, ?_, diskCharacteristicFun_interior r x₀ j x⟩
    simpa using x.property

theorem diskCharacteristic_closedCell (j : J) :
    diskCharacteristic r x₀ j '' Metric.closedBall 0 1 =
      Set.range (fun x : ClosedUnitBall E => cell r (boundaryFamilyInclusion J E) ⟨j, x⟩) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖x‖ ≤ 1 := by
      simpa using hx
    exact ⟨⟨x, hx'⟩, (diskCharacteristicFun_closed r x₀ j x hx').symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨x.val, ?_, diskCharacteristicFun_closed r x₀ j x.val x.property⟩
    simpa using x.property

theorem diskCharacteristic_disjoint_old (j : J) :
    Disjoint (diskCharacteristic r x₀ j '' Metric.ball 0 1)
      (Set.range (old r (boundaryFamilyInclusion J E))) := by
  rw [diskCharacteristic_openCell]
  apply (old_fresh_disjoint r (boundaryFamilyInclusion J E)).symm.mono_left
  grind

theorem diskCharacteristic_disjoint {j k : J} (hjk : j ≠ k) :
    Disjoint (diskCharacteristic r x₀ j '' Metric.ball 0 1)
      (diskCharacteristic r x₀ k '' Metric.ball 0 1) := by
  rw [diskCharacteristic_openCell, diskCharacteristic_openCell]
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have hd  := Sum.inr_injective hy
  exact hjk (congrArg (fun d => d.val.1) hd).symm

/-- The weak topology is exactly the topology of the old part and the
individual attached closed disks, including infinitely many disks. -/
theorem diskAttachment_isClosed (S : Set (DiskAttachment r))
    (hOld : IsClosed ((old r (boundaryFamilyInclusion J E)) ⁻¹' S))
    (hDisk : ∀ j, IsClosed ((fun x : ClosedUnitBall E =>
      cell r (boundaryFamilyInclusion J E) ⟨j, x⟩) ⁻¹' S)) : IsClosed S := by
  apply isClosed_coinduced.mpr
  apply isClosed_sum_iff.mpr
  refine ⟨hOld, ?_⟩
  exact isClosed_sigma_iff.mpr hDisk

end FiniteChains.RelativeAttachment
end

section
open scoped Classical
open Set Topology
namespace FiniteChains.RelativeAttachment

universe u
variable {J E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X]

def annulusBoundary (c : ℝ) (hc : 0 ≤ c)
    (x : {x : ClosedUnitBall E // c < ‖x.val‖}) : UnitBoundary E :=
  ⟨‖x.val.val‖⁻¹ • x.val.val, by
    have hx : ‖x.val.val‖ ≠ 0 := ne_of_gt (lt_of_le_of_lt hc x.property)
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx]⟩


/-- An open set of the old space together with its radial collar of width
`1-c` in every attached disk. -/
def oldCollar (r : BoundaryFamily J E → X) (c : ℝ) (hc : 0 ≤ c) (U : Set X) :
    Set (DiskAttachment r) :=
  fun z => match z with
    | Sum.inl x => x ∈ U
    | Sum.inr d => ∃ h : c < ‖d.val.2.val‖,
        r ⟨d.val.1, annulusBoundary c hc ⟨d.val.2, h⟩⟩ ∈ U

omit [TopologicalSpace X] in
@[simp] theorem old_mem_oldCollar (r : BoundaryFamily J E → X)
    (c : ℝ) (hc : 0 ≤ c) (U : Set X) (x : X) :
    old r (boundaryFamilyInclusion J E) x ∈ oldCollar r c hc U ↔ x ∈ U := Iff.rfl

omit [TopologicalSpace X] in
theorem cell_mem_oldCollar (r : BoundaryFamily J E → X)
    (c : ℝ) (hc : 0 ≤ c) (hcone : c < 1) (U : Set X)
    (j : J) (x : ClosedUnitBall E) :
    cell r (boundaryFamilyInclusion J E) ⟨j, x⟩ ∈ oldCollar r c hc U ↔
      ∃ h : c < ‖x.val‖, r ⟨j, annulusBoundary c hc ⟨x, h⟩⟩ ∈ U := by
  by_cases hx : ‖x.val‖ = 1
  · let a : UnitBoundary E := ⟨x.val, hx⟩
    have hx' : c < ‖x.val‖ := by simpa only [hx] using hcone
    have hb : cell r (boundaryFamilyInclusion J E) ⟨j, x⟩ =
        old r (boundaryFamilyInclusion J E) (r ⟨j, a⟩) :=
      cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective ⟨j, a⟩
    rw [hb, old_mem_oldCollar]
    have he (h : c < ‖x.val‖) : annulusBoundary c hc ⟨x, h⟩ = a := by
      ext
      simp only [annulusBoundary, hx, inv_one, one_smul, a]
    constructor
    · simp_all
    · simp_all
  · have hx' : (⟨j, x⟩ : DiskFamily J E) ∉ Set.range (boundaryFamilyInclusion J E) :=
      fun h => hx ((boundaryFamilyInclusion_range J E _).mp h)
    rw [cell_of_not_mem r _ _ hx']
    rfl

theorem oldCollar_isOpen (r : BoundaryFamily J E → X) (hr : Continuous r)
    (c : ℝ) (hc : 0 ≤ c) (hcone : c < 1) (U : Set X) (hU : IsOpen U) :
    IsOpen (oldCollar r c hc U) := by
  apply isOpen_coinduced.mpr
  apply isOpen_sum_iff.mpr
  refine ⟨hU, ?_⟩
  apply isOpen_sigma_iff.mpr
  intro j
  let A : Set (ClosedUnitBall E) := {x | c < ‖x.val‖}
  have hA : IsOpen A := isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
  have he : (fun x : ClosedUnitBall E => cell r (boundaryFamilyInclusion J E) ⟨j, x⟩) ⁻¹'
      oldCollar r c hc U =
      Subtype.val '' ((fun x : A => r ⟨j, annulusBoundary c hc x⟩) ⁻¹' U) := by
    ext x
    rw [Set.mem_preimage, cell_mem_oldCollar r c hc hcone U j x]
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨⟨x, h⟩, hh, rfl⟩
    · rintro ⟨x', hx', rfl⟩
      exact ⟨x'.property, hx'⟩
  change IsOpen ((fun x : ClosedUnitBall E => cell r (boundaryFamilyInclusion J E) ⟨j, x⟩) ⁻¹'
    oldCollar r c hc U)
  rw [he]
  apply hA.isOpenEmbedding_subtypeVal.isOpenMap
  exact hU.preimage (hr.comp (continuous_sigmaMk.comp (by
    apply Continuous.subtype_mk
    apply Continuous.smul
    · exact (continuous_norm.comp
        (continuous_subtype_val.comp continuous_subtype_val)).inv₀
          (fun x => ne_of_gt (lt_of_le_of_lt hc x.property))
    · exact continuous_subtype_val.comp continuous_subtype_val)))


theorem separate_old_fresh (r : BoundaryFamily J E → X) (hr : Continuous r)
    (x : X) (d : {d : DiskFamily J E // d ∉ Set.range (boundaryFamilyInclusion J E)}) :
    ∃ U V : Set (DiskAttachment r), IsOpen U ∧ IsOpen V ∧
      old r (boundaryFamilyInclusion J E) x ∈ U ∧
      fresh r (boundaryFamilyInclusion J E) d ∈ V ∧ Disjoint U V := by
  have hdlt : ‖d.val.2.val‖ < 1 :=
    lt_of_le_of_ne d.val.2.property
      (fun h => d.property ((boundaryFamilyInclusion_range J E _).mpr h))
  let c  := (‖d.val.2.val‖ + 1) / 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcone : c < 1 := by dsimp [c]; linarith
  have hdc : ‖d.val.2.val‖ < c := by dsimp [c]; linarith
  let V : Set {d : DiskFamily J E // d ∉ Set.range (boundaryFamilyInclusion J E)} :=
    {d | ‖d.val.2.val‖ < c}
  have hV : IsOpen V := by
    have hn : Continuous (fun d : DiskFamily J E => ‖d.2.val‖) := by
      apply continuous_sigma
      intro j
      exact continuous_norm.comp continuous_subtype_val
    exact isOpen_lt (hn.comp continuous_subtype_val) continuous_const
  refine ⟨oldCollar r c hc Set.univ,
    fresh r (boundaryFamilyInclusion J E) '' V,
    oldCollar_isOpen r hr c hc hcone Set.univ isOpen_univ,
    (fresh_isOpenEmbedding r _
      (boundaryFamilyInclusion_isClosedEmbedding J E).isClosed_range).isOpenMap _ hV,
    trivial, ⟨d, hdc, rfl⟩, ?_⟩
  apply Set.disjoint_left.mpr
  rintro _ hU ⟨d', hd', rfl⟩
  obtain ⟨h, _⟩ := hU
  exact (not_lt_of_ge h.le) hd'

/-- Adjoining any family of genuine normed disks to a Hausdorff space along
continuous boundary maps preserves Hausdorffness. -/
theorem diskAttachment_t2Space [T2Space X]
    (r : BoundaryFamily J E → X) (hr : Continuous r) : T2Space (DiskAttachment r) where
  t2 := by
    rintro (x | d) (y | e) hne
    · have hxy : x ≠ y := fun h => hne (congrArg Sum.inl h)
      obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation hxy
      exact ⟨oldCollar r 0 le_rfl U, oldCollar r 0 le_rfl V,
        oldCollar_isOpen r hr 0 le_rfl zero_lt_one U hU,
        oldCollar_isOpen r hr 0 le_rfl zero_lt_one V hV,
        hx, hy, (by
          apply Set.disjoint_left.mpr
          rintro (x | d) hx hy
          · exact Set.disjoint_left.mp hUV hx hy
          · obtain ⟨h, hh⟩ := hx
            obtain ⟨h', hh'⟩ := hy
            exact Set.disjoint_left.mp hUV hh hh')⟩
    · exact separate_old_fresh r hr x e
    · obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := separate_old_fresh r hr y d
      exact ⟨V, U, hV, hU, hy, hx, hUV.symm⟩
    · have hde : d ≠ e := fun h => hne (congrArg Sum.inr h)
      obtain ⟨U, V, hU, hV, hd, he, hUV⟩ := t2_separation hde
      have hf := fresh_isOpenEmbedding r (boundaryFamilyInclusion J E)
        (boundaryFamilyInclusion_isClosedEmbedding J E).isClosed_range
      refine ⟨fresh r _ '' U, fresh r _ '' V, hf.isOpenMap _ hU, hf.isOpenMap _ hV,
        ⟨d, hd, rfl⟩, ⟨e, he, rfl⟩, ?_⟩
      apply Set.disjoint_left.mpr
      rintro _ ⟨d', hd', rfl⟩ ⟨e', he', heq⟩
      have heq' := hf.injective heq
      subst e'
      exact Set.disjoint_left.mp hUV hd' he'

end FiniteChains.RelativeAttachment
end

section
open scoped Classical
open Set Topology Metric
namespace FiniteChains.RelativeAttachment

variable {X J : Type} [TopologicalSpace X] [Nonempty X]
  [CWComplex (Set.univ : Set X)]
variable (n : ℕ) (r : BoundaryFamily J (Fin n → ℝ) → X) (hr : Continuous r) (x₀ : X)

/-- The precise cellular condition on the attaching maps. -/
def FiniteLowerBoundary : Prop := ∀ j : J,
  ∃ I : ∀ m, Finset (RelCWComplex.cell (Set.univ : Set X) m),
    ∀ a : UnitBoundary (Fin n → ℝ),
      r ⟨j, a⟩ ∈ ⋃ (m < n) (k ∈ I m), RelCWComplex.closedCell m k

abbrev AttachmentCell (m : ℕ) :=
  RelCWComplex.cell (Set.univ : Set X) m ⊕ {_j : J // m = n}

def attachmentCharacteristic (m : ℕ) : AttachmentCell (X := X) (J := J) n m →
    PartialEquiv (Fin m → ℝ) (DiskAttachment r)
  | Sum.inl j => ClosedEmbeddingCW.imageCharacteristic
      (old r (boundaryFamilyInclusion J (Fin n → ℝ)))
      (old_isClosedEmbedding r _ hr (boundaryFamilyInclusion_isClosedEmbedding J (Fin n → ℝ))) m j
  | Sum.inr ⟨j, h⟩ => by
      subst m
      exact diskCharacteristic r x₀ j

@[simp] theorem attachmentCharacteristic_old (m : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set X) m) :
    attachmentCharacteristic n r hr x₀ m (Sum.inl j) =
      ClosedEmbeddingCW.imageCharacteristic
        (old r (boundaryFamilyInclusion J (Fin n → ℝ)))
        (old_isClosedEmbedding r _ hr (boundaryFamilyInclusion_isClosedEmbedding J (Fin n → ℝ)))
        m j := rfl

@[simp] theorem attachmentCharacteristic_new (j : J) :
    attachmentCharacteristic n r hr x₀ n (Sum.inr ⟨j, rfl⟩) =
      diskCharacteristic r x₀ j := rfl

theorem attachmentCharacteristic_old_image (m : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set X) m) (S : Set (Fin m → ℝ)) :
    attachmentCharacteristic n r hr x₀ m (Sum.inl j) '' S =
      old r (boundaryFamilyInclusion J (Fin n → ℝ)) '' (RelCWComplex.map m j '' S) :=
  ClosedEmbeddingCW.imageCharacteristic_image _ _ m j S

theorem attachmentCharacteristic_source (m : ℕ)
    (j : AttachmentCell (X := X) (J := J) n m) :
    (attachmentCharacteristic n r hr x₀ m j).source = ball 0 1 := by
  rcases j with j | ⟨j, h⟩
  · exact ClosedEmbeddingCW.imageCharacteristic_source _ _ m j
  · subst m
    exact diskCharacteristic_source r x₀ j

theorem attachmentCharacteristic_continuousOn (m : ℕ)
    (j : AttachmentCell (X := X) (J := J) n m) :
    ContinuousOn (attachmentCharacteristic n r hr x₀ m j) (closedBall 0 1) := by
  rcases j with j | ⟨j, h⟩
  · exact ClosedEmbeddingCW.imageCharacteristic_continuousOn _ _ m j
  · subst m
    exact diskCharacteristic_continuousOn r x₀ j

theorem attachmentCharacteristic_continuousOn_symm (m : ℕ)
    (j : AttachmentCell (X := X) (J := J) n m) :
    ContinuousOn (attachmentCharacteristic n r hr x₀ m j).symm
      (attachmentCharacteristic n r hr x₀ m j).target := by
  rcases j with j | ⟨j, h⟩
  · exact ClosedEmbeddingCW.imageCharacteristic_continuousOn_symm _ _ m j
  · subst m
    exact diskCharacteristic_continuousOn_symm r x₀ j


theorem attachmentCharacteristic_mapsTo (hb : FiniteLowerBoundary n r)
    (m : ℕ) (j : AttachmentCell (X := X) (J := J) n m) :
    ∃ I : ∀ k, Finset (AttachmentCell (X := X) (J := J) n k),
      MapsTo (attachmentCharacteristic n r hr x₀ m j) (sphere 0 1)
        (⋃ (k < m) (i ∈ I k), attachmentCharacteristic n r hr x₀ k i '' closedBall 0 1) := by
  rcases j with j | ⟨j, hm⟩
  · obtain ⟨I, hI⟩ := Topology.CWComplex.mapsTo' m j
    refine ⟨fun k => (I k).image Sum.inl, ?_⟩
    intro x hx
    obtain ⟨k, hk, i, hi, hx'⟩ := by
      simpa only [Set.mem_iUnion] using hI hx
    simp only [Set.mem_iUnion]
    refine ⟨k, hk, Sum.inl i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩
    rw [attachmentCharacteristic_old_image]
    exact ⟨RelCWComplex.map m j x, hx', rfl⟩
  · subst m
    obtain ⟨I, hI⟩ := hb j
    refine ⟨fun k => (I k).image Sum.inl, ?_⟩
    intro x hx
    have hx' : ‖x‖ = 1 := by simpa using hx
    rw [attachmentCharacteristic_new, diskCharacteristic_boundary r x₀ j x hx']
    obtain ⟨k, hk, i, hi, ha⟩ := by
      simpa using hI ⟨x, hx'⟩
    simp only [Set.mem_iUnion]
    refine ⟨k, hk, Sum.inl i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩
    rw [attachmentCharacteristic_old_image]
    exact ⟨r ⟨j, ⟨x, hx'⟩⟩, ha, rfl⟩

variable [T2Space X]

/-- The inherited old cells and the genuinely attached disks form a
classical CW complex on the entire attachment space. -/
def attachmentCW (hb : FiniteLowerBoundary n r) : CWComplex (Set.univ : Set (DiskAttachment r)) where
  cell := AttachmentCell (X := X) (J := J) n
  map := attachmentCharacteristic n r hr x₀
  source_eq := attachmentCharacteristic_source n r hr x₀
  continuousOn := attachmentCharacteristic_continuousOn n r hr x₀
  continuousOn_symm := attachmentCharacteristic_continuousOn_symm n r hr x₀
  pairwiseDisjoint' := (by
    rintro ⟨m, i⟩ _ ⟨k, j⟩ _ hne
    change Disjoint (attachmentCharacteristic n r hr x₀ m i '' ball 0 1)
      (attachmentCharacteristic n r hr x₀ k j '' ball 0 1)
    rcases i with i | ⟨i, hi⟩ <;> rcases j with j | ⟨j, hj⟩
    · rw [attachmentCharacteristic_old_image, attachmentCharacteristic_old_image]
      apply Set.disjoint_left.mpr
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
      have he' := old_injective r (boundaryFamilyInclusion J (Fin n → ℝ)) he
      subst b
      apply Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne (C := (Set.univ : Set X)) ?_) ha hb
      intro h
      apply hne
      exact congrArg (fun z : Σ m, RelCWComplex.cell (Set.univ : Set X) m =>
        (⟨z.1, Sum.inl z.2⟩ : Σ m, AttachmentCell (X := X) (J := J) n m)) h
    · subst k
      rw [attachmentCharacteristic_new, attachmentCharacteristic_old_image]
      apply (diskCharacteristic_disjoint_old r x₀ j).symm.mono_left
      exact Set.image_subset_range _ _
    · subst m
      rw [attachmentCharacteristic_new, attachmentCharacteristic_old_image]
      apply (diskCharacteristic_disjoint_old r x₀ i).mono_right
      exact Set.image_subset_range _ _
    · subst m
      subst k
      rw [attachmentCharacteristic_new, attachmentCharacteristic_new]
      apply diskCharacteristic_disjoint r x₀
      intro h
      subst j
      exact hne rfl)
  mapsTo' := attachmentCharacteristic_mapsTo n r hr x₀ hb
  closed' := by
    intro S _ hS
    apply diskAttachment_isClosed r S
    · apply (CWComplex.closed (Set.univ : Set X) _ (Set.subset_univ _)).mpr
      intro m j
      have hs := (hS m (Sum.inl j)).preimage (old_continuous r (boundaryFamilyInclusion J (Fin n → ℝ)))
      rw [attachmentCharacteristic_old_image] at hs
      simpa only [Set.preimage_inter, Set.preimage_image_eq _ (old_injective r _), RelCWComplex.closedCell] using hs
    · intro j
      have hs := (hS n (Sum.inr ⟨j, rfl⟩)).preimage
        (f := fun x : ClosedUnitBall (Fin n → ℝ) =>
          cell r (boundaryFamilyInclusion J (Fin n → ℝ)) ⟨j, x⟩)
        ((cell_continuous r (boundaryFamilyInclusion J (Fin n → ℝ))).comp continuous_sigmaMk)
      rw [attachmentCharacteristic_new, diskCharacteristic_closedCell] at hs
      have he : (fun x : ClosedUnitBall (Fin n → ℝ) =>
          cell r (boundaryFamilyInclusion J (Fin n → ℝ)) ⟨j, x⟩) ⁻¹'
          (S ∩ Set.range (fun x : ClosedUnitBall (Fin n → ℝ) =>
            cell r (boundaryFamilyInclusion J (Fin n → ℝ)) ⟨j, x⟩)) =
          (fun x : ClosedUnitBall (Fin n → ℝ) =>
            cell r (boundaryFamilyInclusion J (Fin n → ℝ)) ⟨j, x⟩) ⁻¹' S := by
        ext x
        exact and_iff_left ⟨x, rfl⟩
      rwa [he] at hs
  union' := by
    apply Set.eq_univ_of_forall
    rintro (x | d)
    · have hx : x ∈ ⋃ m, ⋃ j : RelCWComplex.cell (Set.univ : Set X) m,
          RelCWComplex.closedCell m j := by rw [CWComplex.union]; trivial
      obtain ⟨m, j, hx⟩ := by simpa only [Set.mem_iUnion] using hx
      apply Set.mem_iUnion.mpr
      refine ⟨m, Set.mem_iUnion.mpr ⟨Sum.inl j, ?_⟩⟩
      rw [attachmentCharacteristic_old_image]
      exact ⟨x, hx, rfl⟩
    · apply Set.mem_iUnion.mpr
      refine ⟨n, Set.mem_iUnion.mpr ⟨Sum.inr ⟨d.val.1, rfl⟩, ?_⟩⟩
      rw [attachmentCharacteristic_new, diskCharacteristic_closedCell]
      exact ⟨d.val.2, cell_of_not_mem r _ d.val d.property⟩

variable (hb : FiniteLowerBoundary n r)

/-- The original space is a literal closed subcomplex, with precisely the
original cell summand in every dimension. -/
def attachmentOldSubcomplex :
    letI := attachmentCW n r hr x₀ hb
    CWComplex.Subcomplex (Set.univ : Set (DiskAttachment r)) := by
  letI := attachmentCW n r hr x₀ hb
  refine {
    carrier := Set.range (old r (boundaryFamilyInclusion J (Fin n → ℝ)))
    I := fun m => Set.range Sum.inl
    closed' := (old_isClosedEmbedding r _ hr
      (boundaryFamilyInclusion_isClosedEmbedding J (Fin n → ℝ))).isClosed_range
    union' := ?_ }
  rw [Set.empty_union]
  ext z
  constructor
  · intro hz
    obtain ⟨m, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨j', hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨j, hj⟩ := j'.property
    have hj' : (j'.1 : AttachmentCell (X := X) (J := J) n m) = Sum.inl j := hj.symm
    rw [hj'] at hz
    change z ∈ attachmentCharacteristic n r hr x₀ m (Sum.inl j) '' ball 0 1 at hz
    rw [attachmentCharacteristic_old_image] at hz
    obtain ⟨y, _, rfl⟩ := hz
    exact ⟨y, rfl⟩
  · rintro ⟨x, rfl⟩
    have hx : x ∈ ⋃ m, ⋃ j : RelCWComplex.cell (Set.univ : Set X) m,
        RelCWComplex.openCell m j := by rw [CWComplex.iUnion_openCell_eq_complex]; trivial
    obtain ⟨m, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨m, Set.mem_iUnion.mpr ⟨⟨Sum.inl j, ⟨j, rfl⟩⟩, ?_⟩⟩
    change old r _ x ∈ attachmentCharacteristic n r hr x₀ m (Sum.inl j) '' ball 0 1
    rw [attachmentCharacteristic_old_image]
    exact ⟨x, hx, rfl⟩

def attachmentOldCellEquiv (m : ℕ) :
    RelCWComplex.cell (Set.univ : Set X) m ≃
      {j : AttachmentCell (X := X) (J := J) n m // j ∈ Set.range Sum.inl} where
  toFun j := ⟨Sum.inl j, ⟨j, rfl⟩⟩
  invFun := by
    rintro ⟨j, hj⟩
    rcases j with j | j
    · exact j
    · simp_all
  left_inv _ := rfl
  right_inv j := by
    rcases j with ⟨j, hj⟩
    obtain ⟨j, rfl⟩ := hj
    rfl

theorem attachment_old_openCell (m : ℕ) (j : RelCWComplex.cell (Set.univ : Set X) m) :
    letI := attachmentCW n r hr x₀ hb
    old r (boundaryFamilyInclusion J (Fin n → ℝ)) '' CWComplex.openCell m j =
      CWComplex.openCell (C := (Set.univ : Set (DiskAttachment r))) m
        (attachmentOldCellEquiv (X := X) (J := J) n m j).val :=
  (attachmentCharacteristic_old_image n r hr x₀ m j (ball 0 1)).symm

end FiniteChains.RelativeAttachment

namespace FiniteChains.ClassicalCW

variable {X : Type} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]

def vertexPoint (v : RelCWComplex.cell (Set.univ : Set X) 0) : X :=
  RelCWComplex.map 0 v ![]

/-- Any two points in a single characteristic closed disk are joined in
the actual image of that disk, including points on its attached boundary. -/
theorem closedCell_joined (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set X) n)
    {x y : X} (hx : x ∈ RelCWComplex.closedCell n j)
    (hy : y ∈ RelCWComplex.closedCell n j) :
    JoinedIn (RelCWComplex.closedCell n j) x y := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ((isPathConnected_closedBall zero_le_one).joinedIn a ha b hb).map_continuousOn
    (RelCWComplex.continuousOn n j)

theorem closedCell_joined_vertex (n : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set X) n) {x : X}
    (hx : x ∈ RelCWComplex.closedCell n j) :
    ∃ v : RelCWComplex.cell (Set.univ : Set X) 0, Joined x (vertexPoint v) := by
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      refine ⟨j, ?_⟩
      have he : x = vertexPoint j := by
        simpa only [RelCWComplex.closedCell_zero_eq_singleton, Set.mem_singleton_iff,
          vertexPoint] using hx
      simpa only [he] using (Joined.refl (vertexPoint j))
    · have hnpos  := Nat.pos_of_ne_zero hn
      letI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
      let a : Fin n → ℝ := fun _ => 1
      have ha : a ∈ sphere 0 1 := by
        simp only [Metric.mem_sphere, dist_zero_right, a, pi_norm_const, norm_one]
      obtain ⟨I, hI⟩ := Topology.CWComplex.mapsTo' n j
      obtain ⟨m, hmn, k, _, hk⟩ := by
        simpa only [Set.mem_iUnion] using hI ha
      obtain ⟨v, hv⟩ := ih m hmn k hk
      refine ⟨v, ?_⟩
      have hp :=
        (closedCell_joined n j hx
          ⟨a, Metric.sphere_subset_closedBall ha, rfl⟩).joined
      exact hp.trans hv

/-- Every actual point has an actual continuous path to an original
zero-cell. The CW complex need not be finite or connected. -/
theorem point_joined_vertex (x : X) :
    ∃ v : RelCWComplex.cell (Set.univ : Set X) 0, Joined x (vertexPoint v) := by
  have hx : x ∈ ⋃ n, ⋃ j : RelCWComplex.cell Set.univ n,
      RelCWComplex.closedCell n j := by rw [CWComplex.union]; trivial
  obtain ⟨n, j, hx⟩ := by simpa using hx
  exact closedCell_joined_vertex n j hx

def pointVertex (x : X) : RelCWComplex.cell (Set.univ : Set X) 0 :=
  Classical.choose (point_joined_vertex x)

def pointVertexPath (x : X) : Path x (vertexPoint (pointVertex x)) :=
  (Classical.choose_spec (point_joined_vertex x)).somePath

end FiniteChains.ClassicalCW
end

section
open scoped Classical unitInterval
open Set Topology
namespace FiniteChains.RelativeAttachment

theorem oneBoundary_finiteSet :
    ({x : Fin 1 → ℝ | ‖x‖ = 1} : Set (Fin 1 → ℝ)).Finite := by
  apply ((Set.finite_singleton (fun _ : Fin 1 => (-1 : ℝ))).insert
    (fun _ : Fin 1 => 1)).subset
  intro x hx
  have he : x = fun _ => x 0 := by
    funext i
    exact congrArg x (Subsingleton.elim i 0)
  have hx' : |x 0| = 1 := by
    calc
      |x 0| = ‖fun _ => x 0‖ := by rw [pi_norm_const, Real.norm_eq_abs]
      _ = ‖x‖ := congrArg norm he.symm
      _ = 1 := hx
  rcases (abs_eq zero_le_one).mp hx' with h | h
  · exact Or.inl (he.trans (by simp only [h]))
  · exact Or.inr (Set.mem_singleton_iff.mpr (he.trans (by simp only [h])))

instance oneBoundary_finite : Finite (UnitBoundary (Fin 1 → ℝ)) :=
  oneBoundary_finiteSet.to_subtype

instance oneBoundary_discrete : DiscreteTopology (UnitBoundary (Fin 1 → ℝ)) := inferInstance

variable {X J : Type} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]

/-- The new one-cell endpoints are chosen among original zero-cells. -/
def vertexBoundaryMap (r : BoundaryFamily J (Fin 1 → ℝ) → X) :
    C(BoundaryFamily J (Fin 1 → ℝ), X) :=
  ⟨fun a => ClassicalCW.vertexPoint (ClassicalCW.pointVertex (r a)), continuous_of_discreteTopology⟩

/-- Arbitrarily many endpoints move simultaneously. Their disjoint domain
is discrete, so the chosen vertex paths give a continuous homotopy. -/
def vertexBoundaryHomotopy (r : C(BoundaryFamily J (Fin 1 → ℝ), X)) :
    ContinuousMap.Homotopy r (vertexBoundaryMap r) := by
  let F : C(BoundaryFamily J (Fin 1 → ℝ), C(I, X)) :=
    ⟨fun a => (ClassicalCW.pointVertexPath (r a)).toContinuousMap,
      continuous_of_discreteTopology⟩
  exact {
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := fun a => (ClassicalCW.pointVertexPath (r a)).source
    map_one_left := fun a => (ClassicalCW.pointVertexPath (r a)).target }

theorem vertexBoundaryMap_finiteLowerBoundary
    (r : BoundaryFamily J (Fin 1 → ℝ) → X) :
    FiniteLowerBoundary 1 (vertexBoundaryMap r) := by
  letI := Fintype.ofFinite (UnitBoundary (Fin 1 → ℝ))
  intro j
  let V  :=
    Finset.univ.image (fun a : UnitBoundary (Fin 1 → ℝ) => ClassicalCW.pointVertex (r ⟨j, a⟩))
  let cells : ∀ m, Finset (RelCWComplex.cell Set.univ m)
    | 0 => V
    | _ + 1 => ∅
  refine ⟨cells, ?_⟩
  intro a
  simp only [Set.mem_iUnion]
  refine ⟨0, Nat.zero_lt_one, ClassicalCW.pointVertex (r ⟨j, a⟩), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  · rw [RelCWComplex.closedCell_zero_eq_singleton]
    rfl

end FiniteChains.RelativeAttachment
end

namespace FiniteChains.RelativeAttachment
open scoped Topology unitInterval Classical

theorem norm_coordinate_bounds {n : ℕ} (x : Fin n → ℝ)
    (hx : ‖x‖ ≤ 1) (i : Fin n) : -1 ≤ x i ∧ x i ≤ 1 := by
  have hi  := (Real.norm_eq_abs (x i)) ▸ (norm_le_pi_norm x i).trans hx
  exact abs_le.mp hi

theorem norm_one_coordinate {n : ℕ} (x : Fin n → ℝ) (hx : ‖x‖ = 1) :
    ∃ i, x i = 1 ∨ x i = -1 := by
  by_contra! h
  have hl  := (pi_norm_lt_iff zero_lt_one).mpr (fun i => by
    have hu := (norm_le_pi_norm x i).trans hx.le
    apply lt_of_le_of_ne hu
    intro he
    have hi : x i = 1 ∨ x i = -1 := (abs_eq zero_le_one).mp
      (by simpa using he)
    exact hi.elim (h i).1 (h i).2)
  simp_all

def unitBoundarySquareHomeomorph : UnitBoundary (Fin 2 → ℝ) ≃ₜ SquareBoundary where
  toFun x := ⟨fun i => ⟨(x.val i + 1) / 2, by
      have hi := norm_coordinate_bounds x.val x.property.le i
      constructor <;> linarith⟩, by
    obtain ⟨i, hi | hi⟩ := norm_one_coordinate x.val x.property
    · exact ⟨i, Or.inr (Subtype.ext (by simp [hi]))⟩
    · exact ⟨i, Or.inl (Subtype.ext (by simp [hi]))⟩⟩
  invFun x := ⟨fun i => 2 * (x.val i : ℝ) - 1, by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro i
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      have hi := (x.val i).property
      constructor <;> linarith [hi.1, hi.2]
    · obtain ⟨i, hi | hi⟩ := x.property
      · have h := norm_le_pi_norm (fun j => 2 * (x.val j : ℝ) - 1) i
        simpa only [hi, Set.Icc.coe_zero, mul_zero, zero_sub, norm_neg, norm_one] using h
      · have h := norm_le_pi_norm (fun j => 2 * (x.val j : ℝ) - 1) i
        norm_num only [hi, Set.Icc.coe_one, mul_one, show (2 : ℝ) - 1 = 1 by norm_num,
          norm_one] at h
        exact h⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    dsimp
    ring
  right_inv x := by simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (((continuous_apply i).comp continuous_subtype_val).add continuous_const).div_const 2
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_const.mul
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val))).sub
        continuous_const

def oneBallIntervalHomeomorph : ClosedUnitBall (Fin 1 → ℝ) ≃ₜ I where
  toFun x := ⟨(x.val 0 + 1) / 2, by
    have hi := norm_coordinate_bounds x.val x.property 0
    constructor <;> linarith⟩
  invFun t := ⟨fun _ => 2 * (t : ℝ) - 1, by
    rw [pi_norm_const, Real.norm_eq_abs]
    apply abs_le.mpr
    have ht := t.property
    constructor <;> linarith [ht.1, ht.2]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    dsimp
    ring
  right_inv t := by simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2
  continuous_invFun := by fun_prop

def oneBoundaryPoint (b : Bool) : UnitBoundary (Fin 1 → ℝ) :=
  ⟨fun _ => if b then 1 else -1, by cases b <;> simp [pi_norm_const]⟩

theorem oneBoundary_eq (a : UnitBoundary (Fin 1 → ℝ)) :
    a = oneBoundaryPoint false ∨ a = oneBoundaryPoint true := by
  obtain ⟨i, hi | hi⟩ := norm_one_coordinate a.val a.property
  · apply Or.inr
    apply Subtype.ext
    funext j
    have hj : j = i := Subsingleton.elim _ _
    simpa [hj, oneBoundaryPoint] using hi
  · apply Or.inl
    apply Subtype.ext
    funext j
    have hj : j = i := Subsingleton.elim _ _
    simpa [hj, oneBoundaryPoint] using hi

@[simp] theorem oneBallIntervalHomeomorph_boundary (b : Bool) :
    oneBallIntervalHomeomorph (unitBoundaryInclusion _ (oneBoundaryPoint b)) =
      boolEndpoint b := by
  ext
  cases b <;> norm_num [oneBallIntervalHomeomorph, unitBoundaryInclusion,
    oneBoundaryPoint, boolEndpoint]

end FiniteChains.RelativeAttachment

namespace FiniteChains.RelativeAttachment
open scoped Topology unitInterval Classical

variable {X : Type} [TopologicalSpace X]

structure IntervalEndpointExtension (f : C(I, X)) {x₀ x₁ : X}
    (p₀ : Path (f 0) x₀) (p₁ : Path (f 1) x₁) where
  map : C(I × I, X)
  zero : ∀ t, map (0, t) = f t
  side_zero : ∀ τ, map (τ, 0) = p₀ τ
  side_one : ∀ τ, map (τ, 1) = p₁ τ

def intervalEndpointExtension (f : C(I, X)) {x₀ x₁ : X}
    (p₀ : Path (f 0) x₀) (p₁ : Path (f 1) x₁) :
    IntervalEndpointExtension f p₀ p₁ := by
  let e := oneBallIntervalHomeomorph
  let P : C(UnitBoundary (Fin 1 → ℝ), C(I, X)) :=
    ⟨fun a => if a.val 0 = -1 then p₀.toContinuousMap else p₁.toContinuousMap,
      continuous_of_discreteTopology⟩
  have hP₀ : P (oneBoundaryPoint false) = p₀.toContinuousMap := by
    simp [P, oneBoundaryPoint]
  have hP₁ : P (oneBoundaryPoint true) = p₁.toContinuousMap := by
    norm_num [P, oneBoundaryPoint]
  let H : C(I × UnitBoundary (Fin 1 → ℝ), X) :=
    P.uncurry.comp ⟨Prod.swap, continuous_swap⟩
  let F := f.comp e.toContinuousMap
  have h₀ : ∀ a, H (0, a) = F (unitBoundaryInclusion _ a) := by
    intro a
    change P a 0 = f (oneBallIntervalHomeomorph (unitBoundaryInclusion _ a))
    rcases oneBoundary_eq a with rfl | rfl
    · rw [hP₀, oneBallIntervalHomeomorph_boundary]
      exact p₀.source
    · rw [hP₁, oneBallIntervalHomeomorph_boundary]
      exact p₁.source
  let G := ballHomotopyExtension F H h₀
  have he (b : Bool) : e.symm (boolEndpoint b) =
      unitBoundaryInclusion _ (oneBoundaryPoint b) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (oneBallIntervalHomeomorph_boundary b).symm
  refine {
    map := G.comp ⟨fun z => (z.1, e.symm z.2),
      continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)⟩
    zero := ?_
    side_zero := ?_
    side_one := ?_ }
  · intro t
    change G (0, e.symm t) = f t
    rw [ballHomotopyExtension_zero]
    exact congrArg f (e.apply_symm_apply t)
  · intro τ
    change G (τ, e.symm (boolEndpoint false)) = p₀ τ
    rw [he, ballHomotopyExtension_boundary]
    change P (oneBoundaryPoint false) τ = p₀ τ
    rw [hP₀]
    rfl
  · intro τ
    change G (τ, e.symm (boolEndpoint true)) = p₁ τ
    rw [he, ballHomotopyExtension_boundary]
    change P (oneBoundaryPoint true) τ = p₁ τ
    rw [hP₁]
    rfl

end FiniteChains.RelativeAttachment

namespace MonoidAlgebra

variable {R M N P : Type*} [Semiring R]

/-- Composition of coefficient reindexing for the wrapped group algebra. -/
theorem mapDomain_comp (f : M → N) (g : N → P) (x : MonoidAlgebra R M) :
    mapDomain (g ∘ f) x = mapDomain g (mapDomain f x) := by
  apply coeff_injective
  exact Finsupp.mapDomain_comp

@[simp] theorem mapDomain_id (x : MonoidAlgebra R M) : mapDomain id x = x := by
  apply coeff_injective
  exact Finsupp.mapDomain_id

end MonoidAlgebra

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [DecidableEq α]

/-- The integral group ring of the free group on `α`. -/
abbrev FreeGroupRing (α : Type*) := MonoidAlgebra ℤ (FreeGroup α)

/-- The image of a group element in the group ring. -/
def grp (g : FreeGroup α) : FreeGroupRing α := MonoidAlgebra.of ℤ (FreeGroup α) g

omit [DecidableEq α] in
@[simp] theorem grp_one : grp (1 : FreeGroup α) = 1 := map_one _

omit [DecidableEq α] in
theorem grp_mul (g h : FreeGroup α) : grp (g * h) = grp g * grp h := map_mul _ _ _

omit [DecidableEq α] in
@[simp] theorem grp_mul_grp_inv (g : FreeGroup α) : grp g * grp g⁻¹ = 1 := by
  rw [← grp_mul]; simp

omit [DecidableEq α] in
@[simp] theorem grp_inv_mul_grp (g : FreeGroup α) : grp g⁻¹ * grp g = 1 := by
  rw [← grp_mul]; simp

/-- The `2 × 2` matrix attached to a generator in the construction of the `i`-th Fox
derivative: `![![x_k, δ_{ik}], ![0, 1]]`, as a unit of the matrix ring. -/
def foxGen (i : α) (k : α) :
    (Matrix (Fin 2) (Fin 2) (FreeGroupRing α))ˣ where
  val := !![grp (FreeGroup.of k), if i = k then 1 else 0; 0, 1]
  inv := !![grp (FreeGroup.of k)⁻¹, -(grp (FreeGroup.of k)⁻¹ * (if i = k then 1 else 0)); 0, 1]
  val_inv := by
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The homomorphism computing the `i`-th Fox derivative. -/
def foxHom (i : α) :
    FreeGroup α →* (Matrix (Fin 2) (Fin 2) (FreeGroupRing α))ˣ :=
  FreeGroup.lift (foxGen i)

/-- The Fox derivative `∂w/∂x_i` as an element of the integral group ring. -/
def fox (i : α) (w : FreeGroup α) : FreeGroupRing α :=
  ((foxHom i w : Matrix (Fin 2) (Fin 2) (FreeGroupRing α))) 0 1

theorem foxHom_entries (i : α) (w : FreeGroup α) :
    (foxHom i w : Matrix (Fin 2) (Fin 2) (FreeGroupRing α)) 0 0 = grp w ∧
    (foxHom i w : Matrix (Fin 2) (Fin 2) (FreeGroupRing α)) 1 0 = 0 ∧
    (foxHom i w : Matrix (Fin 2) (Fin 2) (FreeGroupRing α)) 1 1 = 1 := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of k => simp [foxHom, foxGen, FreeGroup.lift_apply_of]
  | inv_of k _ =>
      have : foxHom i (FreeGroup.of k)⁻¹ = (foxGen i k)⁻¹ := by
        simp [foxHom, FreeGroup.lift_apply_of]
      rw [this]
      simp [foxGen, Units.inv_mk]
  | mul u v hu hv =>
      have hmul : (foxHom i (u * v))
          = (foxHom i u) *
            (foxHom i v : Matrix (Fin 2) (Fin 2) (FreeGroupRing α)) := by
        rw [map_mul]; rfl
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hu.1, hu.2.1, hu.2.2, hv.1, hv.2.1,
          hv.2.2, grp_mul]

@[simp] theorem fox_one (i : α) : fox i (1 : FreeGroup α) = 0 := rfl

/-- `∂x_k/∂x_i = δ_{ik}`. -/
@[simp] theorem fox_of (i k : α) : fox i (FreeGroup.of k) = if i = k then 1 else 0 := by
  simp [fox, foxHom, foxGen, FreeGroup.lift_apply_of]

/-- The product rule `∂(uv)/∂x_i = ∂u/∂x_i + u · ∂v/∂x_i`. -/
theorem fox_mul (i : α) (u v : FreeGroup α) :
    fox i (u * v) = fox i u + grp u * fox i v := by
  have hmul : (foxHom i (u * v))
      = (foxHom i u) *
        (foxHom i v : Matrix (Fin 2) (Fin 2) (FreeGroupRing α)) := by
    rw [map_mul]; rfl
  obtain ⟨h00, h10, h11⟩ := foxHom_entries i u
  have : fox i (u * v)
      = (foxHom i u) 0 0 * fox i v +
        (foxHom i u) 0 1 *
        (foxHom i v) 1 1 := by
    simp [fox, Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, h00, (foxHom_entries i v).2.2, mul_one, add_comm]
  rfl

theorem fox_inv (i : α) (u : FreeGroup α) :
    fox i u⁻¹ = -(grp u⁻¹ * fox i u) := by
  have h : 0 = fox i u + grp u * fox i u⁻¹ := by
    rw [← fox_mul i u u⁻¹]; simp
  have h'  := eq_neg_of_add_eq_zero_right h.symm
  calc fox i u⁻¹ = grp u⁻¹ * (grp u * fox i u⁻¹) := by
        rw [← mul_assoc, grp_inv_mul_grp, one_mul]
    _ = -(grp u⁻¹ * fox i u) := by rw [h', mul_neg]

/-- The augmentation `ℤ[F] → ℤ`. -/
def aug : FreeGroupRing α →+* ℤ :=
  (MonoidAlgebra.lift ℤ ℤ (FreeGroup α) 1).toRingHom

omit [DecidableEq α] in
@[simp] theorem aug_grp (g : FreeGroup α) : aug (grp g) = 1 := by
  simp [aug, grp]

/-- Exponent sum of the generator `i` in a word, as a group homomorphism. -/
def expSum (i : α) : FreeGroup α →* Multiplicative ℤ :=
  FreeGroup.lift fun k => Multiplicative.ofAdd (if i = k then (1 : ℤ) else 0)

@[simp] theorem expSum_of (i k : α) :
    Multiplicative.toAdd (expSum i (FreeGroup.of k)) = if i = k then (1 : ℤ) else 0 := by
  simp [expSum, FreeGroup.lift_apply_of]

/-- Augmenting the Fox derivative gives the exponent sum: this is the passage from the
Fox boundary of Remark 1 to the exponent-sum matrix `M` of (3.1). -/
theorem aug_fox (i : α) (w : FreeGroup α) :
    aug (fox i w) = Multiplicative.toAdd (expSum i w) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of k => simp
  | inv_of k h =>
      rw [fox_inv, map_neg, map_mul, aug_grp, one_mul, h, map_inv]
      simp
  | mul u v hu hv => simp [fox_mul, map_mul, hu, hv]

end FiniteChains

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [DecidableEq α]

/-- The linear extension `D_i : ℤ[F] → ℤ[F]` of the Fox derivative `∂/∂x_i`. -/
def foxLin (i : α) : FreeGroupRing α →ₗ[ℤ] FreeGroupRing α :=
  (Finsupp.linearCombination ℤ (fun g => fox i g)).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp] theorem foxLin_single (i : α) (g : FreeGroup α) (n : ℤ) :
    foxLin i (single g n) = n • fox i g := Finsupp.linearCombination_single ℤ n g

omit [DecidableEq α] in
theorem grp_eq_single (g : FreeGroup α) : (grp g : FreeGroupRing α) = single g 1 := rfl

@[simp] theorem foxLin_grp (i : α) (g : FreeGroup α) : foxLin i (grp g) = fox i g := by
  rw [grp_eq_single, foxLin_single, one_smul]

omit [DecidableEq α] in
theorem single_eq_smul_grp (g : FreeGroup α) (n : ℤ) :
    (single g n : FreeGroupRing α) = n • grp g := by
  rw [grp_eq_single, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

omit [DecidableEq α] in
@[simp] theorem aug_single (g : FreeGroup α) (n : ℤ) :
    aug (single g n : FreeGroupRing α) = n := by
  rw [single_eq_smul_grp, map_zsmul, aug_grp, smul_eq_mul, mul_one]

/-- The Leibniz rule for the linear extension of the Fox derivative. -/
theorem foxLin_mul (i : α) (a b : FreeGroupRing α) :
    foxLin i (a * b) = aug b • foxLin i a + a * foxLin i b := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a₁ a₂ h₁ h₂ =>
      rw [add_mul, map_add, h₁, h₂, map_add, smul_add, add_mul]
      abel
  | single g n =>
      induction b using MonoidAlgebra.induction_linear with
      | zero => simp
      | add b₁ b₂ h₁ h₂ =>
          rw [mul_add, map_add, h₁, h₂, map_add, map_add, add_smul, mul_add]
          abel
      | single h m =>
          rw [MonoidAlgebra.single_mul_single, foxLin_single, foxLin_single, foxLin_single,
            aug_single, fox_mul, single_eq_smul_grp g n, smul_mul_assoc, smul_smul]
          simp only [smul_add, zsmul_eq_mul, Int.cast_mul, mul_assoc]
          rw [← mul_assoc (m : FreeGroupRing α), (Int.cast_commute m (grp g)).eq, mul_assoc]
          congr 1
          rw [← mul_assoc, ← mul_assoc, ← Int.cast_mul, ← Int.cast_mul, mul_comm n m]

end FiniteChains

section
open scoped commutatorElement
namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]

/-- The group ring `ℤ[Q]` of the deck group `Q = F/Ñ` of the cover. -/
abbrev CoverRing : Type _ := MonoidAlgebra ℤ (FreeGroup α ⧸ Nsub)

/-- The projection `π : ℤ[F] → ℤ[Q]`. -/
def proj : FreeGroupRing α →+* CoverRing Nsub :=
  MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' Nsub)

/-- The image of a word in `ℤ[Q]`. -/
def qgrp (g : FreeGroup α) : CoverRing Nsub :=
  MonoidAlgebra.single (QuotientGroup.mk g) 1

/-- The augmentation `ℤ[Q] → ℤ`. -/
def augQ : CoverRing Nsub →+* ℤ :=
  (MonoidAlgebra.lift ℤ ℤ (FreeGroup α ⧸ Nsub) 1).toRingHom

/-- A set-theoretic lift `ℤ[Q] → ℤ[F]` of the projection. -/
def liftQ (z : CoverRing Nsub) : FreeGroupRing α :=
  MonoidAlgebra.mapDomain (fun q => Quotient.out q) z

omit [Fintype α] [DecidableEq α] in
theorem proj_apply (b : FreeGroupRing α) :
    proj Nsub b = MonoidAlgebra.mapDomain (fun g => (QuotientGroup.mk g : FreeGroup α ⧸ Nsub)) b := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem proj_single (g : FreeGroup α) (n : ℤ) :
    proj Nsub (single g n) = single (QuotientGroup.mk g : FreeGroup α ⧸ Nsub) n := by
  rw [proj_apply]
  exact MonoidAlgebra.mapDomain_single

omit [Fintype α] [DecidableEq α] in
theorem proj_grp (g : FreeGroup α) : proj Nsub (grp g) = qgrp Nsub g := by
  rw [grp_eq_single, proj_single, qgrp]

omit [Fintype α] [DecidableEq α] in
theorem qgrp_eq_one_of_mem {g : FreeGroup α} (hg : g ∈ Nsub) : qgrp Nsub g = 1 := by
  have h  := (QuotientGroup.eq_one_iff g).2 hg
  rw [qgrp, h]
  rfl

omit [Fintype α] [DecidableEq α] in
theorem proj_grp_of_mem {g : FreeGroup α} (hg : g ∈ Nsub) : proj Nsub (grp g) = 1 := by
  rw [proj_grp, qgrp_eq_one_of_mem Nsub hg]

omit [Fintype α] [DecidableEq α] in
@[simp] theorem augQ_single (q : FreeGroup α ⧸ Nsub) (n : ℤ) : augQ Nsub (single q n) = n := by
  simp [augQ]

omit [Fintype α] [DecidableEq α] in
theorem augQ_proj (b : FreeGroupRing α) : augQ Nsub (proj Nsub b) = aug b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b₁ b₂ h₁ h₂ => simp_all
  | single g n => simp

omit [Fintype α] [DecidableEq α] in
theorem proj_liftQ (z : CoverRing Nsub) : proj Nsub (liftQ Nsub z) = z := by
  have hcomp : (fun q : FreeGroup α ⧸ Nsub => (QuotientGroup.mk (Quotient.out q) : FreeGroup α ⧸ Nsub))
      = id := funext fun q => QuotientGroup.out_eq' q
  rw [proj_apply, liftQ, ← MonoidAlgebra.mapDomain_comp]
  show MonoidAlgebra.mapDomain (fun q : FreeGroup α ⧸ Nsub =>
    (QuotientGroup.mk (Quotient.out q) : FreeGroup α ⧸ Nsub)) z = z
  simp_all

/-! ### The Fox vector of a word -/

/-- The Fox vector `(π(∂w/∂x_i))_i ∈ ℤ[Q]^n` of a word. -/
def foxVec (w : FreeGroup α) : α → CoverRing Nsub :=
  fun i => proj Nsub (fox i w)

omit [Fintype α] in
@[simp] theorem foxVec_one : foxVec Nsub 1 = 0 := rfl

variable {Nsub}

omit [Fintype α] in
theorem foxVec_mul {v : FreeGroup α} (hv : v ∈ Nsub) (w : FreeGroup α) :
    foxVec Nsub (v * w) = foxVec Nsub v + foxVec Nsub w := by grind [foxVec, fox_mul, map_add, map_mul, proj_grp_of_mem, one_mul, Pi.add_apply]

omit [Fintype α] in
theorem foxVec_inv {v : FreeGroup α} (hv : v ∈ Nsub) :
    foxVec Nsub v⁻¹ = - foxVec Nsub v := by
  have h := foxVec_mul (Subgroup.inv_mem _ hv) v
  rw [inv_mul_cancel, foxVec_one] at h
  grind

omit [Fintype α] in
theorem foxVec_conj {r : FreeGroup α} (hr : r ∈ Nsub) (f : FreeGroup α) :
    foxVec Nsub (f * r * f⁻¹) = proj Nsub (grp f) • foxVec Nsub r := by
  funext i
  have hfox : fox i (f * r * f⁻¹)
      = fox i f + grp f * fox i r + grp (f * r) * fox i f⁻¹ := by
    rw [fox_mul, fox_mul]
  have hff : proj Nsub (grp f) * proj Nsub (grp f⁻¹) = 1 := by
    rw [← map_mul, ← grp_mul, mul_inv_cancel, grp_one, map_one]
  simp only [foxVec, Pi.smul_apply, smul_eq_mul, hfox, fox_inv i f, grp_mul, map_add, map_mul,
    map_neg, proj_grp_of_mem Nsub hr, mul_one]
  rw [mul_neg, ← mul_assoc, hff, one_mul]
  abel

omit [Fintype α] in
theorem foxVec_zpow {r : FreeGroup α} (hr : r ∈ Nsub) (n : ℤ) :
    foxVec Nsub (r ^ n) = n • foxVec Nsub r := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have hmem : r ^ (k : ℤ) ∈ Nsub := Subgroup.zpow_mem _ hr _
      rw [zpow_add_one, foxVec_mul hmem, ih, add_smul, one_smul]
  | pred k ih =>
      have hmem : r ^ (-(k : ℤ)) ∈ Nsub := Subgroup.zpow_mem _ hr _
      rw [zpow_sub_one, foxVec_mul hmem, foxVec_inv hr, ih, sub_smul, one_smul, sub_eq_add_neg]

/-! ### The module of Fox vectors -/

/-- The set of Fox vectors of the elements of `Ñ`; by the Crowell exact sequence this is
exactly the module of `1`-cycles of the cover. -/
def foxMod : Submodule (CoverRing Nsub) (α → CoverRing Nsub) where
  carrier := {c | ∃ r ∈ Nsub, c = foxVec Nsub r}
  zero_mem' := ⟨1, Subgroup.one_mem _, by simp⟩
  add_mem' := by
    rintro a b ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
    exact ⟨r * s, Subgroup.mul_mem _ hr hs, by rw [foxVec_mul hr]⟩
  smul_mem' := by
    rintro u a ⟨r, hr, rfl⟩
    induction u using MonoidAlgebra.induction_linear with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | add u₁ u₂ h₁ h₂ =>
        obtain ⟨r₁, hr₁, e₁⟩ := h₁
        obtain ⟨r₂, hr₂, e₂⟩ := h₂
        refine ⟨r₁ * r₂, Subgroup.mul_mem _ hr₁ hr₂, ?_⟩
        rw [foxVec_mul hr₁, ← e₁, ← e₂, add_smul]
    | single q n =>
        obtain ⟨f, rfl⟩ := Quotient.exists_rep q
        have hconj : f * r * f⁻¹ ∈ Nsub := Subgroup.Normal.conj_mem ‹Nsub.Normal› r hr f
        refine ⟨(f * r * f⁻¹) ^ n, Subgroup.zpow_mem _ hconj n, ?_⟩
        have hsingle : (single (QuotientGroup.mk f : FreeGroup α ⧸ Nsub) n : CoverRing Nsub)
            = n • proj Nsub (grp f) := by
          rw [proj_grp, qgrp, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
        rw [foxVec_zpow hconj, foxVec_conj hr, hsingle, smul_assoc]

/-! ### The kernel of the projection `ℤ[F] → ℤ[Q]` -/

/-- Reindexing of a group-ring element along a map of the free group, viewed on `ℤ[F]`. -/
def mapDom (φ : FreeGroup α → FreeGroup α) (c : FreeGroupRing α) :
    FreeGroupRing α := MonoidAlgebra.mapDomain φ c

omit [Fintype α] [DecidableEq α] in
theorem mapDom_add (φ : FreeGroup α → FreeGroup α) (c d : FreeGroupRing α) :
    mapDom φ (c + d) = mapDom φ c + mapDom φ d := MonoidAlgebra.mapDomain_add φ c d


variable (Nsub)

/-- The left ideal of `ℤ[F]` generated by the elements `r - 1` with `r ∈ Ñ`. -/
def relIdeal : Submodule (FreeGroupRing α) (FreeGroupRing α) :=
  Submodule.span (FreeGroupRing α) {y | ∃ r ∈ Nsub, y = grp r - 1}


/-! ### The Fox vector of a ring element -/

/-- The Fox vector of an element of `ℤ[F]`, i.e. the vector of the linearly extended Fox
derivatives, projected to `ℤ[Q]`. -/
def foxProj (b : FreeGroupRing α) : α → CoverRing Nsub :=
  fun i => proj Nsub (foxLin i b)


omit [Fintype α] in
theorem foxProj_add (b₁ b₂ : FreeGroupRing α) :
    foxProj Nsub (b₁ + b₂) = foxProj Nsub b₁ + foxProj Nsub b₂ := by
  funext i; simp [foxProj]


omit [Fintype α] in
theorem foxProj_mem_foxMod (b : FreeGroupRing α) (hb : proj Nsub b = 0) :
    foxProj Nsub b ∈ foxMod (Nsub := Nsub) := by
  have hmem := (by
    set φ : FreeGroup α → FreeGroup α :=
      fun g => Quotient.out (QuotientGroup.mk g) with hφ
    have hmap : mapDom φ b = 0 := by
      show MonoidAlgebra.mapDomain φ b = 0
      have hcomp : MonoidAlgebra.mapDomain φ b
          = MonoidAlgebra.mapDomain (fun q : FreeGroup α ⧸ Nsub => Quotient.out q)
              (MonoidAlgebra.mapDomain (fun g => (QuotientGroup.mk g)) b) :=
        MonoidAlgebra.mapDomain_comp _ _ b
      rw [hcomp, ← proj_apply, hb, MonoidAlgebra.mapDomain_zero]
    have key : ∀ c : FreeGroupRing α, c - mapDom φ c ∈ relIdeal Nsub := by
      intro c
      induction c using MonoidAlgebra.induction_linear with
      | zero =>
          have hz : 0 - mapDom φ 0 = 0 := by
            rw [show mapDom φ 0 = 0 from MonoidAlgebra.mapDomain_zero φ, sub_zero]
          rw [hz]
          exact Submodule.zero_mem _
      | add c₁ c₂ h₁ h₂ =>
          have hsplit : (c₁ + c₂) - mapDom φ (c₁ + c₂)
              = (c₁ - mapDom φ c₁) + (c₂ - mapDom φ c₂) := by
            rw [mapDom_add]; abel
          rw [hsplit]
          exact Submodule.add_mem _ h₁ h₂
      | single g n =>
          have hmk : (QuotientGroup.mk (φ g)) = QuotientGroup.mk g :=
            QuotientGroup.out_eq' _
          have hmem := QuotientGroup.eq.1 hmk
          have hmapd : mapDom φ (single g n) = single (φ g) n :=
            (MonoidAlgebra.mapDomain_single)
          have hgrp : grp (φ g) * (grp ((φ g)⁻¹ * g) - 1) = grp g - grp (φ g) := by
            rw [mul_sub, ← grp_mul, mul_inv_cancel_left, mul_one]
          have hrewrite : (single g n) - mapDom φ (single g n)
              = (n : FreeGroupRing α) * (grp (φ g) * (grp ((φ g)⁻¹ * g) - 1)) := by
            rw [hmapd, hgrp, single_eq_smul_grp, single_eq_smul_grp, ← smul_sub, zsmul_eq_mul]
          rw [hrewrite]
          have hgen : grp ((φ g)⁻¹ * g) - 1 ∈ relIdeal Nsub :=
            Submodule.subset_span ⟨_, hmem, rfl⟩
          have h1 : grp (φ g) * (grp ((φ g)⁻¹ * g) - 1) ∈ relIdeal Nsub := by
            simpa [smul_eq_mul] using Submodule.smul_mem (relIdeal Nsub) (grp (φ g)) hgen
          simpa [smul_eq_mul] using
            Submodule.smul_mem (relIdeal Nsub) ((n : FreeGroupRing α)) h1
    have hb' := key b
    rwa [hmap, sub_zero] at hb')
  refine (Submodule.span_induction
    (p := fun y _ => aug y = 0 ∧ foxProj Nsub y ∈ foxMod (Nsub := Nsub)) ?_ ?_ ?_ ?_ hmem).2
  · rintro y ⟨r, hr, rfl⟩
    refine ⟨by simp [map_sub], ?_⟩
    have hval : foxProj Nsub (grp r - 1) = foxVec Nsub r := by
      funext i
      have h1 : foxLin i 1 = 0 := by
        rw [← grp_one, foxLin_grp, fox_one]
      simp only [foxProj, foxVec, map_sub, foxLin_grp, h1, sub_zero]
    rw [hval]
    exact ⟨r, hr, rfl⟩
  · exact ⟨by simp, Submodule.zero_mem _⟩
  · rintro x y hx hy ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [map_add, hx1, hy1, add_zero], by
      rw [foxProj_add]; exact Submodule.add_mem _ hx2 hy2⟩
  · rintro a x hx ⟨hx1, hx2⟩
    refine ⟨by rw [smul_eq_mul, map_mul, hx1, mul_zero], ?_⟩
    rw [smul_eq_mul, (show foxProj Nsub (a * x) = proj Nsub a • foxProj Nsub x by
      funext i
      simp only [foxProj, foxLin_mul, hx1, zero_smul, zero_add, map_mul, Pi.smul_apply, smul_eq_mul])]
    exact Submodule.smul_mem _ _ hx2

/-! ### The boundary maps of the cover -/

/-! ### The second boundary and the homology of the cover -/

variable {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

/-- The boundary `∂₂ : ℤ[Q]^m → ℤ[Q]^n`, `∂₂(e_j) = (π(∂r_j/∂x_i))_i`. -/
def bdry2 (u : J → CoverRing Nsub) : α → CoverRing Nsub :=
  fun i => ∑ j : J, u j * proj Nsub (fox i (ρ j))

omit [Fintype α] in
theorem bdry2_add (u v : J → CoverRing Nsub) :
    bdry2 Nsub ρ (u + v) = bdry2 Nsub ρ u + bdry2 Nsub ρ v := by
  funext i
  simp [bdry2, add_mul, Finset.sum_add_distrib]

omit [Fintype α] in
theorem bdry2_zero : bdry2 Nsub ρ 0 = 0 := by
  funext i; simp [bdry2]

end FiniteChains
end

namespace FiniteChains

open Set

variable {G : Type*} [Group G]

/-- A requirement is *finitely determined* when its truth value at a subgroup depends only
on the membership of the elements of some fixed finite set. -/
def FinitelyDetermined {ι : Type*} (Sat : Subgroup G → ι → Prop) : Prop :=
  ∀ v : ι, ∃ F : Finset G, ∀ N N' : Subgroup G,
    (∀ g ∈ F, (g ∈ N ↔ g ∈ N')) → (Sat N v ↔ Sat N' v)

section Compactness

/-- The indicator functions of normal subgroups, inside the compact space `G → Bool`. -/
def NSSet (G : Type*) [Group G] : Set (G → Bool) :=
  {f | f 1 = true ∧ (∀ a b, f a = true → f b = true → f (a * b) = true) ∧
    (∀ a, f a = true → f a⁻¹ = true) ∧ (∀ g a, f a = true → f (g * a * g⁻¹) = true)}

/-- The normal subgroup with a given indicator function. -/
def toSubgroup (f : G → Bool) (hf : f ∈ NSSet G) : Subgroup G where
  carrier := {g | f g = true}
  one_mem' := hf.1
  mul_mem' ha hb := hf.2.1 _ _ ha hb
  inv_mem' ha := hf.2.2.1 _ ha

theorem mem_toSubgroup {f : G → Bool} (hf : f ∈ NSSet G) (g : G) :
    g ∈ toSubgroup f hf ↔ f g = true := Iff.rfl


omit [Group G] in
/-- A condition on `G → Bool` that only depends on finitely many coordinates is closed. -/
theorem isClosed_of_finite_determination (P : (G → Bool) → Prop) (F : Finset G)
    (hF : ∀ f f' : G → Bool, (∀ g ∈ F, f g = f' g) → P f → P f') :
    IsClosed {f | P f} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro f hf
  refine ⟨{f' | ∀ g ∈ F, f' g = f g}, ?_, ?_, fun g _ => rfl⟩
  · intro f' hf' hP
    exact hf (hF f' f hf' hP)
  · have hset : {f' : G → Bool | ∀ g ∈ F, f' g = f g}
        = ⋂ g ∈ F, (fun h : G → Bool => h g) ⁻¹' {f g} := by
      ext f'; simp
    rw [hset]
    exact isOpen_biInter_finset fun g _ => (isOpen_discrete _).preimage (continuous_apply g)

theorem isClosed_NSSet : IsClosed (NSSet G) := by
  classical
  have h1 : IsClosed {f : G → Bool | f 1 = true} :=
    isClosed_of_finite_determination _ {1} (by
      intro f f' hff' hf
      simpa [← hff' 1 (by simp)] using hf)
  have h2 : ∀ a b : G, IsClosed {f : G → Bool | f a = true → f b = true → f (a * b) = true} := by
    intro a b
    refine isClosed_of_finite_determination _ {a, b, a * b} ?_
    intro f f' hff' hf ha hb
    rw [← hff' _ (by simp)]
    exact hf (by rw [hff' _ (by simp)]; exact ha) (by rw [hff' _ (by simp)]; exact hb)
  have h3 : ∀ a : G, IsClosed {f : G → Bool | f a = true → f a⁻¹ = true} := by
    intro a
    refine isClosed_of_finite_determination _ {a, a⁻¹} ?_
    intro f f' hff' hf ha
    rw [← hff' _ (by simp)]
    exact hf (by rw [hff' _ (by simp)]; exact ha)
  have h4 : ∀ g a : G, IsClosed {f : G → Bool | f a = true → f (g * a * g⁻¹) = true} := by
    intro g a
    refine isClosed_of_finite_determination _ {a, g * a * g⁻¹} ?_
    intro f f' hff' hf ha
    rw [← hff' _ (by simp)]
    exact hf (by rw [hff' _ (by simp)]; exact ha)
  have hset : NSSet G = {f : G → Bool | f 1 = true}
      ∩ ((⋂ p : G × G, {f : G → Bool | f p.1 = true → f p.2 = true → f (p.1 * p.2) = true})
      ∩ ((⋂ a : G, {f : G → Bool | f a = true → f a⁻¹ = true})
      ∩ (⋂ p : G × G, {f : G → Bool | f p.2 = true → f (p.1 * p.2 * p.1⁻¹) = true}))) := by
    ext f
    simp only [NSSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Prod.forall]
  rw [hset]
  exact h1.inter ((isClosed_iInter fun p : G × G => h2 p.1 p.2).inter
    ((isClosed_iInter fun a => h3 a).inter (isClosed_iInter fun p : G × G => h4 p.1 p.2)))

/-- **The compactness step of Section 2.**  If every finite family of finitely determined
requirements is satisfied by some normal subgroup, then all requirements are satisfied
simultaneously by a single normal subgroup. -/
theorem exists_normal_subgroup_forall {ι : Type*} (Sat : Subgroup G → ι → Prop)
    (hdet : FinitelyDetermined Sat)
    (hfin : ∀ S : Finset ι, ∃ N : Subgroup G, N.Normal ∧ ∀ v ∈ S, Sat N v) :
    ∃ N : Subgroup G, N.Normal ∧ ∀ v, Sat N v := by
  classical
  choose F hF using hdet
  -- the closed set of indicator functions satisfying the requirement `v`
  set B : ι → Set (G → Bool) := fun v =>
    NSSet G ∩ {f | ∀ N : Subgroup G, (∀ g, g ∈ N ↔ f g = true) → Sat N v} with hB
  have hBclosed : ∀ v, IsClosed (B v) := by
    intro v
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro f hf
    by_cases hfZ : f ∈ NSSet G
    · have hnot : ¬ ∀ N : Subgroup G, (∀ g, g ∈ N ↔ f g = true) → Sat N v := fun h => hf ⟨hfZ, h⟩
      push Not at hnot
      obtain ⟨N, hNmem, hNsat⟩ := hnot
      refine ⟨{f' | ∀ g ∈ F v, f' g = f g}, ?_, ?_, fun g _ => rfl⟩
      · intro f' hf' hf'B
        obtain ⟨hf'Z, hf'sat⟩ := hf'B
        have hNN' : Sat N v ↔ Sat (toSubgroup f' hf'Z) v := by
          refine hF v N (toSubgroup f' hf'Z) ?_
          intro g hg
          rw [hNmem g, mem_toSubgroup hf'Z g, hf' g hg]
        exact hNsat (hNN'.mpr (hf'sat _ (mem_toSubgroup hf'Z)))
      · have hset : {f' : G → Bool | ∀ g ∈ F v, f' g = f g}
            = ⋂ g ∈ F v, (fun h : G → Bool => h g) ⁻¹' {f g} := by
          ext f'; simp
        rw [hset]
        exact isOpen_biInter_finset fun g _ => (isOpen_discrete _).preimage (continuous_apply g)
    · exact ⟨(NSSet G)ᶜ, fun f' hf' hf'B => hf' hf'B.1, isClosed_NSSet.isOpen_compl, hfZ⟩
  -- the indicator function of a normal subgroup lies in the corresponding closed sets
  have hmemZ : ∀ N : Subgroup G, N.Normal → (fun g => decide (g ∈ N)) ∈ NSSet G := by
    intro N hN
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro a b ha hb
      simp at ha hb ⊢
      exact N.mul_mem ha hb
    · simp
    · intro g a ha
      simp at ha ⊢
      exact hN.conj_mem a ha g
  have hmemB : ∀ (N : Subgroup G), N.Normal → ∀ v, Sat N v →
      (fun g => decide (g ∈ N)) ∈ B v := by
    intro N hN v hNv
    refine ⟨hmemZ N hN, ?_⟩
    intro N' hN'
    have : N' = N := by
      ext g
      simpa using hN' g
    rwa [this]
  -- compactness
  have hne : (NSSet G ∩ ⋂ v, B v).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hempty
    obtain ⟨u, hu⟩ := isClosed_NSSet.isCompact.elim_finite_subfamily_closed B hBclosed hempty
    obtain ⟨N, hN, hNu⟩ := hfin u
    have hmem : (fun g => decide (g ∈ N)) ∈ NSSet G ∩ ⋂ v ∈ u, B v :=
      ⟨hmemZ N hN, Set.mem_iInter₂.mpr fun v hv => hmemB N hN v (hNu v hv)⟩
    exact absurd hmem.2 (Set.disjoint_left.mp hu hmem.1)
  obtain ⟨f, hfZ, hfB⟩ := hne
  refine ⟨toSubgroup f hfZ, (⟨fun n hn g => hfZ.2.2.2 g n hn⟩), fun v => ?_⟩
  exact (Set.mem_iInter.mp hfB v).2 _ (mem_toSubgroup hfZ)

end Compactness

/-- **The minimality step of Section 2.**  If the requirements pass to intersections of
decreasing chains, then a normal subgroup satisfying them all contains a minimal such
normal subgroup. -/
theorem exists_minimal_normal_sat (Sat : Subgroup G → Prop)
    (hchain : ∀ C : Set (Subgroup G), IsChain (· ≤ ·) C → C.Nonempty →
      (∀ N ∈ C, N.Normal ∧ Sat N) → Sat (sInf C))
    (M : Subgroup G) (hM : M.Normal) (hMs : Sat M) :
    ∃ N : Subgroup G, N ≤ M ∧ N.Normal ∧ Sat N ∧
      ∀ N' : Subgroup G, N' ≤ N → N'.Normal → Sat N' → N' = N := by
  set s : Set (Subgroup G) := {N | N ≤ M ∧ N.Normal ∧ Sat N} with hs
  have hMem : M ∈ s := ⟨le_rfl, hM, hMs⟩
  have hub : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, ub ≤ z := by
    intro c hcs hchain' y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    refine ⟨sInf c, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact (sInf_le hy).trans (hcs hy).1
    · constructor
      intro n hn g
      rw [Subgroup.mem_sInf] at hn ⊢
      intro N hN
      exact ((hcs hN).2.1).conj_mem n (hn N hN) g
    · grind
    · intro z hz
      exact sInf_le hz
  obtain ⟨m, -, hmax⟩ := zorn_le_nonempty₀ (α := (Subgroup G)ᵒᵈ) s
    (fun c hcs hc y hy => hub c hcs hc.symm y hy) M hMem
  obtain ⟨hmM, hmN, hmS⟩ := hmax.1
  refine ⟨m, hmM, hmN, hmS, ?_⟩
  intro N' hN' hN'norm hN'sat
  have hN's : N' ∈ s := ⟨hN'.trans hmM, hN'norm, hN'sat⟩
  exact le_antisymm hN' (hmax.2 hN's hN')

end FiniteChains

namespace FiniteChains

open Finset

variable {G : Type*} [Group G]

open scoped Classical in
/-- The reduction of `x ∈ ℤ[G]` to `ℤ[G/N]` is zero: inside every coset of `N` the
coefficients of `x` add up to zero. -/
def VanishesMod (N : Subgroup G) (x : G →₀ ℤ) : Prop :=
  ∀ g : G, ∑ h ∈ x.support.filter (fun h => h * g⁻¹ ∈ N), x h = 0


variable {I J : Type*}

/-- The `i`-th coordinate of the Fox boundary of the coefficient vector `v`, with respect
to the boundary data `b i j = ∂r_j/∂x_i` read in the group ring. -/
def foxBoundary (b : I → J → MonoidAlgebra ℤ G)
    (v : J →₀ MonoidAlgebra ℤ G) (i : I) : MonoidAlgebra ℤ G :=
  ∑ j ∈ v.support, v j * b i j

/-- The requirement (2.2) attached to the coefficient vector `v`: if the reduced boundary
of `v` vanishes, then the reduced `v` vanishes. -/
def FoxSat (b : I → J → MonoidAlgebra ℤ G) (v : J →₀ MonoidAlgebra ℤ G)
    (N : Subgroup G) : Prop :=
  (∀ i : I, VanishesMod N (foxBoundary b v i).coeff) → ∀ j : J, VanishesMod N (v j).coeff

end FiniteChains

namespace FiniteChains

open scoped Classical in
/-- **A torsion-free abelian group has unique sums.**  Two nonempty finite subsets always
contain a pair whose sum is achieved only once. -/
theorem uniqueSums_of_isAddTorsionFree (A : Type*) [AddCommGroup A] [IsAddTorsionFree A] :
    UniqueSums A := by
  constructor
  intro S T hS hT
  -- the finitely generated subgroup containing both finite sets
  set G : AddSubgroup A := AddSubgroup.closure (S ∪ T : Finset A) with hG
  haveI : AddGroup.FG G := by
    rw [hG]; exact AddGroup.closure_finset_fg (S ∪ T)
  haveI : Module.Finite ℤ G := inferInstance
  haveI := Function.Injective.isAddTorsionFree
    (f := (AddSubgroup.subtype G)) Subtype.val_injective
  haveI : Module.IsTorsionFree ℤ G := inferInstance
  haveI : Module.Free ℤ G := Module.free_of_finite_type_torsion_free' (R := ℤ) (M := G)
  haveI : TwoUniqueSums G :=
    TwoUniqueSums.of_injective_addHom
      ((Module.Free.chooseBasis ℤ G).repr.toLinearMap.toAddMonoidHom.toAddHom)
      (Module.Free.chooseBasis ℤ G).repr.injective inferInstance
  haveI : UniqueSums G := inferInstance
  -- pull the two finite sets back into the subgroup
  have hSG : ∀ a ∈ S, a ∈ G := fun a ha =>
    AddSubgroup.subset_closure (by simp [ha])
  have hTG : ∀ b ∈ T, b ∈ G := fun b hb =>
    AddSubgroup.subset_closure (by simp [hb])
  set S' : Finset G := S.subtype (· ∈ G) with hS'
  set T' : Finset G := T.subtype (· ∈ G) with hT'
  have hS'ne : S'.Nonempty := by
    obtain ⟨a, ha⟩ := hS
    exact ⟨⟨a, hSG a ha⟩, by simpa [hS', Finset.mem_subtype] using ha⟩
  have hT'ne : T'.Nonempty := by
    obtain ⟨b, hb⟩ := hT
    exact ⟨⟨b, hTG b hb⟩, by simpa [hT', Finset.mem_subtype] using hb⟩
  obtain ⟨a0, ha0, b0, hb0, huniq⟩ := UniqueSums.uniqueAdd_of_nonempty hS'ne hT'ne
  refine ⟨a0, by simpa [hS', Finset.mem_subtype] using ha0,
    b0, by simpa [hT', Finset.mem_subtype] using hb0, ?_⟩
  intro a b ha hb hab
  have ha' : ⟨a, hSG a ha⟩ ∈ S' := by simpa [hS', Finset.mem_subtype] using ha
  have hb' : ⟨b, hTG b hb⟩ ∈ T' := by simpa [hT', Finset.mem_subtype] using hb
  have : (⟨a, hSG a ha⟩ + ⟨b, hTG b hb⟩) = a0 + b0 := Subtype.ext (by simpa using hab)
  obtain ⟨h1, h2⟩ := huniq ha' hb' this
  exact ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩

/-- **A torsion-free abelian group has unique products** (multiplicative form). -/
theorem uniqueProds_of_isMulTorsionFree (H : Type*) [CommGroup H] [IsMulTorsionFree H] :
    UniqueProds H := by
  haveI : IsAddTorsionFree (Additive H) := inferInstance
  haveI := uniqueSums_of_isAddTorsionFree (Additive H)
  haveI : UniqueProds (Multiplicative (Additive H)) := inferInstance
  exact UniqueProds.of_injective_mulHom
    (MulEquiv.multiplicativeAdditive H).symm.toMonoidHom.toMulHom
    (MulEquiv.multiplicativeAdditive H).symm.injective inferInstance

/-- **The group ring of a torsion-free abelian group over an integral domain is an integral
domain.**  This is the hypothesis on the coefficient ring `k[H]` used in Lemma 2.1, for
`k = ℤ` and `k = 𝔽ₚ`. -/
theorem monoidAlgebra_isDomain (k : Type*) [CommRing k] [IsDomain k]
    (H : Type*) [CommGroup H] [IsMulTorsionFree H] :
    IsDomain (MonoidAlgebra k H) := by
  haveI := uniqueProds_of_isMulTorsionFree H
  infer_instance

end FiniteChains

namespace FiniteChains

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]

/-- Coefficientwise reduction of a finitely supported vector along a ring map. -/
def reduceVec (ε : R →+* S) {κ : Type*} (v : κ →₀ R) : κ →₀ S :=
  Finsupp.mapRange ε ε.map_zero v

omit [IsDomain R] [IsDomain S] in
@[simp] theorem reduceVec_apply (ε : R →+* S) {κ : Type*} (v : κ →₀ R) (k : κ) :
    reduceVec ε v k = ε (v k) := rfl

omit [IsDomain R] [IsDomain S] in
theorem reduceVec_smul (ε : R →+* S) {κ : Type*} (a : R) (v : κ →₀ R) :
    reduceVec ε (a • v) = ε a • reduceVec ε v := by
  ext k; simp

omit [IsDomain R] [IsDomain S] in
theorem reduceVec_sub (ε : R →+* S) {κ : Type*} (v w : κ →₀ R) :
    reduceVec ε (v - w) = reduceVec ε v - reduceVec ε w := by
  ext k; simp

/-- **Independence is detected after reduction.**  If a finite family of vectors in a free
module over a commutative domain `R` becomes linearly independent after coefficientwise
reduction along `ε : R →+* S` to a commutative domain `S`, then the family was already
linearly independent over `R`. -/
theorem eq_zero_of_reduction_indep {κ ι : Type*} (ε : R →+* S)
    (T : Finset ι) (v : ι → (κ →₀ R))
    (hred : ∀ d : ι → S, (∑ j ∈ T, d j • reduceVec ε (v j)) = 0 → ∀ j ∈ T, d j = 0)
    (c : ι → R) (hc : (∑ j ∈ T, c j • v j) = 0) : ∀ j ∈ T, c j = 0 := by
  classical
  have key : ∀ T : Finset ι, ∀ v : ι → (κ →₀ R),
      (∀ d : ι → S, (∑ j ∈ T, d j • reduceVec ε (v j)) = 0 → ∀ j ∈ T, d j = 0) →
      ∀ c : ι → R, (∑ j ∈ T, c j • v j) = 0 → ∀ j ∈ T, c j = 0 := by
    intro T
    induction T using Finset.strongInduction with
    | _ T ih =>
      intro v hred c hc j₀ hj₀
      set T' : Finset ι := T.erase j₀ with hT'
      -- the reduced vector `v̄ j₀` is nonzero, so some coordinate survives `ε`
      have hv₀ : ∃ k : κ, ε (v j₀ k) ≠ 0 := by
        by_contra hall
        push_neg at hall
        have hzero : reduceVec ε (v j₀) = 0 := by
          ext k; simpa using hall k
        have hsum : (∑ j ∈ T, (if j = j₀ then (1 : S) else 0) • reduceVec ε (v j)) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          by_cases hj : j = j₀
          · subst hj; simp [hzero]
          · simp [hj]
        have := hred (fun j => if j = j₀ then 1 else 0) hsum j₀ hj₀
        simp at this
      obtain ⟨k, hk⟩ := hv₀
      set a : R := v j₀ k with ha
      have ha0 : a ≠ 0 := fun h => hk (by rw [h, map_zero])
      -- the modified family
      set w : ι → (κ →₀ R) := fun j => a • v j - (v j k) • v j₀ with hw
      have hwj₀ : w j₀ = 0 := by simp [hw, ha]
      -- reduced independence of the modified family
      have hred' : ∀ d : ι → S, (∑ j ∈ T', d j • reduceVec ε (w j)) = 0 → ∀ j ∈ T', d j = 0 := by
        intro d hd j hj
        set e : ι → S := fun j =>
          if j = j₀ then -(∑ j ∈ T', d j * ε (v j k)) else d j * ε a with he
        have hsplit : (∑ j ∈ T, e j • reduceVec ε (v j)) = 0 := by
          have hcalc : (∑ j ∈ T', d j • reduceVec ε (w j))
              = (∑ j ∈ T', (d j * ε a) • reduceVec ε (v j))
                - (∑ j ∈ T', d j * ε (v j k)) • reduceVec ε (v j₀) := by
            rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hw]
            simp only [reduceVec_sub, reduceVec_smul, smul_sub, smul_smul]
          have h1 : e j₀ = -(∑ j ∈ T', d j * ε (v j k)) := by simp [he]
          have h3 : (∑ j ∈ T.erase j₀, e j • reduceVec ε (v j))
              = ∑ j ∈ T', (d j * ε a) • reduceVec ε (v j) :=
            Finset.sum_congr rfl fun j hj' => by
              rw [show e j = d j * ε a by simp [he, Finset.ne_of_mem_erase hj']]
          rw [← Finset.add_sum_erase T (fun j => e j • reduceVec ε (v j)) hj₀, h1, h3, neg_smul, ← sub_eq_neg_add, ← hcalc, hd]
        have hj0 := Finset.mem_of_mem_erase hj
        have := hred e hsplit j hj0
        rw [he] at this
        simp only [Finset.ne_of_mem_erase hj, if_false] at this
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · grind
      -- the coefficients satisfy the corresponding relation for the modified family
      have hcw : (∑ j ∈ T', c j • w j) = 0 := by
        have hsplit : c j₀ • v j₀ + ∑ j ∈ T', c j • v j = 0 := by
          rw [hT', Finset.add_sum_erase T (fun j => c j • v j) hj₀]; exact hc
        have hsum1 : (∑ j ∈ T', c j • v j) = (-c j₀) • v j₀ := by
          rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]; exact hsplit
        have hcoord : (∑ j ∈ T', c j * (v j k)) = -(c j₀ * a) := by
          have := congrArg (fun x : κ →₀ R => x k) hsum1
          simpa [Finset.sum_apply', ha] using this
        have hcalc : (∑ j ∈ T', c j • w j)
            = a • (∑ j ∈ T', c j • v j) - (∑ j ∈ T', c j * (v j k)) • v j₀ := by
          rw [Finset.smul_sum, Finset.sum_smul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hw]
          simp only [smul_sub, smul_smul]
          rw [mul_comm (c j) a]
        rw [hcalc, hsum1, hcoord, smul_smul, neg_smul, sub_neg_eq_add, ← add_smul]
        have : a * -c j₀ + c j₀ * a = 0 := by ring
        rw [this, zero_smul]
      -- induction on the smaller family
      have hsub : T' ⊂ T := Finset.erase_ssubset hj₀
      have hzero' : ∀ j ∈ T', c j = 0 := ih T' hsub w hred' c hcw
      -- only the `j₀` term survives, and evaluating at `k` finishes the proof
      have honly : c j₀ • v j₀ = 0 := by
        have hsplit : c j₀ • v j₀ + ∑ j ∈ T', c j • v j = 0 := by
          rw [hT', Finset.add_sum_erase T (fun j => c j • v j) hj₀]; exact hc
        have : (∑ j ∈ T', c j • v j) = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          rw [hzero' j hj, zero_smul]
        rwa [this, add_zero] at hsplit
      have := congrArg (fun x : κ →₀ R => x k) honly
      simp only [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul] at this
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · grind
  exact key T v hred c hc

/-- The reduction along `ε : R →+* S` of an `R`-linear map between free modules. -/
def reduceMap (ε : R →+* S) {ι κ : Type*}
    (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) : (ι →₀ S) →ₗ[S] (κ →₀ S) :=
  Finsupp.lsum S fun i =>
    LinearMap.toSpanSingleton S (κ →₀ S) (reduceVec ε (f (Finsupp.single i 1)))

omit [IsDomain R] [IsDomain S] in
@[simp] theorem reduceMap_single (ε : R →+* S) {ι κ : Type*}
    (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) (i : ι) (s : S) :
    reduceMap ε f (Finsupp.single i s) = s • reduceVec ε (f (Finsupp.single i 1)) := by
  simp [reduceMap, LinearMap.toSpanSingleton_apply]

/-- **Lemma 2.1, module-theoretic core.**  Reduction along a ring homomorphism between
commutative domains detects injectivity of maps between free modules of arbitrary rank. -/
theorem injective_of_reduceMap_injective (ε : R →+* S) {ι κ : Type*}
    (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) (h : Function.Injective (reduceMap ε f)) :
    Function.Injective f := by
  classical
  rw [injective_iff_map_eq_zero]
  intro u hu
  -- the reduced images of the relevant basis vectors are independent
  set v : ι → (κ →₀ R) := fun i => f (Finsupp.single i 1) with hv
  have hred : ∀ d : ι → S, (∑ j ∈ u.support, d j • reduceVec ε (v j)) = 0 →
      ∀ j ∈ u.support, d j = 0 := by
    intro d hd j hj
    have hmap : reduceMap ε f (∑ j ∈ u.support, Finsupp.single j (d j)) = 0 := by
      rw [map_sum]
      simpa [hv] using hd
    have hzero : (∑ j ∈ u.support, Finsupp.single j (d j)) = 0 := by
      have := h (by simpa using hmap : reduceMap ε f (∑ j ∈ u.support, Finsupp.single j (d j))
        = reduceMap ε f 0)
      simpa using this
    have := congrArg (fun x : ι →₀ S => x j) hzero
    simpa [Finset.sum_apply', Finsupp.single_apply, Finset.sum_ite_eq' u.support j, hj] using this
  -- the coefficients of `u` satisfy the corresponding relation
  have hc : (∑ j ∈ u.support, u j • v j) = 0 := by
    have hu' : u = ∑ j ∈ u.support, Finsupp.single j (u j) := (Finsupp.sum_single u).symm
    calc (∑ j ∈ u.support, u j • v j)
        = f (∑ j ∈ u.support, Finsupp.single j (u j)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hv]
          simp [← LinearMap.map_smul, Finsupp.smul_single]
      _ = f u := by rw [← hu']
      _ = 0 := hu
  have hzero := eq_zero_of_reduction_indep ε u.support v hred u hc
  ext j
  by_cases hj : j ∈ u.support
  · simp_all
  · simp_all

end FiniteChains

namespace FiniteChains

open MonoidAlgebra

variable (k : Type*) [CommRing k] {Q : Type*} [Group Q] (H : Subgroup Q)

/-- The right cosets `H \ Q`; left multiplication by `H` preserves a class. -/
abbrev RightCosets : Type _ := Quotient (QuotientGroup.rightRel H)

/-- The inclusion of group algebras `k[H] → k[Q]`. -/
def groupRingIncl : MonoidAlgebra k H →+* MonoidAlgebra k Q :=
  MonoidAlgebra.mapDomainRingHom k H.subtype

/-- `k[Q]` as a left module over `k[H]`. -/
instance moduleGroupRing :
    Module (MonoidAlgebra k H) (MonoidAlgebra k Q) := (groupRingIncl k H).toModule

variable {k H}

theorem groupRingIncl_apply_mem (x : MonoidAlgebra k H) (q : Q) (hq : q ∈ H) :
    (groupRingIncl k H x).coeff q = x.coeff (⟨q, hq⟩ : H) :=
  Finsupp.mapDomain_apply_of_injective Subtype.val_injective x.coeff (⟨q, hq⟩ : H)

theorem groupRingIncl_apply_notMem (x : MonoidAlgebra k H) (q : Q) (hq : q ∉ H) :
    (groupRingIncl k H x).coeff q = 0 := by simp_all [Finsupp.mapDomain_notin_range, hq, groupRingIncl]

theorem smul_def' (x : MonoidAlgebra k H) (y : MonoidAlgebra k Q) :
    x • y = groupRingIncl k H x * y := rfl

theorem groupRingIncl_single (h : H) (a : k) :
    groupRingIncl k H (single h a) = single (h : Q) a :=
  MonoidAlgebra.mapDomain_single

variable (k H)

/-- The chosen representative of a right coset. -/
def cosetRep (c : RightCosets H) : Q := c.out

variable {k H}

theorem mul_cosetRep_inv_mem (q : Q) :
    q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹ ∈ H := by
  have h : (Quotient.mk (QuotientGroup.rightRel H) q) =
      Quotient.mk (QuotientGroup.rightRel H)
        (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q)) :=
    (Quotient.out_eq _).symm
  have := Quotient.exact h.symm
  exact QuotientGroup.rightRel_apply.mp this

theorem mk_eq_iff {q r : Q} :
    Quotient.mk (QuotientGroup.rightRel H) q = Quotient.mk (QuotientGroup.rightRel H) r ↔
      r * q⁻¹ ∈ H := by
  rw [Quotient.eq]
  exact QuotientGroup.rightRel_apply

/-- The `k[H]`-linear map `(H \ Q →₀ k[H]) → k[Q]` sending the `c`-th basis vector to the
chosen representative of the coset `c`. -/
def cosetCombination :
    (RightCosets H →₀ MonoidAlgebra k H) →ₗ[MonoidAlgebra k H] MonoidAlgebra k Q :=
  Finsupp.linearCombination (MonoidAlgebra k H) fun c => single (cosetRep H c) (1 : k)

/-- The coefficients of `cosetCombination`: the `q`-th coefficient only sees the coset of
`q`, at the position `q · (rep of its coset)⁻¹` of `H`. -/
theorem cosetCombination_apply (F : RightCosets H →₀ MonoidAlgebra k H) (q : Q) :
    (cosetCombination F).coeff q =
      (F (Quotient.mk (QuotientGroup.rightRel H) q)).coeff
        ⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹,
          mul_cosetRep_inv_mem q⟩ := by
  classical
  rw [cosetCombination, Finsupp.linearCombination_apply, Finsupp.sum]
  have hterm : ∀ c ∈ F.support,
      (F c • single (cosetRep H c) 1 : MonoidAlgebra k Q).coeff q =
        if Quotient.mk (QuotientGroup.rightRel H) q = c then
          (F (Quotient.mk (QuotientGroup.rightRel H) q)).coeff
            ⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹,
              mul_cosetRep_inv_mem q⟩
        else 0 := by
    intro c _
    rw [smul_def', MonoidAlgebra.coeff_mul_single_apply, mul_one]
    by_cases hc : Quotient.mk (QuotientGroup.rightRel H) q = c
    · subst hc
      rw [if_pos rfl]
      exact groupRingIncl_apply_mem _ _ (mul_cosetRep_inv_mem q)
    · rw [if_neg hc]
      refine groupRingIncl_apply_notMem _ _ ?_
      intro hmem
      apply hc
      have : Quotient.mk (QuotientGroup.rightRel H) q =
          Quotient.mk (QuotientGroup.rightRel H) (cosetRep H c) := by
        rw [mk_eq_iff]
        simpa using (Subgroup.inv_mem _ hmem)
      rw [this]
      exact Quotient.out_eq c
  have hsum : (∑ c ∈ F.support, F c • single (cosetRep H c) 1).coeff q
      = ∑ c ∈ F.support, (F c • single (cosetRep H c) (1 : k)).coeff q := by
    simp [MonoidAlgebra.coeff_sum]
  rw [hsum, Finset.sum_congr rfl hterm, Finset.sum_ite_eq F.support]
  by_cases hq : Quotient.mk (QuotientGroup.rightRel H) q ∈ F.support
  · simp_all
  · simp_all

/-- The inverse bijection `Q ≃ (H \ Q) × H`. -/
def cosetEquiv : Q ≃ (RightCosets H × H) where
  toFun q := (Quotient.mk (QuotientGroup.rightRel H) q,
    ⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹, mul_cosetRep_inv_mem q⟩)
  invFun p := (p.2 : Q) * cosetRep H p.1
  left_inv q := by simp
  right_inv p := by
    obtain ⟨c, h, hh⟩ := p
    have hmk : Quotient.mk (QuotientGroup.rightRel H) ((h : Q) * cosetRep H c) = c := by
      have : Quotient.mk (QuotientGroup.rightRel H) ((h : Q) * cosetRep H c) =
          Quotient.mk (QuotientGroup.rightRel H) (cosetRep H c) := by
        rw [mk_eq_iff]
        simpa using Subgroup.inv_mem _ hh
      rw [this]; exact Quotient.out_eq c
    ext
    · exact hmk
    · simp_all

/-- `cosetCombination` is bijective: `k[Q]` is free over `k[H]` on coset representatives. -/
theorem cosetCombination_bijective :
    Function.Bijective (cosetCombination (k := k) (H := H)) := by
  constructor
  · intro F G hFG
    ext c h
    have h1 := congrArg (fun f : MonoidAlgebra k Q => f.coeff (h * cosetRep H c)) hFG
    simp only [cosetCombination_apply] at h1
    have hmk : Quotient.mk (QuotientGroup.rightRel H) (h * cosetRep H c) = c :=
      congrArg Prod.fst ((cosetEquiv).right_inv (c, h))
    simp only [hmk] at h1
    have heq : ⟨h * cosetRep H c * (cosetRep H c)⁻¹,
        show h * cosetRep H c * (cosetRep H c)⁻¹ ∈ H by
          simpa [hmk] using mul_cosetRep_inv_mem (h * cosetRep H c)⟩ = h := by
      ext; simp
    simp only [heq] at h1
    exact h1
  · intro f
    refine MonoidAlgebra.induction f ⟨0, map_zero _⟩ ?_
    rintro q a g - - ⟨G, hG⟩
    refine ⟨Finsupp.single (Quotient.mk (QuotientGroup.rightRel H) q)
      (single ⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹,
        mul_cosetRep_inv_mem q⟩ a) + G, ?_⟩
    rw [map_add, hG, cosetCombination, Finsupp.linearCombination_single, smul_def',
      groupRingIncl_single, MonoidAlgebra.single_mul_single]
    simp

/-- The basis of `k[Q]` over `k[H]` given by coset representatives. -/
def cosetBasis :
    Module.Basis (RightCosets H) (MonoidAlgebra k H) (MonoidAlgebra k Q) :=
  Module.Basis.ofRepr
    (LinearEquiv.ofBijective (cosetCombination (k := k) (H := H))
      cosetCombination_bijective).symm


end FiniteChains

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains

open MonoidAlgebra

variable (k : Type*) [CommRing k] {Q : Type*} [Group Q] (H : Subgroup Q)

/-- The augmentation `k[H] → k`. -/
def augH [IsMulCommutative H] : MonoidAlgebra k H →+* k :=
  (MonoidAlgebra.lift k k H (1 : H →* k)).toRingHom

/-- The reduction map of group rings `k[Q] → k[Q/H]`. -/
def quotRingHom [H.Normal] : MonoidAlgebra k Q →+* MonoidAlgebra k (Q ⧸ H) :=
  MonoidAlgebra.mapDomainRingHom k (QuotientGroup.mk' H)

variable {k H}

@[simp] theorem augH_single [IsMulCommutative H] (h : H) (a : k) :
    augH k H (single h a) = a := by
  simp [augH]

@[simp] theorem quotRingHom_single [H.Normal] (q : Q) (a : k) :
    quotRingHom k H (single q a) = single (q : Q ⧸ H) a := MonoidAlgebra.mapDomain_single

variable (H) in
/-- For a normal subgroup the right cosets are the elements of the quotient group. -/
def cosetQuotEquiv [H.Normal] : RightCosets H ≃ Q ⧸ H where
  toFun := Quotient.map' id (by
    intro a b h
    rw [QuotientGroup.rightRel_apply] at h
    rw [QuotientGroup.leftRel_apply]
    have := (Subgroup.Normal.conj_mem (by infer_instance) _ h a⁻¹)
    have e : a⁻¹ * (b * a⁻¹) * a⁻¹⁻¹ = a⁻¹ * b := by group
    rwa [e] at this)
  invFun := Quotient.map' id (by
    intro a b h
    rw [QuotientGroup.leftRel_apply] at h
    rw [QuotientGroup.rightRel_apply]
    have := (Subgroup.Normal.conj_mem (by infer_instance) _ h a)
    have e : a * (a⁻¹ * b) * a⁻¹ = b * a⁻¹ := by group
    rwa [e] at this)
  left_inv := by rintro ⟨q⟩; rfl
  right_inv := by rintro ⟨q⟩; rfl

@[simp] theorem cosetQuotEquiv_mk [H.Normal] (q : Q) :
    cosetQuotEquiv H (Quotient.mk (QuotientGroup.rightRel H) q) = (q : Q ⧸ H) := rfl

/-- The coordinates of an element of `k[Q]` in the `k[H]`-basis of coset representatives. -/
theorem cosetBasis_repr_cosetCombination [IsMulCommutative H]
    (F : RightCosets H →₀ MonoidAlgebra k H) :
    (cosetBasis (k := k) (H := H)).repr (cosetCombination F) = F := by
  simp [cosetBasis, cosetCombination]

theorem cosetCombination_single_single [IsMulCommutative H] (q : Q) (a : k) :
    cosetCombination (Finsupp.single (Quotient.mk (QuotientGroup.rightRel H) q)
      (single (⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹,
        mul_cosetRep_inv_mem q⟩ : H) a)) = (single q a : MonoidAlgebra k Q) := by
  rw [cosetCombination, Finsupp.linearCombination_single, smul_def', groupRingIncl_single,
    MonoidAlgebra.single_mul_single]
  simp

theorem cosetBasis_repr_single [IsMulCommutative H] (q : Q) (a : k) :
    (cosetBasis (k := k) (H := H)).repr (single q a) =
      Finsupp.single (Quotient.mk (QuotientGroup.rightRel H) q)
        (single (⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹,
          mul_cosetRep_inv_mem q⟩ : H) a) := by
  rw [← cosetCombination_single_single (H := H) q a, cosetBasis_repr_cosetCombination]

/-- The key compatibility, on the generators `single q a` of `k[Q]`. -/
theorem augH_cosetBasis_repr_single [H.Normal] [IsMulCommutative H] (q : Q) (a : k)
    (c : RightCosets H) :
    augH k H ((cosetBasis (k := k) (H := H)).repr (single q a) c) =
      (quotRingHom k H (single q a)).coeff (cosetQuotEquiv H c) := by
  classical
  rw [cosetBasis_repr_single q a, quotRingHom_single (H := H) q a]
  by_cases hc : c = Quotient.mk (QuotientGroup.rightRel H) q
  · simp_all
  · rw [Finsupp.single_apply, if_neg (fun h => hc h.symm), map_zero, MonoidAlgebra.coeff_single, Finsupp.single_apply,
      if_neg]
    intro h
    exact hc ((cosetQuotEquiv H).injective (by rw [cosetQuotEquiv_mk, h]))

/-- **The key compatibility.**  Reducing an element of `k[Q]` to `k[Q/H]` amounts to
applying the augmentation `k[H] → k` to each of its coordinates in the basis of coset
representatives. -/
theorem augH_cosetBasis_repr [H.Normal] [IsMulCommutative H] (x : MonoidAlgebra k Q)
    (c : RightCosets H) :
    augH k H ((cosetBasis (k := k) (H := H)).repr x c) = (quotRingHom k H x).coeff (cosetQuotEquiv H c) := by
  -- both sides are additive in `x`, so it suffices to treat `x = single q a`
  set L : MonoidAlgebra k Q →+ k :=
    (augH k H).toAddMonoidHom.comp
      ((Finsupp.applyAddHom c).comp
        ((cosetBasis).repr.toLinearMap.toAddMonoidHom)) with hL
  set M : MonoidAlgebra k Q →+ k :=
    (Finsupp.applyAddHom (cosetQuotEquiv H c)).comp
      ((MonoidAlgebra.coeffAddEquiv).toAddMonoidHom.comp (quotRingHom k H).toAddMonoidHom) with hM
  have hLM : L = M := by
    refine MonoidAlgebra.addMonoidHom_ext ?_
    intro q a
    simp only [hL, hM, AddMonoidHom.coe_comp, Function.comp_apply,
      LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, Finsupp.applyAddHom_apply,
      RingHom.toAddMonoidHom_eq_coe]
    exact augH_cosetBasis_repr_single q a c
  have := congrArg (fun g : MonoidAlgebra k Q →+ k => g x) hLM
  simpa [hL, hM] using this

variable (k H)

/-- A vector of elements of `k[Q]`, written in the `k[H]`-basis of coset representatives:
this exhibits `k[Q]^{(ι)}` as a free `k[H]`-module on `ι × (H \ Q)`. -/
def vecCoords (ι : Type*) [IsMulCommutative H] :
    (ι →₀ MonoidAlgebra k Q) ≃ₗ[MonoidAlgebra k H]
      ((ι × RightCosets H) →₀ MonoidAlgebra k H) :=
  (Finsupp.mapRange.linearEquiv (cosetBasis (k := k) (H := H)).repr).trans
    (Finsupp.curryLinearEquiv (MonoidAlgebra k H)).symm

/-- A vector of elements of `k[Q/H]`, written in the `k`-basis `Q/H`, indexed through the
bijection between `Q/H` and the right cosets. -/
def redCoords (ι : Type*) [H.Normal] :
    (ι →₀ MonoidAlgebra k (Q ⧸ H)) ≃ₗ[k] ((ι × RightCosets H) →₀ k) :=
  (Finsupp.mapRange.linearEquiv
      ((MonoidAlgebra.coeffLinearEquiv k).trans
        (Finsupp.domLCongr (R := k) (cosetQuotEquiv H).symm) :
        MonoidAlgebra k (Q ⧸ H) ≃ₗ[k] (RightCosets H →₀ k))).trans
    (Finsupp.curryLinearEquiv k).symm

variable {k H}

@[simp] theorem vecCoords_apply [IsMulCommutative H] {ι : Type*} (u : ι →₀ MonoidAlgebra k Q)
    (i : ι) (c : RightCosets H) :
    vecCoords k H ι u (i, c) = (cosetBasis (k := k) (H := H)).repr (u i) c := rfl

@[simp] theorem redCoords_apply [H.Normal] {ι : Type*} (w : ι →₀ MonoidAlgebra k (Q ⧸ H))
    (i : ι) (c : RightCosets H) :
    redCoords k H ι w (i, c) = (w i).coeff (cosetQuotEquiv H c) := rfl

/-- **The commuting square.**  Reducing a vector over `k[Q]` to `k[Q/H]` is the same as
applying the augmentation `k[H] → k` to all its coordinates in the basis of coset
representatives. -/
theorem mapRange_augH_vecCoords [H.Normal] [IsMulCommutative H] {ι : Type*}
    (u : ι →₀ MonoidAlgebra k Q) :
    Finsupp.mapRange (augH k H) (map_zero _) (vecCoords k H ι u) =
      redCoords k H ι (Finsupp.mapRange (quotRingHom k H) (map_zero _) u) := by
  ext ⟨i, c⟩
  by_cases hi : u i = 0
  · simp_all
  · simpa using augH_cosetBasis_repr (u i) c

end FiniteChains
end

section
open scoped IsMulCommutative
namespace FiniteChains

open MonoidAlgebra

variable (k : Type*) [CommRing k] {Q : Type*} [Group Q] (H : Subgroup Q)

/-- Coefficientwise reduction of a vector over `k[Q]` to a vector over `k[Q/H]`. -/
def reduceVecQ [H.Normal] {ι : Type*} (u : ι →₀ MonoidAlgebra k Q) :
    ι →₀ MonoidAlgebra k (Q ⧸ H) :=
  Finsupp.mapRange (quotRingHom k H) (map_zero _) u

/-- The reduction along `k[Q] → k[Q/H]` of a map of free left `k[Q]`-modules: the map given
by the reduced matrix. -/
def reduceLinQ [H.Normal] {ι κ : Type*}
    (f : (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k Q] (κ →₀ MonoidAlgebra k Q)) :
    (ι →₀ MonoidAlgebra k (Q ⧸ H)) →ₗ[MonoidAlgebra k (Q ⧸ H)]
      (κ →₀ MonoidAlgebra k (Q ⧸ H)) :=
  Finsupp.linearCombination _ fun i => reduceVecQ k H (f (Finsupp.single i 1))

variable {k H}

@[simp] theorem reduceVecQ_apply [H.Normal] {ι : Type*} (u : ι →₀ MonoidAlgebra k Q) (i : ι) :
    reduceVecQ k H u i = quotRingHom k H (u i) := rfl

theorem reduceVecQ_smul [H.Normal] {ι : Type*} (x : MonoidAlgebra k Q)
    (u : ι →₀ MonoidAlgebra k Q) :
    reduceVecQ k H (x • u) = quotRingHom k H x • reduceVecQ k H u := by
  ext i
  simp

theorem reduceLinQ_single [H.Normal] {ι κ : Type*}
    (f : (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k Q] (κ →₀ MonoidAlgebra k Q))
    (i : ι) (b : MonoidAlgebra k (Q ⧸ H)) :
    reduceLinQ k H f (Finsupp.single i b) = b • reduceVecQ k H (f (Finsupp.single i 1)) := by
  simp [reduceLinQ]

/-- The `k[H]`-scalar action on vectors over `k[Q]` is the action of the image in `k[Q]`. -/
theorem smul_vec_eq {ι : Type*} [IsMulCommutative H] (r : MonoidAlgebra k H)
    (u : ι →₀ MonoidAlgebra k Q) : r • u = groupRingIncl k H r • u := rfl

variable (H) in
/-- A map of free left `k[Q]`-modules, viewed as a map of `k[H]`-modules. -/
def restrictToH [IsMulCommutative H] {ι κ : Type*}
    (f : (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k Q] (κ →₀ MonoidAlgebra k Q)) :
    (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k H] (κ →₀ MonoidAlgebra k Q) where
  toFun := f
  map_add' := f.map_add
  map_smul' r u := by
    rw [smul_vec_eq (H := H) r u, f.map_smul, ← smul_vec_eq (H := H)]
    rfl

variable (H) in
@[simp] theorem restrictToH_apply [IsMulCommutative H] {ι κ : Type*}
    (f : (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k Q] (κ →₀ MonoidAlgebra k Q))
    (u : ι →₀ MonoidAlgebra k Q) : restrictToH H f u = f u := rfl

theorem cosetQuotEquiv_cosetRep [H.Normal] (c : RightCosets H) :
    ((cosetRep H c : Q) : Q ⧸ H) = cosetQuotEquiv H c := by
  conv_rhs => rw [← Quotient.out_eq c]
  rfl

/-- The coordinates of a chosen coset representative: it is the corresponding basis vector. -/
theorem cosetBasis_repr_cosetRep [IsMulCommutative H] (c : RightCosets H) :
    (cosetBasis (k := k) (H := H)).repr (single (cosetRep H c) (1 : k)) =
      Finsupp.single c (1 : MonoidAlgebra k H) := by
  rw [cosetBasis_repr_single]
  have hc : Quotient.mk (QuotientGroup.rightRel H) (cosetRep H c) = c := Quotient.out_eq c
  simp only [hc]
  congr 1
  have hone : (⟨cosetRep H c * (cosetRep H c)⁻¹, by simp⟩ : H) = 1 := Subtype.ext (by simp)
  rw [hone]
  rfl

theorem vecCoords_symm_single [IsMulCommutative H] {ι : Type*} (i : ι) (c : RightCosets H) :
    (vecCoords k H ι).symm (Finsupp.single (i, c) 1) =
      Finsupp.single i (single (cosetRep H c) (1 : k)) := by
  classical
  rw [LinearEquiv.symm_apply_eq]
  refine Finsupp.ext ?_
  rintro ⟨i', c'⟩
  rw [vecCoords_apply]
  by_cases hi : i' = i
  · subst hi
    rw [Finsupp.single_eq_same, cosetBasis_repr_cosetRep, Finsupp.single_apply,
      Finsupp.single_apply]
    simp [Prod.ext_iff]
  · simp_all

theorem redCoords_symm_single [H.Normal] {ι : Type*} (i : ι) (c : RightCosets H) (a : k) :
    (redCoords k H ι).symm (Finsupp.single (i, c) a) =
      Finsupp.single i (single (cosetQuotEquiv H c) a) := by
  classical
  rw [LinearEquiv.symm_apply_eq]
  refine Finsupp.ext ?_
  rintro ⟨i', c'⟩
  rw [redCoords_apply]
  by_cases hi : i' = i
  · subst hi
    rw [Finsupp.single_eq_same, MonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    have hiff : ((cosetQuotEquiv H) c = (cosetQuotEquiv H) c') ↔ ((i', c) = (i', c')) := by
      simp [Prod.ext_iff, (cosetQuotEquiv H).injective.eq_iff]
    simp [hiff]
  · simp_all

section Main

variable [IsDomain k] [H.Normal] [IsMulCommutative H] [IsMulTorsionFree H]

/-- **Lemma 2.1.**  For a torsion-free abelian normal subgroup `H ◁ Q` and an integral
domain `k`, a map of free left `k[Q]`-modules of arbitrary rank is injective as soon as its
reduction along `k[Q] → k[Q/H]` is. -/
theorem injective_of_reduceLinQ_injective {ι κ : Type*}
    (f : (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k Q] (κ →₀ MonoidAlgebra k Q))
    (hred : Function.Injective (reduceLinQ k H f)) : Function.Injective f := by
  haveI := monoidAlgebra_isDomain k H
  -- `f` written in the `k[H]`-basis of coset representatives
  set F : ((ι × RightCosets H) →₀ MonoidAlgebra k H) →ₗ[MonoidAlgebra k H]
      ((κ × RightCosets H) →₀ MonoidAlgebra k H) :=
    (vecCoords k H κ).toLinearMap ∘ₗ (restrictToH H f) ∘ₗ (vecCoords k H ι).symm.toLinearMap with hF
  -- the reduced map, in coordinates, is the reduction of `f` along `k[Q] → k[Q/H]`
  have hsquare : ∀ w, reduceMap (augH k H) F w =
      redCoords k H κ (reduceLinQ k H f ((redCoords k H ι).symm w)) := by
    intro w
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add w₁ w₂ h₁ h₂ => simp_all
    | single p a =>
        obtain ⟨i, c⟩ := p
        rw [reduceMap_single, hF]
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, vecCoords_symm_single,
          restrictToH_apply]
        have hsingle : (Finsupp.single i (single (cosetRep H c) (1 : k))) =
            (single (cosetRep H c) (1 : k)) • Finsupp.single i 1 := by
          ext j
          by_cases hj : j = i <;> simp [hj, Finsupp.single_apply]
        rw [hsingle, f.map_smul]
        -- pass to the reduced side
        rw [show (reduceVec (augH k H)
              (vecCoords k H κ ((single (cosetRep H c) (1 : k)) •
                f (Finsupp.single i 1)))) =
            redCoords k H κ (reduceVecQ k H
              ((single (cosetRep H c) (1 : k)) • f (Finsupp.single i 1)))
          from mapRange_augH_vecCoords _]
        rw [reduceVecQ_smul, quotRingHom_single, cosetQuotEquiv_cosetRep,
          redCoords_symm_single, reduceLinQ_single, ← map_smul (redCoords k H κ)]
        congr 1
        rw [← smul_assoc]
        congr 1
        simp
  have hFinj : Function.Injective (reduceMap (augH k H) F) := by
    have hfun  := funext hsquare
    rw [hfun]
    exact (redCoords k H κ).injective.comp (hred.comp (redCoords k H ι).symm.injective)
  have hFinj'  := injective_of_reduceMap_injective (augH k H) F hFinj
  intro u v huv
  have h1 : F (vecCoords k H ι u) = F (vecCoords k H ι v) := by
    simp only [hF, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      restrictToH_apply, huv]
  exact (vecCoords k H ι).injective (hFinj' h1)

end Main

end FiniteChains
end

namespace FiniteChains

open MonoidAlgebra

variable (k : Type*) [CommRing k] {G : Type*} [Group G] {I J : Type*}

/-- Coefficientwise reduction of a vector over `k[G]` to a vector over `k[G/M]`. -/
def redVecK (M : Subgroup G) [M.Normal] (v : J →₀ MonoidAlgebra k G) :
    J →₀ MonoidAlgebra k (G ⧸ M) :=
  Finsupp.mapRange (quotRingHom k M) (map_zero _) v

variable {k}

@[simp] theorem redVecK_apply (M : Subgroup G) [M.Normal] (v : J →₀ MonoidAlgebra k G) (j : J) :
    redVecK k M v j = quotRingHom k M (v j) := rfl

variable (k) in
/-- The `j`-th column of the reduced boundary matrix, over `k`. -/
def boundaryColK (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] (j : J) :
    I →₀ MonoidAlgebra k (G ⧸ M) :=
  Finsupp.onFinset (hcol j).toFinset (fun i => quotRingHom k M (b i j)) (by
    intro i hi
    simp only [ne_eq] at hi
    have hb : b i j ≠ 0 := fun h => hi (by rw [h, map_zero])
    simpa using hb)

@[simp] theorem boundaryColK_apply (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] (j : J) (i : I) :
    boundaryColK k b hcol M j i = quotRingHom k M (b i j) := rfl

variable (k) in
/-- The Fox boundary `∂_{2,M}` as a map of free left `k[G/M]`-modules. -/
def boundaryMapK (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] :
    (J →₀ MonoidAlgebra k (G ⧸ M)) →ₗ[MonoidAlgebra k (G ⧸ M)]
      (I →₀ MonoidAlgebra k (G ⧸ M)) :=
  Finsupp.linearCombination _ (boundaryColK k b hcol M)

theorem boundaryMapK_apply_coord (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal]
    (u : J →₀ MonoidAlgebra k (G ⧸ M)) (i : I) :
    boundaryMapK k b hcol M u i = ∑ j ∈ u.support, u j * quotRingHom k M (b i j) := by simp_all [boundaryMapK, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finset_sum_apply]

theorem boundaryMapK_single (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] (j : J) :
    boundaryMapK k b hcol M (Finsupp.single j (1 : MonoidAlgebra k (G ⧸ M)))
      = boundaryColK k b hcol M j := by
  rw [boundaryMapK, Finsupp.linearCombination_single, one_smul]

variable (k) in
/-- The `i`-th coordinate of the Fox boundary of the coefficient vector `v`, over `k`. -/
def foxBoundaryK (b : I → J → MonoidAlgebra k G)
    (v : J →₀ MonoidAlgebra k G) (i : I) : MonoidAlgebra k G :=
  ∑ j ∈ v.support, v j * b i j

theorem boundaryMapK_redVecK (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal]
    (v : J →₀ MonoidAlgebra k G) (i : I) :
    boundaryMapK k b hcol M (redVecK k M v) i = quotRingHom k M (foxBoundaryK k b v i) := by
  have hsupp : (redVecK k M v).support ⊆ v.support := by
    intro j hj
    simp at hj ⊢
    intro h
    exact hj (by rw [h, map_zero])
  rw [boundaryMapK_apply_coord, foxBoundaryK, map_sum,
    Finset.sum_congr rfl (fun j (_ : j ∈ v.support) => map_mul (quotRingHom k M) (v j) (b i j))]
  refine Finset.sum_subset hsupp ?_
  simp_all

/-- Reduction of coefficient vectors is surjective. -/
theorem quotRingHomK_surjective (M : Subgroup G) [M.Normal] :
    Function.Surjective (quotRingHom k M) := by
  intro y
  obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective (M := k) (QuotientGroup.mk'_surjective M) y.coeff
  exact ⟨MonoidAlgebra.ofCoeff x, MonoidAlgebra.coeff_injective hx⟩

/-- Every vector over `k[G/M]` lifts to a vector over `k[G]`. -/
theorem exists_liftK (M : Subgroup G) [M.Normal] (u : J →₀ MonoidAlgebra k (G ⧸ M)) :
    ∃ v : J →₀ MonoidAlgebra k G, redVecK k M v = u := by
  classical
  choose lift hlift using quotRingHomK_surjective (k := k) M
  refine ⟨Finsupp.mapRange (fun y => if y = 0 then 0 else lift y) (by simp) u, ?_⟩
  refine Finsupp.ext fun j => ?_
  simp
  by_cases h : u j = 0 <;> simp [h, hlift]

/-- **Lemma 2.1 for a pair of normal subgroups, over an arbitrary domain of
coefficients.**  If `C ≤ N` are normal subgroups of `G` with `N/C` torsion-free abelian,
then injectivity of the boundary reduced modulo `N` implies injectivity of the boundary
reduced modulo `C`. -/
theorem injective_boundaryMapK_of_injective [IsDomain k] (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (C N : Subgroup G) [C.Normal] [N.Normal]
    (hCN : C ≤ N)
    [IsMulCommutative (N.map (QuotientGroup.mk' C))]
    [IsMulTorsionFree (N.map (QuotientGroup.mk' C))]
    (h : Function.Injective (boundaryMapK k b hcol N)) :
    Function.Injective (boundaryMapK k b hcol C) := by
  set H : Subgroup (G ⧸ C) := N.map (QuotientGroup.mk' C) with hH
  set e : ((G ⧸ C) ⧸ H) ≃* (G ⧸ N) := QuotientGroup.quotientQuotientEquivQuotient C N hCN with he
  set E : MonoidAlgebra k ((G ⧸ C) ⧸ H) →+* MonoidAlgebra k (G ⧸ N) :=
    MonoidAlgebra.mapDomainRingHom k e.toMonoidHom with hE
  -- the two reductions of `k[G]` agree
  have L1 : ∀ x : MonoidAlgebra k G,
      E (quotRingHom k H (quotRingHom k C x)) = quotRingHom k N x := by
    intro x
    have key : (E.comp ((quotRingHom k H).comp (quotRingHom k C)))
        = quotRingHom k N := by
      apply MonoidAlgebra.ringHom_ext
      · simp_all
      · intro g
        simp [hE, quotRingHom, MonoidAlgebra.mapDomainRingHom, Finsupp.mapDomain_single, he]
        rfl
    exact congrArg (fun f : MonoidAlgebra k G →+* MonoidAlgebra k (G ⧸ N) => f x) key
  have hEinj : Function.Injective E :=
    fun _ _ h => MonoidAlgebra.coeff_injective (Finsupp.mapDomain_injective e.injective (congrArg MonoidAlgebra.coeff h))
  have hEv : Function.Injective (Finsupp.mapRange (α := J) E (map_zero _)) :=
    Finsupp.mapRange_injective E (map_zero _) hEinj
  -- the columns correspond
  have hcolumn : ∀ j : J,
      Finsupp.mapRange E (map_zero _)
          (reduceVecQ k H (boundaryMapK k b hcol C (Finsupp.single j 1))) =
        boundaryColK k b hcol N j := by
    intro j
    refine Finsupp.ext fun i => ?_
    rw [Finsupp.mapRange_apply, reduceVecQ_apply, boundaryColK_apply,
      boundaryMapK_single, boundaryColK_apply]
    exact L1 (b i j)
  -- the square: reduction over `k[Q]` corresponds to reduction modulo `N`
  have hsq : ∀ w : J →₀ MonoidAlgebra k ((G ⧸ C) ⧸ H),
      Finsupp.mapRange E (map_zero _) (reduceLinQ k H (boundaryMapK k b hcol C) w) =
        boundaryMapK k b hcol N (Finsupp.mapRange E (map_zero _) w) := by
    intro w
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add w₁ w₂ h₁ h₂ =>
        rw [map_add, Finsupp.mapRange_add (by simp) (f := E), h₁, h₂,
          Finsupp.mapRange_add (by simp) (f := E), map_add]
    | single j y =>
        have hsmul : Finsupp.mapRange E (map_zero _)
            (y • reduceVecQ k H (boundaryMapK k b hcol C (Finsupp.single j 1))) =
            E y • Finsupp.mapRange E (map_zero _)
              (reduceVecQ k H (boundaryMapK k b hcol C (Finsupp.single j 1))) := by
          refine Finsupp.ext fun i => ?_
          simp
        rw [reduceLinQ_single, Finsupp.mapRange_single, hsmul, hcolumn j]
        conv_rhs => rw [boundaryMapK, Finsupp.linearCombination_single]
  -- the reduced map is injective, so Lemma 2.1 applies
  have hred : Function.Injective (reduceLinQ k H (boundaryMapK k b hcol C)) := by
    intro w z hwz
    refine hEv ?_
    have h1 : boundaryMapK k b hcol N (Finsupp.mapRange E (map_zero _) w) =
        boundaryMapK k b hcol N (Finsupp.mapRange E (map_zero _) z) := by
      rw [← hsq w, ← hsq z, hwz]
    exact h h1
  exact injective_of_reduceLinQ_injective (boundaryMapK k b hcol C) hred

end FiniteChains

section
open scoped commutatorElement
namespace FiniteChains

open MonoidAlgebra

variable {G : Type*} [Group G] {I J : Type*}

/-- Coefficientwise reduction of a vector over `ℤ[G]` to a vector over `ℤ[G/M]`. -/
def redVec (M : Subgroup G) [M.Normal] (v : J →₀ MonoidAlgebra ℤ G) :
    J →₀ MonoidAlgebra ℤ (G ⧸ M) :=
  redVecK ℤ M v

@[simp] theorem redVec_apply (M : Subgroup G) [M.Normal] (v : J →₀ MonoidAlgebra ℤ G) (j : J) :
    redVec M v j = quotRingHom ℤ M (v j) := rfl

/-- The Fox boundary `∂_{2,M}` as a map of free left `ℤ[G/M]`-modules. -/
def boundaryMap (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] :
    (J →₀ MonoidAlgebra ℤ (G ⧸ M)) →ₗ[MonoidAlgebra ℤ (G ⧸ M)]
      (I →₀ MonoidAlgebra ℤ (G ⧸ M)) :=
  boundaryMapK ℤ b hcol M

theorem boundaryMap_apply_coord (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal]
    (u : J →₀ MonoidAlgebra ℤ (G ⧸ M)) (i : I) :
    boundaryMap b hcol M u i = ∑ j ∈ u.support, u j * quotRingHom ℤ M (b i j) :=
  boundaryMapK_apply_coord b hcol M u i

theorem boundaryMap_redVec (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal]
    (v : J →₀ MonoidAlgebra ℤ G) (i : I) :
    boundaryMap b hcol M (redVec M v) i = quotRingHom ℤ M (foxBoundary b v i) :=
  boundaryMapK_redVecK b hcol M v i

/-- Reduction of `x ∈ ℤ[G]` vanishes exactly when, inside every coset of `M`, the
coefficients of `x` add up to zero. -/
theorem vanishesMod_iff_quotRingHom_eq_zero (M : Subgroup G) [M.Normal] (x : MonoidAlgebra ℤ G) :
    VanishesMod M x.coeff ↔ quotRingHom ℤ M x = 0 := by
  classical
  have hval : ∀ g : G, (quotRingHom ℤ M x).coeff (g) =
      ∑ h ∈ x.coeff.support.filter (fun h => h * g⁻¹ ∈ M), x.coeff h := by
    intro g
    show (Finsupp.mapDomain (QuotientGroup.mk' M) x.coeff) g = _
    rw [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finsupp.single_apply]
    congr 1
    simp
    rw [QuotientGroup.eq]
    constructor
    · intro hh
      have h1 : g⁻¹ * h ∈ M := by simpa using M.inv_mem hh
      have h2 := Subgroup.Normal.conj_mem (by infer_instance) _ h1 h
      have hgr : h * (g⁻¹ * h) * h⁻¹ = h * g⁻¹ := by group
      rwa [hgr] at h2
    · intro hh
      have h1 : g * h⁻¹ ∈ M := by simpa using M.inv_mem hh
      have h2 := Subgroup.Normal.conj_mem (by infer_instance) _ h1 h⁻¹
      have hgr : h⁻¹ * (g * h⁻¹) * h⁻¹⁻¹ = h⁻¹ * g := by group
      rwa [hgr] at h2
  constructor
  · intro h
    ext q
    induction q using QuotientGroup.induction_on with
    | H g => rw [hval g]; simpa using h g
  · intro h g
    rw [← hval g, h]
    simp

/-- Every vector over `ℤ[G/M]` lifts to a vector over `ℤ[G]`. -/
theorem exists_lift (M : Subgroup G) [M.Normal] (u : J →₀ MonoidAlgebra ℤ (G ⧸ M)) :
    ∃ v : J →₀ MonoidAlgebra ℤ G, redVec M v = u := exists_liftK M u

/-- The requirements attached to all coefficient vectors hold at `M` exactly when the
reduced boundary map is injective. -/
theorem forall_foxSat_iff_injective (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] :
    (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v M) ↔
      Function.Injective (boundaryMap b hcol M) := by
  constructor
  · intro h
    rw [injective_iff_map_eq_zero]
    intro u hu
    obtain ⟨v, rfl⟩ := exists_lift M u
    have hbd : ∀ i, VanishesMod M (foxBoundary b v i).coeff := by
      intro i
      rw [vanishesMod_iff_quotRingHom_eq_zero, ← boundaryMap_redVec b hcol M v i, hu]
      rfl
    have hv := h v hbd
    refine Finsupp.ext fun j => ?_
    rw [redVec_apply, Finsupp.coe_zero, Pi.zero_apply]
    exact (vanishesMod_iff_quotRingHom_eq_zero M (v j)).1 (hv j)
  · intro h v hbd j
    rw [vanishesMod_iff_quotRingHom_eq_zero]
    have hu : boundaryMap b hcol M (redVec M v) = 0 := by
      refine Finsupp.ext fun i => ?_
      rw [boundaryMap_redVec, Finsupp.coe_zero, Pi.zero_apply]
      exact (vanishesMod_iff_quotRingHom_eq_zero M _).1 (hbd i)
    have hz : redVec M v = 0 := h (by rw [hu, map_zero])
    have := congrArg (fun w : J →₀ MonoidAlgebra ℤ (G ⧸ M) => w j) hz
    simpa using this

/-- **Lemma 2.1 for a pair of normal subgroups.**  If `C ≤ N` are normal subgroups of `G`
with `N/C` torsion-free abelian, then injectivity of the boundary reduced modulo `N`
implies injectivity of the boundary reduced modulo `C`.  This is the case `k = ℤ` of
`FiniteChains.injective_boundaryMapK_of_injective`. -/
theorem injective_boundaryMap_of_injective (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (C N : Subgroup G) [C.Normal] [N.Normal]
    (hCN : C ≤ N)
    [IsMulCommutative (N.map (QuotientGroup.mk' C))]
    [IsMulTorsionFree (N.map (QuotientGroup.mk' C))]
    (h : Function.Injective (boundaryMap b hcol N)) :
    Function.Injective (boundaryMap b hcol C) :=
  injective_boundaryMapK_of_injective b hcol C N hCN h

/-- The image of `N` in `G/[N,N]`, that is `N/[N,N]`, is abelian. -/
instance isMulCommutative_map_commutator (N : Subgroup G) [N.Normal] :
    IsMulCommutative (N.map (QuotientGroup.mk' ⁅N, N⁆)) := by
  constructor
  constructor
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨m, hm, rfl⟩ := hy
  apply Subtype.ext
  show (QuotientGroup.mk' ⁅N, N⁆ n) * (QuotientGroup.mk' ⁅N, N⁆ m)
      = (QuotientGroup.mk' ⁅N, N⁆ m) * (QuotientGroup.mk' ⁅N, N⁆ n)
  rw [← map_mul, ← map_mul]
  simp only [QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hgr : (n * m)⁻¹ * (m * n) = ⁅m⁻¹, n⁻¹⁆ := by group
  rw [hgr]
  exact Subgroup.commutator_mem_commutator (N.inv_mem hm) (N.inv_mem hn)

/-- **The requirements pass to the commutator subgroup.**  If every requirement (2.2) holds
for the normal subgroup `N` and `N/[N,N]` is torsion free, then every requirement holds for
`[N,N]`. -/
theorem foxSat_commutator (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G) [N.Normal]
    [IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆))]
    (h : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) :
    ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v ⁅N, N⁆ := by
  have hle  := Subgroup.commutator_le_left N N
  rw [forall_foxSat_iff_injective b hcol]
  exact injective_boundaryMap_of_injective b hcol ⁅N, N⁆ N hle
    ((forall_foxSat_iff_injective b hcol N).1 h)

end FiniteChains
end

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α] {J : Type*} [Fintype J]
variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal] (ρ : J → FreeGroup α)

omit [Fintype α] [DecidableEq α] in
theorem proj_eq_quotRingHom : proj Nsub = quotRingHom ℤ Nsub := rfl

end FiniteChains

namespace FiniteChains

variable {G : Type*} [Group G]

/-- A finite subset of a nonempty chain has a lower bound inside the chain. -/
theorem exists_lower_bound_of_chain {C : Set (Subgroup G)} (hC : IsChain (· ≤ ·) C)
    (hne : C.Nonempty) (T : Finset (Subgroup G)) (hT : ↑T ⊆ C) :
    ∃ N ∈ C, ∀ x ∈ T, N ≤ x := by
  classical
  induction T using Finset.induction with
  | empty => obtain ⟨N, hN⟩ := hne; exact ⟨N, hN, by simp⟩
  | insert a T _ ih =>
      have hTsub : ↑T ⊆ C := fun x hx => hT (by simp [hx])
      have haC : a ∈ C := hT (by simp)
      obtain ⟨N, hNC, hN⟩ := ih hTsub
      rcases eq_or_ne N a with rfl | hne'
      · grind
      · rcases hC hNC haC hne' with hle | hle
        · exact ⟨N, hNC, fun x hx => by
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact hle
            · exact hN x hx'⟩
        · exact ⟨a, haC, fun x hx => by
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact le_rfl
            · exact hle.trans (hN x hx')⟩

/-- **The requirements pass to intersections of decreasing chains.**  If every requirement
depends on finitely many membership decisions, and if every member of a nonempty chain of
subgroups satisfies all requirements, then so does the intersection of the chain. -/
theorem sat_sInf_of_finitelyDetermined {ι : Type*} (Sat : Subgroup G → ι → Prop)
    (det : FinitelyDetermined Sat) {C : Set (Subgroup G)} (hC : IsChain (· ≤ ·) C)
    (hne : C.Nonempty) (hsat : ∀ N ∈ C, ∀ v, Sat N v) (v : ι) : Sat (sInf C) v := by
  classical
  obtain ⟨F, hF⟩ := det v
  -- for each element of `F` missing from the intersection, a member of the chain missing it
  have hchoice : ∀ g : G, ∃ N : Subgroup G, N ∈ C ∧ (g ∉ sInf C → g ∉ N) := by
    intro g
    by_cases hg : g ∈ sInf C
    · obtain ⟨N, hN⟩ := hne
      exact ⟨N, hN, fun h => absurd hg h⟩
    · simp_all
  choose wit hwitC hwit using hchoice
  obtain ⟨N, hNC, hNle⟩ :=
    exists_lower_bound_of_chain hC hne (F.image wit)
      (by
        intro x hx
        simp at hx
        obtain ⟨g, -, rfl⟩ := hx
        exact hwitC g)
  have hagree : ∀ g ∈ F, (g ∈ sInf C ↔ g ∈ N) := by
    intro g hg
    refine ⟨fun hmem => (sInf_le hNC) hmem, fun hmem => ?_⟩
    by_contra hcon
    exact hwit g hcon (hNle _ (Finset.mem_image.mpr ⟨g, hg, rfl⟩) hmem)
  exact (hF (sInf C) N hagree).2 (hsat N hNC v)

end FiniteChains

namespace FiniteChains

open Function

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V]

/-- `f` is *injective modulo `n`*: whenever `f u` is divisible by `n`, already `u` is.
For maps between free modules this is injectivity of the reduction `f ⊗ ℤ/n`. -/
def LiftsMod (f : U →+ V) (n : ℕ) : Prop :=
  ∀ u : U, (∃ w : V, f u = n • w) → ∃ u' : U, u = n • u'

/-- **The lifting step.**  If the target is torsion free and `f` is injective modulo every
prime, then every element whose multiple lies in the image already lies in the image. -/
theorem mem_range_of_nsmul_mem_range (f : U →+ V) [IsAddTorsionFree V]
    (hmod : ∀ p : ℕ, p.Prime → LiftsMod f p) :
    ∀ n : ℕ, n ≠ 0 → ∀ x : V, n • x ∈ f.range → x ∈ f.range := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn x hx
    rcases eq_or_ne n 1 with rfl | hn1
    · simpa using hx
    · obtain ⟨p, hp, m, rfl⟩ : ∃ p, p.Prime ∧ ∃ m, n = p * m := by
        obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hn1
        obtain ⟨m, rfl⟩ := hdvd
        exact ⟨p, hp, m, rfl⟩
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      have hpos  := hp.ne_zero
      obtain ⟨u, hu⟩ := hx
      -- `p` divides `f u`, hence `u`
      obtain ⟨u', hu'⟩ := hmod p hp u ⟨m • x, by rw [hu, mul_smul]⟩
      have hmx : m • x = f u' := by
        refine IsAddTorsionFree.nsmul_right_injective hpos ?_
        show p • (m • x) = p • f u'
        rw [← mul_smul, ← hu, hu', map_nsmul]
      have : m • x ∈ f.range := ⟨u', hmx.symm⟩
      rcases eq_or_ne m 1 with rfl | hm1
      · simpa using this
      · refine ih m ?_ hm x this
        have h2 := hp.two_le
        have hm' := Nat.pos_of_ne_zero hm
        nlinarith

/-!
## The Fox complex
-/

/-- Finitely supported functions into a torsion-free group are torsion free. -/
instance isAddTorsionFree_finsupp {α : Type*} {A : Type*} [AddCommGroup A]
    [IsAddTorsionFree A] : IsAddTorsionFree (α →₀ A) := by
  constructor
  intro n hn a b hab
  refine Finsupp.ext fun i => ?_
  have : (n • a) i = (n • b) i := congrArg (fun v : α →₀ A => v i) hab
  simpa using IsAddTorsionFree.nsmul_right_injective hn (by simpa using this)

/-- Group rings over `ℤ` are torsion free as additive groups. -/
instance isAddTorsionFree_monoidAlgebra {Q : Type*} [Monoid Q] :
    IsAddTorsionFree (MonoidAlgebra ℤ Q) :=
  by
    constructor
    intro n hn a b hab
    let e := (MonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Q)).toAddMonoidHom
    have hc : n • a.coeff = n • b.coeff := calc
      _ = e (n • a) := (map_nsmul e n a).symm
      _ = e (n • b) := congrArg e hab
      _ = _ := map_nsmul e n b
    apply MonoidAlgebra.coeff_injective
    exact IsAddTorsionFree.nsmul_right_injective hn hc

variable {G : Type*} [Group G] {I J : Type*}

/-!
## Removing the torsion-freeness hypothesis from the application of Lemma 2.1
-/


end FiniteChains

namespace FiniteChains

open Finset

variable {G : Type*} [Group G]

/-! ### Vanishing modulo `m` of a coefficient vector -/

open scoped Classical in
/-- The reduction of `x ∈ ℤ[G]` to `ℤ[G/N]` is divisible by `m`: inside every coset of `N`
the coefficients of `x` add up to a multiple of `m`.  For `m = 0` this is `VanishesMod`. -/
def VanishesModN (m : ℕ) (N : Subgroup G) (x : G →₀ ℤ) : Prop :=
  ∀ g : G, (m : ℤ) ∣ ∑ h ∈ x.support.filter (fun h => h * g⁻¹ ∈ N), x h


theorem vanishesModN_zero_iff (N : Subgroup G) (x : G →₀ ℤ) :
    VanishesModN 0 N x ↔ VanishesMod N x := by
  simp only [VanishesModN, VanishesMod, Nat.cast_zero, zero_dvd_iff]

/-- Whether the reduction of `x` vanishes modulo `m` only depends on the membership in `N`
of the finitely many quotients `h h'⁻¹` of elements of the support of `x`. -/
theorem vanishesModN_congr {m : ℕ} {x : G →₀ ℤ} {N N' : Subgroup G}
    (h : ∀ g ∈ x.support, ∀ g' ∈ x.support, (g * g'⁻¹ ∈ N ↔ g * g'⁻¹ ∈ N')) :
    VanishesModN m N x ↔ VanishesModN m N' x := by
  classical
  have main : ∀ M M' : Subgroup G,
      (∀ g ∈ x.support, ∀ g' ∈ x.support, (g * g'⁻¹ ∈ M ↔ g * g'⁻¹ ∈ M')) →
      VanishesModN m M x → VanishesModN m M' x := by
    intro M M' hMM' hM g
    by_cases hempty : (x.support.filter (fun h => h * g⁻¹ ∈ M')).Nonempty
    · obtain ⟨h₀, hh₀⟩ := hempty
      rw [mem_filter] at hh₀
      obtain ⟨hh₀supp, hh₀mem⟩ := hh₀
      have hfilter : x.support.filter (fun h => h * g⁻¹ ∈ M')
          = x.support.filter (fun h => h * h₀⁻¹ ∈ M) := by
        refine filter_congr fun h hh => ?_
        constructor
        · intro hmem
          have : h * h₀⁻¹ ∈ M' := by
            have : h * h₀⁻¹ = (h * g⁻¹) * (h₀ * g⁻¹)⁻¹ := by group
            rw [this]
            exact M'.mul_mem hmem (M'.inv_mem hh₀mem)
          exact (hMM' h hh h₀ hh₀supp).mpr this
        · intro hmem
          have hM'  := (hMM' h hh h₀ hh₀supp).mp hmem
          have : h * g⁻¹ = (h * h₀⁻¹) * (h₀ * g⁻¹) := by group
          rw [this]
          exact M'.mul_mem hM' hh₀mem
      rw [hfilter]
      exact hM h₀
    · rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Finset.sum_empty]
      exact dvd_zero _
  grind

variable {I J : Type*}

/-- The requirement (2.2) modulo `m`, attached to the coefficient vector `v`: if the
reduced boundary of `v` is divisible by `m`, then so is the reduced `v`. -/
def FoxSatMod (m : ℕ) (b : I → J → MonoidAlgebra ℤ G) (v : J →₀ MonoidAlgebra ℤ G)
    (N : Subgroup G) : Prop :=
  (∀ i : I, VanishesModN m N (foxBoundary b v i).coeff) → ∀ j : J, VanishesModN m N (v j).coeff

/-- For `m = 0` the requirement modulo `m` is the integral requirement. -/
theorem foxSatMod_zero_iff (b : I → J → MonoidAlgebra ℤ G) (v : J →₀ MonoidAlgebra ℤ G)
    (N : Subgroup G) : FoxSatMod 0 b v N ↔ FoxSat b v N := by
  simp only [FoxSatMod, FoxSat, vanishesModN_zero_iff]

/-- **Each requirement modulo `m` depends on finitely many membership decisions.** -/
theorem foxSatMod_finitelyDetermined (m : ℕ) (b : I → J → MonoidAlgebra ℤ G)
    (v : J →₀ MonoidAlgebra ℤ G) (hfin : {i : I | foxBoundary b v i ≠ 0}.Finite) :
    ∃ F : Finset G, ∀ N N' : Subgroup G,
      (∀ g ∈ F, (g ∈ N ↔ g ∈ N')) → (FoxSatMod m b v N ↔ FoxSatMod m b v N') := by
  classical
  set S : Finset G :=
    (v.support.biUnion fun j => (v j).coeff.support) ∪
      (hfin.toFinset.biUnion fun i => (foxBoundary b v i).coeff.support) with hS
  refine ⟨(S ×ˢ S).image (fun p => p.1 * p.2⁻¹), ?_⟩
  intro N N' hagree
  have hpair : ∀ g ∈ S, ∀ g' ∈ S, (g * g'⁻¹ ∈ N ↔ g * g'⁻¹ ∈ N') := by
    intro g hg g' hg'
    exact hagree _ (Finset.mem_image.mpr ⟨(g, g'), Finset.mem_product.mpr ⟨hg, hg'⟩, rfl⟩)
  have hvsupp : ∀ j : J, (v j).coeff.support ⊆ S := by
    intro j g hg
    by_cases hj : j ∈ v.support
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, hj, hg⟩)
    · rw [Finsupp.notMem_support_iff.mp hj] at hg
      simp at hg
  have hbsupp : ∀ i : I, (foxBoundary b v i).coeff.support ⊆ S := by
    intro i g hg
    by_cases hi : foxBoundary b v i = 0
    · rw [hi] at hg; simp at hg
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, ?_, hg⟩)
      simpa [Set.Finite.mem_toFinset] using hi
  have hv : ∀ j : J, (VanishesModN m N (v j).coeff ↔ VanishesModN m N' (v j).coeff) := fun j =>
    vanishesModN_congr fun g hg g' hg' => hpair g (hvsupp j hg) g' (hvsupp j hg')
  have hb : ∀ i : I,
      (VanishesModN m N (foxBoundary b v i).coeff ↔ VanishesModN m N' (foxBoundary b v i).coeff) :=
    fun i => vanishesModN_congr fun g hg g' hg' => hpair g (hbsupp i hg) g' (hbsupp i hg')
  constructor
  · intro hSat hbdry j
    exact (hv j).mp (hSat (fun i => (hb i).mpr (hbdry i)) j)
  · intro hSat hbdry j
    exact (hv j).mpr (hSat (fun i => (hb i).mp (hbdry i)) j)

/-! ### The requirement modulo `m` as a divisibility statement in `ℤ[G/N]` -/

open scoped Classical in
/-- The coefficient of the reduction of `x` at the coset of `g` is the sum of the
coefficients of `x` over that coset. -/
theorem quotRingHom_apply_mk (M : Subgroup G) [M.Normal] (x : MonoidAlgebra ℤ G) (g : G) :
    (quotRingHom ℤ M x).coeff ((g : G ⧸ M)) = ∑ h ∈ x.coeff.support.filter (fun h => h * g⁻¹ ∈ M), x.coeff h := by
  show (Finsupp.mapDomain (QuotientGroup.mk' M) x.coeff) (g : G ⧸ M) = _
  rw [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finsupp.single_apply]
  congr 1
  simp
  rw [QuotientGroup.eq]
  constructor
  · intro hh
    have h1 : g⁻¹ * h ∈ M := by simpa using M.inv_mem hh
    have h2 := Subgroup.Normal.conj_mem (by infer_instance) _ h1 h
    have hgr : h * (g⁻¹ * h) * h⁻¹ = h * g⁻¹ := by group
    rwa [hgr] at h2
  · intro hh
    have h1 : g * h⁻¹ ∈ M := by simpa using M.inv_mem hh
    have h2 := Subgroup.Normal.conj_mem (by infer_instance) _ h1 h⁻¹
    have hgr : h⁻¹ * (g * h⁻¹) * h⁻¹⁻¹ = h⁻¹ * g := by group
    rwa [hgr] at h2

/-- Vanishing modulo `m` means that every coefficient of the reduction is divisible by
`m`. -/
theorem vanishesModN_iff_dvd_coeff (m : ℕ) (M : Subgroup G) [M.Normal]
    (x : MonoidAlgebra ℤ G) :
    VanishesModN m M x.coeff ↔ ∀ q : G ⧸ M, (m : ℤ) ∣ (quotRingHom ℤ M x).coeff q := by
  constructor
  · intro h q
    induction q using QuotientGroup.induction_on with
    | H g => rw [quotRingHom_apply_mk]; exact h g
  · intro h g
    rw [← quotRingHom_apply_mk M x g]
    exact h _

/-- Coefficientwise division by `m`. -/
def divCoeff (m : ℕ) {H : Type*} (z : MonoidAlgebra ℤ H) : MonoidAlgebra ℤ H :=
  MonoidAlgebra.ofCoeff (Finsupp.mapRange (fun a : ℤ => a / (m : ℤ)) (by simp) z.coeff)

/-- An element all of whose coefficients are divisible by `m` is `m` times an element. -/
theorem nsmul_divCoeff (m : ℕ) {H : Type*} (z : MonoidAlgebra ℤ H)
    (hz : ∀ q : H, (m : ℤ) ∣ z.coeff q) : m • divCoeff m z = z := by
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun q => ?_
  show m • (divCoeff m z).coeff q = z.coeff q
  rw [divCoeff, MonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply, nsmul_eq_mul]
  exact Int.mul_ediv_cancel' (hz q)

/-- Divisibility of all coefficients by `m` means being `m` times an element. -/
theorem dvd_coeff_iff_nsmul (m : ℕ) {H : Type*} (z : MonoidAlgebra ℤ H) :
    (∀ q : H, (m : ℤ) ∣ z.coeff q) ↔ ∃ y : MonoidAlgebra ℤ H, z = m • y := by
  constructor
  · intro h
    exact ⟨divCoeff m z, (nsmul_divCoeff m z h).symm⟩
  · rintro ⟨y, rfl⟩ q
    refine ⟨y.coeff q, ?_⟩
    rw [MonoidAlgebra.coeff_smul_apply, nsmul_eq_mul]

/-- Vanishing modulo `m` in the form used in the chain argument: the reduction is `m` times
an element. -/
theorem vanishesModN_iff_nsmul (m : ℕ) (M : Subgroup G) [M.Normal] (x : MonoidAlgebra ℤ G) :
    VanishesModN m M x.coeff ↔ ∃ y, quotRingHom ℤ M x = m • y := by
  rw [vanishesModN_iff_dvd_coeff, dvd_coeff_iff_nsmul]

/-! ### The requirements modulo `m` are the lifting property of the Fox boundary -/

variable (b : I → J → MonoidAlgebra ℤ G)

/-- **The requirement modulo `m`, in the form used by the universal-coefficient
argument.**  If all requirements modulo `m` hold at `N`, then the reduced Fox boundary is
injective modulo `m`: whenever its value on a vector is divisible by `m`, the vector itself
is. -/
theorem liftsMod_of_foxSatMod (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G)
    [N.Normal] (m : ℕ) (h : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod m b v N) :
    LiftsMod (boundaryMap b hcol N).toAddMonoidHom m := by
  rintro u ⟨w, hw⟩
  obtain ⟨v, rfl⟩ := exists_lift N u
  have hbd : ∀ i : I, VanishesModN m N (foxBoundary b v i).coeff := by
    intro i
    rw [vanishesModN_iff_dvd_coeff]
    intro q
    have hcoord : quotRingHom ℤ N (foxBoundary b v i) = m • w i := by
      rw [← boundaryMap_redVec b hcol N v i]
      have := congrArg (fun z : I →₀ MonoidAlgebra ℤ (G ⧸ N) => z i) hw
      simpa using this
    rw [hcoord]
    exact ⟨(w i).coeff q, by
      rw [MonoidAlgebra.coeff_smul_apply, nsmul_eq_mul]⟩
  have hv := h v hbd
  refine ⟨Finsupp.mapRange (divCoeff m) (by simp [divCoeff]) (redVec N v), ?_⟩
  refine Finsupp.ext fun j => ?_
  show redVec N v j = m • (Finsupp.mapRange (divCoeff m) _ (redVec N v)) j
  rw [Finsupp.mapRange_apply]
  refine (nsmul_divCoeff m (redVec N v j) ?_).symm
  intro q
  have := (vanishesModN_iff_dvd_coeff m N (v j)).1 (hv j) q
  simpa [redVec_apply] using this

end FiniteChains

namespace FiniteChains

open MonoidAlgebra

variable {G : Type*} [Group G] {I J : Type*}

/-! ### Reduction of coefficients `ℤ[G] → k[G]` -/

/-- Coefficientwise reduction of the group ring along the unique ring map `ℤ → k`. -/
def coeffHom (k : Type*) [CommRing k] (H : Type*) [Group H] :
    MonoidAlgebra ℤ H →+* MonoidAlgebra k H :=
  MonoidAlgebra.mapRangeRingHom H (Int.castRingHom k)

variable {k : Type*} [CommRing k]

@[simp] theorem coeffHom_apply (x : MonoidAlgebra ℤ G) (g : G) :
    (coeffHom k G x).coeff g = ((x.coeff g : ℤ) : k) := rfl

theorem quotRingHom_coeffHom (M : Subgroup G) [M.Normal] (x : MonoidAlgebra ℤ G) :
    quotRingHom k M (coeffHom k G x) = coeffHom k (G ⧸ M) (quotRingHom ℤ M x) := by
  apply MonoidAlgebra.coeff_injective
  change Finsupp.mapDomain (QuotientGroup.mk' M)
      (Finsupp.mapRange (fun a : ℤ => ((a : k))) (by simp) x.coeff)
    = Finsupp.mapRange (fun a : ℤ => ((a : k))) (by simp)
      (Finsupp.mapDomain (QuotientGroup.mk' M) x.coeff)
  exact Finsupp.mapDomain_mapRange _ _ _ _ (fun a b => by push_cast; ring)

theorem coeffHom_surjective_zmod (m : ℕ) :
    Function.Surjective (coeffHom (ZMod m) G) := by
  have h : Function.Surjective (fun a : ℤ => ((a : ZMod m))) := ZMod.intCast_surjective
  intro y
  obtain ⟨x, hx⟩ := Finsupp.mapRange_surjective (fun a : ℤ => ((a : ZMod m))) (by simp) h y.coeff
  exact ⟨MonoidAlgebra.ofCoeff x, MonoidAlgebra.coeff_injective hx⟩

/-- Coefficientwise reduction of a vector over `ℤ[G]` to a vector over `k[G]`. -/
def coeffVec (k : Type*) [CommRing k] (H : Type*) [Group H] {J : Type*}
    (v : J →₀ MonoidAlgebra ℤ H) : J →₀ MonoidAlgebra k H :=
  Finsupp.mapRange (coeffHom k H) (map_zero _) v

@[simp] theorem coeffVec_apply (v : J →₀ MonoidAlgebra ℤ G) (j : J) :
    coeffVec k G v j = coeffHom k G (v j) := rfl

/-- Every vector over `ZMod m [G]` comes from a vector over `ℤ[G]`. -/
theorem exists_coeffVec (m : ℕ) (w : J →₀ MonoidAlgebra (ZMod m) G) :
    ∃ v : J →₀ MonoidAlgebra ℤ G, coeffVec (ZMod m) G v = w := by
  classical
  choose lift hlift using coeffHom_surjective_zmod (G := G) m
  refine ⟨Finsupp.mapRange (fun y => if y = 0 then 0 else lift y) (by simp) w, ?_⟩
  refine Finsupp.ext fun j => ?_
  simp
  by_cases h : w j = 0 <;> simp [h, hlift]

/-! ### The reduced presentation matrix -/

/-- The Fox boundary matrix of the presentation, read over `k`. -/
def bMod (k : Type*) [CommRing k] (H : Type*) [Group H] {I J : Type*}
    (b : I → J → MonoidAlgebra ℤ H) (i : I) (j : J) : MonoidAlgebra k H :=
  coeffHom k H (b i j)

theorem bMod_col_finite (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (j : J) : {i | bMod k G b i j ≠ 0}.Finite := by
  refine (hcol j).subset ?_
  intro i hi
  simp at hi ⊢
  intro h
  exact hi (by simp [bMod, h])

theorem foxBoundaryK_bMod (b : I → J → MonoidAlgebra ℤ G) (v : J →₀ MonoidAlgebra ℤ G)
    (i : I) :
    foxBoundaryK k (bMod k G b) (coeffVec k G v) i = coeffHom k G (foxBoundary b v i) := by
  have hsupp : (coeffVec k G v).support ⊆ v.support := by
    intro j hj
    simp at hj ⊢
    intro h
    exact hj (by rw [h, map_zero])
  rw [foxBoundaryK, foxBoundary, map_sum,
    Finset.sum_congr rfl (fun j (_ : j ∈ v.support) =>
      map_mul (coeffHom k G) (v j) (b i j))]
  refine Finset.sum_subset hsupp ?_
  simp_all

/-! ### The requirement modulo `m` is injectivity of the boundary over `ZMod m` -/

/-- Vanishing modulo `m` of a coefficient vector is vanishing of its reduction over
`ZMod m`. -/
theorem vanishesModN_iff_zmod (m : ℕ) (M : Subgroup G) [M.Normal] (x : MonoidAlgebra ℤ G) :
    VanishesModN m M x.coeff ↔ quotRingHom (ZMod m) M (coeffHom (ZMod m) G x) = 0 := by
  rw [vanishesModN_iff_dvd_coeff, quotRingHom_coeffHom]
  constructor
  · intro h
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun q => ?_
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (h q)
  · intro h q
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 ?_
    have := congrArg (fun z : MonoidAlgebra (ZMod m) (G ⧸ M) => z.coeff q) h
    simpa using this

/-- **The requirements modulo `m` are exactly the injectivity of the Fox boundary over
`ZMod m`.**  This is the analogue over `ZMod m` of
`FiniteChains.forall_foxSat_iff_injective`; for `m = 0` the two statements agree. -/
theorem forall_foxSatMod_iff_injective (m : ℕ) (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] :
    (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod m b v M) ↔
      Function.Injective
        (boundaryMapK (ZMod m) (bMod (ZMod m) G b) (bMod_col_finite b hcol) M) := by
  set bm := bMod (ZMod m) G b with hbm
  set hc := bMod_col_finite (k := ZMod m) b hcol with hhc
  have key : ∀ v : J →₀ MonoidAlgebra ℤ G, ∀ i : I,
      boundaryMapK (ZMod m) bm hc M (redVecK (ZMod m) M (coeffVec (ZMod m) G v)) i
        = quotRingHom (ZMod m) M (coeffHom (ZMod m) G (foxBoundary b v i)) := by
    intro v i
    rw [boundaryMapK_redVecK, foxBoundaryK_bMod]
  constructor
  · intro h
    rw [injective_iff_map_eq_zero]
    intro u hu
    obtain ⟨w, rfl⟩ := exists_liftK M u
    obtain ⟨v, rfl⟩ := exists_coeffVec m w
    have hbd : ∀ i : I, VanishesModN m M (foxBoundary b v i).coeff := by
      intro i
      rw [vanishesModN_iff_zmod, ← key v i, hu]
      rfl
    have hv := h v hbd
    refine Finsupp.ext fun j => ?_
    rw [redVecK_apply, coeffVec_apply, Finsupp.coe_zero, Pi.zero_apply]
    exact (vanishesModN_iff_zmod m M (v j)).1 (hv j)
  · intro h v hbd j
    rw [vanishesModN_iff_zmod]
    have hzero : boundaryMapK (ZMod m) bm hc M (redVecK (ZMod m) M (coeffVec (ZMod m) G v)) = 0 := by
      refine Finsupp.ext fun i => ?_
      rw [key v i, Finsupp.coe_zero, Pi.zero_apply]
      exact (vanishesModN_iff_zmod m M _).1 (hbd i)
    have hz : redVecK (ZMod m) M (coeffVec (ZMod m) G v) = 0 := h (by rw [hzero, map_zero])
    have := congrArg (fun z : J →₀ MonoidAlgebra (ZMod m) (G ⧸ M) => z j) hz
    simpa using this

/-! ### Lemma 2.1 over `𝔽ₚ` -/

/-- **The requirements modulo a prime pass to the commutator subgroup.**  This is the
half modulo `p` of the application of Lemma 2.1 at the end of Section 2. -/
theorem foxSatMod_commutator (p : ℕ) [Fact p.Prime] (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G) [N.Normal]
    [IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆))]
    (h : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N) :
    ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v ⁅N, N⁆ := by
  have hle  := Subgroup.commutator_le_left N N
  rw [forall_foxSatMod_iff_injective p b hcol]
  exact injective_boundaryMapK_of_injective _ _ ⁅N, N⁆ N hle
    ((forall_foxSatMod_iff_injective p b hcol N).1 h)

end FiniteChains

namespace FiniteChains

open MonoidAlgebra

universe u

variable {G : Type u} [Group G] {I J : Type u}

/-! ### Reduction of coefficients along a group homomorphism -/

/-- Reduction of coefficients is functorial. -/
theorem mapDomainRingHom_comp_apply {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B →* C) (x : MonoidAlgebra ℤ A) :
    MonoidAlgebra.mapDomainRingHom ℤ g (MonoidAlgebra.mapDomainRingHom ℤ f x)
      = MonoidAlgebra.mapDomainRingHom ℤ (g.comp f) x := by simp

/-! ### The cell-level data of a chain of two-complexes -/

variable (b : I → J → MonoidAlgebra ℤ G)

/-- The cell-level data of a chain `K = X₀ ⊂ ⋯ ⊂ Xₙ` of two-complexes, all of whose
inclusions induce the zero map on `π₂`.  Here `I` indexes the one-cells and `J` the
two-cells of `K`, and `b i j = ∂r_j/∂x_i` is its Fox boundary matrix over `ℤ[G]`,
`G = π₁(K)`. -/
structure ChainInput (n : ℕ) (Fund : ℕ → Type u) [∀ r, Group (Fund r)]
    (Gen Cell : ℕ → Type u) where
  /-- The map `π₁(K) → π₁(X_r)` induced by the inclusion. -/
  phi : ∀ r, G →* Fund r
  /-- The map `π₁(X_r) → π₁(X_{r+1})` induced by the inclusion. -/
  psi : ∀ r, Fund r →* Fund (r + 1)
  /-- The inclusions are compatible. -/
  phi_succ : ∀ r, (psi r).comp (phi r) = phi (r + 1)
  /-- The one-cells of `K` are one-cells of `X_r`. -/
  genIncl : ∀ r, I → Gen r
  /-- The two-cells of `K` are two-cells of `X_r`. -/
  cellIncl : ∀ r, J → Cell r
  cellIncl_injective : ∀ r, Function.Injective (cellIncl r)
  /-- The two-cells of `X_r` are two-cells of `X_{r+1}`. -/
  cellStep : ∀ r, Cell r → Cell (r + 1)
  cellStep_injective : ∀ r, Function.Injective (cellStep r)
  /-- The Fox boundary matrix of `X_r`, over `ℤ[π₁(X_r)]`. -/
  bdry : ∀ r, Gen r → Cell r → MonoidAlgebra ℤ (Fund r)
  /-- On the cells of `K` the boundary matrix of `X_r` is the one of `K`, read in
  `ℤ[π₁(X_r)]`. -/
  bdry_old : ∀ r i j, bdry r (genIncl r i) (cellIncl r j)
      = MonoidAlgebra.mapDomainRingHom ℤ (phi r) (b i j)
  /-- A two-cell of `K` is attached along a word in the one-cells of `K`, so its boundary
  has no component along a new one-cell. -/
  bdry_new : ∀ r (a : Gen r), (∀ i, a ≠ genIncl r i) → ∀ j, bdry r a (cellIncl r j) = 0
  /-- **The inclusion `X_r ⊂ X_{r+1}` is zero on `π₂`**, at the level of chains: a cycle of
  the chain complex of the universal cover of `X_r` has zero image in the chain module of
  `X_{r+1}`. -/
  zero_pi2 : ∀ r, r < n → ∀ u : Cell r →₀ MonoidAlgebra ℤ (Fund r),
      (∀ a : Gen r, ∑ c ∈ u.support, u c * bdry r a c = 0) →
      Finsupp.mapDomain (cellStep r)
        (Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ (psi r)) (map_zero _) u) = 0

variable {b} {n : ℕ} {Fund : ℕ → Type u} [∀ r, Group (Fund r)] {Gen Cell : ℕ → Type u}

namespace ChainInput

variable (h : ChainInput b n Fund Gen Cell)

/-- A coefficient vector of `K`, pushed to `ℤ[π₁(X_r)]` and extended by zero over the
two-cells of `X_r` that do not come from `K`. -/
def oldVec (r : ℕ) (v : J →₀ MonoidAlgebra ℤ G) :
    Cell r →₀ MonoidAlgebra ℤ (Fund r) :=
  Finsupp.mapDomain (h.cellIncl r)
    (Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ (h.phi r)) (map_zero _) v)

theorem oldVec_apply_cellIncl (r : ℕ) (v : J →₀ MonoidAlgebra ℤ G) (j : J) :
    h.oldVec r v (h.cellIncl r j) = MonoidAlgebra.mapDomainRingHom ℤ (h.phi r) (v j) :=
  Finsupp.mapDomain_apply_of_injective (h.cellIncl_injective r) _ j

theorem oldVec_support_subset (r : ℕ) [DecidableEq (Cell r)] (v : J →₀ MonoidAlgebra ℤ G) :
    (h.oldVec r v).support ⊆ v.support.image (h.cellIncl r) := by
  refine Finsupp.mapDomain_support.trans ?_
  grind

end ChainInput

end FiniteChains

namespace FiniteChains

open MonoidAlgebra

universe u

variable {G : Type u} [Group G] {I J : Type u}

/-! ### Divisibility of coefficients and reduction along a homomorphism -/

theorem exists_nsmul_mapDomain_iff {A B : Type*} (psi : A → B) (hpsi : Function.Injective psi)
    (m : ℕ) (z : MonoidAlgebra ℤ A) :
    (∃ y : MonoidAlgebra ℤ B, MonoidAlgebra.mapDomain psi z = m • y) ↔
      ∃ y : MonoidAlgebra ℤ A, z = m • y := by
  constructor
  · rintro ⟨y, hy⟩
    rw [← dvd_coeff_iff_nsmul]
    intro q
    have hq : (MonoidAlgebra.mapDomain psi z).coeff (psi q) = z.coeff q := Finsupp.mapDomain_apply_of_injective hpsi z.coeff q
    refine ⟨y.coeff (psi q), ?_⟩
    rw [← hq, hy]
    rw [MonoidAlgebra.coeff_smul_apply, nsmul_eq_mul]
  · simp_all

/-- The reduction of `x ∈ ℤ[G]` along a homomorphism `φ` is divisible by `m` exactly when
the reduction of `x` modulo `ker φ` is: the fibres of `φ` are the cosets of `ker φ`. -/
theorem vanishesModN_ker_iff {H : Type*} [Group H] (φ : G →* H) (m : ℕ)
    (x : MonoidAlgebra ℤ G) :
    VanishesModN m φ.ker x.coeff ↔ ∃ y, MonoidAlgebra.mapDomainRingHom ℤ φ x = m • y := by
  have hfact : MonoidAlgebra.mapDomainRingHom ℤ φ x
      = MonoidAlgebra.mapDomain (QuotientGroup.kerLift φ) (quotRingHom ℤ φ.ker x) := by
    apply MonoidAlgebra.coeff_injective
    change Finsupp.mapDomain _ x.coeff = Finsupp.mapDomain _ (Finsupp.mapDomain _ x.coeff)
    rw [← Finsupp.mapDomain_comp]
    rfl
  rw [vanishesModN_iff_nsmul, hfact,
    exists_nsmul_mapDomain_iff _ (QuotientGroup.kerLift_injective φ)]

/-! ### The lifting of cycles modulo `m` -/

variable {b : I → J → MonoidAlgebra ℤ G} {n : ℕ} {Fund : ℕ → Type u} [∀ r, Group (Fund r)]
  {Gen Cell : ℕ → Type u}

/-- **The input quoted from Hatcher.**  In the chain complex of the universal cover of
`X_r`, every chain whose boundary is divisible by `m` is congruent modulo `m` to a genuine
cycle. -/
def CycleLiftsMod (h : ChainInput b n Fund Gen Cell) (m : ℕ) : Prop :=
  ∀ r : ℕ, r < n → ∀ u : Cell r →₀ MonoidAlgebra ℤ (Fund r),
    (∀ a : Gen r, ∃ w, ∑ c ∈ u.support, u c * h.bdry r a c = m • w) →
      ∃ u' : Cell r →₀ MonoidAlgebra ℤ (Fund r),
        (∀ a : Gen r, ∑ c ∈ u'.support, u' c * h.bdry r a c = 0) ∧
          ∃ z : Cell r →₀ MonoidAlgebra ℤ (Fund r), u = u' + m • z

namespace ChainInput

variable (h : ChainInput b n Fund Gen Cell)

/-- The additive map induced on chains by the inclusion `X_r ⊂ X_{r+1}`. -/
def stepHom (r : ℕ) :
    (Cell r →₀ MonoidAlgebra ℤ (Fund r)) →+ (Cell (r + 1) →₀ MonoidAlgebra ℤ (Fund (r + 1))) :=
  (Finsupp.mapDomain.addMonoidHom (h.cellStep r)).comp
    (Finsupp.mapRange.addMonoidHom (MonoidAlgebra.mapDomainRingHom ℤ (h.psi r)).toAddMonoidHom)

theorem stepHom_apply (r : ℕ) (u : Cell r →₀ MonoidAlgebra ℤ (Fund r)) :
    h.stepHom r u =
      Finsupp.mapDomain (h.cellStep r)
        (Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ (h.psi r)) (map_zero _) u) := rfl

/-- **The extension by zero of a vector whose reduced boundary vanishes modulo `m` is a
cycle modulo `m`.** -/
theorem oldVec_isCycleMod {r : ℕ} (m : ℕ) (v : J →₀ MonoidAlgebra ℤ G)
    (hv : ∀ i : I, VanishesModN m (h.phi r).ker (foxBoundary b v i).coeff) (a : Gen r) :
    ∃ w, ∑ c ∈ (h.oldVec r v).support, h.oldVec r v c * h.bdry r a c = m • w := by
  classical
  set u := h.oldVec r v with hu
  have hsub  := h.oldVec_support_subset r v
  have hext : ∑ c ∈ u.support, u c * h.bdry r a c
      = ∑ c ∈ v.support.image (h.cellIncl r), u c * h.bdry r a c := by
    refine Finset.sum_subset hsub fun c _ hc => ?_
    rw [Finsupp.notMem_support_iff.mp hc, zero_mul]
  have himg : ∑ c ∈ v.support.image (h.cellIncl r), u c * h.bdry r a c
      = ∑ j ∈ v.support, u (h.cellIncl r j) * h.bdry r a (h.cellIncl r j) :=
    Finset.sum_image fun x _ y _ hxy => h.cellIncl_injective r hxy
  rw [hext, himg]
  by_cases hex : ∃ i, a = h.genIncl r i
  · obtain ⟨i, rfl⟩ := hex
    have hterm : ∀ j ∈ v.support,
        u (h.cellIncl r j) * h.bdry r (h.genIncl r i) (h.cellIncl r j)
          = MonoidAlgebra.mapDomainRingHom ℤ (h.phi r) (v j * b i j) := by
      intro j _
      rw [hu, h.oldVec_apply_cellIncl, h.bdry_old, ← map_mul]
    rw [Finset.sum_congr rfl hterm, ← map_sum]
    have hfox : ∑ j ∈ v.support, v j * b i j = foxBoundary b v i := rfl
    rw [hfox]
    exact (vanishesModN_ker_iff (h.phi r) m _).1 (hv i)
  · push_neg at hex
    refine ⟨0, ?_⟩
    rw [smul_zero]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [h.bdry_new r a hex j, mul_zero]

/-- **Formula (2.3) modulo `m`.**  If the reduced Fox boundary of `v` vanishes modulo `m`
at stage `r`, then `v` itself vanishes modulo `m` at stage `r + 1`. -/
theorem vanishesModN_succ {r : ℕ} (m : ℕ) (hlift : CycleLiftsMod h m) (hr : r < n)
    (v : J →₀ MonoidAlgebra ℤ G)
    (hv : ∀ i : I, VanishesModN m (h.phi r).ker (foxBoundary b v i).coeff) (j : J) :
    ∃ y, MonoidAlgebra.mapDomainRingHom ℤ (h.phi (r + 1)) (v j) = m • y := by
  obtain ⟨u', hu'cycle, z, hz⟩ := hlift r hr (h.oldVec r v) (h.oldVec_isCycleMod m v hv)
  have hzero : h.stepHom r u' = 0 := h.zero_pi2 r hr u' hu'cycle
  have hstep : h.stepHom r (h.oldVec r v) = m • h.stepHom r z := by
    rw [hz, map_add, hzero, zero_add, map_nsmul]
  have hcoord := DFunLike.congr_fun hstep (h.cellStep r (h.cellIncl r j))
  rw [stepHom_apply, Finsupp.mapDomain_apply_of_injective (h.cellStep_injective r)] at hcoord
  simp only [Finsupp.mapRange_apply] at hcoord
  rw [h.oldVec_apply_cellIncl, mapDomainRingHom_comp_apply, h.phi_succ] at hcoord
  exact ⟨(h.stepHom r z) (h.cellStep r (h.cellIncl r j)), by
    rw [hcoord]
    rw [Finsupp.smul_apply]⟩

/-- Once a vector has died modulo `m` at some stage, it stays dead at all later stages. -/
theorem vanishesModN_mono {r : ℕ} (m : ℕ) (x : MonoidAlgebra ℤ G)
    (hx : ∃ y, MonoidAlgebra.mapDomainRingHom ℤ (h.phi r) x = m • y) :
    ∀ s, r ≤ s → ∃ y, MonoidAlgebra.mapDomainRingHom ℤ (h.phi s) x = m • y := by
  have key : ∀ d : ℕ, ∃ y, MonoidAlgebra.mapDomainRingHom ℤ (h.phi (r + d)) x = m • y := by
    intro d
    induction d with
    | zero => simpa using hx
    | succ d ih =>
        obtain ⟨y, hy⟩ := ih
        have hstep : MonoidAlgebra.mapDomainRingHom ℤ
            ((h.psi (r + d)).comp (h.phi (r + d))) x
            = m • MonoidAlgebra.mapDomain (h.psi (r + d)) y := by
          rw [← mapDomainRingHom_comp_apply, hy]
          exact map_nsmul ((MonoidAlgebra.mapDomainRingHom ℤ (h.psi (r + d))).toAddMonoidHom) m y
        rw [h.phi_succ] at hstep
        exact ⟨_, hstep⟩
  intro s hs
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
  exact key d

/-- **Formula (2.3) modulo `m`, in the shape of the hypothesis `chain_subgroups`.**  A
requirement modulo `m` violated at stage `r` holds at every later stage. -/
theorem foxSatMod_of_not_foxSatMod (m : ℕ) (hlift : CycleLiftsMod h m)
    (v : J →₀ MonoidAlgebra ℤ G) (r : ℕ) (hviol : ¬ FoxSatMod m b v (h.phi r).ker) :
    ∀ s, r < s → s ≤ n → FoxSatMod m b v (h.phi s).ker := by
  intro s hrs hsn
  have hbdry : ∀ i : I, VanishesModN m (h.phi r).ker (foxBoundary b v i).coeff := by
    by_contra hcon
    exact hviol fun hb => absurd hb hcon
  have hr  := lt_of_lt_of_le hrs hsn
  intro _ j
  have h1 := h.vanishesModN_succ m hlift hr v hbdry j
  exact (vanishesModN_ker_iff (h.phi s) m (v j)).2
    (h.vanishesModN_mono m (v j) h1 s (by omega))

end ChainInput

end FiniteChains

namespace FiniteChains

/-- **The one-violation principle.**

`P r v` reads "stage `r` satisfies requirement `v`".  The hypothesis `hlater`
is formula (2.3) of the paper: if requirement `v` fails at stage `r`, then it
holds at every later stage of the chain.  If at most `m` requirements are
imposed, then one of the `m + 1` stages `0, …, m` satisfies all of them. -/
theorem exists_stage_satisfying_all {ι : Type*} [DecidableEq ι] {m : ℕ}
    (S : Finset ι) (hcard : S.card ≤ m) (P : ℕ → ι → Prop)
    (hlater : ∀ r, ∀ v, ¬ P r v → ∀ s, r < s → s ≤ m → P s v) :
    ∃ r ≤ m, ∀ v ∈ S, P r v := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · exact ⟨0, Nat.zero_le _, by simp⟩
  -- The stages at which some requirement from `S` fails.
  set bad : Finset ℕ :=
    (Finset.range (m + 1)).filter (fun r => ∃ v ∈ S, ¬ P r v) with hbad
  -- Each requirement fails at most once, so `bad` injects into `S`.
  have hbadcard : bad.card ≤ S.card := by
    have hmem : ∀ r ∈ bad, ∃ v ∈ S, ¬ P r v := by
      intro r hr
      simpa [hbad] using (Finset.mem_filter.mp hr).2
    choose w hwS hwP using hmem
    refine Finset.card_le_card_of_injOn (fun r => if h : r ∈ bad then w r h else v₀)
      ?_ ?_
    · intro r hr
      simp at hr
      simp only [Finset.mem_coe, dif_pos hr]
      exact hwS r hr
    · intro r hr s hs hrs
      simp at hr hs
      simp only [dif_pos hr, dif_pos hs] at hrs
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · grind
      · grind
  -- There are `m + 1` stages but at most `m` bad ones.
  have hsub : bad ⊆ Finset.range (m + 1) := Finset.filter_subset _ _
  have : bad ≠ Finset.range (m + 1) := by
    intro h
    have : m + 1 ≤ m := by
      have := hbadcard.trans hcard
      rwa [h, Finset.card_range] at this
    omega
  obtain ⟨r, hr, hrbad⟩ := Finset.exists_of_ssubset (hsub.ssubset_of_ne this)
  refine ⟨r, by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hr, ?_⟩
  intro v hv
  by_contra hP
  exact hrbad (Finset.mem_filter.mpr ⟨hr, ⟨v, hv, hP⟩⟩)

end FiniteChains

namespace FiniteChains

open MonoidAlgebra

universe u

variable {G : Type u} [Group G] {I J : Type u}

/-- **Condition (1) at cell level, with the lifting of cycles modulo every `m`.**  For
every `n` the chain `K = X₀ ⊂ ⋯ ⊂ Xₙ` supplies the data of `ChainInput` together with the
property that a cycle which becomes divisible by `m` lifts to a chain divisible by `m`. -/
def HasCellChainsLift (b : I → J → MonoidAlgebra ℤ G) : Prop :=
  ∀ n : ℕ, ∃ (Fund : ℕ → Type u) (_ : ∀ r, Group (Fund r)) (Gen Cell : ℕ → Type u)
    (h : ChainInput b n Fund Gen Cell), ∀ m : ℕ, CycleLiftsMod h m

variable {b : I → J → MonoidAlgebra ℤ G}

/-- The index set of the requirements (2.2): a coefficient vector together with either `0`
(the integral requirement) or a prime `p` (the requirement modulo `p`). -/
abbrev ReqIndex (G : Type u) [Group G] (J : Type u) : Type u :=
  (J →₀ MonoidAlgebra ℤ G) × {m : ℕ // m = 0 ∨ m.Prime}

/-- The requirement attached to an index. -/
def SatIndex (b : I → J → MonoidAlgebra ℤ G) (N : Subgroup G) (vm : ReqIndex G J) : Prop :=
  FoxSatMod vm.2.1 b vm.1 N

/-- **Steps 1–2 of Section 2, with the full family of requirements.**  Any finite family of
requirements is satisfied by a single normal subgroup of `G`. -/
theorem exists_normal_forall_finset_mod (hchains : HasCellChainsLift b)
    (S : Finset (ReqIndex G J)) :
    ∃ N : Subgroup G, N.Normal ∧ ∀ vm ∈ S, SatIndex b N vm := by
  classical
  obtain ⟨Fund, inst, Gen, Cell, h, hlift⟩ := hchains S.card
  letI := inst
  obtain ⟨r, -, hr⟩ :=
    exists_stage_satisfying_all S le_rfl (fun r vm => SatIndex b (h.phi r).ker vm)
      (fun r vm hv s hrs hsn =>
        h.foxSatMod_of_not_foxSatMod vm.2.1 (hlift vm.2.1) vm.1 r hv s hrs hsn)
  exact ⟨(h.phi r).ker, inferInstance, hr⟩

/-- **The conclusion of Section 2, with the full family of requirements.**  From the cell
data of chains of every length one obtains a perfect normal subgroup of `G` satisfying all
the requirements (2.2), integrally and modulo every prime.  The only hypothesis besides the
chains is the torsion freeness of `N/[N, N]` for subgroups satisfying the requirements
modulo every prime — the universal-coefficient/Hurewicz input of Section 2. -/
theorem exists_perfect_normal_foxSatMod (hchains : HasCellChainsLift b)
    (hfin : ∀ v : J →₀ MonoidAlgebra ℤ G, {i : I | foxBoundary b v i ≠ 0}.Finite)
    (hcol : ∀ j, {i : I | b i j ≠ 0}.Finite)
    (htf : ∀ (N : Subgroup G) [N.Normal],
      (∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N) →
        IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆))) :
    ∃ N : Subgroup G, N.Normal ∧
      (∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N) ∧
      (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) ∧ ⁅N, N⁆ = N := by
  have hdet : FinitelyDetermined (SatIndex b) := fun vm =>
    foxSatMod_finitelyDetermined vm.2.1 b vm.1 (hfin vm.1)
  -- compactness
  obtain ⟨M, hMnormal, hM⟩ :=
    exists_normal_subgroup_forall (SatIndex b) hdet (exists_normal_forall_finset_mod hchains)
  -- a minimal normal subgroup satisfying all the requirements
  obtain ⟨N, -, hNnormal, hN, hNmin⟩ :=
    exists_minimal_normal_sat (fun N => ∀ vm : ReqIndex G J, SatIndex b N vm)
      (fun C hchain hne hC =>
        sat_sInf_of_finitelyDetermined (SatIndex b) hdet hchain hne
          (fun N hNmem => (hC N hNmem).2))
      M hMnormal hM
  haveI := hNnormal
  have hmod  :=
    fun p hp v => hN (v, ⟨p, Or.inr hp⟩)
  have hint  :=
    fun v => (foxSatMod_zero_iff b v N).1 (hN (v, ⟨0, Or.inl rfl⟩))
  haveI := htf N hmod
  -- Lemma 2.1: the requirements pass to the commutator subgroup
  have hsatcomm : ∀ vm : ReqIndex G J, SatIndex b ⁅N, N⁆ vm := by
    rintro ⟨v, m, hm⟩
    rcases hm with rfl | hp
    · exact (foxSatMod_zero_iff b v ⁅N, N⁆).2 (foxSat_commutator b hcol N hint v)
    · haveI := Fact.mk hp
      exact foxSatMod_commutator m b hcol N (fun w => hmod m hp w) v
  have hcomm : (⁅N, N⁆).Normal := inferInstance
  exact ⟨N, hNnormal, hmod, hint,
    hNmin ⁅N, N⁆ (Subgroup.commutator_le_left N N) hcomm hsatcomm⟩

end FiniteChains

namespace FiniteChains

/-- A Fox derivative has finite support in the generator index even when the generator
type is infinite: a free-group element contains only finitely many letters. -/
theorem fox_generator_support_finite {α : Type*} [DecidableEq α] (w : FreeGroup α) :
    {i : α | fox i w ≠ 0}.Finite := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of k => simp
  | inv_of k hk =>
      apply hk.subset
      intro i hi
      by_contra hz
      simp only [Set.mem_setOf_eq, not_not] at hz
      rw [Set.mem_setOf_eq, fox_inv, hz, mul_zero, neg_zero] at hi
      exact hi rfl
  | mul a b ha hb =>
      apply (ha.union hb).subset
      intro i hi
      by_contra hz
      simp at hz
      simp [fox_mul, hz.1, hz.2] at hi

variable {G I J : Type*} [Group G] (b : I → J → MonoidAlgebra ℤ G)

/-- A finite chain has finite boundary whenever each individual cell has finite boundary. -/
theorem foxBoundary_support_finite
    (hcol : ∀ j, {i : I | b i j ≠ 0}.Finite) (v : J →₀ MonoidAlgebra ℤ G) :
    {i : I | foxBoundary b v i ≠ 0}.Finite := by
  apply (v.support.finite_toSet.biUnion (fun j _ => hcol j)).subset
  intro i hi
  simp at hi
  simp only [Set.mem_iUnion, Finset.mem_coe]
  by_contra h
  apply hi
  unfold foxBoundary
  apply Finset.sum_eq_zero
  intro j hj
  have hz : b i j = 0 := by
    by_contra hn
    exact h ⟨j, hj, hn⟩
  rw [hz, mul_zero]

section Compactness

universe u

/-- Section 2's algebraic compactness conclusion for arbitrarily many cells. Only the
boundary of an individual cell must be finite; no finiteness assumption is imposed on
either cell-index type. -/
theorem exists_perfect_normal_foxSatMod_of_finite_columns
    {G I J : Type u} [Group G] (b : I → J → MonoidAlgebra ℤ G)
    (hchains : HasCellChainsLift b)
    (hcol : ∀ j, {i : I | b i j ≠ 0}.Finite)
    (htf : ∀ (N : Subgroup G) [N.Normal],
      (∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N) →
        IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆))) :
    ∃ N : Subgroup G, N.Normal ∧
      (∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N) ∧
      (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) ∧ ⁅N, N⁆ = N :=
  exists_perfect_normal_foxSatMod hchains (foxBoundary_support_finite b hcol) hcol htf

end Compactness

end FiniteChains

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]
variable {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

variable {Nsub ρ}

omit [Fintype α] in
/-- A `ℤ[Q]`-multiple of the Fox vector of an element of a normal subgroup `P ≤ Ñ` is again
the Fox vector of an element of `P`. -/
theorem exists_mem_smul_foxVec {P : Subgroup (FreeGroup α)} [P.Normal] (hP : P ≤ Nsub)
    {r : FreeGroup α} (hr : r ∈ P) (x : CoverRing Nsub) :
    ∃ w ∈ P, x • foxVec Nsub r = foxVec Nsub w := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | add x₁ x₂ h₁ h₂ =>
      obtain ⟨w₁, hw₁, e₁⟩ := h₁
      obtain ⟨w₂, hw₂, e₂⟩ := h₂
      exact ⟨w₁ * w₂, Subgroup.mul_mem _ hw₁ hw₂, by
        rw [foxVec_mul (hP hw₁), ← e₁, ← e₂, add_smul]⟩
  | single q n =>
      obtain ⟨f, rfl⟩ := Quotient.exists_rep q
      have hconj  := Subgroup.Normal.conj_mem ‹P.Normal› r hr f
      refine ⟨(f * r * f⁻¹) ^ n, Subgroup.zpow_mem _ hconj n, ?_⟩
      have hsingle : (single (QuotientGroup.mk f) n)
          = n • proj Nsub (grp f) := by
        rw [proj_grp, qgrp, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rw [foxVec_zpow (hP hconj) n, foxVec_conj (hP hr),
        hsingle, smul_assoc]

variable (Nsub ρ)

end FiniteChains

namespace FiniteChains

open FreeGroup

variable {α : Type*} (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]

/-- The lengths of the words representing the coset `q`. -/
def cosetLengths (q : FreeGroup α ⧸ Nsub) : Set ℕ :=
  {n | ∃ L : List (α × Bool), L.length = n ∧
    (QuotientGroup.mk (FreeGroup.mk L) : FreeGroup α ⧸ Nsub) = q}

/-- The length of a shortest word representing the coset `q`. -/
def clen (q : FreeGroup α ⧸ Nsub) : ℕ := sInf (cosetLengths Nsub q)


omit [Nsub.Normal] in
theorem clen_mem (q : FreeGroup α ⧸ Nsub) : clen Nsub q ∈ cosetLengths Nsub q :=
  Nat.sInf_mem (by
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective (s := Nsub) q
    obtain ⟨L, rfl⟩ := Quot.exists_rep w
    exact ⟨L.length, L, rfl, rfl⟩)

omit [Nsub.Normal] in
theorem clen_le {q : FreeGroup α ⧸ Nsub} {L : List (α × Bool)}
    (h : (QuotientGroup.mk (FreeGroup.mk L) : FreeGroup α ⧸ Nsub) = q) :
    clen Nsub q ≤ L.length :=
  Nat.sInf_le ⟨L, rfl, h⟩

theorem clen_eq_zero_iff {q : FreeGroup α ⧸ Nsub} : clen Nsub q = 0 ↔ q = 1 := by
  constructor
  · intro h
    obtain ⟨L, hL, hLq⟩ := clen_mem Nsub q
    rw [h, List.length_eq_zero_iff] at hL
    subst hL
    rw [← hLq, ← FreeGroup.one_eq_mk, QuotientGroup.mk_one]
  · rintro rfl
    have : clen Nsub 1 ≤ [].length :=
      clen_le Nsub (by
        rfl)
    simpa using this

/-- Every nontrivial coset is obtained from a coset of smaller minimal length by
appending one letter. -/
theorem exists_parent {q : FreeGroup α ⧸ Nsub} (h : clen Nsub q ≠ 0) :
    ∃ py : (FreeGroup α ⧸ Nsub) × (α × Bool),
      clen Nsub py.1 + 1 = clen Nsub q ∧
        py.1 * (QuotientGroup.mk (FreeGroup.mk [py.2]) : FreeGroup α ⧸ Nsub) = q := by
  obtain ⟨L, hL, hLq⟩ := clen_mem Nsub q
  rcases List.eq_nil_or_concat L with rfl | ⟨L', y, rfl⟩
  · simp_all
  · rw [List.concat_eq_append] at hL hLq
    refine ⟨⟨QuotientGroup.mk (FreeGroup.mk L'), y⟩, ?_, ?_⟩
    · have hmul : (QuotientGroup.mk (FreeGroup.mk L')) *
          (QuotientGroup.mk (FreeGroup.mk [y])) = q := by
        rw [← QuotientGroup.mk_mul]
        rw [show FreeGroup.mk L' * FreeGroup.mk [y] = FreeGroup.mk (L' ++ [y]) from rfl]
        exact hLq
      have hup : clen Nsub (QuotientGroup.mk (FreeGroup.mk L')) ≤ L'.length :=
        clen_le Nsub rfl
      have hdown : clen Nsub q ≤ clen Nsub (QuotientGroup.mk (FreeGroup.mk L')) + 1 := by
        obtain ⟨M, hM, hMq⟩ := clen_mem Nsub (QuotientGroup.mk (FreeGroup.mk L'))
        have : (QuotientGroup.mk (FreeGroup.mk (M ++ [y]))) = q := by
          rw [show FreeGroup.mk (M ++ [y]) = FreeGroup.mk M * FreeGroup.mk [y] from rfl,
            QuotientGroup.mk_mul, hMq, hmul]
        have := clen_le Nsub this
        simpa [hM] using this
      have hlen : (L' ++ [y]).length = L'.length + 1 := by simp
      have hp : clen Nsub (QuotientGroup.mk (FreeGroup.mk L')) + 1 = clen Nsub q := by omega
      exact hp
    · rw [← QuotientGroup.mk_mul]
      rw [show FreeGroup.mk L' * FreeGroup.mk [y] = FreeGroup.mk (L' ++ [y]) from rfl]
      exact hLq

/-- The parent coset and the last letter chosen for a nontrivial coset. -/
def parentData {q : FreeGroup α ⧸ Nsub} (h : clen Nsub q ≠ 0) :
    (FreeGroup α ⧸ Nsub) × (α × Bool) :=
  (exists_parent Nsub h).choose

theorem parentData_clen {q : FreeGroup α ⧸ Nsub} (h : clen Nsub q ≠ 0) :
    clen Nsub (parentData Nsub h).1 + 1 = clen Nsub q :=
  (exists_parent Nsub h).choose_spec.1

theorem parentData_mul {q : FreeGroup α ⧸ Nsub} (h : clen Nsub q ≠ 0) :
    (parentData Nsub h).1 *
      (QuotientGroup.mk (FreeGroup.mk [(parentData Nsub h).2]) : FreeGroup α ⧸ Nsub) = q :=
  (exists_parent Nsub h).choose_spec.2


/-- The chosen representative of a coset: the Schreier transversal. -/
def rep (q : FreeGroup α ⧸ Nsub) : FreeGroup α :=
  if h : clen Nsub q = 0 then 1
  else rep (parentData Nsub h).1 * FreeGroup.mk [(parentData Nsub h).2]
termination_by clen Nsub q
decreasing_by exact (by
  have := parentData_clen Nsub h
  omega)

theorem rep_of_clen_eq_zero {q : FreeGroup α ⧸ Nsub} (h : clen Nsub q = 0) : rep Nsub q = 1 := by
  rw [rep]
  simp [h]

@[simp] theorem rep_one : rep Nsub (1 : FreeGroup α ⧸ Nsub) = 1 :=
  rep_of_clen_eq_zero Nsub ((clen_eq_zero_iff Nsub).2 rfl)

/-- The recursive shape of the representatives: a nontrivial representative is a shorter
representative followed by one letter. -/
theorem rep_mul_letter {q : FreeGroup α ⧸ Nsub} (h : clen Nsub q ≠ 0) :
    rep Nsub q = rep Nsub (parentData Nsub h).1 * FreeGroup.mk [(parentData Nsub h).2] := by
  rw [rep]
  simp [h]

/-- The chosen representative does represent the coset. -/
@[simp] theorem mk_rep (q : FreeGroup α ⧸ Nsub) :
    (QuotientGroup.mk (rep Nsub q) : FreeGroup α ⧸ Nsub) = q := by
  have key : ∀ n : ℕ, ∀ q : FreeGroup α ⧸ Nsub, clen Nsub q ≤ n →
      (QuotientGroup.mk (rep Nsub q)) = q := by
    intro n
    induction n with
    | zero =>
        intro q hq
        have h  := Nat.le_zero.1 hq
        rw [rep_of_clen_eq_zero Nsub h, (clen_eq_zero_iff Nsub).1 h]
        rfl
    | succ n ih =>
        intro q hq
        by_cases h : clen Nsub q = 0
        · simp_all
        · have hlt := parentData_clen Nsub h
          rw [rep_mul_letter Nsub h, QuotientGroup.mk_mul,
            ih (parentData Nsub h).1 (by omega), parentData_mul Nsub h]
  exact key (clen Nsub q) q le_rfl

/-- The Schreier transversal. -/
def repSet : Set (FreeGroup α) := Set.range (rep Nsub)

theorem rep_mem_repSet (q : FreeGroup α ⧸ Nsub) : rep Nsub q ∈ repSet Nsub := ⟨q, rfl⟩

theorem rep_mk_of_mem {t : FreeGroup α} (ht : t ∈ repSet Nsub) :
    rep Nsub (QuotientGroup.mk t) = t := by
  obtain ⟨q, rfl⟩ := ht
  rw [mk_rep]

/-- Distinct elements of the transversal lie in distinct cosets. -/
theorem eq_of_mk_eq {t t' : FreeGroup α} (ht : t ∈ repSet Nsub) (ht' : t' ∈ repSet Nsub)
    (h : (QuotientGroup.mk t : FreeGroup α ⧸ Nsub) = QuotientGroup.mk t') : t = t' := by
  rw [← rep_mk_of_mem Nsub ht, ← rep_mk_of_mem Nsub ht', h]

/-! ### The Schreier generators -/

/-- The Schreier generator attached to a transversal element `t` and a generator `x`. -/
def schreierGen (t : FreeGroup α) (x : α) : FreeGroup α :=
  t * FreeGroup.of x * (rep Nsub (QuotientGroup.mk (t * FreeGroup.of x)))⁻¹

theorem schreierGen_mem (t : FreeGroup α) (x : α) : schreierGen Nsub t x ∈ Nsub := by
  rw [← QuotientGroup.eq_one_iff]
  rw [schreierGen, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_rep]
  group

/-- The set of Schreier generators. -/
def schreierSet : Set (FreeGroup α) :=
  Set.range fun p : (FreeGroup α ⧸ Nsub) × α => schreierGen Nsub (rep Nsub p.1) p.2


/-- The rewriting process: for every word `w`, the element `w · rep(w)⁻¹` is a product of
Schreier generators. -/
theorem mul_inv_rep_mem_closure (w : FreeGroup α) :
    w * (rep Nsub (QuotientGroup.mk w))⁻¹ ∈ Subgroup.closure (schreierSet Nsub) := by
  obtain ⟨L, rfl⟩ := Quot.exists_rep w
  induction L using List.reverseRecOn with
  | nil =>
      show FreeGroup.mk [] *
        (rep Nsub (QuotientGroup.mk (FreeGroup.mk [])))⁻¹ ∈ _
      have h1 : (FreeGroup.mk ([] : List (α × Bool))) = 1 := rfl
      rw [h1]
      simp
  | append_singleton L' y ih =>
      have hsplit : FreeGroup.mk (L' ++ [y]) = FreeGroup.mk L' * FreeGroup.mk [y] := rfl
      set w' : FreeGroup α := FreeGroup.mk L' with hw'
      set t : FreeGroup α := rep Nsub (QuotientGroup.mk w') with ht
      have htmem : t ∈ repSet Nsub := rep_mem_repSet Nsub _
      have hmkt : (QuotientGroup.mk t : FreeGroup α ⧸ Nsub) = QuotientGroup.mk w' := by
        rw [ht, mk_rep]
      have hmk : (QuotientGroup.mk (w' * FreeGroup.mk [y]) : FreeGroup α ⧸ Nsub)
          = QuotientGroup.mk (t * FreeGroup.mk [y]) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hmkt]
      -- the one-letter step
      have hstep : t * FreeGroup.mk [y] *
          (rep Nsub (QuotientGroup.mk (t * FreeGroup.mk [y])))⁻¹
            ∈ Subgroup.closure (schreierSet Nsub) := by
        obtain ⟨x, b⟩ := y
        cases b with
        | true =>
            have hof : FreeGroup.mk [(x, true)] = FreeGroup.of x := rfl
            rw [hof]
            obtain ⟨q, hq⟩ := htmem
            refine Subgroup.subset_closure ⟨⟨q, x⟩, ?_⟩
            show schreierGen Nsub (rep Nsub q) x = _
            rw [hq, schreierGen]
        | false =>
            have hof : FreeGroup.mk [(x, false)] = (FreeGroup.of x)⁻¹ :=
              inv_eq_iff_eq_inv.mp rfl
            rw [hof]
            set t' : FreeGroup α := rep Nsub (QuotientGroup.mk (t * (FreeGroup.of x)⁻¹)) with ht'
            have hmkt' : (QuotientGroup.mk (t' * FreeGroup.of x) : FreeGroup α ⧸ Nsub)
                = QuotientGroup.mk t := by
              rw [QuotientGroup.mk_mul, ht', mk_rep, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
              group
            have hrep : rep Nsub (QuotientGroup.mk (t' * FreeGroup.of x)) = t := by
              rw [hmkt', rep_mk_of_mem Nsub htmem]
            have hgen : schreierGen Nsub t' x = t' * FreeGroup.of x * t⁻¹ := by
              rw [schreierGen, hrep]
            have hmem : schreierGen Nsub t' x ∈ Subgroup.closure (schreierSet Nsub) := by
              refine Subgroup.subset_closure ⟨⟨QuotientGroup.mk (t * (FreeGroup.of x)⁻¹), x⟩, ?_⟩
              show schreierGen Nsub (rep Nsub (QuotientGroup.mk (t * (FreeGroup.of x)⁻¹))) x
                  = schreierGen Nsub t' x
              rw [ht']
            have : t * (FreeGroup.of x)⁻¹ * t'⁻¹ = (schreierGen Nsub t' x)⁻¹ := by
              rw [hgen]; group
            rw [this]
            exact Subgroup.inv_mem _ hmem
      have hprod : FreeGroup.mk (L' ++ [y]) *
          (rep Nsub (QuotientGroup.mk (FreeGroup.mk (L' ++ [y]))))⁻¹
          = (w' * (rep Nsub (QuotientGroup.mk w'))⁻¹) *
            (t * FreeGroup.mk [y] *
              (rep Nsub (QuotientGroup.mk (t * FreeGroup.mk [y])))⁻¹) := by
        rw [hsplit, hmk, ← ht]
        group
      show FreeGroup.mk (L' ++ [y]) *
          (rep Nsub (QuotientGroup.mk (FreeGroup.mk (L' ++ [y]))))⁻¹ ∈ _
      rw [hprod]
      exact Subgroup.mul_mem _ ih hstep

/-- **The Schreier generators generate `Ñ`.** -/
theorem closure_schreierGen : Subgroup.closure (schreierSet Nsub) = Nsub := by
  refine le_antisymm (by
    rw [Subgroup.closure_le]
    rintro _ ⟨p, rfl⟩
    exact schreierGen_mem Nsub _ _) ?_
  intro w hw
  have hmk  := (QuotientGroup.eq_one_iff w).2 hw
  have := mul_inv_rep_mem_closure Nsub w
  rwa [hmk, rep_one, inv_one, mul_one] at this

end FiniteChains

namespace FiniteChains

open MonoidAlgebra FreeGroup

variable {α : Type*} [DecidableEq α] (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]

/-! ### Elementary computations with Fox vectors -/

omit [DecidableEq α] in
theorem qgrp_mul (u v : FreeGroup α) :
    qgrp Nsub (u * v) = qgrp Nsub u * qgrp Nsub v := by simp_all [qgrp, MonoidAlgebra.single_mul_single, QuotientGroup.mk_mul, mul_one]

/-- The coefficient of the coset of `s` in an element of `ℤ[Q]`. -/
def coefAt (s : FreeGroup α) (z : CoverRing Nsub) : ℤ :=
  z.coeff (QuotientGroup.mk s : FreeGroup α ⧸ Nsub)

omit [DecidableEq α] in
@[simp] theorem coefAt_zero (s : FreeGroup α) : coefAt Nsub s 0 = 0 := rfl

omit [DecidableEq α] in
theorem coefAt_add (s : FreeGroup α) (z w : CoverRing Nsub) :
    coefAt Nsub s (z + w) = coefAt Nsub s z + coefAt Nsub s w := rfl

omit [DecidableEq α] in
omit [Nsub.Normal] in
theorem coefAt_neg (s : FreeGroup α) (z : CoverRing Nsub) :
    coefAt Nsub s (-z) = -coefAt Nsub s z := rfl

omit [DecidableEq α] in
theorem coefAt_sub (s : FreeGroup α) (z w : CoverRing Nsub) :
    coefAt Nsub s (z - w) = coefAt Nsub s z - coefAt Nsub s w := rfl

omit [DecidableEq α] in
omit [Nsub.Normal] in
theorem coefAt_qgrp_self (u : FreeGroup α) : coefAt Nsub u (qgrp Nsub u) = 1 :=
  Finsupp.single_eq_same

omit [DecidableEq α] in
omit [Nsub.Normal] in
theorem coefAt_qgrp_of_ne {s u : FreeGroup α}
    (h : (QuotientGroup.mk u : FreeGroup α ⧸ Nsub) ≠ QuotientGroup.mk s) :
    coefAt Nsub s (qgrp Nsub u) = 0 :=
  Finsupp.single_eq_of_ne (Ne.symm h)

/-- The product rule for Fox vectors, valid for arbitrary words. -/
theorem foxVec_mul' (u v : FreeGroup α) (x : α) :
    foxVec Nsub (u * v) x = foxVec Nsub u x + qgrp Nsub u * foxVec Nsub v x := by
  show proj Nsub (fox x (u * v)) = proj Nsub (fox x u) + qgrp Nsub u * proj Nsub (fox x v)
  rw [fox_mul, map_add, _root_.map_mul (proj Nsub), proj_grp]

/-- The rule for inverses, valid for arbitrary words. -/
theorem foxVec_inv' (u : FreeGroup α) (x : α) :
    foxVec Nsub u⁻¹ x = -(qgrp Nsub u⁻¹ * foxVec Nsub u x) := by
  show proj Nsub (fox x u⁻¹) = -(qgrp Nsub u⁻¹ * proj Nsub (fox x u))
  rw [fox_inv, map_neg, _root_.map_mul (proj Nsub), proj_grp]

@[simp] theorem foxVec_of (x y : α) :
    foxVec Nsub (FreeGroup.of y) x = if x = y then 1 else 0 := by
  show proj Nsub (fox x (FreeGroup.of y)) = _
  simp

/-! ### Triangularity of the Fox vectors of the Schreier generators -/

/-- **Claim A.**  The Fox derivative of a transversal element only involves basis elements
`π(s)·e_x` coming from pairs with `s ∈ T` *and* `s·x ∈ T`. -/
theorem coefAt_foxVec_rep (q : FreeGroup α ⧸ Nsub) {s : FreeGroup α} (hs : s ∈ repSet Nsub)
    (x : α) (hsx : s * FreeGroup.of x ∉ repSet Nsub) :
    coefAt Nsub s (foxVec Nsub (rep Nsub q) x) = 0 := by
  have key : ∀ n : ℕ, ∀ q : FreeGroup α ⧸ Nsub, clen Nsub q ≤ n →
      coefAt Nsub s (foxVec Nsub (rep Nsub q) x) = 0 := by
    intro n
    induction n with
    | zero =>
        intro q hq
        rw [rep_of_clen_eq_zero Nsub (Nat.le_zero.1 hq), foxVec_one]
        rfl
    | succ n ih =>
        intro q hq
        by_cases h : clen Nsub q = 0
        · simp_all
        · have hlt := parentData_clen Nsub h
          have hIH : coefAt Nsub s (foxVec Nsub (rep Nsub (parentData Nsub h).1) x) = 0 :=
            ih _ (by omega)
          set t' := rep Nsub (parentData Nsub h).1 with ht'
          have ht'mem : t' ∈ repSet Nsub := rep_mem_repSet Nsub _
          have hstep := rep_mul_letter Nsub h
          rw [← ht'] at hstep
          rcases hy : (parentData Nsub h).2 with ⟨y, b⟩
          rw [hy] at hstep
          cases b with
          | true =>
              have hqrep : rep Nsub q = t' * FreeGroup.of y := hstep
              rw [hqrep, foxVec_mul' Nsub, coefAt_add, hIH, zero_add]
              by_cases hxy : x = y
              · subst hxy
                rw [foxVec_of, if_pos rfl, mul_one]
                by_cases hst : (QuotientGroup.mk t' : FreeGroup α ⧸ Nsub) = QuotientGroup.mk s
                · exfalso
                  have hts  := eq_of_mk_eq Nsub hs ht'mem hst.symm
                  rw [hts] at hsx
                  exact hsx (by rw [← hqrep]; exact rep_mem_repSet Nsub q)
                · exact coefAt_qgrp_of_ne Nsub hst
              · rw [foxVec_of, if_neg hxy, mul_zero]
                exact coefAt_zero Nsub s
          | false =>
              have hqrep : rep Nsub q = t' * (FreeGroup.of y)⁻¹ := hstep
              rw [hqrep, foxVec_mul' Nsub, coefAt_add, hIH, zero_add]
              by_cases hxy : x = y
              · subst hxy
                rw [foxVec_inv' Nsub, foxVec_of, if_pos rfl, mul_one, mul_neg, ← qgrp_mul,
                  coefAt_neg]
                by_cases hst : (QuotientGroup.mk (t' * (FreeGroup.of x)⁻¹) :
                    FreeGroup α ⧸ Nsub) = QuotientGroup.mk s
                · exfalso
                  have hmem : t' * (FreeGroup.of x)⁻¹ ∈ repSet Nsub := by
                    rw [← hqrep]; exact rep_mem_repSet Nsub q
                  have hts : s = t' * (FreeGroup.of x)⁻¹ := eq_of_mk_eq Nsub hs hmem hst.symm
                  rw [hts] at hsx
                  refine hsx ?_
                  rw [inv_mul_cancel_right]
                  exact ht'mem
                · rw [coefAt_qgrp_of_ne Nsub hst, neg_zero]
              · rw [foxVec_inv' Nsub, foxVec_of, if_neg hxy, mul_zero, neg_zero, mul_zero]
                exact coefAt_zero Nsub s
  exact key (clen Nsub q) q le_rfl

/-- **Claim B.**  Triangularity of the Fox vectors of the Schreier generators: at the
"leading" coefficient of its own Schreier pair a generator has coefficient `1`, and at the
leading coefficient of any other Schreier pair it has coefficient `0`. -/
theorem coefAt_foxVec_schreierGen {t : FreeGroup α} (ht : t ∈ repSet Nsub) (y : α)
    {s : FreeGroup α} (hs : s ∈ repSet Nsub) (x : α) (hsx : s * FreeGroup.of x ∉ repSet Nsub) :
    coefAt Nsub s (foxVec Nsub (schreierGen Nsub t y) x)
      = if s = t ∧ x = y then 1 else 0 := by
  obtain ⟨qt, rfl⟩ := ht
  set t := rep Nsub qt with ht
  set u := rep Nsub (QuotientGroup.mk (t * FreeGroup.of y)) with hu
  have hprod : schreierGen Nsub t y = t * FreeGroup.of y * u⁻¹ := rfl
  have hone : qgrp Nsub (t * FreeGroup.of y * u⁻¹) = 1 :=
    qgrp_eq_one_of_mem Nsub (schreierGen_mem Nsub t y)
  have hexp : foxVec Nsub (schreierGen Nsub t y) x
      = foxVec Nsub t x + qgrp Nsub t * foxVec Nsub (FreeGroup.of y) x
        - foxVec Nsub u x := by
    rw [hprod, foxVec_mul' Nsub, foxVec_mul' Nsub, foxVec_inv' Nsub]
    rw [mul_neg, ← mul_assoc, ← qgrp_mul, hone, one_mul, ← sub_eq_add_neg]
  rw [hexp, coefAt_sub, coefAt_add]
  rw [coefAt_foxVec_rep Nsub qt hs x hsx, coefAt_foxVec_rep Nsub _ hs x hsx, zero_add, sub_zero]
  by_cases hxy : x = y
  · subst hxy
    rw [foxVec_of, if_pos rfl, mul_one]
    by_cases hst : s = t
    · subst hst
      rw [coefAt_qgrp_self, if_pos ⟨rfl, rfl⟩]
    · have hne : (QuotientGroup.mk t) ≠ QuotientGroup.mk s := fun hq =>
        hst (eq_of_mk_eq Nsub hs ⟨qt, rfl⟩ hq.symm)
      rw [coefAt_qgrp_of_ne Nsub hne, if_neg (by tauto)]
  · simp_all

/-! ### The Schreier generators of the proper pairs -/

omit [DecidableEq α] in
/-- A Schreier generator attached to a pair with `t·x ∈ T` is trivial. -/
theorem schreierGen_eq_one {t : FreeGroup α} (x : α)
    (h : t * FreeGroup.of x ∈ repSet Nsub) : schreierGen Nsub t x = 1 := by
  rw [schreierGen, rep_mk_of_mem Nsub h, mul_inv_cancel]

/-- The Schreier generators attached to the pairs `(t, x)` with `t ∈ T` and `t·x ∉ T`; the
remaining Schreier generators are trivial. -/
def properSchreierSet : Set (FreeGroup α) :=
  {g | ∃ (q : FreeGroup α ⧸ Nsub) (x : α),
    rep Nsub q * FreeGroup.of x ∉ repSet Nsub ∧ g = schreierGen Nsub (rep Nsub q) x}

omit [DecidableEq α] in
theorem properSchreierSet_subset : properSchreierSet Nsub ⊆ (Nsub : Set (FreeGroup α)) := by
  rintro g ⟨q, x, -, rfl⟩
  exact schreierGen_mem Nsub _ _


/-! ### A triangularity criterion in an abelian group -/

/-- If an abelian group is generated by a family `g` and carries functionals `c` with
`c i (g j) = δ_{ij}`, then an element killed by all the functionals is zero. -/
theorem eq_zero_of_forall_coefHom {M : Type*} [AddCommGroup M] {Idx : Type*} (g : Idx → M)
    (hgen : ∀ a : M, a ∈ AddSubgroup.closure (Set.range g))
    (c : Idx → (M →+ ℤ)) (hdiag : ∀ i, c i (g i) = 1)
    (hoff : ∀ i j, j ≠ i → c i (g j) = 0)
    {a : M} (ha : ∀ i, c i a = 0) : a = 0 := by
  classical
  have key : ∀ b ∈ AddSubgroup.closure (Set.range g),
      ∃ d : Idx →₀ ℤ, b = d.sum fun i n => n • g i := by
    intro b hb
    induction hb using AddSubgroup.closure_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact ⟨Finsupp.single i 1, by simp⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ ihx ihy =>
        obtain ⟨d₁, h₁⟩ := ihx
        obtain ⟨d₂, h₂⟩ := ihy
        refine ⟨d₁ + d₂, ?_⟩
        rw [h₁, h₂, Finsupp.sum_add_index' (by simp) (fun i n m => by rw [add_smul])]
    | neg x _ ih =>
        obtain ⟨d, hd⟩ := ih
        refine ⟨-d, ?_⟩
        rw [hd, Finsupp.sum_neg_index (by simp)]
        simp [neg_smul, Finsupp.sum_neg]
  obtain ⟨d, rfl⟩ := key a (hgen a)
  have hd : ∀ i, d i = 0 := by
    intro i
    have h0 := ha i
    rw [map_finsuppSum] at h0
    have hterm : ∀ j : Idx, ∀ n : ℤ, c i (n • g j) = if j = i then n else 0 := by
      intro j n
      rw [map_zsmul]
      by_cases hji : j = i
      · simp_all
      · simp_all
    rw [Finsupp.sum_congr (g2 := fun j n => if j = i then n else 0)
      (fun j _ => hterm j (d j))] at h0
    rw [Finsupp.sum_ite_eq' d i (fun _ n => n)] at h0
    by_cases hi : i ∈ d.support
    · simp_all
    · simp_all
  have hzero : d = 0 := Finsupp.ext hd
  rw [hzero]
  simp

/-! ### The Fox vector map on `Ñ` and its kernel -/

/-- The Fox vector map, as a homomorphism on `Ñ`. -/
def foxHomNsub : Nsub →* Multiplicative (α → CoverRing Nsub) where
  toFun w := Multiplicative.ofAdd (foxVec Nsub (w : FreeGroup α))
  map_one' := rfl

  map_mul' := fun a b => by
    show Multiplicative.ofAdd (foxVec Nsub ((a : FreeGroup α) * (b : FreeGroup α))) = _
    rw [foxVec_mul a.2]
    rfl

/-- The Fox vector map on the abelianization of `Ñ`. -/
def foxAb : Abelianization Nsub →* Multiplicative (α → CoverRing Nsub) :=
  Abelianization.lift (foxHomNsub Nsub)

/-- The Fox vector map on the abelianization of `Ñ`, written additively. -/
def foxAbAdd : Additive (Abelianization Nsub) →+ (α → CoverRing Nsub) where
  toFun a := Multiplicative.toAdd (foxAb Nsub (Additive.toMul a))
  map_zero' := rfl
  map_add' := fun a b => by
    show Multiplicative.toAdd (foxAb Nsub (Additive.toMul a * Additive.toMul b)) = _
    rw [_root_.map_mul]
    rfl

theorem foxAbAdd_of (w : Nsub) :
    foxAbAdd Nsub (Additive.ofMul (Abelianization.of w)) = foxVec Nsub (w : FreeGroup α) := rfl

/-- The index set of the Schreier generators: pairs `(q, x)` with `rep q · x ∉ T`. -/
def SchreierIdx : Type _ :=
  {p : (FreeGroup α ⧸ Nsub) × α // rep Nsub p.1 * FreeGroup.of p.2 ∉ repSet Nsub}

/-- The image in the abelianization of `Ñ` of the Schreier generator of a proper pair. -/
def schreierClass (i : SchreierIdx Nsub) : Additive (Abelianization Nsub) :=
  Additive.ofMul (Abelianization.of
    ⟨schreierGen Nsub (rep Nsub i.1.1) i.1.2, schreierGen_mem Nsub _ _⟩)

/-- The functional reading off the leading coefficient of a Schreier pair. -/
def schreierCoef (i : SchreierIdx Nsub) :
    Additive (Abelianization Nsub) →+ ℤ :=
  (Finsupp.applyAddHom (QuotientGroup.mk (rep Nsub i.1.1) : FreeGroup α ⧸ Nsub)).comp
    ((MonoidAlgebra.coeffAddEquiv).toAddMonoidHom.comp
      ((Pi.evalAddMonoidHom (fun _ : α => CoverRing Nsub) i.1.2).comp (foxAbAdd Nsub)))

theorem schreierCoef_apply (i : SchreierIdx Nsub) (a : Additive (Abelianization Nsub)) :
    schreierCoef Nsub i a = coefAt Nsub (rep Nsub i.1.1) (foxAbAdd Nsub a i.1.2) := rfl

/-- **The triangularity relation** between the Schreier generators and the leading
coefficients. -/
theorem schreierCoef_schreierClass_self (i : SchreierIdx Nsub) :
    schreierCoef Nsub i (schreierClass Nsub i) = 1 := by
  rw [schreierCoef_apply, schreierClass, foxAbAdd_of]
  rw [coefAt_foxVec_schreierGen Nsub (rep_mem_repSet Nsub i.1.1) i.1.2
    (rep_mem_repSet Nsub i.1.1) i.1.2 i.2, if_pos ⟨rfl, rfl⟩]

theorem schreierCoef_schreierClass_of_ne (i j : SchreierIdx Nsub) (hij : j ≠ i) :
    schreierCoef Nsub i (schreierClass Nsub j) = 0 := by
  rw [schreierCoef_apply, schreierClass, foxAbAdd_of]
  rw [coefAt_foxVec_schreierGen Nsub (rep_mem_repSet Nsub j.1.1) j.1.2
    (rep_mem_repSet Nsub i.1.1) i.1.2 i.2]
  rw [if_neg ?_]
  rintro ⟨h1, h2⟩
  refine hij ?_
  have hq : i.1.1 = j.1.1 := by
    have := congrArg (fun t : FreeGroup α => (QuotientGroup.mk t : FreeGroup α ⧸ Nsub)) h1
    simpa [mk_rep] using this
  exact Subtype.ext (Prod.ext hq.symm h2.symm)

omit [DecidableEq α] in
/-- The Schreier classes generate the abelianization of `Ñ`. -/
theorem closure_schreierClass (a : Additive (Abelianization Nsub)) :
    a ∈ AddSubgroup.closure (Set.range (schreierClass Nsub)) := by
  obtain ⟨u, hu⟩ := Quotient.exists_rep (Additive.toMul a)
  have ha : a = Additive.ofMul (Abelianization.of u) := by
    apply Additive.toMul.injective
    exact hu.symm
  subst ha
  have hmem : u ∈ Subgroup.closure ((Nsub.subtype) ⁻¹' properSchreierSet Nsub) := by
    have hmap : Subgroup.map Nsub.subtype
        (Subgroup.closure ((Nsub.subtype) ⁻¹' properSchreierSet Nsub)) = Nsub := by
      have hsub : properSchreierSet Nsub ⊆ Set.range ⇑Nsub.subtype := fun g hg =>
        ⟨⟨g, properSchreierSet_subset Nsub hg⟩, rfl⟩
      rw [MonoidHom.map_closure, Set.image_preimage_eq_inter_range,
        Set.inter_eq_self_of_subset_left hsub]
      exact (by
        refine le_antisymm ?_ ?_
        · rw [Subgroup.closure_le]
          exact properSchreierSet_subset Nsub
        · have hle : Subgroup.closure (schreierSet Nsub) ≤ Subgroup.closure (properSchreierSet Nsub) := by
            rw [Subgroup.closure_le]
            rintro _ ⟨⟨q, x⟩, rfl⟩
            by_cases h : rep Nsub q * FreeGroup.of x ∈ repSet Nsub
            · show schreierGen Nsub (rep Nsub q) x ∈ _
              rw [schreierGen_eq_one Nsub x h]
              exact Subgroup.one_mem _
            · exact Subgroup.subset_closure ⟨q, x, h, rfl⟩
          intro w hw
          refine hle ?_
          rw [closure_schreierGen Nsub]
          exact hw)
    have htop : Subgroup.map Nsub.subtype (⊤) = Nsub := by
      ext x
      simp [Subgroup.mem_map]
    have := Subgroup.map_injective Subtype.val_injective (hmap.trans htop.symm)
    rw [this]
    trivial
  clear hu
  induction hmem using Subgroup.closure_induction with
  | mem v hv =>
      obtain ⟨q, x, hnot, hval⟩ := hv
      refine AddSubgroup.subset_closure (Set.mem_range.2 ⟨⟨(q, x), hnot⟩, ?_⟩)
      unfold schreierClass
      congr 2
      exact Subtype.ext hval.symm
  | one => simp
  | mul v w _ _ ihv ihw =>
      have : Additive.ofMul (Abelianization.of (v * w))
          = Additive.ofMul (Abelianization.of v) + Additive.ofMul (Abelianization.of w) := by
        show Additive.ofMul (Abelianization.of (v * w))
          = Additive.ofMul (Abelianization.of v * Abelianization.of w)
        rw [_root_.map_mul]
      rw [this]
      exact AddSubgroup.add_mem _ ihv ihw
  | inv v _ ihv => simp_all

/-- **The Magnus/Blanchfield theorem.**  For `w ∈ Ñ`, the Fox vector of `w` vanishes exactly
when `w` lies in the commutator subgroup `[Ñ, Ñ]`. -/
theorem foxVec_eq_zero_iff {w : FreeGroup α} (hw : w ∈ Nsub) :
    foxVec Nsub w = 0 ↔ w ∈ ⁅Nsub, Nsub⁆ := by
  constructor
  · intro h0
    have hzero : Additive.ofMul (Abelianization.of (⟨w, hw⟩ : Nsub)) = 0 := by
      refine eq_zero_of_forall_coefHom (schreierClass Nsub) (closure_schreierClass Nsub)
        (schreierCoef Nsub) (schreierCoef_schreierClass_self Nsub)
        (schreierCoef_schreierClass_of_ne Nsub) ?_
      intro i
      rw [schreierCoef_apply, foxAbAdd_of]
      rw [h0]
      rfl
    have hcomm : ⟨w, hw⟩ ∈ commutator Nsub := by
      have h1 : Abelianization.of (⟨w, hw⟩ : Nsub) = 1 := by
        apply Additive.ofMul.injective
        exact hzero
      rw [Abelianization.of] at h1
      exact (QuotientGroup.eq_one_iff _).1 h1
    rw [← Subgroup.map_subtype_commutator Nsub]
    exact ⟨⟨w, hw⟩, hcomm, rfl⟩
  · intro hcomm
    have hker : ⁅Nsub, Nsub⁆ ≤ (foxHomNsub Nsub).ker.map Nsub.subtype := by
      rw [← Subgroup.map_subtype_commutator Nsub]
      exact Subgroup.map_mono (Abelianization.commutator_subset_ker (foxHomNsub Nsub))
    obtain ⟨u, hu, huw⟩ := hker hcomm
    have hu'  := hu
    have hzero  := hu'
    rw [← huw]
    exact hzero

end FiniteChains

namespace FiniteChains

open MonoidAlgebra

universe u

/-! ### Transport of the lifting property along isomorphisms -/

/-- `LiftsMod` transfers along additive isomorphisms intertwining the two maps. -/
theorem liftsMod_of_addEquiv {U V U' V' : Type*} [AddCommGroup U] [AddCommGroup V]
    [AddCommGroup U'] [AddCommGroup V'] (f : U →+ V) (f' : U' →+ V')
    (eU : U ≃+ U') (eV : V ≃+ V') (hcomm : ∀ u, f' (eU u) = eV (f u)) (n : ℕ)
    (h : LiftsMod f n) : LiftsMod f' n := by
  intro u' ⟨w', hw'⟩
  obtain ⟨u, rfl⟩ : ∃ u, eU u = u' := ⟨eU.symm u', eU.apply_symm_apply u'⟩
  have hfu : eV (f u) = n • w' := by rw [← hcomm u]; exact hw'
  have : f u = n • eV.symm w' := by
    apply eV.injective
    rw [hfu, map_nsmul, eV.apply_symm_apply]
  obtain ⟨u₀, hu₀⟩ := h u ⟨eV.symm w', this⟩
  exact ⟨eU u₀, by rw [hu₀, map_nsmul]⟩

/-! ### A torsion-freeness criterion -/

/-- If, in a normal subgroup `N`, a power of an element lying in `[N, N]` forces the element
itself into `[N, N]`, then the abelian group `N/[N, N]` is torsion free. -/
theorem isMulTorsionFree_map_commutator_of_pow {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] (hkey : ∀ g ∈ N, ∀ n : ℕ, n ≠ 0 → g ^ n ∈ ⁅N, N⁆ → g ∈ ⁅N, N⁆) :
    IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆)) := by
  haveI hcomm :=
    isMulCommutative_map_commutator N
  constructor
  intro n hn a b hab
  have hab' : a ^ n = b ^ n := hab
  have hcab : Commute a b⁻¹ := hcomm.is_comm.comm a b⁻¹
  have hone : (a * b⁻¹) ^ n = 1 := by
    rw [hcab.mul_pow, hab', inv_pow, mul_inv_cancel]
  obtain ⟨z, hz, hzeq⟩ := (a * b⁻¹).2
  have hzn : z ^ n ∈ ⁅N, N⁆ := by
    have hz1 : (QuotientGroup.mk' ⁅N, N⁆) (z ^ n) = 1 := by
      rw [map_pow, hzeq]
      exact congrArg Subtype.val hone
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz1
  have hzmem  := hkey z hz n hn hzn
  have hab1 : (a * b⁻¹) = 1 := by
    ext
    rw [Subgroup.coe_one, ← hzeq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hzmem
  exact mul_inv_eq_one.1 hab1

/-! ### The presented complex -/

variable {α : Type*} [Fintype α] [DecidableEq α] {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

/-- The relator subgroup `R = ⟪r_1, …, r_m⟫ ◁ F`. -/
def relSub : Subgroup (FreeGroup α) := Subgroup.normalClosure (Set.range ρ)

instance relSub_normal : (relSub ρ).Normal := Subgroup.normalClosure_normal

/-- The fundamental group `G = π₁(K) = F/R` of the presented complex. -/
abbrev PresGroup : Type _ := FreeGroup α ⧸ relSub ρ

/-- The Fox boundary matrix of the presentation, read in `ℤ[G]`. -/
def foxMatrixPres (i : α) (j : J) : MonoidAlgebra ℤ (PresGroup ρ) :=
  quotRingHom ℤ (relSub ρ) (fox i (ρ j))

omit [Fintype α] [Fintype J] in
theorem foxMatrixPres_col_finite (j : J) : {i : α | foxMatrixPres ρ i j ≠ 0}.Finite :=
  (fox_generator_support_finite (ρ j)).subset (by
    intro i hi
    by_contra hz
    simp only [Set.mem_setOf_eq, not_not] at hz
    exact hi (by simp only [foxMatrixPres, hz, map_zero]))

section Subgroups

variable (Nt : Subgroup (FreeGroup α)) [Nt.Normal] (hR : relSub ρ ≤ Nt)

/-- The normal subgroup `N = Ñ/R ◁ G` attached to `Ñ ◁ F`. -/
def presSub : Subgroup (PresGroup ρ) := Nt.map (QuotientGroup.mk' (relSub ρ))

instance presSub_normal : (presSub ρ Nt).Normal :=
  Subgroup.Normal.map ‹Nt.Normal› _ (QuotientGroup.mk'_surjective _)

/-- The identification `G/N ≅ F/Ñ` of the deck group of the cover. -/
def quotQuotEquivPres :
    (PresGroup ρ ⧸ presSub ρ Nt) ≃* (FreeGroup α ⧸ Nt) :=
  QuotientGroup.quotientQuotientEquivQuotient (relSub ρ) Nt hR

omit [Fintype α] [DecidableEq α] [Fintype J] in
theorem quotQuotEquivPres_mk (w : FreeGroup α) :
    quotQuotEquivPres ρ Nt hR
        (QuotientGroup.mk (QuotientGroup.mk w : PresGroup ρ) : PresGroup ρ ⧸ presSub ρ Nt)
      = (QuotientGroup.mk w : FreeGroup α ⧸ Nt) :=
  (MulEquiv.eq_symm_apply (quotQuotEquivPres ρ Nt hR)).mp rfl

/-- The induced isomorphism of group rings `ℤ[G/N] ≅ ℤ[F/Ñ]`. -/
def ringEquivPres :
    MonoidAlgebra ℤ (PresGroup ρ ⧸ presSub ρ Nt) ≃ₐ[ℤ] MonoidAlgebra ℤ (FreeGroup α ⧸ Nt) :=
  MonoidAlgebra.domCongr ℤ ℤ (quotQuotEquivPres ρ Nt hR)

omit [Fintype α] [DecidableEq α] [Fintype J] in
/-- The reduction of the group ring of the free group to `ℤ[F/Ñ]` factors through the two
successive quotients. -/
theorem ringEquivPres_quot (x : MonoidAlgebra ℤ (FreeGroup α)) :
    ringEquivPres ρ Nt hR (quotRingHom ℤ (presSub ρ Nt) (quotRingHom ℤ (relSub ρ) x))
      = proj Nt x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp_all
  | single g n =>
      rw [quotRingHom_single, quotRingHom_single, proj_single]
      show MonoidAlgebra.domCongr ℤ ℤ (quotQuotEquivPres ρ Nt hR) (single _ n) = _
      rw [MonoidAlgebra.domCongr_single, quotQuotEquivPres_mk]

end Subgroups

end FiniteChains

namespace FiniteChains
namespace Nerve

universe u

open FreeAbelianGroup

variable {P Q : Type u}

/-- The augmented simplicial chains on the nerve: the free abelian group on finite lists.  A
list of length `k+1` is a `k`-simplex, and the empty list is the generator of the augmentation
degree. -/
abbrev Ch (P : Type u) : Type u := FreeAbelianGroup (List P)

/-- Two additive maps out of the chains agree as soon as they agree on lists. -/

theorem ext_apply {A : Type*} [AddCommGroup A] {F G : Ch P →+ A}
    (h : ∀ l : List P, F (of l) = G (of l)) (x : Ch P) : F x = G x := by
  rw [(show F = G by
    ext x
    exact h x)]

/-! ### The basic operators -/

/-- Prepending a fixed element to every list. -/
def consMap (a : P) : Ch P →+ Ch P := lift fun l => of (a :: l)

@[simp] theorem consMap_of (a : P) (l : List P) : consMap a (of l) = of (a :: l) :=
  lift_apply_of _ _

/-- Prepending a fixed list to every list. -/
def consList (pre : List P) : Ch P →+ Ch P := lift fun l => of (pre ++ l)

@[simp] theorem consList_of (pre l : List P) : consList pre (of l) = of (pre ++ l) :=
  lift_apply_of _ _

@[simp] theorem consList_nil (x : Ch P) : consList ([] : List P) x = x := by
  refine ext_apply (G := AddMonoidHom.id _) ?_ x
  intro l; simp

theorem consList_consMap (pre : List P) (a : P) (x : Ch P) :
    consList pre (consMap a x) = consList (pre ++ [a]) x := by
  refine ext_apply (F := (consList pre).comp (consMap a)) ?_ x
  intro l; simp

/-- The boundary, on a basis element. -/
def bdryOn : List P → Ch P
  | [] => 0
  | a :: t => of t - consMap a (bdryOn t)

/-- The boundary map of the augmented chain complex of the nerve. -/
def bdry : Ch P →+ Ch P := lift bdryOn

@[simp] theorem bdry_of (l : List P) : bdry (of l) = bdryOn l := lift_apply_of _ _

@[simp] theorem bdryOn_nil : bdryOn ([] : List P) = 0 := rfl

theorem bdryOn_cons (a : P) (t : List P) : bdryOn (a :: t) = of t - consMap a (bdryOn t) := rfl

/-- The boundary of a chain prefixed by one element. -/
theorem bdry_consMap (a : P) (x : Ch P) : bdry (consMap a x) = x - consMap a (bdry x) := by
  refine ext_apply (F := bdry.comp (consMap a))
    (G := (AddMonoidHom.id _) - (consMap a).comp bdry) ?_ x
  intro l
  simp [bdryOn_cons]

/-- `∂ ∘ ∂ = 0`: the chains of the nerve form a complex. -/
theorem bdry_bdry (x : Ch P) : bdry (bdry x) = 0 := by
  refine ext_apply (F := bdry.comp bdry) (G := 0) ?_ x
  intro l
  simp
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [bdryOn_cons, map_sub, bdry_of, bdry_consMap, ih]
      simp

/-- Pushing chains forward along a map of posets. -/
def cmap (f : P → Q) : Ch P →+ Ch Q := lift fun l => of (l.map f)

@[simp] theorem cmap_of (f : P → Q) (l : List P) : cmap f (of l) = of (l.map f) :=
  lift_apply_of _ _

@[simp] theorem cmap_id (x : Ch P) : cmap id x = x := by
  refine ext_apply (G := AddMonoidHom.id _) ?_ x
  intro l; simp

theorem cmap_consMap (f : P → Q) (a : P) (x : Ch P) :
    cmap f (consMap a x) = consMap (f a) (cmap f x) := by
  refine ext_apply (F := (cmap f).comp (consMap a))
    (G := (consMap (f a)).comp (cmap f)) ?_ x
  intro l; simp

/-- Pushforward is a chain map. -/
theorem cmap_bdry (f : P → Q) (x : Ch P) : cmap f (bdry x) = bdry (cmap f x) := by
  refine ext_apply (F := (cmap f).comp bdry) (G := bdry.comp (cmap f)) ?_ x
  intro l
  simp
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, bdryOn_cons, map_sub, cmap_consMap, ih, cmap_of]

/-! ### The prism operator -/

/-- The prism operator `P_{f,g}[σ₀,…,σ_k] = Σ_i (-1)^i [f σ₀,…,f σ_i, g σ_i,…,g σ_k]`, on a
basis element, in its recursive form. -/
def prismOn (f g : P → P) : List P → Ch P
  | [] => 0
  | a :: t => of (f a :: (a :: t).map g) - consMap (f a) (prismOn f g t)

/-- The prism operator of a pair of order maps. -/
def prism (f g : P → P) : Ch P →+ Ch P := lift (prismOn f g)

@[simp] theorem prism_of (f g : P → P) (l : List P) : prism f g (of l) = prismOn f g l :=
  lift_apply_of _ _

theorem prismOn_cons (f g : P → P) (a : P) (t : List P) :
    prismOn f g (a :: t) = of (f a :: (a :: t).map g) - consMap (f a) (prismOn f g t) := rfl

/-- The prism operator on a chain prefixed by one element. -/
theorem prism_consMap (f g : P → P) (a : P) (x : Ch P) :
    prism f g (consMap a x) =
      consMap (f a) (consMap (g a) (cmap g x)) - consMap (f a) (prism f g x) := by
  refine ext_apply (F := (prism f g).comp (consMap a))
    (G := ((consMap (f a)).comp ((consMap (g a)).comp (cmap g))) -
      (consMap (f a)).comp (prism f g)) ?_ x
  intro l
  simp [prismOn_cons]

/-- **The prism identity**: `∂ P_{f,g} + P_{f,g} ∂ = g_* - f_*`.  No hypothesis on `f` and `g`
is needed; monotonicity and `f ≤ g` enter only through the fact that the operator preserves the
increasing chains (`FiniteChains.Nerve.prism_mem_inc`). -/
theorem bdry_prism_add_prism_bdry (f g : P → P) (x : Ch P) :
    bdry (prism f g x) + prism f g (bdry x) = cmap g x - cmap f x := by
  -- the inductive step, for an arbitrary chain
  have key : ∀ a X,
      bdry (prism f g X) + prism f g (bdry X) = cmap g X - cmap f X →
      bdry (prism f g (consMap a X)) + prism f g (bdry (consMap a X)) =
        cmap g (consMap a X) - cmap f (consMap a X) := by
    intro a X hX
    have h1 : bdry (prism f g (consMap a X)) =
        (consMap (g a) (cmap g X) - consMap (f a) (cmap g X) +
            consMap (f a) (consMap (g a) (bdry (cmap g X)))) -
          (prism f g X - consMap (f a) (bdry (prism f g X))) := by
      rw [prism_consMap, map_sub, bdry_consMap (f a) (consMap (g a) (cmap g X)),
        bdry_consMap (f a) (prism f g X), bdry_consMap (g a) (cmap g X), map_sub]
      abel
    have h2 : prism f g (bdry (consMap a X)) =
        prism f g X - (consMap (f a) (consMap (g a) (bdry (cmap g X))) -
          consMap (f a) (prism f g (bdry X))) := by
      rw [bdry_consMap, map_sub, prism_consMap, cmap_bdry]
    have h3 : consMap (f a) (bdry (prism f g X)) + consMap (f a) (prism f g (bdry X)) =
        consMap (f a) (cmap g X) - consMap (f a) (cmap f X) := by
      rw [← map_add, hX, map_sub]
    have h4 : cmap g (consMap a X) - cmap f (consMap a X) =
        consMap (g a) (cmap g X) - consMap (f a) (cmap f X) := by
      rw [cmap_consMap, cmap_consMap]
    rw [h1, h2, h4]
    linear_combination (norm := abel) h3
  refine ext_apply (F := bdry.comp (prism f g) + (prism f g).comp bdry)
    (G := cmap g - cmap f) ?_ x
  intro l
  simp only [AddMonoidHom.add_apply, AddMonoidHom.sub_apply, AddMonoidHom.coe_comp,
    Function.comp_apply]
  induction l with
  | nil => simp [prismOn]
  | cons a t ih =>
      have := key a (of t) ih
      simpa using this

/-! ### Increasing chains -/

variable [Preorder P]

/-- The simplicial chains of the order complex: the subgroup generated by the weakly increasing
lists (the nondegenerate ones are the simplices of the order complex, the degenerate ones are
the extra basis elements of the unnormalised complex of the nerve). -/
def Inc (P : Type u) [Preorder P] : AddSubgroup (Ch P) :=
  AddSubgroup.closure {x : Ch P | ∃ l : List P, List.IsChain (· ≤ ·) l ∧ x = of l}

theorem of_mem_inc {l : List P} (hl : List.IsChain (· ≤ ·) l) : of l ∈ Inc P :=
  AddSubgroup.subset_closure ⟨l, hl, rfl⟩

/-- Removing an element from an increasing list leaves an increasing list. -/
theorem isChain_append_of_isChain_append_cons {pre t : List P} {a : P}
    (h : List.IsChain (· ≤ ·) (pre ++ a :: t)) : List.IsChain (· ≤ ·) (pre ++ t) := by grind

/-- The boundary of an increasing list, with any increasing prefix adjoined, is an increasing
chain. -/
theorem consList_bdryOn_mem_inc :
    ∀ (l pre : List P), List.IsChain (· ≤ ·) (pre ++ l) → consList pre (bdryOn l) ∈ Inc P := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      intro pre hpre
      rw [bdryOn_cons, map_sub, consList_of, consList_consMap]
      refine AddSubgroup.sub_mem _ ?_ ?_
      · exact of_mem_inc (isChain_append_of_isChain_append_cons hpre)
      · simp_all


/-- The boundary preserves the increasing chains. -/
theorem bdry_mem_inc {x : Ch P} (hx : x ∈ Inc P) : bdry x ∈ Inc P := by
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, hl, rfl⟩
    simpa using (by
      have := consList_bdryOn_mem_inc l [] (by simpa using hl)
      simpa using this)
  · simp
  · intro y z _ _ hy hz
    simpa using AddSubgroup.add_mem _ hy hz
  · simp

/-- Pushing forward along a monotone map preserves the increasing chains. -/
theorem cmap_mem_inc {f : P → P} (hf : Monotone f) {x : Ch P} (hx : x ∈ Inc P) :
    cmap f x ∈ Inc P := by
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, hl, rfl⟩
    rw [cmap_of]
    exact of_mem_inc (List.isChain_map_of_isChain f (fun _ _ h => hf h) hl)
  · simp
  · intro y z _ _ hy hz
    simpa using AddSubgroup.add_mem _ hy hz
  · simp

/-- The prism of an increasing list, with any increasing prefix adjoined, is an increasing
chain.  This is where `f ≤ g` is used. -/
theorem consList_prismOn_mem_inc {f g : P → P} (hg : Monotone g)
    (hfg : ∀ p : P, f p ≤ g p) :
    ∀ (l pre : List P), List.IsChain (· ≤ ·) l → List.IsChain (· ≤ ·) (pre ++ l.map f) →
      consList pre (prismOn f g l) ∈ Inc P := by
  intro l
  induction l with
  | nil => intro pre _ _; simp [prismOn]
  | cons a t ih =>
      intro pre hl hpre
      rw [prismOn_cons, map_sub, consList_of, consList_consMap]
      refine AddSubgroup.sub_mem _ ?_ ?_
      · refine of_mem_inc ?_
        rw [List.isChain_append] at hpre ⊢
        obtain ⟨hp, hmf, hlast⟩ := hpre
        refine ⟨hp, ?_, ?_⟩
        · rw [List.isChain_cons]
          refine ⟨?_, List.isChain_map_of_isChain g (fun _ _ h => hg h) hl⟩
          intro y hy
          have hya : y = g a := by simpa [eq_comm] using hy
          rw [hya]
          exact hfg a
        · simp_all
      · grind

/-- The prism operator preserves the increasing chains. -/
theorem prism_mem_inc {f g : P → P} (hf : Monotone f) (hg : Monotone g) (hfg : ∀ p : P, f p ≤ g p)
    {x : Ch P} (hx : x ∈ Inc P) : prism f g x ∈ Inc P := by
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, hl, rfl⟩
    rw [prism_of]
    have := consList_prismOn_mem_inc hg hfg l [] hl (by
      simpa using List.isChain_map_of_isChain f (fun _ _ h => hf h) hl)
    simpa using this
  · simp
  · intro y z _ _ hy hz
    simpa using AddSubgroup.add_mem _ hy hz
  · simp

/-! ### The contraction -/

variable (ρ : P → P) (d : P)

/-- The contracting homotopy of the source text: `P_{ρ,id} - P_{ρ,c_d}`, corrected by the cone
on `d` which kills the constant map. -/
def contraction : Ch P →+ Ch P :=
  prism ρ id - prism ρ (fun _ => d) + (consMap d).comp (cmap (fun _ => d))

omit [Preorder P] in
/-- **The augmented chain complex of the nerve is contractible.**  The identity is the boundary
of the explicit homotopy. -/
theorem bdry_contraction_add_contraction_bdry (x : Ch P) :
    bdry (contraction ρ d x) + contraction ρ d (bdry x) = x := by
  have t1 : bdry (prism ρ id x) + prism ρ id (bdry x) = x - cmap ρ x := by
    have := bdry_prism_add_prism_bdry ρ id x
    simpa using this
  have t2 : bdry (prism ρ (fun _ => d) x) + prism ρ (fun _ => d) (bdry x) =
      cmap (fun _ => d) x - cmap ρ x := bdry_prism_add_prism_bdry _ _ x
  have t3 : bdry (consMap d (cmap (fun _ => d) x)) + consMap d (cmap (fun _ => d) (bdry x)) =
      cmap (fun _ => d) x := by
    rw [bdry_consMap, cmap_bdry]
    abel
  simp only [contraction, AddMonoidHom.add_apply, AddMonoidHom.sub_apply, AddMonoidHom.coe_comp,
    Function.comp_apply, map_add, map_sub]
  grind

omit [Preorder P] in
/-- The head of a constant list is the constant. -/
theorem eq_of_mem_head?_map_const {l : List P} {y : P}
    (hy : y ∈ (l.map (fun _ => d)).head?) : y = d := by grind

/-- Constant lists are increasing. -/

theorem cone_const_mem_inc (x : Ch P) : consMap d (cmap (fun _ => d) x) ∈ Inc P := by
  refine FreeAbelianGroup.induction_on x (by simp) (fun l => ?_) (fun l hl => by
    simpa using AddSubgroup.neg_mem _ hl) (fun u v hu hv => by
    simpa using AddSubgroup.add_mem _ hu hv)
  rw [cmap_of, consMap_of]
  refine of_mem_inc ?_
  rw [List.isChain_cons]
  refine ⟨?_, (by
    induction l with
    | nil => simp
    | cons a t ih =>
        rw [List.map_cons, List.isChain_cons]
        refine ⟨?_, ih⟩
        intro y hy
        rw [eq_of_mem_head?_map_const d hy])⟩
  intro y hy
  rw [eq_of_mem_head?_map_const d hy]

/-- The contraction preserves the increasing chains. -/
theorem contraction_mem_inc (hρ : Monotone ρ) (hρle : ∀ p : P, ρ p ≤ p)
    (hρd : ∀ p : P, ρ p ≤ d) {x : Ch P} (hx : x ∈ Inc P) : contraction ρ d x ∈ Inc P := by
  have h1  := prism_mem_inc hρ monotone_id hρle hx
  have h2  :=
    prism_mem_inc hρ (monotone_const) hρd hx
  have h3  := cone_const_mem_inc d x
  simp only [contraction, AddMonoidHom.add_apply, AddMonoidHom.sub_apply, AddMonoidHom.coe_comp,
    Function.comp_apply]
  exact AddSubgroup.add_mem _ (AddSubgroup.sub_mem _ h1 h2) h3

/-- **Acyclicity of the order complex**: if `ρ` is monotone with `ρ ≤ id` and `ρ ≤ c_d`, then
every increasing cycle — in every degree, including the augmentation degree — is the boundary of
an increasing chain. -/
theorem exists_bdry_eq_of_cycle (hρ : Monotone ρ) (hρle : ∀ p : P, ρ p ≤ p)
    (hρd : ∀ p : P, ρ p ≤ d) {x : Ch P} (hx : x ∈ Inc P) (hcyc : bdry x = 0) :
    ∃ y ∈ Inc P, bdry y = x := by
  refine ⟨contraction ρ d x, contraction_mem_inc ρ d hρ hρle hρd hx, ?_⟩
  have := bdry_contraction_add_contraction_bdry ρ d x
  simp_all

end Nerve
end FiniteChains

namespace FiniteChains
namespace Nerve

universe u

open FreeAbelianGroup

/-! ### The support criterion -/

section Support

variable {X : Type u}

/-- **Membership in the subgroup generated by a set of basis elements, read off the support.** -/
theorem mem_closure_image_of_iff (S : Set X) (x : FreeAbelianGroup X) :
    x ∈ AddSubgroup.closure (FreeAbelianGroup.of '' S) ↔ ∀ y ∈ x.support, y ∈ S := by
  classical
  constructor
  · intro hx
    refine AddSubgroup.closure_induction (p := fun z _ => ∀ y ∈ z.support, y ∈ S) ?_ ?_ ?_ ?_ hx
    · rintro z ⟨l, hl, rfl⟩
      intro y hy
      rw [support_of, Finset.mem_singleton] at hy
      exact hy ▸ hl
    · simp
    · intro u v _ _ hu hv y hy
      rcases Finset.mem_union.1 (support_add u v hy) with h | h
      exacts [hu y h, hv y h]
    · simp
  · intro h
    have key : ∀ f : X →₀ ℤ, (∀ y ∈ f.support, y ∈ S) →
        (equivFinsupp X).symm f ∈ AddSubgroup.closure (FreeAbelianGroup.of '' S) := by
      intro f
      induction f using Finsupp.induction with
      | zero => simp
      | @single_add a b f ha hb ih =>
          intro hsup
          have hsupport  :=
            Finsupp.support_single_add ha hb
          have haS  := hsup a (by rw [hsupport]; exact Finset.mem_cons_self _ _)
          have hfS : ∀ y ∈ f.support, y ∈ S := by
            intro y hy
            exact hsup y (by rw [hsupport]; exact Finset.mem_cons_of_mem hy)
          have hsingle : (equivFinsupp X).symm (Finsupp.single a b) = b • FreeAbelianGroup.of a := by
            apply (equivFinsupp X).injective
            simp [equivFinsupp]
          rw [map_add, hsingle]
          refine AddSubgroup.add_mem _ ?_ (ih hfS)
          exact AddSubgroup.zsmul_mem _
            (AddSubgroup.subset_closure (Set.mem_image_of_mem _ haS)) b
    have hx : x = (equivFinsupp X).symm ((equivFinsupp X) x) := by simp
    rw [hx]
    exact key _ h

end Support

/-! ### Chains supported on a subposet -/

variable {P Q : Type u} [Preorder P]

/-- The admissible increasing lists with all vertices in `A`. -/
def IncLists (A : P → Prop) : Set (List P) :=
  {l : List P | List.IsChain (· ≤ ·) l ∧ ∀ a ∈ l, A a}

/-- **The chains supported on the subposet `A`**: the subgroup `C_*(A)` of `ℤ[List P]` generated
by the increasing lists whose vertices all satisfy `A`. -/
def IncOn (A : P → Prop) : AddSubgroup (Ch P) :=
  AddSubgroup.closure (FreeAbelianGroup.of '' IncLists A)

/-- **The support criterion for `C_*(A)`.** -/
theorem mem_incOn_iff {A : P → Prop} (x : Ch P) :
    x ∈ IncOn A ↔ ∀ l ∈ x.support, List.IsChain (· ≤ ·) l ∧ ∀ a ∈ l, A a :=
  mem_closure_image_of_iff _ x

theorem of_mem_incOn {A : P → Prop} {l : List P} (hl : List.IsChain (· ≤ ·) l)
    (hA : ∀ a ∈ l, A a) : FreeAbelianGroup.of l ∈ IncOn A :=
  AddSubgroup.subset_closure ⟨l, ⟨hl, hA⟩, rfl⟩

/-- The support criterion for the full complex of increasing chains. -/
theorem mem_inc_iff (x : Ch P) :
    x ∈ Inc P ↔ ∀ l ∈ x.support, List.IsChain (· ≤ ·) l := by
  have hset : {x : Ch P | ∃ l : List P, List.IsChain (· ≤ ·) l ∧ x = FreeAbelianGroup.of l} =
      FreeAbelianGroup.of '' {l : List P | List.IsChain (· ≤ ·) l} := by
    ext y
    constructor
    · grind
    · grind
  rw [Inc, hset]
  exact mem_closure_image_of_iff _ x

theorem incOn_le_inc (A : P → Prop) : IncOn A ≤ Inc P := by
  intro x hx
  rw [mem_inc_iff]
  intro l hl
  exact ((mem_incOn_iff x).1 hx l hl).1

theorem incOn_mono {A B : P → Prop} (h : ∀ p, A p → B p) : IncOn A ≤ IncOn B := by
  intro x hx
  rw [mem_incOn_iff] at hx ⊢
  grind


/-- **`C_*(A) ∩ C_*(B) = C_*(A ∩ B)`.** -/
theorem incOn_inf (A B : P → Prop) :
    IncOn A ⊓ IncOn B = IncOn (fun p => A p ∧ B p) := by
  ext x
  simp only [AddSubgroup.mem_inf, mem_incOn_iff]
  grind

/-! ### The boundary preserves `C_*(A)` -/

theorem consList_bdryOn_mem_incOn (A : P → Prop) :
    ∀ (l pre : List P), List.IsChain (· ≤ ·) (pre ++ l) → (∀ a ∈ pre ++ l, A a) →
      consList pre (bdryOn l) ∈ IncOn A := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      intro pre hchain hall
      rw [bdryOn_cons, map_sub, consList_of, consList_consMap]
      refine AddSubgroup.sub_mem _ ?_ ?_
      · refine of_mem_incOn (isChain_append_of_isChain_append_cons hchain) ?_
        intro b hb
        rcases List.mem_append.1 hb with h | h
        · exact hall b (List.mem_append.2 (Or.inl h))
        · exact hall b (List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ h)))
      · grind


/-- The boundary preserves the chains supported on a subposet. -/
theorem bdry_mem_incOn {A : P → Prop} {x : Ch P} (hx : x ∈ IncOn A) : bdry x ∈ IncOn A := by
  refine AddSubgroup.closure_induction (p := fun y _ => bdry y ∈ IncOn A) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, ⟨hl, hA⟩, rfl⟩
    simpa using (by
      have := consList_bdryOn_mem_incOn A l [] (by simpa using hl) (by simpa using hA)
      simpa using this)
  · simp
  · intro y z _ _ hy hz
    simpa using AddSubgroup.add_mem _ hy hz
  · simp

/-! ### Unmixedness and the splitting of chains of a union -/

/-- Every increasing list with vertices in the union lies entirely in one of the two pieces.
This is where "unmixedness" of the covering is used: any two vertices of an increasing list are
comparable, so a vertex outside `A` forces every vertex into `B`. -/
theorem forall_mem_or_of_unmixed {A B U : P → Prop}
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    {l : List P} (hl : List.IsChain (· ≤ ·) l) (hlU : ∀ a ∈ l, U a) :
    (∀ a ∈ l, A a) ∨ (∀ a ∈ l, B a) := by
  by_cases hA : ∀ a ∈ l, A a
  · simp_all
  · refine Or.inr ?_
    push Not at hA
    obtain ⟨c₀, hc₀l, hc₀⟩ := hA
    have hpair : ∀ x ∈ l, ∀ y ∈ l, x ≤ y ∨ y ≤ x := by
      have hpw : l.Pairwise (fun x y : P => x ≤ y ∨ y ≤ x) :=
        (List.IsChain.pairwise hl).imp (fun h => Or.inl h)
      intro x hx y hy
      by_cases hxy : x = y
      · simp_all
      · letI : Std.Symm (fun x y : P => x ≤ y ∨ y ≤ x) := ⟨fun _ _ h => h.symm⟩
        exact hpw.forall hx hy hxy
    intro c hc
    rcases hpair c₀ hc₀l c hc with h | h
    · grind
    · grind

/-- **Splitting a chain of the union.**  The decomposition is defined on the basis: a list goes
into `a` if all its vertices lie in `A`, and into `b` otherwise. -/
theorem exists_split_of_unmixed {A B U : P → Prop}
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    {z : Ch P} (hz : z ∈ IncOn U) :
    ∃ a ∈ IncOn A, ∃ b ∈ IncOn B, z = a + b := by
  refine AddSubgroup.closure_induction
    (p := fun y _ => ∃ a ∈ IncOn A, ∃ b ∈ IncOn B, y = a + b) ?_ ?_ ?_ ?_ hz
  · rintro y ⟨l, ⟨hl, hlU⟩, rfl⟩
    rcases forall_mem_or_of_unmixed hmix hl hlU with h | h
    · exact ⟨FreeAbelianGroup.of l, of_mem_incOn hl h, 0, AddSubgroup.zero_mem _, by simp⟩
    · exact ⟨0, AddSubgroup.zero_mem _, FreeAbelianGroup.of l, of_mem_incOn hl h, by simp⟩
  · exact ⟨0, AddSubgroup.zero_mem _, 0, AddSubgroup.zero_mem _, by simp⟩
  · rintro y z _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    exact ⟨a + a', AddSubgroup.add_mem _ ha ha', b + b', AddSubgroup.add_mem _ hb hb', by abel⟩
  · rintro y _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨-a, AddSubgroup.neg_mem _ ha, -b, AddSubgroup.neg_mem _ hb, by abel⟩

/-! ### The gluing computation -/

/-- Acyclicity of the part of the complex supported on `A`: every cycle supported on `A` is the
boundary of a chain supported on `A`. -/
def AcyclicIn (A : P → Prop) : Prop :=
  ∀ x ∈ IncOn A, bdry x = 0 → ∃ y ∈ IncOn A, bdry y = x

theorem acyclicIn_congr {A B : P → Prop} (h : ∀ p, A p ↔ B p) (hA : AcyclicIn A) :
    AcyclicIn B := by
  have hAB : IncOn A = IncOn B := (le_antisymm (incOn_mono fun p hp => (h p).1 hp) (incOn_mono fun p hp => (h p).2 hp))
  intro x hx hcyc
  obtain ⟨y, hy, hdy⟩ := hA x (by rw [hAB]; exact hx) hcyc
  grind

/-- **The chain-level gluing step.**  If the two pieces and their intersection have vanishing
homology (in all degrees, in the augmented complex), so does their union. -/
theorem acyclicIn_union_of_unmixed {A B U : P → Prop}
    (hU : ∀ p, U p ↔ (A p ∨ B p))
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hA : AcyclicIn A) (hB : AcyclicIn B) (hJ : AcyclicIn (fun p => A p ∧ B p)) :
    AcyclicIn U := by
  intro z hz hcyc
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_split_of_unmixed hmix hz
  -- `t = ∂a = -∂b` is a cycle supported on the intersection
  have hda  := bdry_mem_incOn ha
  have hdb  := bdry_mem_incOn hb
  have hsum : bdry a + bdry b = 0 := by rw [← map_add]; exact hcyc
  have hdaB : bdry a ∈ IncOn B := by
    have : bdry a = -bdry b := by linear_combination (norm := abel) hsum
    rw [this]
    exact AddSubgroup.neg_mem _ hdb
  have htJ : bdry a ∈ IncOn (fun p => A p ∧ B p) := by
    rw [← incOn_inf]
    exact ⟨hda, hdaB⟩
  obtain ⟨u, hu, hdu⟩ := hJ (bdry a) htJ (by simp [bdry_bdry])
  have huA  := (incOn_mono (fun p hp => hp.1)) hu
  have huB  := (incOn_mono (fun p hp => hp.2)) hu
  -- `a - u` and `b + u` are cycles of the two pieces
  obtain ⟨p, hp, hdp⟩ := hA (a - u) (AddSubgroup.sub_mem _ ha huA) (by
    rw [map_sub, hdu, sub_self])
  obtain ⟨q, hq, hdq⟩ := hB (b + u) (AddSubgroup.add_mem _ hb huB) (by
    rw [map_add, hdu]
    linear_combination (norm := abel) hsum)
  refine ⟨p + q, AddSubgroup.add_mem _ ?_ ?_, ?_⟩
  · exact incOn_mono (fun r hr => (hU r).2 (Or.inl hr)) hp
  · exact incOn_mono (fun r hr => (hU r).2 (Or.inr hr)) hq
  · simp_all

/-! ### Transfer between a subposet and the chains supported on it -/

section Transfer

variable (A : P → Prop)

theorem cmap_val_mem_incOn {x : Ch {p : P // A p}} (hx : x ∈ Inc {p : P // A p}) :
    cmap (Subtype.val) x ∈ IncOn A := by
  refine AddSubgroup.closure_induction (p := fun y _ => cmap (Subtype.val) y ∈ IncOn A)
    ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, hl, rfl⟩
    rw [cmap_of]
    refine of_mem_incOn ?_ ?_
    · exact List.isChain_map_of_isChain (Subtype.val : {p : P // A p} → P) (fun _ _ h => h) hl
    · intro a ha
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
      exact b.2
  · simp
  · intro y z _ _ hy hz
    simpa using AddSubgroup.add_mem _ hy hz
  · simp

theorem exists_preimage_of_mem_incOn {x : Ch P} (hx : x ∈ IncOn A) :
    ∃ x' ∈ Inc {p : P // A p}, cmap (Subtype.val) x' = x := by
  refine AddSubgroup.closure_induction
    (p := fun y _ => ∃ y' ∈ Inc {p : P // A p}, cmap (Subtype.val) y' = y) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, ⟨hl, hA⟩, rfl⟩
    refine ⟨FreeAbelianGroup.of (l.attachWith A hA), of_mem_inc ?_, ?_⟩
    · have hmap : (l.attachWith A hA).map Subtype.val = l := by
        simp
      have : List.IsChain (· ≤ ·) ((l.attachWith A hA).map Subtype.val) := by
        rw [hmap]; exact hl
      exact List.isChain_of_isChain_map (f := (Subtype.val : {p // A p} → P))
        (fun _ _ h => h) this
    · simp
  · exact ⟨0, AddSubgroup.zero_mem _, by simp⟩
  · rintro y z _ _ ⟨y', hy', rfl⟩ ⟨z', hz', rfl⟩
    exact ⟨y' + z', AddSubgroup.add_mem _ hy' hz', by simp⟩
  · rintro y _ ⟨y', hy', rfl⟩
    exact ⟨-y', AddSubgroup.neg_mem _ hy', by simp⟩

omit [Preorder P] in
/-- The pushforward along the inclusion of a nonempty subposet is injective: it has the
retraction induced by any retraction of the inclusion of types. -/
theorem cmap_val_injective (hne : ∃ p : P, A p) :
    Function.Injective (cmap (Subtype.val : {p : P // A p} → P)) := by
  classical
  obtain ⟨p₀, hp₀⟩ := hne
  set r : P → {p : P // A p} := fun p => if h : A p then ⟨p, h⟩ else ⟨p₀, hp₀⟩ with hr
  have hcomp : ∀ q : {p : P // A p}, r q.1 = q := by
    intro q
    simp [hr, q.2]
  intro x y hxy
  have h : ∀ z : Ch {p : P // A p}, cmap r (cmap (Subtype.val) z) = z := by
    intro z
    refine ext_apply (F := (cmap r).comp (cmap (Subtype.val : {p : P // A p} → P)))
      (G := AddMonoidHom.id _) ?_ z
    intro l
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, cmap_of, List.map_map,
      AddMonoidHom.id_apply]
    congr 1
    have : (fun q : {p : P // A p} => r q.1) = id := by
      funext q; exact hcomp q
    simp [Function.comp_def, this]
  have := congrArg (cmap r) hxy
  rwa [h, h] at this

/-- **Transfer of acyclicity from the subposet to the chains supported on it.** -/
theorem acyclicIn_of_subtype (hne : ∃ p : P, A p)
    (hsub : ∀ x ∈ Inc {p : P // A p}, bdry x = 0 →
      ∃ y ∈ Inc {p : P // A p}, bdry y = x) :
    AcyclicIn A := by
  intro x hx hcyc
  obtain ⟨x', hx', rfl⟩ := exists_preimage_of_mem_incOn A hx
  have hcyc' : bdry x' = 0 := by
    refine cmap_val_injective A hne ?_
    rw [cmap_bdry, hcyc, map_zero]
  obtain ⟨y', hy', hdy'⟩ := hsub x' hx' hcyc'
  exact ⟨cmap (Subtype.val) y', cmap_val_mem_incOn A hy', by rw [← cmap_bdry, hdy']⟩

end Transfer

end Nerve
end FiniteChains

namespace FiniteChains
namespace Nerve

universe u

variable {P : Type u} [Preorder P] {Q : Type u} [Preorder Q]

/-! ### Pushforward along a monotone map -/

omit [Preorder P] [Preorder Q] in
theorem cmap_comp (f : P → Q) {R : Type u} (g : Q → R) (x : Ch P) :
    cmap g (cmap f x) = cmap (g ∘ f) x := by
  refine ext_apply (F := (cmap g).comp (cmap f)) ?_ x
  simp

/-- The image of an increasing chain under a monotone map all of whose values satisfy `B` is
supported on `B`. -/
theorem cmap_mem_incOn_of_maps {f : P → Q} (hf : Monotone f) {B : Q → Prop}
    (hB : ∀ p : P, B (f p)) {x : Ch P} (hx : x ∈ Inc P) : cmap f x ∈ IncOn B := by
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, hl, rfl⟩
    rw [cmap_of]
    refine of_mem_incOn (List.isChain_map_of_isChain f (fun _ _ h => hf h) hl) ?_
    intro a ha
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
    exact hB b
  · simp
  · intro y z _ _ hy hz
    simpa using AddSubgroup.add_mem _ hy hz
  · simp

/-- Pushforward along a monotone map of (possibly different) posets preserves increasing
chains. -/
theorem cmap_mem_inc_of_monotone {f : P → Q} (hf : Monotone f) {x : Ch P} (hx : x ∈ Inc P) :
    cmap f x ∈ Inc Q :=
  incOn_le_inc _
    (cmap_mem_incOn_of_maps (B := fun _ : Q => True) hf (fun _ => trivial) hx)

/-- Acyclicity is transported along an order isomorphism of posets. -/
theorem exists_bdry_eq_of_cycle_of_orderIso (e : P ≃o Q)
    (h : ∀ x ∈ Inc Q, bdry x = 0 → ∃ y ∈ Inc Q, bdry y = x) :
    ∀ x ∈ Inc P, bdry x = 0 → ∃ y ∈ Inc P, bdry y = x := by
  intro x hx hcyc
  have hx'  := cmap_mem_inc_of_monotone e.monotone hx
  have hcyc' : bdry (cmap e x) = 0 := by rw [← cmap_bdry, hcyc, map_zero]
  obtain ⟨y, hy, hdy⟩ := h _ hx' hcyc'
  refine ⟨cmap e.symm y,
    cmap_mem_inc_of_monotone e.symm.monotone hy, ?_⟩
  rw [← cmap_bdry, hdy, cmap_comp]
  have hcomp : (e.symm ∘ e) = id := by
    funext p
    simp
  rw [hcomp, cmap_id]

/-! ### Relative acyclicity -/

/-- **Acyclicity of `U` relative to `B`**: every increasing cycle supported on `U` differs, by
the boundary of an increasing chain supported on `U`, from an increasing cycle supported on
`B`. -/
def AcyclicRelIn (U B : P → Prop) : Prop :=
  ∀ z ∈ IncOn U, bdry z = 0 →
    ∃ c ∈ IncOn B, ∃ y ∈ IncOn U, bdry c = 0 ∧ z = c + bdry y

/-- An acyclic piece is relatively acyclic over any subcomplex. -/
theorem acyclicRelIn_of_acyclicIn {U B : P → Prop} (hU : AcyclicIn U) : AcyclicRelIn U B := by
  intro z hz hcyc
  obtain ⟨y, hy, hdy⟩ := hU z hz hcyc
  exact ⟨0, AddSubgroup.zero_mem _, y, hy, by simp, by rw [hdy, zero_add]⟩

/-- **A piece that retracts onto part of `Base`, below the identity, is acyclic relative to
`Base`.**  This is the prism homotopy between the identity and the retraction: every cycle of
the piece is its own image under the retraction plus a boundary, and that image is a cycle
supported on `Base`.  It is exactly the situation of a modified chamber, which retracts onto its
copy of the base poset. -/
theorem acyclicRelIn_of_retraction {U Base : P → Prop} (hne : ∃ p : P, U p)
    (ρ : {p : P // U p} → {p : P // U p}) (hmono : Monotone ρ) (hρle : ∀ q, ρ q ≤ q)
    (hbase : ∀ q, Base (ρ q).1) :
    AcyclicRelIn U Base := by
  intro z hz hcyc
  obtain ⟨z', hz', rfl⟩ := exists_preimage_of_mem_incOn U hz
  have hcyc' : bdry z' = 0 := by
    refine cmap_val_injective U hne ?_
    rw [cmap_bdry, hcyc, map_zero]
  have hid  :=
    bdry_prism_add_prism_bdry ρ id z'
  rw [hcyc', map_zero, add_zero, cmap_id] at hid
  have hyInc  :=
    prism_mem_inc hmono monotone_id hρle hz'
  have hcInc  := cmap_mem_inc hmono hz'
  refine ⟨cmap Subtype.val (cmap ρ z'), ?_, cmap Subtype.val (prism ρ id z'),
    cmap_val_mem_incOn U hyInc, ?_, ?_⟩
  · rw [cmap_comp]
    exact cmap_mem_incOn_of_maps
      (f := Subtype.val ∘ ρ) (fun _ _ h => hmono h)
      (fun q => hbase q) hz'
  · rw [← cmap_bdry, ← cmap_bdry, hcyc', map_zero, map_zero]
  · have h : z' = cmap ρ z' + bdry (prism ρ id z') := by
      rw [hid]
      abel
    rw [← cmap_bdry]
    rw [← map_add, ← h]

end Nerve
end FiniteChains

namespace FiniteChains
namespace Comb

universe u v

/-! ### Edge paths -/

variable {V E : Type*}

/-- The initial vertex of an oriented edge: `(e, true)` is `e`, `(e, false)` is `e`
reversed. -/
def germSrc (src tgt : E → V) (e : E × Bool) : V := if e.2 then src e.1 else tgt e.1

/-- The terminal vertex of an oriented edge. -/
def germTgt (src tgt : E → V) (e : E × Bool) : V := if e.2 then tgt e.1 else src e.1

@[simp] theorem germSrc_true (src tgt : E → V) (e : E) : germSrc src tgt (e, true) = src e := rfl
@[simp] theorem germSrc_false (src tgt : E → V) (e : E) : germSrc src tgt (e, false) = tgt e := rfl
@[simp] theorem germTgt_true (src tgt : E → V) (e : E) : germTgt src tgt (e, true) = tgt e := rfl
@[simp] theorem germTgt_false (src tgt : E → V) (e : E) : germTgt src tgt (e, false) = src e := rfl

/-- `IsPath src tgt p a b` : the list of oriented edges `p` is an edge path from `a`
to `b`. -/
def IsPath (src tgt : E → V) : List (E × Bool) → V → V → Prop
  | [], a, b => a = b
  | e :: p, a, b => a = germSrc src tgt e ∧ IsPath src tgt p (germTgt src tgt e) b

@[simp] theorem isPath_nil (src tgt : E → V) (a b : V) :
    IsPath src tgt [] a b ↔ a = b := Iff.rfl

@[simp] theorem isPath_cons (src tgt : E → V) (e : E × Bool) (p : List (E × Bool)) (a b : V) :
    IsPath src tgt (e :: p) a b ↔
      a = germSrc src tgt e ∧ IsPath src tgt p (germTgt src tgt e) b := Iff.rfl

theorem IsPath.append {src tgt : E → V} {p q : List (E × Bool)} {a b c : V}
    (hp : IsPath src tgt p a b) (hq : IsPath src tgt q b c) : IsPath src tgt (p ++ q) a c := by
  induction p generalizing a with
  | nil => simp_all
  | cons e p ih => simp_all

/-! ### Combinatorial two-complexes -/

/-- A combinatorial two-complex: a graph `(V, E)` together with two-cells `F`, each
attached along a closed edge path. -/
structure Complex2 : Type (u + 1) where
  /-- Vertices. -/
  V : Type u
  /-- Oriented edges. -/
  E : Type u
  /-- Two-cells. -/
  F : Type u
  /-- Initial vertex of an edge. -/
  src : E → V
  /-- Terminal vertex of an edge. -/
  tgt : E → V
  /-- Basepoint of a two-cell. -/
  base : F → V
  /-- Attaching path of a two-cell. -/
  att : F → List (E × Bool)
  /-- The attaching path is a loop at the basepoint. -/
  att_isLoop : ∀ f, IsPath src tgt (att f) (base f) (base f)

variable (X : Complex2.{u})

/-- The complex is path connected. -/
def IsConnected : Prop := ∀ a b : X.V, ∃ p, IsPath X.src X.tgt p a b

/-! ### The cellular chain complex -/

/-- The one-chain carried by an edge path: the signed sum of its edges. -/
def pathChain (p : List (E × Bool)) : E →₀ ℤ :=
  (p.map (fun e => if e.2 then Finsupp.single e.1 (1 : ℤ) else -Finsupp.single e.1 (1 : ℤ))).sum

@[simp] theorem pathChain_nil : pathChain ([] : List (E × Bool)) = 0 := rfl

theorem pathChain_cons (e : E × Bool) (p : List (E × Bool)) :
    pathChain (e :: p) =
      (if e.2 then Finsupp.single e.1 (1 : ℤ) else -Finsupp.single e.1 (1 : ℤ)) +
        pathChain p := rfl

/-- The first boundary `∂₁ e = tgt e - src e`. -/
def bdry1 : (X.E →₀ ℤ) →ₗ[ℤ] (X.V →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun e => Finsupp.single (X.tgt e) (1 : ℤ)
    - Finsupp.single (X.src e) (1 : ℤ))

/-- The second boundary: the signed sum of the edges of the attaching path. -/
def bdry2 : (X.F →₀ ℤ) →ₗ[ℤ] (X.E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun f => pathChain (X.att f))

/-- The augmentation `C₀ → ℤ`. -/
def augC : (X.V →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => (1 : ℤ))

variable {X}

@[simp] theorem bdry1_single (e : X.E) (n : ℤ) :
    bdry1 X (Finsupp.single e n) =
      n • (Finsupp.single (X.tgt e) (1 : ℤ) - Finsupp.single (X.src e) (1 : ℤ)) := by
  simp [bdry1]

@[simp] theorem bdry2_single (f : X.F) (n : ℤ) :
    bdry2 X (Finsupp.single f n) = n • pathChain (X.att f) := by
  simp [bdry2]

@[simp] theorem augC_single (a : X.V) (n : ℤ) : augC X (Finsupp.single a n) = n := by
  simp [augC]

/-- The boundary of the chain of an edge path is the difference of its endpoints. -/
theorem bdry1_pathChain_of_isPath {p : List (X.E × Bool)} {a b : X.V}
    (hp : IsPath X.src X.tgt p a b) :
    bdry1 X (pathChain p) = Finsupp.single b (1 : ℤ) - Finsupp.single a (1 : ℤ) := by
  induction p generalizing a with
  | nil =>
      cases hp
      simp
  | cons e p ih =>
      obtain ⟨ha, hrest⟩ := hp
      have h := ih hrest
      rw [pathChain_cons, map_add, h]
      cases e with
      | mk e b =>
          cases b <;> simp [ha, germSrc, germTgt]

/-- The chain complex condition `∂₁ ∘ ∂₂ = 0`. -/
theorem bdry1_bdry2 (c : X.F →₀ ℤ) : bdry1 X (bdry2 X c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp_all
  | single f n =>
      rw [bdry2_single, map_smul, bdry1_pathChain_of_isPath (X.att_isLoop f)]
      simp

/-- Acyclicity of a combinatorial two-complex: `H₂ = H₁ = H̃₀ = 0`. -/
structure IsAcyclic (X : Complex2.{u}) : Prop where
  /-- `H₂ = ker ∂₂ = 0`. -/
  h2 : Function.Injective (bdry2 X)
  /-- `H₁ = 0`: every cycle is a boundary. -/
  h1 : ∀ c : X.E →₀ ℤ, bdry1 X c = 0 → ∃ u : X.F →₀ ℤ, bdry2 X u = c
  /-- `H̃₀ = 0`: every zero-chain of augmentation `0` is a boundary. -/
  h0 : ∀ c : X.V →₀ ℤ, augC X c = 0 → ∃ u : X.E →₀ ℤ, bdry1 X u = c

/-! ### Cellular maps and coverings -/

/-- A cellular map of combinatorial two-complexes. -/
structure Hom (X Y : Complex2.{u}) where
  /-- Action on vertices. -/
  onV : X.V → Y.V
  /-- Action on edges. -/
  onE : X.E → Y.E
  /-- Action on two-cells. -/
  onF : X.F → Y.F
  src_onE : ∀ e, Y.src (onE e) = onV (X.src e)
  tgt_onE : ∀ e, Y.tgt (onE e) = onV (X.tgt e)
  base_onF : ∀ f, Y.base (onF f) = onV (X.base f)
  att_onF : ∀ f, Y.att (onF f) = (X.att f).map (fun eb => (onE eb.1, eb.2))

variable {X Y : Complex2.{u}}

theorem germSrc_onE (p : Hom X Y) (eb : X.E × Bool) :
    germSrc Y.src Y.tgt (p.onE eb.1, eb.2) = p.onV (germSrc X.src X.tgt eb) := by
  obtain ⟨e, b⟩ := eb
  cases b <;> simp [germSrc, p.src_onE, p.tgt_onE]

/-- The germs of oriented edges at a vertex. -/
def Germ (X : Complex2.{u}) (a : X.V) : Type u :=
  {eb : X.E × Bool // germSrc X.src X.tgt eb = a}

/-- A cellular map sends germs at `a` to germs at the image of `a`. -/
def germMap (p : Hom X Y) (a : X.V) : Germ X a → Germ Y (p.onV a) :=
  fun eb => ⟨(p.onE eb.1.1, eb.1.2), by rw [germSrc_onE p eb.1, eb.2]⟩

/-- The two-cells of `X` mapped to a two-cell of `Y` together with a lift of its
basepoint. -/
def cellMap (p : Hom X Y) : X.F → {gv : Y.F × X.V // Y.base gv.1 = p.onV gv.2} :=
  fun f => ⟨(p.onF f, X.base f), p.base_onF f⟩

/-- A combinatorial covering map: onto on vertices, a bijection on germs at each vertex,
and unique lifting of two-cells once a lift of the basepoint is chosen. -/
structure IsCovering (p : Hom X Y) : Prop where
  surjV : Function.Surjective p.onV
  germ : ∀ a : X.V, Function.Bijective (germMap p a)
  cell : Function.Bijective (cellMap p)

/-- An action of a group `Q` on a combinatorial two-complex by cellular automorphisms. -/
structure DeckAction (X : Complex2.{u}) (Q : Type v) [Group Q] where
  /-- Action on vertices. -/
  smulV : Q → X.V → X.V
  /-- Action on edges. -/
  smulE : Q → X.E → X.E
  /-- Action on two-cells. -/
  smulF : Q → X.F → X.F
  one_smulV : ∀ a, smulV 1 a = a
  mul_smulV : ∀ q q' a, smulV (q * q') a = smulV q (smulV q' a)
  one_smulE : ∀ e, smulE 1 e = e
  mul_smulE : ∀ q q' e, smulE (q * q') e = smulE q (smulE q' e)
  one_smulF : ∀ f, smulF 1 f = f
  mul_smulF : ∀ q q' f, smulF (q * q') f = smulF q (smulF q' f)
  src_smul : ∀ q e, X.src (smulE q e) = smulV q (X.src e)
  tgt_smul : ∀ q e, X.tgt (smulE q e) = smulV q (X.tgt e)
  base_smul : ∀ q f, X.base (smulF q f) = smulV q (X.base f)
  att_smul : ∀ q f, X.att (smulF q f) = (X.att f).map (fun eb => (smulE q eb.1, eb.2))

/-- The covering `p` is regular with deck group `Q`: the action preserves the fibres of
`p` and is simply transitive on each of them. -/
structure IsRegular (p : Hom X Y) {Q : Type v} [Group Q] (A : DeckAction X Q) : Prop where
  compat : ∀ q a, p.onV (A.smulV q a) = p.onV a
  simply_transitive : ∀ a b : X.V, p.onV a = p.onV b → ∃! q : Q, A.smulV q a = b

end Comb
end FiniteChains

namespace FiniteChains
namespace Comb

universe u v

variable {X Y Z : Complex2.{u}}

/-! ### Edge paths -/

/-- The reverse of an oriented edge. -/
def revGerm (eb : X.E × Bool) : X.E × Bool := (eb.1, !eb.2)

@[simp] theorem revGerm_revGerm (eb : X.E × Bool) : revGerm (X := X) (revGerm eb) = eb := by simp_all [revGerm]

@[simp] theorem germSrc_revGerm (eb : X.E × Bool) :
    germSrc X.src X.tgt (revGerm (X := X) eb) = germTgt X.src X.tgt eb := by
  cases eb with
  | mk e b => cases b <;> rfl

@[simp] theorem germTgt_revGerm (eb : X.E × Bool) :
    germTgt X.src X.tgt (revGerm (X := X) eb) = germSrc X.src X.tgt eb := by
  cases eb with
  | mk e b => cases b <;> rfl

/-- The reverse of an edge path. -/
def revPath (p : List (X.E × Bool)) : List (X.E × Bool) := (p.map revGerm).reverse

@[simp] theorem revPath_nil : revPath ([] : List (X.E × Bool)) = [] := rfl

@[simp] theorem revPath_cons (eb : X.E × Bool) (p : List (X.E × Bool)) :
    revPath (eb :: p) = revPath p ++ [revGerm eb] := by
  simp [revPath]

theorem revPath_append (p q : List (X.E × Bool)) :
    revPath (p ++ q) = revPath q ++ revPath p := by
  simp [revPath]

@[simp] theorem revPath_revPath (p : List (X.E × Bool)) : revPath (revPath p) = p := by
  induction p with
  | nil => rfl
  | cons eb p ih => simp [revPath_append, ih]

/-- Paths split along a concatenation. -/
theorem isPath_append_iff {p q : List (X.E × Bool)} {a c : X.V} :
    IsPath X.src X.tgt (p ++ q) a c ↔
      ∃ b, IsPath X.src X.tgt p a b ∧ IsPath X.src X.tgt q b c := by
  induction p generalizing a with
  | nil => simp
  | cons eb p ih =>
      constructor
      · simp_all
      · rintro ⟨b, ⟨ha, hb1⟩, hb2⟩
        exact ⟨ha, ih.mpr ⟨b, hb1, hb2⟩⟩

theorem isPath_single (eb : X.E × Bool) :
    IsPath X.src X.tgt [eb] (germSrc X.src X.tgt eb) (germTgt X.src X.tgt eb) := ⟨rfl, rfl⟩

theorem isPath_revPath {p : List (X.E × Bool)} {a b : X.V}
    (hp : IsPath X.src X.tgt p a b) : IsPath X.src X.tgt (revPath p) b a := by
  induction p generalizing a with
  | nil => simp_all
  | cons eb p ih =>
      obtain ⟨ha, hrest⟩ := hp
      subst ha
      rw [revPath_cons]
      refine isPath_append_iff.mpr ⟨germTgt X.src X.tgt eb, ih hrest, ?_⟩
      refine ⟨?_, ?_⟩ <;> simp

/-! ### Elementary cancellations and homotopy -/

/-- The elementary cancellations of edge paths: deleting a backtrack `e e⁻¹`, and deleting
the attaching loop of a two-cell.  Both are allowed at an arbitrary position. -/
def Cancels (X : Complex2.{u}) (l l' : List (X.E × Bool)) : Prop :=
  (∃ (p q : List (X.E × Bool)) (eb : X.E × Bool),
      l = p ++ eb :: revGerm eb :: q ∧ l' = p ++ q) ∨
  (∃ (p q : List (X.E × Bool)) (f : X.F), l = p ++ X.att f ++ q ∧ l' = p ++ q)

/-- One elementary homotopy between two edge paths with the same endpoints. -/
def Step (X : Complex2.{u}) (a b : X.V) (l l' : List (X.E × Bool)) : Prop :=
  IsPath X.src X.tgt l a b ∧ IsPath X.src X.tgt l' a b ∧ Cancels X l l'

/-- **Combinatorial homotopy** of edge paths from `a` to `b`. -/
def Htpy (X : Complex2.{u}) (a b : X.V) (p q : List (X.E × Bool)) : Prop :=
  Relation.ReflTransGen (fun l l' => Step X a b l l' ∨ Step X a b l' l) p q

namespace Htpy

variable {a b c : X.V}

theorem refl (p : List (X.E × Bool)) : Htpy X a b p p := Relation.ReflTransGen.refl

theorem trans {p q r : List (X.E × Bool)} (h : Htpy X a b p q) (h' : Htpy X a b q r) :
    Htpy X a b p r := Relation.ReflTransGen.trans h h'

theorem symm {p q : List (X.E × Bool)} (h : Htpy X a b p q) : Htpy X a b q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep.symm) ih

theorem of_step {p q : List (X.E × Bool)} (h : Step X a b p q) : Htpy X a b p q :=
  Relation.ReflTransGen.single (Or.inl h)

/-- Homotopy preserves the property of being a path with the given endpoints. -/
theorem isPath {p q : List (X.E × Bool)} (h : Htpy X a b p q)
    (hp : IsPath X.src X.tgt p a b) : IsPath X.src X.tgt q a b := by
  induction h with
  | refl => exact hp
  | tail _ hstep _ =>
      rcases hstep with h | h
      · exact h.2.1
      · exact h.1

end Htpy

/-- Elementary cancellations survive inside a longer path. -/
theorem Cancels.append {l l' : List (X.E × Bool)} (h : Cancels X l l')
    (r s : List (X.E × Bool)) : Cancels X (r ++ l ++ s) (r ++ l' ++ s) := by
  rcases h with ⟨p, q, eb, hl, hl'⟩ | ⟨p, q, f, hl, hl'⟩
  · refine Or.inl ⟨r ++ p, q ++ s, eb, ?_, ?_⟩
    · rw [hl]; simp
    · rw [hl']; simp
  · refine Or.inr ⟨r ++ p, q ++ s, f, ?_, ?_⟩
    · rw [hl]; simp
    · rw [hl']; simp

theorem Step.append {a b c d : X.V} {l l' : List (X.E × Bool)} (h : Step X a b l l')
    {r s : List (X.E × Bool)} (hr : IsPath X.src X.tgt r c a) (hs : IsPath X.src X.tgt s b d) :
    Step X c d (r ++ l ++ s) (r ++ l' ++ s) := by
  refine ⟨?_, ?_, h.2.2.append r s⟩
  · rw [List.append_assoc]
    exact isPath_append_iff.mpr ⟨a, hr, isPath_append_iff.mpr ⟨b, h.1, hs⟩⟩
  · rw [List.append_assoc]
    exact isPath_append_iff.mpr ⟨a, hr, isPath_append_iff.mpr ⟨b, h.2.1, hs⟩⟩

theorem Htpy.congr_append {a b c d : X.V} {p q : List (X.E × Bool)} (h : Htpy X a b p q)
    {r s : List (X.E × Bool)} (hr : IsPath X.src X.tgt r c a) (hs : IsPath X.src X.tgt s b d) :
    Htpy X c d (r ++ p ++ s) (r ++ q ++ s) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      refine Relation.ReflTransGen.tail ih ?_
      rcases hstep with h | h
      · exact Or.inl (h.append hr hs)
      · exact Or.inr (h.append hr hs)

/-- Homotopies may be concatenated. -/
theorem Htpy.append_congr {a b c : X.V} {p p' q q' : List (X.E × Bool)}
    (hp : IsPath X.src X.tgt p a b) (hq : IsPath X.src X.tgt q b c)
    (h : Htpy X a b p p') (h' : Htpy X b c q q') :
    Htpy X a c (p ++ q) (p' ++ q') := by
  have hp'  := h.isPath hp
  have h1 : Htpy X a c (p ++ q) (p' ++ q) := by
    simpa using h.congr_append (r := []) rfl hq
  have h2 : Htpy X a c (p' ++ q) (p' ++ q') := by
    simpa using h'.congr_append (s := []) hp' rfl
  exact h1.trans h2

/-! ### Cancelling a path against its reverse -/

theorem htpy_append_revPath {p : List (X.E × Bool)} {a b : X.V}
    (hp : IsPath X.src X.tgt p a b) : Htpy X a a (p ++ revPath p) [] := by
  induction p generalizing a with
  | nil => cases hp; exact Relation.ReflTransGen.refl
  | cons eb p ih =>
      obtain ⟨ha, hrest⟩ := hp
      subst ha
      set s := germSrc X.src X.tgt eb with hs
      set t := germTgt X.src X.tgt eb with ht
      have hih  := ih hrest
      have hcongr : Htpy X s s ([eb] ++ (p ++ revPath p) ++ [revGerm eb])
          ([eb] ++ [] ++ [revGerm eb]) :=
        hih.congr_append (isPath_single eb) (by refine ⟨?_, ?_⟩ <;> simp [hs, ht])
      have hrw : (eb :: p) ++ revPath (eb :: p) = [eb] ++ (p ++ revPath p) ++ [revGerm eb] := by
        simp
      have hlast : Htpy X s s [eb, revGerm eb] [] := by
        refine Htpy.of_step ⟨?_, rfl, Or.inl ⟨[], [], eb, rfl, rfl⟩⟩
        exact ⟨rfl, by simp, by simp [hs]⟩
      rw [hrw]
      refine hcongr.trans ?_
      simpa using hlast

theorem htpy_revPath_append {p : List (X.E × Bool)} {a b : X.V}
    (hp : IsPath X.src X.tgt p a b) : Htpy X b b (revPath p ++ p) [] := by
  have h := htpy_append_revPath (isPath_revPath hp)
  simpa using h

/-- Homotopy is compatible with reversal of paths. -/
theorem htpy_revPath {p q : List (X.E × Bool)} {a b : X.V} (hp : IsPath X.src X.tgt p a b)
    (h : Htpy X a b p q) : Htpy X b a (revPath p) (revPath q) := by
  have hq  := h.isPath hp
  have hrp  := isPath_revPath hp
  have hrq  := isPath_revPath hq
  have hnil : IsPath X.src X.tgt [] a a := rfl
  -- `revPath p ++ [] ~ revPath p ++ (q ++ revPath q)`
  have h1  :=
    Htpy.append_congr hrp hnil (Htpy.refl _) (htpy_append_revPath hq).symm
  -- `revPath p ++ q ~ revPath p ++ p ~ []`
  have h3  :=
    (Htpy.append_congr hrp hq (Htpy.refl _) h.symm).trans (htpy_revPath_append hp)
  have h2  :=
    Htpy.append_congr (isPath_append_iff.mpr ⟨a, hrp, hq⟩) hrq h3 (Htpy.refl _)
  have hfinal : Htpy X b a (revPath p ++ []) (revPath q) := by
    refine h1.trans ?_
    rw [← List.append_assoc]
    simpa using h2
  simpa using hfinal

/-! ### The fundamental group -/

/-- Edge loops at a vertex. -/
def Loop (X : Complex2.{u}) (a : X.V) : Type u :=
  {p : List (X.E × Bool) // IsPath X.src X.tgt p a a}

instance loopSetoid (X : Complex2.{u}) (a : X.V) : Setoid (Loop X a) where
  r p q := Htpy X a a p.1 q.1
  iseqv := ⟨fun p => Htpy.refl p.1, fun h => h.symm, fun h h' => h.trans h'⟩

/-- The **fundamental group** of a combinatorial two-complex at a vertex: edge loops modulo
combinatorial homotopy. -/
def Pi1 (X : Complex2.{u}) (a : X.V) : Type u := Quotient (loopSetoid X a)

namespace Pi1

variable {a : X.V}

/-- The class of a loop. -/
def mk (p : Loop X a) : Pi1 X a := Quotient.mk _ p

instance : One (Pi1 X a) := ⟨mk ⟨[], rfl⟩⟩

instance : Mul (Pi1 X a) :=
  ⟨Quotient.map₂ (fun p q => ⟨p.1 ++ q.1, isPath_append_iff.mpr ⟨a, p.2, q.2⟩⟩)
    (fun p _ h q _ h' => Htpy.append_congr p.2 q.2 h h')⟩

instance : Inv (Pi1 X a) :=
  ⟨Quotient.map (fun p => ⟨revPath p.1, isPath_revPath p.2⟩)
    (fun p _ h => htpy_revPath p.2 h)⟩

instance : Group (Pi1 X a) where
  mul_assoc := by
    rintro ⟨p⟩ ⟨q⟩ ⟨r⟩
    apply Quotient.sound
    change Htpy X a a ((p.1 ++ q.1) ++ r.1) (p.1 ++ (q.1 ++ r.1))
    rw [List.append_assoc]
    exact Htpy.refl _
  one_mul := by
    rintro ⟨p⟩
    exact Quotient.sound (Htpy.refl _)
  mul_one := by
    rintro ⟨p⟩
    apply Quotient.sound
    change Htpy X a a (p.1 ++ []) p.1
    rw [List.append_nil]
    exact Htpy.refl _
  inv_mul_cancel := by
    rintro ⟨p⟩
    exact Quotient.sound (htpy_revPath_append p.2)

end Pi1

/-- A complex is **simply connected** if every edge loop is null-homotopic. -/
def SimplyConnected (X : Complex2.{u}) : Prop :=
  ∀ (a : X.V) (p : List (X.E × Bool)), IsPath X.src X.tgt p a a → Htpy X a a p []

/-! ### Functoriality -/

/-- The image of an edge path under a cellular map. -/
def mapPath (h : Hom X Y) (p : List (X.E × Bool)) : List (Y.E × Bool) :=
  p.map (fun eb => (h.onE eb.1, eb.2))

@[simp] theorem mapPath_nil (h : Hom X Y) : mapPath h ([] : List (X.E × Bool)) = [] := rfl

@[simp] theorem mapPath_append (h : Hom X Y) (p q : List (X.E × Bool)) :
    mapPath h (p ++ q) = mapPath h p ++ mapPath h q := by
  simp [mapPath]

theorem germTgt_onE (h : Hom X Y) (eb : X.E × Bool) :
    germTgt Y.src Y.tgt (h.onE eb.1, eb.2) = h.onV (germTgt X.src X.tgt eb) := by
  obtain ⟨e, b⟩ := eb
  cases b <;> simp [germTgt, h.src_onE, h.tgt_onE]

theorem isPath_mapPath (h : Hom X Y) {p : List (X.E × Bool)} {a b : X.V}
    (hp : IsPath X.src X.tgt p a b) : IsPath Y.src Y.tgt (mapPath h p) (h.onV a) (h.onV b) := by
  induction p generalizing a with
  | nil => simp_all
  | cons eb p ih =>
      obtain ⟨ha, hrest⟩ := hp
      subst ha
      refine ⟨(germSrc_onE h eb).symm, ?_⟩
      have := ih hrest
      rwa [germTgt_onE h eb]

theorem mapPath_htpy (h : Hom X Y) {a b : X.V} {p q : List (X.E × Bool)}
    (hpq : Htpy X a b p q) :
    Htpy Y (h.onV a) (h.onV b) (mapPath h p) (mapPath h q) := by
  have hstep : ∀ l l' : List (X.E × Bool), Step X a b l l' →
      Step Y (h.onV a) (h.onV b) (mapPath h l) (mapPath h l') := by
    rintro l l' ⟨hl, hl', hc⟩
    refine ⟨isPath_mapPath h hl, isPath_mapPath h hl', ?_⟩
    rcases hc with ⟨p', q', eb, hlEq, hl'Eq⟩ | ⟨p', q', f, hlEq, hl'Eq⟩
    · refine Or.inl ⟨mapPath h p', mapPath h q', (h.onE eb.1, eb.2), ?_, ?_⟩
      · rw [hlEq]; simp [mapPath, revGerm]
      · rw [hl'Eq]; simp
    · refine Or.inr ⟨mapPath h p', mapPath h q', h.onF f, ?_, ?_⟩
      · rw [hlEq]
        have hatt : mapPath h (X.att f) = Y.att (h.onF f) := by
          rw [h.att_onF f]; rfl
        simp [hatt]
      · rw [hl'Eq]; simp
  induction hpq with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
      rcases hs with hel | hel
      · exact ih.trans (Htpy.of_step (hstep _ _ hel))
      · exact ih.trans (Htpy.of_step (hstep _ _ hel)).symm

/-- The homomorphism induced by a cellular map on fundamental groups. -/
def pi1Map (h : Hom X Y) (a : X.V) : Pi1 X a →* Pi1 Y (h.onV a) where
  toFun := Quotient.map (fun p => ⟨mapPath h p.1, isPath_mapPath h p.2⟩)
    (fun _ _ hpq => mapPath_htpy h hpq)
  map_one' := Quotient.sound (Htpy.refl (X := Y) (a := h.onV a) (b := h.onV a) [])
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩
    apply Quotient.sound
    change Htpy Y (h.onV a) (h.onV a) (mapPath h (p.1 ++ q.1))
      (mapPath h p.1 ++ mapPath h q.1)
    rw [mapPath_append]
    exact Htpy.refl _

/-- The map induced on fundamental groups by a cellular map is **trivial**: every loop of `X`
becomes null-homotopic in `Y`. -/
def Pi1Trivial (h : Hom X Y) : Prop :=
  ∀ (a : X.V) (p : List (X.E × Bool)), IsPath X.src X.tgt p a a →
    Htpy Y (h.onV a) (h.onV a) (mapPath h p) []

end Comb
end FiniteChains
