module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.SquareBoundaryNormHomeomorph

@[expose] public section

/-! Move both endpoints of a path along prescribed paths, extending the
motion continuously over the whole interval by the actual disk HEP. -/

noncomputable section
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
  let H  :=
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

/-- Four paths with compatible endpoints on the sides of the square. -/
abbrev BoundaryPaths (v : SquareBoundary → X) :=
  ∀ s : SquareSide, Path (v (squareSideMap s 0)) (v (squareSideMap s 1))

def boundaryOfPaths {v : SquareBoundary → X} (p : BoundaryPaths v) : C(SquareBoundary, X) :=
  squareBoundaryPasting (fun s => (p s).toContinuousMap) v (by
    aesop)

@[simp] theorem boundaryOfPaths_side {v : SquareBoundary → X} (p : BoundaryPaths v)
    (s : SquareSide) (t : I) : boundaryOfPaths p (squareSideMap s t) = p s t :=
  squareBoundaryPasting_side ..

theorem squareBoundary_ext {f g : C(SquareBoundary, X)}
    (h : ∀ s t, f (squareSideMap s t) = g (squareSideMap s t)) : f = g := by
  ext z
  obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
  exact h s t

/-- Homotopies on the sides paste when they have the same corner tracks. -/
def squareBoundaryHomotopy {f g : C(SquareBoundary, X)}
    (H : SquareSide → C(I × I, X)) (V : I → SquareBoundary → X)
    (hv : ∀ s τ t, t = 0 ∨ t = 1 → H s (τ, t) = V τ (squareSideMap s t))
    (h₀ : ∀ s t, H s (0, t) = f (squareSideMap s t))
    (h₁ : ∀ s t, H s (1, t) = g (squareSideMap s t)) : f.Homotopy g where
  toContinuousMap := squareBoundaryHomotopyPasting H V hv
  map_zero_left z := by
    obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
    exact (squareBoundaryHomotopyPasting_side H V hv s 0 t).trans (h₀ s t)
  map_one_left z := by
    obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
    exact (squareBoundaryHomotopyPasting_side H V hv s 1 t).trans (h₁ s t)

/-- Extend individual motions of the square's corners to a homotopy of its boundary. -/
theorem homotopic_boundaryOfPaths (f : C(SquareBoundary, X)) (v : SquareBoundary → X)
    (p : ∀ z, Path (f z) (v z)) : ∃ l : BoundaryPaths v, f.Homotopic (boundaryOfPaths l) := by
  let E (s : SquareSide) := intervalEndpointExtension (f.comp (squareSideMap s))
    (p (squareSideMap s 0)) (p (squareSideMap s 1))
  let l : BoundaryPaths v := fun s => {
    toFun := fun t => (E s).map (1, t)
    continuous_toFun := (E s).map.continuous.comp (continuous_const.prodMk continuous_id)
    source' := ((E s).side_zero 1).trans (p (squareSideMap s 0)).target
    target' := ((E s).side_one 1).trans (p (squareSideMap s 1)).target }
  refine ⟨l, ⟨squareBoundaryHomotopy (fun s => (E s).map) (fun τ z => p z τ) ?_
    (fun s => (E s).zero) (fun s t => (boundaryOfPaths_side l s t).symm)⟩⟩
  rintro s τ t (rfl | rfl)
  · exact (E s).side_zero τ
  · exact (E s).side_one τ

theorem boundaryOfPaths_homotopic {v : SquareBoundary → X} {p q : BoundaryPaths v}
    (h : ∀ s, (p s).Homotopic (q s)) : (boundaryOfPaths p).Homotopic (boundaryOfPaths q) := by
  let H (s : SquareSide) := (h s).some
  refine ⟨squareBoundaryHomotopy (fun s => (H s).toHomotopy.toContinuousMap) (fun _ => v) ?_ ?_ ?_⟩
  · rintro s τ t (rfl | rfl)
    · exact (H s).source τ
    · exact (H s).target τ
  · intro s t
    rw [boundaryOfPaths_side]
    exact (H s).apply_zero t
  · intro s t
    rw [boundaryOfPaths_side]
    exact (H s).apply_one t

theorem boundaryOfPaths_comp {Y : Type} [TopologicalSpace Y] (f : C(X, Y))
    {v : SquareBoundary → X} (p : BoundaryPaths v) :
    f.comp (boundaryOfPaths p) = boundaryOfPaths (v := f ∘ v) (fun s => (p s).map f.continuous) :=
  squareBoundary_ext fun s t => by simp

end FiniteChains.RelativeAttachment
