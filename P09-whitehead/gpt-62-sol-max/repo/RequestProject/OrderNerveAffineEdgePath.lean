module

public import RequestProject.OrderNerveRealizationContraction
public import RequestProject.OrderNerveFiniteCoordinates
public import RequestProject.OrderNerveRealizationMapCoordinates
public import RequestProject.SimpleLoopBoundaryHomeomorph

@[expose] public section

/-! Explicit affine paths along actual realization edges, with exact
barycentric coordinates and injectivity. Unlike an arbitrary chosen path
inside a simplex, these paths parametrize each edge exactly once.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology


namespace FiniteChains.Comb
open CategoryTheory Simplicial

variable {P : Type} [PartialOrder P]

def affineEdgeSimplex {a b : P} (h : a ≤ b) :
    (nerve P).obj (Opposite.op ⦋1⦌) := ComposableArrows.mk₁ (homOfLE h)

def affineEdgeEndpoint {a b : P} (h : a ≤ b) (i : Fin 2) :
    SimplexCategory.toTop.obj ⦋1⦌ :=
  Classical.choose (orderNerveRealizationVertex_mem_simplex (affineEdgeSimplex h) i)

theorem affineEdgeEndpoint_spec {a b : P} (h : a ≤ b) (i : Fin 2) :
    orderNerveRealizationSimplex P (affineEdgeSimplex h) (affineEdgeEndpoint h i) =
      orderNerveRealizationVertex ((affineEdgeSimplex h).obj i) :=
  Classical.choose_spec (orderNerveRealizationVertex_mem_simplex (affineEdgeSimplex h) i)

def orderNerveAffineEdgePath {a b : P} (h : a ≤ b) :
    Path (orderNerveRealizationVertex a) (orderNerveRealizationVertex b) where
  toFun t := orderNerveRealizationSimplex P (affineEdgeSimplex h)
    (topologicalSimplexBlend t (affineEdgeEndpoint h 0) (affineEdgeEndpoint h 1))
  continuous_toFun := (orderNerveRealizationSimplex P (affineEdgeSimplex h)).hom.continuous.comp
    (topologicalSimplexBlend_continuous.comp (continuous_id.prodMk
      (continuous_const.prodMk continuous_const)))
  source' := by
    apply orderNerveRealizationCoordinates_injective P
    funext p
    rw [orderNerveRealizationCoordinates_blend, affineEdgeEndpoint_spec, affineEdgeEndpoint_spec]
    simp
    rfl
  target' := by
    apply orderNerveRealizationCoordinates_injective P
    funext p
    rw [orderNerveRealizationCoordinates_blend, affineEdgeEndpoint_spec, affineEdgeEndpoint_spec]
    simp
    rfl

theorem orderNerveAffineEdgePath_coordinates {a b : P} (h : a ≤ b) (t : I) (p : P) :
    orderNerveRealizationCoordinates P (orderNerveAffineEdgePath h t) p =
      (1 - (t : ℝ)) * (if a = p then 1 else 0) + (t : ℝ) * (if b = p then 1 else 0) := by
  change orderNerveRealizationCoordinates P
    (orderNerveRealizationSimplex P (affineEdgeSimplex h)
      (topologicalSimplexBlend t (affineEdgeEndpoint h 0) (affineEdgeEndpoint h 1))) p = _
  rw [orderNerveRealizationCoordinates_blend, affineEdgeEndpoint_spec, affineEdgeEndpoint_spec]
  simp only [orderNerveRealizationCoordinates_vertex]
  rfl

def orderNerveComparablePath {a b : P} (h : a ≤ b ∨ b ≤ a) :
    Path (orderNerveRealizationVertex a) (orderNerveRealizationVertex b) :=
  if hab : a ≤ b then orderNerveAffineEdgePath hab
  else (orderNerveAffineEdgePath (h.resolve_left hab)).symm

theorem orderNerveComparablePath_coordinates {a b : P} (h : a ≤ b ∨ b ≤ a) (t : I) (p : P) :
    orderNerveRealizationCoordinates P (orderNerveComparablePath h t) p =
      (1 - (t : ℝ)) * (if a = p then 1 else 0) + (t : ℝ) * (if b = p then 1 else 0) := by
  by_cases hab : a ≤ b
  · simpa only [orderNerveComparablePath, dif_pos hab] using orderNerveAffineEdgePath_coordinates hab t p
  simp_all [orderNerveComparablePath, Path.symm_apply, orderNerveAffineEdgePath_coordinates, unitInterval.coe_symm_eq] <;> abel

theorem orderNerveAffineEdgePath_affine (v : P → ℝ) {a b : P}
    (h : a ≤ b) (t : I) :
    orderNerveAffineRealization v (orderNerveAffineEdgePath h t) =
      (1 - (t : ℝ)) * v a + (t : ℝ) * v b := by
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P (affineEdgeSimplex h)
    (topologicalSimplexBlend t (affineEdgeEndpoint h 0) (affineEdgeEndpoint h 1))) = _
  rw [orderNerveAffineRealization_simplex, orderNerveAffineSimplex_blend,
    ← orderNerveAffineRealization_simplex, ← orderNerveAffineRealization_simplex,
    affineEdgeEndpoint_spec, affineEdgeEndpoint_spec,
    orderNerveAffineRealization_vertex, orderNerveAffineRealization_vertex]
  rfl

theorem orderNerveComparablePath_affine (v : P → ℝ) {a b : P}
    (h : a ≤ b ∨ b ≤ a) (t : I) :
    orderNerveAffineRealization v (orderNerveComparablePath h t) =
      (1 - (t : ℝ)) * v a + (t : ℝ) * v b := by
  by_cases hab : a ≤ b
  · simpa only [orderNerveComparablePath, dif_pos hab] using
      orderNerveAffineEdgePath_affine v hab t
  · simp only [orderNerveComparablePath, dif_neg hab, Path.symm_apply, Function.comp_apply]
    rw [orderNerveAffineEdgePath_affine v (h.resolve_left hab), unitInterval.coe_symm_eq]
    ring

/-- Collapsing vertices is allowed: the affine path formula is natural for
every monotone map, including the actual letter-reading map. -/
theorem orderNerveComparablePath_natural {Q : Type} [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) {a b : P} (h : a ≤ b ∨ b ≤ a)
    (h' : f a ≤ f b ∨ f b ≤ f a) (t : I) :
    orderNerveRealizationMap f hf (orderNerveComparablePath h t) =
      orderNerveComparablePath h' t := by
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  change orderNerveAffineRealization (fun z => if z = q then 1 else 0)
    (orderNerveRealizationMap f hf (orderNerveComparablePath h t)) = _
  rw [orderNerveAffineRealization_natural, orderNerveComparablePath_affine,
    orderNerveComparablePath_coordinates]
  rfl

theorem orderNerveComparablePath_injective {a b : P} (h : a ≤ b ∨ b ≤ a) (hne : a ≠ b) :
    Function.Injective (orderNerveComparablePath h) := by
  intro s t hst
  have hcoord := congrArg (fun x => orderNerveRealizationCoordinates P x b) hst
  simp only [orderNerveComparablePath_coordinates, if_neg hne, ite_true,
    mul_zero, mul_one, zero_add] at hcoord
  exact Subtype.ext hcoord

theorem orderNerveComparablePath_of_support [Fintype P] {a b : P}
    (h : a ≤ b ∨ b ≤ a) (hne : a ≠ b) (x : orderNerveRealization P)
    (hx : ∀ p, p ≠ a → p ≠ b → orderNerveRealizationCoordinates P x p = 0) :
    ∃ t : I, orderNerveComparablePath h t = x := by
  let c := orderNerveRealizationCoordinates P x
  have hsum : c a + c b = 1 := by
    calc
      c a + c b = ∑ p ∈ ({a, b}), c p := by simp [hne]
      _ = ∑ p : P, c p := by
        grind [Finset.sum_subset]
      _ = 1 := orderNerveRealizationCoordinates_sum x
  have ha := orderNerveRealizationCoordinates_nonneg x a
  have hb := orderNerveRealizationCoordinates_nonneg x b
  let t : I := ⟨c b, hb, by linarith⟩
  refine ⟨t, ?_⟩
  apply orderNerveRealizationCoordinates_injective P
  funext p
  rw [orderNerveComparablePath_coordinates]
  by_cases hpa : p = a
  · subst p
    simp only [ite_true, if_neg hne.symm, mul_one, mul_zero, add_zero]
    linarith
  · by_cases hpb : p = b
    · subst p
      simp only [if_neg hne, ite_true, mul_zero, mul_one, zero_add]
      rfl
    · rw [if_neg (Ne.symm hpa), if_neg (Ne.symm hpb), hx p hpa hpb]
      ring

end FiniteChains.Comb
