module

public import PottsDiscontinuity.Duality.RectangleDualPotential
public import PottsDiscontinuity.Duality.RectangleFaceFlow
public import PottsDiscontinuity.Duality.NormalizedPotentialSpace

@[expose] public section

namespace PottsDiscontinuity.FK

open Finset Medial
open scoped Classical

noncomputable section

variable (a : LatticeVertex) (w h : ℕ)

local notation "G₀" => rectangleGraph a w h
local notation "G₁" => rectangleDualGraph a w h
local notation "V₀" => RectangleVertex a w h
local notation "V₁" => RectangleDualVertex a w h
local notation "F₀" => Subtype (fun z => z ∈ rectangleDualInterior a w h)
local notation "E₀" => OpenEdgeIndex G₀ (rectangleAllEdges a w h)
local notation "β₁" => rectangleDualBoundaryCondition a w h
local notation "v₁" => rectangleDualBaseVertex a w h

local instance : Fintype V₁ := Fintype.ofFinite _

variable (A : Configuration (rectangleGraph a w h))
local notation "Eₐ" => OpenEdgeIndex G₀ A
local notation "A₁" => rectangleDualConfiguration a w h A
local notation "Dₐ" => signedDivergence G₀ A (rectangleOpenEdgeOrientation a w h A)
local notation "D₀" => rectangleFullDivergence a w h
local notation "curl₀" => rectangleFaceCurl a w h

private def supportedPotential (A : Configuration (rectangleGraph a w h)) : Submodule ℝ (F₀ → ℝ) :=
  ⨅ e : {e : E₀ // e.val ∉ A}, LinearMap.ker ((LinearMap.proj e.val).comp curl₀)

private theorem mem_supported (φ : F₀ → ℝ) : φ ∈ supportedPotential a w h A ↔
    ∀ e : E₀, e.val ∉ A → curl₀ φ e = 0 := by
  simp [supportedPotential, LinearMap.mem_ker]

private theorem pad_boundary (φ : F₀ → ℝ) {z : LatticeVertex}
    (hz : z ∈ rectangleDualBoundary a w h) : facePotentialPad a w h φ z = 0 := by
  exact dite_eq_right (mem_filter.mp hz).2

private theorem curl_zero_iff (φ : F₀ → ℝ) (e : E₀) :
    curl₀ φ e = 0 ↔
      facePotentialPad a w h φ (rectangleDualEdgeSource a w h (rectanglePrimalDualEdgeEquiv a w h e.val)).val =
        facePotentialPad a w h φ (rectangleDualEdgeTarget a w h (rectanglePrimalDualEdgeEquiv a w h e.val)).val := by
  rw [rectangleDualEdgeSource_faceBase, rectangleDualEdgeTarget_faceBase, rectangleFaceCurl_eval]
  dsimp [rectanglePrimalDualEdgeEquiv]
  split <;> (constructor <;> intro hh <;> linarith)

private theorem pad_componentConstant (φ : supportedPotential a w h A) :
    (fun z : V₁ => facePotentialPad a w h φ.val z.val) ∈ componentConstantFunctions G₁ β₁ A₁ := by
  apply (componentConstant_iff_local G₁ β₁ A₁ _).2
  constructor
  · intro x y hxy
    obtain ⟨d, hd, he⟩ := (rectangleDualOpen_adj_iff a w h A x y).1 hxy
    let e : E₀ := ⟨d.primalEdge, mem_rectangleAllEdges a w h _⟩
    have hc := (curl_zero_iff a w h φ.val e).1 ((mem_supported a w h A φ.val).1 φ.prop e hd)
    change _ = _ at hc
    have hde : rectanglePrimalDualEdgeEquiv a w h e.val = d :=
      (rectanglePrimalDualEdgeEquiv a w h).apply_symm_apply d
    rw [hde] at hc
    rw [rectangleDualCarrierPair, Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hc
    · exact hc.symm
  · intro x y hxy
    rcases (rectangleDualBoundaryCondition_rel a w h x y).1 hxy with rfl | ⟨hx, hy⟩
    · rfl
    · exact (pad_boundary a w h _ hx).trans (pad_boundary a w h _ hy).symm

private abbrev DualNorm := normalizedComponentPotentials G₁ β₁ A₁ v₁

private def padLinear : supportedPotential a w h A →ₗ[ℝ] DualNorm a w h A where
  toFun φ := ⟨⟨_, pad_componentConstant a w h A φ⟩, pad_boundary a w h _ (rectangleDualBaseVertex_boundary a w h)⟩
  map_add' φ ψ := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change facePotentialPad a w h (φ.val + ψ.val) z.val =
      facePotentialPad a w h φ.val z.val + facePotentialPad a w h ψ.val z.val
    by_cases hz : z.val ∈ rectangleDualInterior a w h <;>
      simp [facePotentialPad, hz]
  map_smul' c φ := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change facePotentialPad a w h (c • φ.val) z.val = c • facePotentialPad a w h φ.val z.val
    by_cases hz : z.val ∈ rectangleDualInterior a w h <;>
      simp [facePotentialPad]

private def faceAsDual (f : F₀) : V₁ :=
  ⟨f.val, (mem_filter.1 f.prop).1⟩

private theorem padLinear_bijective : Function.Bijective (padLinear a w h A) := by
  constructor
  · intro φ ψ hφψ
    apply Subtype.ext
    funext f
    have he := congrArg (fun g : DualNorm a w h A => g.val.val (faceAsDual a w h f)) hφψ
    change facePotentialPad a w h φ.val f.val = facePotentialPad a w h ψ.val f.val at he
    simpa [facePotentialPad] using he
  · intro ψ
    let φ (f : F₀) := ψ.val.val (faceAsDual a w h f)
    have hp (z : V₁) : facePotentialPad a w h φ z.val = ψ.val.val z := by
      by_cases hz : z.val ∈ rectangleDualInterior a w h
      · simp [facePotentialPad, hz, φ, faceAsDual]
      have hzb : z.val ∈ rectangleDualBoundary a w h := mem_filter.2 ⟨z.prop, hz⟩
      have hl := (componentConstant_iff_local G₁ β₁ A₁ _).1 ψ.val.prop
      have he := hl.2 ((rectangleDualBoundaryCondition_rel a w h z v₁).2
        (Or.inr ⟨hzb, rectangleDualBaseVertex_boundary a w h⟩))
      rw [pad_boundary a w h φ hzb, he]
      exact ψ.prop.symm
    have hs : φ ∈ supportedPotential a w h A := (mem_supported a w h A φ).2 fun e he => by
      let d := rectanglePrimalDualEdgeEquiv a w h e.val
      apply (curl_zero_iff a w h φ e).2
      rw [hp, hp]
      exact ((componentConstant_iff_local G₁ β₁ A₁ _).1 ψ.val.prop).1
        ((rectangleDualOpen_adj_iff a w h A _ _).2 ⟨d, he, rfl⟩)
    refine ⟨⟨φ, hs⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact hp z

private def allEdge (e : Eₐ) : E₀ := ⟨e.val, mem_rectangleAllEdges a w h _⟩

/-- Inserting zeros on missing edges does not change the vertex divergences. -/
private theorem full_div_restrict (f : E₀ → ℝ) (hf : ∀ e : E₀, e.val ∉ A → f e = 0) :
    D₀ f = Dₐ (fun e : Eₐ => f (allEdge a w h A e)) := by
  letI : Fintype E₀ := openEdgeIndexFintype G₀ (rectangleAllEdges a w h)
  letI : Fintype Eₐ := openEdgeIndexFintype G₀ A
  have hs (g : E₀ → ℝ) (hg : ∀ e : E₀, e.val ∉ A → g e = 0) :
      (∑ e : Eₐ, g (allEdge a w h A e)) = ∑ e : E₀, g e := by
    let s := univ.filter fun e : E₀ => e.val ∈ A
    calc
      _ = ∑ e ∈ s, g e := by
        apply sum_bij (fun e _ => allEdge a w h A e)
        · intro e _; exact mem_filter.2 ⟨mem_univ _, e.prop⟩
        · intro e _ e' _ he; exact Subtype.ext (congrArg (fun g : E₀ => g.val) he)
        · intro e he
          refine ⟨⟨e.val, (mem_filter.1 he).2⟩, mem_univ _, Subtype.ext rfl⟩
        grind
      _ = _ := sum_subset (filter_subset _ _) fun e _ he => hg e (by simpa [s] using he)
  funext v
  unfold rectangleFullDivergence
  rw [signedDivergence_apply, signedDivergence_apply]
  congr 1
  · exact (hs (fun e => if (rectangleOpenEdgeOrientation a w h (rectangleAllEdges a w h)).source e = v then f e else 0)
      (fun e he => by simp [hf e he])).symm
  · exact (hs (fun e => if (rectangleOpenEdgeOrientation a w h (rectangleAllEdges a w h)).target e = v then f e else 0)
      (fun e he => by simp [hf e he])).symm

private def restrictCurl : supportedPotential a w h A →ₗ[ℝ] LinearMap.ker Dₐ where
  toFun φ := ⟨fun e => curl₀ φ.val (allEdge a w h A e), by
    rw [LinearMap.mem_ker, ← full_div_restrict a w h A _ ((mem_supported a w h A _).1 φ.prop)]
    exact rectangleFullDivergence_faceCurl a w h φ.val⟩
  map_add' φ ψ := by ext e; exact congrFun (map_add curl₀ φ.val ψ.val) _
  map_smul' c φ := by ext e; exact congrFun (map_smul curl₀ c φ.val) _

private theorem restrictCurl_bijective : Function.Bijective (restrictCurl a w h A) := by
  constructor
  · intro φ ψ he
    apply Subtype.ext
    apply curl_injective a w h
    funext e
    by_cases hA : e.val ∈ A
    · exact congrArg (fun g : LinearMap.ker Dₐ => g.val ⟨e.val, hA⟩) he
    · rw [(mem_supported a w h A _).1 φ.prop e hA, (mem_supported a w h A _).1 ψ.prop e hA]
  · intro y
    let f (e : E₀) := if he : e.val ∈ A then y.val ⟨e.val, he⟩ else 0
    have hf (e : E₀) (he : e.val ∉ A) : f e = 0 := dif_neg he
    have hres : (fun e : Eₐ => f (allEdge a w h A e)) = y.val := by
      funext e
      exact dif_pos e.prop
    have hh : f ∈ LinearMap.range curl₀ := by
      rw [rectangleFaceCurl_range, LinearMap.mem_ker, full_div_restrict a w h A f hf, hres]
      exact y.prop
    obtain ⟨φ, hφ⟩ := hh
    refine ⟨⟨φ, (mem_supported a w h A φ).2 (hφ ▸ hf)⟩, ?_⟩
    apply Subtype.ext
    change (fun e : Eₐ => curl₀ φ (allEdge a w h A e)) = y.val
    rwa [hφ]

/-- Euler's relation follows from identifying the dual potentials constant on
closed edges with the divergence-free flows on the open primal graph. -/
theorem rectangleEuler_additive_config :
    componentCount G₁ β₁ A₁ + Fintype.card V₀ =
      A.card + componentCount G₀ (BoundaryCondition.free (∅ : Set V₀)) A + 1 := by
  have hd := rectangleSignedFlowDimension a w h A
  have hpot := normalizedComponentPotentials_finrank_add_one G₁ β₁ A₁ v₁
  rw [← (LinearEquiv.ofBijective _ (padLinear_bijective a w h A)).finrank_eq,
    (LinearEquiv.ofBijective _ (restrictCurl_bijective a w h A)).finrank_eq] at hpot
  omega

theorem rectangleEuler_additive_card_config :
    componentCount G₁ β₁ A₁ + (w + 1) * (h + 1) =
      A.card + componentCount G₀ (BoundaryCondition.free (∅ : Set V₀)) A + 1 := by
  rw [← card_rectangleVertex a w h]
  exact rectangleEuler_additive_config a w h A

end
end PottsDiscontinuity.FK
