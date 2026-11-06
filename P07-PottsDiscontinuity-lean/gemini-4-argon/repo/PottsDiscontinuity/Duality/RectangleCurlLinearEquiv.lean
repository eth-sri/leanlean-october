module

public import PottsDiscontinuity.Duality.RectangleFlowIntegration
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

def rectangleExteriorPotentialSubmodule (a : LatticeVertex) (w h : ℕ) :
    Submodule ℝ (RectangleDualVertex a w h → ℝ) where
  carrier := {φ | ∀ z, z.1 ∈ rectangleDualBoundary a w h → φ z = 0}
  zero_mem' := by simp
  add_mem' := by intro φ ψ hφ hψ z hz; simp [hφ z hz, hψ z hz]
  smul_mem' := by intro c φ hφ z hz; simp [hφ z hz]

private def rectanglePotentialAsExterior (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) : RectangleExteriorPotential a w h :=
  ⟨φ.1, φ.2⟩

def rectangleDivergenceFreeFlowSubmodule (a : LatticeVertex) (w h : ℕ) :
    Submodule ℝ (RectanglePrimalBond a w h → ℝ) where
  carrier := {F | ∀ v, v ∈ latticeRectangle a w h →
    rectanglePrimalFlowDivergence a w h F v = 0}
  zero_mem' := by intro v _; simp [rectanglePrimalFlowDivergence]
  add_mem' := by
    intro F G hF hG v hv
    classical
    have : rectanglePrimalFlowDivergence a w h (F + G) v =
        rectanglePrimalFlowDivergence a w h F v + rectanglePrimalFlowDivergence a w h G v := by
      unfold rectanglePrimalFlowDivergence
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hs : b.1.1.source = v <;> simp [hs]; ring
    rw [this, hF v hv, hG v hv, add_zero]
  smul_mem' := by
    intro c F hF v hv
    classical
    have : rectanglePrimalFlowDivergence a w h (c • F) v =
        c * rectanglePrimalFlowDivergence a w h F v := by
      unfold rectanglePrimalFlowDivergence
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hs : b.1.1.source = v <;> simp [hs]
    rw [this, hF v hv, mul_zero]

private theorem rectangleExtendedPotential_add (a : LatticeVertex) (w h : ℕ)
    (φ ψ : rectangleExteriorPotentialSubmodule a w h) (z : LatticeVertex) :
    rectangleExtendedPotential a w h ⟨(φ + ψ).1, (φ + ψ).2⟩ z =
      rectangleExtendedPotential a w h ⟨φ.1, φ.2⟩ z +
        rectangleExtendedPotential a w h ⟨ψ.1, ψ.2⟩ z := by
  by_cases hz : z ∈ rectangleDualExpanded a w h <;>
    simp [rectangleExtendedPotential, hz]

private theorem rectangleExtendedPotential_smul (a : LatticeVertex) (w h : ℕ)
    (c : ℝ) (φ : rectangleExteriorPotentialSubmodule a w h) (z : LatticeVertex) :
    rectangleExtendedPotential a w h ⟨(c • φ).1, (c • φ).2⟩ z =
      c * rectangleExtendedPotential a w h ⟨φ.1, φ.2⟩ z := by
  by_cases hz : z ∈ rectangleDualExpanded a w h <;>
    simp [rectangleExtendedPotential, hz]

def rectanglePotentialCurlMap (a : LatticeVertex) (w h : ℕ) :
    rectangleExteriorPotentialSubmodule a w h →ₗ[ℝ]
      (RectanglePrimalBond a w h → ℝ) where
  toFun φ b := rectangleCurlFlow a w h ⟨φ.1, φ.2⟩ b.1
  map_add' φ ψ := by
    funext b
    cases hax : b.1.axis <;>
      simp only [rectangleCurlFlow, hax, Pi.add_apply, rectangleExtendedPotential_add] <;> abel
  map_smul' c φ := by
    funext b
    cases hax : b.1.axis <;>
      simp only [rectangleCurlFlow, hax, Pi.smul_apply, smul_eq_mul,
        rectangleExtendedPotential_smul, RingHom.id_apply] <;> ring

theorem rectanglePotentialCurlMap_mem_divergenceFree
    (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) :
    rectanglePotentialCurlMap a w h φ ∈ rectangleDivergenceFreeFlowSubmodule a w h := by
  intro v hv
  rw [rectanglePrimalFlowDivergence_eq_stencil]
  have hcand (i : Fin 4) :
      rectangleExtendedPrimalFlow a w h (rectanglePotentialCurlMap a w h φ)
        (rectangleCurlIncidentCandidate v i) =
      rectangleCurlFlow a w h (rectanglePotentialAsExterior a w h φ)
        (rectangleCurlIncidentCandidate v i) := by
    unfold rectangleExtendedPrimalFlow
    split_ifs with hb
    · rfl
    · exact (rectangleCurlCandidate_flow_zero_of_not_inside a w h
        (rectanglePotentialAsExterior a w h φ) v i hv hb).symm
  have h0 := hcand 0; have h1 := hcand 1; have h2 := hcand 2; have h3 := hcand 3
  dsimp [rectangleCurlIncidentCandidate] at h0 h1 h2 h3
  unfold rectangleFlowDivergenceStencil
  rw [h0, h1, h2, h3]
  simp [rectangleCurlFlow, LatticeBond.faceBase]
  ring

def rectanglePotentialCurlIntoDivergenceFree (a : LatticeVertex) (w h : ℕ) :
    rectangleExteriorPotentialSubmodule a w h →ₗ[ℝ]
      rectangleDivergenceFreeFlowSubmodule a w h where
  toFun φ := ⟨rectanglePotentialCurlMap a w h φ,
    rectanglePotentialCurlMap_mem_divergenceFree a w h φ⟩
  map_add' φ ψ := Subtype.ext (map_add (rectanglePotentialCurlMap a w h) φ ψ)
  map_smul' c φ := Subtype.ext (map_smul (rectanglePotentialCurlMap a w h) c φ)

private theorem rectangleExtendedPotential_zero_of_boundary
    (a : LatticeVertex) (w h : ℕ) (φ : RectangleExteriorPotential a w h)
    (z : LatticeVertex) (hz : z ∈ rectangleDualBoundary a w h) :
    rectangleExtendedPotential a w h φ z = 0 := by
  rw [rectangleExtendedPotential_of_mem a w h φ z (Finset.mem_filter.mp hz).1]
  exact φ.2 ⟨z, (Finset.mem_filter.mp hz).1⟩ hz

private theorem rectangleExteriorPotential_ext_atInterior
    (a : LatticeVertex) (w h : ℕ)
    (φ ψ : RectangleExteriorPotential a w h)
    (hcurl : ∀ b : RectanglePrimalBond a w h,
      rectangleCurlFlow a w h φ b.1 = rectangleCurlFlow a w h ψ b.1)
    (n m : ℕ) (hn : n < w) (hm : m < h) :
    rectangleExtendedPotential a w h φ (rectangleFlowVertex a (n : ℤ) (m : ℤ)) =
      rectangleExtendedPotential a w h ψ (rectangleFlowVertex a (n : ℤ) (m : ℤ)) := by
  have hedgeMem (j : ℕ) (hj : j < h) :
      (⟨rectangleFlowVertex a (n : ℤ) (j : ℤ), .horizontal⟩ : LatticeBond).source ∈
          latticeRectangle a w h ∧
        (⟨rectangleFlowVertex a (n : ℤ) (j : ℤ), .horizontal⟩ : LatticeBond).target ∈
          latticeRectangle a w h := by
    constructor <;> rw [mem_latticeRectangle] <;>
      simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY,
        LatticeBond.source, LatticeBond.target] <;> omega
  induction m with
  | zero =>
      have hc := hcurl ⟨⟨rectangleFlowVertex a (n : ℤ) (0 : ℤ), .horizontal⟩, hedgeMem 0 hm⟩
      simp [rectangleCurlFlow, LatticeBond.faceBase, rectangleFlowVertex,
        rectangleFlowX, rectangleFlowY] at hc
      have hbd' : (a.1 + (n : ℤ), a.2 - 1) ∈ rectangleDualBoundary a w h := by
        simp [rectangleDualBoundary, rectangleDualInterior, rectangleDualExpanded,
          latticeRectangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        omega
      rw [rectangleExtendedPotential_zero_of_boundary a w h φ _ hbd',
        rectangleExtendedPotential_zero_of_boundary a w h ψ _ hbd'] at hc
      simpa [rectangleFlowVertex, rectangleFlowX, rectangleFlowY] using hc
  | succ j ih =>
      have hc := hcurl ⟨⟨rectangleFlowVertex a (n : ℤ) (j.succ : ℤ), .horizontal⟩,
        hedgeMem j.succ hm⟩
      simp [rectangleCurlFlow, LatticeBond.faceBase, rectangleFlowVertex,
        rectangleFlowX, rectangleFlowY] at hc
      have hprev := ih (by omega)
      simp only [rectangleFlowVertex, rectangleFlowX, rectangleFlowY] at hprev ⊢
      push_cast
      rw [show a.2 + ((j : ℤ) + 1) - 1 = a.2 + (j : ℤ) by ring, hprev] at hc
      linarith

theorem rectanglePotentialCurlMap_injective (a : LatticeVertex) (w h : ℕ) :
    Function.Injective (rectanglePotentialCurlMap a w h) := by
  intro φ ψ hφψ
  ext z
  by_cases hI : z.1 ∈ rectangleDualInterior a w h
  · have hprop := (Finset.mem_filter.mp hI).2
    let n : ℕ := (z.1.1 - a.1).toNat
    let m : ℕ := (z.1.2 - a.2).toNat
    have hcoords : z.1 = rectangleFlowVertex a (n : ℤ) (m : ℤ) := by
      ext <;> simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY, n, m] <;> omega
    have hp := rectangleExteriorPotential_ext_atInterior a w h ⟨φ.1, φ.2⟩ ⟨ψ.1, ψ.2⟩
      (fun b => congrFun hφψ b) n m (by omega) (by omega)
    rw [ ← hcoords, rectangleExtendedPotential_of_mem a w h _ _ z.2,
      rectangleExtendedPotential_of_mem a w h _ _ z.2] at hp
    exact hp
  · have hb : z.1 ∈ rectangleDualBoundary a w h := Finset.mem_filter.mpr ⟨z.2, hI⟩
    rw [φ.2 z hb, ψ.2 z hb]

noncomputable def rectanglePotentialCurlLinearEquiv (a : LatticeVertex) (w h : ℕ) :
    rectangleExteriorPotentialSubmodule a w h ≃ₗ[ℝ]
      rectangleDivergenceFreeFlowSubmodule a w h :=
  LinearEquiv.ofBijective (rectanglePotentialCurlIntoDivergenceFree a w h)
    ⟨fun _ _ hxy => rectanglePotentialCurlMap_injective a w h (congrArg Subtype.val hxy),
      fun F => ⟨⟨(rectangleFlowExteriorPotential a w h ⟨F.1, F.2⟩).1,
        (rectangleFlowExteriorPotential a w h ⟨F.1, F.2⟩).2⟩,
        Subtype.ext (funext fun b =>
          rectangleFlowExteriorPotential_curl_eq_flow a w h ⟨F.1, F.2⟩ b)⟩⟩

end PottsDiscontinuity.FK
