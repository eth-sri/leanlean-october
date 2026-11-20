module

public import GS.Singularity.Model

public import GS.Singularity.Charts

public import GS.Results.Nonmanifold

public import GS.Topology.RankCone

public import GS.Unitary.RealEmbedding

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix Set GS.NonmanifoldFinal
namespace GS.Shared.Singularity
variable {𝕜 : Type*} [RCLike 𝕜] {q d n : ℕ} {o : Fin q}

/-- Absorb the regular outer and midpoint coordinates into one Euclidean factor. -/
theorem outer_cone_not_euclidean
    (h : ∀ e : ℕ, ¬ EuclideanAt ((0,rankZero) : (Fin e → ℝ) × Cone 𝕜 d)) :
    ¬ EuclideanAt ((1,0,rankZero) : Outer 𝕜 q o × Coordinate d × Cone 𝕜 d) := by
  let E := (Anchor o → FullModel 𝕜 2) × Coordinate d
  let e : OpenPartialHomeomorph (Outer 𝕜 q o × Coordinate d) E :=
    (OpenPartialHomeomorph.pi fun _ : Anchor o => factorPartialChart (1 : FullU 𝕜 2)).prod
      (OpenPartialHomeomorph.refl _)
  let m := Module.finrank ℝ E
  let c : E ≃L[ℝ] (Fin m → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [m])
  have h₀ : e (1,0) = 0 := Prod.ext (funext fun _ => factorPartialChart_base _) rfl
  have he : (1,0) ∈ e.source := ⟨fun _ _ => base_mem_factorSource _,mem_univ _⟩
  let f := (e.transHomeomorph c.toHomeomorph).prod (OpenPartialHomeomorph.refl (Cone 𝕜 d))
  have hf : ((1,0),rankZero) ∈ f.source := ⟨he,mem_univ _⟩
  have hz : f ((1,0),rankZero) = (0,rankZero) := by
    change (c (e (1,0)),rankZero) = _
    rw [h₀, map_zero]
  intro hE
  apply h m
  rw [← hz]
  apply (euclideanAt_partial f hf).mp
  exact euclideanAt_of_homeomorph (Homeomorph.prodAssoc _ _ _).symm _ hE

/-- Real singularities hold at every reference with nonzero entries. -/
theorem _root_.GSPalomar.real_three_factor_singularity {q : ℕ} (hq : 3 ≤ q) (A : GS.Mat q) (hA : Orthogonal A)
    (hne : ∀ i j, A i j ≠ 0) : ¬ EuclideanAtSubset (localFamily q) (basePoint A) := by
  let Q := asFull A hA
  let o : Fin q := ⟨0,by omega⟩
  have ha : AnchorsNonzero (Factor.matrix Q) o := fun _ => hne _ _
  have hn : ¬ EuclideanAtSubset (shuffleFamily ℝ q) (familyCenter Q).val :=
    not_euclidean (realSliceChart Q o ha) (outer_cone_not_euclidean fun e => by
      unfold Cone
      rw [Module.finrank_self]
      exact GS.NonmanifoldTopology.cone_not_euclidean e _ (realSkew_finrank_ge_two hq))
  rw [familyCenter_val] at hn
  exact hn

theorem _root_.GSPalomar.real_singular_point (q : ℕ) (hq : 3 ≤ q) :
    ∃ A : GS.Mat (q*2), A ∈ localFamily q ∧ ¬ EuclideanAtSubset (localFamily q) A := by
  let A := GS.Results.reflectionBase q
  have hA := GS.Results.reflectionBase_orthogonal q (by omega)
  refine ⟨basePoint A,?_,GSPalomar.real_three_factor_singularity hq A hA (GS.Results.reflectionBase_entries_ne_zero q hq)⟩
  have h := (familyCenter (asFull A hA)).property
  rw [familyCenter_val] at h
  exact h

open GS.UnitaryGeometry in
/-- The complex cone obstruction applies when the width `(q-1)^2` is divisible by four. -/
theorem _root_.GSPalomar.unitary_singular_point (q : ℕ) (hq : 3 ≤ q) (hodd : Odd q) :
    let P := cPermMatrix (scalarShuffle q 2)
    let S : Set (CMat (q*2)) := {A | CInA3Unitary 2 q 2 P Pᴴ A}
    ∃ A : CMat (q*2), A ∈ S ∧ ¬ EuclideanAtSubset S A := by
  let A := GS.Results.reflectionBase q
  let Q := asFull (GS.UnitaryGeometry.ofRealMatrix A) (GS.UnitaryGeometry.ofRealMatrix_unitary <| GS.Results.reflectionBase_orthogonal q (by omega))
  let o : Fin q := ⟨0, by omega⟩
  have hne (i j : Fin q) : Factor.matrix Q i j ≠ 0 := by
    change (A i j : ℂ) ≠ 0
    exact_mod_cast GS.Results.reflectionBase_entries_ne_zero q hq i j
  have ha : AnchorsNonzero (Factor.matrix Q) o := fun _ => hne _ _
  refine ⟨(familyCenter Q).val,(familyCenter Q).property,not_euclidean (complexSliceChart Q o ha) ?_⟩
  apply outer_cone_not_euclidean
  intro e
  unfold Cone
  rw [Complex.finrank_real_complex]
  apply GS.UnitaryTopology.rankThreeProduct_not_euclidean_of_four_dvd
  · exact pow_pos (by omega) _
  · obtain ⟨k,rfl⟩ := hodd
    grind

end GS.Shared.Singularity
