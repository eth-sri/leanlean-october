module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.VertexChains

@[expose] public section

/-! # Recursive subdivision of vertex chains

The boundary identity is valid for any chosen center of every simplex.
Barycenters will be used for the geometric specialization. Naturality
requires that the vertex map carry the chosen centers to chosen centers.
-/

namespace FiniteChains.VertexChains

universe u v
variable {V : Type u} {W : Type v}
variable (center : ∀ n, Vertices V n → V)

noncomputable def subdivide : (n : ℕ) → Chain V n →ₗ[ℤ] Chain V n
  | 0 => LinearMap.id
  | n + 1 => Finsupp.linearCombination ℤ (fun v : Vertices V (n + 1) =>
      cone (center (n + 1) v) n (subdivide n (boundary n (Finsupp.single v 1))))

theorem subdivide_zero (c : Chain V 0) : subdivide center 0 c = c := rfl

variable (n : ℕ)

theorem subdivide_succ_single (v : Vertices V _) (r : ℤ) :
    subdivide center _ (Finsupp.single v r) =
      r • cone (center (n + 1) v) n (subdivide center n (boundary n (Finsupp.single v 1))) := by
  simp [subdivide, Finsupp.linearCombination_single]

theorem boundary_subdivide :
    (boundary n).comp (subdivide center _) = (subdivide center n).comp (boundary n) := by
  induction n with
  | zero =>
    apply linearMap_ext_basis
    simp_all [subdivide_succ_single, subdivide_zero, boundary_cone_zero, augmentation_boundary]
  | succ n ih =>
    apply linearMap_ext_basis
    intro v
    simp only [LinearMap.comp_apply, subdivide_succ_single, one_smul]
    rw [boundary_cone]
    have hz : boundary n (subdivide center (n + 1)
        (boundary (n + 1) (Finsupp.single v 1))) = 0 := by
      rw [← LinearMap.comp_apply, ih, LinearMap.comp_apply, boundary_boundary, map_zero]
    simp_all

theorem subdivide_boundary (c : Chain V _) :
    subdivide center n (boundary n c) = boundary n (subdivide center (n + 1) c) :=
  (DFunLike.congr_fun (boundary_subdivide center n) c).symm

theorem subdivide_naturality (other : ∀ n, Vertices W n → W) (f : V → W)
    (hf : ∀ n v, f (center n v) = other n (f ∘ v)) (n : ℕ) :
    (map f n).comp (subdivide center n) = (subdivide other n).comp (map f n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply linearMap_ext_basis
    intro v
    simp only [LinearMap.comp_apply, subdivide_succ_single, one_smul, map_single]
    rw [map_cone, hf]
    have he := DFunLike.congr_fun ih (boundary n (Finsupp.single v 1))
    dsimp only [LinearMap.comp_apply] at he
    rw [he, map_boundary, map_single]

end FiniteChains.VertexChains
