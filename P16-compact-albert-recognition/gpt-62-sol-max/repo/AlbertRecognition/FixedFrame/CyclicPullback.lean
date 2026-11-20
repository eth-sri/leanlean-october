/- Actual native cyclic frame transport for an unrestricted symmetric cubic.
Unknown-cubic invariance is neither a field nor a premise: B is pulled back.
-/
module

public import AlbertRecognition.JacobiBridge
public import Glennie.Automorphism
public import Glennie.Native.RealConjugation
@[expose] public section
namespace AlbertRecognition
noncomputable section
open Glennie

/-- Restrict an actual native trace-preserving automorphism to the real trace kernel. -/
def automorphismV (g : CompactAutomorphism) : V ≃ₗ[ℝ] V :=
  g.equiv.ofSubmodules V V (by
    ext x
    rw [Submodule.mem_map_equiv]
    change trace (g.symm.equiv x) = 0 ↔ trace x = 0
    rw [g.symm.map_trace])

@[simp] theorem automorphismV_coe (g : CompactAutomorphism) (x : V) :
    (automorphismV g x : Albert) = g.equiv (x : Albert) := rfl

/-- The specified metric scale remains trace/3 under the actual automorphism. -/
theorem automorphismV_gA (g : CompactAutomorphism) (x y : V) :
    gA (automorphismV g x) (automorphismV g y) = gA x y := by
  exact congrArg (fun r : ℝ => r / 3) (g.inner_map (x : Albert) (y : Albert))

/-- Native projected Jordan multiplication is transported, never postulated. -/
theorem automorphismV_KA (g : CompactAutomorphism) (x y : V) :
    automorphismV g (KA x y) = KA (automorphismV g x) (automorphismV g y) := by grind [automorphismV_coe, KA_apply, project_coe, g.map_traceless, g.map_jordan]

/-- Pullback of an arbitrary genuine symmetric trilinear form by a real equivalence. -/
def pullbackCubic (T : V ≃ₗ[ℝ] V) (B : SymmetricCubic) : SymmetricCubic where
  form := (B.form.compl₁₂ T.toLinearMap T.toLinearMap).compr₂
    (LinearMap.lcomp ℝ ℝ T.toLinearMap)
  swap12 x y z := B.swap12 (T x) (T y) (T z)
  swap23 x y z := B.swap23 (T x) (T y) (T z)

@[simp] theorem pullbackCubic_form (T : V ≃ₗ[ℝ] V) (B : SymmetricCubic)
    (x y z : V) : (pullbackCubic T B).form x y z = B.form (T x) (T y) (T z) := rfl

/-- Raising an index commutes with pullback because the actual metric is preserved.
The transformed unknown is B(Tx,Ty,Tz); B itself is unrestricted. -/
theorem automorphismV_KB_pullback (g : CompactAutomorphism) (B : SymmetricCubic)
    (x y : V) :
    automorphismV g (KB (pullbackCubic (automorphismV g) B) x y) =
      KB B (automorphismV g x) (automorphismV g y) := by
  apply metricDual.injective
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := (automorphismV g).surjective z
  rw [metricDual_apply, metricDual_apply, automorphismV_gA,
    KB_pairing, KB_pairing, pullbackCubic_form]

/-- The actual reference-q tensor transports with the native automorphism. -/
theorem automorphismV_q_reference (g : CompactAutomorphism) (x y v : V) :
    automorphismV g (q referenceCubic x y v) =
      q referenceCubic (automorphismV g x) (automorphismV g y)
        (automorphismV g v) := by
  simp only [q, KB_referenceCubic, operatorComm_apply, map_sub, automorphismV_KA]

/-- Literal A(q) covariance for the pulled-back arbitrary cubic, pointwise. -/
theorem automorphismV_A_q_pullback (g : CompactAutomorphism) (B : SymmetricCubic)
    (x y z v : V) :
    automorphismV g (A (q referenceCubic) (pullbackCubic (automorphismV g) B)
      x y z v) =
      A (q referenceCubic) B (automorphismV g x) (automorphismV g y)
        (automorphismV g z) (automorphismV g v) := by simp [A, LinearMap.add_apply, operatorComm_apply, map_add, map_sub, automorphismV_KB_pullback, automorphismV_q_reference]

/-- The sole original Jacobi-kernel hypothesis is stable under actual pullback. -/
theorem A_q_pullback_zero (g : CompactAutomorphism) (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    A (q referenceCubic) (pullbackCubic (automorphismV g) B) = 0 := by
  funext x y z
  apply LinearMap.ext
  intro v
  apply (automorphismV g).injective
  change automorphismV g
    (A (q referenceCubic) (pullbackCubic (automorphismV g) B) x y z v) =
      automorphismV g 0
  rw [automorphismV_A_q_pullback, hB]
  simp only [Pi.zero_apply, LinearMap.zero_apply, map_zero]

namespace FixedFrame

@[simp] theorem permutation_h (s : Equiv.Perm (Fin 3)) (i : Fin 3) :
    automorphismV (permutationAutomorphism s) (h i) = h (s.symm i) := by
  apply Subtype.ext
  change (permutationAutomorphism s).equiv (1 - (3 : ℝ) • e i) = 1 - (3 : ℝ) • e (s.symm i)
  simp only [map_sub, map_smul, CompactAutomorphism.map_unit]
  congr 2
  have he (j : Fin 3) : e j = diagonalOf (Pi.single j 1) := by
    fin_cases j <;> apply Albert.ext <;> norm_num [e, diagonalOf, diagonalAlbert, Pi.single_apply]
  rw [he, he, permutation_diagonalOf]
  congr 1
  funext j
  simp [Pi.single_apply, ← s.eq_symm_apply]

end FixedFrame
end
end AlbertRecognition
