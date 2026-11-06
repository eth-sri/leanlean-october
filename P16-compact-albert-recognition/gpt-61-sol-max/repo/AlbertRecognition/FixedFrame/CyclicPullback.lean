/- Actual native cyclic frame transport for an unrestricted symmetric cubic.
Unknown-cubic invariance is neither a field nor a premise: B is pulled back.
-/
module
public import Mathlib.Tactic.Simps.Basic

public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.NormNum
public import Aesop

public import AlbertRecognition.CubicOperators
public import Glennie.Automorphism
public import Glennie.Native.RealConjugation

@[expose] public section
namespace AlbertRecognition
noncomputable section
open Glennie

/-- Restrict an actual native trace-preserving automorphism to the real trace kernel. -/
def automorphismV (g : CompactAutomorphism) : V ≃ₗ[ℝ] V :=
  g.equiv.ofSubmodules _ _ (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext x
    change trace (g.symm.equiv x) = 0 ↔ trace x = 0
    rw [g.symm.map_trace])


/-- The specified metric scale remains trace/3 under the actual automorphism. -/
theorem automorphismV_gA (g : CompactAutomorphism) (x y : V) :
    gA (automorphismV g x) (automorphismV g y) = gA x y := congrArg (fun r : ℝ => r / 3) (g.inner_map (x : Albert) (y : Albert))

/-- Native projected Jordan multiplication is transported, never postulated. -/
theorem automorphismV_KA (g : CompactAutomorphism) (x y : V) :
    automorphismV g (KA x y) = KA (automorphismV g x) (automorphismV g y) := by
  apply Subtype.ext
  simp only [KA_apply_apply, automorphismV, LinearEquiv.ofSubmodules_apply, project_apply_coe]
  rw [g.map_traceless, g.map_jordan]

/-- Pullback of an arbitrary genuine symmetric trilinear form by a real equivalence. -/
@[simps! form_apply_apply_apply] def pullbackCubic (T : V ≃ₗ[ℝ] V) (B : SymmetricCubic) : SymmetricCubic where
  form := (B.form.compl₁₂ T.toLinearMap T.toLinearMap).compr₂
    (LinearMap.lcomp ℝ ℝ T.toLinearMap)
  swap12 x y z := B.swap12 (T x) (T y) (T z)
  swap23 x y z := B.swap23 (T x) (T y) (T z)



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
  change gA (automorphismV g (KB (pullbackCubic (automorphismV g) B) x y))
      (automorphismV g w) =
    gA (KB B (automorphismV g x) (automorphismV g y)) (automorphismV g w)
  rw [automorphismV_gA, KB_pairing, KB_pairing, pullbackCubic_form_apply_apply_apply]

/-- Transfer one proved scalar action of the pullback to the original unknown. -/
theorem scalar_action_of_pullback (g : CompactAutomorphism) (B : SymmetricCubic)
    (x y : V) (r : ℝ)
    (hxy : KB (pullbackCubic (automorphismV g) B) x y = r • y) :
    KB B (automorphismV g x) (automorphismV g y) =
      r • automorphismV g y := by
  rw [← automorphismV_KB_pullback, hxy, map_smul]

/-- The actual reference-q tensor transports with the native automorphism. -/
theorem automorphismV_q_reference (g : CompactAutomorphism) (x y v : V) :
    automorphismV g (q referenceCubic x y v) =
      q referenceCubic (automorphismV g x) (automorphismV g y)
        (automorphismV g v) := by
  simp only [q, KB_referenceCubic, operatorComm, LinearMap.sub_apply,
    LinearMap.comp_apply, map_sub, automorphismV_KA]

/-- Literal A(q) covariance for the pulled-back arbitrary cubic, pointwise. -/
theorem automorphismV_A_q_pullback (g : CompactAutomorphism) (B : SymmetricCubic)
    (x y z v : V) :
    automorphismV g (A (q referenceCubic) (pullbackCubic (automorphismV g) B)
      x y z v) =
      A (q referenceCubic) B (automorphismV g x) (automorphismV g y)
        (automorphismV g z) (automorphismV g v) := by
  simp only [A, operatorComm, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, map_add, map_sub, automorphismV_KB_pullback,
    automorphismV_q_reference]

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

/-- Concrete native cyclic permutation: first swap01, then swap02. -/
def cyclicAutomorphism : CompactAutomorphism :=
  realSwap02Automorphism.comp realSwap01Automorphism

def cyclicV : V ≃ₗ[ℝ] V := automorphismV cyclicAutomorphism

theorem cyclicAutomorphism_coordinates (x : Albert) :
    cyclicAutomorphism.equiv x =
      ⟨x.d2,x.d0,x.d1,octConj x.o02,octConj x.o12,x.o01⟩ := by
  change realConjugateAlbert realSwap02 (realConjugateAlbert realSwap01 x) = _
  rw [realSwap01_coordinates, realSwap02_coordinates, octConj_conj]

theorem cyclicV_coordinates (x : V) :
    (cyclicV x : Albert) =
      ⟨(x : Albert).d2,(x : Albert).d0,(x : Albert).d1,
        octConj (x : Albert).o02,octConj (x : Albert).o12,(x : Albert).o01⟩ :=
  cyclicAutomorphism_coordinates (x : Albert)

@[simp] theorem cyclicV_h (i : Fin 3) : cyclicV (h i) = h (i + 1) := by
  apply Subtype.ext
  rw [cyclicV_coordinates]
  fin_cases i <;> apply Albert.ext <;> norm_num [h, e, unit, octConj]

@[simp] theorem cyclicV_X01 (u : Octonion) : cyclicV (X01 u) = X12 u := by
  apply Subtype.ext
  rw [cyclicV_coordinates]
  apply Albert.ext <;> simp [X01, X12, octConj]

@[simp] theorem cyclicV_X02 (u : Octonion) :
    cyclicV (X02 u) = X01 (octConj u) := by
  apply Subtype.ext
  rw [cyclicV_coordinates]
  apply Albert.ext <;> simp [X01, X02, octConj]

@[simp] theorem cyclicV_X12 (u : Octonion) :
    cyclicV (X12 u) = X02 (octConj u) := by
  apply Subtype.ext
  rw [cyclicV_coordinates]
  apply Albert.ext <;> simp [X02, X12, octConj]

end FixedFrame
end
end AlbertRecognition
