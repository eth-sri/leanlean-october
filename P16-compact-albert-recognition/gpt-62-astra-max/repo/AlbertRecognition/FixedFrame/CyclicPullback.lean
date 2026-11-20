/- Actual native cyclic frame transport for an unrestricted symmetric cubic.
Unknown-cubic invariance is neither a field nor a premise: B is pulled back.
-/
module

public import AlbertRecognition.CubicOperators
public import Glennie.Automorphism
public import Glennie.Native.RealConjugation

@[expose] public section
namespace AlbertRecognition
noncomputable section
open Glennie

/-- Restrict an actual native trace-preserving automorphism to the real trace kernel. -/
def automorphismV (g : CompactAutomorphism) : V ≃ₗ[ℝ] V where
  toFun x := ⟨g.equiv (x : Albert), by
    change trace (g.equiv (x : Albert)) = 0
    rw [g.map_trace]
    exact trace_V x⟩
  invFun x := ⟨g.symm.equiv (x : Albert), by
    change trace (g.symm.equiv (x : Albert)) = 0
    rw [g.symm.map_trace]
    exact trace_V x⟩
  left_inv x := by
    apply Subtype.ext
    exact g.equiv.symm_apply_apply (x : Albert)
  right_inv x := by
    apply Subtype.ext
    exact g.equiv.apply_symm_apply (x : Albert)
  map_add' x y := by apply Subtype.ext; exact map_add g.equiv _ _
  map_smul' r x := by
    apply Subtype.ext
    change g.equiv (r • (x : Albert)) = r • g.equiv (x : Albert)
    simpa only [RingHom.id_apply] using map_smul g.equiv r (x : Albert)

@[simp] theorem automorphismV_coe (g : CompactAutomorphism) (x : V) :
    (automorphismV g x : Albert) = g.equiv (x : Albert) := rfl

@[simp] theorem automorphismV_comp_apply (g f : CompactAutomorphism) (x : V) :
    automorphismV (g.comp f) x = automorphismV g (automorphismV f x) := rfl

/-- The specified metric scale remains trace/3 under the actual automorphism. -/
theorem automorphismV_gA (g : CompactAutomorphism) (x y : V) :
    gA (automorphismV g x) (automorphismV g y) = gA x y := congrArg (fun r : ℝ => r / 3) (g.inner_map (x : Albert) (y : Albert))

/-- Native projected Jordan multiplication is transported, never postulated. -/
theorem automorphismV_KA (g : CompactAutomorphism) (x y : V) :
    automorphismV g (KA x y) = KA (automorphismV g x) (automorphismV g y) := by
  apply Subtype.ext
  simp [g.map_traceless, g.map_jordan]

def pull (g : CompactAutomorphism) (B : SymmetricCubic) : SymmetricCubic where
  K := let T := automorphismV g; (B.K.compl₁₂ T.toLinearMap T.toLinearMap).compr₂ T.symm.toLinearMap
  comm x y := congrArg (automorphismV g).symm (B.comm ..)
  symm x y z := by
    let T := automorphismV g
    change gA (T.symm _) z = gA (T.symm _) y
    rw [← automorphismV_gA g _ z, ← automorphismV_gA g _ y]; simp only [← show T = automorphismV g from rfl, LinearEquiv.apply_symm_apply]; apply B.symm

theorem pull_K (g : CompactAutomorphism) (B : SymmetricCubic) (x y : V) :
    automorphismV g ((pull g B).K x y) = B.K (automorphismV g x) (automorphismV g y) := (automorphismV g).apply_symm_apply _
theorem pull_form (g : CompactAutomorphism) (B : SymmetricCubic) (x : V) :
    (pull g B).form x x x = B.form (automorphismV g x) (automorphismV g x) (automorphismV g x) := by
  change gA _ x = gA _ _; rw [← automorphismV_gA g _ x,pull_K]
theorem q_pullback {B : SymmetricCubic} (hq : q B = q referenceCubic) (g : CompactAutomorphism) : q (pull g B) = q referenceCubic := by
  funext x y; ext1 v; apply (automorphismV g).injective
  simp only [q_apply, map_sub,pull_K]
  change q B _ _ _ = _ - _; rw [hq,q_apply]; simp only [referenceCubic,automorphismV_KA]

theorem move_h (i : Fin 3) : ∃ g : CompactAutomorphism, automorphismV g (h 0) = h i := by
  fin_cases i
  · exact ⟨CompactAutomorphism.refl,rfl⟩
  · exact ⟨realSwap01Automorphism,Subtype.ext (by ext <;> simp [realSwap01_coordinates,h,e,octConj,unit])⟩
  · exact ⟨realSwap02Automorphism,Subtype.ext (by ext <;> simp [realSwap02_coordinates,h,e,octConj,unit])⟩
end
end AlbertRecognition
