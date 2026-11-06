
import GS.UnitaryTopology.EuclideanRetract
import GS.UnitaryTopology.QuaternionRetraction
import Mathlib.Analysis.Normed.Module.FiniteDimension



/-!
# The Clifford retraction with arbitrary Euclidean factors

The singular zero-matrix stratum is retained. The sole deleted point is the
origin of the full product. The Euclidean projection has exactly that zero.
-/
noncomputable section
open GS.UnitaryLocalModel
open GS.NonmanifoldClosure
namespace GS.UnitaryTopology
variable (e r : ℕ)

def pairCoordinatesEuclidean  :
    ((Fin e → ℝ) × (Fin r × Fin 4 → ℝ)) ≃ₜ Eucl (e+r*4)  :=
  (ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (by aesop)).toHomeomorph

@[simp] theorem pairCoordinatesEuclidean_zero  :
    pairCoordinatesEuclidean e r (0,0) = 0 := by simp [pairCoordinatesEuclidean]

def quaternionProductProjection 
    (p : (Fin e → ℝ) × RankThreeCone (Fin r × Fin 4)) := (p.1,quaternionContraction p.2.val)

def quaternionProductSection 
    (p : (Fin e → ℝ) × (Fin r × Fin 4 → ℝ)) := (p.1,firstRowSection p.2)

theorem continuous_quaternionProductProjection  :
    Continuous (quaternionProductProjection e r) :=
  continuous_fst.prodMk ((continuous_quaternionContraction r).comp
    (continuous_subtype_val.comp continuous_snd))

theorem continuous_quaternionProductSection  :
    Continuous (quaternionProductSection e r) :=
  by fun_prop [quaternionProductSection,firstRowSection,sphereOuter]

@[simp] theorem quaternionProductProjection_section 
    (p : (Fin e → ℝ) × (Fin r × Fin 4 → ℝ)) :
    quaternionProductProjection e r (quaternionProductSection e r p) = p := Prod.ext rfl (quaternionContraction_section p.2)





/-- An explicit isolated-zero Euclidean retract, with no topological premise. -/
def quaternionProductRetract  :
    IsolatedEuclideanRetract ((Fin e → ℝ) × RankThreeCone (Fin r × Fin 4))
      (0,rankThreeZero) (e+r*4) where
  sectionMap := quaternionProductSection e r ∘ (pairCoordinatesEuclidean e r).symm
  projectionMap := pairCoordinatesEuclidean e r ∘ quaternionProductProjection e r
  section_continuous := (continuous_quaternionProductSection e r).comp
    (pairCoordinatesEuclidean e r).symm.continuous
  projection_continuous := (pairCoordinatesEuclidean e r).continuous.comp
    (continuous_quaternionProductProjection e r)
  projection_section x := by simp
  section_zero := by aesop (add norm [sphereOuter,pairCoordinatesEuclidean,quaternionProductSection,firstRowSection])
  projection_zero_iff p := by simp_all [pairCoordinatesEuclidean,quaternionProductProjection,quaternionContraction_zero_iff,Prod.ext_iff]

end GS.UnitaryTopology
