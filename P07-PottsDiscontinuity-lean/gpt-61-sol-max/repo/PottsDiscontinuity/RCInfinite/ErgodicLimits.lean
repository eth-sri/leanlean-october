module
public import Mathlib

public import PottsDiscontinuity.RCInfinite.GeneratorMixing

@[expose] public section

open MeasureTheory Filter Topology Set


namespace PottsDiscontinuity.RCInfinite
open FK

section

variable (θ : Parameters) (i : Fin 2) (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
include hμ

section

variable {B : Set LatticeConfiguration} (hB : MeasurableSet B) (hinv : ∀ a : LatticeVertex,  edgeTranslate a  ⁻¹' B = B)
include hB hinv

theorem invariant_allOpen_independent 
     (F : Finset Edge) :
    μ.real (LatticeConfiguration.allOpen F ∩ B) =
      μ.real (LatticeConfiguration.allOpen F) * μ.real B := by
  have h := allOpen_measurable_joint_tendsto θ i μ hμ F hB
  simp_all

theorem invariant_restrict_eq_smul 
     :
    μ.restrict B =  μ B  • μ := by
  have : IsProbabilityMeasure μ := hμ.1
  apply ext_of_generate_finite LatticeConfiguration.allOpenCylinders
    LatticeConfiguration.generateFrom_allOpenCylinders.symm
    LatticeConfiguration.isPiSystem_allOpenCylinders
  · rintro A ⟨F, rfl⟩
    rw [Measure.restrict_apply (isCylinder_allOpen F).measurableSet]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _)
      (ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _))).mp
    rw [ENNReal.toReal_mul]
    exact (invariant_allOpen_independent θ i μ hμ hB hinv F).trans (mul_comm _ _)
  · simp

end

/-- The free and wired infinite-volume laws are ergodic for the full lattice
translation action. The proof uses the proved generator mixing and cylinder
determination, with no extremality or ergodicity assumption. -/
theorem isRCInfiniteVolumeLimit_interior_edge_ergodic  :
    IsEdgeTranslationErgodic μ := by
  have : IsProbabilityMeasure μ := hμ.1
  constructor
  · exact (translation_invariant θ.toP θ.toQ θ.property i μ hμ)
  · intro B hB hinv
    
    have hBB := congrArg (fun ν  => ν B) (invariant_restrict_eq_smul θ i μ hμ hB hinv)
    rw [Measure.restrict_apply hB, inter_self, Measure.smul_apply, smul_eq_mul] at hBB
    have hr := congrArg ENNReal.toReal hBB
    rw [ENNReal.toReal_mul] at hr
    
    rcases mul_eq_zero.mp (by
                             change (μ B).toReal * ((μ B).toReal - 1) = 0
                             nlinarith) with hzero | hone
    · left
      exact ((ENNReal.toReal_eq_zero_iff (μ B)).mp hzero).resolve_right (measure_ne_top μ B)
    · right
      
      rw [measure_compl hB (measure_ne_top μ B), measure_univ,  (ENNReal.toReal_eq_one_iff (μ B)).mp (by
                                                                  
                                                                  linarith) , tsub_self]

end

theorem dirac_constant_edge_ergodic (b : Bool) :
    IsEdgeTranslationErgodic (Measure.dirac  fun _ : Edge => b ) := by
  constructor
  · exact dirac_constant_translation_invariant b
  · simp_all <;> grind

/-- Ergodicity on the unchanged frozen limit predicate, including both
deterministic endpoint parameters. -/
theorem isRCInfiniteVolumeLimit_edge_ergodic
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit p q i μ) :
    IsEdgeTranslationErgodic μ := by
  by_cases hp0 : (p : ℝ) = 0
  · have hp : p = endpointParameter false := Subtype.ext hp0
    subst p
    
    rw [ rc_limit_unique (endpointParameter false) q i μ
           (Measure.dirac  fun _ => false ) hμ (isRCInfiniteVolumeLimit_endpoint q i false) ]
    exact dirac_constant_edge_ergodic false
  by_cases hp1 : (p : ℝ) = 1
  · have hp : p = endpointParameter true := Subtype.ext hp1
    subst p
    
    rw [ rc_limit_unique (endpointParameter true) q i μ
           (Measure.dirac  fun _ => true ) hμ (isRCInfiniteVolumeLimit_endpoint q i true) ]
    exact dirac_constant_edge_ergodic true
  let θ : Parameters :=
    { val := q
      property := hq
      edgeProbability := ⟨p, lt_of_le_of_ne p.property.1 (Ne.symm hp0),
        lt_of_le_of_ne p.property.2 hp1⟩ }
  exact isRCInfiniteVolumeLimit_interior_edge_ergodic θ i μ hμ

end PottsDiscontinuity.RCInfinite
