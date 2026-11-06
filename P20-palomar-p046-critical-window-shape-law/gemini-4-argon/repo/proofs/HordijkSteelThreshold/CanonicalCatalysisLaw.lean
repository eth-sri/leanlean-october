module

public import proofs.HordijkSteelThreshold.AmbientIndependence

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval

def ambientPartition {n : ℕ} (ω : AmbientCoord n → Prop) : CatalysisSample n :=
  ({z | ω (z.1, z.2.val)}, {z | ω (z.1, z.2.val)})

theorem ambientPartition_map (n : ℕ) (lambda : ℝ) :
    (ambientPiMeasure n lambda).map ambientPartition = uniformCatalysisMeasure n lambda := by
  have hm {P : Reaction n → Prop} [DecidablePred P] :
      (ambientPiMeasure n lambda).map (fun ω : AmbientCoord n → Prop => {z : Molecule n × Subtype P | ω (z.1, z.2.1)}) =
        setBernoulli Set.univ (catalysisP n lambda) := by
    let f : Molecule n × Subtype P → AmbientCoord n := fun z => (z.1, z.2.1)
    have hf : Function.Injective f := fun _ _ h =>
      Prod.ext (congrArg (fun z : AmbientCoord n => z.1) h) (Subtype.ext (congrArg (fun z : AmbientCoord n => z.2) h))
    have hfield : (ambientPiMeasure n lambda).map (fun ω j => ω (f j)) =
        Measure.infinitePi (fun _ : Molecule n × Subtype P => ambientCoordLaw (catalysisP n lambda)) := by
      rw [((ambientCoordinate_iIndep n lambda).precomp hf).map_fun_eq_pi_map fun j => (measurable_pi_apply (f j)).aemeasurable]
      simp_rw [ambientPiMeasure, Measure.infinitePi_map_eval]
      exact (Measure.infinitePi_eq_pi _).symm
    refine (Measure.map_map (measurable_of_finite fun v : Molecule n × Subtype P → Prop => {j | v j})
      (measurable_of_finite fun (ω : AmbientCoord n → Prop) j => ω (f j))).symm.trans ?_
    rw [hfield, setBernoulli_eq_map]
    simp only [Set.mem_univ, ambientCoordLaw, bernoulliMeasure_def]
  let B : Finset (AmbientCoord n) := Finset.univ.filter fun z => RevSeedReaction (binaryPolymerCRS n 2) z.2
  let D : Finset (AmbientCoord n) := Finset.univ.filter fun z => ¬ RevSeedReaction (binaryPolymerCRS n 2) z.2
  have hd : Disjoint B D := Finset.disjoint_left.mpr fun _ hb hd =>
    (Finset.mem_filter.mp hd).2 (Finset.mem_filter.mp hb).2
  have hind : IndepFun (fun ω : AmbientCoord n → Prop => (ambientPartition ω).1)
      (fun ω => (ambientPartition ω).2) (ambientPiMeasure n lambda) :=
    ((ambientCoordinate_iIndep n lambda).indepFun_finset B D hd fun z => measurable_pi_apply z).comp
      (measurable_of_finite fun v : B → Prop => {z : SeedCoord n | v ⟨(z.1, z.2.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.2.2⟩⟩})
      (measurable_of_finite fun v : D → Prop => {z : NonseedCoord n | v ⟨(z.1, z.2.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.2.2⟩⟩})
  have hi := hind.map_prod_eq_prod_map_map (measurable_of_finite _).aemeasurable (measurable_of_finite _).aemeasurable
  dsimp [ambientPartition] at hi
  rwa [hm, hm] at hi

@[simp] theorem catalysisOf_ambientPartition {n : ℕ} (ω : AmbientCoord n → Prop)
    (x : Molecule n) (r : Reaction n) : catalysisOf (ambientPartition ω) x r ↔ ω (x,r) := by
  by_cases h : RevSeedReaction (binaryPolymerCRS n 2) r <;>
    simp [catalysisOf, ambientPartition, h]

end HordijkSteelThreshold
