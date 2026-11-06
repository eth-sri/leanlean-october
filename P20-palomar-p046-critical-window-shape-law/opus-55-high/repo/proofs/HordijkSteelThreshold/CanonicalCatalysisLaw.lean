module

public import proofs.HordijkSteelThreshold.AmbientIndependence

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval

/-- Any injectively selected ambient coordinates have the literal set-Bernoulli law. -/
theorem ambient_subfield_set_map {n : ℕ} (lambda : ℝ) {J : Type*} [Fintype J]
    (f : J → AmbientCoord n) (hf : Function.Injective f) :
    (ambientPiMeasure n lambda).map (fun ω => {j | ω $ f j}) =
      setBernoulli (Set.univ : Set J) (catalysisP n lambda) := by
  change Measure.map ((fun v : J → Prop => {j | v j}) ∘ (fun (ω : AmbientCoord n → Prop) j => ω $ f j)) _ = _
  rw [setBernoulli_eq_map, ← Measure.map_map (measurable_of_finite _) $ measurable_of_finite _,
    ((ambientCoordinate_iIndep n lambda).precomp hf).map_fun_eq_pi_map
      (fun j => (measurable_pi_apply $ f j).aemeasurable)]
  simp_rw [ambientPiMeasure, Measure.infinitePi_map_eval, ← Measure.infinitePi_eq_pi]
  rfl

def ambientPartition {n : ℕ} (ω : AmbientCoord n → Prop) : CatalysisSample n :=
  ({z | ω (z.1,z.2.val)}, {z | ω (z.1,z.2.val)})

variable (n : ℕ) (lambda : ℝ)

theorem ambientPartition_indep  :
    IndepFun (fun ω : AmbientCoord n → Prop => (ambientPartition ω).1)
      (fun ω => (ambientPartition ω).2) (ambientPiMeasure n lambda) := by
  exact ((ambientCoordinate_iIndep n lambda).indepFun_finset
    (Finset.univ.filter fun z => RevSeedReaction (binaryPolymerCRS n 2) z.2)
    (Finset.univ.filter fun z => ¬ RevSeedReaction (binaryPolymerCRS n 2) z.2)
    (Finset.disjoint_left.mpr $ by grind) measurable_pi_apply).comp
    (measurable_of_finite fun v => {z : SeedCoord n | v ⟨(z.1,z.2.val), by simpa using z.2.2⟩})
    (measurable_of_finite fun v => {z : NonseedCoord n | v ⟨(z.1,z.2.val), by simpa using z.2.2⟩})

/-- The unpartitioned iid presentation is exactly the canonical seed/nonseed
sample measure. It has the same catalysis parameter and literal reaction IDs. -/
theorem ambientPartition_map  :
    (ambientPiMeasure n lambda).map ambientPartition = uniformCatalysisMeasure n lambda := by
  have hs : (ambientPiMeasure n lambda).map (fun ω => (ambientPartition ω).1) =
      setBernoulli Set.univ (catalysisP n lambda) :=
    ambient_subfield_set_map lambda _ fun x y h => by grind
  have hn : (ambientPiMeasure n lambda).map (fun ω => (ambientPartition ω).2) =
      setBernoulli Set.univ (catalysisP n lambda) :=
    ambient_subfield_set_map lambda _ fun x y h => by grind
  have hi := (ambientPartition_indep n lambda).map_prod_eq_prod_map_map
    (measurable_of_finite _).aemeasurable (measurable_of_finite _).aemeasurable
  aesop


@[simp] theorem catalysisOf_ambientPartition {n : ℕ} (ω : AmbientCoord n → Prop)
    (x : Molecule n) (r : Reaction n) : catalysisOf (ambientPartition ω) x r ↔ ω (x,r) := by
  by_cases h : RevSeedReaction (binaryPolymerCRS n 2) r <;>
    simp [catalysisOf, ambientPartition]

end HordijkSteelThreshold
