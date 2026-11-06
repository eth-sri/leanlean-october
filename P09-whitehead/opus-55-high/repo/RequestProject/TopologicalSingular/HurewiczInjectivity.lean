import RequestProject.TopologicalSingular.StationaryPi2Chain
import RequestProject.TopologicalSingular.StickSimplexQuotient
import RequestProject.TopologicalSingular.HurewiczSurjectivity


namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- A vanishing genuine Hurewicz class forces the actual based homotopy class
to be trivial. Every square is first represented by a pointed triangle; the
stationary normalization detects its class and kills its singular filling. -/
theorem singularHurewicz2_eq_zero_iff x (q : HomotopyGroup (Fin 2) X x) :
    singularHurewicz2 x q = 0 ↔ q = 1 := by
  constructor
  · intro hq
    cases' pointed_triangle_pi2_surjective (Additive.ofMul q) with a ha
    have hrep : (Quotient.mk _ (basedTriangleSquare a.map a.based)) = q := congrArg Additive.toMul ha
    rw [← hrep] at hq
    obtain ⟨b, hb⟩ := (singularHurewicz2_mk_eq_zero_iff
      _).mp hq
    have hzero := stationaryPi2Chain_boundary x b
    simp_all [hb, squareCycle_basedTriangleSquare, stationaryPi2Chain_basedTriangleCycle]
  · rintro rfl
    exact singularHurewicz2_one x
