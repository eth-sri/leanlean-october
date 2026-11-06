module

public import GS.Shared.GeneratorAction
public import GS.Shared.LocalSections

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Smooth minimum-physical-norm lifting on a fixed shared orbit

At a point g.P the canonical lift is Ad(g) D_P^dagger (g^-1.Z).
A smooth local factor section gives a smooth formula; equivariance makes
all such local formulas agree. The carrier may be singular, even zero.
No smooth pseudoinverse across changing orbit ranks is assumed.
-/


noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS Set Filter
open scoped Topology Manifold
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (right left : Pattern 𝕜 n) (P : 𝕄)
local instance smoothLiftNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance smoothLiftChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P

/-- Polynomial transport of a fixed linear lift. The model projections only
provide total extensions off the shared factor group. -/
def transportedMinimumNormLift (p : 𝕄 × (𝕄 × 𝕄)) : PairGenerator right left :=
  let v := minimumNormLift right left P (p.1ᴴ * p.2.2 * p.2.1)
  (modelProjection left (p.1 * v.1.val * p.1ᴴ),
   modelProjection right (p.2.1 * v.2.val * p.2.1ᴴ))

theorem transportedMinimumNormLift_smooth :
    ContDiff ℝ ⊤ (transportedMinimumNormLift right left P) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hL : ContDiffAt ℝ ⊤ (fun q : 𝕄 × (𝕄 × 𝕄) => q.1) p := contDiffAt_fst
  have hR : ContDiffAt ℝ ⊤ (fun q : 𝕄 × (𝕄 × 𝕄) => q.2.1) p := contDiffAt_snd.fst
  have hZ : ContDiffAt ℝ ⊤ (fun q : 𝕄 × (𝕄 × 𝕄) => q.2.2) p := contDiffAt_snd.snd
  have hv := (minimumNormLift right left P).contDiff.contDiffAt.comp p
    (smooth_mul_at (smooth_mul_at (smooth_conjTranspose_at hL) hZ) hR)
  have hvL := (contDiff_val _).contDiffAt.comp p hv.fst
  have hvR := (contDiff_val _).contDiffAt.comp p hv.snd
  exact ((modelProjection left).contDiff.contDiffAt.comp p
    (smooth_mul_at (smooth_mul_at hL hvL) (smooth_conjTranspose_at hL))).prodMk
    ((modelProjection right).contDiff.contDiffAt.comp p
      (smooth_mul_at (smooth_mul_at hR hvR) (smooth_conjTranspose_at hR)))

section
variable (g : Factors right left)
theorem transportedMinimumNormLift_on_factors (Z : 𝕄) :
    transportedMinimumNormLift right left P (Factor.matrix g.1, (Factor.matrix g.2, Z)) =
      minimumNormLift right left (g • P) Z := by
  rw [minimumNormLift_factor_formula]
  have he : g⁻¹ • Z = (Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2 := by
    change (Factor.matrix g.1)ᴴ * Z * ((Factor.matrix g.2)ᴴ)ᴴ = _
    simp
  rw [he]
  apply Prod.ext
  · exact modelProjection_inclusion (generatorAction g
      (minimumNormLift right left P ((Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2))).1
  · exact modelProjection_inclusion (generatorAction g
      (minimumNormLift right left P ((Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2))).2

/-- A fixed local section produces an ambient extension near its source. -/
def localMinimumNormLift (p : 𝕄 × 𝕄) : PairGenerator right left :=
  let q := localFactors right left P g p.1
  transportedMinimumNormLift right left P (Factor.matrix q.1, (Factor.matrix q.2, p.2))

theorem localMinimumNormLift_eq (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source)
    (Z : 𝕄) :
    localMinimumNormLift right left P g (X.val, Z) = minimumNormLift right left X.val Z := by
  have he : localFactors right left P g X.val • P = X.val :=
    congrArg Subtype.val (localFactors_right_inverse right left P g X hX)
  change transportedMinimumNormLift right left P _ = _
  rw [transportedMinimumNormLift_on_factors, he]

theorem localMinimumNormLift_smooth_at (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source)
    (Z : 𝕄) :
    ContDiffAt ℝ ⊤ (localMinimumNormLift right left P g) (X.val, Z) := by
  have hL := (localFactors_left_matrix_smooth_at right left P g X hX).comp
    (X.val, Z) contDiffAt_fst
  have hR := (localFactors_right_matrix_smooth_at right left P g X hX).comp
    (X.val, Z) contDiffAt_fst
  exact (transportedMinimumNormLift_smooth right left P).contDiffAt.comp
    (X.val, Z) (by fun_prop)

end

/-- Joint smoothness on the whole fixed orbit times the ambient matrix space. -/
theorem minimumNormLift_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄)))
      (𝓘(ℝ, PairGenerator right left)) ⊤
      (fun p : MatrixOrbit right left P × 𝕄 => minimumNormLift right left p.1.val p.2) := by
  intro p
  let g := preferredFactor P p.1
  have h₀ : p.1 ∈ (translatedOrbitSlice right left P g).source := by
    simpa only [g, preferredFactor_spec] using translatedOrbitSlice_centre_mem right left P g
  have hinc : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄)))
      (𝓘(ℝ, 𝕄 × 𝕄)) ⊤ (fun q : MatrixOrbit right left P × 𝕄 => (q.1.val, q.2)) :=
    ((sharedOrbit_val_contMDiff right left P).comp contMDiff_fst).prodMk_space contMDiff_snd
  have hs := ContDiffAt.comp_contMDiffAt
    (f := fun q : MatrixOrbit right left P × 𝕄 => (q.1.val, q.2))
    (g := localMinimumNormLift right left P g)
    (localMinimumNormLift_smooth_at right left P g p.1 h₀ p.2) (hinc p)
  apply hs.congr_of_eventuallyEq
  have hn :=
    (continuous_fst.continuousAt).eventually
      ((translatedOrbitSlice right left P g).open_source.mem_nhds h₀)
  filter_upwards [hn] with q hq
  exact (localMinimumNormLift_eq right left P g q.1 hq q.2).symm

end GS.Shared
