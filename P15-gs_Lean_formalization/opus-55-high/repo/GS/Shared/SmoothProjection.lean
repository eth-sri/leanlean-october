module

public import GS.Shared.LocalSections
public import GS.Shared.TangentBridge

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Joint smoothness of the exact shared tangent projector

On a local smooth factor section the projector is conjugate to the fixed
Frobenius projector at P.  Equivariance makes these formulas agree.  This
proves smoothness on the whole actual shared orbit without a global smooth
factor choice, an entrywise overlap mask, or a variable-rank pseudoinverse
assumption.  The carrier P is arbitrary.
-/


noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS Set Filter
open scoped Topology Manifold
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (right left : Pattern 𝕜 n) (P : 𝕄)
local instance smoothProjectionNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance smoothProjectionChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P

section
variable (g : Factors right left)
/-- Matrix form of equivariance with arbitrary shared unitary factors. -/
theorem pointProjection_factor_formula (Z : 𝕄) :
    pointProjection right left (g • P) Z =
      Factor.matrix g.1 * pointProjection right left P
        ((Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2) * (Factor.matrix g.2)ᴴ := by
  have h := pointProjection_equivariant g P (g⁻¹ • Z)
  rw [smul_inv_smul] at h
  have hi : g⁻¹ • Z = (Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2 := by
    change (Factor.matrix g.1)ᴴ * Z * ((Factor.matrix g.2)ᴴ)ᴴ = _
    simp
  simp_all

/-- An ambient smooth extension valid near the source of a fixed slice. -/
def localProjectionFormula (p : 𝕄 × 𝕄) : 𝕄 :=
  let q := localFactors right left P g p.1
  Factor.matrix q.1 * pointProjection right left P
    ((Factor.matrix q.1)ᴴ * p.2 * Factor.matrix q.2) * (Factor.matrix q.2)ᴴ

theorem localProjectionFormula_eq (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source)
    (Z : 𝕄) :
    localProjectionFormula right left P g (X.val, Z) =
      pointProjection right left X.val Z := by
  have he : localFactors right left P g X.val • P = X.val :=
    congrArg Subtype.val (localFactors_right_inverse right left P g X hX)
  have h := pointProjection_factor_formula right left P
    (localFactors right left P g X.val) Z
  aesop

theorem localProjectionFormula_smooth_at (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source)
    (Z : 𝕄) :
    ContDiffAt ℝ ⊤ (localProjectionFormula right left P g) (X.val, Z) := by
  have hL := (localFactors_left_matrix_smooth_at right left P g X hX).comp
    (X.val, Z) contDiffAt_fst
  have hR := (localFactors_right_matrix_smooth_at right left P g X hX).comp
    (X.val, Z) contDiffAt_fst
  have hcore := smooth_mul_at (smooth_mul_at (smooth_conjTranspose_at hL) contDiffAt_snd) hR
  have hproj := (pointProjection right left P).contDiff.contDiffAt.comp (X.val, Z) hcore
  exact smooth_mul_at (smooth_mul_at hL hproj) (smooth_conjTranspose_at hR)

end

/-- The exact point-only projector is smooth jointly in the orbit point and
ambient vector.  The topology and tangent space are those of the new atlas. -/
theorem pointProjection_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄)))
      (𝓘(ℝ, 𝕄)) ⊤ (fun p : MatrixOrbit right left P × 𝕄 =>
        pointProjection right left p.1.val p.2) := by
  intro p
  let g := preferredFactor P p.1
  have h₀ : p.1 ∈ (translatedOrbitSlice right left P g).source := by
    simpa only [g, preferredFactor_spec] using translatedOrbitSlice_centre_mem right left P g
  have hinc : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄)))
      (𝓘(ℝ, 𝕄 × 𝕄)) ⊤ (fun q : MatrixOrbit right left P × 𝕄 =>
        (q.1.val, q.2)) :=
    ((sharedOrbit_val_contMDiff right left P).comp contMDiff_fst).prodMk_space contMDiff_snd
  have hs := ContDiffAt.comp_contMDiffAt
    (f := fun q : MatrixOrbit right left P × 𝕄 => (q.1.val, q.2))
    (g := localProjectionFormula right left P g)
    (localProjectionFormula_smooth_at right left P g p.1 h₀ p.2) (hinc p)
  apply hs.congr_of_eventuallyEq
  have hn : ∀ᶠ q : MatrixOrbit right left P × 𝕄 in 𝓝 p,
      q.1 ∈ (translatedOrbitSlice right left P g).source :=
    (continuous_fst.continuousAt).eventually
      ((translatedOrbitSlice right left P g).open_source.mem_nhds h₀)
  filter_upwards [hn] with q hq
  exact (localProjectionFormula_eq right left P g q.1 hq q.2).symm

end GS.Shared
