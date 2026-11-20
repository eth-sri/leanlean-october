module

public import DedekindZetaZeroFree.MeasureTheory.SphereCoordinateDistribution

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse

open MeasureTheory
open Set
open scoped Pointwise RealInnerProductSpace ENNReal

section

variable (g : Ambient ≃ₗᵢ[ℝ] Ambient)

noncomputable def sphereRotation (x : Sphere) : Sphere :=
  ⟨g x, by simpa using x.property⟩
lemma sphereRotation_continuous :
    Continuous (sphereRotation g) := (g.continuous.comp continuous_subtype_val).subtype_mk _
lemma sphereRotation_cone_preimage (s : Set Sphere) :
    g ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) =
    Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereRotation g ⁻¹' s)) := by apply @RawSphereProjection.rotation_cone_preimage <;> assumption
lemma sphereRotation_preserving :
    MeasurePreserving (sphereRotation g) (volume : Measure Ambient).toSphere
      (volume : Measure Ambient).toSphere := by apply @RawSphereProjection.rotation_preserving <;> assumption
lemma sphereArea_rotation_preserving :
    MeasurePreserving (sphereRotation g) sphereArea sphereArea := (sphereRotation_preserving g).smul_measure _
lemma sphereArea_projection_rotation (x : Sphere) :
    Measure.map (fun y : Sphere => (1 - inner ℝ (g x) (y : Ambient)) / 2) sphereArea =
    Measure.map (fun y : Sphere => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2) sphereArea := by
  calc
    _ = Measure.map (fun y : Sphere => (1 - inner ℝ (g x) (y : Ambient)) / 2)
        (Measure.map (sphereRotation g) sphereArea) := by
          rw [(sphereArea_rotation_preserving g).map_eq]
    _ = _ := by
      rw [Measure.map_map (by fun_prop) (sphereRotation_continuous g).measurable]
      congr 1
      ext y
      simp [Function.comp_def, sphereRotation, g.inner_map_map]

end
lemma sphereArea_projection_independent (x z : Sphere) :
    Measure.map (fun y : Sphere => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2) sphereArea =
    Measure.map (fun y : Sphere => (1 - inner ℝ (z : Ambient) (y : Ambient)) / 2) sphereArea := by
  let g := (ℝ ∙ ((z : Ambient) - (x : Ambient)))ᗮ.reflection
  have hg : g z = (x : Ambient) := Submodule.reflection_sub (by
    rw [mem_sphere_zero_iff_norm.mp z.property, mem_sphere_zero_iff_norm.mp x.property])
  simpa [hg] using sphereArea_projection_rotation g z

lemma sphereProjection_raw_mass :
    (volume : Measure Ambient).toSphere univ = ENNReal.ofReal (4 * Real.pi) := by apply @RawSphereProjection.raw_mass <;> assumption

noncomputable def sphereProjection_split : Ambient ≃ᵐ ℝ × EuclideanSpace ℝ (Fin 2) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm |>.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))
lemma sphereProjection_split_preserving : MeasurePreserving sphereProjection_split := by apply @RawSphereProjection.split_preserving <;> assumption
section

variable (z : ℝ) (w : EuclideanSpace ℝ (Fin 2))

lemma sphereProjection_split_symm_apply :
    sphereProjection_split.symm (z,w) = WithLp.toLp 2 (Fin.cons z w.ofLp) := by apply @RawSphereProjection.split_symm_apply <;> assumption
lemma sphereProjection_split_norm_sq :
    ‖sphereProjection_split.symm (z,w)‖ ^ 2 = z ^ 2 + ‖w‖ ^ 2 := by apply @RawSphereProjection.split_norm_sq <;> assumption

end

lemma sphereProjection_north_cone (t : ℝ) (i : Fin 3) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' {y : Sphere | t ≤ (y : Ambient) i}) =
      {v : Ambient | 0 < ‖v‖ ∧ ‖v‖ < 1 ∧ t * ‖v‖ ≤ v i} := by apply @RawSphereProjection.north_cone <;> assumption
lemma sphereProjection_north_cone_Fubini (t : ℝ) :
    volume (Ioo (0 : ℝ) 1 • (Subtype.val '' {y : Sphere | t ≤ (y : Ambient) 0})) =
      ∫⁻ z : ℝ, volume {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖sphereProjection_split.symm (z,w)‖ ∧
        ‖sphereProjection_split.symm (z,w)‖ < 1 ∧
        t * ‖sphereProjection_split.symm (z,w)‖ ≤ z} := by apply @RawSphereProjection.north_cone_Fubini <;> assumption
section

variable {t z : ℝ} (ht : 0 < t)

include ht in
lemma sphereProjection_north_slice_lower (ht1 : t ≤ 1)
    (hz : 0 < z) (hzt : z < t) :
    {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖sphereProjection_split.symm (z,w)‖ ∧
        ‖sphereProjection_split.symm (z,w)‖ < 1 ∧
        t * ‖sphereProjection_split.symm (z,w)‖ ≤ z} =
      Metric.closedBall 0 (Real.sqrt ((z / t) ^ 2 - z ^ 2)) := by apply @RawSphereProjection.north_slice_lower <;> assumption
include ht in
lemma sphereProjection_north_slice_upper (htz : t ≤ z)
    (hz1 : z < 1) :
    {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖sphereProjection_split.symm (z,w)‖ ∧
        ‖sphereProjection_split.symm (z,w)‖ < 1 ∧
        t * ‖sphereProjection_split.symm (z,w)‖ ≤ z} =
      Metric.ball 0 (Real.sqrt (1 - z ^ 2)) := by apply @RawSphereProjection.north_slice_upper <;> assumption
include ht in
lemma sphereProjection_north_slice_empty
    (hz : z ≤ 0 ∨ 1 ≤ z) :
    {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖sphereProjection_split.symm (z,w)‖ ∧
        ‖sphereProjection_split.symm (z,w)‖ < 1 ∧
        t * ‖sphereProjection_split.symm (z,w)‖ ≤ z} = ∅ := by apply @RawSphereProjection.north_slice_empty <;> assumption
include ht in
lemma sphereProjection_north_slice_volume_lower (ht1 : t ≤ 1)
    (hz : 0 < z) (hzt : z < t) :
    volume {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖sphereProjection_split.symm (z,w)‖ ∧
        ‖sphereProjection_split.symm (z,w)‖ < 1 ∧
        t * ‖sphereProjection_split.symm (z,w)‖ ≤ z} =
      ENNReal.ofReal (Real.pi * ((z / t) ^ 2 - z ^ 2)) := by apply @RawSphereProjection.north_slice_volume_lower <;> assumption
include ht in
lemma sphereProjection_north_slice_volume_upper (htz : t ≤ z)
    (hz1 : z < 1) :
    volume {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖sphereProjection_split.symm (z,w)‖ ∧
        ‖sphereProjection_split.symm (z,w)‖ < 1 ∧
        t * ‖sphereProjection_split.symm (z,w)‖ ≤ z} =
      ENNReal.ofReal (Real.pi * (1 - z ^ 2)) := by apply @RawSphereProjection.north_slice_volume_upper <;> assumption

end

section

variable {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)

include ht ht1 in
lemma sphereProjection_north_cone_integrals :
    volume (Ioo (0 : ℝ) 1 • (Subtype.val '' {y : Sphere | t ≤ (y : Ambient) 0})) =
      (∫⁻ z in Ioo 0 t, ENNReal.ofReal (Real.pi * ((z / t) ^ 2 - z ^ 2))) +
      (∫⁻ z in Ico t 1, ENNReal.ofReal (Real.pi * (1 - z ^ 2))) := by apply @RawSphereProjection.north_cone_integrals <;> assumption
include ht ht1 in
lemma sphereProjection_north_cone_volume :
    volume (Ioo (0 : ℝ) 1 • (Subtype.val '' {y : Sphere | t ≤ (y : Ambient) 0})) =
      ENNReal.ofReal (2 * Real.pi / 3 * (1 - t)) := by apply @RawSphereProjection.north_cone_volume <;> assumption

end

lemma sphereArea_projection_eq_coordinate (x : Sphere) (i : Fin 3) :
    Measure.map (fun y : Sphere => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2)
      sphereArea =
    Measure.map (fun y : Sphere => (1 - (y : Ambient) i) / 2) sphereArea := by
  let z : Sphere := ⟨EuclideanSpace.single i (1 : ℝ), by
    simp⟩
  simpa [z, EuclideanSpace.inner_single_left] using sphereArea_projection_independent x z

lemma sphereProjection_raw_north_cap {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (volume : Measure Ambient).toSphere {y : Sphere | t ≤ (y : Ambient) 0} =
      ENNReal.ofReal (2 * Real.pi * (1-t)) := by
  rw [Measure.toSphere_apply' _ (by measurability), sphereProjection_north_cone_volume ht ht1]
  have hd : Module.finrank ℝ Ambient = 3 := by simp [Ambient]
  simp only [hd, Nat.cast_ofNat]
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

lemma sphereProjection_raw_antipodal (t : ℝ) :
    (volume : Measure Ambient).toSphere {y : Sphere | (y : Ambient) 0 ≤ t} =
      (volume : Measure Ambient).toSphere {y : Sphere | -t ≤ (y : Ambient) 0} := by
  let g : Ambient ≃ₗᵢ[ℝ] Ambient := LinearIsometryEquiv.neg ℝ
  have hm : MeasurableSet {y : Sphere | (y : Ambient) 0 ≤ t} := by measurability
  have h := (sphereRotation_preserving g).measure_preimage hm.nullMeasurableSet
  have heq : sphereRotation g ⁻¹' {y : Sphere | (y : Ambient) 0 ≤ t} =
      {y : Sphere | -t ≤ (y : Ambient) 0} := by
    ext y
    simp only [mem_preimage, mem_setOf_eq]
    change -(y : Ambient) 0 ≤ t ↔ -t ≤ (y : Ambient) 0
    constructor <;> intro hy <;> linarith
  rw [heq] at h
  exact h.symm

theorem sphereArea_uniform_projection (x : Sphere) :
    Measure.map (fun y : Sphere => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2)
      sphereArea = (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1) := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.PolynomialFunkHecke.uniform_projection <;> assumption

end DedekindZetaZeroFree.ComplexFractionalInverse
