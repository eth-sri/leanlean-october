module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureTimeScaling
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! # Literal positive-position radial and angular coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/- The open positive-position half-plane, with its actual product-plane carrier. -/
abbrev BellmanPositivePositionPlane := {q : ℝ × ℝ // 0 < q.1}

/- The source coordinates X=s³ and v=sy on positive position. -/
def bellmanAngularPoint (w : BellmanPositiveTime × ℝ) : BellmanPuncturedPlane :=
  ⟨(w.1.val ^ 3, w.1.val * w.2), by
    intro h
    exact (pow_ne_zero 3 (ne_of_gt w.1.property)) (congrArg Prod.fst h)⟩

/- The source radial measure for density degree β, with no angular density assumption. -/
def bellmanRadialWeight (β : ℝ) : Measure BellmanPositiveTime :=
  bellmanPositiveTimeVolume.withDensity (fun s => ENNReal.ofReal (s.val ^ (3 - β)))

/- The literal homogeneous representation of an arbitrary positive angular measure. -/
def bellmanAngularRep (β : ℝ) (F : Measure ℝ) : Measure BellmanPuncturedPlane :=
  Measure.map bellmanAngularPoint ((bellmanRadialWeight β).prod F)

/- The positive cubic root used in the inverse coordinate map. -/
def bellmanPositionRoot (q : BellmanPositivePositionPlane) : BellmanPositiveTime :=
  ⟨q.val.1 ^ ((3 : ℝ)⁻¹), Real.rpow_pos_of_pos q.property _⟩

/- The position root cubed is the original positive position. -/
def bellmanAngularHomeomorph :
    (BellmanPositiveTime × ℝ) ≃ₜ BellmanPositivePositionPlane where
  toFun w := ⟨(w.1.val ^ 3, w.1.val * w.2), pow_pos w.1.property 3⟩
  invFun q := (bellmanPositionRoot q, q.val.2 / (bellmanPositionRoot q).val)
  left_inv w := by
    have he : ((w.1.val ^ 3 : ℝ) ^ ((3 : ℝ)⁻¹)) = w.1.val :=
      Real.pow_rpow_inv_natCast w.1.property.le (by norm_num : (3 : ℕ) ≠ 0)
    apply Prod.ext
    · apply Subtype.ext
      exact he
    · dsimp [bellmanPositionRoot]
      rw [he, mul_div_cancel_left₀ _ w.1.property.ne']
  right_inv q := by
    apply Subtype.ext
    have _h_inl_15 : (bellmanPositionRoot q).val ^ 3 = q.val.1 := by
        exact (
      Real.rpow_inv_natCast_pow q.property.le (by norm_num : (3 : ℕ) ≠ 0)

      /- Radial-angular coordinates are a homeomorphism onto the positive-position half-plane. -/
      )
    exact Prod.ext _h_inl_15
      (mul_div_cancel₀ q.val.2 (bellmanPositionRoot q).property.ne')
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by
    have hroot : Continuous (fun q : BellmanPositivePositionPlane =>
        q.val.1 ^ ((3 : ℝ)⁻¹)) := by
      apply Continuous.rpow_const
      · fun_prop
      · intro q
        exact Or.inl q.property.ne'
    apply Continuous.prodMk
    · exact hroot.subtype_mk _
    · exact (continuous_snd.comp continuous_subtype_val).div hroot
        (fun q => (Real.rpow_pos_of_pos q.property _).ne')

/- The literal angular point map is continuous. -/
theorem continuous_bellmanAngularPoint : Continuous bellmanAngularPoint := by
  unfold bellmanAngularPoint
  fun_prop

/- Positive radial scaling acts as the kinetic dilation in the source coordinates. -/
end HypoellipticAleksandrov.KineticAleksandrov
