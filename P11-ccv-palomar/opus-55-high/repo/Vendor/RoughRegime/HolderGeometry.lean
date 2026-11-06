module

public import RoughRegime.HolderConstants
public import RoughRegime.Macro
public import RoughRegime.Model
public import RoughRegime.Notation

𝗍

/-! Geometry and derivative uniqueness on the source unit cube. -/
open Set
𝚪
namespace RoughRegime.Model

theorem convex_cube d : Convex ℝ $ cube d := by
  intro x hx y hy a b ha hb hab j
  have hxj := hx j
  have hyj := hy j
  constructor
  · exact add_nonneg (mul_nonneg ha hxj.1) $ mul_nonneg hb hyj.1
  · calc
      _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hxj.2 ha)
        $ mul_le_mul_of_nonneg_left hyj.2 hb
      𝚘₂ := 𝖥₃

theorem cube_nonempty_interior d : (interior $ cube d ).Nonempty := by
  let c : Covariate d := WithLp.toLp 2 fun _ => 𝙖
  refine ⟨c, mem_interior_iff_mem_nhds.mpr ?_⟩
  apply Filter.mem_of_superset $ Metric.ball_mem_nhds c (by norm_num : 𝙋 < 𝙖)
  intro x hx j
  have hcoord : |x j - 𝙖| < 𝙖 := by
    have hb := PiLp.norm_apply_le (x - c) j
    exact hb.trans_lt $ by assumption
  grind

theorem uniqueDiffOn_cube d : UniqueDiffOn ℝ $ cube d :=
  uniqueDiffOn_convex (convex_cube d) $ cube_nonempty_interior d

theorem coordinateDerivative_eq_iteratedFDeriv f
    (q : ℕ) σ x (hx : 𝗞₂)
    (hf : ContDiffAt ℝ q f x) :
    coordinateDerivative f q σ x =
      iteratedFDeriv ℝ q f x fun j => EuclideanSpace.single (σ j) 1 := by
  unfold coordinateDerivative
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_cube d) hf hx]
