module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Tactic

/-! # Transposition with an envelope

An estimate for adjoint test functions in a weighted `L¹` norm yields a distributional
solution *with the pointwise weight as envelope*. We apply Hahn–Banach once, on the
range of the weighted adjoint. Hilbert representation on `L²` and testing measurable
indicators identify the required density, without a separate `L¹` duality theorem.
-/

@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal

variable {E V : Type*} [AddCommGroup E] [Module ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem dominated_extension (R : E →ₗ[ℝ] V) (F : E →ₗ[ℝ] ℝ)
    (h : ∀ e, |F e| ≤ ‖R e‖) : ∃ g : V →L[ℝ] ℝ, ‖g‖ ≤ 1 ∧ ∀ e, g (R e) = F e := by
  have hk : LinearMap.ker R ≤ LinearMap.ker F := fun x hx => by
    have m := h x; rw [LinearMap.mem_ker.mp hx, norm_zero,abs_nonpos_iff] at m; exact m
  let f := ((LinearMap.ker R).liftQ F hk).comp R.quotKerEquivRange.symm.toLinearMap
  have he (x) : f (R.rangeRestrict x) = F x := by
    change R.ker.liftQ F hk (R.quotKerEquivRange.symm ⟨R x,_⟩) = _
    simp
  have hb (x : LinearMap.range R) : ‖f x‖ ≤ 1 * ‖x‖ := by
    obtain ⟨e,rfl⟩ := LinearMap.range_rangeRestrict R ▸ (show x ∈ (⊤ : Submodule ℝ _) from trivial)
    simpa [he] using h e
  let l := f.mkContinuous 1 hb
  obtain ⟨g,hg,hn⟩ := exists_extension_norm_eq _ l
  exact ⟨g,hn.le.trans (f.mkContinuous_norm_le zero_le_one hb),fun e => (hg (R.rangeRestrict e)).trans (he e)⟩

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem weighted_dual (R : E →ₗ[ℝ] Lp ℝ 2 μ) (F : E →ₗ[ℝ] ℝ) {B : X → ℝ}
    (hB : MemLp B 2 μ) (hp : 0 ≤ᵐ[μ] B) (h : ∀ e, |F e| ≤ ∫ x, B x * |R e x| ∂μ) :
    ∃ u : Lp ℝ 2 μ, (∀ᵐ x ∂μ, |u x| ≤ B x) ∧ ∀ e, (∫ x, u x * R e x ∂μ) = F e := by
  let T := (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 hB.toLp
  have hn (v) : ‖T v‖ = ∫ x, B x * |v x| ∂μ := by
    rw [L1.norm_eq_integral_norm]; apply integral_congr_ae
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) hB.toLp v, hB.coeFn_toLp,hp] with x hx e hx0
    change |(T v) x| = _; rw [show (T v) x = _ from hx]; simp [e,abs_mul,abs_of_nonneg (show 0 ≤ B x from hx0)]
  obtain ⟨g,hg,he⟩ := dominated_extension (T.toLinearMap.comp R) F (fun e => (h e).trans_eq (hn (R e)).symm)
  let u := (InnerProductSpace.toDual ℝ _).symm (g.comp T)
  have pair (v) : ⟪u,v⟫ = g (T v) := InnerProductSpace.toDual_symm_apply
  have ub (s : Set X) (hs : MeasurableSet s) (hf : μ s < ∞) : |∫ x in s, u x ∂μ| ≤ ∫ x in s, B x ∂μ := by
    let v := indicatorConstLp 2 hs hf.ne (1:ℝ)
    rw [← L2.inner_indicatorConstLp_one hs hf.ne,real_inner_comm, pair]
    apply (g.le_opNorm (T v)).trans
    apply (mul_le_of_le_one_left (norm_nonneg _) hg).trans_eq
    rw [hn,← integral_indicator hs]; apply integral_congr_ae
    filter_upwards [(show (v : X → ℝ) =ᵐ[μ] s.indicator (fun _ => (1:ℝ)) from indicatorConstLp_coeFn)] with x hx
    change B x * |v x| = _; rw [show v x = _ from hx]; by_cases hxs : x ∈ s <;> simp [hxs]
  have hu := (Lp.memLp u).integrable (by norm_num)
  have hb := hB.integrable (by norm_num)
  have h1 := ae_le_of_forall_setIntegral_le hu hb (fun s hs hf => (le_abs_self _).trans (ub s hs hf))
  have h2 := ae_le_of_forall_setIntegral_le hu.neg hb (fun s hs hf => by simpa only [Pi.neg_apply, integral_neg] using (neg_le_abs _).trans (ub s hs hf))
  refine ⟨u,h1.and h2 |>.mono fun x hx => abs_le.mpr ⟨neg_le.mp hx.2,hx.1⟩,fun e => ?_⟩
  simpa [L2.inner_def, real_inner_comm, mul_comm] using (pair (R e)).trans (he e)

end HypoellipticAleksandrov.Parabolic.Transposition
