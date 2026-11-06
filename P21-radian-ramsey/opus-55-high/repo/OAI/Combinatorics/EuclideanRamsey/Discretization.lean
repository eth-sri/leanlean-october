module

public import OAI.Combinatorics.EuclideanRamsey.LatticeMoments

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Pointwise ContDiff

set_option autoImplicit true
namespace OAI.EuclideanRamsey
set_option hygiene false
notation "𝔡" => ∑ γ ∈ E, d γ
local notation "𝔠" => ∑ γ ∈ E, AddMonoidAlgebra.single γ (q γ)
local notation "𝔟" => (v γ)
local notation "𝔞" => (∫ x, f x)
notation "𝔫" => (n:ℝ)
notation "𝔩" => (latticeSample n γ)

variable {k n : ℕ}

lemma compact_taylor_bound [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ K, 0 ≤ K ∧ ∀ x h,
      |f (x+h)-f x-fderiv ℝ f x h-(1/2:ℝ)*iteratedFDeriv ℝ 2 f x ![h,h]| ≤ K*‖h‖^3 := by
  obtain ⟨K,hK⟩ := (hf.continuous_iteratedFDeriv (by norm_cast)).bounded_above_of_compact_support
    (hfc.iteratedFDeriv 3)
  refine ⟨K,((norm_nonneg _).trans (hK 0)),fun x h => ?_⟩
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n := 2) (x := x) (y := h)
    (fun t ht => (hf.of_le (by norm_cast)).contDiffAt)
  have hvec : (fun _ => h) = ![h,h] := by ext i
                                          fin_cases i <;> rfl
  simp [Finset.sum_range_succ, hvec] at ht
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun t => (1-t)^2 * iteratedFDeriv ℝ 3 f (x+t • h) (fun _ => h)) fun t ht => by
    simp at ht
    have := ((iteratedFDeriv ℝ 3 f (x+t•h)).le_opNorm fun _ => h).trans
      (mul_le_mul_of_nonneg_right (hK _) (by positivity))
    simp at this
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by rw [norm_pow, Real.norm_eq_abs, sq_abs]; nlinarith)).trans this
  simp [abs_le] at this
  rw [ht, abs_le]
  constructor <;> nlinarith

lemma linear_moment_contract S (q : ι → ℝ) (v : ι → 𝕍 k)
    (h : ∀ j, ∑ γ ∈ S,q γ*v γ j = 0) (L : 𝕍 k →L[ℝ] ℝ) : ∑ γ ∈ S,q γ*L 𝔟 = 0 := by
  conv_lhs => arg 2
              intro γ
              rw [pi_expand 𝔟]
  simp [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [← mul_assoc, ← Finset.sum_mul, h]

lemma bilinear_moment_contract S (q : ι → ℝ) (v : ι → 𝕍 k)
    (L : 𝕍 k →L[ℝ] 𝕍 k →L[ℝ] ℝ) :
    ∑ γ ∈ S,q γ*L 𝔟 𝔟 =
      ∑ j,∑ l,(∑ γ ∈ S,q γ*v γ j*v γ l)*L (Pi.single j 1) (Pi.single l 1) := by
  conv_lhs => arg 2
              intro γ
              rw [pi_expand 𝔟]
  simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm_cycle]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans (by grind)

abbrev realLattice (k : ℕ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k)))
def latticeSample (n : ℕ) (γ : Fin k → ℤ) : 𝕍 k := fun j => γ j/n

notation "𝔾" n:max => 𝔫⁻¹ • (realLattice k : Set (𝕍 k))

section
variable (hn : n ≠ 0)
include hn

lemma latticeSample_injective : Function.Injective (@latticeSample k n) :=
  fun γ δ h => funext fun j => by simpa [latticeSample, hn] using congr_fun h j

lemma mem_grid x :
    x ∈ 𝔾 n ↔ x ∈ Set.range (latticeSample n) := by
  have : NeZero n := ⟨hn⟩
  rw [← Submodule.coe_pointwise_smul, SetLike.mem_coe, BoxIntegral.unitPartition.mem_smul_span_iff]
  simp [latticeSample, funext_iff, div_eq_iff (Nat.cast_ne_zero.2 hn : 𝔫 ≠ 0), Classical.skolem, mul_comm]

lemma bounded_grid_finite
    (hs : Bornology.IsBounded s) :
    (s ∩ 𝔾 n).Finite := by
  rw [← Submodule.coe_pointwise_smul, ZSpan.smul _ (inv_ne_zero (mod_cast hn))]
  exact ZSpan.setFinite_inter _ hs

lemma lattice_tsum_eq_grid s
    (f : 𝕍 k → ℝ) (hf : Function.support f ⊆ s) :
    (∑' γ : Fin k → ℤ, f 𝔩) =
      ∑' x : ↑(s ∩ 𝔾 n), f x := by
  rw [tsum_subtype, ← (latticeSample_injective hn).tsum_eq fun x hx =>
    (mem_grid hn x).1 (Set.mem_of_indicator_ne_zero hx).2]
  congr with γ
  by_cases h : f 𝔩 = 0
  · rw [h, eq_comm, Set.indicator_apply_eq_zero]
    exact fun _ => h
  simp [hf h, mem_grid hn]

lemma latticeSample_finite_support
    {f : 𝕍 k → ℝ} (hf : HasCompactSupport f) :
    Function.HasFiniteSupport (fun γ => f 𝔩) :=
  ((bounded_grid_finite hn hf.isCompact.isBounded).preimage (latticeSample_injective hn).injOn).subset
    fun γ h => ⟨subset_closure h, (mem_grid hn _).2 ⟨γ, rfl⟩⟩

end

theorem lattice_riemann_perturb f
    (g : ℕ → 𝕍 k → ℝ) (hf : Continuous f) (hR : 0 < R)
    (hfs : Function.support f ⊆ Metric.closedBall 0 R)
    (hgs : ∀ n, Function.support (g n) ⊆ Metric.closedBall 0 R)
    ε (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, 1 ≤ n → ∀ x ∈ Metric.closedBall 0 R, |g n x-f x| ≤ ε n) :
    Tendsto (fun n => (∑' γ : Fin k → ℤ, g n 𝔩)/𝔫^k)
      atTop (𝓝 𝔞) := by
  have hfront : volume (frontier (Metric.closedBall (0 : 𝕍 k) R)) = 0 :=
    measure_mono_null Metric.frontier_closedBall_subset_sphere (volume.addHaar_sphere_of_ne_zero 0 hR.ne')
  have h := tendsto_tsum_div_pow_atTop_integral _ f hf Metric.isBounded_closedBall
    measurableSet_closedBall hfront
  have hc := hε.mul (tendsto_card_div_pow_atTop_volume _ Metric.isBounded_closedBall
    measurableSet_closedBall hfront)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
    Function.notMem_support.1 (mt (@hfs x) hx)] at h
  rw [zero_mul] at hc
  simp only [Fintype.card_fin] at h hc
  rw [← add_zero 𝔞]
  refine (h.add (squeeze_zero_norm' (f := fun n : ℕ => (∑' x : ↑(Metric.closedBall 0 R ∩ 𝔾 n), g n x)/𝔫^k - (∑' x : ↑(Metric.closedBall 0 R ∩ 𝔾 n), f x)/𝔫^k) ?_ hc)).congr' ?_ <;>
    filter_upwards [eventually_ge_atTop 1] with n hn
  · have := (bounded_grid_finite (by linarith) (Metric.isBounded_closedBall (x := (0 : 𝕍 k)) (r := R))).fintype
    rw [tsum_fintype, tsum_fintype, ← sub_div, ← Finset.sum_sub_distrib, Real.norm_eq_abs, abs_div,
      Nat.card_eq_fintype_card, mul_div_assoc', abs_of_nonneg (by positivity : (0:ℝ) ≤ n^k)]
    gcongr
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_card_nsmul _ _ _ fun x _ => hbound n hn x.1 x.2.1).trans_eq ?_)
    simp [mul_comm]
  · rw [lattice_tsum_eq_grid (by omega) _ _ (hgs n)]
    ring

theorem lattice_riemann (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun n => (∑' γ : Fin k → ℤ, f 𝔩)/𝔫^k) atTop (𝓝 𝔞) := by
  obtain ⟨R,hR,hfR⟩ := hfc.exists_pos_le_norm
  have hs : Function.support f ⊆ Metric.closedBall 0 R := fun x hx =>
    mem_closedBall_zero_iff.2 (not_le.1 (hx ∘ hfR x)).le
  exact lattice_riemann_perturb f (fun _ => f) hf hR hs (fun _ => hs) 0 tendsto_const_nhds (by simp)

notation "𝒯" d:max δ:max => ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext d (δ-γ)
notation "𝒩" d:max => ∑ δ ∈ ν.coeff.support + E, max (-(𝒯 d δ)) 0*w δ

lemma rationalize_convolution ν (w : Lattice k → ℝ) η
    (ha : Function.HasFiniteSupport a)
    (hp : 0 < ∑' γ,a γ)
    (hn : (∑' δ,max (-(∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*a (δ-γ))) 0*w δ) <
      η*∑' γ,a γ) :
    ∃ b,
      0 < (mass b : ℝ) ∧ (∑' δ,max (-((ν*b).coeff δ:ℝ)) 0*w δ) < η*mass b := by
  let E := ha.toFinset
  let ext (d : Lattice k → ℝ) γ := (if γ ∈ E then 1 else 0) * d γ
  have hext : ext a = a := funext fun γ => by
    by_cases h : γ ∈ E
    · simp [ext, h]
    simp [ext, Function.notMem_support.1 (mt ha.mem_toFinset.2 h)]
  have hsum d : ∑' γ, ext d γ = 𝔡 :=
    (tsum_eq_sum fun γ h => by grind).trans (Finset.sum_congr rfl fun γ h => by grind)
  have hN d : (∑' δ,max (-(𝒯 d δ)) 0*w δ) =
      𝒩 d :=
    tsum_eq_sum fun δ hδ => by
      rw [Finset.sum_eq_zero fun γ hγ => by
        simp [ext]
        exact fun h => (hδ (Finset.mem_add.mpr ⟨γ,hγ,δ-γ,h,by abel⟩)).elim]
      simp
  obtain ⟨q, hq0, hqN⟩ := (DenseRange.piMap fun _ => Rat.denseRange_cast).exists_mem_open
    ((isOpen_lt continuous_const (by fun_prop : Continuous fun d => 𝔡)).inter
    (isOpen_lt (by fun_prop : Continuous fun d => 𝒩 d) (by fun_prop :
      Continuous fun d => η * 𝔡)))
    ⟨a, by simpa [← hsum, hext] using hp, by simpa [← hN, ← hsum, hext] using hn⟩
  have hb x : (((𝔠).coeff x : ℚ) : ℝ) = ext (fun i => q i) x := by
    simp [ext, Finsupp.single_apply, apply_ite (Rat.cast : ℚ → ℝ)]
  have hm : (mass (𝔠) : ℝ) = ∑ γ ∈ E, (q γ : ℝ) := by
    simp [moments_linear]
  refine ⟨_, by rw [hm]; exact hq0, ?_⟩
  have hc δ : (((ν * 𝔠).coeff δ : ℚ) : ℝ) =
      𝒯 (fun i => q i) δ := by
    simp [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum, neg_add_eq_sub, ← hb]
  simp only [hc, hN, hm]
  exact hqN
