module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNorm
public import HypoellipticAleksandrov.Parabolic.LocalGluing
public import HypoellipticAleksandrov.Parabolic.WeakJetCutoff
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.ContactMap
import all HypoellipticAleksandrov.Parabolic.ParabolicMollifierJetCauchy
import all HypoellipticAleksandrov.Parabolic.ParabolicMorreyNorm
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
import all HypoellipticAleksandrov.Parabolic.WeakJetExtension
import all HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import PDEFoundation.Calculus.RegularityOrder


open private HypoellipticAleksandrov.Parabolic.velocityHessian_tsupport from HypoellipticAleksandrov.Parabolic.WeakJetExtension
open private HypoellipticAleksandrov.Parabolic.velocityHessian_compact from HypoellipticAleksandrov.Parabolic.WeakJetProduct
open private HypoellipticAleksandrov.Parabolic.velocityGradient_tsupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
open private HypoellipticAleksandrov.Parabolic.velocityHessian_continuous from HypoellipticAleksandrov.Parabolic.ParabolicMorreyNorm
open private HypoellipticAleksandrov.Parabolic.timeDerivative_tsupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
open private HypoellipticAleksandrov.Parabolic.velocityGradient_continuous from HypoellipticAleksandrov.Parabolic.ParabolicMorreyNorm
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
open private HypoellipticAleksandrov.Parabolic.timeDerivative_compact from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.parabolicExponent_one_le from HypoellipticAleksandrov.Parabolic.ParabolicMollifierJetCauchy


/-!
This module fixes a normalized reference collar cutoff and derives its exact
selected-jet product estimate from the four restricted-component `MemLp`
certificates. It proves no Hölder, PDE, or representative theorem.
-/

 public section



open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

/-- The literal closed reference collar is contained in the open unit source box. -/
private theorem reference_closed_collar_subset_unit_box (d : Nat) :
    parabolicClosedBox (d := d) 1 (1 / 2 : Real) (1 / 4 : Real) 0 ⊆
      parabolicBox  1 1 0 0 := by
  rintro ⟨t, v⟩ hz
  rw [mem_parabolicClosedBox_iff] at hz
  rw [mem_parabolicBox_iff]
  refine ⟨?_, ?_, ?_⟩
  · norm_num at hz ⊢
    linarith
  · norm_num at hz ⊢
    linarith
  · intro i
    exact lt_of_le_of_lt (hz.2.2 i) (by norm_num)

variable (d : Nat)

/-- The closed unit coordinate box contains the closure of the open unit source box. -/
private theorem closure_reference_unit_box_subset_closed  :
    closure (parabolicBox  1 1 0 (0 : PDE.Vec d)) ⊆
      parabolicClosedBox  1 1 0 0 := by
  refine closure_minimal ?_ (isClosed_parabolicClosedBox 1 1 0 0)
  rintro ⟨t, v⟩ hz
  rw [mem_parabolicBox_iff] at hz
  rw [mem_parabolicClosedBox_iff]
  exact ⟨hz.1.le, hz.2.1.le, fun i => (hz.2.2 i).le⟩

/-- The open unit source box has compact closure. -/
private theorem isCompact_closure_reference_unit_box  :
    IsCompact (closure (parabolicBox  1 1 0 (0 : PDE.Vec d))) := IsCompact.of_isClosed_subset (isCompact_parabolicClosedBox 1 1 0 0)
    isClosed_closure (closure_reference_unit_box_subset_closed d)

variable {d : Nat}

section
variable {U : HypoellipticAleksandrov.Parabolic.Region d} {eta q : HypoellipticAleksandrov.Parabolic.ScalarField d} (hU : IsOpen U) (heta : ContDiff Real 2 eta) (hetaU : tsupport eta ⊆ U) (hq : ContDiffOn Real 2 q U) (z : TimeVelocity d)

include hU heta hetaU hq
/-- The literal time derivative of a cutoff product, valid also outside the
locality set because the cutoff is zero on a neighbourhood there. -/
private theorem timeDerivative_cutoff_mul
      :
    timeDerivative (fun y => eta y * q y) z =
      eta z * timeDerivative q z + q z * timeDerivative eta z := by
  by_cases hz : z ∈ U
  · unfold timeDerivative
    change (fderiv Real (eta * q) z) (1, 0) = _
    rw [fderiv_mul (heta.differentiable (by norm_num) z)
      ((hq.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ·
    have hzero : eta =ᶠ[𝓝 z] fun _  => (0 ) :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hzeta => hz (hetaU hzeta))
    have hproduct : (fun y => eta y * q y) =ᶠ[𝓝 z] fun _  => (0 ) := by
      filter_upwards [hzero] with y hy
      simp [hy]

    have htime_eta : timeDerivative eta z = 0 := by
      unfold timeDerivative
      rw [hzero.fderiv_eq]
      simp
    have htime_product : timeDerivative (fun y => eta y * q y) z = 0 := by
      unfold timeDerivative
      rw [hproduct.fderiv_eq]
      simp
    rw [htime_product, hzero.self_of_nhds, htime_eta]
    ring

/-- The literal velocity-gradient product rule for a locally smooth scalar
and a compact cutoff. -/
private theorem velocityGradient_cutoff_mul
      (i : Fin d) :
    velocityGradient (fun y => eta y * q y) z i =
      eta z * velocityGradient q z i + q z * velocityGradient eta z i := by
  by_cases hz : z ∈ U
  · unfold velocityGradient
    change (fderiv Real (eta * q) z) (0, Pi.single i 1) = _
    rw [fderiv_mul (heta.differentiable (by norm_num) z)
      ((hq.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ·
    have hzero : eta =ᶠ[𝓝 z] fun _  => (0 ) :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hzeta => hz (hetaU hzeta))
    have hproduct : (fun y => eta y * q y) =ᶠ[𝓝 z] fun _  => (0 ) := by
      filter_upwards [hzero] with y hy
      simp [hy]

    have hgrad_eta : velocityGradient eta z i = 0 := by
      unfold velocityGradient
      rw [hzero.fderiv_eq]
      simp
    have hgrad_product : velocityGradient (fun y => eta y * q y) z i = 0 := by
      unfold velocityGradient
      rw [hproduct.fderiv_eq]
      simp
    rw [hgrad_product, hzero.self_of_nhds, hgrad_eta]
    ring

/-- The ordered velocity-Hessian product formula for a compact cutoff and a
locally `C²` scalar.  The middle terms have the project-wide `(i,j)`
orientation. -/
private theorem velocityHessian_cutoff_mul
      (i j : Fin d) :
    velocityHessian (fun y => eta y * q y) z i j =
      eta z * velocityHessian q z i j + velocityGradient eta z j * velocityGradient q z i +
        velocityGradient q z j * velocityGradient eta z i +
          q z * velocityHessian eta z i j := by
  let sharedTerm_d3f99a6f57 := (((0, Pi.single i 1) : TimeVelocity d))
  let sharedTerm_b40e6c72e5 := (((0, Pi.single j 1) : TimeVelocity d))
  let sharedTerm_4fcfd705fe := ((fderiv Real (eta * q)))
  let sharedTerm_8df86e1678 := ((fun y => eta y • fderiv Real q y + q y • fderiv Real eta y))

  by_cases hz : z ∈ U
  · have heta_at : ContDiffAt Real 2 eta z := heta.contDiffAt
    have hq_at  := hq.contDiffAt (hU.mem_nhds hz)
    have heta_diff : DifferentiableAt Real eta z := heta_at.differentiableAt (by norm_num)
    have hq_diff : DifferentiableAt Real q z := hq_at.differentiableAt (by norm_num)
    have heta_deriv_diff : DifferentiableAt Real (fderiv Real eta) z :=
      (heta_at.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hq_deriv_diff : DifferentiableAt Real (fderiv Real q) z :=
      (hq_at.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)




    have hq_symm := (hq_at.isSymmSndFDerivAt (by norm_num)).eq
      sharedTerm_b40e6c72e5 sharedTerm_d3f99a6f57
    have heta_symm := (heta_at.isSymmSndFDerivAt (by norm_num)).eq
      sharedTerm_b40e6c72e5 sharedTerm_d3f99a6f57
    have heval := congrArg (fun H : TimeVelocity d →L[Real]
        TimeVelocity d →L[Real] Real => H sharedTerm_b40e6c72e5
          sharedTerm_d3f99a6f57) (show fderiv Real sharedTerm_4fcfd705fe z =
        eta z • fderiv Real (fderiv Real q) z +
          (fderiv Real eta z).smulRight (fderiv Real q z) +
            q z • fderiv Real (fderiv Real eta) z +
              (fderiv Real q z).smulRight (fderiv Real eta z) by
              calc
                fderiv Real sharedTerm_4fcfd705fe z =
                    fderiv Real sharedTerm_8df86e1678 z := (show fderiv Real (eta * q) =ᶠ[𝓝 z]
                sharedTerm_8df86e1678 by
                        filter_upwards [(hq_at.eventually (by norm_num))] with y hy
                        rw [fderiv_mul (heta.differentiable (by norm_num) y)
                          (hy.differentiableAt (by norm_num))]).fderiv_eq
                _ = fderiv Real (fun y => eta y • fderiv Real q y) z +
                    fderiv Real (fun y => q y • fderiv Real eta y) z := (id (fderiv_add (DifferentiableAt.smul heta_diff hq_deriv_diff) (DifferentiableAt.smul hq_diff heta_deriv_diff)))
                _ = _ := by
                      change fderiv Real (eta • fderiv Real q) z +
                        fderiv Real (q • fderiv Real eta) z = _
                      rw [fderiv_smul heta_diff hq_deriv_diff,
                        fderiv_smul hq_diff heta_deriv_diff]
                      ac_rfl)
    calc
      velocityHessian (fun y => eta y * q y) z i j =
          velocityHessian (fun y => eta y * q y) z j i := (velocityHessian_isSymm (contDiff_cutoff_mul_of_tsupport_subset hU heta hetaU hq) z).apply j i
      _ = eta z * velocityHessian q z i j +
          velocityGradient eta z j * velocityGradient q z i +
            velocityGradient q z j * velocityGradient eta z i +
              q z * velocityHessian eta z i j := by
        change (fderiv Real sharedTerm_4fcfd705fe z)
            sharedTerm_b40e6c72e5 sharedTerm_d3f99a6f57 = _
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.smulRight_apply, smul_eq_mul] at heval
        have heval' :
            (fderiv Real sharedTerm_4fcfd705fe z)
                sharedTerm_b40e6c72e5 sharedTerm_d3f99a6f57 =
              eta z * (fderiv Real (fderiv Real q) z)
                  sharedTerm_d3f99a6f57 sharedTerm_b40e6c72e5 +
                (fderiv Real eta z) sharedTerm_b40e6c72e5 *
                    (fderiv Real q z) sharedTerm_d3f99a6f57 +
                  (fderiv Real q z) sharedTerm_b40e6c72e5 *
                    (fderiv Real eta z) sharedTerm_d3f99a6f57 +
                      q z * (fderiv Real (fderiv Real eta) z)
                        sharedTerm_d3f99a6f57
                        sharedTerm_b40e6c72e5 := by
          rw [heval, hq_symm, heta_symm]
          ring
        simpa only [velocityHessian, velocityGradient] using heval'
  ·
    have hzero : eta =ᶠ[𝓝 z] fun _  => (0 ) :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hzeta => hz (hetaU hzeta))
    have hproduct : (fun y => eta y * q y) =ᶠ[𝓝 z] fun _  => (0 ) := by
      filter_upwards [hzero] with y hy
      simp [hy]
    have heta_zero : eta z = 0 := hzero.self_of_nhds
    have hgrad_eta : velocityGradient eta z = 0 := by
      funext k
      unfold velocityGradient
      rw [hzero.fderiv_eq]
      simp
    have hhess_eta : velocityHessian eta z = 0 := by
      ext k l
      unfold velocityHessian
      rw [hzero.fderiv.fderiv_eq, fderiv_fun_const]
      simp
    have hhess_product : velocityHessian (fun y => eta y * q y) z = 0 := by
      ext k l
      unfold velocityHessian
      rw [hproduct.fderiv.fderiv_eq, fderiv_fun_const]
      simp
    simp_all
end


variable {eta : HypoellipticAleksandrov.Parabolic.ScalarField d}

private theorem timeDerivative_cutoff_continuous
    (heta : ContDiff Real 2 eta) : Continuous (timeDerivative eta) := (continuous_timeDerivative heta)
























variable {U : HypoellipticAleksandrov.Parabolic.Region d} {p : ENNReal} {a f : HypoellipticAleksandrov.Parabolic.ScalarField d}

/-- A bounded cutoff supported in `U` multiplies a locally finite `Lᵖ`
function with the corresponding restricted-norm bound. -/
private theorem eLpNorm_cutoff_mul_le

    (haf : AEStronglyMeasurable (fun z => a z * f z) volume)
    (hU : MeasurableSet U) (haU : tsupport a ⊆ U)
    {B : Real} (hB : ∀ z, ‖a z‖ ≤ B) :
    eLpNorm (fun z => a z * f z) p volume ≤
      ENNReal.ofReal B * eLpNorm f p (volume.restrict U) := by
  have hzero : ∀ z ∉ U, a z = 0 := by
    intro z hz

    exact (notMem_tsupport_iff_eventuallyEq.mp (fun hza => hz (haU hza))).self_of_nhds
  have hproduct : (fun z => a z * f z) = fun z => a z * U.indicator f z := by
    funext z
    by_cases hz : z ∈ U
    · simp [hz]
    · simp [hz, hzero z hz]
  rw [hproduct]
  calc
    eLpNorm (fun z => a z * U.indicator f z) p volume ≤
        ENNReal.ofReal B * eLpNorm (U.indicator f) p volume := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hproduct ▸ haf) _ p
      filter_upwards [] with z
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB z) (norm_nonneg _)
    _ = ENNReal.ofReal B * eLpNorm f p (volume.restrict U) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hU]

private theorem memLp_cutoff_mul
      (hU : MeasurableSet U) (ha : Continuous a)
    (haCompact : HasCompactSupport a) (haU : tsupport a ⊆ U)
    (hf : MemLp f p (volume.restrict U)) :
    MemLp (fun z => a z * f z) p volume := by
  have hzero : ∀ z ∉ U, a z = 0 := by
    intro z hz
    have hnot : z ∉ tsupport a := fun hza => hz (haU hza)
    exact (notMem_tsupport_iff_eventuallyEq.mp hnot).self_of_nhds
  have hproduct : (fun z => a z * f z) = fun z => a z * U.indicator f z := by
    funext z
    by_cases hz : z ∈ U
    · simp [hz]
    · simp [hz, hzero z hz]
  rw [hproduct]
  have ha_top : MemLp a ∞ volume := ha.memLp_of_hasCompactSupport haCompact
  have hf_indicator : MemLp (U.indicator f) p volume :=
    (memLp_indicator_iff_restrict hU).mpr hf
  simpa only [mul_comm] using hf_indicator.mul' ha_top

/-- The fixed normalized collar admits the smooth compact cutoff required for
the later quantitative product estimate. -/
private theorem exists_reference_collar_cutoff (d : Nat) :
    ∃ eta : HypoellipticAleksandrov.Parabolic.ScalarField d,
      ContDiff Real PDE.smoothOrder eta ∧ HasCompactSupport eta ∧
        (∀ᶠ z in 𝓝ˢ
          (parabolicClosedBox (d := d) 1 (1 / 2 : Real) (1 / 4 : Real) 0), eta z = 1) ∧
          tsupport eta ⊆ parabolicBox  1 1 0 0 := by


  obtain ⟨eta, heta, heta_one, hetaU⟩ := exists_smooth_cutoff_tsupport_subset
    (isCompact_parabolicClosedBox 1 (1 / 2 : Real) (1 / 4 : Real) 0)
    (isOpen_parabolicBox 1 1 0 0) (reference_closed_collar_subset_unit_box d)
  refine ⟨eta, heta, ?_, heta_one, hetaU⟩
  exact hasCompactSupport_of_tsupport_subset_of_isCompact_closure hetaU
    (isCompact_closure_reference_unit_box d)

private theorem cutoff_uniform_bound {d : Nat} {a : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (ha : Continuous a) (haCompact : HasCompactSupport a) :
    ∃ B : Real, 0 ≤ B ∧ ∀ z, ‖a z‖ ≤ B := by
  obtain ⟨B, hB⟩ := ha.bounded_above_of_compact_support haCompact
  refine ⟨max 0 B, le_max_left _ _, fun z => (hB z).trans (le_max_right _ _)⟩




private theorem eLpNorm_cutoff_mul_le_of_bound_le
    {d : Nat} {U : HypoellipticAleksandrov.Parabolic.Region d} {p : ENNReal}
    {a f : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (haf : AEStronglyMeasurable (fun z => a z * f z) volume)
    (hU : MeasurableSet U) (haU : tsupport a ⊆ U)
    {B M : Real} (hB : ∀ z, ‖a z‖ ≤ B) (hBM : B ≤ M) :
    eLpNorm (fun z => a z * f z) p volume ≤
      ENNReal.ofReal M * eLpNorm f p (volume.restrict U) := (Trans.trans (eLpNorm_cutoff_mul_le haf hU haU hB)
  (mul_le_mul' (ENNReal.ofReal_le_ofReal hBM) (le_refl (eLpNorm f p (volume.restrict U)))))

/-- The normalized reference collar cutoff has a selected-jet product bound
against the literal unit source box. -/
theorem exists_parabolicMorreyReferenceCollarCutoffJetConst (d : Nat) :
    ∃ eta : HypoellipticAleksandrov.Parabolic.ScalarField d, ∃ C : Real, 0 < C ∧
      ContDiff Real PDE.smoothOrder eta ∧ HasCompactSupport eta ∧
      (∀ᶠ z in 𝓝ˢ
        (parabolicClosedBox 1 (1 / 2 : Real) (1 / 4 : Real) 0), eta z = 1) ∧
      tsupport eta ⊆ parabolicBox 1 1 0 0 ∧
      ∀ q : HypoellipticAleksandrov.Parabolic.ScalarField d,
        ContDiffOn Real 2 q (parabolicBox 1 1 0 0) ->
        ParabolicMemLpOn (parabolicBox 1 1 0 0) (parabolicExponent d) q ->
        ParabolicMemLpOn (parabolicBox 1 1 0 0) (parabolicExponent d)
          (timeDerivative q) ->
        (∀ i : Fin d, ParabolicMemLpOn (parabolicBox 1 1 0 0)
          (parabolicExponent d) (fun z => velocityGradient q z i)) ->
        (∀ i j : Fin d, ParabolicMemLpOn (parabolicBox 1 1 0 0)
          (parabolicExponent d) (fun z => velocityHessian q z i j)) ->
        parabolicSmoothJetLpNorm d (fun z => eta z * q z) <=
          C * (parabolicLpNormOn d q (parabolicBox 1 1 0 0) +
               parabolicLpNormOn d (timeDerivative q) (parabolicBox 1 1 0 0) +
               ∑ i : Fin d, parabolicLpNormOn d
                 (fun z => velocityGradient q z i) (parabolicBox 1 1 0 0) +
               ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
                 (fun z => velocityHessian q z i j) (parabolicBox 1 1 0 0)) := by
  let U : HypoellipticAleksandrov.Parabolic.Region d := parabolicBox 1 1 0 0
  obtain ⟨eta, heta, hetaCompact, heta_one, hetaU⟩ := exists_reference_collar_cutoff d
  have heta₂ : ContDiff Real 2 eta := heta.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨B₀, hB₀nonneg, hB₀⟩ := cutoff_uniform_bound heta.continuous hetaCompact
  obtain ⟨Bt, hBtnonneg, hBt⟩ := cutoff_uniform_bound
    (timeDerivative_cutoff_continuous heta₂)
    (_root_.HypoellipticAleksandrov.Parabolic.timeDerivative_compact hetaCompact)
  choose Bg hBgnonneg hBg using fun i : Fin d => cutoff_uniform_bound
    (_root_.HypoellipticAleksandrov.Parabolic.velocityGradient_continuous heta₂)
    (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport hetaCompact)
  choose Bh hBhnonneg hBh using fun i : Fin d => fun j : Fin d => cutoff_uniform_bound
    (_root_.HypoellipticAleksandrov.Parabolic.velocityHessian_continuous heta₂)
    (_root_.HypoellipticAleksandrov.Parabolic.velocityHessian_compact hetaCompact)
  let M : Real := 1 + B₀ + Bt + ∑ i : Fin d, Bg i + ∑ i : Fin d, ∑ j : Fin d, Bh i j
  have hBgSum : 0 ≤ ∑ i : Fin d, Bg i :=
    Finset.sum_nonneg fun i _ => hBgnonneg i
  have hBhSum : 0 ≤ ∑ i : Fin d, ∑ j : Fin d, Bh i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hBhnonneg i j

  have hB₀M : B₀ ≤ M := by
    dsimp [M]

    linarith

  have hBgM (i : Fin d) : Bg i ≤ M := by
    dsimp [M]
    have hsum : Bg i ≤ ∑ j : Fin d, Bg j := Finset.single_le_sum
      (fun j _ => hBgnonneg j) (Finset.mem_univ i)

    linarith
  have hBhM (i j : Fin d) : Bh i j ≤ M := by
    dsimp [M]
    have hinner : Bh i j ≤ ∑ k : Fin d, Bh i k := Finset.single_le_sum
      (fun k _ => hBhnonneg i k) (Finset.mem_univ j)
    have houter : (∑ k : Fin d, Bh i k) ≤ ∑ l : Fin d, ∑ k : Fin d, Bh l k :=
      Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun k _ => hBhnonneg l k)
        (Finset.mem_univ i)

    linarith
  let N : Nat := 3 + d * 2 + d ^ 2 * 4
  let C : Real := (N : Real) * M
  have hCpos : 0 < C := by
    dsimp [C, N]
    positivity
  refine ⟨eta, C, hCpos, heta, hetaCompact, heta_one, hetaU, ?_⟩
  intro q hq hqMem hqtMem hqgMem hqhMem
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_parabolicBox 1 1 0 0
  have hUmeas  := hUopen.measurableSet
  have hp  := _root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.parabolicExponent_one_le d
  have hetaU' : tsupport eta ⊆ U := by exact hetaU
  have htimeU : tsupport (timeDerivative eta) ⊆ U :=
    (_root_.HypoellipticAleksandrov.Parabolic.timeDerivative_tsupport eta).trans hetaU'
  have hgradU (i : Fin d) : tsupport (fun z => velocityGradient eta z i) ⊆ U :=
    (_root_.HypoellipticAleksandrov.Parabolic.velocityGradient_tsupport eta).trans hetaU'
  have hhessU (i j : Fin d) : tsupport (fun z => velocityHessian eta z i j) ⊆ U :=
    (_root_.HypoellipticAleksandrov.Parabolic.velocityHessian_tsupport eta).trans hetaU'


  have htimeRightMem : MemLp (fun z => q z * timeDerivative eta z)
      (parabolicExponent d) volume := by
    simpa only [mul_comm] using memLp_cutoff_mul hUmeas
      (timeDerivative_cutoff_continuous heta₂)
      (_root_.HypoellipticAleksandrov.Parabolic.timeDerivative_compact hetaCompact) htimeU hqMem

  have hgradLeftMem (i : Fin d)  :=
    memLp_cutoff_mul hUmeas heta.continuous hetaCompact hetaU' (hqgMem i)
  have hgradRightMem (i : Fin d) : MemLp (fun z => q z * velocityGradient eta z i)
      (parabolicExponent d) volume := by
    simpa only [mul_comm] using memLp_cutoff_mul hUmeas
      (_root_.HypoellipticAleksandrov.Parabolic.velocityGradient_continuous heta₂)
      (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport hetaCompact) (hgradU i) hqMem

  have hhessOneMem (i j : Fin d)  :=
    memLp_cutoff_mul hUmeas heta.continuous hetaCompact hetaU' (hqhMem i j)
  have hhessTwoMem (i j : Fin d)  :=
    memLp_cutoff_mul hUmeas (_root_.HypoellipticAleksandrov.Parabolic.velocityGradient_continuous heta₂)
      (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport hetaCompact) (hgradU j) (hqgMem i)
  have hhessThreeMem (i j : Fin d) : MemLp (fun z =>
      velocityGradient q z j * velocityGradient eta z i) (parabolicExponent d) volume := by
    simpa only [mul_comm] using memLp_cutoff_mul hUmeas
      (_root_.HypoellipticAleksandrov.Parabolic.velocityGradient_continuous heta₂)
      (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport hetaCompact) (hgradU i) (hqgMem j)
  have hhessFourMem (i j : Fin d) : MemLp (fun z => q z * velocityHessian eta z i j)
      (parabolicExponent d) volume := by
    simpa only [mul_comm] using memLp_cutoff_mul hUmeas
      (_root_.HypoellipticAleksandrov.Parabolic.velocityHessian_continuous heta₂)
      (_root_.HypoellipticAleksandrov.Parabolic.velocityHessian_compact hetaCompact) (hhessU i j) hqMem


  let m  := ENNReal.ofReal M
  let Q  := eLpNorm q (parabolicExponent d) (volume.restrict U)
  let T  := eLpNorm (timeDerivative q) (parabolicExponent d) (volume.restrict U)
  let G  := fun i =>
    eLpNorm (fun z => velocityGradient q z i) (parabolicExponent d) (volume.restrict U)
  let H  := fun i j =>
    eLpNorm (fun z => velocityHessian q z i j) (parabolicExponent d) (volume.restrict U)
  let R  := Q + T + ∑ i : Fin d, G i + ∑ i : Fin d, ∑ j : Fin d, H i j
  have hQR : Q ≤ R := by
    dsimp [R]
    exact le_self_add.trans (le_self_add.trans le_self_add)

  have hGR (i : Fin d) : G i ≤ R := by
    dsimp [R]
    exact le_trans (Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i))
      ((le_add_of_nonneg_left (by positivity : 0 ≤ Q + T)).trans le_self_add)
  have hHR (i j : Fin d) : H i j ≤ R := by
    dsimp [R]
    calc
      H i j ≤ ∑ k : Fin d, H i k := Finset.single_le_sum (fun k _ => bot_le) (Finset.mem_univ j)
      _ ≤ ∑ l : Fin d, ∑ k : Fin d, H l k :=
        Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun k _ => bot_le) (Finset.mem_univ i)
      _ ≤ R := le_add_of_nonneg_left (by positivity : 0 ≤ Q + T + ∑ i : Fin d, G i)



  have hgradLeftE (i : Fin d) : eLpNorm (fun z => eta z * velocityGradient q z i)
      (parabolicExponent d) volume ≤ m * G i := by
    simpa only [m, G] using eLpNorm_cutoff_mul_le_of_bound_le
      ((hgradLeftMem i).aestronglyMeasurable) hUmeas hetaU' hB₀ hB₀M
  have hgradRightE (i : Fin d) : eLpNorm (fun z => q z * velocityGradient eta z i)
      (parabolicExponent d) volume ≤ m * Q := by
    simpa only [m, Q, mul_comm] using eLpNorm_cutoff_mul_le_of_bound_le
      (by simpa only [mul_comm] using (hgradRightMem i).aestronglyMeasurable) hUmeas (hgradU i)
      (hBg i) (hBgM i)
  have hhessOneE (i j : Fin d) : eLpNorm (fun z => eta z * velocityHessian q z i j)
      (parabolicExponent d) volume ≤ m * H i j := by
    simpa only [m, H] using eLpNorm_cutoff_mul_le_of_bound_le
      ((hhessOneMem i j).aestronglyMeasurable) hUmeas hetaU' hB₀ hB₀M
  have hhessTwoE (i j : Fin d) : eLpNorm (fun z =>
      velocityGradient eta z j * velocityGradient q z i)
      (parabolicExponent d) volume ≤ m * G i := by
    simpa only [m, G] using eLpNorm_cutoff_mul_le_of_bound_le
      ((hhessTwoMem i j).aestronglyMeasurable)
      hUmeas (hgradU j) (hBg j) (hBgM j)
  have hhessThreeE (i j : Fin d) : eLpNorm (fun z =>
      velocityGradient q z j * velocityGradient eta z i)
      (parabolicExponent d) volume ≤ m * G j := by
    have hraw := eLpNorm_cutoff_mul_le_of_bound_le (d := d) (U := U)
      (p := parabolicExponent d)
      (a := fun z => velocityGradient eta z i)
      (f := fun z => velocityGradient q z j)
      (by simpa only [mul_comm] using (hhessThreeMem i j).aestronglyMeasurable)
      hUmeas (hgradU i) (hBg i) (hBgM i)
    simpa only [m, G, mul_comm] using hraw
  have hhessFourE (i j : Fin d) : eLpNorm (fun z => q z * velocityHessian eta z i j)
      (parabolicExponent d) volume ≤ m * Q := by
    simpa only [m, Q, mul_comm] using eLpNorm_cutoff_mul_le_of_bound_le
      (by simpa only [mul_comm] using (hhessFourMem i j).aestronglyMeasurable) hUmeas (hhessU i j)
      (hBh i j) (hBhM i j)


  have hgradR (i : Fin d) : eLpNorm (fun z => velocityGradient (fun y => eta y * q y) z i)
      (parabolicExponent d) volume ≤ 2 * (m * R) := by
    rw [show (fun z => velocityGradient (fun y => eta y * q y) z i) = fun z =>
        eta z * velocityGradient q z i + q z * velocityGradient eta z i by
      funext z
      exact velocityGradient_cutoff_mul hUopen heta₂ hetaU' hq z i]
    calc
      eLpNorm (fun z => eta z * velocityGradient q z i + q z * velocityGradient eta z i)
          (parabolicExponent d) volume ≤
          eLpNorm (fun z => eta z * velocityGradient q z i) (parabolicExponent d) volume +
            eLpNorm (fun z => q z * velocityGradient eta z i) (parabolicExponent d) volume :=
        eLpNorm_add_le hp
      _ ≤ m * R + m * R := add_le_add
        ((hgradLeftE i).trans (mul_le_mul_right (hGR i) m))
        ((hgradRightE i).trans (mul_le_mul_right hQR m))
      _ = 2 * (m * R) := by ring
  have hhessR (i j : Fin d) : eLpNorm (fun z => velocityHessian (fun y => eta y * q y) z i j)
      (parabolicExponent d) volume ≤ 4 * (m * R) := by
    rw [show (fun z => velocityHessian (fun y => eta y * q y) z i j) = fun z =>
        eta z * velocityHessian q z i j +
          velocityGradient eta z j * velocityGradient q z i +
            velocityGradient q z j * velocityGradient eta z i +
              q z * velocityHessian eta z i j by
      funext z
      exact velocityHessian_cutoff_mul hUopen heta₂ hetaU' hq z i j]
    rw [show (fun z =>
        eta z * velocityHessian q z i j +
          velocityGradient eta z j * velocityGradient q z i +
            velocityGradient q z j * velocityGradient eta z i +
              q z * velocityHessian eta z i j) =
        ((fun z => eta z * velocityHessian q z i j) +
          (fun z => velocityGradient eta z j * velocityGradient q z i) +
            (fun z => velocityGradient q z j * velocityGradient eta z i)) +
          fun z => q z * velocityHessian eta z i j by
      funext z
      rfl]
    calc
      eLpNorm (fun z => eta z * velocityHessian q z i j +
          velocityGradient eta z j * velocityGradient q z i +
            velocityGradient q z j * velocityGradient eta z i +
              q z * velocityHessian eta z i j) (parabolicExponent d) volume ≤
          (eLpNorm (fun z => eta z * velocityHessian q z i j) (parabolicExponent d) volume +
            eLpNorm (fun z => velocityGradient eta z j * velocityGradient q z i)
              (parabolicExponent d) volume +
              eLpNorm (fun z => velocityGradient q z j * velocityGradient eta z i)
                (parabolicExponent d) volume) +
            eLpNorm (fun z => q z * velocityHessian eta z i j) (parabolicExponent d) volume := (Trans.trans (eLpNorm_add_le hp)
  (add_le_add_left
    (Eq.mpr
      (id
        (congrArg
          (fun _a =>
            eLpNorm _a (parabolicExponent d) volume ≤
              eLpNorm (fun z => eta z * velocityHessian q z i j) (parabolicExponent d) volume +
                  eLpNorm (fun z => velocityGradient eta z j * velocityGradient q z i) (parabolicExponent d) volume +
                eLpNorm (fun z => velocityGradient q z j * velocityGradient eta z i) (parabolicExponent d) volume)
          (funext fun z =>
            Eq.refl
              (eta z * velocityHessian q z i j + velocityGradient eta z j * velocityGradient q z i +
                velocityGradient q z j * velocityGradient eta z i))))
      (LE.le.trans (eLpNorm_add_le hp)
        (add_le_add_left (eLpNorm_add_le hp)
          (eLpNorm (fun z => velocityGradient q z j * velocityGradient eta z i) (parabolicExponent d) volume))))
    (eLpNorm (fun z => q z * velocityHessian eta z i j) (parabolicExponent d) volume)))
      _ ≤ (m * R + m * R + m * R) + m * R := by
        gcongr
        · exact (hhessOneE i j).trans (mul_le_mul_right (hHR i j) m)
        · exact (hhessTwoE i j).trans (mul_le_mul_right (hGR i) m)
        · exact (hhessThreeE i j).trans (mul_le_mul_right (hGR j) m)
        · exact (hhessFourE i j).trans (mul_le_mul_right hQR m)
      _ = 4 * (m * R) := by ring
  have hENN : parabolicSmoothJetELpNorm d (fun z => eta z * q z) ≤ ENNReal.ofReal C * R := by
    unfold parabolicSmoothJetELpNorm parabolicELpNorm
    calc
      eLpNorm (fun z => eta z * q z) (parabolicExponent d) volume +
          eLpNorm (timeDerivative (fun z => eta z * q z)) (parabolicExponent d) volume +
          ∑ i : Fin d, eLpNorm (fun z => velocityGradient (fun y => eta y * q y) z i)
            (parabolicExponent d) volume +
          ∑ i : Fin d, ∑ j : Fin d, eLpNorm
            (fun z => velocityHessian (fun y => eta y * q y) z i j) (parabolicExponent d) volume ≤
          m * R + 2 * (m * R) + ∑ _i : Fin d, 2 * (m * R) +
            ∑ _i : Fin d, ∑ _j : Fin d, 4 * (m * R) := add_le_add
          (add_le_add
            (add_le_add ((show eLpNorm (fun z => eta z * q z) (parabolicExponent d) volume ≤ m * Q by
                simpa only [m, Q] using eLpNorm_cutoff_mul_le_of_bound_le
                  ((MemLp.aestronglyMeasurable (memLp_cutoff_mul hUmeas heta.continuous hetaCompact hetaU' hqMem))) hUmeas hetaU' hB₀ hB₀M).trans (mul_le_mul_right hQR m)) (by
                rw [show timeDerivative (fun z => eta z * q z) = fun z =>
                    eta z * timeDerivative q z + q z * timeDerivative eta z by
                  funext z
                  exact timeDerivative_cutoff_mul hUopen heta₂ hetaU' hq z]
                calc
                  eLpNorm (fun z => eta z * timeDerivative q z + q z * timeDerivative eta z)
                      (parabolicExponent d) volume ≤
                      eLpNorm (fun z => eta z * timeDerivative q z) (parabolicExponent d) volume +
                        eLpNorm (fun z => q z * timeDerivative eta z) (parabolicExponent d) volume :=
                    eLpNorm_add_le hp
                  _ ≤ m * R + m * R := add_le_add
                    ((show eLpNorm (fun z => eta z * timeDerivative q z)
      (parabolicExponent d) volume ≤ m * T by
                        simpa only [m, T] using eLpNorm_cutoff_mul_le_of_bound_le
                          ((MemLp.aestronglyMeasurable (memLp_cutoff_mul hUmeas heta.continuous hetaCompact hetaU' hqtMem))) hUmeas hetaU' hB₀ hB₀M).trans (mul_le_mul_right (by
                        dsimp [R]
                        exact (le_add_of_nonneg_left (zero_le : 0 ≤ Q)).trans
                          (le_self_add.trans le_self_add)) m))
                    ((show eLpNorm (fun z => q z * timeDerivative eta z)
      (parabolicExponent d) volume ≤ m * Q by
                        simpa only [m, Q, mul_comm] using eLpNorm_cutoff_mul_le_of_bound_le
                          (by simpa only [mul_comm] using (htimeRightMem).aestronglyMeasurable) hUmeas htimeU hBt (by
                              dsimp [M]

                              linarith)).trans (mul_le_mul_right hQR m))
                  _ = 2 * (m * R) := by ring))
            (Finset.sum_le_sum fun i _ => hgradR i))
          (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hhessR i j)
      _ = (N : ENNReal) * (m * R) := by
        dsimp [N]
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
        ring
      _ = ENNReal.ofReal C * R := by
        dsimp [C, m]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        simp only [ENNReal.ofReal_natCast]
        ring
  have hQtop : Q ≠ ⊤ := by exact hqMem.eLpNorm_ne_top
  have hTtop : T ≠ ⊤ := by exact hqtMem.eLpNorm_ne_top
  have hGtop (i : Fin d) : G i ≠ ⊤ := by exact (hqgMem i).eLpNorm_ne_top
  have hHtop (i j : Fin d) : H i j ≠ ⊤ := by exact (hqhMem i j).eLpNorm_ne_top


  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      dsimp [R]
      apply ENNReal.add_ne_top.mpr
      constructor
      · apply ENNReal.add_ne_top.mpr
        constructor
        · exact ENNReal.add_ne_top.mpr ⟨hQtop, hTtop⟩
        · exact ENNReal.sum_ne_top.mpr fun i _ => hGtop i
      · exact ENNReal.sum_ne_top.mpr fun i _ => ENNReal.sum_ne_top.mpr fun j _ => hHtop i j)) hENN
  have hRreal : R.toReal =
      parabolicLpNormOn d q (parabolicBox 1 1 0 0) +
        parabolicLpNormOn d (timeDerivative q) (parabolicBox 1 1 0 0) +
        ∑ i : Fin d, parabolicLpNormOn d (fun z => velocityGradient q z i)
          (parabolicBox 1 1 0 0) +
        ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
          (fun z => velocityHessian q z i j) (parabolicBox 1 1 0 0) := by
    dsimp [R, Q, T, G, H, U, parabolicLpNormOn, parabolicELpNormOn]
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hQtop, hTtop⟩, ENNReal.sum_ne_top.mpr fun i _ => hGtop i⟩)
      (ENNReal.sum_ne_top.mpr fun i _ => ENNReal.sum_ne_top.mpr fun j _ => hHtop i j)]
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hQtop, hTtop⟩)
      (ENNReal.sum_ne_top.mpr fun i _ => hGtop i)]
    rw [ENNReal.toReal_add hQtop hTtop]
    rw [ENNReal.toReal_sum fun i _ => hGtop i]
    rw [ENNReal.toReal_sum fun i _ => ENNReal.sum_ne_top.mpr fun j _ => hHtop i j]
    simp_rw [ENNReal.toReal_sum fun j _ => hHtop _ j]
    rfl
  simpa only [parabolicSmoothJetLpNorm, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hCpos.le, hRreal] using hreal

end HypoellipticAleksandrov.Parabolic
