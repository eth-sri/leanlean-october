module

import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.MetricSpace.ProperSpace
public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set
open scoped MatrixOrder Topology


/-- Maximum principle on a compact region, strict version. -/
theorem le_zero_of_strict_viscous_compact {n : ℕ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} {ε : ℝ} {K D : Set (KineticPoint n)}
    {w : KineticPoint n → ℝ} (hε : 0 ≤ ε) (hKc : IsCompact K)
    (hwc : ContinuousOn w K)
    (hfut : ∀ p ∈ D, ∀ᶠ q in 𝓝 p, p.time ≤ q.time → q ∈ K)
    (hreg : ∀ p ∈ D, IsSliceRegularAt w p)
    (hB : ∀ p ∈ D, (B p.time p.position p.velocity).PosSemidef)
    (hpos : ∀ p ∈ D, 0 < viscousTransportedOperator B b ε w p)
    (hbdry : ∀ p ∈ K, p ∉ D → w p ≤ 0) :
    ∀ p ∈ K, w p ≤ 0 := by
  intro p₀ hp₀
  by_contra hneg'
  obtain ⟨p, hpK, hpmax⟩ := hKc.exists_isMaxOn ⟨p₀, hp₀⟩ hwc
  have hwp := lt_of_lt_of_le (not_le.mp hneg') (hpmax hp₀)
  have hpD : p ∈ D := by
    by_contra h
    exact absurd (hbdry p hpK h) (not_le.mpr hwp)
  have hmax : ∀ᶠ q in 𝓝 p, p.time ≤ q.time → w q ≤ w p := by
    filter_upwards [hfut p hpD] with q hq hqt using hpmax (hq hqt)
  exact absurd
    (viscousTransportedOperator_nonpos_of_future_localMax hε (hreg p hpD) hmax (hB p hpD))
    (not_le.mpr (hpos p hpD))

/-- The time coordinate has `L_ε (σ - T) = 1`. -/
theorem viscousTransportedOperator_time_sub {n : ℕ} (B : FullKineticCoefficient n)
    (b : PDE.Vec n → PDE.Vec n) (ε T : ℝ) (p : KineticPoint n) :
    viscousTransportedOperator B b ε (fun q => q.time - T) p = 1 := by
  have hh : ∀ x : PDE.Vec n, sliceHessian (fun _ => p.time - T) x = 0 := by
    intro x
    have hz : (fun y => PDE.classicalGradient (fun _ : PDE.Vec n => p.time - T) y) =
        fun _ => 0 := by
      funext y
      ext i
      simp [PDE.classicalGradient]
    ext i j
    simp only [sliceHessian, hz]
    simp
  have hg : kineticVelocityGradient (fun q => q.time - T) p = 0 := by
    ext i
    simp [kineticVelocityGradient, PDE.classicalGradient]
  rw [viscousTransportedOperator_apply, transportedForwardOperator_apply]
  have h1 : kineticTimeDerivative (fun q => q.time - T) p = 1 := by
    unfold kineticTimeDerivative
    simp
  have h2 : diffusedHessian (fun q => q.time - T) p = 0 := by
    rw [diffusedHessian_eq_sliceHessian]
    exact hh _
  have h3 : kineticVelocityHessian (fun q => q.time - T) p = 0 := by
    rw [kineticVelocityHessian_eq_sliceHessian]
    exact hh _
  rw [h1, h2, h3, hg]
  simp [PDE.vecDot]

/-- The time coordinate `σ - T` is slice regular everywhere. -/
theorem isSliceRegularAt_time_sub {n : ℕ} (T : ℝ) (p : KineticPoint n) :
    IsSliceRegularAt (fun q : KineticPoint n => q.time - T) p :=
  ⟨differentiableAt_id.sub_const T,
    (show ContDiffAt ℝ 2 (fun _ => p.time - T) p.position from contDiffAt_const),
    (show ContDiffAt ℝ 2 (fun _ => p.time - T) p.velocity from contDiffAt_const)⟩

/-- Maximum principle on a compact region for a subsolution `L_ε w ≥ 0`. -/
theorem le_zero_of_viscous_nonneg_compact {n : ℕ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} {ε : ℝ} {K D : Set (KineticPoint n)}
    {w : KineticPoint n → ℝ} {T : ℝ} (hε : 0 ≤ ε) (hKc : IsCompact K)
    (hKT : ∀ p ∈ K, p.time ≤ T) (hwc : ContinuousOn w K)
    (hfut : ∀ p ∈ D, ∀ᶠ q in 𝓝 p, p.time ≤ q.time → q ∈ K)
    (hreg : ∀ p ∈ D, IsSliceRegularAt w p)
    (hB : ∀ p ∈ D, (B p.time p.position p.velocity).PosSemidef)
    (hsub : ∀ p ∈ D, 0 ≤ viscousTransportedOperator B b ε w p)
    (hbdry : ∀ p ∈ K, p ∉ D → w p ≤ 0) :
    ∀ p ∈ K, w p ≤ 0 := by
  have hcontT : Continuous (fun q : KineticPoint n => q.time - T) :=
    continuous_time.sub continuous_const
  have hregT := isSliceRegularAt_time_sub (n := n) T
  have key : ∀ δ : ℝ, 0 < δ → ∀ p ∈ K, w p + δ * (p.time - T) ≤ 0 := by
    intro δ hδ
    refine le_zero_of_strict_viscous_compact (b := b) (ε := ε)
      (w := fun q => w q + δ * (q.time - T)) hε hKc ?_ hfut ?_ hB ?_ ?_
    · exact hwc.add ((continuous_const.mul hcontT).continuousOn)
    · intro p hp
      exact (hreg p hp).add ((hregT p).const_mul δ)
    · intro p hp
      rw [viscousTransportedOperator_add (hreg p hp) ((hregT p).const_mul δ),
        viscousTransportedOperator_const_mul δ (hregT p),
        viscousTransportedOperator_time_sub]
      have := hsub p hp
      linarith
    · intro p hp hpD
      have h1 := hbdry p hp hpD
      have h2 :=
        mul_nonpos_of_nonneg_of_nonpos hδ.le (sub_nonpos.mpr (hKT p hp))
      linarith
  intro p hp
  by_contra hneg'
  have hneg := not_le.mp hneg'
  have hTp := sub_nonneg.mpr (hKT p hp)
  have hδ : 0 < w p / (2 * (T - p.time + 1)) := by positivity
  have := key _ hδ p hp
  have hden : 0 < 2 * (T - p.time + 1) := by positivity
  have hmul : w p / (2 * (T - p.time + 1)) * (p.time - T) =
      -(w p * (T - p.time) / (2 * (T - p.time + 1))) := by
    field_simp
    ring
  rw [hmul] at this
  have hfrac : w p * (T - p.time) / (2 * (T - p.time + 1)) < w p := by
    rw [div_lt_iff₀ hden]
    nlinarith
  linarith



/-- The squared Euclidean size `|y|² + |z|²` of the spatial coordinates of a kinetic
point. -/
def radialSq {n : ℕ} (p : KineticPoint n) : ℝ :=
  PDE.vecNormSq p.position + PDE.vecNormSq p.velocity

/-- The closed moving slab `{a ≤ σ ≤ b, y ∈ closure (γ(σ) + Ω)}` (all `z`). -/
def movingClosedSlab {n : ℕ} (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n) (a b : ℝ) :
    Set (KineticPoint n) :=
  {p | a ≤ p.time ∧ p.time ≤ b ∧ p.position ∈ closure (movingDomain Ω γ p.time)}

/-- The active part `{a ≤ σ < b, y ∈ γ(σ) + Ω}` of the moving slab. -/
def movingActiveSlab {n : ℕ} (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n) (a b : ℝ) :
    Set (KineticPoint n) :=
  {p | a ≤ p.time ∧ p.time < b ∧ p.position ∈ movingDomain Ω γ p.time}

/-- A point of the closed moving cylinder lies in `movingClosedSlab` exactly when its
position is in the closure of the moving domain. -/
theorem mem_closure_movingDomain_iff {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {σ : ℝ} {y : PDE.Vec n} :
    y ∈ closure (movingDomain Ω γ σ) ↔ y - γ σ ∈ closure Ω := by
  have h : movingDomain Ω γ σ = (Homeomorph.subRight (γ σ)) ⁻¹' Ω := by
    rw [movingDomain, ← PDE.preimage_subRight_eq_translateSet]
    rfl
  rw [h, ← Homeomorph.preimage_closure]
  rfl

/-- Membership in the moving domain. -/
theorem mem_movingDomain_iff {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {σ : ℝ} {y : PDE.Vec n} : y ∈ movingDomain Ω γ σ ↔ y - γ σ ∈ Ω :=
  PDE.mem_translateSet_iff_sub_mem

/-- The set of kinetic points whose position lies in the moving domain is open. -/
theorem isOpen_setOf_mem_movingDomain {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) :
    IsOpen {p : KineticPoint n | p.position ∈ movingDomain Ω γ p.time} := by
  have := hΩ.preimage (continuous_position.sub (hγ.comp continuous_time))
  convert this using 1
  ext p
  exact mem_movingDomain_iff

/-- The set of kinetic points whose position lies in the closure of the moving domain
is closed. -/
theorem isClosed_setOf_mem_closure_movingDomain {n : ℕ} {Ω : Set (PDE.Vec n)}
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) :
    IsClosed {p : KineticPoint n | p.position ∈ closure (movingDomain Ω γ p.time)} := by
  have := (isClosed_closure (s := Ω)).preimage (continuous_position.sub (hγ.comp continuous_time))
  convert this using 1
  ext p
  exact mem_closure_movingDomain_iff

/-- Continuity of `|y|² + |z|²`. -/
theorem continuous_radialSq {n : ℕ} : Continuous (@radialSq n) := by
  unfold radialSq PDE.vecNormSq PDE.vecDot
  have h1 : Continuous (@KineticPoint.position n) := continuous_position
  have h2 : Continuous (@KineticPoint.velocity n) := continuous_velocity
  fun_prop

/-- A closed set of kinetic points with bounded times has compact bounded truncations. -/
theorem isCompact_inter_radialSq {n : ℕ} {K : Set (KineticPoint n)} (hK : IsClosed K)
    {a b : ℝ} (hKt : ∀ p ∈ K, a ≤ p.time ∧ p.time ≤ b) (R : ℝ) :
    IsCompact (K ∩ {p | radialSq p ≤ R ^ 2}) := by
  let Kbig :=
    KineticPoint.homeomorphProd n ⁻¹'
      (Icc a b ×ˢ (Metric.closedBall 0 |R| ×ˢ Metric.closedBall 0 |R|))
  have hKbig : IsCompact Kbig :=
    (KineticPoint.homeomorphProd n).isCompact_preimage.mpr
      (isCompact_Icc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)))
  have hclosed : IsClosed (K ∩ {p | radialSq p ≤ R ^ 2}) :=
    hK.inter (isClosed_le continuous_radialSq continuous_const)
  refine hKbig.of_isClosed_subset hclosed ?_
  intro p hp
  obtain ⟨hpK, hr⟩ := hp
  obtain ⟨hat, htb⟩ := hKt p hpK
  have hbound : ∀ x : PDE.Vec n, PDE.vecNormSq x ≤ R ^ 2 →
      x ∈ Metric.closedBall 0 |R| := by
    intro x hx
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
    intro i
    rw [Real.norm_eq_abs]
    exact abs_le_of_sq_le_sq (by rw [sq_abs]; exact (PDE.sq_apply_le_vecNormSq x i).trans hx) (abs_nonneg R)
  have hr' : radialSq p ≤ R ^ 2 := hr
  have hpos := PDE.vecNormSq_nonneg p.position
  have hvel := PDE.vecNormSq_nonneg p.velocity
  refine ⟨⟨hat, htb⟩, hbound p.position ?_, hbound p.velocity ?_⟩
  · unfold radialSq at hr'; linarith
  · unfold radialSq at hr'; linarith

/-- The closed moving slab is closed. -/
theorem isClosed_movingClosedSlab {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (hγ : Continuous γ) (a b : ℝ) : IsClosed (movingClosedSlab Ω γ a b) := by
  have h1 : IsClosed {p : KineticPoint n | a ≤ p.time} :=
    isClosed_le continuous_const continuous_time
  have h2 : IsClosed {p : KineticPoint n | p.time ≤ b} :=
    isClosed_le continuous_time continuous_const
  have := (h1.inter h2).inter (isClosed_setOf_mem_closure_movingDomain (Ω := Ω) (n := n) hγ)
  convert this using 1
  ext p
  simp [movingClosedSlab]
  tauto

/-- Bounded truncations of the closed moving slab are compact. -/
theorem isCompact_movingClosedSlab_inter {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (hγ : Continuous γ) (a b R : ℝ) :
    IsCompact (movingClosedSlab Ω γ a b ∩ {p | radialSq p ≤ R ^ 2}) :=
  isCompact_inter_radialSq (isClosed_movingClosedSlab hγ a b) (fun _ hp => ⟨hp.1, hp.2.1⟩) R

/-- The active part of the moving slab has the one-sided neighbourhood property. -/
theorem eventually_future_mem_movingClosedSlab {n : ℕ} {Ω : Set (PDE.Vec n)}
    (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {a b : ℝ} {p : KineticPoint n}
    (hp : p ∈ movingActiveSlab Ω γ a b) :
    ∀ᶠ q in 𝓝 p, p.time ≤ q.time → q ∈ movingClosedSlab Ω γ a b := by
  obtain ⟨hat, htb, hpm⟩ := hp
  have h2 :=
    (isOpen_lt continuous_time continuous_const).mem_nhds htb
  filter_upwards [((isOpen_setOf_mem_movingDomain hΩ hγ).mem_nhds hpm), h2] with q hq1 hq2 hqt
  exact ⟨hat.trans hqt, hq2.le, subset_closure hq1⟩

/-- A point of the closed moving slab that is not in the active part lies on the
terminal face or the lateral frontier. -/
theorem mem_boundary_of_movingClosedSlab {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} {a b : ℝ} {p : KineticPoint n}
    (hp : p ∈ movingClosedSlab Ω γ a b) (hnot : p ∉ movingActiveSlab Ω γ a b) :
    p.time = b ∨ p.position ∈ frontier (movingDomain Ω γ p.time) := by
  obtain ⟨hat, htb, hpc⟩ := hp
  by_cases h1 : p.time < b
  · by_cases h2 : p.position ∈ movingDomain Ω γ p.time
    · exact absurd ⟨hat, h1, h2⟩ hnot
    · right
      rw [(isOpen_movingDomain hΩ p.time).frontier_eq]
      exact ⟨hpc, h2⟩
  · left
    exact le_antisymm htb (not_lt.mp h1)

/-- The active part of a bounded truncation has the one-sided neighbourhood property:
every nearby point of no earlier time still lies in the truncated closed slab. -/
theorem eventually_future_mem_truncated {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {a b R : ℝ} {p : KineticPoint n}
    (hp : p ∈ movingActiveSlab Ω γ a b ∩ {q | radialSq q < R ^ 2}) :
    ∀ᶠ q in 𝓝 p, p.time ≤ q.time →
      q ∈ movingClosedSlab Ω γ a b ∩ {q | radialSq q ≤ R ^ 2} := by
  obtain ⟨⟨hat, htb, hpm⟩, hr⟩ := hp
  have h1 :=
    (isOpen_setOf_mem_movingDomain hΩ hγ).mem_nhds hpm
  have h2 :=
    (isOpen_lt continuous_time continuous_const).mem_nhds htb
  have h3 : ∀ᶠ q in 𝓝 p, radialSq q < R ^ 2 :=
    (isOpen_lt continuous_radialSq continuous_const).mem_nhds hr
  filter_upwards [h1, h2, h3] with q hq1 hq2 hq3 hqt
  exact ⟨⟨hat.trans hqt, hq2.le, subset_closure hq1⟩, hq3.le⟩

/-- A point of the truncated closed slab that is not in the active part lies on the
terminal face, the lateral frontier, or the artificial radial boundary. -/
theorem mem_boundary_of_truncated {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} {a b R : ℝ} {p : KineticPoint n}
    (hp : p ∈ movingClosedSlab Ω γ a b ∩ {q | radialSq q ≤ R ^ 2})
    (hnot : p ∉ movingActiveSlab Ω γ a b ∩ {q | radialSq q < R ^ 2}) :
    p.time = b ∨ p.position ∈ frontier (movingDomain Ω γ p.time) ∨ radialSq p = R ^ 2 := by
  obtain ⟨⟨hat, htb, hpc⟩, hr⟩ := hp
  by_cases h1 : p.time < b
  · by_cases h2 : p.position ∈ movingDomain Ω γ p.time
    · right; right
      by_contra h3
      exact hnot ⟨⟨hat, h1, h2⟩, lt_of_le_of_ne hr h3⟩
    · right; left
      have hopen : IsOpen (movingDomain Ω γ p.time) :=
        isOpen_movingDomain hΩ p.time
      rw [hopen.frontier_eq]
      exact ⟨hpc, h2⟩
  · left
    exact le_antisymm htb (not_lt.mp h1)

end HypoellipticAleksandrov.KineticAleksandrov

