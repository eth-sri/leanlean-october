module

import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCompact
public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel

/-!
# Moving slabs and their bounded truncations

Geometry of the moving cylinder `{(σ, y, z) : y ∈ γ(σ) + Ω}` used by the comparison
theorems: closures of moving domains, compactness of bounded truncations of the closed
slab `a ≤ σ ≤ b`, and the one-sided neighbourhood property of the active part.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set
open scoped Topology

variable {n : ℕ}

/-- The squared Euclidean size `|y|² + |z|²` of the spatial coordinates of a kinetic
point. -/
def radialSq  (p : KineticPoint n) : ℝ :=
  PDE.vecNormSq p.position + PDE.vecNormSq p.velocity

variable (Ω : PDE.VelocityRegion n) (γ : ℝ → PDE.Vec n) (a b : ℝ)

/-- The closed moving slab `{a ≤ σ ≤ b, y ∈ closure (γ(σ) + Ω)}` (all `z`). -/
def movingClosedSlab   :
    Set (KineticPoint n) :=
  {p | a ≤ p.time ∧ p.time ≤ b ∧ p.position ∈ closure (movingDomain Ω γ p.time)}

/-- The active part `{a ≤ σ < b, y ∈ γ(σ) + Ω}` of the moving slab. -/
def movingActiveSlab   :
    Set (KineticPoint n) :=
  {p | a ≤ p.time ∧ p.time < b ∧ p.position ∈ movingDomain Ω γ p.time}

variable {Ω : PDE.VelocityRegion n}

variable {γ : ℝ → PDE.Vec n} {σ : ℝ} {y : PDE.Vec n}

/-- A point of the closed moving cylinder lies in `movingClosedSlab` exactly when its
position is in the closure of the moving domain. -/
theorem mem_closure_movingDomain_iff    :
    y ∈ closure (movingDomain Ω γ σ) ↔ y - γ σ ∈ closure Ω := by
  have h : movingDomain Ω γ σ = (Homeomorph.subRight (γ σ)) ⁻¹' Ω := by
    rw [movingDomain, ← PDE.preimage_subRight_eq_translateSet]
    rfl
  rw [h, ← Homeomorph.preimage_closure]
  rfl

/-- Membership in the moving domain. -/
theorem mem_movingDomain_iff    : y ∈ movingDomain Ω γ σ ↔ y - γ σ ∈ Ω :=
  PDE.mem_translateSet_iff_sub_mem

/-- The set of kinetic points whose position lies in the moving domain is open. -/
theorem isOpen_setOf_mem_movingDomain   (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) :
    IsOpen {p : KineticPoint n | p.position ∈ movingDomain Ω γ p.time} := by

  have := hΩ.preimage (continuous_position.sub (hγ.comp continuous_time))
  convert this using 1
  ext p
  exact mem_movingDomain_iff

/-- The set of kinetic points whose position lies in the closure of the moving domain
is closed. -/
theorem isClosed_setOf_mem_closure_movingDomain
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) :
    IsClosed {p : KineticPoint n | p.position ∈ closure (movingDomain Ω γ p.time)} := by

  have := (isClosed_closure (s := Ω)).preimage (continuous_position.sub (hγ.comp continuous_time))
  convert this using 1
  ext p
  exact mem_closure_movingDomain_iff

/-- Continuity of `|y|² + |z|²`. -/
theorem continuous_radialSq  : Continuous (@radialSq n) := by
  unfold radialSq PDE.vecNormSq PDE.vecDot
  have h1 : Continuous (@KineticPoint.position n) := continuous_position
  have h2 : Continuous (@KineticPoint.velocity n) := continuous_velocity
  fun_prop

/-- A closed set of kinetic points with bounded times has compact bounded truncations. -/
theorem isCompact_inter_radialSq  {K : Set (KineticPoint n)} (hK : IsClosed K)
    {a b : ℝ} (hKt : ∀ p ∈ K, a ≤ p.time ∧ p.time ≤ b) (R : ℝ) :
    IsCompact (K ∩ {p | radialSq p ≤ R ^ 2}) := by
  let sharedTerm_62f8dc1c0c := (Metric.closedBall (0 : PDE.Vec n) |R|)
  let Kbig  :=
    KineticPoint.homeomorphProd n ⁻¹'
      (Icc a b ×ˢ (sharedTerm_62f8dc1c0c ×ˢ sharedTerm_62f8dc1c0c))
  have hKbig : IsCompact Kbig :=
    (KineticPoint.homeomorphProd n).isCompact_preimage.mpr
      (isCompact_Icc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)))

  refine hKbig.of_isClosed_subset (hK.inter (isClosed_le continuous_radialSq continuous_const)) ?_
  intro p hp
  obtain ⟨hpK, hr⟩ := hp
  obtain ⟨hat, htb⟩ := hKt p hpK
  have hbound : ∀ x : PDE.Vec n, PDE.vecNormSq x ≤ R ^ 2 →
      x ∈ sharedTerm_62f8dc1c0c := by
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

variable {Ω : PDE.VelocityRegion n}

section
variable {γ : ℝ → PDE.Vec n} (hγ : Continuous γ)

include hγ
/-- The closed moving slab is closed. -/
theorem isClosed_movingClosedSlab    (a b : ℝ) : IsClosed (movingClosedSlab Ω γ a b) := by
  have h1 : IsClosed {p : KineticPoint n | a ≤ p.time} :=
    isClosed_le continuous_const continuous_time
  have h2 : IsClosed {p : KineticPoint n | p.time ≤ b} :=
    isClosed_le continuous_time continuous_const
  have h3 := isClosed_setOf_mem_closure_movingDomain (Ω := Ω) (n := n) hγ
  have := (h1.inter h2).inter h3
  convert this using 1
  ext p
  simp only [movingClosedSlab, mem_inter_iff, Set.mem_ofPred_eq]
  tauto

/-- Bounded truncations of the closed moving slab are compact. -/
theorem isCompact_movingClosedSlab_inter    (a b R : ℝ) :
    IsCompact (movingClosedSlab Ω γ a b ∩ {p | radialSq p ≤ R ^ 2}) :=
  isCompact_inter_radialSq (isClosed_movingClosedSlab hγ a b) (fun _ hp => ⟨hp.1, hp.2.1⟩) R
end


variable (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n}

include hΩ
/-- The active part of the moving slab has the one-sided neighbourhood property. -/
theorem eventually_future_mem_movingClosedSlab
     (hγ : Continuous γ) {a b : ℝ} {p : KineticPoint n}
    (hp : p ∈ movingActiveSlab Ω γ a b) :
    ∀ᶠ q in 𝓝 p, p.time ≤ q.time → q ∈ movingClosedSlab Ω γ a b := (And.casesOn hp fun hat right =>
  And.casesOn right fun htb hpm =>
    Filter.mp_mem (IsOpen.mem_nhds (isOpen_lt continuous_time continuous_const) htb)
      (Filter.mp_mem (IsOpen.mem_nhds (isOpen_setOf_mem_movingDomain hΩ hγ) hpm)
        (Filter.univ_mem' (id fun q hq1 hq2 hqt => ⟨LE.le.trans hat hqt, ⟨LT.lt.le hq2, subset_closure hq1⟩⟩))))

/-- A point of the closed moving slab that is not in the active part lies on the
terminal face or the lateral frontier. -/
theorem mem_boundary_of_movingClosedSlab    {a b : ℝ} {p : KineticPoint n}
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
theorem eventually_future_mem_truncated    (hγ : Continuous γ) {a b R : ℝ} {p : KineticPoint n}
    (hp : p ∈ movingActiveSlab Ω γ a b ∩ {q | radialSq q < R ^ 2}) :
    ∀ᶠ q in 𝓝 p, p.time ≤ q.time →
      q ∈ movingClosedSlab Ω γ a b ∩ {q | radialSq q ≤ R ^ 2} := by
  obtain ⟨⟨hat, htb, hpm⟩, hr⟩ := hp



  filter_upwards [((isOpen_setOf_mem_movingDomain hΩ hγ).mem_nhds hpm), ((isOpen_lt continuous_time continuous_const).mem_nhds htb), ((isOpen_lt continuous_radialSq continuous_const).mem_nhds hr)] with q hq1 hq2 hq3 hqt
  exact ⟨⟨hat.trans hqt, hq2.le, subset_closure hq1⟩, hq3.le⟩

/-- A point of the truncated closed slab that is not in the active part lies on the
terminal face, the lateral frontier, or the artificial radial boundary. -/
theorem mem_boundary_of_truncated    {a b R : ℝ} {p : KineticPoint n}
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

      rw [(isOpen_movingDomain hΩ p.time).frontier_eq]
      exact ⟨hpc, h2⟩
  · left
    exact le_antisymm htb (not_lt.mp h1)

end HypoellipticAleksandrov.KineticAleksandrov
