module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.StraightenedTransferClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyGeometry

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology


/-- The actual scalar Dirichlet solution transfers to a slice-regular kinetic solution
on its finite open cylinder; no Hörmander or joint C2 premise is needed. -/
theorem straightenedPullback_dirichlet_sliceRegular
    {n : ℕ} {D : Set (PDE.Vec (n + n))} (hD : IsOpen D)
    {g : ℝ → PDE.Vec n} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} {ε a τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} {u : TimeVelocity (n + n) → ℝ}
    (hu : IsClassicalBackwardDirichletSolution a τ D
      (straightenedCoefficient B g ε) (straightenedDrift b g)
      (fun _ _ => 0) (fun _ _ => 0) (fun x => F (g τ + spatialY x, spatialZ x))
      (fun _ => 0) u) :
    ∀ p ∈ straightenedPoint g ⁻¹' scalarParabolicOpenCylinder a τ D,
      IsSliceRegularAt (straightenedPullback g u) p ∧
      viscousTransportedOperator B b ε (straightenedPullback g u) p = 0 := by
  intro p hp
  have ho : IsOpen (scalarParabolicOpenCylinder a τ D) := isOpen_Ioo.prod hD
  have hd := scalarC12_differentiableAt ho hu.2.1 hp
  have hs := hu.2.1.spatialSlice_contDiffAt hp
  have hgd := (hg.differentiable (by simp)) p.time
  refine ⟨isSliceRegularAt_straightenedPullback hgd hd hs, ?_⟩
  rw [viscousTransportedOperator_straightenedPullback hgd hd hs]
  simpa using hu.2.2.1 _ hp

/-- The straightening map, with its explicit inverse, is a homeomorphism on the literal
kinetic and scalar time-spatial carriers. -/
def straightenedPointHomeomorph {n : ℕ} (g : ℝ → PDE.Vec n) (hg : Continuous g) :
    KineticPoint n ≃ₜ TimeVelocity (n + n) where
  toFun := straightenedPoint g
  invFun q := ⟨q.1, g q.1 + spatialY q.2, spatialZ q.2⟩
  left_inv p := by
    ext <;> simp [straightenedPoint]
  right_inv q := by
    rcases q with ⟨t, x⟩
    simp [straightenedPoint]
  continuous_toFun := continuous_straightenedPoint hg
  continuous_invFun := KineticPoint.continuous_mk continuous_fst
    ((hg.comp continuous_fst).add
      ((contDiff_spatialY (m := 0)).continuous.comp continuous_snd))
    ((contDiff_spatialZ (m := 0)).continuous.comp continuous_snd)

/-- A bounded finite spatial cylinder remains compact in absolute moving coordinates. -/
theorem isCompact_straightened_closedCylinder {n : ℕ} {D : Set (PDE.Vec (n + n))}
    (hD : Bornology.IsBounded D) {g : ℝ → PDE.Vec n} (hg : Continuous g) (a τ : ℝ) :
    IsCompact (straightenedPoint g ⁻¹' scalarParabolicClosedCylinder a τ D) :=
  (straightenedPointHomeomorph g hg).isCompact_preimage.mpr
    (isCompact_Icc.prod hD.isCompact_closure)



/-- The closed straightened ellipsoid lies in the closed diffused block ball. -/
theorem vecNormSq_spatialY_le_of_mem_closure_straightenedEllipsoid
    {n : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {x : PDE.Vec (n + n)}
    (hx : x ∈ closure (openEllipsoid (straightenedEllipsoidMatrix n r R))) :
    PDE.vecNormSq (spatialY x) ≤ r ^ 2 := by
  have hc : IsClosed {x : PDE.Vec (n + n) | PDE.vecNormSq (spatialY x) ≤ r ^ 2} :=
    isClosed_le (PDE.continuous_vecNormSq.comp (contDiff_spatialY (m := 0)).continuous)
      continuous_const
  apply closure_minimal ?_ hc hx
  intro y hy
  have hsum := (straightenedEllipsoid_characterization n r R hr hR).2 y |>.mp hy
  have hZ := div_nonneg (PDE.vecNormSq_nonneg (spatialZ y)) (sq_nonneg R)
  exact ((div_lt_one (sq_pos_of_pos hr)).mp (by linarith)).le

/-- Future neighbourhoods of active finite-cylinder points remain in the closed cylinder. -/
theorem eventually_future_mem_straightened_closedCylinder
    {n : ℕ} {D : Set (PDE.Vec (n + n))} (hD : IsOpen D)
    {g : ℝ → PDE.Vec n} (hg : Continuous g) {α τ : ℝ} {p : KineticPoint n}
    (hp : (straightenedPoint g p).1 ∈ Ico α τ ∧ (straightenedPoint g p).2 ∈ D) :
    ∀ᶠ q in 𝓝 p, p.time ≤ q.time →
      q ∈ straightenedPoint g ⁻¹' scalarParabolicClosedCylinder α τ D := by
  have he := (hD.preimage ((continuous_straightenedPoint hg).snd)).mem_nhds hp.2
  have ht' :=
    (isOpen_lt continuous_time continuous_const).mem_nhds hp.1.2
  filter_upwards [he, ht'] with q hq hqt hpq
  exact ⟨⟨hp.1.1.trans hpq, hqt.le⟩, subset_closure hq⟩

end HypoellipticAleksandrov.KineticAleksandrov

