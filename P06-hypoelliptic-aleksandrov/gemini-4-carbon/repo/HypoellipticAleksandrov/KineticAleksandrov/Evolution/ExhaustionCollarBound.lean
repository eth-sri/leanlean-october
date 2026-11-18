module

public import HypoellipticAleksandrov.Parabolic.ScalarMaximum
public import HypoellipticAleksandrov.Parabolic.AffineScalarCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierTwo

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped MatrixOrder Matrix.Norms.Elementwise Topology


/-- Every actual straightened finite Dirichlet solution has the original datum bound,
independent of the curve, both ellipsoid radii, and positive viscosity. -/
theorem abs_le_straightened_dirichlet {n : ℕ} {lam Lam : ℝ}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    {a τ r R : ℝ} (haτ : a < τ) (hr : 0 < r) (hR : 0 < R)
    {g : ℝ → PDE.Vec n} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {ε : ℝ} (hε : 0 ≤ ε) (F : BoundedBorel (EvolutionAmbientState n))
    (u : TimeVelocity (n + n) → ℝ)
    (hu : IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n r R))
      (straightenedCoefficient B g ε) (straightenedDrift b g)
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g τ + spatialY x, spatialZ x)) (fun _ => 0) u)
    {C : ℝ} (hC : 0 ≤ C) (hFC : ∀ q, |F q| ≤ C) :
    ∀ q ∈ scalarParabolicClosedCylinder a τ
      (openEllipsoid (straightenedEllipsoidMatrix n r R)), |u q| ≤ C  := by
  have abs_le_of_classicalBackwardDirichlet_zero {d : ℕ} {Ω : Set (PDE.Vec d)} {a τ : ℝ} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (haτ : a < τ) (A : CoefficientField d) (β : ℝ → PDE.Vec d → PDE.Vec d) (hA : IsContinuousCoefficient A) (hβ : Continuous (fun q : TimeVelocity d => β q.1 q.2)) (hAp : ∀ s x, (A s x).PosSemidef) (φ : PDE.Vec d → ℝ) (u : TimeVelocity d → ℝ) (hu : IsClassicalBackwardDirichletSolution a τ Ω A β
      (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) u) {C : ℝ} (hC : 0 ≤ C) (hφ : ∀ x ∈ closure Ω, |φ x| ≤ C) :
      ∀ q ∈ scalarParabolicClosedCylinder a τ Ω, |u q| ≤ C := by
    have side (s : ℝ) (hs : s = 1 ∨ s = -1) :
        ∀ q ∈ scalarParabolicClosedCylinder a τ Ω, s * u q + 0 ≤ C := by
      apply scalar_le_on_closedCylinder_of_terminal_lateral_le hΩ hΩb haτ A β hA hβ hAp
        (fun q => s * u q + 0)
      · exact (hu.1.const_smul s).add continuousOn_const
      · exact hu.2.1.const_mul_add_const s 0
      · intro q hq
        have heq := hu.2.2.1 q hq
        have hid := scalarParabolicZeroOrderOperator_const_mul_add_const
          A β (fun _ _ => 0) s 0 u q
        simp only [scalarParabolicZeroOrderOperator, zero_mul, add_zero] at heq hid
        simpa only [add_zero, hid, heq, mul_zero] using (le_refl (0 : ℝ))
      · rintro ⟨t, x⟩ ⟨ht, hx⟩
        simp only [mem_singleton_iff] at ht
        subst t
        rw [hu.2.2.2.1 x hx]
        rcases hs with rfl | rfl
        · simpa only [one_mul, add_zero] using (abs_le.mp (hφ x hx)).2
        · have := (abs_le.mp (hφ x hx)).1
          linarith
      · intro q hq
        rw [hu.2.2.2.2 q hq, mul_zero, zero_add]
        exact hC
    intro q hq
    have hp := side 1 (Or.inl rfl) q hq
    have hn := side (-1) (Or.inr rfl) q hq
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  apply abs_le_of_classicalBackwardDirichlet_zero
    (isOpen_straightenedEllipsoid n hr hR) (isBounded_straightenedEllipsoid n hr hR)
    haτ (straightenedCoefficient B g ε) (straightenedDrift b g)
    (isSmoothCoefficient_straightenedCoefficient hBs hg ε).continuous
    (contDiff_straightenedDrift hbs hg).continuous
    (fun s x => ?_) _ u hu hC (fun x _ => hFC _)
  rw [straightenedCoefficient_apply]
  exact viscousBlockMatrix_posSemidef
    (posSemidef_of_hasEverywhereLoewnerBounds hlam.le hB _ _ _) hε



/-- The actual finite Dirichlet solution obeys the collar estimate uniformly in the
transported truncation radius. The lower comparison time is strictly inside its slab. -/
theorem abs_le_collar_straightened_dirichlet
    {n : ℕ} {lam Lam : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    {a α τ r R d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hr : 0 < r) (hR : 0 < R) (hd : 0 < d) (hdr : d < r)
    {g : ℝ → PDE.Vec n} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hL : 0 ≤ L)
    (hgL : ∀ s t, PDE.vecEuclideanNorm (g s - g t) ≤ L * |s - t|)
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * d ≤ r - PDE.vecEuclideanNorm (q.1 - g τ))
    (u : TimeVelocity (n + n) → ℝ)
    (hu : IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n r R))
      (straightenedCoefficient B g ε) (straightenedDrift b g)
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g τ + spatialY x, spatialZ x)) (fun _ => 0) u) :
    ∀ p ∈ straightenedPoint g ⁻¹' scalarParabolicClosedCylinder α τ
      (openEllipsoid (straightenedEllipsoidMatrix n r R)),
      (r - d) ^ 2 ≤ centreSq 0 g p →
      |straightenedPullback g u p| ≤ collarSupersolution 0 r d L lam C g p := by
  let D := openEllipsoid (straightenedEllipsoidMatrix n r R)
  let K := (straightenedPoint g ⁻¹' scalarParabolicClosedCylinder α τ D) ∩
    {p | (r - d) ^ 2 ≤ centreSq 0 g p}
  let A := {p : KineticPoint n | p.time ∈ Ico α τ ∧ (straightenedPoint g p).2 ∈ D} ∩
    {p | (r - d) ^ 2 < centreSq 0 g p}
  let v := straightenedPullback g u
  let G := collarSupersolution 0 r d L lam C g
  have hDo : IsOpen D := isOpen_straightenedEllipsoid n hr hR
  have hκ : 0 < collarKappa L lam := div_pos (by linarith) hlam
  have hcoef : 0 ≤ C / barrierW (collarKappa L lam) d :=
    div_nonneg hC (barrierW_pos hκ hd).le
  have hKc : IsCompact K :=
    (isCompact_straightened_closedCylinder (isBounded_straightenedEllipsoid n hr hR)
      hg.continuous α τ).inter_right
      (isClosed_le continuous_const (continuous_centreSq 0 hg.continuous))
  have hsub (p : KineticPoint n) (hp : p ∈ K) :
      straightenedPoint g p ∈ scalarParabolicClosedCylinder a τ D :=
    ⟨⟨haα.le.trans hp.1.1.1, hp.1.1.2⟩, hp.1.2⟩
  have hv : ContinuousOn v K :=
    hu.1.comp (continuous_straightenedPoint hg.continuous).continuousOn hsub
  have hbound (p : KineticPoint n) (hp : p ∈ K) : |v p| ≤ C :=
    abs_le_straightened_dirichlet hlam hB hBs hbs (haα.trans hατ) hr hR hg hε
      F u hu hC hFC _ (hsub p hp)
  have hGn (p : KineticPoint n) (hp : p ∈ K) : 0 ≤ G p := by
    have hY := vecNormSq_spatialY_le_of_mem_closure_straightenedEllipsoid hr hR hp.1.2
    have hS : centreSq 0 g p ≤ r ^ 2 := by
      simpa only [centreSq, straightenedPoint, spatialY_spatialPack, add_zero] using hY
    exact mul_nonneg hcoef (collarBarrier_nonneg hκ hr.le hS)
  have hreg (p : KineticPoint n) (hp : p ∈ A) :
      IsSliceRegularAt v p ∧ viscousTransportedOperator B b ε v p = 0 :=
    straightenedPullback_dirichlet_sliceRegular hDo hg hu p
      ⟨⟨haα.trans_le hp.1.1.1, hp.1.1.2⟩, hp.1.2⟩
  have hSpos (p : KineticPoint n) (hp : p ∈ A) :
      0 < PDE.vecNormSq (p.position - (g p.time + 0)) :=
    lt_of_le_of_lt (sq_nonneg _) hp.2
  have hGreg (p : KineticPoint n) (hp : p ∈ A) : IsSliceRegularAt G p :=
    (isSliceRegularAt_collarBarrier (collarKappa L lam) r
      (((hg.differentiable (by simp)) p.time).add_const 0) (hSpos p hp)).const_mul _
  have hGop (p : KineticPoint n) (hp : p ∈ A) :
      viscousTransportedOperator B b ε G p ≤ 0 := by
    have hgd := (hg.differentiable (by simp)) p.time
    have hm := hgd.hasDerivAt.add_const (0 : PDE.Vec n)
    have hmL := vecEuclideanNorm_le_of_hasDerivAt_lipschitz hL hgd.hasDerivAt hgL
    have hn := viscousTransportedOperator_collarBarrier_nonpos (b := b) ε hκ hlam.le
      (div_mul_cancel₀ _ hlam.ne') r hm hmL (hSpos p hp) (hB _ _ _).1
    change viscousTransportedOperator B b ε
      (fun q => C / barrierW (collarKappa L lam) d *
        collarBarrier (collarKappa L lam) r (fun t => g t + 0) q) p ≤ 0
    rw [viscousTransportedOperator_const_mul _
      (isSliceRegularAt_collarBarrier (collarKappa L lam) r hm.differentiableAt (hSpos p hp))]
    exact mul_nonpos_of_nonneg_of_nonpos hcoef hn
  have side (s : ℝ) (hs : s = 1 ∨ s = -1) : ∀ p ∈ K, s * v p ≤ G p := by
    have hmax := le_zero_of_viscous_nonneg_compact (B := B) (b := b) (ε := ε)
      (K := K) (D := A) (w := fun p => s * v p - G p) (T := τ) hε hKc
      (fun p hp => hp.1.1.2)
      ((hv.const_smul s).sub
        (continuous_collarSupersolution 0 r d L lam C hg.continuous).continuousOn) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      have := hmax p hp
      linarith
    · intro p hp
      have hf := eventually_future_mem_straightened_closedCylinder hDo hg.continuous hp.1
      have ho : ∀ᶠ q in 𝓝 p, (r - d) ^ 2 < centreSq 0 g q :=
        (isOpen_lt continuous_const (continuous_centreSq 0 hg.continuous)).mem_nhds hp.2
      filter_upwards [hf, ho] with q hq hqS hqt
      exact ⟨hq hqt, hqS.le⟩
    · intro p hp
      exact ((hreg p hp).1.const_mul s).sub (hGreg p hp)
    · intro p _
      exact posSemidef_of_hasEverywhereLoewnerBounds hlam.le hB _ _ _
    · intro p hp
      rw [viscousTransportedOperator_sub ((hreg p hp).1.const_mul s) (hGreg p hp),
        viscousTransportedOperator_const_mul s (hreg p hp).1, (hreg p hp).2, mul_zero]
      exact sub_nonneg.mpr (hGop p hp)
    · intro p hp hn
      by_cases ht : p.time = τ
      · have hz := hu.2.2.2.1 (straightenedPoint g p).2 hp.1.2
        have he : v p = F (p.position, p.velocity) := by
          simpa only [v, straightenedPullback, straightenedPoint, ht,
            spatialY_spatialPack, spatialZ_spatialPack, add_sub_cancel] using hz
        have hF0 := terminalDatum_eq_zero_of_collar hd hdr
          (by simpa only [add_zero] using hsupp) ht hp.2
        rw [he, hF0, mul_zero]
        exact sub_nonpos.mpr (hGn p hp)
      by_cases hx : (straightenedPoint g p).2 ∈ D
      · have hS : centreSq 0 g p = (r - d) ^ 2 :=
          le_antisymm (not_lt.mp (fun h => hn
            ⟨⟨⟨hp.1.1.1, lt_of_le_of_ne hp.1.1.2 ht⟩, hx⟩, h⟩)) hp.2
        have he : G p = C := collarSupersolution_inner hdr hκ hd hS
        have hb := hbound p hp
        rw [he]
        rcases hs with rfl | rfl <;> linarith [le_abs_self (v p), neg_le_abs (v p)]
      · have hfr : (straightenedPoint g p).2 ∈ frontier D := by
          rw [hDo.frontier_eq]
          exact ⟨hp.1.2, hx⟩
        have hz := hu.2.2.2.2 (straightenedPoint g p)
          ⟨⟨haα.le.trans hp.1.1.1, hp.1.1.2⟩, hfr⟩
        change v p = 0 at hz
        rw [hz, mul_zero]
        exact sub_nonpos.mpr (hGn p hp)
  intro p hp hS
  have h1 := side 1 (Or.inl rfl) p ⟨hp, hS⟩
  have h2 := side (-1) (Or.inr rfl) p ⟨hp, hS⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩



/-- The actual finite Dirichlet solution obeys the full minimum-form collar bound on
its entire inset closed cylinder, uniformly in the transported truncation radius. -/
theorem abs_le_min_collar_straightened_dirichlet
    {n : ℕ} {lam Lam : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    {a α τ r R d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hr : 0 < r) (hR : 0 < R) (hd : 0 < d) (hdr : d < r)
    {g : ℝ → PDE.Vec n} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hL : 0 ≤ L)
    (hgL : ∀ s t, PDE.vecEuclideanNorm (g s - g t) ≤ L * |s - t|)
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * d ≤ r - PDE.vecEuclideanNorm (q.1 - g τ))
    (u : TimeVelocity (n + n) → ℝ)
    (hu : IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n r R))
      (straightenedCoefficient B g ε) (straightenedDrift b g)
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g τ + spatialY x, spatialZ x)) (fun _ => 0) u) :
    ∀ p ∈ straightenedPoint g ⁻¹' scalarParabolicClosedCylinder α τ
      (openEllipsoid (straightenedEllipsoidMatrix n r R)),
      |straightenedPullback g u p| ≤ C * min 1
        (barrierW (collarKappa L lam) (r - PDE.vecEuclideanNorm (p.position - g p.time)) /
          barrierW (collarKappa L lam) d) := by
  intro p hp
  have hκ : 0 < collarKappa L lam := div_pos (by linarith) hlam
  have hW := barrierW_pos hκ hd
  have hbound := abs_le_straightened_dirichlet hlam hB hBs hbs (haα.trans hατ) hr hR
    hg hε F u hu hC hFC (straightenedPoint g p)
    ⟨⟨haα.le.trans hp.1.1, hp.1.2⟩, hp.2⟩
  by_cases hratio : 1 ≤
      barrierW (collarKappa L lam) (r - PDE.vecEuclideanNorm (p.position - g p.time)) /
        barrierW (collarKappa L lam) d
  · rw [min_eq_left hratio, mul_one]
    exact hbound
  · have hw : barrierW (collarKappa L lam) (r - PDE.vecEuclideanNorm (p.position - g p.time)) ≤
        barrierW (collarKappa L lam) d := by
      exact (div_le_one hW).mp (le_of_lt (not_le.mp hratio))
    have hd' := le_of_barrierW_le hκ hw
    have hn : r - d ≤ PDE.vecEuclideanNorm (p.position - g p.time) := by linarith
    have hS : (r - d) ^ 2 ≤ centreSq 0 g p := by
      have he := pow_le_pow_left₀ (by linarith : 0 ≤ r - d) hn 2
      simpa only [PDE.vecEuclideanNorm_sq, centreSq, add_zero] using he
    have he := abs_le_collar_straightened_dirichlet hlam hB hBs hbs haα hατ hr hR hd hdr
      hg hL hgL hε hC F hFC hsupp u hu p hp hS
    rw [min_eq_right (le_of_lt (not_le.mp hratio))]
    simpa only [collarSupersolution, collarBarrier, collarProfile, barrierW, add_zero,
      PDE.vecEuclideanNorm, mul_div_assoc, div_mul_eq_mul_div] using he

end HypoellipticAleksandrov.KineticAleksandrov

