module

public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSquares
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeCoord

/-!
# The packed operators and the project's `transportedForwardOperator`

For `u : KineticPoint n → ℝ` write `U = u ∘ evolutionHomeomorph n` for its packed pullback
`(σ, v, z) ↦ u ⟨σ, v, z⟩`.  If `U` is `C²` at `x`, then
`transportedOperator B b U x = transportedForwardOperator B b u (e x)` and
`regularizedOperator B b ε U x = transportedForwardOperator B b u (e x)
  + ε ∑_l kineticVelocityHessian u (e x) l l`.
The proof rewrites each of the `kinetic…` derivative surfaces (time derivative, position and
velocity gradients, the position and velocity Hessians) along an affine slice of the packed space.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

variable {n : ℕ}

/-! ### Slices of the packed space -/

variable (n) in
/-- The time step `s ↦ s ∂_σ`. -/
def stepT : ℝ →L[ℝ] EvolutionVec n := (ContinuousLinearMap.id ℝ ℝ).smulRight basisT

variable (n) in
/-- The embedding `w ↦ (0, w, 0)` of the diffused block. -/
def embedDiffused : PDE.Vec n →L[ℝ] EvolutionVec n :=
  ((evolutionProdCLE n).symm : ℝ × (PDE.Vec n × PDE.Vec n) →L[ℝ] EvolutionVec n).comp
    ((ContinuousLinearMap.inr ℝ ℝ (PDE.Vec n × PDE.Vec n)).comp
      (ContinuousLinearMap.inl ℝ (PDE.Vec n) (PDE.Vec n)))

variable (n) in
/-- The embedding `w ↦ (0, 0, w)` of the transported block. -/
def embedTransported : PDE.Vec n →L[ℝ] EvolutionVec n :=
  ((evolutionProdCLE n).symm : ℝ × (PDE.Vec n × PDE.Vec n) →L[ℝ] EvolutionVec n).comp
    ((ContinuousLinearMap.inr ℝ ℝ (PDE.Vec n × PDE.Vec n)).comp
      (ContinuousLinearMap.inr ℝ (PDE.Vec n) (PDE.Vec n)))

@[simp] theorem stepT_apply (s : ℝ) : stepT n s = packPoint s 0 0 := by
  refine ext_coords ?_ ?_ ?_
  · simp [stepT, basisT]
  · simp_all [stepT, basisT]
  · simp_all [stepT, basisT]

section
variable (w : PDE.Vec n)

@[simp] theorem embedDiffused_apply  : embedDiffused n w = packPoint 0 w 0 := rfl

@[simp] theorem embedTransported_apply  :
    embedTransported n w = packPoint 0 0 w := rfl
end


section
variable (x : EvolutionVec n)

theorem add_stepT  (s : ℝ) :
    x + stepT n s = packPoint (timeCoord n x + s) (diffusedCoord n x) (transportedCoord n x) := by
  rw [stepT_apply]
  refine ext_coords ?_ ?_ ?_ <;> simp

variable (w : PDE.Vec n)

theorem add_embedDiffused   :
    x + embedDiffused n w =
      packPoint (timeCoord n x) (diffusedCoord n x + w) (transportedCoord n x) := by
  rw [embedDiffused_apply]
  refine ext_coords ?_ ?_ ?_ <;> simp

theorem add_embedTransported   :
    x + embedTransported n w =
      packPoint (timeCoord n x) (diffusedCoord n x) (transportedCoord n x + w) := by
  rw [embedTransported_apply]
  refine ext_coords ?_ ?_ ?_ <;> simp
end


section
variable {F E : Type*}

/-- Derivative of a function along an affine slice `y ↦ a + ι (y - p)`. -/
theorem fderiv_comp_affine  [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : F →L[ℝ] E) (a : E) (p : F) {V : E → ℝ}
    (hV : DifferentiableAt ℝ V a) :
    fderiv ℝ (fun y => V (a + ι (y - p))) p = (fderiv ℝ V a).comp ι := by

  have hV' : HasFDerivAt V (fderiv ℝ V a) (a + ι (p - p)) := by simpa using hV.hasFDerivAt
  exact (hV'.comp p (by
      have := (ι.hasFDerivAt).comp p ((hasFDerivAt_id p).sub_const p)
      simpa using this.const_add a)).fderiv

/-- Smoothness along an affine slice. -/
theorem contDiffAt_comp_affine  [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : F →L[ℝ] E) (a : E) (p : F) {V : E → ℝ}
    (hV : ContDiffAt ℝ 2 V a) : ContDiffAt ℝ 2 (fun y => V (a + ι (y - p))) p := by


  exact (show ContDiffAt ℝ 2 V ((fun y  => a + ι (y - p)) p) by simpa using hV).comp p (show ContDiff ℝ 2 (fun y  => a + ι (y - p)) by fun_prop).contDiffAt

/-- Second derivative along an affine slice. -/
theorem fderiv_fderiv_comp_affine  [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : F →L[ℝ] E) (a : E) (p : F) {V : E → ℝ}
    (hV : ContDiffAt ℝ 2 V a) (v w : F) :
    fderiv ℝ (fun y => fderiv ℝ (fun x' => V (a + ι (x' - p))) y w) p v =
      fderiv ℝ (fun z => fderiv ℝ V z (ι w)) a (ι v) := by
  let sharedTerm_ff3b3b4d6f := (fun y => fderiv ℝ V (a + ι (y - p)) (ι w))
  let sharedTerm_14924b0bca := ((fun z => fderiv ℝ V z (ι w)))



  have hslice : ∀ y, (fun x' => V (a + ι (x' - p))) =
      fun x' => V ((a + ι (y - p)) + ι (x' - y)) := by
    intro y
    funext x'
    congr 1
    rw [add_assoc, ← map_add]
    congr 2
    abel
  have heq : (fun y => fderiv ℝ (fun x' => V (a + ι (x' - p))) y w) =ᶠ[nhds p]
      sharedTerm_ff3b3b4d6f := by
    filter_upwards [((show Filter.Tendsto (fun y  => a + ι (y - p)) (nhds p) (nhds a) by

        have := (show ContinuousAt (fun y  => a + ι (y - p)) p by fun_prop).tendsto
        rwa [show a + ι (p - p) = a by simp] at this).eventually (hV.eventually (by simp)))] with y hy
    rw [hslice y, fderiv_comp_affine ι (a + ι (y - p)) y
      (hy.differentiableAt (by norm_num))]
    rfl
  rw [heq.fderiv_eq]
  have hg : DifferentiableAt ℝ sharedTerm_14924b0bca a :=
    ((hV.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have := fderiv_comp_affine ι a p hg
  rw [show (sharedTerm_ff3b3b4d6f) =
      fun y => sharedTerm_14924b0bca (a + ι (y - p)) from rfl, this]
  rfl
end


/-! ### The `kinetic…` derivative surfaces along the bridge -/

section Surfaces

variable {u : KineticPoint n → ℝ} {x : EvolutionVec n}

section
variable (x : EvolutionVec n)

theorem slice_time  (r : ℝ) :
    u ⟨r, diffusedCoord n x, transportedCoord n x⟩ =
      (u ∘ evolutionHomeomorph n) (x + stepT n (r - timeCoord n x)) := by
  rw [add_stepT, Function.comp_apply, evolutionHomeomorph_apply]
  simp

variable (y : PDE.Vec n)

theorem slice_position   :
    u ⟨timeCoord n x, y, transportedCoord n x⟩ =
      (u ∘ evolutionHomeomorph n) (x + embedDiffused n (y - diffusedCoord n x)) := by
  rw [add_embedDiffused, Function.comp_apply, evolutionHomeomorph_apply]
  simp

theorem slice_velocity   :
    u ⟨timeCoord n x, diffusedCoord n x, y⟩ =
      (u ∘ evolutionHomeomorph n) (x + embedTransported n (y - transportedCoord n x)) := by
  rw [add_embedTransported, Function.comp_apply, evolutionHomeomorph_apply]
  simp
end


section
variable (hU : DifferentiableAt ℝ (u ∘ evolutionHomeomorph n) x)

include hU in
/-- The kinetic time derivative is `∂_σ` of the packed pullback. -/
theorem kineticTimeDerivative_comp  :
    kineticTimeDerivative u (evolutionHomeomorph n x) =
      fderiv ℝ (u ∘ evolutionHomeomorph n) x basisT := by
  unfold kineticTimeDerivative
  simp only [time_evolutionHomeomorph, position_evolutionHomeomorph,
    velocity_evolutionHomeomorph]
  rw [show (fun r => u ⟨r, diffusedCoord n x, transportedCoord n x⟩) =
      fun r => (u ∘ evolutionHomeomorph n) (x + stepT n (r - timeCoord n x)) from
        funext (slice_time x), ← fderiv_apply_one_eq_deriv,
    fderiv_comp_affine (stepT n) x (timeCoord n x) hU]
  simp [stepT_apply, basisT]

include hU in
/-- The kinetic position gradient is the `∂_{v_j}` gradient of the packed pullback. -/
theorem kineticPositionGradient_comp
    (j : Fin n) :
    kineticPositionGradient u (evolutionHomeomorph n x) j =
      fderiv ℝ (u ∘ evolutionHomeomorph n) x (basisV j) := by
  unfold kineticPositionGradient
  simp only [time_evolutionHomeomorph, position_evolutionHomeomorph,
    velocity_evolutionHomeomorph, PDE.classicalGradient_apply]
  rw [show (fun y => u ⟨timeCoord n x, y, transportedCoord n x⟩) =
      fun y => (u ∘ evolutionHomeomorph n) (x + embedDiffused n (y - diffusedCoord n x)) from
        funext (slice_position x), fderiv_comp_affine (embedDiffused n) x _ hU]
  simp [basisV, PDE.basisVec]

include hU in
/-- The kinetic velocity gradient is the `∂_{z_l}` gradient of the packed pullback. -/
theorem kineticVelocityGradient_comp
    (l : Fin n) :
    kineticVelocityGradient u (evolutionHomeomorph n x) l =
      fderiv ℝ (u ∘ evolutionHomeomorph n) x (basisZ l) := by
  unfold kineticVelocityGradient
  simp only [time_evolutionHomeomorph, position_evolutionHomeomorph,
    velocity_evolutionHomeomorph, PDE.classicalGradient_apply]
  rw [show (fun y => u ⟨timeCoord n x, diffusedCoord n x, y⟩) =
      fun y => (u ∘ evolutionHomeomorph n) (x + embedTransported n (y - transportedCoord n x))
        from funext (slice_velocity x), fderiv_comp_affine (embedTransported n) x _ hU]
  simp [basisZ, PDE.basisVec]
end


/-- Entries of a gradient-valued function along a slice are derivatives of its entries. -/
theorem fderiv_classicalGradient_apply {f : PDE.Vec n → ℝ} {p : PDE.Vec n}
    (hf : ContDiffAt ℝ 2 f p) (v : PDE.Vec n) (j : Fin n) :
    fderiv ℝ ((PDE.classicalGradient f)) p v j =
      fderiv ℝ (fun y => fderiv ℝ f y (PDE.basisVec j)) p v := by
  have hd : ∀ j', DifferentiableAt ℝ (fun y => fderiv ℝ f y (PDE.basisVec j')) p := fun j' =>
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have := fderiv_pi    hd
  have h2 : ((PDE.classicalGradient f)) = fun y j' => fderiv ℝ f y (PDE.basisVec j') :=
    rfl
  rw [h2, this]
  rfl

variable (hU : ContDiffAt ℝ 2 (u ∘ evolutionHomeomorph n) x) (i j : Fin n)

include hU in
/-- The position Hessian of the kinetic pullback is the `∂_{v_i} ∂_{v_j}` Hessian. -/
theorem diffusedHessian_comp  :
    diffusedHessian u (evolutionHomeomorph n x) i j =
      fderiv ℝ (fun y => fderiv ℝ (u ∘ evolutionHomeomorph n) y (basisV j)) x (basisV i) := by
  let sharedTerm_29eb4e15f6 := ((fun y => u ⟨timeCoord n x, y, transportedCoord n x⟩))
  have hS : (sharedTerm_29eb4e15f6) =
      fun y => (u ∘ evolutionHomeomorph n) (x + embedDiffused n (y - diffusedCoord n x)) :=
    funext (slice_position x)

  rw [diffusedHessian_apply]
  simp only [time_evolutionHomeomorph, position_evolutionHomeomorph,
    velocity_evolutionHomeomorph, kineticPositionGradient]
  rw [fderiv_classicalGradient_apply (show ContDiffAt ℝ 2 sharedTerm_29eb4e15f6
      (diffusedCoord n x) by
      rw [hS]
      exact contDiffAt_comp_affine (embedDiffused n) x (diffusedCoord n x) hU)]
  rw [hS]
  have := fderiv_fderiv_comp_affine (embedDiffused n) x (diffusedCoord n x) hU
    (PDE.basisVec i) (PDE.basisVec j)
  exact this

include hU in
/-- The velocity Hessian of the kinetic pullback is the `∂_{z_i} ∂_{z_j}` Hessian. -/
theorem kineticVelocityHessian_comp  :
    kineticVelocityHessian u (evolutionHomeomorph n x) i j =
      fderiv ℝ (fun y => fderiv ℝ (u ∘ evolutionHomeomorph n) y (basisZ j)) x (basisZ i) := by
  let sharedTerm_de1505fd18 := ((fun y => u ⟨timeCoord n x, diffusedCoord n x, y⟩))
  have hS : (sharedTerm_de1505fd18) =
      fun y => (u ∘ evolutionHomeomorph n) (x + embedTransported n (y - transportedCoord n x)) :=
    funext (slice_velocity x)

  unfold kineticVelocityHessian
  simp only [time_evolutionHomeomorph, position_evolutionHomeomorph,
    velocity_evolutionHomeomorph]
  rw [fderiv_classicalGradient_apply (show ContDiffAt ℝ 2 sharedTerm_de1505fd18
      (transportedCoord n x) by
      rw [hS]
      exact contDiffAt_comp_affine (embedTransported n) x (transportedCoord n x) hU), hS]
  exact fderiv_fderiv_comp_affine (embedTransported n) x (transportedCoord n x) hU
    (PDE.basisVec i) (PDE.basisVec j)

end Surfaces

/-! ### The operators -/

variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}

variable {u : KineticPoint n → ℝ} {x : EvolutionVec n}

/-- **Coordinate bridge for `Lop`.**  For `u : KineticPoint n → ℝ` whose packed pullback
`u ∘ evolutionHomeomorph n` is `C²` at `x`, the packed operator `transportedOperator` of the
Hörmander bracket files agrees with the project's `transportedForwardOperator` at the kinetic
point `⟨σ, v, z⟩` of `x`. -/
theorem transportedOperator_comp
    (hU : ContDiffAt ℝ 2 (u ∘ evolutionHomeomorph n) x) :
    transportedOperator B b (u ∘ evolutionHomeomorph n) x =
      transportedForwardOperator B b u (evolutionHomeomorph n x) := by
  have hd  :=
    hU.differentiableAt (by norm_num)
  rw [transportedForwardOperator_apply, kineticTimeDerivative_comp hd, transportedOperator]
  congr 1
  congr 1
  · unfold matrixContraction
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [diffusedHessian_comp hU i j]
    rfl
  · simp_all [PDE.vecDot, kineticVelocityGradient_comp]

/-- **Coordinate bridge for `L_ε = Lop + ε Δ_z`.** -/
theorem regularizedOperator_comp  (ε : ℝ)
    (hU : ContDiffAt ℝ 2 (u ∘ evolutionHomeomorph n) x) :
    regularizedOperator B b ε (u ∘ evolutionHomeomorph n) x =
      transportedForwardOperator B b u (evolutionHomeomorph n x) +
        ε * ∑ l, kineticVelocityHessian u (evolutionHomeomorph n x) l l := by
  simp_all [regularizedOperator, transportedOperator_comp, kineticVelocityHessian_comp]

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
