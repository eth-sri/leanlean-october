module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.Transport
public import RequestProject.Unitarity

/-!
# Change of base point and translation of the boundary curve (Lemma 10.3)

For a periodic coefficient, the solution of the linear Volterra equation can be continued
over a second period by `W(θ + L) = W(θ) W(L)`.  Consequently, starting the evolution at
the parameter `t` instead of `0` replaces the endpoint value `V = W(L)` by the conjugate
`W(t) V W(t)⁻¹`.  For the boundary transport this is the "cyclic change of base point" part
of Lemma 10.3 (and of Lemma 4.5) of the paper; translations of the curve do not change the
transport at all.  As a consequence `‖U_E - I‖` does not depend on the base point.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace PolyaNeumann

variable {A : Type*} [NormedRing A]
variable {C : ℝ → A} {M L : ℝ} {W : ℝ → A}

/-- The continuation of a solution over a second period. -/
def volterraExt (W : ℝ → A) L θ  :=
  if θ ≤ L then W θ else W (θ - L) * W L

lemma volterraExt_of_le  (h : θ ≤ L) : volterraExt W L θ = W θ := if_pos h

lemma volterraExt_of_ge (hW0 : W 0 = 1)  (h : L ≤ θ) :
    volterraExt W L θ = W (θ - L) * W L := by
  grind only [volterraExt]

lemma volterraExt_continuousOn (hL : 0 ≤ L) (hW : ContinuousOn W (Icc 0 L)) (hW0 : W 0 = 1) :
    ContinuousOn (volterraExt W L) (Icc 0 (2 * L)) := by
  have hU : Icc 0 (2 * L) = Icc 0 L ∪ Icc L (2 * L) := (Icc_union_Icc_eq_Icc hL (by linarith)).symm
  rw [hU]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
  · exact hW.congr fun θ hθ => volterraExt_of_le hθ.2
  · refine ContinuousOn.congr (f := fun θ => W (θ - L) * W L) ?_
      fun θ hθ => volterraExt_of_ge hW0 hθ.1
    refine ContinuousOn.mul ?_ continuousOn_const
    refine hW.comp (continuousOn_id.sub continuousOn_const) fun θ hθ => ?_
    grind

variable [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Integrals commute with right multiplication by a constant. -/
lemma intervalIntegral_mul_const_right  
    (hf : IntervalIntegrable f volume a b) (c : A) :
    ∫ s in a..b, f s * c = (∫ s in a..b, f s) * c :=
  ((ContinuousLinearMap.mul ℝ A).flip c).intervalIntegral_comp_comm hf

section
variable (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M) (hper : Function.Periodic C L)
include hC hM hper

/-- For a periodic coefficient, the continued solution solves the Volterra equation on two
periods. -/
theorem volterraExt_eq (hL : 0 ≤ L) (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s) :
    ∀ θ ∈ Icc 0 (2 * L), volterraExt W L θ = 1 + ∫ s in (0 : ℝ)..θ, C s * volterraExt W L s := by
  have hW0 : W 0 = 1 := by simpa using eW 0 ⟨le_rfl, hL⟩
  have hExt := volterraExt_continuousOn hL hW hW0
  have hInt : ∀ θ ∈ Icc 0 L, ∫ s in (0 : ℝ)..θ, C s * volterraExt W L s =
      ∫ s in (0 : ℝ)..θ, C s * W s := by
    intro θ hθ
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hθ.1] at hs
    grind [volterraExt_of_le, PolyaNeumann.volterraExt]
  intro θ hθ
  rcases le_or_gt θ L with h | h
  · grind [volterraExt_of_le, PolyaNeumann.volterraExt]
  · have hLmem : L ∈ Icc 0 (2 * L) := ⟨hL, by linarith⟩
    have i1 := intervalIntegrable_mul_of_continuousOn hC hM hExt hLmem
    have i2 := intervalIntegrable_mul_of_continuousOn hC hM hExt hθ
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 (i1.symm.trans i2),
      hInt L ⟨hL, le_rfl⟩, ← sub_eq_iff_eq_add'.mpr (eW L ⟨hL, le_rfl⟩)]
    have hθL : θ - L ∈ Icc 0 L := ⟨by linarith, by linarith [hθ.2]⟩
    have i3 := intervalIntegrable_mul_of_continuousOn hC hM hW hθL
    have e2 : ∫ s in L..θ, C s * volterraExt W L s =
        ∫ s in L..θ, (C (s - L) * W (s - L)) * W L := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le h.le] at hs
      rw [volterraExt_of_ge hW0 hs.1, hper.sub_eq s, mul_assoc]
    have i4 : IntervalIntegrable (fun s => C (s - L) * W (s - L)) volume L θ := by
      have := i3.comp_sub_right L
      simpa using this
    rw [e2, intervalIntegral_mul_const_right i4,
      intervalIntegral.integral_comp_sub_right (fun s => C s * W s) L, sub_self,
      ← sub_eq_iff_eq_add'.mpr (eW (θ - L) hθL), volterraExt_of_ge hW0 h.le]
    noncomm_ring

/-- **Change of base point** for a periodic linear Volterra equation: if `W` solves the
equation on `[0, L]` and `W'` solves the equation with the shifted coefficient
`s ↦ C (s + t)`, `t ∈ [0, L]`, and `W(t)` has a right inverse `Winv`, then
`W'(L) = W(t) W(L) Winv`. -/
theorem volterra_basepoint (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s)
     (ht : t ∈ Icc 0 L)  (hinv : W t * Winv = 1) 
    (hW' : ContinuousOn W' (Icc 0 L))
    (eW' : ∀ θ ∈ Icc 0 L, W' θ = 1 + ∫ s in (0 : ℝ)..θ, C (s + t) * W' s) :
    W' L = W t * W L * Winv := by
  have hL  := ht.1.trans ht.2
  have hW0 : W 0 = 1 := by simpa using eW 0 ⟨le_rfl, hL⟩
  have hXc := volterraExt_continuousOn hL hW hW0
  have eX := volterraExt_eq hC hM hper hL hW eW
  have hCt  :=
    hC.comp_measurePreserving (measurePreserving_add_right volume t)
  have hMt  := fun s => hM (s + t)
  set Z : ℝ → A := fun θ => volterraExt W L (θ + t) * Winv with hZ
  have hZc : ContinuousOn Z (Icc 0 L) := by
    refine ContinuousOn.mul ?_ continuousOn_const
    refine hXc.comp (continuousOn_id.add continuousOn_const) fun θ hθ => ?_
    grind
  have eZ : ∀ θ ∈ Icc 0 L, Z θ = 1 + ∫ s in (0 : ℝ)..θ, C (s + t) * Z s := by
    intro θ hθ
    have htm : t ∈ Icc 0 (2 * L) := ⟨ht.1, by linarith [ht.2]⟩
    have hθt : θ + t ∈ Icc 0 (2 * L) := ⟨by linarith [hθ.1, ht.1], by linarith [hθ.2, ht.2]⟩
    have i1 := intervalIntegrable_mul_of_continuousOn hC hM hXc htm
    have i2 := intervalIntegrable_mul_of_continuousOn hC hM hXc hθt
    have i3 : IntervalIntegrable (fun s => C (s + t) * volterraExt W L (s + t)) volume 0 θ := by
      have := (i1.symm.trans i2).comp_add_right t
      simpa using this
    have e1 : volterraExt W L (θ + t) = W t + ∫ s in (0 : ℝ)..θ, C (s + t) * volterraExt W L (s + t) := by
      rw [eX _ hθt, ← intervalIntegral.integral_add_adjacent_intervals i1 (i1.symm.trans i2),
        intervalIntegral.integral_comp_add_right (fun s => C s * volterraExt W L s) t, zero_add, ← add_assoc,
        ← eX t htm, volterraExt_of_le ht.2]
    simp only [hZ]
    rw [e1, add_mul, hinv, ← intervalIntegral_mul_const_right i3]
    simp only [mul_assoc]
  have := volterra_unique hCt hMt L hW' hZc eW' eZ ⟨hL, le_rfl⟩
  grind [volterraExt_of_ge]

end


/-! ### The boundary transport -/


/-- The transport coefficient is skew-adjoint: `C_E(θ)^* = -C_E(θ)`. -/
lemma transportCoeff_star γ E θ :
    star (transportCoeff γ E θ) = -transportCoeff γ E θ := by
  unfold transportCoeff
  rw [ContinuousLinearMap.star_eq_adjoint]
  simp only [map_smulₛₗ, map_add, ContinuousLinearMap.adjoint_adjoint, Complex.conj_conj]
  have hc : (starRingEnd ℂ) (-(Complex.I * (Real.sqrt E : ℂ)) / 2) =
      -(-(Complex.I * (Real.sqrt E : ℂ)) / 2) := by
    rw [map_div₀, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofNat]
    ring
  simp_all

/-- Shifting the parameter of the curve shifts the transport coefficient. -/
lemma transportCoeff_comp_add γ E t s :
    transportCoeff (fun θ => γ (θ + t)) E s = transportCoeff γ E (s + t) := by
  unfold transportCoeff
  rw [deriv_comp_add_const]

/-- The transport coefficient of a periodic curve is periodic. -/
lemma transportCoeff_periodic   (hper : Function.Periodic γ L) E :
    Function.Periodic (transportCoeff γ E) L := by
  intro s
  rw [← transportCoeff_comp_add]
  congr 1
  funext θ
  exact hper θ

section
variable {γ : ComplexCurve} {K } (hK : LipschitzWith K γ)
include γ K hK

/-- The values of the transport of a Lipschitz curve are unitary (Lemma 10.2). -/
lemma transport_mul_adjoint {E : ℝ}
    {W : ℝ → ComplexEnd Ell2} (hW : IsTransport γ E W) {t : ℝ} (ht : t ∈ boundaryInterval) :
    W t * ContinuousLinearMap.adjoint (W t) = 1 := by
  have := (volterra_unitary (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) (transportCoeff_star γ E) hW.1 hW.2 t ht).2
  assumption

/-- Lemma 10.3 (cyclic change of base point): if `W` is the transport of a periodic
Lipschitz curve `γ` and `W'` is the transport of the same curve started at the parameter
`t ∈ [0, L]`, then `V' = W(t) V W(t)^*`, where `V = W(L)`, `V' = W'(L)`. -/
theorem transport_basepoint
    (hper : Function.Periodic γ circlePeriod) {E : ℝ} {W : ℝ → ComplexEnd Ell2}
    (hW : IsTransport γ E W) {t : ℝ} (ht : t ∈ boundaryInterval) {W' : ℝ → ComplexEnd Ell2}
    (hW' : IsTransport (fun θ => γ (θ + t)) E W') :
    W' circlePeriod = W t * W circlePeriod * ContinuousLinearMap.adjoint (W t) := by
  refine volterra_basepoint (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) (transportCoeff_periodic hper E) hW.1 hW.2 ht
    (transport_mul_adjoint hK hW ht) hW'.1 fun θ hθ => ?_
  simp_rw [← transportCoeff_comp_add]
  exact hW'.2 θ hθ

/-- Lemma 10.3: a cyclic change of base point conjugates the monodromy by a unitary,
`U' = W(t) U W(t)^*`. -/
theorem monodromy_basepoint
    (hper : Function.Periodic γ circlePeriod) {E : ℝ} {W : ℝ → ComplexEnd Ell2}
    (hW : IsTransport γ E W) {t : ℝ} (ht : t ∈ boundaryInterval) {W' : ℝ → ComplexEnd Ell2}
    (hW' : IsTransport (fun θ => γ (θ + t)) E W') :
    monodromy W' = W t * monodromy W * ContinuousLinearMap.adjoint (W t) := by
  unfold monodromy
  rw [transport_basepoint hK hper hW ht hW', ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
    star_mul, star_mul, star_star, mul_assoc]

end


end PolyaNeumann

end
