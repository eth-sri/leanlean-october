module

public import HypoellipticAleksandrov.Parabolic.SourceLocalHarnackEndpoint
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure

/-!
# Physical scaling for the source-aware local parabolic Harnack estimate

This module transports the normalized one-box estimate to every positive
physical radius, retaining its compact carrier and raw inhomogeneous source.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Set

variable {d : ℕ}

private def parabolicAffineHomeomorph
     (t0 : ℝ) (v0 : PDE.Vec d) (s : ℝ) (hs : 0 < s) :
    TimeVelocity d ≃ₜ TimeVelocity d where
  toEquiv :=
    { toFun := parabolicAffine t0 v0 s
      invFun := fun z ↦ ((z.1 - t0) / s ^ 2, s⁻¹ • (z.2 - v0))
      left_inv := by
        intro z
        apply Prod.ext
        · change (t0 + s ^ 2 * z.1 - t0) / s ^ 2 = z.1
          field_simp [hs.ne']; ring
        · ext i
          change s⁻¹ * (v0 i + s * z.2 i - v0 i) = z.2 i
          field_simp [hs.ne']; ring
      right_inv := by
        rintro ⟨t, v⟩
        apply Prod.ext
        · change t0 + s ^ 2 * ((t - t0) / s ^ 2) = t
          field_simp [hs.ne']; ring
        · ext i
          change v0 i + s * (s⁻¹ * (v i - v0 i)) = v i
          field_simp [hs.ne']; ring }
  continuous_toFun := (contDiff_infty_parabolicAffine t0 v0 s).continuous
  continuous_invFun := by
    fun_prop

section
variable {t0 s : ℝ} {v0 : PDE.Vec d} (hs : 0 < s)

include hs
private theorem isCompact_parabolicAffine_preimage

    {K : HypoellipticAleksandrov.Parabolic.Region d} (hK : IsCompact K) :
    IsCompact (parabolicAffine t0 v0 s ⁻¹' K) := (id ((Homeomorph.isCompact_preimage (parabolicAffineHomeomorph t0 v0 s hs)).mpr hK))

private theorem parabolicAffine_image_preimage_eq

    (K : HypoellipticAleksandrov.Parabolic.Region d) :
    parabolicAffine t0 v0 s '' (parabolicAffine t0 v0 s ⁻¹' K) = K := (id (image_preimage_eq K (Homeomorph.surjective (parabolicAffineHomeomorph t0 v0 s hs))))
end


section
variable {r : ℝ} {v v0 : PDE.Vec d} (hr : 0 < r)

include hr
private theorem normalized_target_velocity

    (hv : v ∈ velocityCube v0 (r / 2)) :
    (2 / r) • (v - v0) ∈ velocityCube (0 : PDE.Vec d) 1 := by
  intro i

  have hscale : 0 < 2 / r := div_pos (by norm_num) hr
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul, sub_zero]
  rw [abs_mul, abs_of_pos hscale]
  calc
    (2 / r) * |v i - v0 i| < (2 / r) * (r / 2) :=
      mul_lt_mul_of_pos_left (hv i) hscale
    _ = 1 := by field_simp [hr.ne']

private theorem physical_target_from_normalized_velocity
      :
    v0 + (r / 2) • ((2 / r) • (v - v0)) = v := by
  ext i
  change v0 i + (r / 2) * ((2 / r) * (v i - v0 i)) = v i
  field_simp [hr.ne']
  ring
end


/-- The normalized source-aware local Harnack estimate at every positive
physical radius, with the same constants and physical source norm. -/
theorem exists_source_local_parabolic_harnack
    (d : Nat) (hd : 1 <= d) (lam : Real) (hlam : 0 < lam)
    (Lam : Real) (hlamLam : lam <= Lam) :
    ∃ hBox C : Real, 0 < hBox ∧ hBox <= 1 ∧ 0 < C ∧
      ∀ (K U : HypoellipticAleksandrov.Parabolic.Region d) (B : CoefficientField d)
        (q F : TimeVelocity d -> Real) (t0 : Real) (v0 : PDE.Vec d) (r : Real),
        0 < r -> IsCompact K -> K ⊆ U -> IsOpen U ->
        parabolicClosedBox 2 r (t0 - r ^ 2) v0 ⊆ K ->
        IsContinuousCoefficientOn B U -> ContDiffOn Real 2 q U ->
        ContinuousOn F U -> IsNonnegativeOn q K ->
        HasLowerEllipticityOn lam B K -> HasUpperEllipticityOn Lam B K ->
        (∀ x ∈ K, parabolicOperator B q x = F x) ->
        ∀ v : PDE.Vec d, v ∈ velocityCube v0 (r / 2) ->
          hBox * q (t0, v0) <= q (t0 + r ^ 2, v) +
            C * r ^ ((d : Real) / ((d : Real) + 1)) *
              parabolicLpNormOn d F K := by
  let sharedTerm_867fef6c9e := (((d : Real) / ((d : Real) + 1)))
  obtain ⟨hBox, C, hhBox0, hhBox1, hC, hnormalized⟩ :=
    exists_source_local_parabolic_harnack_nonnegative d hd lam hlam Lam hlamLam
  refine ⟨hBox, C, hhBox0, hhBox1, hC, ?_⟩
  intro K U B q F t0 v0 r hr hK hKU hU hbox hB hq hF hnonneg hlower hupper heq v hv
  let s : ℝ := r / 2
  let a  := parabolicAffine (t0 - r ^ 2) v0 s
  let KHat  := a ⁻¹' K
  let UHat  := a ⁻¹' U

  let qHat  := pullbackScalar q (t0 - r ^ 2) v0 s
  let FHat  := fun z ↦ s ^ 2 * F (a z)
  have hs : 0 < s := by
    dsimp [s]
    linarith
  have hmapK : MapsTo a KHat K := mapsTo_preimage _ _
  have hmapU : MapsTo a UHat U := mapsTo_preimage _ _










  let w  := (2 / r) • (v - v0)

  have hphysical : v0 + (r / 2) • w = v := by
    exact physical_target_from_normalized_velocity hr

  have hnormalizedOut := hnormalized KHat UHat (pullbackCoefficient B (t0 - r ^ 2) v0 s) qHat FHat ((id (isCompact_parabolicAffine_preimage hs hK))) (Set.preimage_mono hKU) (by
      dsimp [UHat, a]
      exact hU.preimage (contDiff_infty_parabolicAffine (t0 - r ^ 2) v0 s).continuous) (by
          intro z hz
          change a z ∈ K
          apply hbox

          exact (show z ∈ parabolicAffine (t0 - r ^ 2) v0 (r / 2) ⁻¹'
              parabolicClosedBox 2 r (t0 - r ^ 2) v0 by
              rw [parabolicAffine_preimage_localHarnackClosedBox hr]
              exact hz))
    (hB.pullback hmapU) (ContDiffOn.pullbackScalar hq hmapU) (continuousOn_const.mul
          (hF.comp (contDiff_infty_parabolicAffine (t0 - r ^ 2) v0 s).continuous.continuousOn hmapU)) (hnonneg.pullbackScalar hmapK) (hlower.pullback hmapK) (hupper.pullback hmapK) (by
        intro z hz

        rw [parabolicOperator_pullbackScalar
          (contDiffAt_of_contDiffOn_of_isOpen hU hq (hmapU (by
              change a z ∈ U
              exact hKU (hmapK hz))))]
        change s ^ 2 * parabolicOperator B q (a z) = s ^ 2 * F (a z)
        rw [heq (a z) (hmapK hz)]) w (normalized_target_velocity hr hv)
  have hsource : qHat (4, (0 )) = q (t0, v0) := by
    dsimp [qHat, s]
    rw [parabolicAffine_localHarnack_source]
  have hterminal : qHat (8, w) = q (t0 + r ^ 2, v) := by
    dsimp [qHat, s]
    rw [parabolicAffine_localHarnack_terminal, hphysical]
  have hnorm : parabolicLpNormOn d FHat KHat =
      s ^ sharedTerm_867fef6c9e * parabolicLpNormOn d F K := by
    rw [parabolicLpNormOn_pullback (t0 - r ^ 2) v0 hs F KHat]
    rw [show parabolicAffine (t0 - r ^ 2) v0 s '' KHat = K by exact (id (parabolicAffine_image_preimage_eq hs K))]
  let p : ℝ := sharedTerm_867fef6c9e

  have hscale : s ^ p ≤ r ^ p := by
    exact Real.rpow_le_rpow hs.le (by dsimp [s]; linarith) (by
        dsimp [p]
        positivity)
  have hnormnonneg : 0 ≤ parabolicLpNormOn d F K := ENNReal.toReal_nonneg
  have herror : C * (s ^ p * parabolicLpNormOn d F K) ≤
      C * r ^ p * parabolicLpNormOn d F K := by
    calc
      C * (s ^ p * parabolicLpNormOn d F K) =
          C * s ^ p * parabolicLpNormOn d F K := by ring
      _ ≤ C * r ^ p * parabolicLpNormOn d F K := by
        gcongr
  calc
    hBox * q (t0, v0) = hBox * qHat (4, (0 )) := by rw [hsource]
    _ ≤ qHat (8, w) + C * parabolicLpNormOn d FHat KHat := hnormalizedOut
    _ = q (t0 + r ^ 2, v) + C * (s ^ p * parabolicLpNormOn d F K) := by
      rw [hterminal, hnorm]
    _ ≤ q (t0 + r ^ 2, v) + C * r ^ p * parabolicLpNormOn d F K := by
      linarith

end HypoellipticAleksandrov.Parabolic
