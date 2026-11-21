module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.GoodPrimeBounds
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.BadPrimeBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.EulerProductAux

noncomputable section

open DedekindZetaZeroFree
open scoped NumberField Classical

set_option autoImplicit false

section MultiVitali

open Filter Topology Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_fderiv_le_of_bound {G : E → ℂ} {y : E} {r M : ℝ} (hr : 0 < r)
    (hd : ∀ z ∈ closedBall y r, DifferentiableAt ℂ G z)
    (hb : ∀ z ∈ closedBall y r, ‖G z‖ ≤ M) : ‖fderiv ℂ G y‖ ≤ M / r := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb y (mem_closedBall_self hr.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM hr.le) fun h => ?_
  by_cases h0 : h = 0
  · simp [h0]
  have hh : 0 < ‖h‖ := norm_pos_iff.mpr h0
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = r / ‖h‖ := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; exact div_pos hr hh
  have hcr : c * ‖h‖ = r := by rw [hc]; exact div_mul_cancel₀ _ hh.ne'
  obtain ⟨v, hv⟩ : ∃ v : E, v = (c : ℂ) • h := ⟨_, rfl⟩
  have hmem : ∀ t : ℂ, ‖t‖ ≤ 1 → y + t • v ∈ closedBall y r := by
    intro t ht
    rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_smul, hv, norm_smul,
      Complex.norm_real, Real.norm_of_nonneg hcpos.le, hcr]
    calc ‖t‖ * r ≤ 1 * r := mul_le_mul_of_nonneg_right ht hr.le
      _ = r := one_mul r
  have haff : ∀ t : ℂ, HasDerivAt (fun t : ℂ => y + t • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  have hGy : HasFDerivAt G (fderiv ℂ G y) (y + (0 : ℂ) • v) := by
    rw [zero_smul, add_zero]
    exact (hd y (mem_closedBall_self hr.le)).hasFDerivAt
  have hderiv : HasDerivAt (fun t : ℂ => G (y + t • v)) (fderiv ℂ G y v) 0 :=
    hGy.comp_hasDerivAt (0 : ℂ) (haff 0)
  have hdφ : DifferentiableOn ℂ (fun t : ℂ => G (y + t • v)) (closedBall 0 1) := by
    intro t ht
    have ht' : ‖t‖ ≤ 1 := by simpa using ht
    have h1 : HasFDerivAt G (fderiv ℂ G (y + t • v)) (y + t • v) :=
      (hd _ (hmem t ht')).hasFDerivAt
    exact (h1.comp_hasDerivAt t (haff t)).differentiableAt.differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun t : ℂ => G (y + t • v)) (Metric.ball 0 1) :=
    ⟨hdφ.mono ball_subset_closedBall,
      hdφ.continuousOn.mono (closure_ball (0 : ℂ) one_ne_zero).subset⟩
  have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := (0 : ℂ)) (R := 1)
    one_pos hdc (C := M) (fun t ht => hb _ (hmem t (by simpa using ht.le)))
  rw [hderiv.deriv, div_one, hv, map_smul, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg hcpos.le] at hest
  rw [div_mul_eq_mul_div, le_div_iff₀ hr]
  have := mul_le_mul_of_nonneg_right hest hh.le
  calc ‖fderiv ℂ G y h‖ * r = c * ‖fderiv ℂ G y h‖ * ‖h‖ := by rw [← hcr]; ring
    _ ≤ M * ‖h‖ := this

theorem differentiableOn_of_tendstoLocallyUniformlyOn [ProperSpace E] {ι : Type*}
    [SemilatticeSup ι] [Nonempty ι]
    {F : ι → E → ℂ} {f : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hf : TendstoLocallyUniformlyOn F f atTop U) (hF : ∀ n, DifferentiableOn ℂ (F n) U) :
    DifferentiableOn ℂ f U := by
  intro x hx
  obtain ⟨r, hr, hsub⟩ : ∃ r : ℝ, 0 < r ∧ closedBall x (2 * r) ⊆ U := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
    exact ⟨ε / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hball⟩
  have hK : TendstoUniformlyOn F f atTop (closedBall x (2 * r)) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hf _ hsub
      (isCompact_closedBall x (2 * r))
  have hKc := Metric.uniformCauchySeqOn_iff.mp hK.uniformCauchySeqOn
  have hFd : ∀ n, ∀ z ∈ closedBall x (2 * r), DifferentiableAt ℂ (F n) z :=
    fun n z hz => (hF n).differentiableAt (hU.mem_nhds (hsub hz))
  have hcauchy : UniformCauchySeqOn (fun n => fderiv ℂ (F n)) atTop (Metric.ball x r) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hKc (ε * r / 2) (by positivity)
    refine ⟨N, fun m hm n hn y hy => ?_⟩
    have hyr : closedBall y r ⊆ closedBall x (2 * r) := by
      intro z hz
      rw [mem_closedBall_iff_norm] at hz ⊢
      have hy' : ‖y - x‖ < r := mem_ball_iff_norm.mp hy
      calc ‖z - x‖ = ‖(z - y) + (y - x)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖z - y‖ + ‖y - x‖ := norm_add_le _ _
        _ ≤ 2 * r := by linarith
    have hdm : ∀ z ∈ closedBall y r, DifferentiableAt ℂ (fun z => F m z - F n z) z :=
      fun z hz => (hFd m z (hyr hz)).sub (hFd n z (hyr hz))
    have hest := norm_fderiv_le_of_bound (G := fun z => F m z - F n z) (y := y) (r := r)
      (M := ε * r / 2) hr hdm (fun z hz => by
        have := hN m hm n hn z (hyr hz)
        rw [dist_eq_norm] at this
        exact this.le)
    have hy0 : y ∈ closedBall y r := mem_closedBall_self hr.le
    have heq : fderiv ℂ (fun z => F m z - F n z) y = fderiv ℂ (F m) y - fderiv ℂ (F n) y :=
      ((hFd m y (hyr hy0)).hasFDerivAt.sub (hFd n y (hyr hy0)).hasFDerivAt).fderiv
    rw [heq] at hest
    rw [dist_eq_norm]
    have : ε * r / 2 / r = ε / 2 := by field_simp
    rw [this] at hest
    linarith
  have hex : ∀ y ∈ Metric.ball x r, ∃ a, Tendsto (fun n => fderiv ℂ (F n) y) atTop (𝓝 a) :=
    fun y hy => cauchySeq_tendsto_of_complete (hcauchy.cauchySeq hy)
  choose! g' hg' using hex
  have hlim := hcauchy.tendstoUniformlyOn_of_tendsto hg'
  have hder := hasFDerivAt_of_tendstoUniformlyOn (f := F) (g := f) isOpen_ball hlim
    (fun n y hy => (hFd n y (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith)) hy)).hasFDerivAt)
    (fun y hy => hf.tendsto_at (hsub (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith)) hy)))
    (mem_ball_self hr)
  exact hder.differentiableAt.differentiableWithinAt

theorem diffOn_finsetProd {ι : Type*} (s : Finset ι) {G : ι → E → ℂ} {U : Set E}
    (h : ∀ i ∈ s, DifferentiableOn ℂ (G i) U) :
    DifferentiableOn ℂ (fun x => ∏ i ∈ s, G i x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end MultiVitali
end
end DedekindZetaZeroFree.Quantitative.EulerProductAux

namespace DedekindZetaZeroFree.Quantitative.EulerDomain

noncomputable section

open DedekindZetaZeroFree NumberField CorrectionFactors LocalFiniteSums
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem OmegaStar_isOpen : IsOpen OmegaStar := EulerGeometry.OmegaStar_isOpen

abbrev correctionFactor (U : AllRowEuler.InitialSeparation.RawFrequency D.recipe.A) (p : ExteriorPrime D.recipe.A)
    (x : Coordinates) : ℂ := AllRowEuler.InitialSeparation.localCorrection D.context U p x.1 x.2.1 x.2.2

private theorem factor_differentiableOn (U : AllRowEuler.InitialSeparation.RawFrequency D.recipe.A)
    (p : ExteriorPrime D.recipe.A) : DifferentiableOn ℂ (correctionFactor D U p) OmegaStar := by
  unfold correctionFactor AllRowEuler.InitialSeparation.localCorrection
  by_cases h : (U.j p).val = 0
  · simp only [h, if_true]
    apply goodFactor_differentiableOn
    intro x hx
    obtain ⟨hξ, hw, hz, _, _, _, _, he, _⟩ := hx
    exact ⟨by linarith, hw, hξ, by linarith⟩
  · simpa only [if_neg h] using
      EulerBadPrime.badFactor_differentiableOn D.context p (U.j p) h (U.theta D.context p)

private theorem factor_hasProdUniformlyOn (U : AllRowEuler.InitialSeparation.RawFrequency D.recipe.A) (K : Set Coordinates)
    (hK : IsCompact K) (hKO : K ⊆ OmegaStar) :
    HasProdUniformlyOn (correctionFactor D U) (fun x => ∏' p, correctionFactor D U p x) K := by
  obtain ⟨δ, hδ, hKm⟩ := EulerBadPrime.exists_margin_of_compact K hK hKO
  obtain ⟨M, _, hbound⟩ := EulerGoodPrime.goodFactor_sub_one_le
    (A := D.recipe.A) (σ := D.recipe.σ) (η := D.recipe.target) (hS := D.recipe.traceBad) δ hδ
  have hb : ∀ᶠ p : ExteriorPrime D.recipe.A in Filter.cofinite,
      ∀ x ∈ K, ‖correctionFactor D U p x - 1‖ ≤ M * Q p ^ (-(1 + δ)) := by
    filter_upwards [U.eventually_j_eq_zero] with p h x hx
    simpa only [correctionFactor, AllRowEuler.InitialSeparation.localCorrection, ite_eq_left h,
      show -(1 + δ) = -1 - δ by ring] using
      hbound D.context p U.u x (hKm hx)
  have hs := exterior_norm_majorant_summable (A := D.recipe.A) M (1 + δ) (by linarith)
  simpa using hs.hasProdUniformlyOn_one_add hK hb
        (fun p => ((factor_differentiableOn D U p).continuousOn.mono hKO).sub continuousOn_const)

theorem correctionProduct_normal_convergence (U : AllRowEuler.InitialSeparation.RawFrequency D.recipe.A) :
    (∀ x ∈ OmegaStar, Multipliable (fun p => correctionFactor D U p x)) ∧
    HasProdLocallyUniformlyOn (correctionFactor D U) (fun x => ∏' p, correctionFactor D U p x) OmegaStar ∧
    DifferentiableOn ℂ (fun x => AllRowEuler.InitialSeparation.correctionProduct D.context U x.1 x.2.1 x.2.2) OmegaStar := by
  have hl := hasProdLocallyUniformlyOn_of_forall_compact OmegaStar_isOpen
    (fun K hKO hK => factor_hasProdUniformlyOn D U K hK hKO)
  refine ⟨fun x hx => ?_, hl, ?_⟩
  · exact ((factor_hasProdUniformlyOn D U {x} isCompact_singleton
      (Set.singleton_subset_iff.mpr hx)).hasProd (Set.mem_singleton x)).multipliable
  · exact EulerProductAux.differentiableOn_of_tendstoLocallyUniformlyOn OmegaStar_isOpen hl
      (fun I => EulerProductAux.diffOn_finsetProd I fun p _ => factor_differentiableOn D U p)

theorem Hu_normal_convergence (u : D.Row) :
    OmegaStar ⊆
      {p : Coordinates | Multipliable (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A =>
        CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2)} ∧
    HasProdLocallyUniformlyOn
      (fun (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (p : Coordinates) =>
        CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2)
      (fun p : Coordinates =>
        ∏' pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
          CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2) OmegaStar ∧
    DifferentiableOn ℂ
      (fun p : Coordinates =>
        ∏' pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
          CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2) OmegaStar ∧
    (∀ p ∈ OmegaStar ∩ CorrectionFactors.Omega,
      ∀ h : Multipliable (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A =>
        CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2),
        CorrectionFactors.H_u D.context u.toFrequency p.1 p.2.1 p.2.2 h =
          ∏' pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
            CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2) := by
  obtain ⟨hm, hl, hd⟩ := correctionProduct_normal_convergence D u.toFrequency.toRaw
  exact ⟨hm, hl, hd, fun _ _ _ => rfl⟩

end
end DedekindZetaZeroFree.Quantitative.EulerDomain
