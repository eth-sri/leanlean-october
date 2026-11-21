module

public import DedekindZetaZeroFree.Adeles.Approximation.ArchimedeanChartMultiplication
public import DedekindZetaZeroFree.Analysis.RightFrame.PullbackWords

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff Matrix Matrix.Norms.Operator
open Filter

/-! Right differentiation in the open archimedean product chart. -/
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.RightFlowChart

open NativeChartProduct (product)
open RightFrame.PullbackWords (directionalWord word_smooth)

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rightDerivative (b : KPSmoothActualFlowData.B F)
    (u : G F ζ hζ → ℂ) (g : G F ζ hζ) : ℂ :=
  deriv (fun t => u (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPSmoothActualFlowData.flow F b t))) 0

def word : List (KPSmoothActualFlowData.B F) → (G F ζ hζ → ℂ) → G F ζ hζ → ℂ
  | [], u => u
  | b :: w, u => rightDerivative F ζ hζ b (word w u)

theorem word_eq_foldr (w : List (KPSmoothActualFlowData.B F)) (u : G F ζ hζ → ℂ) :
    word F ζ hζ w u = w.foldr (rightDerivative F ζ hζ) u := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [word, List.foldr_cons, ih]

 def flowMatrix (b : KPSmoothActualFlowData.B F) (t : ℝ)
    (v : NumberField.InfinitePlace F) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KPSmoothActualFlowData.matrixExponential
    (KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = b then t else 0))
def theta (b : KPSmoothActualFlowData.B F) (t : ℝ) : ArchCoordinates F :=
  fun v => KPLiteralChamber.rightCoordinates (flowMatrix F b t v).val
private theorem flowMatrix_zero (b : KPSmoothActualFlowData.B F) (v : NumberField.InfinitePlace F) :
    flowMatrix F b 0 v = 1 := by
  apply Units.ext
  change (NormedSpace.exp _) = (1 : Matrix (Fin 2) (Fin 2) ℂ)
  rw [show KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = b then (0 : ℝ) else 0) = 0 by
    ext i j; fin_cases i <;> fin_cases j <;> simp [KPSmoothActualFlowData.sl2Matrix]]
  exact NormedSpace.exp_zero
theorem theta_zero (b : KPSmoothActualFlowData.B F) : theta F b 0 = archBase F := by
  funext v i
  rw [theta, flowMatrix_zero]
  fin_cases i <;> simp [KPLiteralChamber.rightCoordinates, archBase]
private theorem flowEntry_smooth (b : KPSmoothActualFlowData.B F)
    (v : NumberField.InfinitePlace F) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val i j) := by
  letI : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAlgebra
  let L : ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    { toFun := fun t => KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = b then t else 0)
      map_add' := by intro x y; ext i j; fin_cases i <;> fin_cases j <;>
        simp [KPSmoothActualFlowData.sl2Matrix]; all_goals split_ifs <;> simp <;> ring
      map_smul' := by intro x y; ext i j; fin_cases i <;> fin_cases j <;>
        simp [KPSmoothActualFlowData.sl2Matrix]; all_goals split_ifs <;> simp <;> ring }
  let ev : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have he : ContDiff ℝ (⊤ : ℕ∞) (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → _) :=
    (show AnalyticOnNhd ℝ (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → _) Set.univ from fun _ _ => NormedSpace.exp_analytic _).contDiff
  exact ev.toContinuousLinearMap.contDiff.comp (he.comp L.toContinuousLinearMap.contDiff)
theorem theta_smooth (b : KPSmoothActualFlowData.B F) :
    ContDiffAt ℝ (⊤ : ℕ∞) (theta F b) 0 := by
  apply contDiffAt_pi.mpr; intro v
  apply contDiffAt_pi.mpr; intro i
  have hc (i j : Fin 2) : ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val i j) 0 :=
    (flowEntry_smooth F b v i j).contDiffAt
  have hn : (flowMatrix F b 0 v).val 1 1 ≠ 0 := by rw [flowMatrix_zero]; simp
  fin_cases i <;> simp only [theta, KPLiteralChamber.rightCoordinates, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  · change ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val 0 1 / (flowMatrix F b t v).val 1 1) 0
    simpa only [div_eq_mul_inv] using! (hc 0 1).mul ((hc 1 1).inv hn)
  · change ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val.det / (flowMatrix F b t v).val 1 1 ^ 2) 0
    simp only [Matrix.det_fin_two]
    simpa only [div_eq_mul_inv] using! (((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))).mul
      (((hc 1 1).pow 2).inv (pow_ne_zero _ hn))
  · change ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val 1 0 / (flowMatrix F b t v).val 1 1) 0
    simpa only [div_eq_mul_inv] using! (hc 1 0).mul ((hc 1 1).inv hn)
theorem theta_chart (b : KPSmoothActualFlowData.B F) :
    ∀ᶠ t in nhds (0 : ℝ), KPGlobalResidualConstruction.archChart F ζ hζ (theta F b t) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t) := by
  have hn : ∀ᶠ t in nhds (0 : ℝ), ∀ v : NumberField.InfinitePlace F,
      (flowMatrix F b t v).val 1 1 ≠ 0 := by
    rw [Filter.eventually_all]
    intro v
    have hc : ContinuousAt (fun t => (flowMatrix F b t v).val 1 1) 0 :=
      (flowEntry_smooth F b v 1 1).continuous.continuousAt
    exact hc.eventually_ne (by rw [flowMatrix_zero]; simp)
  filter_upwards [hn] with t ht
  rw [KPLiteralChamber.right_insertion]
  congr 1
  funext v
  exact KPLiteralChamber.rightCoordinates_reconstruct (flowMatrix F b t v) (ht v)
private theorem product_base_right (x : ArchCoordinates F) :
    product F (x,archBase F) = x := by
  funext q i
  fin_cases i <;> simp [product, archBase]
def transport (b : KPSmoothActualFlowData.B F) (p : ArchCoordinates F × ℝ) : ArchCoordinates F :=
  product F (p.1, theta F b p.2)
def field (b : KPSmoothActualFlowData.B F) (x : ArchCoordinates F) : ArchCoordinates F :=
  fderiv ℝ (transport F b) (x,0) (0,1)
private theorem transport_zero (b : KPSmoothActualFlowData.B F) (x : ArchCoordinates F) :
    transport F b (x,0) = x := by
  simp [transport, theta_zero, product_base_right]
private theorem transport_smooth (b : KPSmoothActualFlowData.B F)
    (V : Set (ArchCoordinates F)) (hVo : IsOpen V) (hb : archBase F ∈ V)
    (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (product F) (V ×ˢ V)) (x : ArchCoordinates F) (hx : x ∈ V) :
    ContDiffAt ℝ (⊤ : ℕ∞) (transport F b) (x,0) := by
  have hpair : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ArchCoordinates F × ℝ => (p.1,theta F b p.2)) (x,0) :=
    contDiffAt_fst.prodMk ((theta_smooth F b).comp (x,0) contDiffAt_snd)
  exact (hμ.contDiffAt ((hVo.prod hVo).mem_nhds ⟨hx, by simpa [theta_zero] using hb⟩)).comp (x,0) hpair
theorem field_smooth (b : KPSmoothActualFlowData.B F)
    (V : Set (ArchCoordinates F)) (hVo : IsOpen V) (hb : archBase F ∈ V)
    (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (product F) (V ×ˢ V)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (field F b) V := by
  intro x hx
  have ht := transport_smooth F b V hVo hb hμ x hx
  have hd := (ht.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).comp x
    (contDiffAt_id.prodMk contDiffAt_const)
  exact (hd.clm_apply contDiffAt_const).contDiffWithinAt
private theorem transport_hasDeriv (b : KPSmoothActualFlowData.B F)
    (V : Set (ArchCoordinates F)) (hVo : IsOpen V) (hb : archBase F ∈ V)
    (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (product F) (V ×ˢ V)) (x : ArchCoordinates F) (hx : x ∈ V) :
    HasDerivAt (fun t => transport F b (x,t)) (field F b x) 0 := by
  have ht := (transport_smooth F b V hVo hb hμ x hx).differentiableAt (by simp)
  exact ht.hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_const 0 x).prodMk (hasDerivAt_id 0))

theorem word_in_chart
    (u : G F ζ hζ → ℂ)
    (V : Set (ArchCoordinates F)) (hVo : IsOpen V) (hb : archBase F ∈ V)
    (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (product F) (V ×ˢ V))
    (hprod : ∀ y ∈ V, ∀ x ∈ V, archChart F ζ hζ (product F (y,x)) =
      archChart F ζ hζ y * archChart F ζ hζ x)
    (w : List (KPSmoothActualFlowData.B F)) (g : G F ζ hζ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => u (g * archChart F ζ hζ y)) V) :
    ∀ x ∈ V,
      word F ζ hζ w u (g * archChart F ζ hζ x) =
      directionalWord (field F) w (fun y => u (g * archChart F ζ hζ y)) x := by
  have hf := fun b => field_smooth F b V hVo hb hμ
  induction w with
  | nil => intro x hx; rfl
  | cons b w ih =>
    intro x hx
    let u₀ := fun y => u (g * archChart F ζ hζ y)
    let q := directionalWord (field F) w u₀
    have hq : ContDiffOn ℝ (⊤ : ℕ∞) q V := word_smooth V hVo (field F) hf w u₀ hu
    have hqt := ((hq.contDiffAt (hVo.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have htr := transport_hasDeriv F b V hVo hb hμ x hx
    have htr0 := transport_zero F b x
    have hder : HasDerivAt (fun t => q (transport F b (x,t)))
        (fderiv ℝ q x (field F b x)) 0 := by
      have hh := (show HasFDerivAt q (fderiv ℝ q x) (transport F b (x,0)) from htr0.symm ▸ hqt).comp_hasDerivAt 0 htr
      simpa only [htr0, Function.comp_def] using! hh
    have he : (fun t : ℝ =>
        word F ζ hζ w u ((g * archChart F ζ hζ x) *
            KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t)))
        =ᶠ[nhds 0] (fun t => q (transport F b (x,t))) := by
      have htV : ∀ᶠ t in nhds (0 : ℝ), theta F b t ∈ V :=
        (theta_smooth F b).continuousAt.eventually (by simpa [theta_zero] using hVo.mem_nhds hb)
      have hpV : ∀ᶠ t in nhds (0 : ℝ), transport F b (x,t) ∈ V :=
        htr.continuousAt.eventually (by simpa only [htr0] using (show ∀ᶠ y in nhds x, y ∈ V from hVo.mem_nhds hx))
      filter_upwards [theta_chart F ζ hζ b, htV, hpV] with t ht htV hpV
      rw [← ht, mul_assoc, ← hprod x hx (theta F b t) htV]
      exact ih (transport F b (x,t)) hpV
    unfold word rightDerivative
    change deriv _ 0 = fderiv ℝ q x (field F b x)
    rw [he.deriv_eq]
    exact hder.deriv

theorem rightWord_hasDerivAt_of_chart_smooth
    (u : G F ζ hζ → ℂ)
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (w : List (KPSmoothActualFlowData.B F)) (b : KPSmoothActualFlowData.B F) (g : G F ζ hζ) :
    HasDerivAt (fun t : ℝ => word F ζ hζ w u
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F b t)))
      (word F ζ hζ (b :: w) u g) 0 := by
  obtain ⟨O, hOo, hb, hOD, hμ, hmaps, hprod, hthick, hcomm⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product F ζ hζ
  let q := directionalWord (field F) w (fun y => u (g * archChart F ζ hζ y))
  have hq : ContDiffOn ℝ (⊤ : ℕ∞) q O :=
    word_smooth O hOo (field F) (fun b => field_smooth F b O hOo hb hμ)
      w _ ((hu g).mono hOD)
  have hθ := theta_smooth F b
  have hθO : ∀ᶠ t in nhds (0 : ℝ), theta F b t ∈ O :=
    hθ.continuousAt.eventually (by simpa [theta_zero] using hOo.mem_nhds hb)
  have he : (fun t : ℝ => word F ζ hζ w u
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F b t))) =ᶠ[nhds 0]
      (fun t => q (theta F b t)) := by
    filter_upwards [theta_chart F ζ hζ b, hθO] with t ht htO
    rw [← ht]
    exact word_in_chart F ζ hζ u O hOo hb hμ hprod w g ((hu g).mono hOD) _ htO
  have hd : DifferentiableAt ℝ (fun t => q (theta F b t)) 0 := by
    exact (((hq.contDiffAt (by simpa [theta_zero] using hOo.mem_nhds hb)).comp 0 hθ).differentiableAt (by simp))
  have hd' := hd.congr_of_eventuallyEq he
  exact hd'.hasDerivAt

theorem word_add (u v : G F ζ hζ → ℂ)
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (hv : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => v (g * archChart F ζ hζ x)) (archDomain F))
    (w : List (KPSmoothActualFlowData.B F)) :
    word F ζ hζ w (u + v) = word F ζ hζ w u + word F ζ hζ w v := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    funext g
    unfold word rightDerivative
    simp only [ih, Pi.add_apply]
    exact ((rightWord_hasDerivAt_of_chart_smooth F ζ hζ u hu w b g).add
      (rightWord_hasDerivAt_of_chart_smooth F ζ hζ v hv w b g)).deriv

theorem word_smul (c : ℂ) (u : G F ζ hζ → ℂ)
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (w : List (KPSmoothActualFlowData.B F)) :
    word F ζ hζ w (c • u) = c • word F ζ hζ w u := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    funext g
    unfold word rightDerivative
    simp only [ih, Pi.smul_apply]
    exact ((rightWord_hasDerivAt_of_chart_smooth F ζ hζ u hu w b g).const_smul c).deriv

theorem rightWord_level
    (u : G F ζ hζ → ℂ)
    (a : G F ζ hζ)
    (ha : ∀ x, Commute (archChart F ζ hζ x) a)
    (hu : ∀ g, u (g*a) = u g) (w : List (KPSmoothActualFlowData.B F))
    (g : G F ζ hζ) :
    word F ζ hζ w u (g*a) = word F ζ hζ w u g := by
  induction w generalizing g with
  | nil => exact hu g
  | cons b w ih =>
    unfold word rightDerivative
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [theta_chart F ζ hζ b] with t ht
    rw [← ht, mul_assoc, (ha (theta F b t)).eq.symm, ← mul_assoc]
    exact ih _

theorem rightWord_continuous_of_chart_smooth
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (u : G F ζ hζ → ℂ)
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (hlevel : ∀ g, ∀ a : KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
      u (g*a.val) = u g) (w : List (KPSmoothActualFlowData.B F)) :
    Continuous (word F ζ hζ w u) := by
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨O, hOo, hb, hOD, hμ, hmaps, hprod, hthick, hcomm⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product F ζ hζ
  apply continuous_iff_continuousAt.mpr
  intro g
  let q := directionalWord (field F) w (fun y => u (g * archChart F ζ hζ y))
  have hq : ContDiffOn ℝ (⊤ : ℕ∞) q O :=
    word_smooth O hOo (field F) (fun b => field_smooth F b O hOo hb hμ)
      w _ ((hu g).mono hOD)
  have hbchart : archChart F ζ hζ (archBase F) = 1 := by
    rw [KPLiteralChamber.right_insertion]
    have hh : (fun v : NumberField.InfinitePlace F => Matrix.ProjGenLinGroup.mk
        (KPLiteralChamber.rightMatrix (archBase F v))) = 1 := by
      funext v
      have hm : KPLiteralChamber.rightMatrix (archBase F v) = 1 := by
        apply Units.ext
        rw [KPLiteralChamber.rightMatrix_val _ (by simp [archBase])]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [archBase]
      rw [hm, map_one]
      rfl
    rw [hh]
    exact (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1
  have hbase : q (archBase F) = word F ζ hζ w u g := by
    have hh := word_in_chart F ζ hζ u O hOo hb hμ hprod w g ((hu g).mono hOD) _ hb
    simpa only [hbchart, mul_one, word, q] using hh.symm
  apply tendsto_def.mpr
  intro N hN
  have hn : q ⁻¹' N ∈ nhds (archBase F) :=
    (hq.continuousOn.continuousAt (hOo.mem_nhds hb)).preimage_mem_nhds (hbase.symm ▸ hN)
  obtain ⟨W, hWN, hWo, hbW⟩ := mem_nhds_iff.mp (Filter.inter_mem hn (hOo.mem_nhds hb))
  have hWO : W ⊆ O := fun x hx => (hWN hx).2
  have hT := hthick W hWo hbW hWO U
  change ∀ᶠ y in nhds (1 : G F ζ hζ),
    ∃ x ∈ W, ∃ a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
      y = archChart F ζ hζ x * a at hT
  have hg : ∀ᶠ y in nhds g, ∃ x ∈ W,
      ∃ a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
        g⁻¹*y = archChart F ζ hζ x * a :=
    (show ContinuousAt (fun y : G F ζ hζ => g⁻¹*y) g from
      continuousAt_const.mul continuousAt_id).eventually (by simpa using hT)
  filter_upwards [hg] with y hy
  obtain ⟨x, hx, a, ha, he⟩ := hy
  have hy' : y = (g * archChart F ζ hζ x)*a := by
    calc y = g*(g⁻¹*y) := by simp
         _ = _ := by rw [he, mul_assoc]
  change word F ζ hζ w u y ∈ N
  rw [hy', rightWord_level F ζ hζ u a (fun x => hcomm U a ha x)
    (fun g => hlevel g ⟨a,ha⟩) w]
  change word F ζ hζ w u
    (g * archChart F ζ hζ x) ∈ N
  rw [word_in_chart F ζ hζ u O hOo hb hμ hprod w g ((hu g).mono hOD) x (hWO hx)]
  exact (hWN hx).1

end DedekindZetaZeroFree.KPGlobalResidualConstruction.RightFlowChart

end
