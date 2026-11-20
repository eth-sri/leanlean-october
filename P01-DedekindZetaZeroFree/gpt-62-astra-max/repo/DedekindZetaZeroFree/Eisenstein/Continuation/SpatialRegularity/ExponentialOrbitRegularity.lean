module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.TranslatedBigCellCoordinates

@[expose] public section

noncomputable section
open MeasureTheory
open scoped NumberField Classical Topology Matrix.Norms.Operator
namespace DedekindZetaZeroFree.KPSpatialNativeExponentialOrbit
open KPGlobalResidualConstruction KPLiteralChamber

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def expMatrix (a : KPSmoothActualFlowData.LieCoordinates F)
    (v : NumberField.InfinitePlace F) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KPSmoothActualFlowData.matrixExponential (KPSmoothActualFlowData.sl2Matrix (fun j => a (v,j)))

local notation "Mat₂ℂ" => Matrix (Fin 2) (Fin 2) ℂ

private theorem expMatrix_smooth (v : NumberField.InfinitePlace F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a => (expMatrix F a v).val) := by
  letI : NormedAddCommGroup Mat₂ℂ := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ Mat₂ℂ := Matrix.linftyOpNormedSpace
  letI : NormedRing Mat₂ℂ := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ Mat₂ℂ := Matrix.linftyOpNormedAlgebra
  let L : KPSmoothActualFlowData.LieCoordinates F →ₗ[ℝ] Mat₂ℂ :=
    { toFun := fun a => KPSmoothActualFlowData.sl2Matrix (fun j => a (v,j))
      map_add' := by intros; ext i j; fin_cases i <;> fin_cases j <;>
        simp [KPSmoothActualFlowData.sl2Matrix]; all_goals ring
      map_smul' := by intros; ext i j; fin_cases i <;> fin_cases j <;>
        simp [KPSmoothActualFlowData.sl2Matrix]; all_goals ring }
  exact ((show AnalyticOnNhd ℝ NormedSpace.exp Set.univ from
    fun _ _ => NormedSpace.exp_analytic _).contDiff).comp L.toContinuousLinearMap.contDiff

 def relativeMatrix (a₀ a : KPSmoothActualFlowData.LieCoordinates F)
    (v : NumberField.InfinitePlace F) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  (expMatrix F a₀ v)⁻¹ * expMatrix F a v

theorem exponential_native_local_transition
    (a₀ : KPSmoothActualFlowData.LieCoordinates F) :
    ∃ (O : Set (KPSmoothActualFlowData.LieCoordinates F))
      (q : KPSmoothActualFlowData.LieCoordinates F → ArchCoordinates F),
      IsOpen O ∧ a₀ ∈ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) q O ∧
      Set.MapsTo q O (archDomain F) ∧
      ∀ a ∈ O, KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.exponential F a) =
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPSmoothActualFlowData.exponential F a₀) * archChart F ζ hζ (q a) := by
  let m := relativeMatrix F a₀
  have hm (v : NumberField.InfinitePlace F) : ContDiff ℝ (⊤ : ℕ∞) (fun a => (m a v).val) := contDiff_const.mul (expMatrix_smooth F v)
  have hentry (v : NumberField.InfinitePlace F) (i j : Fin 2) :
      ContDiff ℝ (⊤ : ℕ∞) (fun a => (m a v).val i j) := by
    let ev : Mat₂ℂ →ₗ[ℝ] ℂ :=
      { toFun := fun M => M i j, map_add' := by intros; rfl, map_smul' := by intros; rfl }
    exact ev.toContinuousLinearMap.contDiff.comp (hm v)
  let O := {a | ∀ v, (m a v).val 1 1 ≠ 0}
  let q := fun a v =>
    rightCoordinates (m a v).val
  have hO : IsOpen O := by
    have he : O = ⋂ v : NumberField.InfinitePlace F, {a | (m a v).val 1 1 ≠ 0} := by
      ext a; simp [O]
    rw [he]
    exact isOpen_iInter_of_finite fun v => isOpen_ne_fun (hentry v 1 1).continuous continuous_const
  have hbase : a₀ ∈ O := by simp [O,m,relativeMatrix]
  refine ⟨O,q,hO,hbase,?_,?_,?_⟩
  · apply contDiffOn_pi.mpr; intro v
    apply contDiffOn_pi.mpr; intro i
    have hc (i j : Fin 2) := (hentry v i j).contDiffOn (s := O)
    have hn : ∀ a ∈ O, (m a v).val 1 1 ≠ 0 := fun a ha => ha v
    have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fun a => (m a v).val.det) O := by
      simp only [Matrix.det_fin_two]
      exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))
    fin_cases i <;> simp only [q,rightCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    · simpa using! (hc 0 1).mul ((hc 1 1).inv hn)
    · simpa using! hd.mul
        (((hc 1 1).pow 2).inv (fun a ha => pow_ne_zero _ (hn a ha)))
    · simpa using! (hc 1 0).mul ((hc 1 1).inv hn)
  · intro a ha v
    exact div_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero _) (pow_ne_zero _ (ha v))
  · intro a ha
    rw [right_insertion, ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
    congr 1
    funext v
    change Matrix.ProjGenLinGroup.mk (expMatrix F a v) =
      Matrix.ProjGenLinGroup.mk (expMatrix F a₀ v) *
        Matrix.ProjGenLinGroup.mk (rightMatrix (rightCoordinates (m a v).val))
    rw [rightCoordinates_reconstruct (m a v) (ha v)]
    rw [← map_mul]
    simp [m,relativeMatrix]

theorem native_exponential_contDiff (u : G F ζ hζ → ℂ)
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F)) (g : G F ζ hζ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a => u (g *
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.exponential F a))) := by
  apply contDiff_iff_contDiffAt.mpr
  intro a₀
  obtain ⟨O,q,hO,ha₀,hq,hqd,he⟩ := exponential_native_local_transition F ζ hζ a₀
  apply (((hu (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPSmoothActualFlowData.exponential F a₀))).comp hq hqd).contDiffAt (hO.mem_nhds ha₀)).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds ha₀] with a ha
  dsimp only [Function.comp_def]
  rw [he a ha, mul_assoc]

end DedekindZetaZeroFree.KPSpatialNativeExponentialOrbit

end
