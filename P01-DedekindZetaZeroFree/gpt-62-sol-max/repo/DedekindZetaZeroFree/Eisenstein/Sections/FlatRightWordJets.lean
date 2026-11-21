module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSectionContinuityAndExponentialJets
public import DedekindZetaZeroFree.Eisenstein.Sections.FullProductFlatFamily
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions
public import DedekindZetaZeroFree.Adeles.Archimedean.RightFlowCharts

@[expose] public section

noncomputable section
open scoped Classical NumberField Matrix

namespace DedekindZetaZeroFree.KPContinuation.ChamberFlatSource
namespace ChartMatrix

open KPAdelicCoverRestrictedProduct
open NumberField

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

export KPLiteralChamber (diagonalUnit sectionTuple complexSectionHom)

def chartMatrix (x : Fin 3 → ℂ) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KubotaRankTwo.n ℂ (x 0) * KubotaRankTwo.d ℂ (diagonalUnit (x 1)) 1 *
    KPStandardLocalRootLifts.lowerN ℂ (x 2)

theorem chartMatrix_val (x : Fin 3 → ℂ) (hx : x 1 ≠ 0) :
    (chartMatrix x).val = !![x 1 + x 0 * x 2, x 0; x 2, 1] :=
  KPLiteralChamber.rightMatrix_val x hx

theorem archChart_eq_insertion_chartMatrix
    (x : KPGlobalResidualConstruction.ArchCoordinates F) :
    KPGlobalResidualConstruction.archChart F ζ hζ x =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (chartMatrix (x w))) :=
  KPLiteralChamber.right_insertion F ζ hζ x

end ChartMatrix
end DedekindZetaZeroFree.KPContinuation.ChamberFlatSource

end

section

noncomputable section
open scoped Classical NumberField BigOperators Topology ContDiff Matrix Matrix.Norms.Operator

namespace DedekindZetaZeroFree.KPContinuation.ChamberFlatSource

namespace ChartMatrix

open KPAdelicCoverRestrictedProduct
open NumberField

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def chartCoordinates (M : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℂ :=
  ![M 0 1 / M 1 1, M.det / (M 1 1) ^ 2, M 1 0 / M 1 1]

theorem chartCoordinates_nonzero (M : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hM : M.val 1 1 ≠ 0) : chartCoordinates M.val 1 ≠ 0 :=
  KPLiteralChamber.rightCoordinates_nonzero M hM

theorem chartCoordinates_reconstruct (M : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hM : M.val 1 1 ≠ 0) :
    Matrix.ProjGenLinGroup.mk (chartMatrix (chartCoordinates M.val)) =
      Matrix.ProjGenLinGroup.mk M :=
  KPLiteralChamber.rightCoordinates_reconstruct M hM

end ChartMatrix

open KPGlobalResidualConstruction
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open KPGlobalResidualConstruction.RightFlowChart
open RightFrame.PullbackWords (directionalWord word_smooth)

section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem variable_jet_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : E → ℂ) (n : ℕ) (d : Fin n → E → E)
    (x v : E) (hu : ContDiffAt ℝ (⊤ : ℕ∞) u x)
    (hd : ∀ i, DifferentiableAt ℝ (d i) x) :
    fderiv ℝ (fun y => iteratedFDeriv ℝ n u y (fun i => d i y)) x v =
      iteratedFDeriv ℝ (n+1) u x (Fin.cons v (fun i => d i x)) +
        ∑ i, iteratedFDeriv ℝ n u x (Function.update (fun i => d i x) i (fderiv ℝ (d i) x v)) := by
  have ht : DifferentiableAt ℝ (iteratedFDeriv ℝ n u) x :=
    (hu.iteratedFDeriv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  have hh := (ht.hasFDerivAt.continuousMultilinearMap_apply (fun i => (hd i).hasFDerivAt)).fderiv
  rw [hh]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousMultilinearMap.apply_apply, ContinuousLinearMap.sum_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply]
  rw [iteratedFDeriv_succ_apply_left]
  simp
private def directionJet (t : Σ n : ℕ, Fin n → E → E) (u : E → ℂ) (x : E) : ℂ :=
  iteratedFDeriv ℝ t.1 u x (fun i => t.2 i x)
private theorem list_fderiv {α : Type*} (ts : List α) (f : α → E → ℂ) (x : E)
    (hf : ∀ t ∈ ts, DifferentiableAt ℝ (f t) x) :
    HasFDerivAt (fun y => (ts.map (fun t => f t y)).sum)
      (ts.map (fun t => fderiv ℝ (f t) x)).sum x := by
  induction ts with
  | nil => simpa using hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) x
  | cons t ts ih =>
    exact ((hf t (by simp)).hasFDerivAt.fun_add
      (ih (fun r hr => hf r (by simp [hr]))))
private theorem coordWord_expansion {ι : Type*} (fields : ι → E → E) (U : Set E)
    (hU : IsOpen U) (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U) (w : List ι) :
    ∃ ts : List (Σ n : ℕ, Fin n → E → E),
      (∀ t ∈ ts, t.1 ≤ w.length ∧ ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (t.2 i) U) ∧
      ∀ u : E → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) u U → ∀ x ∈ U,
        directionalWord fields w u x = (ts.map (fun t => directionJet t u x)).sum := by
  induction w with
  | nil =>
    refine ⟨[⟨0, Fin.elim0⟩], ?_, ?_⟩
    · intro t ht; simp only [List.mem_singleton] at ht; subst t
      exact ⟨by simp, fun i => Fin.elim0 i⟩
    · intro u hu x hx; simp [directionalWord, directionJet]
  | cons b w ih =>
    obtain ⟨ts, hts, heq⟩ := ih
    let expand : (Σ n : ℕ, Fin n → E → E) → List (Σ n : ℕ, Fin n → E → E) := fun t =>
      ⟨t.1+1, Fin.cons (fields b) t.2⟩ :: (List.finRange t.1).map (fun i =>
        ⟨t.1, Function.update t.2 i (fun x => fderiv ℝ (t.2 i) x (fields b x))⟩)
    refine ⟨ts.flatMap expand, ?_, ?_⟩
    · intro t ht
      obtain ⟨r, hr, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨hn, hd⟩ := hts r hr
      simp only [expand, List.mem_cons, List.mem_map] at ht
      rcases ht with rfl | ⟨i, hi, rfl⟩
      · refine ⟨Nat.succ_le_succ hn, ?_⟩
        intro i; refine Fin.cases (hf b) (fun j => hd j) i
      · refine ⟨hn.trans (Nat.le_succ _), ?_⟩
        intro j
        by_cases h : j = i
        · subst j; simp only [Function.update_self]
          exact ((hd i).fderiv_of_isOpen hU (by simp)).clm_apply (hf b)
        · simpa only [Function.update_of_ne h] using hd j
    · intro u hu x hx
      have he : directionalWord fields w u =ᶠ[nhds x]
          (fun y => (ts.map (fun t => directionJet t u y)).sum) :=
        Filter.Eventually.mono (hU.mem_nhds hx) (fun y hy => heq u hu y hy)
      simp only [directionalWord]
      rw [he.fderiv_eq]
      have ht (t : Σ n : ℕ, Fin n → E → E) (hm : t ∈ ts) :
          DifferentiableAt ℝ (directionJet t u) x :=
        let huAt := hu.contDiffAt (hU.mem_nhds hx)
        let hjet : DifferentiableAt ℝ (iteratedFDeriv ℝ t.1 u) x :=
          (huAt.iteratedFDeriv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
        (hjet.hasFDerivAt.continuousMultilinearMap_apply (fun i =>
          ((((hts t hm).2 i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt)).differentiableAt
      rw [(list_fderiv ts (fun t => directionJet t u) x ht).fderiv]
      rw [show (ts.flatMap expand).map (fun t => directionJet t u x) =
          (ts.map (fun t => (expand t).map (fun r => directionJet r u x))).flatten by
        simp [List.flatMap, List.map_flatten, List.map_map, Function.comp_def]]
      rw [List.sum_flatten, List.map_map]
      rw [show ((ts.map (fun t => fderiv ℝ (directionJet t u) x)).sum) (fields b x) =
          (ts.map (fun t => fderiv ℝ (directionJet t u) x (fields b x))).sum by
        simpa only [List.map_map, Function.comp_def, ContinuousLinearMap.apply_apply] using
          map_list_sum (ContinuousLinearMap.apply ℝ ℂ (fields b x)) (ts.map (fun t => fderiv ℝ (directionJet t u) x))]
      congr 1
      apply List.map_congr_left
      intro t htmem
      change fderiv ℝ (fun y => iteratedFDeriv ℝ t.1 u y (fun i => t.2 i y)) x (fields b x) = _
      rw [variable_jet_derivative u t.1 t.2 x (fields b x)
        (hu.contDiffAt (hU.mem_nhds hx)) (fun i =>
          (((hts t htmem).2 i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
      simp only [expand, directionJet, List.map_cons, List.sum_cons, List.map_map,
        ← List.ofFn_eq_map, List.sum_ofFn]
      apply congrArg₂ (fun a b : ℂ => a + b)
      · congr 1; funext i; refine Fin.cases rfl (fun j => rfl) i
      · change _ = (List.map (fun r => iteratedFDeriv ℝ r.1 u x (fun i => r.2 i x))
          (List.ofFn (fun i : Fin t.1 => (⟨t.1, Function.update t.2 i
            (fun x => fderiv ℝ (t.2 i) x (fields b x))⟩ : Σ n : ℕ, Fin n → E → E)))).sum
        rw [List.map_ofFn, List.sum_ofFn]
        apply Finset.sum_congr rfl
        intro i hi
        congr 1; funext j
        by_cases h : j = i
        · subst j; simp
        · simp [h]

end Generic
theorem word_eq_green (w : List (KPSmoothActualFlowData.B F)) (u : KPLiteralRaw.G F ζ hζ → ℂ) :
    word F ζ hζ w u = w.foldr (fun b v => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 v) u :=
  word_eq_foldr F ζ hζ w u

theorem actual_rightWord_jet_expansion_uniform
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : List (KPSmoothActualFlowData.B F)) :
    ∃ (n : ℕ) (a : Fin n → ℝ) (j : Fin n → KPGlobalResidualConstruction.Jet F),
      (∀ i, (j i).1 ≤ w.length) ∧
      ∀ (φ : KPLiteralRaw.Flat F ζ hζ (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K)
        (s : ℂ) (g : KPLiteralRaw.G F ζ hζ),
        w.foldr (fun b v => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 v)
          (φ.val s) g =
            ∑ i, (a i : ℂ) * KPLiteralChamber.rightJet F ζ hζ (j i) (φ.val s) g := by
  obtain ⟨V, hVo, hb, hVD, hμ, hmaps, hprod, hthick, hcomm⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product F ζ hζ
  obtain ⟨ts, hts, heq⟩ := coordWord_expansion (field F) V hVo
    (fun b => field_smooth F b V hVo hb hμ) w
  let j : Fin ts.length → Jet F := fun i =>
    ⟨(ts.get i).1, fun k => (ts.get i).2 k (archBase F)⟩
  refine ⟨ts.length, fun _ => 1, j, ?_, ?_⟩
  · intro i
    exact (hts (ts.get i) (List.get_mem ts i)).1
  · intro φ s g
    have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => φ.val s (g * archChart F ζ hζ y)) V :=
      (((φ.property.1 s).1.2.1 g)).mono hVD
    have hword := word_in_chart F ζ hζ (φ.val s) V hVo hb hμ hprod w g hu (archBase F) hb
    rw [word_eq_green] at hword
    rw [KPInterface.ResidueConstruction.Raw.archChart_base, mul_one] at hword
    rw [hword, heq _ hu _ hb]
    simp only [Complex.ofReal_one, one_mul, KPLiteralChamber.rightJet]
    change (ts.map (fun t => directionJet t (fun y => φ.val s (g * archChart F ζ hζ y)) (archBase F))).sum = _
    conv_lhs => rw [← List.ofFn_get ts, List.map_ofFn, List.sum_ofFn]
    rfl

end DedekindZetaZeroFree.KPContinuation.ChamberFlatSource

end
end
