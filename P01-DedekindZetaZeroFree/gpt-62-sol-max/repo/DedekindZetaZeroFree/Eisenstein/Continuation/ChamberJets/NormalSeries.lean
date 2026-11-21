module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.Defs
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.CasimirParameterJets

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff BigOperators
open Topology Filter

namespace DedekindZetaZeroFree.KPContActualChamberCasimirJets

theorem normalSeries_compact_holomorphic {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (O : Set ℂ) (hO : IsOpen O) (j : ℂ → C(X, ℂ))
    (hc : ContinuousOn (fun p : ℂ × X => j p.1 p.2) (O ×ˢ Set.univ))
    (hd : ∀ x : X, DifferentiableOn ℂ (fun z => j z x) O) :
    DifferentiableOn ℂ j O := by
  have hj : ContinuousOn j O := by
    apply continuousOn_iff_continuous_restrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    let a : O × X → ℂ × X := fun p => (p.1.val,p.2)
    have ha : Continuous a := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact hc.comp_continuous ha (fun p => ⟨p.1.property, Set.mem_univ _⟩)
  intro s hs
  obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hs)
  let R := r/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hclosed : Metric.closedBall s R ⊆ O :=
    (Metric.closedBall_subset_ball (by dsimp [R]; linarith)).trans hrO
  have hcircle :=
    (hj.mono (Metric.sphere_subset_closedBall.trans hclosed)).circleIntegrable hR.le
  let g : ℂ → C(X,ℂ) := fun w => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    circleIntegral (fun z => (z-w)⁻¹ • j z) s R
  have heq : Set.EqOn g j (Metric.ball s R) := by
    intro w hw
    ext x
    let L : C(X,ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ x
    have hw' : w ∉ Metric.sphere s |R| := by
      rw [abs_of_pos hR]
      intro hh
      exact (ne_of_lt (Metric.mem_ball.mp hw)) hh
    have hi := hcircle.sub_zpow_smul (-1) hw'
    have hL : L (circleIntegral (fun z => (z-w)⁻¹ • j z) s R) =
        circleIntegral (fun z => (z-w)⁻¹ • j z x) s R := by
      rw [circleIntegral, circleIntegral, ← L.intervalIntegral_comp_comm (by simpa using hi.out)]
      simp only [map_smul]
      rfl
    change L ((2 * Real.pi * Complex.I : ℂ)⁻¹ • _) = _
    rw [map_smul, hL]
    exact (((hd x).mono hclosed).mono Metric.closure_ball_subset_closedBall).diffContOnCl
      |>.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  have hg : DifferentiableAt ℂ g s := by
    change DifferentiableAt ℂ (fun w => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      circleIntegral (fun z => (z-w)⁻¹ • j z) s R) s
    exact ((Complex.hasDerivAt_circleIntegral_sub_inv_smul (w := s) hcircle (by
      simpa [abs_of_pos hR] using (ne_of_gt hR).symm)).const_smul (2 * Real.pi * Complex.I : ℂ)⁻¹).differentiableAt
  have he : g =ᶠ[𝓝 s] j := Filter.eventually_of_mem (Metric.ball_mem_nhds s hR) (fun w hw => heq hw)
  exact (hg.congr_of_eventuallyEq he.symm).differentiableWithinAt

theorem normalSeries_compact_family_of_local {E : Type*} [TopologicalSpace E]
    (O : Set ℂ) (hO : IsOpen O) (U : Set E) (f : ℂ → E → ℂ)
    (hl : ∀ x ∈ U, ∃ (K : Set E) (hK : IsCompact K), x ∈ interior K ∧ K ⊆ U ∧
      (letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
       ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧ ∀ z ∈ O, ∀ y : K, j z y = f z y.val))
    (C : Set E) (hC : IsCompact C) (hCU : C ⊆ U) :
    letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
    ∃ j : ℂ → C(C,ℂ), DifferentiableOn ℂ j O ∧ ∀ z ∈ O, ∀ x : C, j z x = f z x.val := by
  have hc : ContinuousOn (fun p : ℂ × E => f p.1 p.2) (O ×ˢ U) := by
    intro p hp
    obtain ⟨K,hK,hpK,hKU,j,hj,heq⟩ := hl p.2 hp.2
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hcont : ContinuousOn (fun q : ℂ × K => j q.1 q.2) (O ×ˢ Set.univ) :=
      continuous_eval.comp_continuousOn ((hj.continuousOn.comp continuous_fst.continuousOn
        (fun _ hq => hq.1)).prodMk continuous_snd.continuousOn)
    have hfK : ContinuousOn (fun q : ℂ × E => f q.1 q.2) (O ×ˢ K) := by
      apply continuousOn_iff_continuous_restrict.mpr
      let a : (O ×ˢ K) → ℂ × K := fun q => (q.val.1, ⟨q.val.2,q.property.2⟩)
      have ha : Continuous a := (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
      exact (hcont.comp_continuous ha (fun q => ⟨q.property.1, Set.mem_univ _⟩)).congr
        (fun q => heq q.val.1 q.property.1 ⟨q.val.2,q.property.2⟩)
    apply (hfK.continuousAt ?_).continuousWithinAt
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (hO.mem_nhds hp.1) (mem_interior_iff_mem_nhds.mp hpK)
  have hd : ∀ x ∈ U, DifferentiableOn ℂ (fun z => f z x) O := by
    intro x hx
    obtain ⟨K,hK,hxK,hKU,j,hj,heq⟩ := hl x hx
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let L : C(K,ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ ⟨x, interior_subset hxK⟩
    exact (L.differentiable.comp_differentiableOn hj).congr
      (fun z hz => (heq z hz ⟨x,interior_subset hxK⟩).symm)
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hcC : ContinuousOn (fun p : ℂ × C => f p.1 p.2.val) (O ×ˢ Set.univ) :=
    hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1,hCU p.2.property⟩)
  have hslice : ∀ z ∈ O, Continuous (fun x : C => f z x.val) := by
    intro z hz
    exact hcC.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hz,Set.mem_univ _⟩)
  let j : ℂ → C(C,ℂ) := fun z => if hz : z ∈ O then ⟨fun x => f z x.val, hslice z hz⟩ else 0
  have hjval : ∀ z ∈ O, ∀ x : C, j z x = f z x.val := by
    intro z hz x
    simp only [j, dif_pos hz]
    rfl
  refine ⟨j,normalSeries_compact_holomorphic O hO j ?_ ?_,hjval⟩
  · exact hcC.congr (fun p hp => hjval p.1 hp.1 p.2)
  · intro x
    exact (hd x.val (hCU x.property)).congr (fun z hz => hjval z hz x)

namespace ChartCalculus
open RightFrame.PullbackWords
variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype B]


private theorem word_smooth (U : Set E) (hU : IsOpen U) (fields : B → E → E)
    (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (u : E → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (w : List B) :
    ContDiffOn ℝ (⊤ : ℕ∞) (directionalWord fields w u) U := by
  induction w with
  | nil => exact hu
  | cons b w ih => exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply (hf b)



end ChartCalculus

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 theorem jet_constant_word (n : ℕ) (u : E → ℂ) (U : Set E) (hU : IsOpen U)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    iteratedFDerivWithin ℝ n u U x v =
      RightFrame.PullbackWords.constantDirectionWord (List.ofFn v) u x := by
  rw [iteratedFDerivWithin_of_isOpen n hU hx]
  induction n generalizing x with
  | zero => simp [RightFrame.PullbackWords.constantDirectionWord,
      RightFrame.PullbackWords.directionalWord, iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [((hu x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (m := n) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) |>.iteratedFDeriv_succ_apply_left']
    have heq : (fun y => iteratedFDeriv ℝ n u y (Fin.tail v)) =ᶠ[𝓝 x]
        RightFrame.PullbackWords.constantDirectionWord (List.ofFn (Fin.tail v)) u :=
      eventually_of_mem (hU.mem_nhds hx) fun y hy => ih y hy _
    rw [heq.fderiv_eq]
    simp only [List.ofFn_succ, RightFrame.PullbackWords.constantDirectionWord,
      RightFrame.PullbackWords.directionalWord]
    rfl


theorem normalSeries_transported_compact_jet {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] [FiniteDimensional ℝ E]
    {B : Type*} [Fintype B]
    (U : Set E) (hU : IsOpen U) (W : Set P) (hW : IsOpen W)
    (fields : B → E → E) (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
    (ψ : P → E) (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ W) (hψU : Set.MapsTo ψ W U)
    (O : Set ℂ) (h : ℂ → E → ℂ) (hs : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (h z) U)
    (hw : ∀ (w : List B) (K : Set E) (hK : IsCompact K), K ⊆ U →
      letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
      ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧
        ∀ z ∈ O, ∀ x : K, j z x = RightFrame.PullbackWords.directionalWord fields w (h z) x.val)
    (K : Set P) (hK : IsCompact K) (hKW : K ⊆ W) (n : ℕ) (v : Fin n → P) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧ ∀ z ∈ O, ∀ x : K,
      j z x = iteratedFDerivWithin ℝ n (h z ∘ ψ) W x.val v := by
  let A := ψ '' K
  have hA : IsCompact A := hK.image_of_continuousOn (hψ.continuousOn.mono hKW)
  have hAU : A ⊆ U := by rintro _ ⟨x,hx,rfl⟩; exact hψU (hKW hx)
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let q : C(K,A) := ⟨fun x => ⟨ψ x.val, ⟨x.val,x.property,rfl⟩⟩,
    (continuousOn_iff_continuous_restrict.mp (hψ.continuousOn.mono hKW)).subtype_mk _⟩
  obtain ⟨N,c,w,hc,_,heq⟩ := RightFrame.PullbackWords.transport U W hU hW
    fields hfields hframe ψ hψ hψU (List.ofFn v)
  choose j hj hjval using fun i : Fin N => hw (w i) A hA hAU
  let a : Fin N → C(K,ℂ) := fun i => ⟨fun x => (c i x.val : ℂ),
    Complex.continuous_ofReal.comp (continuousOn_iff_continuous_restrict.mp ((hc i).continuousOn.mono hKW))⟩
  refine ⟨fun z => ∑ i : Fin N, a i * (j i z).comp q, ?_, ?_⟩
  · apply DifferentiableOn.fun_sum
    intro i _
    exact ((ContinuousMap.compCLM ℂ ℂ q).differentiable.comp_differentiableOn (hj i)).const_mul (a i)
  · intro z hz x
    rw [jet_constant_word n _ W hW ((hs z hz).comp hψ hψU) x.val (hKW x.property) v,
      heq _ (hs z hz) x.val (hKW x.property)]
    simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.comp_apply, a]
    apply Finset.sum_congr rfl
    intro i _
    rw [hjval i z hz]
    change (c i x.val : ℂ) * _ = c i x.val • _
    exact Complex.real_smul.symm

end








end DedekindZetaZeroFree.KPContActualChamberCasimirJets

end
