module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.NormSheetLogarithmicOperators
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.TraceSchwartzTensors

@[expose] public section

namespace DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory
variable {F : Type} [Field F] [NumberField F]

def complexEuler (g : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  (1 / 2 : ℝ) • SchwartzMap.bilinLeftCLM
    (ContinuousLinearMap.apply (E := ℂ) ℝ ℂ).flip
    (Function.HasTemperateGrowth.id') (SchwartzMap.fderivCLM ℝ ℂ ℂ g)

@[simp] theorem complexEuler_apply (g : SchwartzMap ℂ ℂ) (z : ℂ) :
    complexEuler g z = (1 / 2 : ℝ) • fderiv ℝ g z z := rfl

theorem hasDerivAt_complexNormFlow (g : SchwartzMap ℂ ℂ) (z : ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => g ((Real.exp (v / 2) : ℂ) * z))
      (complexEuler g ((Real.exp (u / 2) : ℂ) * z)) u := by
  have h : HasDerivAt (fun v : ℝ => Real.exp (v / 2))
      (Real.exp (u / 2) / 2) u :=
    by simpa [div_eq_mul_inv] using ((hasDerivAt_id u).div_const 2).exp
  have hc := h.ofReal_comp.mul_const z
  have hd := g.differentiableAt.hasFDerivAt.comp_hasDerivAt u hc
  convert hd using 1
  · rfl
  · rw [complexEuler_apply, ← map_smul]
    congr 1
    simp []
    ring

theorem iteratedDeriv_complexNormFlow (g : SchwartzMap ℂ ℂ) (k : ℕ) (z : ℂ) (u : ℝ) :
    iteratedDeriv k (fun v : ℝ => g ((Real.exp (v / 2) : ℂ) * z)) u =
      ((complexEuler^[k]) g) ((Real.exp (u / 2) : ℂ) * z) := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hf : iteratedDeriv k (fun v : ℝ => g ((Real.exp (v / 2) : ℂ) * z)) =
        fun v : ℝ => ((complexEuler^[k]) g) ((Real.exp (v / 2) : ℂ) * z) := funext ih
    rw [hf, (hasDerivAt_complexNormFlow ((complexEuler^[k]) g) z u).deriv,
      Function.iterate_succ_apply']

set_option backward.isDefEq.respectTransparency false in
private theorem mixed_flow_complex (A : SArithmeticData F) (w : InfinitePlace F)
    (u : ℝ) (x : SLocalProduct F A.Sf) (v : {v : InfinitePlace F // v.IsComplex}) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F (complexNormFlowRaw A w u x).1).2 v =
      if v.val = w then (Real.exp (u / 2) : ℂ) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v
      else (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v := by
  change InfinitePlace.Completion.extensionEmbedding v.val
      (Function.update x.1 w
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm
          (Real.exp (u / 2) : ℂ) * x.1 w) v.val) = _
  by_cases hv : v.val = w
  · subst w
    simp only [Function.update_self, ↓reduceIte]
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place v.val))
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place v.val)).symm
        (Real.exp (u / 2) : ℂ) * x.1 v.val) = _
    rw [map_mul, RingEquiv.apply_symm_apply]
    rfl
  · rw [Function.update_of_ne hv, if_neg hv]
    rfl

private theorem real_places_empty (A : SArithmeticData F) :
    IsEmpty {v : InfinitePlace F // v.IsReal} :=
  ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place v.val)) v.property⟩

private theorem tensor_flow_factor (A : SArithmeticData F) (w : InfinitePlace F)
    (g : (v : {v : InfinitePlace F // v.IsComplex}) → SchwartzMap ℂ ℂ)
    (u : ℝ) (x : SLocalProduct F A.Sf) :
    (∏ v, g v ((InfiniteAdeleRing.ringEquiv_mixedSpace F (complexNormFlowRaw A w u x).1).2 v)) =
      g ⟨w, A.complex_place w⟩ ((Real.exp (u / 2) : ℂ) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 ⟨w, A.complex_place w⟩) *
      ∏ v ∈ Finset.univ.erase ⟨w, A.complex_place w⟩,
        g v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ⟨w, A.complex_place w⟩)]
  congr 1
  · rw [mixed_flow_complex]; simp
  · apply Finset.prod_congr rfl
    intro v hv
    have hne : v.val ≠ w := by
      intro h
      exact (Finset.mem_erase.mp hv).1 (Subtype.ext h)
    rw [mixed_flow_complex, if_neg hne]

theorem logDerivative_tensor (A : SArithmeticData F) (w : InfinitePlace F)
    (k : ℕ) (f : SLocalProduct F A.Sf → ℂ)
    {P : (v : ↥A.Sf) → (v.val.adicCompletion F → ℂ) → Prop}
    (hf : ProbeSheetVerticalDecay.SchwartzTensorWith F A.Sf P f) :
    ProbeSheetVerticalDecay.SchwartzTensorWith F A.Sf P (logDerivativeRaw A w k f) := by
  obtain ⟨c, gr, gc, gf, hgf, hf⟩ := hf
  letI := real_places_empty A
  let v₀ : {v : InfinitePlace F // v.IsComplex} := ⟨w, A.complex_place w⟩
  let gc' := Function.update gc v₀ ((complexEuler^[k]) (gc v₀))
  refine ⟨c, gr, gc', gf, hgf, ?_⟩
  intro x
  have hflow : (fun u => f (complexNormFlowRaw A w u x)) =
      fun u => c * (gc v₀ ((Real.exp (u / 2) : ℂ) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v₀) *
        ∏ v ∈ Finset.univ.erase v₀,
          gc v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v)) *
        ∏ v : ↥A.Sf, gf v (x.2 v) := by
    funext u
    rw [hf, tensor_flow_factor]
    simp [complexNormFlowRaw, v₀, mul_assoc]
  unfold logDerivativeRaw
  rw [hflow]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field,
    iteratedDeriv_complexNormFlow, zero_div, Real.exp_zero, Complex.ofReal_one, one_mul]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  have hp : (∏ v, gc' v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v)) =
      ((complexEuler^[k]) (gc v₀)) ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v₀) *
      ∏ v ∈ Finset.univ.erase v₀, gc v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v₀)]
    simp only [gc', Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    rw [Function.update_of_ne (Finset.mem_erase.mp hv).1]
  rw [hp]
  ring

end
end DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
