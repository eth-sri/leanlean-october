module

public import DedekindZetaZeroFree.Metaplectic.Torus.RationalCenterCharacterData

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]

section

variable (q : HeightOneSpectrum (𝓞 F)) (z : (q.adicCompletion F)ˣ)

private lemma finite_component_norm :
    ‖(z : q.adicCompletion F)‖₊ =
      ((q.asIdeal.absNorm : ℝ≥0)) ^ (-(FiniteIdeleGroup.localOrder q z).toAdd) := by
  have hx : Valued.v (z : q.adicCompletion F) ≠ 0 := by simp
  rw [← NNReal.coe_inj, coe_nnnorm, FinitePlace.norm_def,
    WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero q) hx]
  rw [FiniteIdeleGroup.localOrder_apply]
  simp

private lemma unit_eq :
    Units.mk0 (‖(z : q.adicCompletion F)‖₊) (by simp) =
      (FiniteIdeleGroup.primeNorm q ^ (FiniteIdeleGroup.localOrder q z).toAdd)⁻¹ := by
  apply Units.ext
  simp only [Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rw [FiniteIdeleGroup.primeNorm, Units.val_mk0, finite_component_norm, zpow_neg]

end

private lemma finite_finprod_eq (a : FiniteIdeleGroup F) :
    (∏ᶠ q, Units.mk0 (‖(a q : q.adicCompletion F)‖₊) (by simp)) =
      (FiniteIdeleGroup.absoluteNorm a)⁻¹ := by
  classical
  let n := (FiniteIdeleGroup.valuationVector a).toAdd
  have hg : ∀ q, Units.mk0 (‖(a q : q.adicCompletion F)‖₊) (by simp) =
      (FiniteIdeleGroup.primeNorm q ^ n q)⁻¹ := by
    intro q
    rw [unit_eq]
    rfl
  have hsub : Function.mulSupport (fun q => Units.mk0 (‖(a q : q.adicCompletion F)‖₊) (by simp))
      ⊆ n.support := by
    intro q hq
    by_contra h
    apply hq
    change Units.mk0 (‖(a q : q.adicCompletion F)‖₊) (by simp) = 1
    rw [hg q]
    have := Finsupp.notMem_support_iff.mp h
    rw [this, zpow_zero, inv_one]
  rw [finprod_eq_finsetProd_of_mulSupport_subset _ hsub]
  trans ∏ q ∈ n.support, (FiniteIdeleGroup.primeNorm q ^ n q)⁻¹
  · exact Finset.prod_congr rfl (fun q _ => hg q)
  · rw [Finset.prod_inv_distrib]
    congr 1

theorem idele_localAbs_finprod [NumberField.IsTotallyComplex F] (y : Ideles F) :
    (∏ᶠ v : KPHilbert.Place F,
      Units.mk0 (localAbs F v (KPGlobalCubicIdelePairing.ideleEval F v y))
        (ne_of_gt (localAbs_pos F v (KPGlobalCubicIdelePairing.ideleEval F v y)))) =
      KPGlobalTorusFunctionData.ideleAbs F y := by
  classical
  let a := (IdeleGroup.equivAdeleRingUnits).symm y
  let n := (FiniteIdeleGroup.valuationVector a.2).toAdd
  let f := fun v =>
    Units.mk0 (localAbs F v (KPGlobalCubicIdelePairing.ideleEval F v y))
      (ne_of_gt (localAbs_pos F v (KPGlobalCubicIdelePairing.ideleEval F v y)))
  have hfin : ∀ q, f (Sum.inr q) = (FiniteIdeleGroup.primeNorm q ^ n q)⁻¹ := by
    intro q
    have h1 : f (Sum.inr q) =
        Units.mk0 (‖(a.2 q : q.adicCompletion F)‖₊) (by simp) := by
      apply Units.ext
      rw [Units.val_mk0]
      rfl
    rw [h1, unit_eq F q (a.2 q)]
    rfl
  have hinf : ∀ w, f (Sum.inl w) =
      Units.mk0 (‖(InfiniteIdeleGroup.component w a.1 : w.Completion)‖₊ ^ 2) (by simp) := by
    intro w
    apply Units.ext
    rw [Units.val_mk0]
    rfl
  have hB : (Set.range Sum.inr ∩
      Function.mulSupport f).Finite := by
    apply Set.Finite.subset ((n.support.finite_toSet).image Sum.inr)
    rintro v ⟨⟨q, rfl⟩, hv⟩
    refine ⟨q, ?_, rfl⟩
    by_contra hq
    apply hv
    rw [hfin q]
    rw [(Finsupp.notMem_support_iff.mp hq), zpow_zero, inv_one]
  have hsplit : (∏ᶠ v, f v) =
      (∏ w : InfinitePlace F, f (Sum.inl w)) * (∏ᶠ q, f (Sum.inr q)) := by
    rw [← finprod_mem_univ f]
    rw [show Set.univ =
        Set.range Sum.inl ∪
        Set.range Sum.inr from by
      ext v; cases v <;> simp]
    rw [finprod_mem_union' (Set.disjoint_left.mpr (fun v hv hw => by
      obtain ⟨w, rfl⟩ := hv; obtain ⟨q, h⟩ := hw; exact Sum.inr_ne_inl h)) ((Set.finite_range _).inter_of_left _) hB]
    congr 1
    · rw [finprod_mem_range Sum.inl_injective, finprod_eq_prod_of_fintype]
    · rw [finprod_mem_range Sum.inr_injective]
  rw [hsplit]
  have harch : (∏ w : InfinitePlace F, f (Sum.inl w)) =
      InfiniteIdeleGroup.archimedeanNorm a.1 := by
    rw [InfiniteIdeleGroup.archimedeanNorm_apply]
    apply Finset.prod_congr rfl
    intro w _
    rw [hinf w,
      NumberField.InfinitePlace.IsComplex.mult_eq_two (NumberField.IsTotallyComplex.isComplex w)]
    apply Units.ext
    simp [nnnormUnitHom]
  have hfinp : (∏ᶠ q, f (Sum.inr q)) = (FiniteIdeleGroup.absoluteNorm a.2)⁻¹ := by
    have : (∏ᶠ q, f (Sum.inr q)) =
        ∏ᶠ q, Units.mk0 (‖(a.2 q : q.adicCompletion F)‖₊) (by simp) := by
      apply finprod_congr
      intro q
      apply Units.ext
      rw [Units.val_mk0]
      rfl
    rw [this, finite_finprod_eq F a.2]
  rw [harch, hfinp]
  rw [show KPGlobalTorusFunctionData.ideleAbs F y =
      (FiniteIdeleGroup.absoluteNorm a.2 *
        (InfiniteIdeleGroup.archimedeanNorm a.1)⁻¹)⁻¹ from rfl]
  rw [mul_inv, inv_inv, mul_comm]

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct
