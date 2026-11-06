import Mathlib.Tactic

import RequestProject.OrderNerveGradedDictionary
import RequestProject.OrderNerveExplicitSingularMap
import RequestProject.TopologicalSingular.SupportedFillings

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

variable {P : Type} [PartialOrder P]

  (n : ℕ)
/-- The free simplicial-module boundary, with its exact integer coefficients. -/
theorem mathlibOrderNerve_d_single  (s : ComposableArrows P (n + 1)) (r : ℤ) :
    (AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) n).hom (Finsupp.single s r) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • Finsupp.single ((nerve P).δ i s) r := by
  simp [AlternatingFaceMapComplex.objD, mathlibOrderNerveModule,
    SimplicialObject.δ, ModuleCat.free]

/-- Mathlib's differential and the augmented list boundary coincide in every positive degree. -/
theorem orderNerveGradedEncode_boundary  (c : ComposableArrows P (n + 1) →₀ ℤ) :
    orderNerveGradedEncode n ((AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule P) n).hom c) =
      Nerve.bdry (orderNerveGradedEncode (n + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single s r =>
    rw  [mathlibOrderNerve_d_single, map_sum, orderNerveGradedEncode_single,
      map_zsmul, Nerve.bdry_of]
    unfold orderNerveVertexList
    rw  [Nerve.bdryOn_ofFn, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw  [map_smul, orderNerveGradedEncode_single, smul_comm]
    rfl

/-- Realize a homogeneous part of the augmented nerve by the canonical unit. -/
noncomputable def orderNerveGradedRealize (P : Type) [PartialOrder P] (n : ℕ) :
    Nerve.Ch P →ₗ[ℤ] Chain (orderNerveRealization P) n :=
  ((orderNerveExplicitSingularMap P).f n).hom.comp (orderNerveGradedDecode n)

theorem orderNerveGradedRealize_boundary  {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    boundary n (orderNerveGradedRealize P (n + 1) c) =
      orderNerveGradedRealize P n (Nerve.bdry c) := by
  have hd : (AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) n).hom
      (orderNerveGradedDecode (n + 1) c) = orderNerveGradedDecode n (Nerve.bdry c) := by
    apply orderNerveGradedEncode_injective n
    rw  [orderNerveGradedEncode_boundary, orderNerveGradedEncode_decode _ hc,
      orderNerveGradedEncode_decode _ (Nerve.bdry_mem_inc hc), Nerve.lengthProjection_bdry]
  have he := congrArg (fun f => f (orderNerveGradedDecode (n + 1) c))
    ((orderNerveExplicitSingularMap P).comm (n + 1) n)
  rw  [complex_d, AlternatingFaceMapComplex.obj_d_eq] at he
  change (boundary n) ((orderNerveExplicitSingularMap P).f (n + 1)
      (orderNerveGradedDecode (n + 1) c)) =
    (orderNerveExplicitSingularMap P).f n (orderNerveGradedDecode n (Nerve.bdry c))
  rw  [← hd]
  exact he

theorem orderNerveGradedRealize_supported  (A : Set P)
    {c : Nerve.Ch P} (hc : c ∈ Nerve.IncOn A) :
    orderNerveGradedRealize P n c ∈
      subChains (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) n := by
  classical
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    change (orderNerveExplicitSingularMap P).f n (orderNerveGradedDecode n
      (FreeAbelianGroup.of l)) ∈ _
    rw  [orderNerveGradedDecode_of]
    by_cases h : ∃ s : ComposableArrows P n, orderNerveVertexList s = l
    · rw  [orderNerveGradedDecodeList, dif_pos h, orderNerveExplicitSingularMap_single]
      apply single_mem_subChains
      intro z
      apply orderNerveSingularSimplex_supported
      intro i
      apply hl.2
      have hs : h.choose.obj i ∈ orderNerveVertexList h.choose := List.mem_ofFn.mpr ⟨i, rfl⟩
      exact (congrArg (fun L => h.choose.obj i ∈ L) h.choose_spec).mp hs
    · simp_all [orderNerveGradedDecodeList]
  | zero => simp
  | add x y _ _ hx hy => aesop
  | neg x _ hx => simp_all

end FiniteChains.Comb
