import Mathlib.Tactic

import RequestProject.AcyclicPresentationActualChains
import RequestProject.RegularCoverChainDescent

/-! Retain the actual maps and the triviality on fundamental groups in
the acyclic presentation construction. These data are needed by regular
cover descent and are lost if one retains only the existence of HasChain.
 -/

noncomputable section


namespace FiniteChains.RelativeNormalForm.AmbientChain
open Comb

variable {A C : Type} {core : C → FreeGroup A} {n : ℕ}
  (c : AmbientChain core n)



def cellInclusion (i : ℕ)  :=
  presInclHom (c.chainGenIncl i) (c.chainGenIncl_injective i)
    (c.chainRel i) (c.chainRel (i + 1)) (c.chainCellIncl i) (c.chainRel_incl i)

abbrev cellInclusion_zero (hinj : Function.Injective (expMatrix core))
    (i : ℕ) (hi : i < n + 1)  :=
  (FiniteChains.Comb.zeroPi2_presInclHom_iff (c.chainRel i) (c.chainGenIncl i)
        (FiniteChains.RelativeNormalForm.AmbientChain.chainGenIncl_injective c i) (c.chainCellIncl i)
        (FiniteChains.RelativeNormalForm.AmbientChain.chainRel_incl c i)).mpr
    ((c.toPresChainFS hinj).zero_pi2 i hi)

abbrev first_cellInclusion_pi1Trivial  :=
  (FiniteChains.Comb.pi1Trivial_presInclHom_iff (c.chainRel 0) (c.chainGenIncl 0)
        (FiniteChains.RelativeNormalForm.AmbientChain.chainGenIncl_injective c 0) (c.chainCellIncl 0)
        (FiniteChains.RelativeNormalForm.AmbientChain.chainRel_incl c 0)).mpr
    fun (w : FiniteChains.PresGroup (c.chainRel 0)) =>
    QuotientGroup.induction_on w fun (w : FreeGroup (c.chainGen 0)) =>
      let f := (QuotientGroup.mk' (FiniteChains.relSub (c.chainRel 1))).comp (FreeGroup.map Sum.inl);
      have hf := FreeGroup.ext_hom f 1 fun (a : A) => id (c.core_trivial 0 a);
      id (DFunLike.congr_fun hf w)

end FiniteChains.RelativeNormalForm.AmbientChain






