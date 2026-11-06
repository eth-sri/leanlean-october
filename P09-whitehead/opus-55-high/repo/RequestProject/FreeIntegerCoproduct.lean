import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.Category.ModuleCat.Colimits
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains
open CategoryTheory CategoryTheory.Limits

/-- The actual free integral module agrees with the categorical coproduct of copies of ℤ. -/
def freeIntegerCoproductIso ι :
    (ModuleCat.free ℤ).obj ι ≅
      (sigmaConst.obj (ModuleCat.of ℤ ℤ)).obj ι :=
  by
  classical
  exact (finsuppLequivDFinsupp ℤ).toModuleIso ≪≫
    (ModuleCat.coprodIsoDirectSum _).symm

/-- Each actual coproduct injection corresponds to the actual finitely supported generator. -/
theorem freeIntegerCoproductIso_inv_ι ι i (n : ℤ) :
    (freeIntegerCoproductIso ι).inv (Sigma.ι (fun _ : ι => ModuleCat.of ℤ ℤ) i n) =
      Finsupp.single i n := by
  classical
  change (finsuppLequivDFinsupp ℤ).symm
    ((ModuleCat.coprodIsoDirectSum (fun _ : ι => ModuleCat.of ℤ ℤ)).hom
      (Sigma.ι (fun _ => ModuleCat.of ℤ ℤ) i n)) = _
  have h := congrArg (· n)
    (ModuleCat.ι_coprodIsoDirectSum_hom (fun _ => ModuleCat.of ℤ ℤ) i)
  change (ModuleCat.coprodIsoDirectSum _).hom
    (Sigma.ι (fun _ => ModuleCat.of ℤ ℤ) i n) =
      DirectSum.lof ℤ ι _ i n at h
  aesop

/-- The inverse coefficient comparison is natural under arbitrary maps of index sets. -/
theorem freeIntegerCoproductIso_inv_natural (f : ι → κ) :
    (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map (TypeCat.ofHom f) ≫ (freeIntegerCoproductIso κ).inv =
      (freeIntegerCoproductIso ι).inv ≫ (ModuleCat.free ℤ).map (TypeCat.ofHom f) := by
  apply Sigma.hom_ext
  intro i
  apply ModuleCat.hom_ext
  ext
  simp
  change (freeIntegerCoproductIso κ).inv
      (Sigma.ι (fun _ => ModuleCat.of ℤ ℤ) (f i) 1) =
    Finsupp.mapDomain f ((freeIntegerCoproductIso ι).inv
      (Sigma.ι (fun _ => ModuleCat.of ℤ ℤ) i 1))
  grind [freeIntegerCoproductIso_inv_ι, Finsupp.mapDomain_single]

/-- The coefficient comparison is a genuine natural isomorphism of functors. -/
def freeIntegerCoproductNatIso :=
  NatIso.ofComponents freeIntegerCoproductIso (by
    intro ι κ f
    apply (cancel_mono (freeIntegerCoproductIso κ).inv).mp
    grind [Category.assoc, Iso.hom_inv_id, Category.comp_id, show f = TypeCat.ofHom f.hom from rfl, freeIntegerCoproductIso_inv_natural, ← Category.assoc, Category.id_comp])
