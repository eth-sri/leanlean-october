module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Algebra.Category.ModuleCat.Colimits

@[expose] public section

namespace FiniteChains
open CategoryTheory CategoryTheory.Limits

variable (ι : Type)

/-- The actual free integral module agrees with the categorical coproduct of copies of ℤ. -/
noncomputable def freeIntegerCoproductIso :
    (ModuleCat.free ℤ).obj ι ≅
      (sigmaConst.obj (ModuleCat.of ℤ ℤ)).obj ι :=
  by
  classical
  exact (finsuppLequivDFinsupp ℤ).toModuleIso ≪≫
    (ModuleCat.coprodIsoDirectSum (fun _ : ι => ModuleCat.of ℤ ℤ)).symm

/-- Each actual coproduct injection corresponds to the actual finitely supported generator. -/
theorem freeIntegerCoproductIso_inv_ι (i : ι) (n : ℤ) :
    (freeIntegerCoproductIso ι).inv (Sigma.ι (fun _ : ι => ModuleCat.of ℤ ℤ) i n) =
      Finsupp.single i n := by
  classical
  change (finsuppLequivDFinsupp ℤ).symm
    ((ModuleCat.coprodIsoDirectSum (fun _ : ι => ModuleCat.of ℤ ℤ)).hom
      _) = _
  have h := congrArg (fun k : ModuleCat.of ℤ ℤ ⟶
      ModuleCat.of ℤ (Π₀ _ : ι, ℤ) => k n)
    (ModuleCat.ι_coprodIsoDirectSum_hom (fun _ : ι => ModuleCat.of ℤ ℤ) i)
  change (ModuleCat.coprodIsoDirectSum (fun _ : ι => ModuleCat.of ℤ ℤ)).hom
    (Sigma.ι (fun _ : ι => ModuleCat.of ℤ ℤ) i n) =
      DirectSum.lof ℤ ι (fun _ : ι => ℤ) i n at h
  aesop

/-- The inverse coefficient comparison is natural under arbitrary maps of index sets. -/
theorem freeIntegerCoproductIso_inv_natural {ι κ : Type} (f : ι → κ) :
    (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map (TypeCat.ofHom f) ≫ (freeIntegerCoproductIso κ).inv =
      (freeIntegerCoproductIso ι).inv ≫ (ModuleCat.free ℤ).map (TypeCat.ofHom f) := by
  apply Sigma.hom_ext
  intro i
  ext; simp [ModuleCat.free, sigmaConst]; change (freeIntegerCoproductIso κ).inv
      _ =
    Finsupp.mapDomain f ((freeIntegerCoproductIso ι).inv
      _); rw [freeIntegerCoproductIso_inv_ι, freeIntegerCoproductIso_inv_ι,
    Finsupp.mapDomain_single]

/-- The coefficient comparison is a genuine natural isomorphism of functors. -/
noncomputable def freeIntegerCoproductNatIso :=
  NatIso.ofComponents freeIntegerCoproductIso (by
    intro ι κ f
    apply (cancel_mono (freeIntegerCoproductIso κ).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [show f = TypeCat.ofHom f.hom from rfl, freeIntegerCoproductIso_inv_natural, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp])

end FiniteChains
