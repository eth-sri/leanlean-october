module

public import DedekindZetaZeroFree.LFunctions.Dedekind.AbelianRayCharacterFactorization
public import DedekindZetaZeroFree.LFunctions.Hecke.RayCharacterEntireContinuation

@[expose] public section

namespace DedekindZetaZeroFree.HeckeCorollary

open scoped NumberField Topology
open Filter

theorem zetaFactorization_product_at_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (hf : ∀ i, ContinuousAt (f i) 1)
    (hfactor : ∀ s : ℂ, 1 < s.re →
      NumberField.dedekindZeta L s =
        (∏ i, f i s) * NumberField.dedekindZeta K s) :
    (NumberField.dedekindZeta_residue L : ℂ) =
      (∏ i, f i 1) * (NumberField.dedekindZeta_residue K : ℂ) := by
  have hp : Tendsto (fun x : ℝ => ∏ i, f i (x : ℂ)) (𝓝[>] 1)
      (𝓝 (∏ i, f i 1)) := by
    apply tendsto_finsetProd
    intro i _
    exact (hf i).tendsto.comp
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hlim := hp.mul (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  apply tendsto_nhds_unique (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT L)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 1 < (x : ℂ).re := hx
  rw [hfactor (x : ℂ) hx']
  ring

theorem zetaFactorization_factor_one_ne_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (hf : ∀ i, ContinuousAt (f i) 1)
    (hfactor : ∀ s : ℂ, 1 < s.re →
      NumberField.dedekindZeta L s =
        (∏ i, f i s) * NumberField.dedekindZeta K s)
    (i : ι) : f i 1 ≠ 0 := by
  have hres : (NumberField.dedekindZeta_residue L : ℂ) ≠ 0 := by
    exact_mod_cast NumberField.dedekindZeta_residue_ne_zero L
  rw [zetaFactorization_product_at_one K L f hf hfactor] at hres
  exact (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hres).1) i (Finset.mem_univ i)
