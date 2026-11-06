module

public import Mathlib
public import RequestProject.UniversalCoefficients

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains

open Finset

variable {G : Type*} [Group G]

open scoped Classical in
def VanishesModN (m : ℕ) (N : Subgroup G) (x : G →₀ ℤ) : Prop :=
  ∀ g : G, (m : ℤ) ∣ ∑ h ∈ x.support.filter (fun h => h * g⁻¹ ∈ N), x h

theorem vanishesModN_congr {m : ℕ} {x : G →₀ ℤ} {N N' : Subgroup G}
    (h : ∀ g ∈ x.support, ∀ g' ∈ x.support, (g * g'⁻¹ ∈ N ↔ g * g'⁻¹ ∈ N')) :
    VanishesModN m N x ↔ VanishesModN m N' x := by
  classical
  have main (M M' : Subgroup G)
      (hMM' : ∀ g ∈ x.support, ∀ g' ∈ x.support, (g * g'⁻¹ ∈ M ↔ g * g'⁻¹ ∈ M'))
      (hM : VanishesModN m M x) (g : G) :
      (m : ℤ) ∣ ∑ h ∈ x.support.filter (fun h => h * g⁻¹ ∈ M'), x h := by
    by_cases hempty : (x.support.filter (fun h => h * g⁻¹ ∈ M')).Nonempty
    · obtain ⟨h₀, hh₀⟩ := hempty
      obtain ⟨hh₀supp, hh₀mem⟩ := mem_filter.1 hh₀
      rw [show x.support.filter (fun h => h * g⁻¹ ∈ M') = x.support.filter (fun h => h * h₀⁻¹ ∈ M) from
        filter_congr fun h hh => ⟨fun hmem => (hMM' h hh h₀ hh₀supp).mpr
            (by rw [show h * h₀⁻¹ = (h * g⁻¹) * (h₀ * g⁻¹)⁻¹ by group]; exact M'.mul_mem hmem (M'.inv_mem hh₀mem)),
          fun hmem => by
            rw [show h * g⁻¹ = (h * h₀⁻¹) * (h₀ * g⁻¹) by group]
            exact M'.mul_mem ((hMM' h hh h₀ hh₀supp).mp hmem) hh₀mem⟩]
      exact hM h₀
    · rw [not_nonempty_iff_eq_empty.1 hempty, sum_empty]; exact dvd_zero _
  exact ⟨main N N' h, main N' N fun g hg g' hg' => (h g hg g' hg').symm⟩

variable {I J : Type*}

def FoxSatMod (m : ℕ) (b : I → J → MonoidAlgebra ℤ G) (v : J →₀ MonoidAlgebra ℤ G)
    (N : Subgroup G) : Prop :=
  (∀ i : I, VanishesModN m N (foxBoundary b v i).coeff) → ∀ j : J, VanishesModN m N (v j).coeff

theorem foxSatMod_zero_iff (b : I → J → MonoidAlgebra ℤ G) (v : J →₀ MonoidAlgebra ℤ G)
    (N : Subgroup G) : FoxSatMod 0 b v N ↔ FoxSat b v N := by
  classical simp only [FoxSatMod, FoxSat, VanishesModN, VanishesMod, Nat.cast_zero, zero_dvd_iff]

theorem foxSatMod_finitelyDetermined (m : ℕ) (b : I → J → MonoidAlgebra ℤ G)
    (v : J →₀ MonoidAlgebra ℤ G) (hfin : {i : I | foxBoundary b v i ≠ 0}.Finite) :
    ∃ F : Finset G, ∀ N N' : Subgroup G,
      (∀ g ∈ F, (g ∈ N ↔ g ∈ N')) → (FoxSatMod m b v N ↔ FoxSatMod m b v N') := by
  classical
  let S : Finset G := (v.support.biUnion fun j => (v j).coeff.support) ∪
    (hfin.toFinset.biUnion fun i => (foxBoundary b v i).coeff.support)
  refine ⟨(S ×ˢ S).image (fun p => p.1 * p.2⁻¹), fun N N' hagree => ?_⟩
  have hpair (g) (hg : g ∈ S) (g') (hg' : g' ∈ S) : g * g'⁻¹ ∈ N ↔ g * g'⁻¹ ∈ N' :=
    hagree _ (mem_image.mpr ⟨(g, g'), mem_product.mpr ⟨hg, hg'⟩, rfl⟩)
  have hv (j : J) : VanishesModN m N (v j).coeff ↔ VanishesModN m N' (v j).coeff :=
    vanishesModN_congr fun g hg g' hg' => by
      have hj : j ∈ v.support := by
        by_contra hj; rw [Finsupp.notMem_support_iff.mp hj] at hg; simp at hg
      exact hpair g (mem_union_left _ (mem_biUnion.mpr ⟨j, hj, hg⟩))
        g' (mem_union_left _ (mem_biUnion.mpr ⟨j, hj, hg'⟩))
  have hb (i : I) : VanishesModN m N (foxBoundary b v i).coeff ↔ VanishesModN m N' (foxBoundary b v i).coeff :=
    vanishesModN_congr fun g hg g' hg' => by
      have hi : foxBoundary b v i ≠ 0 := fun hi => by rw [hi] at hg; simp at hg
      have hmem {u} (hu : u ∈ (foxBoundary b v i).coeff.support) : u ∈ S :=
        mem_union_right _ (mem_biUnion.mpr ⟨i, by simpa [Set.Finite.mem_toFinset] using hi, hu⟩)
      exact hpair g (hmem hg) g' (hmem hg')
  exact ⟨fun hSat hbdry j => (hv j).mp (hSat (fun i => (hb i).mpr (hbdry i)) j),
    fun hSat hbdry j => (hv j).mpr (hSat (fun i => (hb i).mp (hbdry i)) j)⟩

theorem vanishesModN_iff_dvd_coeff (m : ℕ) (M : Subgroup G) [M.Normal] (x : MonoidAlgebra ℤ G) :
    VanishesModN m M x.coeff ↔ ∀ q : G ⧸ M, (m : ℤ) ∣ (quotRingHom ℤ M x).coeff q := by
  classical
  have hmk (g : G) : (quotRingHom ℤ M x).coeff (g : G ⧸ M) =
      ∑ h ∈ x.coeff.support.filter (fun h => h * g⁻¹ ∈ M), x.coeff h := by
    show (Finsupp.mapDomain (QuotientGroup.mk' M) x.coeff) (g : G ⧸ M) = _
    rw [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, sum_filter]
    refine sum_congr rfl fun h _ => ?_
    rw [Finsupp.single_apply]; congr 1
    simp only [eq_iff_iff, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact ⟨fun hh => by
        have h2 := Subgroup.Normal.conj_mem ‹_› _ (by simpa using M.inv_mem hh) h
        rwa [show h * (g⁻¹ * h) * h⁻¹ = h * g⁻¹ by group] at h2,
      fun hh => by
        have h2 := Subgroup.Normal.conj_mem ‹_› _ (by simpa using M.inv_mem hh) h⁻¹
        rwa [show h⁻¹ * (g * h⁻¹) * h⁻¹⁻¹ = h⁻¹ * g by group] at h2⟩
  exact ⟨fun h q => QuotientGroup.induction_on q fun g => hmk g ▸ h g,
    fun h g => hmk g ▸ h _⟩

def divCoeff (m : ℕ) {H : Type*} (z : MonoidAlgebra ℤ H) : MonoidAlgebra ℤ H :=
  MonoidAlgebra.ofCoeff (Finsupp.mapRange (fun a : ℤ => a / (m : ℤ)) (by simp) z.coeff)

theorem nsmul_divCoeff (m : ℕ) {H : Type*} (z : MonoidAlgebra ℤ H)
    (hz : ∀ q : H, (m : ℤ) ∣ z.coeff q) : m • divCoeff m z = z :=
  MonoidAlgebra.coeff_injective <| Finsupp.ext fun q => by
    show m • (divCoeff m z).coeff q = z.coeff q
    rw [divCoeff, MonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply, nsmul_eq_mul]
    exact Int.mul_ediv_cancel' (hz q)

theorem dvd_coeff_iff_nsmul (m : ℕ) {H : Type*} (z : MonoidAlgebra ℤ H) :
    (∀ q : H, (m : ℤ) ∣ z.coeff q) ↔ ∃ y : MonoidAlgebra ℤ H, z = m • y :=
  ⟨fun h => ⟨divCoeff m z, (nsmul_divCoeff m z h).symm⟩,
   by rintro ⟨y, rfl⟩ q
      exact ⟨y.coeff q, by
        show ((m • y : MonoidAlgebra ℤ H).coeff q : ℤ) = (m : ℤ) * y.coeff q
        rw [MonoidAlgebra.coeff_smul_apply, nsmul_eq_mul]⟩⟩

theorem vanishesModN_iff_nsmul (m : ℕ) (M : Subgroup G) [M.Normal] (x : MonoidAlgebra ℤ G) :
    VanishesModN m M x.coeff ↔ ∃ y, quotRingHom ℤ M x = m • y := by
  rw [vanishesModN_iff_dvd_coeff, dvd_coeff_iff_nsmul]

variable (b : I → J → MonoidAlgebra ℤ G)

theorem liftsMod_of_foxSatMod (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G)
    [N.Normal] (m : ℕ) (h : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod m b v N) :
    LiftsMod (boundaryMap b hcol N).toAddMonoidHom m := by
  classical
  rintro u ⟨w, hw⟩
  obtain ⟨v, rfl⟩ := exists_lift N u
  have hv := h v fun i => (vanishesModN_iff_nsmul m N _).2 ⟨w i, by
    rw [← boundaryMap_redVec b hcol N v i]
    simpa using congrArg (fun z : I →₀ MonoidAlgebra ℤ (G ⧸ N) => z i) hw⟩
  refine ⟨Finsupp.mapRange (divCoeff m) (by simp [divCoeff]) (redVec N v), Finsupp.ext fun j => ?_⟩
  show redVec N v j = m • (Finsupp.mapRange (divCoeff m) _ (redVec N v)) j
  rw [Finsupp.mapRange_apply]
  exact (nsmul_divCoeff m (redVec N v j) fun q => by
    simpa [redVec_apply] using (vanishesModN_iff_dvd_coeff m N (v j)).1 (hv j) q).symm
