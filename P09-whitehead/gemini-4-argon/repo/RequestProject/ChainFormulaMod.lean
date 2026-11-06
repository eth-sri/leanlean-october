module

public import RequestProject.ChainFormula
public import RequestProject.FoxRequirementMod

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains

open MonoidAlgebra

universe u

variable {G : Type u} [Group G] {I J : Type u}

theorem vanishesModN_ker_iff {H : Type*} [Group H] (φ : G →* H) (m : ℕ)
    (x : MonoidAlgebra ℤ G) :
    VanishesModN m φ.ker x.coeff ↔ ∃ y, MonoidAlgebra.mapDomainRingHom ℤ φ x = m • y := by
  have hinj : ∀ (z : MonoidAlgebra ℤ (G ⧸ φ.ker)),
      (∃ y : MonoidAlgebra ℤ H, MonoidAlgebra.mapDomain (QuotientGroup.kerLift φ) z = m • y) ↔
        ∃ y : MonoidAlgebra ℤ (G ⧸ φ.ker), z = m • y := fun z => by
    classical
    refine ⟨fun ⟨y, hy⟩ => (dvd_coeff_iff_nsmul m z).1 fun q => ⟨y.coeff (QuotientGroup.kerLift φ q), ?_⟩,
      by rintro ⟨y, rfl⟩; exact ⟨MonoidAlgebra.mapDomain (QuotientGroup.kerLift φ) y,
        map_nsmul ((MonoidAlgebra.mapDomainLinearMap ℤ ℤ (QuotientGroup.kerLift φ)).toAddMonoidHom) m y⟩⟩
    have hq : (MonoidAlgebra.mapDomain (QuotientGroup.kerLift φ) z).coeff (QuotientGroup.kerLift φ q) = z.coeff q :=
      Finsupp.mapDomain_apply_of_injective (QuotientGroup.kerLift_injective φ) z.coeff q
    rw [← hq, hy]
    show ((m • y : MonoidAlgebra ℤ H).coeff (QuotientGroup.kerLift φ q) : ℤ) =
      (m : ℤ) * y.coeff (QuotientGroup.kerLift φ q)
    rw [MonoidAlgebra.coeff_smul_apply, nsmul_eq_mul]
  rw [vanishesModN_iff_nsmul,
    show MonoidAlgebra.mapDomainRingHom ℤ φ x =
      MonoidAlgebra.mapDomain (QuotientGroup.kerLift φ) (quotRingHom ℤ φ.ker x) from
      MonoidAlgebra.coeff_injective (by
        change Finsupp.mapDomain _ x.coeff = Finsupp.mapDomain _ (Finsupp.mapDomain _ x.coeff)
        rw [← Finsupp.mapDomain_comp]; rfl),
    hinj]

variable {b : I → J → MonoidAlgebra ℤ G} {n : ℕ} {Fund : ℕ → Type u} [∀ r, Group (Fund r)]
  {Gen Cell : ℕ → Type u}

def CycleLiftsMod (h : ChainInput b n Fund Gen Cell) (m : ℕ) : Prop :=
  ∀ r : ℕ, r < n → ∀ u : Cell r →₀ MonoidAlgebra ℤ (Fund r),
    (∀ a : Gen r, ∃ w, ∑ c ∈ u.support, u c * h.bdry r a c = m • w) →
      ∃ u' : Cell r →₀ MonoidAlgebra ℤ (Fund r),
        (∀ a : Gen r, ∑ c ∈ u'.support, u' c * h.bdry r a c = 0) ∧
          ∃ z : Cell r →₀ MonoidAlgebra ℤ (Fund r), u = u' + m • z

namespace ChainInput

variable (h : ChainInput b n Fund Gen Cell)

noncomputable def stepHom (r : ℕ) :
    (Cell r →₀ MonoidAlgebra ℤ (Fund r)) →+ (Cell (r + 1) →₀ MonoidAlgebra ℤ (Fund (r + 1))) :=
  (Finsupp.mapDomain.addMonoidHom (h.cellStep r)).comp
    (Finsupp.mapRange.addMonoidHom (MonoidAlgebra.mapDomainRingHom ℤ (h.psi r)).toAddMonoidHom)

theorem foxSatMod_of_not_foxSatMod (m : ℕ) (hlift : CycleLiftsMod h m)
    (v : J →₀ MonoidAlgebra ℤ G) (r : ℕ) (hviol : ¬ FoxSatMod m b v (h.phi r).ker) :
    ∀ s, r < s → s ≤ n → FoxSatMod m b v (h.phi s).ker := by
  classical
  intro s hrs hsn
  have hbdry : ∀ i : I, VanishesModN m (h.phi r).ker (foxBoundary b v i).coeff := by
    by_contra hcon; exact hviol fun hb => absurd hb hcon
  have hr : r < n := lt_of_lt_of_le hrs hsn
  have hcyc (a : Gen r) :
      ∃ w, ∑ c ∈ (h.oldVec r v).support, h.oldVec r v c * h.bdry r a c = m • w := by
    rw [Finset.sum_subset (h.oldVec_support_subset r v) fun c _ hc => by
        rw [Finsupp.notMem_support_iff.mp hc, zero_mul],
      Finset.sum_image fun x _ y _ hxy => h.cellIncl_injective r hxy]
    by_cases hex : ∃ i, a = h.genIncl r i
    · obtain ⟨i, rfl⟩ := hex
      rw [Finset.sum_congr rfl fun j (_ : j ∈ v.support) => by
          rw [h.oldVec_apply_cellIncl, h.bdry_old, ← map_mul], ← map_sum]
      exact (vanishesModN_ker_iff (h.phi r) m (foxBoundary b v i)).1 (hbdry i)
    · push_neg at hex
      exact ⟨0, by rw [smul_zero]; exact Finset.sum_eq_zero fun j _ => (by
        rw [h.bdry_new r a hex j, mul_zero])⟩
  obtain ⟨u', hu'cycle, z, hz⟩ := hlift r hr (h.oldVec r v) hcyc
  have hstep : h.stepHom r (h.oldVec r v) = m • h.stepHom r z := by
    rw [hz, map_add, show h.stepHom r u' = 0 from h.zero_pi2 r hr u' hu'cycle, zero_add, map_nsmul]
  intro _ j
  have hcoord := DFunLike.congr_fun hstep (h.cellStep r (h.cellIncl r j))
  change (Finsupp.mapDomain (h.cellStep r)
      (Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ (h.psi r)) (map_zero _) (h.oldVec r v)))
      (h.cellStep r (h.cellIncl r j)) = _ at hcoord
  rw [Finsupp.mapDomain_apply_of_injective (h.cellStep_injective r)] at hcoord
  simp only [Finsupp.mapRange_apply] at hcoord
  rw [h.oldVec_apply_cellIncl, mapDomainRingHom_comp_apply, h.phi_succ] at hcoord
  have h1 : ∃ y, MonoidAlgebra.mapDomainRingHom ℤ (h.phi (r + 1)) (v j) = m • y :=
    ⟨(h.stepHom r z) (h.cellStep r (h.cellIncl r j)), by rw [hcoord, Finsupp.smul_apply]⟩
  have hmono : ∀ d : ℕ, ∃ y, MonoidAlgebra.mapDomainRingHom ℤ (h.phi (r + 1 + d)) (v j) = m • y := by
    intro d; induction d with
    | zero => simpa using h1
    | succ d ih =>
        obtain ⟨y, hy⟩ := ih
        change ∃ y, MonoidAlgebra.mapDomainRingHom ℤ (h.phi ((r + 1 + d) + 1)) (v j) = m • y
        refine ⟨MonoidAlgebra.mapDomain (h.psi (r + 1 + d)) y, ?_⟩
        rw [← h.phi_succ, ← mapDomainRingHom_comp_apply, hy]
        exact map_nsmul ((MonoidAlgebra.mapDomainRingHom ℤ (h.psi (r + 1 + d))).toAddMonoidHom) m y
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hrs)
  exact (vanishesModN_ker_iff (h.phi (r + 1 + d)) m (v j)).2 (hmono d)

end ChainInput
end FiniteChains
