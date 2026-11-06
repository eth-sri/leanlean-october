import RequestProject.TopologicalSingular.PrismLocality
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.TopologicalSingular
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X]

def simplexHomotopyPrism {f g : Simplex X n} (H : f.Homotopy g) :=
  SingularPrism.prism H n (Finsupp.single (ContinuousMap.id _) 1)

def homotopyFamilyPrism n (g : Simplex X n → Simplex X n)
    (H : ∀ tau : Simplex X n, tau.Homotopy (g tau)) : Chain X n →ₗ[ℤ] Chain X (n + 1) :=
  Finsupp.linearCombination ℤ (fun tau => simplexHomotopyPrism (H tau))

theorem homotopyFamilyPrism_single n g
    H (tau : Simplex X n) r :
    homotopyFamilyPrism n g H (Finsupp.single tau r) = r • simplexHomotopyPrism (H tau) :=
  Finsupp.linearCombination_single ℤ r tau

def simplexFamilyMap n (g : Simplex X n → Simplex X n) :
    Chain X n →ₗ[ℤ] Chain X n := Finsupp.lmapDomain ℤ ℤ g

theorem simplexFamilyMap_single n g
    (tau : Simplex X n) r : simplexFamilyMap n g (Finsupp.single tau r) =
      Finsupp.single (g tau) r := Finsupp.mapDomain_single

variable (n : ℕ) (lo : Simplex X n → Simplex X n)
  (hi : Simplex X (n + 1) → Simplex X (n + 1))
  (L : ∀ tau : Simplex X n, tau.Homotopy (lo tau))
  (H : ∀ tau : Simplex X (n + 1), tau.Homotopy (hi tau))
  (compat : ∀ (tau : Simplex X (n + 1)) (i : Fin (n + 2)) (t : I) (z : Domain n),
    H tau (t, stdSimplex.map (SimplexCategory.δ i) z) = L (face i tau) (t, z))

include compat

theorem coherentPrism_boundary_single tau :
    SingularPrism.prism (H tau) n
      (boundary n (Finsupp.single (ContinuousMap.id (Domain (n + 1))) 1)) =
        homotopyFamilyPrism n lo L (boundary n (Finsupp.single tau 1)) := by
  simp only [boundary_single, map_sum, map_zsmul, homotopyFamilyPrism_single, one_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg _
  exact SingularPrism.prism_single_congr _ _
    _ _
    (compat tau i) 1

theorem coherentPrism_identity_single tau :
    boundary (n + 1) (simplexHomotopyPrism (H tau)) +
      homotopyFamilyPrism n lo L (boundary n (Finsupp.single tau 1)) =
        Finsupp.single (hi tau) 1 - Finsupp.single tau 1 := by
  have he := SingularPrism.prism_identity_succ_single (H tau) n
    (ContinuousMap.id (Domain (n + 1))) 1
  rw [coherentPrism_boundary_single n lo hi L H compat] at he
  aesop

/-- The prism formula remains valid when each singular simplex has its own
homotopy, provided those homotopies agree on every face. -/
theorem coherentPrism_identity c :
    boundary (n + 1) (homotopyFamilyPrism (n + 1) hi H c) +
      homotopyFamilyPrism n lo L (boundary n c) = simplexFamilyMap (n + 1) hi c - c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp [map_add]
    linear_combination (norm := abel) ha + hb
  | single tau r =>
    have hr : Finsupp.single tau r = r • Finsupp.single tau 1 := by simp
    rw [hr]
    simpa only [map_smul, homotopyFamilyPrism_single, one_smul, simplexFamilyMap_single,
      smul_add, smul_sub] using
      congrArg (fun b : Chain X (n + 1) => r • b) (coherentPrism_identity_single n lo hi L H compat tau)

theorem coherentPrism_cycle_difference_bounds c (hc : boundary n c = 0) :
    simplexFamilyMap (n + 1) hi c - c ∈ LinearMap.range (boundary (n + 1)) := by
  refine ⟨homotopyFamilyPrism _ hi H c, ?_⟩
  simpa [hc, map_zero, add_zero] using coherentPrism_identity n lo hi L H compat c

theorem coherentPrism_preserves_cycles c (hc : boundary n c = 0) :
    boundary n (simplexFamilyMap (n + 1) hi c) = 0 := by
  cases' coherentPrism_cycle_difference_bounds n lo hi L H compat c hc with b hb
  have he := boundary_boundary n b
  simp_all
