import Mathlib.Tactic

import RequestProject.TopologicalSingular.PrismLocality

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
open scoped unitInterval
variable {X : Type u} [TopologicalSpace X]

noncomputable def simplexHomotopyPrism {n : ℕ} {f g : Simplex X n} (H : f.Homotopy g)  :=
  SingularPrism.prism H n (Finsupp.single (ContinuousMap.id (Domain n)) 1)

variable (n : ℕ)
  (g : Simplex X n → Simplex X n)
include g in
noncomputable def homotopyFamilyPrism  
    (H : ∀ tau : Simplex X n, tau.Homotopy (g tau))  :=
  Finsupp.linearCombination ℤ (fun tau => simplexHomotopyPrism (H tau))

include g in
theorem homotopyFamilyPrism_single  
    (H : ∀ tau : Simplex X n, tau.Homotopy (g tau)) (tau : Simplex X n) (r : ℤ) :
    homotopyFamilyPrism n g H (Finsupp.single tau r) = r • simplexHomotopyPrism (H tau) :=
  Finsupp.linearCombination_single ℤ r tau

include g in
noncomputable def simplexFamilyMap    := Finsupp.lmapDomain ℤ ℤ g

include g in
theorem simplexFamilyMap_single  
    (tau : Simplex X n) (r : ℤ) : simplexFamilyMap n g (Finsupp.single tau r) =
      Finsupp.single (g tau) r := Finsupp.mapDomain_single

variable (n : ℕ) (lo : Simplex X n → Simplex X n)
  (hi : Simplex X (n + 1) → Simplex X (n + 1))
  (L : ∀ tau : Simplex X n, tau.Homotopy (lo tau))
  (H : ∀ tau : Simplex X (n + 1), tau.Homotopy (hi tau))
  (compat : ∀ (tau : Simplex X (n + 1)) (i : Fin (n + 2)) (t : I) (z : Domain n),
    H tau (t, stdSimplex.map (SimplexCategory.δ i) z) = L (face i tau) (t, z))

include compat

variable (tau : Simplex X (n + 1))
theorem coherentPrism_boundary_single  :
    SingularPrism.prism (H tau) n
      (boundary n (Finsupp.single (ContinuousMap.id (Domain (n + 1))) 1)) =
        homotopyFamilyPrism n lo L (boundary n (Finsupp.single tau 1)) := by
  simp only [boundary_single, map_sum, map_zsmul, homotopyFamilyPrism_single, one_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun c : Chain X (n + 1) => (-1 : ℤ) ^ i.val • c)
  exact SingularPrism.prism_single_congr (H tau) (L (face i tau))
    (face i (ContinuousMap.id (Domain (n + 1)))) (ContinuousMap.id (Domain n))
    (compat tau i) 1

theorem coherentPrism_identity_single  :
    boundary (n + 1) (simplexHomotopyPrism (H tau)) +
      homotopyFamilyPrism n lo L (boundary n (Finsupp.single tau 1)) =
        Finsupp.single (hi tau) 1 - Finsupp.single tau 1 := by
  have he := SingularPrism.prism_identity_succ_single (H tau) n
    (ContinuousMap.id (Domain (n + 1))) 1
  rw [coherentPrism_boundary_single n lo hi L H compat] at he
  simpa only [simplexHomotopyPrism, map_single, simplexMap, ContinuousMap.comp_id] using he

variable (c : Chain X (n + 1))
/-- The prism formula remains valid when each singular simplex has its own
homotopy, provided those homotopies agree on every face. -/
theorem coherentPrism_identity  :
    boundary (n + 1) (homotopyFamilyPrism (n + 1) hi H c) +
      homotopyFamilyPrism n lo L (boundary n c) = simplexFamilyMap (n + 1) hi c - c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, add_zero, sub_zero]
  | add a b ha hb =>
    simp only [map_add]
    linear_combination (norm := abel) ha + hb
  | single tau r =>
    have hr : Finsupp.single tau r = r • Finsupp.single tau 1 := by simp
    rw [hr]
    simpa only [map_smul, homotopyFamilyPrism_single, one_smul, simplexFamilyMap_single,
      smul_add, smul_sub] using
      congrArg (fun b : Chain X (n + 1) => r • b) (coherentPrism_identity_single n lo hi L H compat tau)

variable (hc : boundary n c = 0)
include hc in
theorem coherentPrism_cycle_difference_bounds   :
    simplexFamilyMap (n + 1) hi c - c ∈ LinearMap.range (boundary (n + 1)) := by
  refine ⟨homotopyFamilyPrism (n + 1) hi H c, ?_⟩
  simpa [hc, map_zero, add_zero] using coherentPrism_identity n lo hi L H compat c

include hc in
theorem coherentPrism_preserves_cycles   :
    boundary n (simplexFamilyMap (n + 1) hi c) = 0 := by
  obtain ⟨b, hb⟩ := coherentPrism_cycle_difference_bounds n lo hi L H compat c hc
  have he := boundary_boundary n b
  rw [hb, map_sub, hc, sub_zero] at he
  exact he

end FiniteChains.TopologicalSingular
