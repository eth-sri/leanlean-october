module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos821.P3Pair.PairingFromMoment

public import Erdos821.S2.TransferenceAssemblyTask
public import Erdos821.P3.PhysicalSchur

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Packet

open Erdos821.Blueprint.Graph

def absolutePhysicalRawReal {F } {P } {J m }
    (A : Model F P J m) (z z' : A.State)  :=
  if P.physical (J + F.ell) z.1 z.2 ∧ P.physical (J + F.ell) z'.1 z'.2 then
    ∑ v, ∑ u : P.Aux J,
      if (A.pattern v).compatible z.2 z'.2 ∧
          (A.pattern v).ban z.2 z'.2 u ∧
          z'.1 = z.1 + A.k * ((A.pattern v).D z.2 u : ℤ) then
        ((A.pattern v).auxMass u * (A.pattern v).physicalTargetMass *
          A.damping z.1 * A.damping z'.1) *
          ‖(A.pattern v).coefficient (P.restrictBig z.2) (P.restrictBig z'.2)
            (fun g => u g.val) *
            imaginaryPower ((A.pattern v).D z.2 u) A.zeta‖
      else 0
  else 0

section
variable {F : FixedData} {P : PrimeGroups} {J m : ℕ} {x : ℝ} (A : Model F P J m) (z z' : A.State)

lemma physicalRaw_true_eq_ofReal_absolutePhysicalRawReal
         
        :
    A.physicalRaw true z z' = (absolutePhysicalRawReal A z z' : ℂ) := by
  classical
  by_cases hphys : P.physical (J + F.ell) z.1 z.2 ∧
      P.physical (J + F.ell) z'.1 z'.2
  · simp only [absolutePhysicalRawReal, Model.physicalRaw, ite_eq_left hphys, ite_true]
    simp only [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro u hu
    bound
  · simp [absolutePhysicalRawReal, Model.physicalRaw, hphys]

lemma absolutePhysicalRawReal_nonneg
           
        (hP : P.Admissible F x) :
    0 ≤ absolutePhysicalRawReal A z z' := by
  classical
  unfold absolutePhysicalRawReal
  split_ifs with hphys
  · apply Finset.sum_nonneg
    intro v hv
    apply Finset.sum_nonneg
    intro u hu
    split_ifs with hcond
    · have haux : 0 < (A.pattern v).auxMass u :=
        Erdos821.P3Core.auxMass_pos_of_admissible (A.pattern v) u hP
      have hV : ∀ g : P.Group, 0 < P.V g :=
        Erdos821.P3Core.V_pos_of_admissible hP
      have htarget : 0 < (A.pattern v).physicalTargetMass :=
        Erdos821.P3Core.physicalTargetMass_pos_of_admissible (A.pattern v) hV
      have hd₁ : 0 < A.damping z.1 := Erdos821.P3Core.damping_pos A z.1
      have hd₂ : 0 < A.damping z'.1 := Erdos821.P3Core.damping_pos A z'.1
      positivity
    · exact le_of_eq rfl
  · exact le_of_eq rfl

end

def absolutePhysicalKernelReal {F } {P } {J m }
    (A : Model F P J m) (z z' : A.State)  :=
  ((Fintype.card (P.Permutations (J + F.ell)) : ℝ) ^ 2)⁻¹ *
    ∑ π : P.Permutations (J + F.ell), ∑ τ : P.Permutations (J + F.ell),
      absolutePhysicalRawReal A (z.1, P.act π z.2) (z'.1, P.act τ z'.2)

section
variable {F : FixedData} {P : PrimeGroups} {J ell m : ℕ} {x : ℝ} (A : Model F P J m) (z z' : A.State) (hP : P.Admissible F x) (n : ℤ)

lemma physicalKernel_true_eq_ofReal_absolutePhysicalKernelReal
         
        :
    A.physicalKernel true z z' = (absolutePhysicalKernelReal A z z' : ℂ) := by
  classical
  simp [absolutePhysicalKernelReal, Model.physicalKernel,
    physicalRaw_true_eq_ofReal_absolutePhysicalRawReal,
    Complex.ofReal_sum, Complex.ofReal_mul]

include hP in
lemma absolutePhysicalKernelReal_nonneg
           
          :
    0 ≤ absolutePhysicalKernelReal A z z' := by
  classical
  unfold absolutePhysicalKernelReal
  apply mul_nonneg
  · exact inv_nonneg.mpr (sq_nonneg _)
  · apply Finset.sum_nonneg
    intro π hπ
    apply Finset.sum_nonneg
    intro τ hτ
    exact absolutePhysicalRawReal_nonneg A _ _ hP

include hP in
lemma physicalKernel_true_norm_eq_re
           
          :
    ‖A.physicalKernel true z z'‖ = (A.physicalKernel true z z').re := by
  rw [physicalKernel_true_eq_ofReal_absolutePhysicalKernelReal]
  simp [absolutePhysicalKernelReal_nonneg A z z' hP]

alias pattern_D_le_sup_pow := _root_.SharedProofs.pattern_D_le_sup_pow

lemma possiblePhysicalTargets_subset_neighbors    
          :
    Erdos821.P3Core.possiblePhysicalTargets A n ⊆ A.neighbors n := by
  classical
  intro z hz
  change z ∈ Erdos821.P3Core.possiblePhysicalPositions A n ×ˢ Finset.univ at hz
  rcases Finset.mem_product.mp hz with ⟨hzpos, _⟩
  rcases Finset.mem_image.mp hzpos with ⟨w, hw, htime⟩
  rcases w with ⟨v, a, u⟩
  change n + A.k * ((A.pattern v).D a u : ℤ) = z.1 at htime
  have hD := pattern_D_le_sup_pow (A.pattern v) a u
  have hn : Int.natAbs (A.k * ((A.pattern v).D a u : ℤ)) ≤
      A.k.natAbs * (P.allPrimes.sup id) ^ (J * P.count) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ hD
  have hcast : (Int.natAbs (A.k * ((A.pattern v).D a u : ℤ)) : ℤ) ≤
      (A.stepBound : ℤ) := by
    exact_mod_cast hn
  have habs : |A.k * ((A.pattern v).D a u : ℤ)| ≤ (A.stepBound : ℤ) := by
    simpa only [Int.natCast_natAbs] using hcast
  have hdisp := abs_le.mp habs
  have hmem : n + A.k * ((A.pattern v).D a u : ℤ) ∈
      Finset.Icc (n - A.stepBound) (n + A.stepBound) := by
    simp only [Finset.mem_Icc]
    omega
  have hmem' : z.1 ∈ Finset.Icc (n - A.stepBound) (n + A.stepBound) := by
    simpa [htime] using hmem
  simp [Model.neighbors, hmem']

lemma possiblePhysicalTargets_reverse_subset_neighbors    
          :
    Erdos821.P3Core.possiblePhysicalTargets (Erdos821.P3Core.reversePhysicalModel A) n ⊆
      A.neighbors n := by
  grind [possiblePhysicalTargets_subset_neighbors, Erdos821.P3Core.reversePhysicalModel, Model.neighbors, Model.stepBound]

include hP in
lemma physicalKernel_true_row_neighbor_norm_eq_tsum_re
           
          :
    (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z z'‖) =
      ∑' z', (A.physicalKernel true z z').re := by
  classical
  let S := Erdos821.P3Core.possiblePhysicalTargets A z.1
  have hsubset : S ⊆ A.neighbors z.1 := possiblePhysicalTargets_subset_neighbors A z.1
  have hsum : (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z z'‖) =
      ∑ z' ∈ S, ‖A.physicalKernel true z z'‖ := (Finset.sum_subset hsubset (by
      intro z' hz' hzS
      simp [Erdos821.P3Core.physicalKernel_zero_outside_targets A z.1 z.2 z' hzS])).symm
  have htsum : (∑' z', (A.physicalKernel true z z').re) =
      ∑ z' ∈ S, (A.physicalKernel true z z').re := by
    apply tsum_eq_sum
    intro z' hz'
    simp [Erdos821.P3Core.physicalKernel_zero_outside_targets A z.1 z.2 z' hz']
  calc
    (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z z'‖) =
        ∑ z' ∈ S, ‖A.physicalKernel true z z'‖ := hsum
    _ = ∑ z' ∈ S, (A.physicalKernel true z z').re := by
      apply Finset.sum_congr rfl
      intro z' hz'
      exact physicalKernel_true_norm_eq_re A z z' hP
    _ = ∑' z', (A.physicalKernel true z z').re := htsum.symm

include hP in
lemma physicalKernel_true_column_neighbor_norm_eq_tsum_re
           
          :
    (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z' z‖) =
      ∑' z', (A.physicalKernel true z' z).re := by
  classical
  let R := Erdos821.P3Core.reversePhysicalModel A
  let S := Erdos821.P3Core.possiblePhysicalTargets R z.1
  have hsubset : S ⊆ A.neighbors z.1 := possiblePhysicalTargets_reverse_subset_neighbors A z.1
  have hzero (z' : A.State) (hz' : z' ∉ S) : A.physicalKernel true z' z = 0 := by
    rw [Erdos821.P3Core.physicalKernel_reverse_eq A z.1 z'.1 z.2 z'.2]
    exact Erdos821.P3Core.physicalKernel_zero_outside_targets R z.1 z.2 z' hz'
  have hsum : (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z' z‖) =
      ∑ z' ∈ S, ‖A.physicalKernel true z' z‖ := (Finset.sum_subset hsubset (by
      intro z' hz' hzS
      simp [hzero z' hzS])).symm
  have htsum : (∑' z', (A.physicalKernel true z' z).re) =
      ∑ z' ∈ S, (A.physicalKernel true z' z).re := by
    apply tsum_eq_sum
    intro z' hz'
    simp [hzero z' hz']
  calc
    (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z' z‖) =
        ∑ z' ∈ S, ‖A.physicalKernel true z' z‖ := hsum
    _ = ∑ z' ∈ S, (A.physicalKernel true z' z).re := by
      apply Finset.sum_congr rfl
      intro z' hz'
      exact physicalKernel_true_norm_eq_re A z' z hP
    _ = ∑' z', (A.physicalKernel true z' z).re := htsum.symm

end

theorem AbsolutePhysicalPacketTask_proof :
    Erdos821.S2Core.AbsolutePhysicalPacketTask := by
  change Erdos821.Blueprint.Graph.AbsolutePhysicalBounds
  intro F m C₁
  obtain ⟨Cabs, hSchur⟩ := Erdos821.P3Core.physical_schur_proof F m C₁
  refine ⟨Cabs, ?_⟩
  intro J
  obtain ⟨x₀, hx₀⟩ := hSchur J
  filter_upwards [Filter.eventually_ge_atTop x₀] with x hge
  intro P A hP hmass
  obtain ⟨hrow, hcol⟩ := hx₀ x hge P hP A hmass
  constructor
  · intro z
    rw [physicalKernel_true_row_neighbor_norm_eq_tsum_re A z hP]
    exact hrow z
  · intro z
    rw [physicalKernel_true_column_neighbor_norm_eq_tsum_re A z hP]
    exact hcol z

end Erdos821.S2Packet
