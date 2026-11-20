module

public import Erdos821.P3Clean.Structure
public import Erdos821.P3Clean.Contractions

/-! The damping factors of a literal clean edge. -/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {P : PrimeGroups} {F : FixedData}

def pendingDamping {M : ℕ} (rho : ℝ) (s : P.MemoryState M) : ℝ :=
  rho ^ (∑ g : P.BigGroup, (zeroMemoryIndices (s.2.2 g)).card)

theorem pendingDamping_nonneg {M : ℕ} (r : MemoryParameters F) (s : P.MemoryState M) :
    0 ≤ pendingDamping r.rho s := pow_nonneg r.rho_pos.le _

theorem pendingDamping_le_one {M : ℕ} (r : MemoryParameters F) (s : P.MemoryState M) :
    pendingDamping r.rho s ≤ 1 := pow_le_one₀ r.rho_pos.le r.rho_lt.le

theorem rawEdgeWeight_rho {J m : ℕ} (A : Model F P J m) (n : ℕ) (rho : ℝ)
    (ν : Pattern P J F.ell m) (u : P.Aux J)
    (s t : P.MemoryState (J + F.ell)) (c : TransferChoice s) :
    rawEdgeWeight A n rho ν u s t c =
      pendingDamping rho s * rawEdgeWeight A n 1 ν u s t c * pendingDamping rho t := by
  simp only [rawEdgeWeight, one_pow, mul_one, pendingDamping, pow_add]
  ring

theorem edgeChoiceCoefficient_rho {J m : ℕ} (A : Model F P J m) (n : ℕ)
    (rho theta : ℝ) (i : Fin n) (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) :
    edgeChoiceCoefficient A n rho theta i s t c =
      (pendingDamping rho s : ℂ) * edgeChoiceCoefficient A n 1 theta i s t c *
        (pendingDamping rho t : ℂ) := by
  simp only [edgeChoiceCoefficient]
  rw [rawEdgeWeight_rho A n rho (A.pattern c.2.2.1) c.2.2.2.1
    (permuteActive c.1 s) (permuteActive c.2.1 t) c.2.2.2.2]
  simp only [Complex.ofReal_mul]
  change ((pendingDamping rho s : ℂ) * _ * (pendingDamping rho t : ℂ)) * _ * _ = _
  ring

theorem memoryEdgeKernel_rho {J m : ℕ} (A : Model F P J m) (n : ℕ)
    (rho theta : ℝ) (i : Fin n) (mode : TransferMode)
    (phi : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ)
    (s t : P.MemoryState (J + F.ell)) :
    memoryEdgeKernel A n rho theta i mode phi s t =
      (pendingDamping rho s : ℂ) * memoryEdgeKernel A n 1 theta i mode phi s t *
        (pendingDamping rho t : ℂ) := by
  classical
  have hc (c : EdgeChoice A s) :
      (if edgeChoiceValid A mode i s t c then
        edgeChoiceCoefficient A n rho theta i s t c * phi s t c else 0) =
      (pendingDamping rho s : ℂ) *
        (if edgeChoiceValid A mode i s t c then
          edgeChoiceCoefficient A n 1 theta i s t c * phi s t c else 0) *
        (pendingDamping rho t : ℂ) := by
    by_cases h : edgeChoiceValid A mode i s t c
    · rw [ite_eq_left h, ite_eq_left h, edgeChoiceCoefficient_rho]
      ring
    · simp only [ite_eq_right h, mul_zero, zero_mul]
  simp only [memoryEdgeKernel]
  simp_rw [hc]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem memoryMass_nonneg (J n : ℕ)
    (hV : ∀ g, 0 < P.V g)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (s : P.MemoryState (J + F.ell)) : 0 ≤ P.memoryMass F J n s := by
  classical
  have ht (g : P.BigGroup) (p : P.Prime g.val) : 0 ≤ tiltedMu F P n g.val p := by
    unfold tiltedMu
    apply inv_nonneg.mpr
    exact (mul_pos (mul_pos (hV g.val)
      (by exact_mod_cast (P.prime g.val p.val p.property).pos)) (hb g p)).le
  have hg (g : P.BigGroup) : 0 ≤ P.groupMemoryMass F n g.val (s.2.2 g) := by
    unfold PrimeGroups.groupMemoryMass
    apply div_nonneg
    · apply Multiset.prod_nonneg
      intro z hz
      obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hz
      exact ht g p.1
    · positivity
  unfold PrimeGroups.memoryMass
  split_ifs
  · apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · exact Finset.prod_nonneg (fun g _ => zpow_nonneg (hV g.val).le _)
      · exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => ht g _))
    · exact Finset.prod_nonneg (fun g _ => hg g)
  · exact le_refl 0

end Erdos821.P3Clean
