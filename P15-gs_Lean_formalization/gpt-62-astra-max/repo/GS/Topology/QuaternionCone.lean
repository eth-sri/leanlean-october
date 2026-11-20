module
public import GS.Topology.ConeRetract
public import Mathlib.Analysis.Quaternion
@[expose] public section

/-! Pack each row in quaternion coordinates. On a rank-one matrix the
Clifford contraction is simply left multiplication by a single quaternion.
There are no extra zeros because the quaternions have no zero divisors. -/
noncomputable section
open Matrix GS.Local
open scoped Quaternion
set_option backward.isDefEq.respectTransparency false
namespace GS.RankLocus
variable {d k : ℕ} (h : (Fin d → ℝ) ≃L[ℝ] (Fin k → ℍ))
local notation "I₁" => (⟨0,1,0,0⟩ : ℍ)
local notation "I₂" => (⟨0,0,1,0⟩ : ℍ)
def contract (X : Locus 3 (Fin d)) : Fin k → ℍ := fun j => h (X.val 0) j + I₁ * h (X.val 1) j + I₂ * h (X.val 2) j
lemma contract_outer (u : Fin 3 → ℝ) (v : Fin d → ℝ) (j : Fin k) :
    contract h (outer u v) j = (⟨u 0,u 1,u 2,0⟩ : ℍ) * h v j := by
  have row (i) : (outer u v).val i = u i • v := rfl
  simp only [contract,row,map_smul,Pi.smul_apply]
  have hc : (⟨u 0,u 1,u 2,0⟩ : ℍ) = u 0 • (1:ℍ) + u 1 • I₁ + u 2 • I₂ := by ext <;> simp
  rw [hc]; noncomm_ring

def quatRetract : Retract (tip : Locus 3 (Fin d)) (Fin k → ℍ) where
  project := ⟨contract h,by
    apply continuous_pi; intro j
    have hc (i : Fin 3) : Continuous (fun X : Locus 3 (Fin d) => h (X.val i) j) := (continuous_apply j).comp (h.continuous.comp (continuous_row i))
    exact ((hc 0).add (continuous_const.mul (hc 1))).add (continuous_const.mul (hc 2))⟩
  lift := ⟨fun z => outer ![1,0,0] (h.symm z),by apply Continuous.subtype_mk; unfold vecMulVec; fun_prop⟩
  cancel z := funext fun j => (contract_outer h _ _ j).trans (by change (1:ℍ) * h (h.symm z) j = _; simp)
  isolated X := by
    constructor
    · obtain ⟨u,v,rfl⟩ := factors X
      intro hz; by_cases H : (⟨u 0,u 1,u 2,0⟩ : ℍ) = 0
      · have hu : u = 0 := by ext i; fin_cases i <;> first | exact congrArg QuaternionAlgebra.re H | exact congrArg QuaternionAlgebra.imI H | exact congrArg QuaternionAlgebra.imJ H
        simp [hu]
      · have hv : h v = 0 := funext fun j => (mul_eq_zero.mp ((contract_outer h u v j).symm.trans (congrFun hz j))).resolve_left H
        simp [(map_eq_zero_iff h h.injective).mp hv]
    · rintro rfl; funext j; change h 0 j + I₁ * h 0 j + I₂ * h 0 j = _; simp

theorem three_row_bad (e d : ℕ) (hd : 0<d) (hdiv : 4∣d) : ¬Euclidean ((0,tip) : Space e 3 (Fin d)) := by
  obtain ⟨k,rfl⟩ := hdiv
  let h : (Fin (4*k) → ℝ) ≃L[ℝ] (Fin k → ℍ) := .ofFinrankEq (by simp [Module.finrank_pi_fintype,Quaternion.finrank_eq_four,Nat.mul_comm])
  apply obstruction (quatRetract h) e 1; rintro t ht ⟨z,hz⟩
  have eq := congrArg (fun X : Locus 3 (Fin (4*k)) => X.val 1 ⟨0,hd⟩) hz
  change 0 * _ = 1*t at eq; linarith
end GS.RankLocus
