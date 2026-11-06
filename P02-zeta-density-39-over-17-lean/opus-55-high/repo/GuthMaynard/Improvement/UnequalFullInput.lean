module
public import GuthMaynard.Improvement.AffineBox
public import GuthMaynard.Improvement.AffineSupportTransfer

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap ContDiff
namespace GuthMaynard.Improvement
open GuthMaynard.NativeMoment

/-- Integer injection induced by g(x)=f(L(x-1)). -/
def supportIndexMap (L : ℕ) (p : ℤ × (ℤ × ℤ)) : ℤ × (ℤ × ℤ) :=
  (p.1,(L:ℤ)*p.2.1,p.2.2+(L:ℤ)*p.2.1)

section
variable {L : ℕ} (hL : 0 < L)
include L hL
theorem supportIndexMap_injective : Function.Injective (supportIndexMap L) := by
  intro p q hpq
  have h₁ := congrArg (fun p : ℤ × (ℤ × ℤ) => p.1) hpq
  have h₂ := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.1) hpq
  have h₃ := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.2) hpq
  dsimp only [supportIndexMap] at h₁ h₂ h₃
  have hLi : (L:ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have hq : p.2.1 = q.2.1 := mul_left_cancel₀ hLi h₂
  apply Prod.ext h₁
  apply Prod.ext hq
  rw [hq] at h₃
  exact add_right_cancel h₃

/-- No Jacobian in u: only the integer denominator and translation change. -/
theorem supportIndexMap_term {f g : ℝ → ℝ}
    (hg : ∀ x, g x = f ((L:ℝ)*(x-1))) (p : ℤ × (ℤ × ℤ)) (hq : p.2.1 ≠ 0) (u : ℝ) :
    gmAffineTerm f p.1 p.2.1 p.2.2 u =
      gmAffineTerm g (supportIndexMap L p).1 (supportIndexMap L p).2.1 (supportIndexMap L p).2.2 u := by
  unfold gmAffineTerm supportIndexMap
  rw [hg]
  congr 1
  push_cast
  have hLr : (L:ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hqr : (p.2.1:ℝ) ≠ 0 := by exact_mod_cast hq
  field_simp [hLr,hqr]
  ring
end

end GuthMaynard.Improvement
