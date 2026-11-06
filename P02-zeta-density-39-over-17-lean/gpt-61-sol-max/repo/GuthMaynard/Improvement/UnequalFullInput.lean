module
import Mathlib
public import GuthMaynard.Improvement.AffineBox
public import GuthMaynard.Improvement.AffineSupportTransfer

@[expose] public section
noncomputable section
open MeasureTheory
open scoped SchwartzMap ContDiff
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- Integer injection induced by g(x)=f(L(x-1)). -/
def supportIndexMap (L : ℕ) (p : ℤ × (ℤ × ℤ)) : ℤ × (ℤ × ℤ) :=
  (p.1,(L:ℤ)*p.2.1,p.2.2+(L:ℤ)*p.2.1)

theorem supportIndexMap_injective {L : ℕ} (hL : 0 < L) : Function.Injective (supportIndexMap L) := by
  intro p q hpq
  have h₁ := congrArg (fun p : ℤ × (ℤ × ℤ) => p.1) hpq
  have h₂ := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.1) hpq
  have h₃ := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.2) hpq
  dsimp only [supportIndexMap] at h₁ h₂ h₃
  have hLi : (L:ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have hq : p.2.1 = q.2.1 := mul_left_cancel₀ hLi h₂
  apply Prod.ext h₁
  apply Prod.ext hq
  simp_all

/-- No Jacobian in u: only the integer denominator and translation change. -/
theorem supportIndexMap_term {L : ℕ} (hL : 0 < L) {f g : ℝ → ℝ}
    (hg : ∀ x, g x = f ((L:ℝ)*(x-1))) (p : ℤ × (ℤ × ℤ)) (hq : p.2.1 ≠ 0) (u : ℝ) :
    gmAffineTerm f p.1 p.2.1 p.2.2 u =
      gmAffineTerm g (supportIndexMap L p).1 (supportIndexMap L p).2.1 (supportIndexMap L p).2.2 u := by
  unfold gmAffineTerm supportIndexMap
  rw [hg]
  congr 1
  push_cast
  field_simp <;> ring


