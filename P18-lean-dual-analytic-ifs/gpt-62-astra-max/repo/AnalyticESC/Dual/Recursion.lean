module
public import AnalyticESC.Dual.Derivatives

@[expose] public section
namespace AnalyticESC
open Set Metric

/-- Real coordinate distortion, viewed as a complex-valued function. -/
noncomputable def D (g : ℝ → ℝ) (x : ℝ) : ℂ := (logDer g x : ℝ)

/-- A bounded error dominated by a strict contraction cannot be positive. -/
theorem contraction_estimate {α : Type*} {E : α → ℝ} {q : ℝ} (hq : 0 ≤ q) (hlt : q < 1)
    (hb : BddAbove (range E)) (step : ∀ x, ∃ y, E x ≤ q * E y) (x : α) :
    E x ≤ 0 := by
  have : Nonempty α := ⟨x⟩
  have h : (⨆ y, E y) ≤ q * (⨆ y, E y) := by
    apply ciSup_le; intro z
    obtain ⟨y,hy⟩ := step z
    exact hy.trans (by gcongr; exact le_ciSup hb y)
  exact (le_ciSup hb x).trans (by nlinarith)

namespace IFS
variable {N : ℕ} (Φ : IFS N)

/-- Block recursion for real restrictions of projections. -/
def Rec (a : Letters N) (H K : ℝ → ℂ) := EqOn H
  (fun x => logDer (Φ.comp a) x + deriv (Φ.comp a) x * K (Φ.R a x)) I

lemma rec_block (w : Address N) (m : ℕ) : Φ.Rec (block m w).reverse (Φ.P w) (Φ.P (shift m w)) := by
  intro x hx; dsimp only [P,R]; rw [← Φ.comp_ofReal _ hx]
  simpa only [ENat.top_sub_natCast] using Φ.expand ⊤ w (m := m) le_top (Φ.closedReal hx)

lemma head_rec (w : Address N) : Φ.Rec [w 0] (Φ.P w) (Φ.P (shift 1 w)) := by
  simpa [block,pref] using Φ.rec_block w 1

/-- Action of a letter on a point of the real interval. -/
noncomputable def next (i : Fin N) (x : I) : I := ⟨_,(Φ.inClass i).re_mem_I x x.2⟩

end IFS
end AnalyticESC
