module

public import Glennie.Compact.LocalContrast

/- Deterministic robustness of the six raw scalar readouts. -/
@[expose] public section
namespace Glennie.Compact.ReadoutRobustnessR01
open Glennie Glennie.Compact.Affine20 Glennie.Compact.Sections
open Glennie.Compact.OperationalPhi
noncomputable section

/-- Six scalars in native order: h+, h-, x+, x-, 1+, 1-. -/
structure Readouts where
  hPlus : ℝ
  hMinus : ℝ
  xPlus : ℝ
  xMinus : ℝ
  onePlus : ℝ
  oneMinus : ℝ

def weightedScore (r : Readouts) : ℝ :=
  4 * r.hPlus - 4 * r.hMinus - r.xPlus + r.xMinus - r.onePlus + r.oneMinus

def rawPlus (x y z a : Albert) : ℝ :=
  inner z (U y (U x (U z (U a y))))

def rawMinus (x y z a : Albert) : ℝ :=
  inner z (U x (U y (U z (U a y))))

def exactReadouts (T : Triple) : Readouts :=
  let x := encoder (T 0)
  let y := encoder (T 1)
  let z := encoder (T 2)
  ⟨rawPlus x y z (halfAmplitude x), rawMinus x y z (halfAmplitude x),
   rawPlus x y z x, rawMinus x y z x, rawPlus x y z 1, rawMinus x y z 1⟩

def ErrorsAtMost (noisy exact : Readouts) (ε : ℝ) : Prop :=
  |noisy.hPlus - exact.hPlus| ≤ ε ∧
  |noisy.hMinus - exact.hMinus| ≤ ε ∧
  |noisy.xPlus - exact.xPlus| ≤ ε ∧
  |noisy.xMinus - exact.xMinus| ≤ ε ∧
  |noisy.onePlus - exact.onePlus| ≤ ε ∧
  |noisy.oneMinus - exact.oneMinus| ≤ ε

theorem weightedScore_exact (T : Triple) :
    weightedScore (exactReadouts T) = LocalContrast.score T := by
  simp only [weightedScore, exactReadouts, LocalContrast.score, delta, contrast,
    inner_sub_right, rawPlus, rawMinus]
  ring

theorem weightedScore_eq_two_phi (T : Triple) :
    weightedScore (exactReadouts T) = 2 * phiOf T := by
  rw [weightedScore_exact, LocalContrast.score_eq_two_phi]

/-- Deterministic coefficient bound; independence and positivity are unnecessary. -/
theorem weightedScore_error (noisy exact : Readouts) (ε : ℝ)
    (h : ErrorsAtMost noisy exact ε) :
    |weightedScore noisy - weightedScore exact| ≤ 12 * ε := by
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
  rcases abs_le.mp h₀ with ⟨l₀, u₀⟩
  rcases abs_le.mp h₁ with ⟨l₁, u₁⟩
  rcases abs_le.mp h₂ with ⟨l₂, u₂⟩
  rcases abs_le.mp h₃ with ⟨l₃, u₃⟩
  rcases abs_le.mp h₄ with ⟨l₄, u₄⟩
  rcases abs_le.mp h₅ with ⟨l₅, u₅⟩
  apply abs_le.mpr
  dsimp [weightedScore]
  constructor <;> linarith

def noisyPhi (noisy : Readouts) : ℝ := weightedScore noisy / 2
variable (T : Triple) (noisy : Readouts)
include T noisy in

theorem phi_error  (ε : ℝ)
    (h : ErrorsAtMost noisy (exactReadouts T) ε) :
    |noisyPhi noisy - phiOf T| ≤ 6 * ε := by
  have hb := weightedScore_error noisy (exactReadouts T) ε h
  rw [weightedScore_eq_two_phi] at hb
  rcases abs_le.mp hb with ⟨hl, hu⟩
  apply abs_le.mpr
  dsimp [noisyPhi]
  constructor <;> linarith
include T noisy in

theorem positive_certificate  (ε : ℝ)
    (h : ErrorsAtMost noisy (exactReadouts T) ε)
    (hp : 12 * ε < weightedScore noisy) : 0 < phiOf T := by
  have hb := weightedScore_error noisy (exactReadouts T) ε h
  rw [weightedScore_eq_two_phi] at hb
  have hu := (abs_le.mp hb).2
  linarith
include T noisy in

theorem negative_certificate  (ε : ℝ)
    (h : ErrorsAtMost noisy (exactReadouts T) ε)
    (hn : weightedScore noisy < -(12 * ε)) : phiOf T < 0 := by
  have hb := weightedScore_error noisy (exactReadouts T) ε h
  rw [weightedScore_eq_two_phi] at hb
  have hl := (abs_le.mp hb).1
  linarith
include T noisy in

/-- A posteriori strict sign certificate for the actual ordered triple. -/
theorem sign_certificate  (ε : ℝ)
    (hε : 0 ≤ ε) (h : ErrorsAtMost noisy (exactReadouts T) ε)
    (hm : 12 * ε < |weightedScore noisy|) :
    (weightedScore noisy < 0 ∧ phiOf T < 0) ∨
    (0 < weightedScore noisy ∧ 0 < phiOf T) := by
  rcases le_total 0 (weightedScore noisy) with hp | hn
  · rw [abs_of_nonneg hp] at hm
    exact Or.inr ⟨by linarith, positive_certificate T noisy ε h hm⟩
  · rw [abs_of_nonpos hn] at hm
    have hm' : weightedScore noisy < -(12 * ε) := by linarith
    exact Or.inl ⟨by linarith, negative_certificate T noisy ε h hm'⟩

end
end Glennie.Compact.ReadoutRobustnessR01
