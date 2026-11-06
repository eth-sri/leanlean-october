/- Rational 1+9+16 fixed-frame coordinates on the actual compact trace kernel.
The scaled metric is explicit; no inner-product instance is installed. -/
module
public import Mathlib.Tactic.Simps.Basic

public import AlbertRecognition.Reference
public import AlbertRecognition.FixedFrame.SpinCommutant

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie

abbrev FrameCoordinates := ℝ × ℝ × Octonion × Spin

/-- Complementary diagonal direction d=e1-e2 for the zero-based frame. -/
def frameD : V := ⟨⟨0, 1, -1, 0, 0, 0⟩, by
  change (0 : ℝ) + 1 + (-1) = 0
  norm_num⟩

/-- The ordered spin pair is the actual upper-slot pair (01,02). -/
@[simps! apply] def frameSpin : Spin →ₗ[ℝ] V :=
  X01.comp (LinearMap.fst ℝ Octonion Octonion) +
    X02.comp (LinearMap.snd ℝ Octonion Octonion)



/-- Exact rational coordinates (alpha,beta,slot12,(slot01,slot02)). -/
def frameCoordinates : V ≃ₗ[ℝ] FrameCoordinates where
  toFun x :=
    (-(x : Albert).d0 / 2, ((x : Albert).d1 - (x : Albert).d2) / 2,
      (x : Albert).o12, ((x : Albert).o01, (x : Albert).o02))
  invFun c :=
    ⟨⟨-2*c.1, c.1+c.2.1, c.1-c.2.1,
      c.2.2.2.1, c.2.2.2.2, c.2.2.1⟩, by
      change -2*c.1 + (c.1+c.2.1) + (c.1-c.2.1) = 0
      ring⟩
  left_inv x := by
    have ht := trace_V x
    change (x : Albert).d0 + (x : Albert).d1 + (x : Albert).d2 = 0 at ht
    apply Subtype.ext
    ext <;> dsimp <;> linarith
  right_inv c := by ext <;> dsimp <;> ring
  map_add' x y := by ext <;> simp <;> ring
  map_smul' r x := by ext <;> simp [smul_eq_mul] <;> ring

def frameEmbed : FrameCoordinates →ₗ[ℝ] V := frameCoordinates.symm.toLinearMap

/-- Actual 1+1+8+16 block decomposition, rather than a spanning assumption. -/
theorem frameEmbed_eq (a b : ℝ) (z : Octonion) (s : Spin) :
    frameEmbed (a,b,z,s) = a • h 0 + b • frameD + X12 z + frameSpin s := by
  rcases s with ⟨u,v⟩
  apply Subtype.ext
  apply Albert.ext <;>
    simp [frameEmbed, frameCoordinates, h, e, frameD, frameSpin,
      X01, X02, X12] <;> ring

theorem frame_decompose (x : V) :
    x = (frameCoordinates x).1 • h 0 + (frameCoordinates x).2.1 • frameD +
      X12 (frameCoordinates x).2.2.1 + frameSpin (frameCoordinates x).2.2.2 := by
  calc
    x = frameEmbed (frameCoordinates x) := (frameCoordinates.symm_apply_apply x).symm
    _ = _ := frameEmbed_eq (frameCoordinates x).1 (frameCoordinates x).2.1
      (frameCoordinates x).2.2.1 (frameCoordinates x).2.2.2

end
end AlbertRecognition.FixedFrame
