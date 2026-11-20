module
public import GS.Core
public import GS.Isometric.Pack
@[expose] public section
noncomputable section
open Matrix GS.Isometric
namespace GS.M4
def P : Mat 6 := !![1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0;
  0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1]

abbrev slots : Fin 2 × Fin 3 ≃ Fin 6 := (Equiv.prodComm ..).trans finProdFinEquiv
abbrev load {𝕜 : Type*} [RCLike 𝕜] := pack (𝕜 := 𝕜) slots
lemma load_apply {𝕜} [RCLike 𝕜] (B : Fin 3 → Square 𝕜 2) (i j : Fin 6) :
    load B i j = if (@Fin.divNat 3 2 i : Fin 3) = (@Fin.divNat 3 2 j) then B (@Fin.divNat 3 2 i) (@Fin.modNat 3 2 i) (@Fin.modNat 3 2 j) else 0 := rfl
lemma load_supported {𝕜} [RCLike 𝕜] (B : Fin 3 → Square 𝕜 2) : DiagonalBlocks 2 (load B) := pack_supported slots (fun _ => rfl) B

variable {𝕜 : Type*} [RCLike 𝕜]
abbrev wiring (𝕜 : Type*) [RCLike 𝕜] := P.map (algebraMap ℝ 𝕜)
abbrev rowWire := (![0,2,4,1,3,5] : Fin 6 → Fin 6)
abbrev colWire := (![0,3,1,4,2,5] : Fin 6 → Fin 6)
lemma wire_left (A : Square 𝕜 6) (i j) : (wiring 𝕜*A) i j = A (rowWire i) j := by
  fin_cases i <;> simp [wiring,P,mul_apply,Fin.sum_univ_succ,rowWire]
lemma wire_right (A : Square 𝕜 6) (i j) : (A*wiring 𝕜) i j = A i (colWire j) := by
  fin_cases j <;> simp [wiring,P,mul_apply,Fin.sum_univ_succ,colWire]
def route (W Y : Square 𝕜 6) := wiring 𝕜*W*wiring 𝕜*Y*wiring 𝕜
lemma route_apply (W Y : Square 𝕜 6) (i j) : route W Y i j = ∑ k, W (rowWire i) (colWire k) * Y k (colWire j) := by
  rw [route,wire_right,mul_apply]; simp only [wire_right,wire_left]

abbrev minor {𝕜} [RCLike 𝕜] (A : Square 𝕜 6) (i j : Fin 3) := (readBlock slots A i j).det
lemma minor_apply (A : Square 𝕜 6) (i j : Fin 3) : minor A i j =
    A (![0,2,4] i) (![0,2,4] j) * A (![1,3,5] i) (![1,3,5] j) -
    A (![0,2,4] i) (![1,3,5] j) * A (![1,3,5] i) (![0,2,4] j) := by
  rw [minor,det_fin_two]; fin_cases i <;> fin_cases j <;> rfl
@[simp] lemma wiring_real : wiring ℝ = P := by ext; simp [wiring]
abbrev minors {𝕜} [RCLike 𝕜] (A : Square 𝕜 6) (i j : Fin 3) := ‖minor A i j‖
def Bound (d : Fin 3 → Fin 3 → ℝ) := d 0 0 * d 2 2 ≤ d 1 1 * (1-d 0 2)^2
end GS.M4
