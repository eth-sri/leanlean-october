module
public import GS.M4Data
public import GS.Isometric.Layers
public import Mathlib.Analysis.CStarAlgebra.Basic
@[expose] public section

/-! Only four of the two-by-two minors are needed. Outer unitary blocks
preserve their determinant moduli. For the remaining core, the product of the
opposite corner moduli is the central modulus times a square; Cauchy-Schwarz
on two unit rows bounds the square. No division or nonzero premise is needed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open Matrix GS.Isometric
namespace GS.M4
variable {𝕜 : Type*} [RCLike 𝕜]
local notation "A" => Square 𝕜 6
local notation "B" => Fin 3 → Square 𝕜 2
local notation "p" => wiring 𝕜
private def innerNet (W Y : B) := route (load W) (load Y)

private lemma col (U : Square 𝕜 2) (h : IsU U) (j : Fin 2) : ‖U 0 j‖^2 + ‖U 1 j‖^2 = 1 := by
  simpa [mul_apply,conjTranspose_apply,RCLike.star_def,RCLike.conj_mul,Fin.sum_univ_two] using congrArg RCLike.re (congrFun (congrFun h.1 j) j)
private lemma row (U : Square 𝕜 2) (h : IsU U) : ‖U 0 0‖^2 + ‖U 0 1‖^2 = 1 := by simpa [conjTranspose_apply] using col _ h.conjTranspose 0
private lemma off {U : Square 𝕜 2} (h : IsU U) : ‖U 1 0‖ = ‖U 0 1‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp; linarith [col U h 0,row U h]

private lemma core_bound (W Y : B) (u : ∀ i, IsU (W i)) (v : ∀ i, IsU (Y i)) : Bound (minors (innerNet W Y)) := by
  let a i := ‖W i 0 0‖; let b i := ‖W i 0 1‖; let c i := ‖Y i 0 0‖; let f i := ‖Y i 0 1‖
  let m := minors (innerNet W Y)
  have w (i) := off (u i); have y (i) := off (v i)
  have table : m 0 0 = b 0*b 1*f 1*f 0 ∧ m 2 2 = b 1*b 2*f 2*f 1 ∧ m 1 1 = b 2*b 0*f 0*f 2 ∧ m 0 2 = a 1*b 0*c 1*f 2 := by
    refine ⟨?_,?_,?_,?_⟩ <;> norm_num [m,minors,minor_apply,innerNet,route_apply,colWire,rowWire,load_apply,Fin.divNat,Fin.modNat,Fin.sum_univ_succ] <;>
      (conv_lhs => arg 1; ring_nf) <;> simp [norm_mul,w,y,a,b,c,f] <;> ring
  obtain ⟨e₀,e₁,e₂,e₃⟩ := table
  have h : m 0 2 ≤ a 1*c 1 := by
    rw [e₃]; calc a 1*b 0*c 1*f 2 ≤ a 1*1*c 1*1 := by dsimp [a,b,c,f]; gcongr <;> solve_by_elim [entry_bound]
                 _ = _ := by ring
  have h' : b 1*f 1 ≤ 1-m 0 2 := by
    dsimp [a,b,c,f] at h ⊢; nlinarith [row _ (u 1),row _ (v 1),sq_nonneg (a 1-c 1),sq_nonneg (b 1-f 1)]
  change m 0 0 * m 2 2 ≤ _
  calc m 0 0*m 2 2 = m 1 1*(b 1*f 1)^2 := by rw [e₀,e₁,e₂]; ring
       _ ≤ m 1 1*(1-m 0 2)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h' _) (norm_nonneg _)

private lemma outer (L R : B) (M : A) (l : ∀ i, IsU (L i)) (r : ∀ i, IsU (R i)) :
    minors (load L*M*load R) = minors M := by
  funext i j
  have eq : readBlock slots (load L*M*load R) i j = L i * readBlock slots M i j * R j := by
    simp [read_mul,ite_mul,mul_ite]
  simp [minors,minor,eq,norm_mul,CStarRing.norm_of_mem_unitary (det_of_mem_unitary (l i)),CStarRing.norm_of_mem_unitary (det_of_mem_unitary (r j))]

lemma necessary {L W Y R : A} (sL : DiagonalBlocks 2 L) (sW : DiagonalBlocks 2 W) (sY : DiagonalBlocks 2 Y) (sR : DiagonalBlocks 2 R)
    (uL : IsU L) (uW : IsU W) (uY : IsU Y) (uR : IsU R) : Bound (minors (L*p*W*p*Y*p*R)) := by
  have h := packed (𝕜 := 𝕜) slots (fun _ => rfl)
  obtain ⟨L,l,rfl⟩ := (h _).1 ⟨sL,uL⟩; obtain ⟨R,r,rfl⟩ := (h _).1 ⟨sR,uR⟩
  obtain ⟨W,u,rfl⟩ := (h _).1 ⟨sW,uW⟩; obtain ⟨Y,v,rfl⟩ := (h _).1 ⟨sY,uY⟩
  rw [show load L*p*load W*p*load Y*p*load R = load L*innerNet W Y*load R by simp [innerNet,route,mul_assoc], outer _ _ _ l r]
  exact core_bound W Y u v
end GS.M4
