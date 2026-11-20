module

public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.RecursiveBlockPrograms
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Rank

@[expose] public noncomputable section

namespace OAI.MatrixMultiplication.Arithmetic
open Foundation AuxiliarySeparation Code

/-- Run the larger program with the original entries in its first block and
zero in both tails. Input remapping and constants have no operation cost. -/
theorem pad_program {F : Type*} [Ring F] {n m k : ℕ} (h : n ≤ m) (P : Compiler F m k) :
    ∃ Q : SquareAlgorithm F n, Q.Correct ∧ Q.cost ≤ k := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le h
  let pad (tag : Pos n → Inputs n) (o : Pos (n+l)) : Inputs n ⊕ F :=
    Fin.addCases (fun i => Fin.addCases (fun j => .inl (tag (i,j))) (fun _ => .inr 0) o.2) (fun _ => .inr 0) o.1
  let src := Sum.elim (pad Sum.inl) (pad Sum.inr)
  let val (j : Inputs (n+l)) (x : Inputs n → F) := Sum.elim x id (src j)
  let p : Code F (Inputs n) := ⟨0,.nil⟩
  obtain ⟨q,hq,ho⟩ := (Build.sources p src).bind fun q _ hv => P q val hv
  choose out hout using ho
  let o (i : Fin n) := Fin.castAdd l i
  refine ⟨⟨_,q.prog,fun i j => out (o i,o j)⟩, ?_, by simpa [MatrixAlgorithm.cost, p, Program.cost] using hq.cost⟩
  intro A B; funext i j
  exact (congrFun (hout (o i,o j)) (matrixInputs A B)).trans (by
    simp [entry, Fin.sum_univ_add, Finset.sum_apply, val, src, pad, o, matrixInputs, Matrix.mul_apply])

end OAI.MatrixMultiplication.Arithmetic

namespace OAI.MatrixMultiplication.AuxiliarySeparation.Integral
open Arithmetic
universe u

/-- Choose one block at half the requested slack. Its rank is strictly less
than the target growth factor, so a fixed constant absorbs the quadratic
wiring cost in every recursive call. Pad to the next block power. -/
theorem exactRankExponent_int_admissible (F : Type u) [Ring F] : AdmissibleExponent F (exactRankExponent ℤ) := by
  intro ε hε
  let τ := exactRankExponent ℤ
  have hτ : 2 ≤ τ := exactRankExponent_lower
  obtain ⟨b,r,hb,hr,hrank⟩ := finite_blocks (lt_add_of_pos_right τ (half_pos hε))
  let s := τ+ε
  let q := (b:ℝ)^s
  let w := 6*r*(b:ℝ)^2
  have hb₁ : (1:ℝ) < b := by aesop
  have hgap : (r:ℝ) < q := hr.trans_lt (by aesop)
  have hquad : (b:ℝ)^2 ≤ q := by
    rw [← Real.rpow_two]; bound
  obtain ⟨N,hN⟩ := exists_lt_nsmul (sub_pos.mpr hgap) w
  let C := (N:ℝ)+1
  have hc : r*C + w ≤ C*q := by dsimp [C]; rw [nsmul_eq_mul] at hN; nlinarith
  have hpow (j : ℕ) : ∃ k : ℕ, Compiler F (b^j) k ∧ (k:ℝ) ≤ C*q^j := by
    induction j with
    | zero => exact ⟨1,scalarCompiler,by simp [C]⟩
    | succ j ih =>
      obtain ⟨k,P,hcost⟩ := ih
      rw [pow_succ']; refine ⟨_,blockCompiler hrank P,?_⟩
      have hw : ((b:ℝ)^j)^2 ≤ q^j := by rw [← pow_mul, Nat.mul_comm j, pow_mul]; gcongr
      calc
        _ = r*(k:ℝ)+w*((b:ℝ)^j)^2 := by push_cast; rfl
        _ ≤ r*(C*q^j)+w*q^j := by gcongr
        _ ≤ _ := by rw [pow_succ]; nlinarith
  refine ⟨C*q, by positivity, fun n hn => ?_⟩
  obtain ⟨j, hj, hn'⟩ := exists_nat_pow_near hn (by omega : 1 < b)
  obtain ⟨k,P,hp⟩ := hpow (j+1)
  obtain ⟨Q,hQ,hqp⟩ := pad_program hn'.le P
  refine ⟨Q,hQ,(Nat.cast_le.mpr hqp).trans (hp.trans ?_)⟩
  rw [pow_succ']; ring_nf
  have hj' := Real.rpow_le_rpow (by positivity) (Nat.cast_le (α := ℝ) |>.mpr hj) (show 0 ≤ s by dsimp [s]; linarith)
  rw [Nat.cast_pow, ← Real.rpow_pow_comm (by positivity)] at hj'
  gcongr

end OAI.MatrixMultiplication.AuxiliarySeparation.Integral
