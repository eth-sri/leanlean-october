module

public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Builder
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.Basic

@[expose] public noncomputable section

namespace OAI.MatrixMultiplication.Arithmetic
open Foundation AuxiliarySeparation Code
variable {F : Type*} [Ring F] {n r m : ℕ}

abbrev Scheme (n r : ℕ) := Fin r → Pos n → ℤ

/-- Integer scalars act centrally even when the input ring is noncommutative. -/
private theorem contract (a b c : Scheme n r)
    (h : ∀ x y z, squareTensor ℤ n x y z =
      ∑ q, a q x * b q y * c q z) (l g : Pos n → F) (i k : Fin n) :
    (∑ q, c q (k,i) • ((∑ x, a q x • l x)*(∑ y, b q y • g y))) =
      ∑ j,l (i,j)*g (j,k) := by
  simp only [Finset.smul_sum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  calc
    _ = ∑ y, ∑ x, (∑ q, a q x * b q y * c q (k,i)) • (l x * g y) := by
      simp only [Finset.sum_smul]; tensor_sums
    _ = _ := by simp [← h, squareTensor, Fintype.sum_prod_type, ite_and, ite_smul]

private abbrev join (x : Fin n) (y : Fin m) : Fin (n*m) := finProdFinEquiv (x,y)
private def blockWire (x : Pos n) : Inputs m → Inputs (n*m) :=
  let f := Prod.map (join x.1) (join x.2)
  Sum.map f f

/-- Three program stages: wire the two linear input maps, run `r` copies of
the inner compiler, and combine the product blocks. The middle stage costs
`r*k`, and each of the two linear stages touches O(m²) entries per block. -/
theorem blockCompiler
    (hr : Tensor.RankAtMost (squareTensor ℤ n) r)
    {k : ℕ} (rec : Compiler F m k) : Compiler F (n*m) (r*k + 6*r*n^2*m^2) := by
  classical
  intro I p v hv
  obtain ⟨a,b,c,hr⟩ := hr
  let coeff (q : Fin r) : Inputs m → Pos n → ℤ := Sum.elim (fun _ => a q) (fun _ => b q)
  let input (t : Fin r × Inputs m) x := v (blockWire x t.2)
  let V := Build.linearForms input (fun t => coeff t.1 t.2)
  let H (j : Fin r) := entry (fun t => V (j,t))
  let split := (finProdFinEquiv (m := n) (n := m)).symm
  let products (o : Pos (n*m)) (j : Fin r) := H j ((split o.1).2,(split o.2).2)
  let weights (o : Pos (n*m)) (j : Fin r) := c j ((split o.2).1,(split o.1).1)
  let W := Build.linearForms products weights
  have correct : W = entry v := by
    funext ⟨i,k⟩
    simp only [W, Build.linearForms, products, weights, H, entry, Finset.smul_sum]
    rw [Finset.sum_comm]
    dsimp [V, Build.linearForms, input, coeff, blockWire]
    simp_rw [contract a b c hr]
    rw [Finset.sum_comm]
    have hj (l : Fin (n*m)) : join (split l).1 (split l).2 = l := finProdFinEquiv.apply_symm_apply l
    simpa [Fintype.sum_prod_type, hj] using finProdFinEquiv.sum_comp (fun j => v (.inl (i,j)) * v (.inr (j,k)))
  rw [← correct]
  have build := Build.forms input (fun t => coeff t.1 t.2) (fun t x => hv _)
  convert build.bind (fun q _ hV => (Build.batch (fun j s => ∀ o, H j o ∈ s) (fun _ _ _ h hg i => h (hg i))
    (fun j t hq => rec t (fun i => V (j,i)) (fun i => hq (hV (j,i))))).bind
      (fun t _ hH => Build.forms products weights (fun o j => hH j _))) using 1
  simp; ring

end OAI.MatrixMultiplication.Arithmetic
