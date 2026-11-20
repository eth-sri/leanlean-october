module

public import OAI.LinearAlgebra.MatrixMultiplication.Model
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Matrix.Composition
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

public section

@[expose] section

namespace OAI.MatrixMultiplication.Arithmetic

noncomputable section

open Foundation

variable {F I J U V : Type*} [Ring F]

namespace Program

omit [Ring F] in
theorem cost_le_registers {r : ℕ} (p : Program F I r) : p.cost ≤ r := by
  induction p with
  | nil => exact le_rfl
  | step p g ih => cases g <;> simp [Program.cost, Gate.cost] <;> omega

end Program

private abbrev Pair (n : ℕ) := Fin n × Fin n
private abbrev Square (F : Type*) (n : ℕ) := Matrix (Fin n) (Fin n) F
private abbrev Input (n : ℕ) := MatrixInput n n n

/-- Translate register names and replace inputs by single gates. -/
def Gate.subst (w : J → Gate F I V) (v : U → V) : Gate F J U → Gate F I V
  | .input j => w j
  | .constant c => .constant c
  | .add i j => .add (v i) (v j)
  | .sub i j => .sub (v i) (v j)
  | .mul i j => .mul (v i) (v j)

@[simp] theorem Gate.eval_subst (w : J → Gate F I V) (v : U → V) (g : Gate F J U)
    (x : I → F) (a : V → F) : (g.subst w v).eval x a =
      g.eval (fun j => (w j).eval x a) (fun i => a (v i)) := by cases g <;> rfl

namespace Program

variable {r s : ℕ}

abbrev oldOutput (s : ℕ) (i : Fin r) : Fin (r+s) := i.addNat s
abbrev newOutput (r : ℕ) (i : Fin s) : Fin (r+s) := i.castLE (Nat.le_add_left s r)

structure Compiled (p : Program F I r) (q : Program F J s) (src : J → Gate F I (Fin r)) where
  program : Program F I (r+s)
  correctOld : ∀ x i, program.eval x (oldOutput s i) = p.eval x i
  correct : ∀ x i, program.eval x (newOutput r i) = q.eval (fun j => (src j).eval x (p.eval x)) i

/-- Extend a prefix using one register per gate. -/
def compile (p : Program F I r) (src : J → Gate F I (Fin r)) :
    {s : ℕ} → (q : Program F J s) → Compiled p q src
  | 0, .nil => ⟨p, fun _ _ => rfl, fun _ i => i.elim0⟩
  | s+1, .step q g =>
    let a := p.compile src q
    let t := g.subst (fun j => (src j).subst .input (oldOutput s)) (newOutput r)
    ⟨a.program.step t, a.correctOld, fun x => Fin.cases (by
      change t.eval x (a.program.eval x) = g.eval _ _
      simp only [t, Gate.eval_subst, a.correct, a.correctOld]
      rfl) (a.correct x)⟩

end Program

private def pad {n m : ℕ} {G : Type*} (f : Pair n → G) (z : G)
    (i j : Fin m) : G :=
  if h : i.val < n ∧ j.val < n then f (⟨i.val, h.1⟩, ⟨j.val, h.2⟩) else z

/-- Substitute constants for all inputs outside the smaller matrices. -/
theorem MatrixAlgorithm.exists_restrict {n m : ℕ} (h : n ≤ m)
    (P : MatrixAlgorithm F m m m) (hP : P.Correct) :
    ∃ Q : MatrixAlgorithm F n n n, Q.Correct ∧ Q.registers = P.registers := by
  let src : Input m → Gate F (Input n) (Fin 0) :=
    matrixInputs (pad (Gate.input ∘ Sum.inl) (.constant 0))
      (pad (Gate.input ∘ Sum.inr) (.constant 0))
  let s := Program.nil.compile src P.program
  refine ⟨⟨_, s.program, fun i k => Program.newOutput 0 (P.output (Fin.castLE h i) (Fin.castLE h k))⟩,
    fun A B => ?_, Nat.zero_add _⟩
  let lift (M : Square F n) : Square F m := pad (fun x => M x.1 x.2) 0
  have hsrc : (fun i => (src i).eval (matrixInputs A B) Fin.elim0) = matrixInputs (lift A) (lift B) := by
    funext x
    rcases x with ⟨i,j⟩ | ⟨i,j⟩ <;> simp only [src, lift, pad, matrixInputs] <;> split <;> rfl
  funext i k
  rw [MatrixAlgorithm.eval, s.correct, Program.eval, hsrc]
  refine (congrFun₂ (hP (lift A) (lift B)) _ _).trans ?_
  simp only [Matrix.mul_apply]
  symm
  apply Fintype.sum_of_injective (Fin.castLE h) (by simp [Function.Injective])
  · intro j hj
    by_cases hj' : j.val < n
    · exact (hj ⟨⟨j, hj'⟩, rfl⟩).elim
    simp [lift, pad, hj']
  simp [lift, pad]


section BlockCompiler

/-- A circuit with specified semantics and register budget. -/
private structure Circuit {I O : Type*} (f : (I → F) → O → F) (r : ℕ) where
  program : Program F I r
  output : O → Fin r
  spec : ∀ x o, program.eval x (output o) = f x o

namespace Circuit

variable {I M O : Type*}

private def seq {f : (I → F) → M → F} {g : (M → F) → O → F} {r s : ℕ}
    (p : Circuit f r) (q : Circuit g s) : Circuit (fun x => g (f x)) (r + 1 + s) :=
  let c := (p.program.step (.constant 0)).compile (fun i => .add (p.output i).succ 0) q.program
  ⟨c.program, Program.newOutput (r+1) ∘ q.output, fun x o => by
    simp [c.correct, Program.eval, Gate.eval, p.spec, q.spec]⟩

/-- Run independent circuits of a common size on the same inputs. -/
private def parallel {s : ℕ} : {r : ℕ} → {f : Fin r → (I → F) → O → F} →
    (∀ i, Circuit (f i) s) → Circuit (fun x (o : Fin r × O) => f o.1 x o.2) (r * s)
  | 0, _, _ => ⟨by rw [Nat.zero_mul]; exact .nil, fun o => o.1.elim0, fun _ o => o.1.elim0⟩
  | r+1, f, p => by
    let q := parallel (fun i : Fin r => p i.succ)
    let c := q.program.compile Gate.input (p 0).program
    rw [Nat.succ_mul]
    exact ⟨c.program, fun (i,o) => Fin.cases (Program.newOutput (r*s) ((p 0).output o))
      (fun j => Program.oldOutput s (q.output (j,o))) i,
      fun x (i,o) => Fin.cases ((c.correct _ _).trans ((p 0).spec _ _))
        (fun j => (c.correctOld _ _).trans (q.spec x (j,o))) i⟩

private def linearFin : (n : ℕ) → (a : Fin n → F × I) →
    Circuit (fun x (_ : Unit) => ∑ i, (a i).1 * x (a i).2) (4*n+1)
  | 0, _ => ⟨Program.nil.step (.constant 0), fun _ => 0, fun _ _ => rfl⟩
  | n+1, a =>
    let q := linearFin n (a ∘ Fin.succ)
    let p := ((q.program.step (.input (a 0).2)).step (.constant (a 0).1)).step (.mul 0 (Fin.succ 0))
    ⟨p.step (.add 0 (q.output ()).succ.succ.succ), fun _ => 0, fun x _ => by
      simp only [p, Program.eval, Fin.cases_zero, Fin.cases_succ, Gate.eval,
        q.spec, Fin.sum_univ_succ, Function.comp_apply]⟩

private def linear {J : Type*} [Fintype J] [Fintype O] (a : O → J → F × I) :
    Circuit (fun x o => ∑ j, (a o j).1 * x (a o j).2) (Fintype.card O * (4*Fintype.card J+1)) := by
  let e := Fintype.equivFin O
  let d := (Fintype.equivFin J).symm
  let p := parallel (fun i => linearFin _ (a (e.symm i) ∘ d))
  refine ⟨p.program, fun o => p.output (e o, ()), fun x o => ?_⟩
  rw [p.spec]
  simpa [e] using d.sum_comp (fun j => (a o j).1 * x (a o j).2)

private def ofMatrix {m : ℕ} (p : MatrixAlgorithm F m m m) (hp : p.Correct) :
    Circuit (fun (x : Input m → F) (o : Pair m) =>
      ∑ j, x (.inl (o.1, j)) * x (.inr (j, o.2))) p.registers := by
  refine ⟨p.program, fun o => p.output o.1 o.2, fun x o => ?_⟩
  let A : Square F m := fun i j => x (.inl (i,j))
  let B : Square F m := fun j k => x (.inr (j,k))
  have h : matrixInputs A B = x := by bound
  simpa only [MatrixAlgorithm.eval, h, Matrix.mul_apply] using congrFun₂ (hp A B) o.1 o.2

end Circuit

variable {n m r : ℕ}

private def join (i : Fin n) (j : Fin m) : Fin (n * m) := finProdFinEquiv (i, j)

private def blocks : Square F (n*m) ≃+* Matrix (Fin n) (Fin n) (Square F m) :=
  (Matrix.reindexRingEquiv F finProdFinEquiv).symm.trans (Matrix.compRingEquiv (Fin n) (Fin m) F).symm

@[simp] private theorem blocks_apply (A : Square F (n*m)) (i k : Fin n) (s t : Fin m) :
    blocks A i k s t = A (join i s) (join k t) := rfl

private def lin (a : Pair n → ℤ) (A : Square F n) : F := ∑ x, a x • A x.1 x.2

/-- The integer coefficient identity can be contracted in any ring. -/
private theorem block_identity (M : Tensor.Maps ℤ (Pair n) (Pair n) (Pair n) (Fin r) (Fin r) (Fin r))
    (h : Tensor.squareCoefficients n = Tensor.restrict M (Tensor.diagonal (Fin r)))
    (A B : Square F n) (i k : Fin n) :
    (∑ q, M.right (k, i) q • (lin (fun x => M.left x q) A * lin (fun y => M.middle y q) B)) = (A * B) i k := by
  rw [Tensor.restrict_diagonal] at h
  have coeff (x y : Pair n) : (∑ q, M.right (k, i) q * (M.middle y q * M.left x q)) =
      Tensor.squareCoefficients n x y (k, i) := by
    grind
  simp only [lin, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Finset.smul_sum,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin r))), ← Finset.sum_smul, coeff]
  simp [Tensor.squareCoefficients, Fintype.sum_prod_type, ite_and]

/-- Compile the two sets of input forms, run `r` copies of the smaller
algorithm, then compile the output forms. -/
private theorem int_rank_block_step (h : Tensor.RankAtMost (Tensor.squareCoefficients n) r) :
    ∃ B : ℕ, ∀ {m}, 1 ≤ m → ∀ p : MatrixAlgorithm F m m m, p.Correct →
      ∃ q : MatrixAlgorithm F (n*m) (n*m) (n*m), q.Correct ∧
        q.registers ≤ r * p.registers + B * m^2 := by
  obtain ⟨M, h⟩ := h
  refine ⟨(12*r+1)*n^2+3*r+1, fun {m} hm p hp => ?_⟩
  let forms : Fin r → Input m → Pair n → F × Input (n * m)
    | q, .inl (s, t), x => (↑(M.left x q), .inl (join x.1 s, join x.2 t))
    | q, .inr (t, u), y => (↑(M.middle y q), .inr (join y.1 t, join y.2 u))
  let outputs (o : Pair (n * m)) (q : Fin r) : F × (Fin r × Pair m) :=
    let i := finProdFinEquiv.symm o.1
    let k := finProdFinEquiv.symm o.2
    (↑(M.right (k.1, i.1) q), q, (i.2, k.2))
  let f := (Circuit.parallel fun q => (Circuit.linear (forms q)).seq (Circuit.ofMatrix p hp)).seq
    (Circuit.linear outputs)
  refine ⟨⟨_, f.program, fun i k => f.output (i, k)⟩, ?_, ?_⟩
  · intro A B
    funext i k
    obtain ⟨⟨i, s⟩, rfl⟩ := finProdFinEquiv.surjective i
    obtain ⟨⟨k, u⟩, rfl⟩ := finProdFinEquiv.surjective k
    change f.program.eval (matrixInputs A B) (f.output (join i s, join k u)) = _
    rw [f.spec]
    have hf (q : Fin r) (x : Input m) :
        (∑ j, (forms q x j).1 * matrixInputs A B (forms q x j).2) =
          matrixInputs (lin (fun x => M.left x q) (blocks A)) (lin (fun y => M.middle y q) (blocks B)) x := by
      rcases x with ⟨_,_⟩ | ⟨_,_⟩ <;>
        simp only [forms, matrixInputs, lin, Matrix.sum_apply, Matrix.smul_apply, blocks_apply] <;>
        simp only [zsmul_eq_mul]
    simp only [outputs, join, Equiv.symm_apply_apply, hf]
    have H := congrArg (fun M : Square F m => M s u) (block_identity M h (blocks A) (blocks B) i k)
    simp only [Matrix.sum_apply, Matrix.smul_apply, ← map_mul, blocks_apply] at H
    simpa only [zsmul_eq_mul, Function.comp_apply, matrixInputs, Matrix.mul_apply, join] using H
  · simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
    nlinarith [Nat.one_le_pow 2 m hm]


end BlockCompiler

/-- A fixed block scheme gives a uniform cost bound at any rate strictly above
its rank growth and at least quadratic. -/
theorem cost_bound_of_int_scheme {b r : ℕ} (hb : 2 ≤ b)
    (hRank : Tensor.RankAtMost (Tensor.squareCoefficients b) r)
    {t : ℝ} (ht : 2 ≤ t) (hr : (r : ℝ) < (b : ℝ) ^ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n n n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ t := by
  let q := (b : ℝ) ^ t
  obtain ⟨B, step⟩ := int_rank_block_step (F := F) hRank
  let D := 3 + (B : ℝ) / (q - r)
  have hgap : 0 < q-r := sub_pos.mpr hr
  have hD : 3 ≤ D := le_add_of_nonneg_right (by positivity)
  have hrec : (r : ℝ)*D + B ≤ D*q := by
    linarith [(div_le_iff₀ hgap).mp (le_add_of_nonneg_left (show (0 : ℝ) ≤ 3 by norm_num) : B / (q-r) ≤ D)]
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hquad : (b : ℝ)^2 ≤ q := by simpa using Real.rpow_le_rpow_of_exponent_le hb' ht
  have hpow (j : ℕ) : ∃ P : MatrixAlgorithm F (b^j) (b^j) (b^j),
      P.Correct ∧ (P.registers : ℝ) ≤ D * q^j := by
    induction j with
    | zero =>
      rw [pow_zero b]
      refine ⟨⟨3, ((Program.nil.step (.input (.inl (0, 0)))).step (.input (.inr (0, 0)))).step
        (.mul (Fin.succ 0) 0), fun _ _ => 0⟩, fun A B => ?_, by simpa using hD⟩
      funext i k
      change A 0 0 * B 0 0 = _
      simp [Matrix.mul_apply, Fin.fin_one_eq_zero]
    | succ j ih =>
      rw [pow_succ' b]
      obtain ⟨P, hP, hc⟩ := ih
      obtain ⟨Q, hQ, hcost⟩ := step (Nat.one_le_pow _ _ (by omega)) P hP
      have hsize : ((b : ℝ)^j)^2 ≤ q^j := by
        rw [← pow_mul, mul_comm j, pow_mul]
        gcongr
      refine ⟨Q, hQ, ?_⟩
      calc
        (Q.registers : ℝ) ≤ r * (P.registers : ℝ) + B * ((b : ℝ)^j)^2 := by exact_mod_cast hcost
        _ ≤ (r * D + B) * q^j := by rw [add_mul, mul_assoc]; gcongr
        _ ≤ D * q^(j+1) := by simpa [pow_succ', mul_assoc] using mul_le_mul_of_nonneg_right hrec (by positivity : 0 ≤ q^j)
  refine ⟨D * q, by dsimp [D, q]; positivity, fun n hn => ?_⟩
  let j := Nat.log b n
  have hle : n ≤ b^(j+1) := (Nat.lt_pow_succ_log_self (by omega) n).le
  obtain ⟨P, hP, hc⟩ := hpow (j+1)
  obtain ⟨Q, hQ, hq⟩ := P.exists_restrict hle hP
  refine ⟨Q, hQ, (Nat.cast_le.mpr Q.program.cost_le_registers).trans ?_⟩
  rw [hq]
  refine hc.trans ?_
  rw [pow_succ' q, ← mul_assoc]
  dsimp [q]
  rw [Real.rpow_pow_comm (Nat.cast_nonneg b), ← Nat.cast_pow]
  gcongr
  exact Nat.pow_log_le_self b (by omega)


end
end OAI.MatrixMultiplication.Arithmetic
