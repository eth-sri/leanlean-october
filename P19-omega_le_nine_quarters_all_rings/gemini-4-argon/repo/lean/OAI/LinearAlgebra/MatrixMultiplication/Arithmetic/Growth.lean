module

public import OAI.LinearAlgebra.MatrixMultiplication.Model
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

public section

@[expose] section

namespace OAI.MatrixMultiplication.Arithmetic

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

variable {F : Type*} [Ring F]

namespace Program

variable {Input Mid : Type*}

@[simp] theorem eval_step_zero {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) (inputs : Input → F) :
    (p.step g).eval inputs 0 = g.eval inputs (p.eval inputs) := rfl

@[simp] theorem eval_step_succ {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) (inputs : Input → F) (i : Fin r) :
    (p.step g).eval inputs i.succ = p.eval inputs i := rfl

omit [Ring F] in
@[simp] theorem cost_step {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) : (p.step g).cost = p.cost + g.cost := rfl

structure Substituted {r s : ℕ} (p : Program F Input r) (q : Program F Mid s)
    (wires : Mid → Input ⊕ Fin r) where
  registers : ℕ
  program : Program F Input registers
  oldOutput : Fin r → Fin registers
  output : Fin s → Fin registers
  correctOld : ∀ inputs i, program.eval inputs (oldOutput i) = p.eval inputs i
  correct : ∀ inputs i, program.eval inputs (output i) =
    q.eval (fun j => Sum.elim inputs (p.eval inputs) (wires j)) i
  cost_eq : program.cost = p.cost + q.cost

def Substituted.step {r s : ℕ} {p : Program F Input r} {q : Program F Mid s}
    {wires : Mid → Input ⊕ Fin r} (a : Substituted p q wires)
    (g : Gate F Mid (Fin s)) (h : Gate F Input (Fin a.registers))
    (heval : ∀ inputs, h.eval inputs (a.program.eval inputs) =
      g.eval (fun j => Sum.elim inputs (p.eval inputs) (wires j))
        (q.eval (fun j => Sum.elim inputs (p.eval inputs) (wires j))))
    (hcost : h.cost = g.cost) : Substituted p (q.step g) wires where
  registers := a.registers + 1
  program := a.program.step h
  oldOutput i := (a.oldOutput i).succ
  output := Fin.cases 0 (fun i => (a.output i).succ)
  correctOld := a.correctOld
  correct inputs := Fin.cases (heval inputs) (a.correct inputs)
  cost_eq := by simp only [cost_step, a.cost_eq, hcost, Nat.add_assoc]

def substitute {r : ℕ} (p : Program F Input r) :
    {s : ℕ} → (q : Program F Mid s) → (wires : Mid → Input ⊕ Fin r) → Substituted p q wires
  | 0, .nil, _ =>
    ⟨r, p, id, Fin.elim0, fun _ _ => rfl, fun _ i => Fin.elim0 i, by simp [cost]⟩
  | _ + 1, .step q g, wires =>
    let a := substitute p q wires
    match g with
    | .input j =>
      match hw : wires j with
      | .inl i => a.step (.input j) (.input i) (by intro inputs; simp only [Gate.eval, hw, Sum.elim_inl]) rfl
      | .inr w =>
        ⟨a.registers, a.program, a.oldOutput, Fin.cases (a.oldOutput w) a.output,
          a.correctOld,
          fun inputs => Fin.cases (by simpa only [Fin.cases_zero, eval_step_zero, Gate.eval, hw, Sum.elim_inr] using a.correctOld inputs w) (a.correct inputs),
          by simpa only [cost_step, Gate.cost, Nat.add_zero] using a.cost_eq⟩
    | .constant z => a.step (.constant z) (.constant z) (fun _ => rfl) rfl
    | .add i j => a.step (.add i j) (.add (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .sub i j => a.step (.sub i j) (.sub (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .mul i j => a.step (.mul i j) (.mul (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl

def registerCost : {r : ℕ} → Program F Input r → Fin r → ℕ
  | 0, .nil => Fin.elim0
  | _ + 1, .step p g => Fin.cases g.cost p.registerCost

omit [Ring F] in
theorem sum_registerCost {r : ℕ} (p : Program F Input r) :
    ∑ i, p.registerCost i = p.cost := by
  induction p with
  | nil => simp [registerCost, cost]
  | step p g ih => simp [registerCost, Fin.sum_univ_succ, ih, Nat.add_comm]

theorem eval_eq_constant_or_input_of_registerCost_eq_zero
    {r : ℕ} (p : Program F Input r) (i : Fin r) (hi : p.registerCost i = 0) :
    (∃ z : F, ∀ inputs, p.eval inputs i = z) ∨
      (∃ a : Input, ∀ inputs, p.eval inputs i = inputs a) := by
  induction p with
  | nil => exact Fin.elim0 i
  | step p g ih =>
    refine Fin.cases (fun hi => ?_) (fun j hi => ih j hi) i hi
    cases g with
    | constant z => exact Or.inl ⟨z, fun _ => rfl⟩
    | input a => exact Or.inr ⟨a, fun _ => rfl⟩
    | add | sub | mul => contradiction

end Program

def scalarAlgorithm (F : Type*) [Ring F] : MatrixAlgorithm F 1 1 1 where
  registers := 3
  program := ((Program.nil.step (.input (.inl (0, 0)))).step
    (.input (.inr (0, 0)))).step (.mul 1 0)
  output := fun _ _ => 0

theorem scalarAlgorithm_correct (F : Type*) [Ring F] : (scalarAlgorithm F).Correct := by
  intro A B
  funext i k
  rw [Subsingleton.elim i 0, Subsingleton.elim k 0]
  change A 0 0 * B 0 0 = (A * B) 0 0
  simp [Matrix.mul_apply]

@[simp] theorem scalarAlgorithm_cost (F : Type*) [Ring F] : (scalarAlgorithm F).cost = 1 := rfl

def zeroPadMatrix {a b : ℕ} (A B : ℕ) (M : Matrix (Fin a) (Fin b) F) :
    Matrix (Fin A) (Fin B) F :=
  fun i j => if hi : i.val < a then
    if hj : j.val < b then M ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else 0

@[simp] theorem zeroPadMatrix_castLE {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B)
    (M : Matrix (Fin a) (Fin b) F) (i : Fin a) (j : Fin b) :
    zeroPadMatrix A B M (Fin.castLE ha i) (Fin.castLE hb j) = M i j := by
  simp [zeroPadMatrix, i.is_lt, j.is_lt]

theorem zeroPadMatrix_mul {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (M : Matrix (Fin a) (Fin b) F) (N : Matrix (Fin b) (Fin c) F)
    (i : Fin a) (k : Fin c) :
    (zeroPadMatrix A B M * zeroPadMatrix B C N) (Fin.castLE ha i) (Fin.castLE hc k) =
      (M * N) i k := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine (Fintype.sum_of_injective (Fin.castLE hb)
    (fun i j hij => Fin.ext (congrArg (fun v : Fin B => v.val) hij))
    (fun j : Fin b => zeroPadMatrix A B M (Fin.castLE ha i) (Fin.castLE hb j) *
      zeroPadMatrix B C N (Fin.castLE hb j) (Fin.castLE hc k)) _
    (fun j hj => ?_) (fun _ => rfl)).symm.trans (by simp)
  have hge : b ≤ j.val := le_of_not_gt fun hsmall => hj ⟨⟨j.val, hsmall⟩, Fin.ext rfl⟩
  simp [zeroPadMatrix, not_lt_of_ge hge]

def padSource {a b c A B C : ℕ} : MatrixInput A B C → MatrixInput a b c ⊕ Fin 1
  | .inl (i, j) => if hi : i.val < a then
      if hj : j.val < b then .inl (.inl (⟨i.val, hi⟩, ⟨j.val, hj⟩)) else .inr 0
    else .inr 0
  | .inr (j, k) => if hj : j.val < b then
      if hk : k.val < c then .inl (.inr (⟨j.val, hj⟩, ⟨k.val, hk⟩)) else .inr 0
    else .inr 0

theorem padSource_eval {a b c A B C : ℕ}
    (M : Matrix (Fin a) (Fin b) F) (N : Matrix (Fin b) (Fin c) F) :
    (fun x : MatrixInput A B C =>
      Sum.elim (matrixInputs M N) ((Program.nil.step (.constant 0)).eval (matrixInputs M N))
        (padSource x)) =
      matrixInputs (zeroPadMatrix A B M) (zeroPadMatrix B C N) := by
  funext x
  rcases x with ⟨i, j⟩ | ⟨j, k⟩
  · by_cases hi : i.val < a <;> by_cases hj : j.val < b <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hi, hj, Gate.eval]
  · by_cases hj : j.val < b <;> by_cases hk : k.val < c <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hj, hk, Gate.eval]

theorem MatrixAlgorithm.exists_restrict {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (P : MatrixAlgorithm F A B C) (hP : P.Correct) :
    ∃ Q : MatrixAlgorithm F a b c, Q.Correct ∧ Q.cost ≤ P.cost := by
  let s := (Program.nil.step (.constant (0 : F))).substitute P.program (padSource (a := a) (b := b) (c := c))
  refine ⟨⟨s.registers, s.program,
    fun i k => s.output (P.output (Fin.castLE ha i) (Fin.castLE hc k))⟩,
    fun M N => funext fun i => funext fun k => ?_,
    by simpa [MatrixAlgorithm.cost, Program.cost, Gate.cost] using s.cost_eq.le⟩
  exact (s.correct (matrixInputs M N) _).trans
    ((congrArg (fun f => P.program.eval f _) (padSource_eval M N)).trans
      ((congrFun (congrFun (hP (zeroPadMatrix A B M) (zeroPadMatrix B C N))
        (Fin.castLE ha i)) (Fin.castLE hc k)).trans (zeroPadMatrix_mul ha hb hc M N i k)))

namespace RecursiveBlock

def linProg {Input : Type*} : (k : ℕ) → (Fin k → F) → (Fin k → Input) → Program F Input (4 * k + 1)
  | 0, _, _ => Program.nil.step (.constant 0)
  | k + 1, a, w =>
    ((((linProg k (fun j => a j.succ) (fun j => w j.succ)).step
      (.constant (a 0))).step
      (.input (w 0))).step
      (.mul 1 0)).step
      (.add 0 3)

theorem eval_linProg {Input : Type*} (k : ℕ) (a : Fin k → F) (w : Fin k → Input) (inputs : Input → F) :
    (linProg k a w).eval inputs 0 = ∑ j, a j * inputs (w j) := by
  induction k with
  | zero => simp [linProg, Gate.eval]
  | succ k ih => rw [Fin.sum_univ_succ, ← ih (fun j => a j.succ) (fun j => w j.succ)]; rfl

theorem cost_linProg {Input : Type*} (k : ℕ) (a : Fin k → F) (w : Fin k → Input) :
    (linProg k a w).cost = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (linProg k (fun j => a j.succ) (fun j => w j.succ)).cost + 0 + 0 + 1 + 1 = 2 * (k + 1)
    rw [ih]; omega

structure Family (F Input Output : Type*) where
  registers : ℕ
  program : Program F Input registers
  output : Output → Fin registers

namespace Family

variable {Input Mid Output : Type*}

def eval (p : Family F Input Output) (inputs : Input → F) (o : Output) : F :=
  p.program.eval inputs (p.output o)

def cost (p : Family F Input Output) : ℕ := p.program.cost

def compose (p : Family F Input Mid) (q : Family F Mid Output) : Family F Input Output :=
  let s := p.program.substitute q.program (fun j => .inr (p.output j))
  ⟨s.registers, s.program, fun o => s.output (q.output o)⟩

theorem eval_compose (p : Family F Input Mid) (q : Family F Mid Output)
    (inputs : Input → F) (o : Output) :
    (compose p q).eval inputs o = q.eval (p.eval inputs) o :=
  (p.program.substitute q.program (fun j => .inr (p.output j))).correct inputs (q.output o)

theorem cost_compose (p : Family F Input Mid) (q : Family F Mid Output) :
    (compose p q).cost = p.cost + q.cost :=
  (p.program.substitute q.program (fun j => .inr (p.output j))).cost_eq

def parallel : (r : ℕ) → (Fin r → Family F Input Output) → Family F Input (Fin r × Output)
  | 0, _ => ⟨0, Program.nil, fun o => Fin.elim0 o.1⟩
  | r + 1, p =>
    let head := p 0
    let tail := parallel r (fun i => p i.succ)
    let s := head.program.substitute tail.program .inl
    ⟨s.registers, s.program, fun o => Fin.cases (s.oldOutput (head.output o.2))
      (fun i => s.output (tail.output (i, o.2))) o.1⟩

theorem eval_parallel (r : ℕ) (p : Fin r → Family F Input Output)
    (inputs : Input → F) (o : Fin r × Output) :
    (parallel r p).eval inputs o = (p o.1).eval inputs o.2 := by
  induction r with
  | zero => exact Fin.elim0 o.1
  | succ r ih =>
    rcases o with ⟨i, o⟩
    let s := (p 0).program.substitute (parallel r (fun j => p j.succ)).program .inl
    refine Fin.cases (s.correctOld inputs _) (fun j => ?_) i
    exact (s.correct inputs _).trans (ih (fun j => p j.succ) (j, o))

theorem cost_parallel (r : ℕ) (p : Fin r → Family F Input Output) :
    (parallel r p).cost = ∑ i, (p i).cost := by
  induction r with
  | zero => simp [parallel, cost, Program.cost]
  | succ r ih =>
    rw [Fin.sum_univ_succ, ← ih]
    exact ((p 0).program.substitute (parallel r (fun i => p i.succ)).program .inl).cost_eq

def mkLinearFamily {Term : Type*} [Fintype Output] [Fintype Term]
    (a : Output → Term → F) (w : Output → Term → Input) : Family F Input Output :=
  let eo := Fintype.equivFin Output
  let et := (Fintype.equivFin Term).symm
  let q := parallel (Fintype.card Output) fun i =>
    ⟨4 * Fintype.card Term + 1,
      linProg (Fintype.card Term) (a (eo.symm i) ∘ et) (w (eo.symm i) ∘ et), fun _ => 0⟩
  ⟨q.registers, q.program, fun o => q.output (eo o, ())⟩

theorem eval_mkLinearFamily {Term : Type*} [Fintype Output] [Fintype Term]
    (a : Output → Term → F) (w : Output → Term → Input) (inputs : Input → F) (o : Output) :
    (mkLinearFamily a w).eval inputs o = ∑ t, a o t * inputs (w o t) := by
  change (parallel _ _).eval inputs ((Fintype.equivFin Output) o, ()) = _
  rw [eval_parallel, Equiv.symm_apply_apply]
  change (linProg _ _ _).eval inputs 0 = _
  rw [eval_linProg]
  exact (Fintype.equivFin Term).symm.sum_comp (fun t => a o t * inputs (w o t))

theorem cost_mkLinearFamily {Term : Type*} [Fintype Output] [Fintype Term]
    (a : Output → Term → F) (w : Output → Term → Input) :
    (mkLinearFamily a w).cost = Fintype.card Output * (2 * Fintype.card Term) := by
  change (parallel _ _).cost = _
  rw [cost_parallel]
  simp [cost, cost_linProg]

end Family

section Block

variable {n r m : ℕ}

def join {n m : ℕ} (i : Fin n) (j : Fin m) : Fin (n * m) := finProdFinEquiv (i, j)

def leftBlock (a : Fin r → Fin n × Fin n → F)
    (A : Matrix (Fin (n * m)) (Fin (n * m)) F) (q : Fin r) : Matrix (Fin m) (Fin m) F :=
  fun s t => ∑ x, a q x * A (join x.1 s) (join x.2 t)

def rightBlock (b : Fin r → Fin n × Fin n → F)
    (B : Matrix (Fin (n * m)) (Fin (n * m)) F) (q : Fin r) : Matrix (Fin m) (Fin m) F :=
  fun t u => ∑ y, b q y * B (join y.1 t) (join y.2 u)

theorem int_rank_bilinear_identity
    (a b c : Fin r → Fin n × Fin n → ℤ)
    (h : Tensor.matrixCoefficients (K := ℤ) (Fin n) (Fin n) (Fin n) =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (left right : Fin n × Fin n → F) (i k : Fin n) :
    (∑ q, (c q (k, i) : F) * (∑ x, (a q x : F) * left x) *
      (∑ y, (b q y : F) * right y)) = ∑ j, left (i, j) * right (j, k) := by
  have hcentral (u v w : ℤ) (x y : F) :
      (w : F) * ((u : F) * x) * ((v : F) * y) = ((u * v * w : ℤ) : F) * x * y := by
    have hc : (w : F) * (u : F) * (v : F) = ((u * v * w : ℤ) : F) := by
      simpa only [Int.cast_mul] using congrArg (fun z : ℤ => (z : F)) (by ring : w * u * v = u * v * w)
    rw [← hc]
    simp only [mul_assoc]
    rw [← mul_assoc x (v : F) y, ← Int.cast_comm v x]
    simp only [mul_assoc]
  have hcoeff (x y z : Fin n × Fin n) :
      (∑ q, ((a q x * b q y * c q z : ℤ) : F)) =
        ((Tensor.matrixCoefficients (K := ℤ) (Fin n) (Fin n) (Fin n) x y z : ℤ) : F) := by
    simpa only [Tensor.rankOne, Int.cast_sum] using
      (congrArg (fun z : ℤ => (z : F)) (congrFun (congrFun (congrFun h x) y) z)).symm
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ q, ∑ y, ∑ x, (c q (k, i) : F) * ((a q x : F) * left x) * ((b q y : F) * right y)) =
        ∑ x, ∑ q, ∑ y, (c q (k, i) : F) * ((a q x : F) * left x) * ((b q y : F) * right y) :=
      (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ q, ((a q x * b q y * c q (k, i) : ℤ) : F) * left x * right y :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans <|
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => hcentral _ _ _ _ _
    _ = ∑ x, ∑ y, ((Tensor.matrixCoefficients (K := ℤ) (Fin n) (Fin n) (Fin n) x y (k, i) : ℤ) : F) *
          left x * right y := by simp_rw [← Finset.sum_mul, hcoeff]
    _ = ∑ j, left (i, j) * right (j, k) := by
      simp [Tensor.matrixCoefficients, Fintype.sum_prod_type, ite_and, ite_mul]

theorem int_block_identity
    (a b c : Fin r → Fin n × Fin n → ℤ)
    (h : Tensor.matrixCoefficients (K := ℤ) (Fin n) (Fin n) (Fin n) =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (A B : Matrix (Fin (n * m)) (Fin (n * m)) F) (i k : Fin n) (s u : Fin m) :
    (∑ q, (c q (k, i) : F) *
      ((leftBlock (fun q x => (a q x : F)) A q) *
        (rightBlock (fun q y => (b q y : F)) B q)) s u) =
      (A * B) (join i s) (join k u) := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlocal (t : Fin m) := int_rank_bilinear_identity a b c h
    (fun x => A (join x.1 s) (join x.2 t))
    (fun y => B (join y.1 t) (join y.2 u)) i k
  simp only [leftBlock, rightBlock]
  simp_rw [← mul_assoc, hlocal]
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type _).symm.trans
    (finProdFinEquiv.sum_comp (fun j => A (join i s) j * B j (join k u)))

def inputFamily (a b : Fin r → Fin n × Fin n → F) :
    Family F (MatrixInput (n * m) (n * m) (n * m)) (Fin r × MatrixInput m m m) :=
  Family.mkLinearFamily
    (fun | (q, .inl _) => a q | (q, .inr _) => b q)
    (fun | (_, .inl (s, t)), x => .inl (join x.1 s, join x.2 t)
         | (_, .inr (t, u)), y => .inr (join y.1 t, join y.2 u))

theorem inputFamily_eval (a b : Fin r → Fin n × Fin n → F)
    (A B : Matrix (Fin (n * m)) (Fin (n * m)) F) (q : Fin r) (x : MatrixInput m m m) :
    (inputFamily a b).eval (matrixInputs A B) (q, x) =
      matrixInputs (leftBlock a A q) (rightBlock b B q) x := by
  cases x <;> simp [inputFamily, Family.eval_mkLinearFamily, matrixInputs, leftBlock, rightBlock]

def recursiveProducts (a b : Fin r → Fin n × Fin n → F) (p : MatrixAlgorithm F m m m) :
    Family F (MatrixInput (n * m) (n * m) (n * m)) (Fin r × (Fin m × Fin m)) :=
  (inputFamily a b).compose (Family.parallel r fun q =>
    let s := (Program.nil : Program F (Fin r × MatrixInput m m m) 0).substitute p.program (fun x => .inl (q, x))
    ⟨s.registers, s.program, fun o => s.output (p.output o.1 o.2)⟩)

theorem recursiveProducts_eval (a b : Fin r → Fin n × Fin n → F)
    (p : MatrixAlgorithm F m m m) (hp : p.Correct)
    (A B : Matrix (Fin (n * m)) (Fin (n * m)) F) (q : Fin r) (s u : Fin m) :
    (recursiveProducts a b p).eval (matrixInputs A B) (q, (s, u)) =
      ((leftBlock a A q) * (rightBlock b B q)) s u := by
  rw [recursiveProducts, Family.eval_compose, Family.eval_parallel]
  let sub := (Program.nil : Program F (Fin r × MatrixInput m m m) 0).substitute p.program (fun x => .inl (q, x))
  refine (sub.correct _ _).trans ?_
  have heq : (fun x => (inputFamily a b).eval (matrixInputs A B) (q, x)) =
      matrixInputs (leftBlock a A q) (rightBlock b B q) :=
    funext (inputFamily_eval a b A B q)
  exact (congrArg (fun f => p.program.eval f (p.output s u)) heq).trans
    (congrFun (congrFun (hp _ _) s) u)

def outputFamily (c : Fin r → Fin n × Fin n → F) :
    Family F (Fin r × (Fin m × Fin m)) (Fin (n * m) × Fin (n * m)) :=
  Family.mkLinearFamily
    (fun o q => c q ((finProdFinEquiv.symm o.2).1, (finProdFinEquiv.symm o.1).1))
    (fun o q => (q, ((finProdFinEquiv.symm o.1).2, (finProdFinEquiv.symm o.2).2)))

theorem outputFamily_eval (c : Fin r → Fin n × Fin n → F)
    (inputs : Fin r × (Fin m × Fin m) → F) (i k : Fin n) (s u : Fin m) :
    (outputFamily c).eval inputs (join i s, join k u) =
      ∑ q, c q (k, i) * inputs (q, (s, u)) := by
  simp only [outputFamily, Family.eval_mkLinearFamily, join, Equiv.symm_apply_apply]

def algorithm (a b c : Fin r → Fin n × Fin n → F) (p : MatrixAlgorithm F m m m) :
    MatrixAlgorithm F (n * m) (n * m) (n * m) :=
  let f := (recursiveProducts a b p).compose (outputFamily c)
  ⟨f.registers, f.program, fun i k => f.output (i, k)⟩

theorem int_rank_block_step
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := ℤ) (Fin n) (Fin n) (Fin n)) r)
    (p : MatrixAlgorithm F m m m) (hp : p.Correct) :
    ∃ q : MatrixAlgorithm F (n * m) (n * m) (n * m), q.Correct ∧
      q.cost = r * p.cost + 6 * r * n ^ 2 * m ^ 2 := by
  rcases h with ⟨a, b, c, h⟩
  refine ⟨algorithm (fun q x => (a q x : F)) (fun q y => (b q y : F)) (fun q z => (c q z : F)) p, ?_, ?_⟩
  · intro A B
    funext i k
    obtain ⟨⟨i, s⟩, rfl⟩ := finProdFinEquiv.surjective i
    obtain ⟨⟨k, u⟩, rfl⟩ := finProdFinEquiv.surjective k
    change ((recursiveProducts (fun q x => (a q x : F)) (fun q y => (b q y : F)) p).compose
      (outputFamily (fun q z => (c q z : F)))).eval (matrixInputs A B) (join i s, join k u) = _
    rw [Family.eval_compose, outputFamily_eval]
    simp_rw [recursiveProducts_eval _ _ p hp A B]
    exact int_block_identity a b c h A B i k s u
  · change ((recursiveProducts _ _ p).compose (outputFamily _)).cost = _
    rw [Family.cost_compose, recursiveProducts, Family.cost_compose, inputFamily,
      Family.cost_mkLinearFamily, Family.cost_parallel, outputFamily, Family.cost_mkLinearFamily]
    have hsub (q : Fin r) :
        ((Program.nil : Program F (Fin r × MatrixInput m m m) 0).substitute p.program
          (fun x => .inl (q, x))).program.cost = p.cost := by
      simpa [Program.cost, MatrixAlgorithm.cost] using
        ((Program.nil : Program F (Fin r × MatrixInput m m m) 0).substitute p.program
          (fun x => .inl (q, x))).cost_eq
    simp only [Family.cost, hsub, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
    change (r * (m * m + m * m)) * (2 * (n * n)) + r * p.cost + (n * m * (n * m)) * (2 * r) = _
    ring

end Block

end RecursiveBlock

abbrev SquareAlgorithm (F : Type*) (n : ℕ) := MatrixAlgorithm F n n n

theorem geometric_cost_recurrence_bound (x : ℕ → ℝ) (a b d q : ℝ)
    (hx : 0 ≤ x 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (haq : a < q) (hdq : d ≤ q)
    (hstep : ∀ k, x (k + 1) ≤ a * x k + b * d ^ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ k, x k ≤ C * q ^ k := by
  let C := x 0 + b / (q - a) + 1
  have hgap : 0 < q - a := sub_pos.mpr haq
  have hC : 0 < C := by dsimp [C]; linarith [div_nonneg hb hgap.le]
  have hcoeff : a * C + b ≤ C * q := by
    have hmul : b ≤ (q - a) * C := by
      simpa [mul_div_cancel₀ _ hgap.ne'] using
        mul_le_mul_of_nonneg_left (by dsimp [C]; linarith : b / (q - a) ≤ C) hgap.le
    linarith
  refine ⟨C, hC, fun k => ?_⟩
  induction k with
  | zero => simp [C]; linarith [div_nonneg hb hgap.le]
  | succ k ih =>
    calc x (k + 1) ≤ a * (C * q ^ k) + b * q ^ k :=
        (hstep k).trans (add_le_add (mul_le_mul_of_nonneg_left ih ha)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd hdq k) hb))
      _ = (a * C + b) * q ^ k := by ring
      _ ≤ (C * q) * q ^ k := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (hd.trans hdq) k)
      _ = C * q ^ (k + 1) := by ring

def blockRecurrenceCost (b R K : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => R * blockRecurrenceCost b R K k + K * (b ^ k) ^ 2

theorem power_programs_of_block_step {b R K : ℕ}
    (hstep : ∀ m : ℕ, ∀ P : SquareAlgorithm F m, P.Correct →
      ∃ Q : SquareAlgorithm F (b * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    ∀ k : ℕ, ∃ P : SquareAlgorithm F (b ^ k), P.Correct ∧
      P.cost ≤ blockRecurrenceCost b R K k
  | 0 => ⟨scalarAlgorithm F, scalarAlgorithm_correct F, le_rfl⟩
  | k + 1 => by
    obtain ⟨P, hP, hcost⟩ := power_programs_of_block_step hstep k
    obtain ⟨Q, hQ, hQcost⟩ := hstep (b ^ k) P hP
    exact (pow_succ' b k).symm ▸ ⟨Q, hQ,
      hQcost.trans (Nat.add_le_add_right (Nat.mul_le_mul_left R hcost) _)⟩

theorem admissibleExponent_of_int_rank_bounds {τ : ℝ} (hτ : 2 ≤ τ)
    (hRank : ∀ ε : ℝ, 0 < ε → ∃ n r : ℕ, 2 ≤ n ∧
      Tensor.RankAtMost (Tensor.matrixCoefficients (K := ℤ) (Fin n) (Fin n) (Fin n)) r ∧
      (r : ℝ) ≤ (n : ℝ) ^ (τ + ε)) :
    AdmissibleExponent F τ := by
  intro ε hε
  obtain ⟨n, r, hn, hrank, hr⟩ := hRank (ε / 2) (half_pos hε)
  let K := 6 * r * n ^ 2
  have hstep : ∀ m : ℕ, ∀ P : SquareAlgorithm F m, P.Correct →
      ∃ Q : SquareAlgorithm F (n * m), Q.Correct ∧ Q.cost ≤ r * P.cost + K * m ^ 2 := by
    intro m P hP
    obtain ⟨Q, hQ, hcost⟩ := RecursiveBlock.int_rank_block_step hrank P hP
    exact ⟨Q, hQ, hcost.le⟩
  have hnone : 1 < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hrate : (r : ℝ) < (n : ℝ) ^ (τ + ε) :=
    hr.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hnone (by linarith))
  have hquad : (n : ℝ) ^ (2 : ℕ) ≤ (n : ℝ) ^ (τ + ε) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hnone.le (by norm_cast; linarith)
  obtain ⟨C, hC, hbound⟩ := geometric_cost_recurrence_bound
    (fun k => (blockRecurrenceCost n r K k : ℝ))
    (r : ℝ) (K : ℝ) ((n : ℝ) ^ (2 : ℕ)) ((n : ℝ) ^ (τ + ε))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (sq_nonneg _) hrate hquad (fun k => by
      simp only [blockRecurrenceCost, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2])
  have hnpos : 0 < (n : ℝ) := by positivity
  refine ⟨C * (n : ℝ) ^ (τ + ε), mul_pos hC (Real.rpow_pos_of_pos hnpos _), fun m hm => ?_⟩
  let k := Nat.log n m + 1
  have hmk : m ≤ n ^ k := (Nat.lt_pow_succ_log_self (by omega) m).le
  have hkm : n ^ k ≤ n * m := by
    rw [pow_succ']
    exact Nat.mul_le_mul_left n (Nat.pow_log_le_self n (by omega))
  obtain ⟨P, hP, hcost⟩ := power_programs_of_block_step hstep k
  obtain ⟨Q, hQ, hQP⟩ := MatrixAlgorithm.exists_restrict hmk hmk hmk P hP
  refine ⟨Q, hQ, ?_⟩
  calc
    (Q.cost : ℝ) ≤ (blockRecurrenceCost n r K k : ℝ) := by exact_mod_cast hQP.trans hcost
    _ ≤ C * ((n : ℝ) ^ (τ + ε)) ^ k := hbound k
    _ = C * ((n ^ k : ℕ) : ℝ) ^ (τ + ε) := by rw [Real.rpow_pow_comm hnpos.le, Nat.cast_pow]
    _ ≤ C * ((n : ℝ) * (m : ℝ)) ^ (τ + ε) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkm) (by linarith)) hC.le
    _ = (C * (n : ℝ) ^ (τ + ε)) * (m : ℝ) ^ (τ + ε) := by
      rw [Real.mul_rpow hnpos.le (Nat.cast_nonneg m), mul_assoc]

section ElementaryMatrices

variable {a b c : ℕ}

def elementaryLeft (i : Fin a) (j : Fin b) : Matrix (Fin a) (Fin b) F :=
  fun x y => if x = i then if y = j then 1 else 0 else 0

def elementaryRight (j : Fin b) (k : Fin c) : Matrix (Fin b) (Fin c) F :=
  fun y z => if z = k then if y = j then 1 else 0 else 0

theorem elementaryProduct (i x : Fin a) (j : Fin b) (k z : Fin c) :
    (elementaryLeft (F := F) i j * elementaryRight (F := F) j k) x z =
      if (x, z) = (i, k) then 1 else 0 := by
  by_cases hi : x = i <;> by_cases hk : z = k <;>
    simp [Matrix.mul_apply, elementaryLeft, elementaryRight, hi, hk]

end ElementaryMatrices

namespace MatrixAlgorithm

variable [Nontrivial F] {a b c : ℕ}

theorem output_injective (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) : Function.Injective (fun o : Fin a × Fin c => P.output o.1 o.2) := by
  classical
  intro x y hxy
  let j : Fin b := ⟨0, by omega⟩
  let A := elementaryLeft (F := F) x.1 j
  let B := elementaryRight (F := F) j x.2
  have heq : (A * B) x.1 x.2 = (A * B) y.1 y.2 := by
    rw [← congrFun (congrFun (hP A B) x.1) x.2, ← congrFun (congrFun (hP A B) y.1) y.2]
    exact congrArg (P.program.eval (matrixInputs A B)) hxy
  simp only [A, B, elementaryProduct, Prod.eta, ite_true] at heq
  by_contra hne
  simp [Ne.symm hne] at heq

theorem one_le_output_registerCost (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) (i : Fin a) (k : Fin c) :
    1 ≤ P.program.registerCost (P.output i k) := by
  by_contra hn
  let j : Fin b := ⟨0, by omega⟩
  have hentry (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
      P.program.eval (matrixInputs A B) (P.output i k) = (A * B) i k :=
    congrFun (congrFun (hP A B) i) k
  rcases P.program.eval_eq_constant_or_input_of_registerCost_eq_zero
      (P.output i k) (by omega) with ⟨z, hz⟩ | ⟨⟨x, y⟩ | ⟨y, z⟩, hu⟩
  · have hz0 : z = 0 := by have h := hentry 0 0; rw [hz] at h; simpa using h
    have hz1 : z = 1 := by
      have h := hentry (elementaryLeft i j) (elementaryRight j k)
      rw [hz] at h; simpa only [elementaryProduct, ite_true] using h
    exact zero_ne_one (hz0.symm.trans hz1)
  · have h := hentry (Matrix.of fun _ _ => 1) 0
    rw [hu] at h; simp [matrixInputs, Matrix.mul_apply] at h
  · have h := hentry 0 (Matrix.of fun _ _ => 1)
    rw [hu] at h; simp [matrixInputs, Matrix.mul_apply] at h

theorem output_size_le_cost (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) : a * c ≤ P.cost := by
  classical
  let f : Fin a × Fin c → Fin P.registers := fun o => P.output o.1 o.2
  calc
    a * c = ∑ _o : Fin a × Fin c, (1 : ℕ) := by simp
    _ ≤ ∑ o : Fin a × Fin c, P.program.registerCost (f o) :=
      Finset.sum_le_sum fun o _ => P.one_le_output_registerCost hb hP o.1 o.2
    _ = ∑ r ∈ Finset.univ.image f, P.program.registerCost r :=
      (Finset.sum_image fun _ _ _ _ h => P.output_injective hb hP h).symm
    _ ≤ ∑ r, P.program.registerCost r := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = P.cost := P.program.sum_registerCost

end MatrixAlgorithm

theorem admissibleExponent_two_le [Nontrivial F] {τ : ℝ}
    (hτ : AdmissibleExponent F τ) : 2 ≤ τ := by
  by_contra hneg
  let ε : ℝ := (2 - τ) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C ^ ε⁻¹) 1)
  have hnreal : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hnreal
  have hn1 : 1 ≤ n := (Nat.one_le_cast (α := ℝ)).mp hnreal.le
  have hpow : C < (n : ℝ) ^ ε :=
    (Real.rpow_inv_lt_iff_of_pos hC.le (Nat.cast_nonneg n) hε).mp
      (lt_of_le_of_lt (le_max_left _ _) hn)
  obtain ⟨P, hP, hcost⟩ := hbound n hn1
  have hlower : (n : ℝ) ^ (2 : ℕ) ≤ P.cost := by
    exact_mod_cast (by simpa [pow_two] using P.output_size_le_cost hn1 hP : n ^ 2 ≤ P.cost)
  have hstrict : (n : ℝ) ^ (2 : ℕ) < (n : ℝ) ^ (2 : ℕ) := calc
    (n : ℝ) ^ (2 : ℕ) ≤ C * (n : ℝ) ^ (τ + ε) := hlower.trans hcost
    _ < (n : ℝ) ^ ε * (n : ℝ) ^ (τ + ε) :=
      mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hnpos _)
    _ = (n : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_add hnpos, show ε + (τ + ε) = 2 by dsimp [ε]; ring]
      norm_num
  exact lt_irrefl _ hstrict

theorem admissibleExponent_bddBelow (F : Type*) [Ring F] [Nontrivial F] :
    BddBelow {τ : ℝ | AdmissibleExponent F τ} :=
  ⟨2, fun _ h => admissibleExponent_two_le h⟩

theorem omega_le_of_admissibleExponent [Nontrivial F] {τ : ℝ}
    (hτ : AdmissibleExponent F τ) : omega F ≤ τ :=
  csInf_le (admissibleExponent_bddBelow F) hτ

end

end OAI.MatrixMultiplication.Arithmetic

end
