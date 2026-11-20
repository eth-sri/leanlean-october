module

public import OAI.LinearAlgebra.MatrixMultiplication.Model

@[expose] public noncomputable section

namespace OAI.MatrixMultiplication.Arithmetic

/-- A partially emitted program; its pool is the set of scalar functions
already available in registers. Reindexing old wires is internal to `Step`. -/
structure Code (F I : Type*) where
  size : ℕ
  prog : Program F I size

namespace Code
variable {F I J A : Type*} [Ring F]
abbrev Value (F I : Type*) := (I → F) → F

def pool (p : Code F I) : Set (Value F I) := Set.range fun i x => p.prog.eval x i

structure Step (p q : Code F I) (k : ℕ) : Prop where
  keep : p.pool ⊆ q.pool
  cost : q.prog.cost ≤ p.prog.cost + k

theorem Step.refl (p : Code F I) : Step p p 0 := ⟨fun _ h => h, by simp⟩

theorem Step.trans {p q r : Code F I} {k l} (h : Step p q k) (g : Step q r l) : Step p r (k+l) :=
  ⟨h.keep.trans g.keep, by linarith [h.cost,g.cost]⟩

abbrev push (p : Code F I) (g : Gate F I (Fin p.size)) : Code F I := ⟨_, p.prog.step g⟩

theorem pushed (p : Code F I) (g : Gate F I (Fin p.size)) : Step p (p.push g) g.cost :=
  ⟨fun _ ⟨i,hi⟩ => ⟨i.succ,hi⟩, le_rfl⟩

/-- A computation extends one concrete program, with a budget and a
postcondition on the values it leaves available. -/
def Build (p : Code F I) (c : ℕ) (Q : Set (Value F I) → Prop) :=
  ∃ q, Step p q c ∧ Q q.pool

namespace Build
variable {p : Code F I} {P Q : Set (Value F I) → Prop} {c d : ℕ}

theorem bind (h : Build p c P) (g : ∀ q, p.pool ⊆ q.pool → P q.pool → Build q d Q) : Build p (c+d) Q := by
  obtain ⟨q,hq,hP⟩ := h; obtain ⟨r,hr,hQ⟩ := g q hq.keep hP
  exact ⟨r,hq.trans hr,hQ⟩

private theorem fold [Fintype A] [DecidableEq A] (Q : Finset A → Set (Value F I) → Prop)
    (start : Build p 0 (Q ∅)) (next : ∀ i t, i ∉ t → ∀ q, p.pool ⊆ q.pool → Q t q.pool → Build q c (Q (insert i t))) :
    Build p (Fintype.card A*c) (Q Finset.univ) := by
  suffices ∀ t, Build p (t.card*c) (Q t) by simpa using this Finset.univ
  intro t; induction t using Finset.induction_on with
  | empty => simpa using start
  | insert i t hi ih => simpa [hi,add_mul] using ih.bind (next i t hi)

theorem batch [Fintype J] (Q : J → Set (Value F I) → Prop) (hm : ∀ j, Monotone (Q j))
    (each : ∀ j q, p.pool ⊆ q.pool → Build q c (Q j)) : Build p (Fintype.card J*c) (fun s => ∀ j, Q j s) := by
  classical
  simpa using fold (fun t s => ∀ j ∈ t, Q j s) ⟨p,.refl _,by simp⟩ (by
    intro j t hj q hq ht
    obtain ⟨r,hr,he⟩ := each j q hq
    exact ⟨r,hr,by simpa using And.intro he (fun i hi => hm i hr.keep (ht i hi))⟩)

/-- Sources (constants or input reads) are loaded for free. -/
theorem sources [Fintype J] (p : Code F I) (v : J → I ⊕ F) : Build p 0 (fun s => ∀ j, (fun x => Sum.elim x id (v j)) ∈ s) := by
  simpa using batch (fun j s => (fun x => Sum.elim x id (v j)) ∈ s) (fun _ _ _ h hx => h hx) (c := 0) (by
    intro j q _; cases e : v j with
    | inl i => exact ⟨_,q.pushed (.input i),0,rfl⟩
    | inr c => exact ⟨_,q.pushed (.constant c),0,rfl⟩)

abbrev linearForms [Fintype A] (v : J → A → Value F I) (a : J → A → ℤ) (j : J) : Value F I :=
  ∑ i, a j i • v j i

/-- Emit a batch of linear forms, at two operations per term. -/
theorem forms [Fintype J] [Fintype A] (v : J → A → Value F I) (a : J → A → ℤ)
    (hv : ∀ j i, v j i ∈ p.pool) : Build p (Fintype.card J*(Fintype.card A*2))
      (fun s => ∀ j, linearForms v a j ∈ s) := by
  classical
  apply batch (fun j s => linearForms v a j ∈ s) (fun _ _ _ h hx => h hx)
  intro j q hq; apply fold (c := 2) (fun t s => (∑ i ∈ t, a j i • v j i) ∈ s)
  · exact ⟨_,q.pushed (.constant 0),0,rfl⟩
  intro i t hi q' hq' ⟨l,hl⟩
  obtain ⟨u,hu⟩ := hq' (hq (hv j i))
  let b := q'.push (.constant (a j i : F))
  let d := b.push (.mul 0 u.succ)
  refine ⟨_,((q'.pushed _).trans (b.pushed _)).trans (d.pushed (.add 0 l.succ.succ)),0,?_⟩
  rw [Finset.sum_insert hi]; funext x
  change (a j i : F) * q'.prog.eval x u + q'.prog.eval x l = a j i • v j i x + _
  grind [congrFun hu x, congrFun hl x, zsmul_eq_mul]

end Build
end Code

abbrev SquareAlgorithm (F : Type*) (n : ℕ) := MatrixAlgorithm F n n n
abbrev Pos (n : ℕ) := Fin n × Fin n
abbrev Inputs (n : ℕ) := MatrixInput n n n

variable {F : Type*} [Ring F] {n : ℕ}

def entry (x : Inputs n → F) (o : Pos n) := ∑ j, x (.inl (o.1,j)) * x (.inr (j,o.2))

open Code

/-- A block compiler emits the product entries in an arbitrary caller's
register pool. Recursive calls are inlined when they are made, so no
renaming or interpretation of a separately finished program is required. -/
def Compiler (F : Type*) [Ring F] (n k : ℕ) := ∀ {I : Type} (p : Code F I)
  (v : Inputs n → Value F I), (∀ i, v i ∈ p.pool) → Build p k (fun s => ∀ o, entry v o ∈ s)

theorem scalarCompiler : Compiler F 1 1 := by
  intro I p v hv
  obtain ⟨i, hi⟩ := hv (.inl (0,0))
  obtain ⟨j, hj⟩ := hv (.inr (0,0))
  refine ⟨_,p.pushed (.mul i j),fun o => ⟨0,?_⟩⟩
  obtain rfl : o = (0,0) := Subsingleton.elim ..
  funext x; change p.prog.eval x i * p.prog.eval x j = _
  simp [entry, congrFun hi x, congrFun hj x]

end OAI.MatrixMultiplication.Arithmetic
