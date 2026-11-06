module

public import OAI.NumberTheory.PrimeGaps.TensorProfiles

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set





open scoped Classical



open scoped Convolution Pointwise

def PatternMaps {ι : Type*} (r : Setoid ι) (α : Type*) :=
  {b : ι → α // Setoid.ker b = r}

noncomputable def patternLift {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) :
    Quotient r → α :=
  Quotient.lift b.val (by
    intro i j hij
    rw [←b.property] at hij
    exact hij)

@[simp] theorem patternLift_mk {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) (i : ι) :
    patternLift b (Quotient.mk r i)=b.val i := rfl

theorem patternLift_injective {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) :
    Function.Injective (patternLift b) := by
  intro x y
  induction x using Quotient.inductionOn with | h i =>
    induction y using Quotient.inductionOn with | h j =>
      intro h
      apply Quotient.sound
      rw [←b.property]
      simp_all

noncomputable def patternClass {ι α : Type*} [Fintype ι] [Fintype α]
    (r : Setoid ι) : Finset (ι → α) := Finset.univ.filter (fun b => Setoid.ker b=r)

@[simp] theorem mem_patternClass {ι α : Type*} [Fintype ι] [Fintype α]
    (r : Setoid ι) (b : ι → α) : b∈patternClass r ↔ Setoid.ker b=r := by
  simp [patternClass]

noncomputable instance finiteSetoidFintype (ι : Type*) [Fintype ι] : Fintype (Setoid ι) :=
  Fintype.ofInjective (fun r : Setoid ι => r.r) (fun _ _ h => Setoid.ext (by intro i j; exact Iff.of_eq (congrFun (congrFun h i) j)))

noncomputable def patternEmbedding {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) :
    Quotient r ↪ α := ⟨patternLift b,patternLift_injective b⟩

noncomputable def embeddingPattern {ι α : Type*} (r : Setoid ι) (e : Quotient r ↪ α) :
    PatternMaps r α := ⟨fun i => e (Quotient.mk r i),by
  apply Setoid.ext
  intro i j
  change e (Quotient.mk r i)=e (Quotient.mk r j) ↔ r i j
  rw [e.injective.eq_iff,Quotient.eq]⟩

noncomputable def patternEquivEmbedding {ι α : Type*} (r : Setoid ι) :
    PatternMaps r α ≃ (Quotient r ↪ α) where
  toFun := patternEmbedding
  invFun := embeddingPattern r
  left_inv b := by apply Subtype.ext; rfl
  right_inv e := by
    apply Function.Embedding.ext
    intro x
    induction x using Quotient.inductionOn with | h i => rfl

noncomputable def patternClassEquiv {ι α : Type*} [Fintype ι] [Fintype α] (r : Setoid ι) :
    {b // b∈patternClass (α:=α) r} ≃ (Quotient r ↪ α) :=
  (Equiv.subtypeEquivRight (fun b => mem_patternClass r b)).trans (patternEquivEmbedding r)

theorem constant_boxTuple_injective_iff {s h : ℕ} (a : ℤ) (n : Fin s → Fin h) :
    Function.Injective (boxTuple (fun _ => a) n) ↔ Function.Injective n := by
  constructor
  · intro hn i j he
    apply hn
    simp [boxTuple,he]
  · intro hn i j he
    apply hn
    have hv : (n i:ℕ)=(n j:ℕ) := by
      exact_mod_cast (add_left_cancel he : (n i:ℤ)=(n j:ℤ))
    omega

noncomputable def patternTupleEquiv {ι : Type*} [Fintype ι] (r : Setoid ι) (h : ℕ) (a : ℤ) :
    {b // b∈patternClass (α:=Fin h) r} ≃
    {n // n∈distinctBox (s:=Fintype.card (Quotient r)) (h:=h) (fun _ => a)} :=
  (patternClassEquiv r).trans
    ((Equiv.embeddingCongr (Fintype.equivFin (Quotient r)) (Equiv.refl (Fin h))).trans
      ((Equiv.subtypeInjectiveEquivEmbedding _ _).symm.trans
        (Equiv.subtypeEquivRight (fun n => by
          simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and,
            constant_boxTuple_injective_iff]))))

@[simp] theorem patternTupleEquiv_apply {ι : Type*} [Fintype ι] (r : Setoid ι) (h : ℕ) (a : ℤ)
    (b : {b // b∈patternClass (α:=Fin h) r}) (j : Fin (Fintype.card (Quotient r))) :
    (patternTupleEquiv r h a b).val j=
      patternLift ⟨b.val,(mem_patternClass r b.val).mp b.property⟩
        ((Fintype.equivFin (Quotient r)).symm j) := rfl

end LargePrimeGaps

end OAI
