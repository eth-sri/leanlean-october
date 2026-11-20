/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReferenceContext

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd

noncomputable section

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}
  {n : ℕ} {t : Fin n ↪ M}

/-- The reference-only prefix of acquisition, with no intermediate cap. -/
structure RawReferenceContext (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M)
    (blocks : Finset Ordinal.{0}) extends Ctx R t where
  repBase : blocks → Cell p₀.scheme.scheme
  repOff : blocks → ℕ
  rep_label : ∀ μ, p₀.label (repBase μ) = ofOrd (μ.1 + repOff μ)

namespace RawReferenceContext

variable {blocks : Finset Ordinal.{0}} (C : RawReferenceContext R t blocks)

/-- A finite bound chosen after the actual offsets have been obtained. -/
def offsetBound : ℕ := Finset.univ.sup C.repOff

theorem rep_off_le (μ : blocks) : C.repOff μ ≤ C.offsetBound :=
  Finset.le_sup (f := C.repOff) (Finset.mem_univ μ)

def step {y : M} {hy : y ∉ Set.range C.ctx} {q : S α.1 (C.m + 1)}
    (hq : IsCoface C.p₀ q) (heval : R.eval (snoc C.ctx y hy) = some q) :
    RawReferenceContext R t blocks :=
  ⟨C.toCtx.step y hy q heval, hq.extendsDomain.cellOf ∘ C.repBase, C.repOff,
    fun μ => (hq.label_cellOf (C.repBase μ)).trans (C.rep_label μ)⟩

/-- Increase arity without changing the offsets of the previously acquired cells. -/
theorem pad (hM : R.IsModel) (k : ℕ) :
    ∃ C' : RawReferenceContext R t blocks, C'.m = C.m + k ∧ C'.repOff = C.repOff := by
  induction k with
  | zero => exact ⟨C, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨C', hm, ho⟩ := ih
    obtain ⟨y, hy, q, -, hcof, heval⟩ := hM.highGradeDominance C'.ctx C'.p₀ C'.eval_ctx 0 stage_pos
    exact ⟨C'.step hcof heval, congrArg (· + 1) hm, ho⟩

end RawReferenceContext

/-- Acquire the root and raw representatives only. In particular the empty
request set performs no padding or high-grade dominance step. -/
theorem exists_rawReferenceContext (hM : R.IsModel) (p : S α.1 n)
    (hp : R.eval t = some p) (blocks : Finset Ordinal.{0})
    (hblocks : ∀ μ ∈ blocks, IsNonSuccessor μ ∧ μ < α.1) :
    Nonempty (RawReferenceContext R t blocks) := by
  classical
  have acquire : ∃ C : Ctx R t, ∀ μ ∈ blocks, ∃ (c : Cell C.p₀.scheme.scheme) (j : ℕ),
      C.p₀.label c = ofOrd (μ + j) := by
    induction blocks using Finset.induction_on with
    | empty => exact ⟨Ctx.root p hp, by simp⟩
    | @insert μ blocks _ ih =>
      obtain ⟨C, hC⟩ := ih fun ν hν => hblocks ν (Finset.mem_insert_of_mem hν)
      obtain ⟨hns, hlt⟩ := hblocks μ (Finset.mem_insert_self _ _)
      obtain ⟨y, hy, q, ⟨d, hlo, hhi⟩, hcof, heval⟩ :=
        hM.uniformity C.ctx C.p₀ C.eval_ctx μ hns hlt
      refine ⟨C.step y hy q heval, fun ν hν => ?_⟩
      rcases Finset.mem_insert.mp hν with rfl | hν
      · obtain ⟨j, hj⟩ := exists_nat_of_band hlo hhi
        exact ⟨d, j, hj⟩
      · obtain ⟨c, j, hj⟩ := hC ν hν
        exact ⟨hcof.extendsDomain.cellOf c, j, (hcof.label_cellOf c).trans hj⟩
  obtain ⟨C, hC⟩ := acquire
  choose rep off hrep using fun μ : blocks => hC μ μ.2
  exact ⟨⟨C, rep, off, hrep⟩⟩

end

end VaughtConjecture.Knight
