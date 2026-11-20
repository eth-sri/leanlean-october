/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RowReadback

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd Cardinal

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}

/-- A finite request: a block (to be a non-successor below the stage) and an offset. -/
structure BlockRequest where
  /-- The requested limit block. -/
  block : Ordinal.{0}
  /-- The requested finite offset. -/
  offset : ℕ

open Classical in
/-- The blocks of a request list. -/
noncomputable def blocksOf (reqs : List BlockRequest) : Finset Ordinal.{0} :=
  reqs.toFinset.image BlockRequest.block

open Classical in
theorem mem_blocksOf {reqs : List BlockRequest} {μ : Ordinal.{0}} :
    μ ∈ blocksOf reqs ↔ ∃ r ∈ reqs, r.block = μ := by
  unfold blocksOf
  simp

/-- An intermediate enlarged context: a realized tuple with the root as a face. -/
structure Ctx (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M) : Type (max 1 w) where
  m : ℕ
  ctx : Fin m ↪ M
  proj : Fin n ↪ Fin m
  proj_ctx : proj.trans ctx = t
  p₀ : S α.1 m
  eval_ctx : R.eval ctx = some p₀

namespace Ctx

variable {n : ℕ} {t : Fin n ↪ M}

/-- The root context. -/
def root (p : S α.1 n) (hp : R.eval t = some p) : Ctx R t :=
  ⟨n, t, Function.Embedding.refl _, by ext i; rfl, p, hp⟩

/-- One coface step: adjoin a fresh point realizing a coface `q` of the current type. -/
def step (C : Ctx R t) (y : M) (hy : y ∉ Set.range C.ctx) (q : S α.1 (C.m + 1))
    (heval : R.eval (snoc C.ctx y hy) = some q) : Ctx R t :=
  ⟨C.m + 1, snoc C.ctx y hy, C.proj.trans Fin.castSuccEmb, by
    rw [Function.Embedding.trans_assoc, castSuccEmb_trans_snoc, C.proj_ctx], q, heval⟩

end Ctx

/-- **The finite reference context** over a root tuple `t`, for the requests `reqs`. -/
structure ReferenceContext (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M)
    (reqs : List BlockRequest) extends Ctx R t where
  /-- The cap: an old full-grade cell. -/
  capBase : Cell p₀.scheme.scheme
  /-- The cap has grade `N`. -/
  cap_grade : p₀.scheme.scheme.grade capBase = m
  /-- The block representatives. -/
  repBase : Ordinal.{0} → Cell p₀.scheme.scheme
  /-- Their offsets. -/
  repOff : Ordinal.{0} → ℕ
  /-- Each representative carries its block plus a finite offset. -/
  rep_label : ∀ r ∈ reqs, p₀.label (repBase r.block) = ofOrd (r.block + repOff r.block)
  /-- The offsets are below the threshold. -/
  rep_off_lt : ∀ r ∈ reqs, repOff r.block < m
  /-- The requested offsets are below the threshold. -/
  offset_lt : ∀ r ∈ reqs, r.offset < m

namespace ReferenceContext

variable {n : ℕ} {t : Fin n ↪ M} {reqs : List BlockRequest} (C : ReferenceContext R t reqs)

/-- At full grade the cap has full scope. -/
theorem cap_index : C.p₀.scheme.scheme.cell C.capBase = (Finset.univ, C.m) := by
  rw [CellScheme.cell_eq, C.cap_grade]
  have h := C.p₀.scheme.scheme.grade_le_card_scope C.capBase
  rw [C.cap_grade] at h
  exact Prod.ext (Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) (by simpa only [Fintype.card_fin] using h))) rfl

end ReferenceContext

/-- A label in the band `[μ, μ + ω)` is `μ + j` for a finite `j`. -/
theorem exists_nat_of_band {μ : Ordinal.{0}} {x : ExtOrd} (h1 : ofOrd μ ≤ x)
    (h2 : x < ofOrd (μ + Ordinal.omega0)) : ∃ j : ℕ, x = ofOrd (μ + j) := by
  obtain ⟨β, rfl⟩ : ∃ β : Ordinal.{0}, x = ofOrd β := by
    rcases x with _ | _ | β
    all_goals tauto
  rw [ofOrd_le_ofOrd] at h1
  rw [ofOrd_lt_ofOrd] at h2
  obtain ⟨j, hj⟩ := Ordinal.lt_omega0.mp (Ordinal.sub_lt_of_lt_add h2 Ordinal.omega0_pos)
  refine ⟨j, ?_⟩
  rw [← hj, Ordinal.add_sub_cancel_of_le h1]

/-- Below a limit stage, a block plus a finite offset stays below the stage. -/
theorem add_nat_lt_stage {μ : Ordinal.{0}} (hμ : μ < α.1) (j : ℕ) : μ + j < α.1 :=
  lt_of_lt_of_le ((add_lt_add_iff_left μ).mpr (Ordinal.natCast_lt_omega0 j))
    (add_omega0_le_of_lt_isSuccLimit α.2 hμ)

theorem stage_pos : (0 : Ordinal.{0}) < α.1 := by
  have := α.2.bot_lt
  simpa using this

/-- **Bridge to `ReadbackInputs.block_limit`**: a non-successor block is its own limit part. -/
theorem limitPart_eq_self_of_isNonSuccessor {μ : Ordinal.{0}} (h : Value.IsNonSuccessor μ) :
    limitPart μ = μ := by
  rcases h with rfl | h
  · simp [limitPart]
  · exact le_antisymm (limitPart_le μ) (succLimit_le_limitPart h le_rfl)

end VaughtConjecture.Knight
