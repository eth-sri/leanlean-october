module

public import Chazelle.Golf

public import Chazelle.Core.SpecRam

/-!
# Core specification, part 5: the two stages and the final assembly

The target `Chazelle.LinearTimeTriangulation` is obtained from

* `CoreStageSpec` — the visibility-map stage (this design): one structured statement which, from
  the initial configuration, runs in at most `C (n + 1)` steps with words bounded by any
  `W ≥ K (n + 1)` and leaves the trapezoid table (and the empty vertex-chord table) of the
  sheared geometry polygon `Q` in memory (`TablesReady Q`);
* `FinalStageSpec` — the final stage (the `Chazelle.Split`/`Chazelle.Mountain` team): one
  structured statement which, from any configuration holding valid tables for any `Q` related to
  the input by a shear (`ShearRel`), emits a triangulation of `Q` in at most `C (n + 1)` steps,
  reading the input `P` (the machine never sees `Q`; `det` signs and the lexicographic order of
  `P` are those of `Q`: `det_shearPt`, `YlexAgree`);
* `ShearInvarianceSpec` — a triangulation of `Q = shear ε P` is a triangulation of `P`.

`linear_of_core` (**proved**) composes them: the program is `Stmt.compile (s₁ ; s₂) 0 ++ [halt]`,
the step constant is `C₁ + C₂ + 1`, the word constant `K₁ + C₁ + K₂ + 1` (the allocator after the
core is at most its step count).
-/

namespace Chazelle.Core

@[expose] public section

open Chazelle.Machine (Stmt Exec)

/-- **The visibility-map stage.** -/
def CoreStageSpec : Prop :=
  ∃ (s : Stmt) (C K : ℕ), ∀ P : Polygon, P.Simple → ∀ W : ℕ, K * (P.n + 1) ≤ W →
    ∃ c' k, Exec P W s initConfig c' k ∧ k ≤ C * (P.n + 1) ∧ c'.nreg ALLOC ≤ C * (P.n + 1) ∧
      ∃ Q : Polygon, ShearRel P Q ∧ Q.Simple ∧ TablesReady Q c'

/-- **The final stage** (visibility map to triangulation, [6], [11]; `Chazelle.Final`). -/
def FinalStageSpec : Prop :=
  ∃ (s : Stmt) (C K : ℕ), ∀ P Q : Polygon, P.Simple → Q.Simple → ShearRel P Q →
    ∀ (W : ℕ) (c : Config), WordsBounded W c → TablesReady Q c →
      c.nreg ALLOC + K * (P.n + 1) ≤ W →
        ∃ c' k, Exec P W s c c' k ∧ k ≤ C * (P.n + 1) ∧ Q.Triangulates c'.output

/-- `RunsWithin` is monotone in the step budget. -/
theorem runsWithin_mono {prog : Program} {P : Polygon} {W s s' : ℕ}
    {out : List Polygon.Triangle} (h : RunsWithin prog P W s out) (hs : s ≤ s') :
    RunsWithin prog P W s' out := by
  obtain ⟨k, hk, h1, h2⟩ := h
  exact ⟨k, hk.trans hs, h1, h2⟩

/-- **The final assembly.**  The two stage specifications and shear invariance give the target
theorem. -/
theorem linear_of_core (hcore : CoreStageSpec) (hfin : FinalStageSpec)
    (hsh : ShearInvarianceSpec) : LinearTimeTriangulation := by
  obtain ⟨s₁, C₁, K₁, h₁⟩ := hcore
  obtain ⟨s₂, C₂, K₂, h₂⟩ := hfin
  refine ⟨Machine.Stmt.compile (Stmt.seq s₁ s₂) 0 ++ [Instr.halt], C₁ + C₂ + 1, K₁ + C₁ + K₂ + 1,
    ⋄, ⋄, ?_⟩
  intro P hP
  have hW : (K₁ + C₁ + K₂ + 1) * (P.n + 1) =
      K₁ * (P.n + 1) + C₁ * (P.n + 1) + K₂ * (P.n + 1) + (P.n + 1) := ⋆
  obtain ⟨c₁, k₁, e₁, hk₁, halloc, Q, hPQ, hQ, hready⟩ :=
    h₁ P hP ((K₁ + C₁ + K₂ + 1) * (P.n + 1)) (by rw [hW]; omega)
  obtain ⟨c₂, k₂, e₂, hk₂, htri⟩ := h₂ P Q hP hQ hPQ ((K₁ + C₁ + K₂ + 1) * (P.n + 1)) c₁
    e₁.wb_right hready (by rw [hW]; omega)
  refine ⟨c₂.output, ?_, ?_⟩
  · have hr := Machine.runsWithin_of_exec (Exec.seq e₁ e₂)
    refine runsWithin_mono hr ?_
    have hC : (C₁ + C₂ + 1) * (P.n + 1) = C₁ * (P.n + 1) + C₂ * (P.n + 1) + (P.n + 1) := ⋆
    Ξ hC
    omega
  · obtain ⟨ε, -, rfl, -⟩ := hPQ
    exact ((hsh ε P).2 _).1 htri

end

end Chazelle.Core
