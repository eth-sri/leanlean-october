module
public import Mathlib.Tactic
public meta section
open Lean Elab Tactic Meta

/-- Expose the fields of propositional records before arithmetic normalization. -/
elab "ram_fields" : tactic => do
  for _ in [:32] do
    let h? ← withMainContext do
      let env ← getEnv
      let mut found := none
      for h in ← getLCtx do
        if (← isProp h.type) && isStructure env ((← whnf h.type).getAppFn.constName?.getD .anonymous) then
          found := some h.fvarId
          break
      return found
    let some h := h? | break
    let gs ← (← getMainGoal).cases h
    replaceMainGoal (gs.toList.map (·.mvarId))

macro "ram_arith" : tactic =>
  `(tactic| (ram_fields; simp_all [abs_le, -abs_mul] <;> first | omega | nlinarith))
macro "ram_arith" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (ram_fields; simp_all [abs_le, -abs_mul, $hs,*] <;> first | omega | nlinarith))

macro "ram_safe" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (intros; ram_fields; try simp_all [abs_le, -abs_mul, $hs,*]; try zify at *; try ring_nf at *; try simp_all; all_goals first | omega | nlinarith | grind | ((repeat' constructor) <;> nlinarith)))
macro "ram_safe" : tactic => `(tactic| ram_safe [])

macro "ram_aesop" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (intros; ram_fields; try simp_all [abs_le, -abs_mul, $hs,*]; aesop))
macro "ram_grind" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (intros; ram_fields; try simp_all [abs_le, -abs_mul, $hs,*]; grind))
macro "ram_grind" : tactic => `(tactic| ram_grind [])
