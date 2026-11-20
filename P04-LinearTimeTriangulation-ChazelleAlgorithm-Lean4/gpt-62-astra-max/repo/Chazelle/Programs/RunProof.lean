module

public import Chazelle.Programs.Verification
public meta import Lean.Elab.Tactic.RCases

/-!
# Strengthening execution specifications

A write-mask theorem derives a frame from the execution itself. Discharge that conjunct
separately from symbolic execution, without restating the spec and copying every register
value from the first spec into the second.
-/

public meta section
namespace Chazelle.Programs
open Lean Meta Elab Tactic

/-- Strip the final frame conjunct, using `pf` with the run named `e` to restore it. -/
elab "frame_from " e:ident " => " pf:term : tactic => withMainContext do
  let_expr Exists dc pred := ← whnf (← getMainTarget) | throwError "expected a run specification"
  withLocalDeclD `d dc fun d => do
    let_expr Exists kc post := pred.beta #[d] | throwError "expected a cost witness"
    withLocalDeclD `k kc fun k => do
      let mut t := post.beta #[k]
      let mut parts := #[]
      while t.isAppOfArity ``And 2 do
        parts := parts.push t.appFn!.appArg!
        t := t.appArg!.headBeta
      unless parts.size ≥ 2 do throwError "expected a postcondition and a frame"
      let body := parts.pop.foldr mkAnd parts.back!
      let ty ← mkAppM ``Exists #[← mkLambdaFVars #[d] (← mkAppM ``Exists #[← mkLambdaFVars #[k] body])]
      let premise ← Term.exprToSyntax ty
      let mut names := #[← `(ident| d), ← `(ident| k), e]
      for i in [1:parts.size] do names := names.push (← `(ident| $(mkIdent <| Name.mkSimple s!"__post{i}")))
      let ps ← names.mapM fun id => `(rcasesPat| $id:ident)
      let xs ← names.mapM fun id => `($id:ident)
      evalTactic (← `(tactic| suffices prior : $premise by
        obtain ⟨$ps,*⟩ := prior
        exact ⟨$xs,*, $pf⟩))

/-- Finish a specification with the given execution and the facts about its final state. -/
macro "finish_run " e:term:max : tactic =>
  `(tactic| (refine ⟨_, _, $e, ?_⟩; first | block_post | grind))

end Chazelle.Programs
