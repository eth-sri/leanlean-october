module

@[expose] public section

set_option hygiene false
open Lean in
macro "𝗇" a:ident t:term : command =>
  `(set_option hygiene false in local notation $(Syntax.mkStrLit $ a.getId.toString (escape := false) ):str => $t)
open Lean in
macro "𝗁" a:ident x:ident t:term : command =>
  `(set_option hygiene false in local notation:max $(Syntax.mkStrLit $ a.getId.toString (escape := false) ):str $x:ident:max => $t)
open Lean in
macro "𝗃" a:ident t:term : command =>
  `(set_option hygiene false in set_option linter.unusedVariables false in local notation:max $(Syntax.mkStrLit $ a.getId.toString (escape := false) ):str ἀ:max => $t)
open Lean in
macro "𝗀" a:ident t:term : command =>
  `(set_option hygiene false in notation $(Syntax.mkStrLit (String.map (fun c => if 0x1d49c ≤ c.toNat && c.toNat ≤ 0x1d59f then Char.ofNat (c.toNat + 0x104) else c) (a.getId.toString (escape := false)))):str => $t)
macro "𝗌" : command => `(@[expose] public section
noncomputable section)
macro "𝗍" : command => `(public section
noncomputable section)
macro "𝗎" : command => `(@[expose] public section
noncomputable section
namespace NearlyMinimax)
macro "𝚨" : command => `(namespace NearlyMinimax)
macro "𝚩" : command => `(set_option backward.isDefEq.respectTransparency false)
macro "𝚪" : command => `(open scoped BigOperators)
macro "𝚫" : command => `(open MeasureTheory Set)
macro "𝚬" : command => `(attribute [local instance] Classical.propDecidable)
macro "𝚭" : command => `(set_option maxHeartbeats 1000000)
macro "𝚮" : command => `(open scoped ENNReal)
macro "𝚯" : command => `(open MeasureTheory)
macro "𝚰" : command => `(set_option maxHeartbeats 600000)
macro "𝚱" : command => `(set_option maxHeartbeats 800000)
macro "𝚳" : command => `(open scoped BigOperators ENNReal)
macro "𝚴" : command => `(open MeasureTheory ProbabilityTheory Set)
macro "𝚵" : command => `(open MeasureTheory ProbabilityTheory)
macro "𝚶" : command => `(open scoped Topology)
macro "𝚷" : command => `(open Filter)
macro "𝚸" : command => `(open Set MeasureTheory)
macro "𝚹" : command => `(open MeasureTheory ProbabilityTheory Filter Set)
macro "𝚺" : command => `(open scoped BigOperators Matrix.Norms.L2Operator)
macro "𝚻" : command => `(open scoped RealInnerProductSpace)
macro "𝚼" : command => `(open scoped Matrix.Norms.L2Operator)
macro "𝚽" : command => `(set_option maxHeartbeats 500000)
macro "𝚾" : command => `(set_option maxHeartbeats 700000)
macro "𝚿" : command => `(attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend)
macro "𝛀" : command => `(set_option backward.isDefEq.respectTransparency true)
macro "𝛃" : command => `(set_option synthInstance.maxHeartbeats 200000)
macro "𝛄" : command => `(open MeasureTheory Set MvPolynomial)
macro "𝛅" : command => `(open MeasureTheory Set Filter)
macro "𝛆" : command => `(set_option maxHeartbeats 1200000)
macro "𝛇" : command => `(variable (C : ModelConstants d))
macro "𝛈" : command => `(set_option maxHeartbeats 1500000)
macro "𝛉" : command => `(open scoped ENNReal BigOperators)
macro "𝛊" : command => `(open MeasureTheory Filter Set)
macro "𝛋" : command => `(open Set MeasureTheory Function)
macro "𝛌" : command => `(variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H])
macro "𝛍" : command => `(open MeasureTheory Set Matrix)
macro "𝛎" : command => `(open Matrix MeasureTheory Set)
macro "𝛏" : command => `(open MeasureTheory ProbabilityTheory Set Filter)
macro "𝛔" : command => `(variable (i : Fin n))
