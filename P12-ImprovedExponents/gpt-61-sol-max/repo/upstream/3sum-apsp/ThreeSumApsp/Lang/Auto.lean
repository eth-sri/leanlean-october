module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Util.RamArith

public meta section
namespace Light

/-- Execute a straight-line block symbolically and discharge its arithmetic obligations. -/
macro "light_block" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
`(tactic| (ram_fields; refine Light.Ends.block ?_ (by light_time [$hs,*]); simp_all [Light.Stmt.Runs, Light.update_frame_setLocal, abs_le, -abs_mul, $hs,*]; zify at *; ring_nf at *; simp_all; all_goals first | omega | grind | ((repeat' constructor) <;> nlinarith)))

end Light
