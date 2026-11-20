module

public import Lean.Elab.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp.Attr

/-! The opt-in simplification rules for exact-RAM configurations. -/

register_simp_attr ram_cfg

/-- Reduce a register block's per-instruction permissions and word bounds. -/
register_simp_attr reg_check
/-- Register numbers, bands, and arithmetic descriptions of register ranges. -/
register_simp_attr ram_layout

/-- Compute the register and memory write footprint of structured RAM code. -/
register_simp_attr write_check
