module

public import HK.SBC5

/-!
# Perpetual SBC oscillation with arbitrarily small radius spread

For `0 < δ ≤ 1`, the five-agent system has initial state `sbc5_lim + δ • sbc5_v`
and radii `(6-3δ, 6+3δ, 6+3δ, 6+3δ, 6-3δ)`. Its constant neighborhood table is
the same as that of `sbc5_x0`, and its offset at time `t` is `sbc5Rate^t * δ • sbc5_v`.
Thus the radius ratio can be arbitrarily close to one while the three interior agents
continue crossing their limits forever.
-/
