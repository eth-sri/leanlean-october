module

public import Mathlib

/-! A simp set for explicit finite HK systems. It contains the vector data as well as
normalization rules for finite quantifiers and scalar bounds. Keeping these rules separate
from `simp` avoids unfolding numerical examples in the general theory. -/
register_simp_attr hk_data
