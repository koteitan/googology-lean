/-
Por.BMS: the BMS layer used by the imported 0-Y / 1-Y core (`ZeroY`, `OneY`).
Written independently; Lean core and Std only, no Mathlib.
Taken from koteitan, 1y-wo-por, `Por/BMS.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.Por.BMS.Defs
import Googology.Notation.Y.WellOrder.Por.BMS.Search
import Googology.Notation.Y.WellOrder.Por.BMS.Array
import Googology.Notation.Y.WellOrder.Por.BMS.ParentAncestor
import Googology.Notation.Y.WellOrder.Por.BMS.Context
import Googology.Notation.Y.WellOrder.Por.BMS.CopyLemma
