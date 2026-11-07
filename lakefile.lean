import Lake
open Lake DSL

require veil from git "https://github.com/verse-lab/veil.git" @ "4eaf93e9b7d0a4f850244db956e5f2d1e1bf9a71"

-- The chokepoint device (degg-research experiments/chokepoint-step), for the refinement theorem
-- `VeilPilot/AriadneRefines.lean`.
require chokepoint from git "https://github.com/emberian/degg-research.git" @ "8af679e6295d35481ba5d94bc2aeaac64a5c395d" / "experiments/chokepoint-step"

package «veil-pilot»

@[default_target]
lean_lib VeilPilot where
  globs := #[.submodules `VeilPilot]
