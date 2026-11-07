import Lake
open Lake DSL

-- Dev: Veil at the shared checkout, already built, with its dependency store reused (no second
-- copy). For a stranger: replace with
--   require veil from git "https://github.com/verse-lab/veil.git" @ "4eaf93e9b7d0a4f850244db956e5f2d1e1bf9a71"
-- and drop `packagesDir`.
require veil from "/Users/ember/src/veil"

package «veil-pilot» where
  packagesDir := "/Users/ember/src/veil/.lake/packages"

@[default_target]
lean_lib VeilPilot where
  globs := #[.submodules `VeilPilot]

-- The device of degg-research's chokepoint experiment, compiled from its source tree (no copy), for
-- the refinement theorem `VeilPilot/AriadneRefines.lean`.
lean_lib AriadneStep where
  srcDir := "/Users/ember/dev/degg-research/experiments/chokepoint-step"
  roots := #[`AriadneStep]
