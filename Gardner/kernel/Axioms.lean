import Gardner.kernel.Reduction
import Gardner.kernel.MomentContexts
import Lean.Util.CollectAxioms

namespace Gardner.Kernel
open Lean Elab Command

/-- A regression check on the complete imported theorem dependencies. The
mathematical results themselves are checked by the kernel during compilation. -/
def verifyAllowedAxioms (names : Array Name) : CommandElabM Unit := do
  for name in names do
    unless (← getEnv).contains name do throwError "missing theorem {name}"
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext,`Classical.choice,`Quot.sound].contains axiomName do
        throwError "unapproved axiom {axiomName} in {name}"

run_cmd do
  verifyAllowedAxioms #[`Gardner.Bridge.no_isolated30,`Gardner.Bridge.paired_axes30,
    `Gardner.Bridge.fully_paired_axis_moment,`Gardner.Bridge.deficient_sum_axis_balance,
    `Gardner.Kernel.at_least_28_diagonals,`Gardner.Kernel.equal_spans_of_fewer_than_30,
    `Gardner.Kernel.reduce30,`Gardner.Kernel.MomentCuts.check_sound,
    `Gardner.Kernel.MomentCuts.residual_realizes,
    `Gardner.Kernel.MomentCuts.paired_residual_realizes]
  for i in [:2032] do
    verifyAllowedAxioms #[Name.str `Gardner.Kernel.MomentContexts s!"leaf{i}"]
  logInfo "PASS standard-axiom audit of structural results and all 2032 moment contexts."

end Gardner.Kernel
