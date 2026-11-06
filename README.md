# veil-pilot

Two of our protocols modelled in Veil 2.0 (verse-lab/veil `4eaf93e9`, Lean v4.35.0), initiative 19.
Analysis: `/Users/ember/dev/zkml-research/notes/veil/VEIL-VS-OURS.md`.

- `VeilPilot/ChokepointAsync.lean`: the chokepoint device (degg-research `CommitStep.lean`) with an
  asynchronous host, crashes and a snapshot-replaying adversary. Run: `runs/chokepoint-run4.txt`.
- `VeilPilot/CustodyHandover.lean`: a resharing handover for the dark-learning custodians under a
  mobile adversary. Run: `runs/handover-run*.txt`.

Build: `lake build` (the model checks run during elaboration). The lakefile points at the shared
checkout `/Users/ember/src/veil` and reuses its dependency store; a stranger swaps in the git
`require` given in the lakefile comment.
