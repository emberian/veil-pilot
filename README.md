# veil-pilot

Two of our protocols modelled in Veil 2.0 (verse-lab/veil `4eaf93e9`, Lean v4.35.0), initiative 19.
Analysis: `/Users/ember/dev/zkml-research/notes/veil/VEIL-VS-OURS.md`.

- `VeilPilot/ChokepointAsync.lean`: the chokepoint device (degg-research `CommitStep.lean`) with an
  asynchronous host, crashes and a snapshot-replaying adversary. Run: `runs/chokepoint-run4.txt`.
- `VeilPilot/CustodyHandover.lean`: a resharing handover for the dark-learning custodians under a
  mobile adversary. Run: `runs/handover-run*.txt`.

Build: `lake build` (the model checks run during elaboration). Veil and the chokepoint device
(emberian/degg-research `experiments/chokepoint-step`) are pinned git dependencies; `lake build`
on a fresh clone fetches and builds them.
- `VeilPilot/ChokepointAriadne.lean`, `VeilPilot/CounterWord.lean`: Ariadne state continuity for the
  chokepoint device. Run: `runs/ariadne-run15.txt`, `runs/counterword.txt`.
- `VeilPilot/AriadneRefines.lean`: the device step (degg-research `AriadneStep.lean`, proved for all
  sizes) is a forward simulation of the Veil model; the one-increment variant is not.
