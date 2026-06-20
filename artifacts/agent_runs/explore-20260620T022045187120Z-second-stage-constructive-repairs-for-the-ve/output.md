# Explore output

Run id: `explore-20260620T022045187120Z-second-stage-constructive-repairs-for-the-ve`

This run treated the verified first-stage report as a partial solution for the
second-stage constructive goal. The existing terminal artifact proves the edge-PML
linear-growth obstruction and a Gronwall estimate; it does not yet provide a repaired
monotone or uniformly bounded energy.

## Main insight

The obstruction is the zero-transverse-frequency shifted magnetic invariant in an edge
layer. For constant `sigma_x=s>0`, `sigma_y=0`, the verified edge mode reduces to

```text
M_x = Q_x + mu*(s/epsilon_0)*H_x,
H_{x,t} = M_x / mu,
M_{x,t} = 0.
```

This is a Jordan block. A second-stage repair must either exclude this invariant by
compatibility, damp it by changing the shifted-memory dynamics, or use a CFS/split
formulation that moves the zero-frequency pole.

## Candidate repairs

1. Compatibility/quotient route: keep the source equations but require the transverse
   zero-mode projection of the undamped shifted invariant to vanish. This may give a
   bounded estimate on a restricted data class, not for arbitrary eight-variable data.

2. Damped shifted-variable or MPML route: change the shifted equations to include
   edge-positive damping, for example `M_t = source - gamma M`. The zero-mode ODE
   admits a positive quadratic Lyapunov functional with a cross term, so this directly
   removes the verified Jordan block.

3. CFS/split-field route: reformulate the PML memories with positive frequency shifts.
   This is the most plausible arbitrary-data repair, but it is a modified-model
   theorem, not a theorem about the original source equations.

4. Corner-first route: because both shifted memories are damped when
   `sigma_x,sigma_y>0`, constant corners deserve a separate frozen-mode Lyapunov
   search. This cannot by itself solve the edge-inclusive source problem.

## Created artifacts

- `artifacts/route_checks/second-stage-constructive-repairs-for-the-verified-edge-pml-linear-growt/explore-20260620T022045187120Z-second-stage-constructive-repairs-for-the-ve/exploration_report.md`
- `artifacts/route_checks/second-stage-constructive-repairs-for-the-verified-edge-pml-linear-growt/explore-20260620T022045187120Z-second-stage-constructive-repairs-for-the-ve/candidate_routes.json`
- `artifacts/route_checks/second-stage-constructive-repairs-for-the-verified-edge-pml-linear-growt/explore-20260620T022045187120Z-second-stage-constructive-repairs-for-the-ve/artifact_manifest.json`

## Proposed next TASK_POOL entries

- `task-stage2-edge-compat-fourier`: prove/refute the constant-coefficient edge
  compatibility route and identify the exact admissible data condition.
- `task-stage2-damped-shifted-lyapunov`: prove the damped shifted-variable zero-mode
  Lyapunov lemma and extend/falsify it for frozen nonzero modes.
- `task-stage2-cfs-split-field-model`: derive a CFS/split-field alpha=1 repaired model
  and run frozen-mode Lyapunov checks for edges and corners.

No durable facts were promoted. The claims below remain candidate facts requiring
verification.
