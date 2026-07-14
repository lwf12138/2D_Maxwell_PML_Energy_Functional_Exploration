---
fact_id: fact:2d_maxwell_pml_energy_functional_exploration:v6-elliptic-correction-residual
problem_id: 2d_maxwell_pml_energy_functional_exploration
source_project: 2d_maxwell_pml_energy_functional_exploration
source_task: task-v6-nonlocal-and-route-audit
predecessors:
  - fact:2d_maxwell_pml_energy_functional_exploration:variable-baffet-remainder-small-gradient
status: verified
fact_type: obstruction
review_level: verified
claim_policy: stable_claim
claim_summary: "The proposed static elliptic nonlocal correction does not cancel the variable Baffet remainder after complete time differentiation."
verification: verify-20260714T112105126790Z-fact-verify-fact-2d_maxwell_pml_energy_f
---

## statement

Let A(z,v)=(C grad z,grad v)+(c z,v)=-(u grad a,grad v), with a time-independent coercive elliptic operator, and F=eta(lambda,grad z)+eta A(z,z)/2. Then z_t solves A(z_t,v)=-(u_t grad a,grad v), and exactly F prime/eta=(lambda_t,grad z)+(lambda-u grad a,grad z_t). Hence (E_B+F) prime retains -(u grad a,lambda) and adds lambda_t and u_t terms; it does not yield the claimed cancellation. A second static elliptic variable produces u_t lambda+u lambda_t terms, while a temporal primitive r_t=lambda cancels the target only at the cost of the new term (u_t grad a,r) and loss of natural-norm equivalence. This rejects the displayed candidate, not every possible nonlocal Lyapunov operator.

## notes

Evidence: artifacts/proofs/v6_nonlocal_route_audit.md; results/v6_tex report section 5; exact Lean and SymPy proxy identities.
