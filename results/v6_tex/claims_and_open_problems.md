# Claims and open problems (v6)

## Proved in the declared scope

1. The separated-coordinate strict Maxwell--Debye PML is exactly represented
   by the displayed Baffet primitive system on the causal compatibility
   manifold.
2. At a flat `x` interface with no tangential stretch, the causal outgoing
   square-root branch has `Y_+=Y_0`, hence `R=0`, for every `Re s>0`, real
   tangential frequency, and arbitrary nonnegative normal profile.
3. The variable-coefficient identity is exactly
   `E_B'=-D_0-(u grad a,lambda)+B`.
4. On a uniformly positive corner PML, `E_B` is norm-equivalent and monotone
   under nonpositive flux and the uniform pointwise Schur margin
   `(grad a)^T C_lambda^{-1}(grad a)<4 mu epsilon a b`.
5. The proposed elliptic correction differentiates to
   `(lambda_t,grad z)+(lambda-u grad a,grad z_t)` and does not cancel the
   Baffet remainder.

## Explicitly not claimed

- No unconditional Level-A monotone energy is claimed for every nonnegative
  `W^{1,infty}` profile.
- Inner-interface perfect matching is not identified with zero reflection from
  a finite PML's outer truncation.
- Multi-axial/cross damping is not called perfectly matched when it changes the
  tangential stretch and hence oblique admittance.
- A Gronwall estimate is not called monotonicity.
- The passive port layer is not substituted for the strict stretched PML.
- The finite-dimensional proxy is not a proof of PDE nonexistence; it is an
  exact audit of the proposed algebra and a necessary-condition test.
- Gramian positivity/equivalence is not claimed without independent exponential
  stability and exact observability.

## Open problems

1. Prove profile-uniform resolvent estimates for the compatible variable-
   coefficient strict-PML generator, or produce a genuine full-PDE
   impossibility theorem.
2. Solve the local symmetrizer differential Riccati inequality with coefficients
   regular across `a=0`, or prove it infeasible in a stated multiplier class.
3. Construct a KYP/passivity realization for the coupled matrix ratio kernel;
   scalar positive-realness is insufficient because impulse weights can change
   sign.
4. Establish a natural-state formulation that is uniformly coercive across
   physical, edge, and corner regions without primitive gauge modes.
5. Design DG fluxes for piecewise-constant/small-gradient profiles that cancel
   analytic interface fluxes and inherit the Level-B identity.
6. Add a completely monotone Cole--Cole polarization memory after, not before,
   the spatial PML commutator is controlled.

## Recommended next route

For analysis, pursue a non-circular resolvent-to-KYP/Gramian construction.  For
an immediately executable DG paper, use the verified Level-B Baffet theorem on
piecewise-constant or pointwise-Schur-admissible profiles and keep all interface
fluxes explicit.
