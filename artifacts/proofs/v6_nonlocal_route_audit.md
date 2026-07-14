# V6 nonlocal and alternative-route audit

## Scope

This note audits the variable-coefficient strict stretched-coordinate
Maxwell--Debye Baffet identity on the corner subdomain
`Omega_+ = {sigma_x>0 and sigma_y>0}`.  Put

```text
a = sigma_x + sigma_y,  b = sigma_x sigma_y,
g = grad a,
C_lambda = Gamma_1(I+a^{-1}Gamma_1),
c_u = mu epsilon a b.
```

The exact identity (with the displayed outward flux) is

```text
E_B' = -D_0 - (u g,lambda) + integral_boundary (u_t+a u) lambda.n.
```

Here `D_0` contains `(C_lambda lambda,lambda)+c_u||u||^2` and the
other nonnegative Baffet--Debye terms.

## Exact conditional absorption

The relevant pointwise block is

```text
Q(x) = [[c_u, g^T/2], [g/2, C_lambda]].
```

If `C_lambda>0`, its Schur complement condition is

```text
g^T C_lambda^{-1} g <= 4 c_u.
```

Under the strict version with a uniform margin and nonpositive boundary flux,
`E_B' + theta D_0 <= 0` for some `theta>0`.  This is a Level-B theorem, not an
unconditional result.  In global integral form it is enough that

```text
D_0 >= m_u||u||^2+m_lambda||lambda||^2+...,
||g||_infty^2 < 4 m_u m_lambda.
```

The exact adversarial frozen block `m_u=m_lambda=1, |g|=3` has eigenvalues
`-1/2, 5/2`, so the original Baffet dissipation cannot absorb arbitrary high
gradients.

## Elliptic candidate

Let `V=H_0^1(Omega_+)`, let `C` be a symmetric matrix field with
`xi^T C xi >= c_*|xi|^2`, and let `c>=0`.  Define

```text
A(z,v)=(C grad z,grad v)+(c z,v),
L z=div(u g),
A(z,v)=-(u g,grad v).
```

Dirichlet data remove the kernel and Lax--Milgram gives a unique `z`.  With
Neumann data one instead needs `(C grad z+u g).n=0`, and either `c>=c_0>0` or a
mean-zero quotient plus compatibility.  Since coefficients are stationary,

```text
A(z_t,v)=-(u_t g,grad v).
```

For the proposed correction

```text
F=eta (lambda,grad z)+eta/2 A(z,z)
```

the complete derivative is

```text
F'/eta=(lambda_t,grad z)+(lambda,grad z_t)+A(z,z_t)
      =(lambda_t,grad z)+(lambda-u g,grad z_t).
```

Consequently

```text
(E_B+F)' = -D_0 -(u g,lambda)
  +eta[(lambda_t,grad z)+(lambda-u g,grad z_t)] + boundary flux.
```

There is no `+(u g,lambda)` term.  The proposal therefore fails dynamically,
even when its static Schur complement is positive.  The scalar proxy
`ell z=-g u` gives the certified residual

```text
-g u lambda + eta[-g u lambda_t/ell-g u_t lambda/ell
                   +g^2 u u_t/ell].
```

The correction can be positive for sufficiently small `eta` relative to the
ellipticity and the `lambda`/`u` coercivity already in `E_B`; boundedness of
`L^{-1}div(u g)` also gives an upper norm bound.  These static facts do not fix
the derivative.  In edge layers and near `a=0`, the primitive energy itself is
not uniformly coercive on the unrestricted ADE state, so equivalence also
fails without a compatibility-manifold or a physical/primitive partition.

## Two explicit repairs that still fail

### Second elliptic variable

Let `p=L^{-1}div(lambda)`.  A static cross term `A(z,p)` is proportional to a
spatially smoothed `u-lambda` product.  Its derivative contains only
`A(z_t,p)+A(z,p_t)`.  In the scalar proxy `ell p=-lambda`,

```text
d/dt [ell z p] = g(u_t lambda+u lambda_t)/ell,
```

not `g u lambda`.  Thus a second instantaneous elliptic solve does not create
the missing zeroth-order-in-time product.

### Temporal primitive

Introduce `r_t=lambda`.  Then

```text
d/dt (u g,r)=(u_t g,r)+(u g,lambda),
```

and the second term does cancel the Baffet remainder.  The new remainder is
`(u_t g,r)`.  Moreover, the bare cross term is unbounded below; adding
`delta||r||^2/2` produces `delta(r,lambda)`, while `r` is a new gauge/history
state not controlled by the original natural norm.  This is not an equivalent
finite-memory energy without an additional stable evolution/observability
mechanism.

## Local cross term

For each component the exact strict-PML relation is

```text
lambda_i,t = partial_i u_t + sigma_j partial_i u - sigma_i lambda_i.
```

Hence

```text
d/dt integral c_i u lambda_i
 = integral c_i[u_t lambda_i+u partial_i u_t
                +sigma_j u partial_i u-sigma_i u lambda_i].
```

Choosing `c_i=-(partial_i a)/sigma_i` creates the desired
`+(partial_i a)u lambda_i` but leaves

```text
-(partial_i a/sigma_i)
 [u_t lambda_i+u partial_i u_t+sigma_j u partial_i u].
```

It is singular where `sigma_i=0`, generally incompatible with the inner
interface, and further integration by parts introduces derivatives of `c_i`.
A full local symmetrizer must therefore solve a matrix differential
Lyapunov/Riccati inequality

```text
M A_0^{-1}A_i=(M A_0^{-1}A_i)^T,
M A_0^{-1}B+(A_0^{-1}B)^T M
 - sum_i partial_i(M A_0^{-1}A_i) >= 0,
```

with uniform `M>0`.  No such profile-uniform solution is established here.

## Gramian/history route

On a bounded truncated domain, take the compatible strict-ADE state space
consisting of the physical `L2` fields and minimal PML/Debye histories, with
PEC outer boundary, tangential transmission conditions, and the corresponding
`H(curl)` generator domain.  If `A_sigma` independently generates an
exponentially stable semigroup and `C` is exactly observable, then

```text
G=int_0^infty T(t)^* C^*C T(t) dt,
A_sigma^*G+G A_sigma=-C^*C
```

defines a positive norm-equivalent monotone energy.  Exponential stability is
needed for convergence; exact observability is needed for the lower norm
bound.  Neither has been proved here for arbitrary variable profiles, so using
this Gramian to prove those properties would be circular.

For strong but non-exponential stability the infinite integral may diverge.
The finite-horizon Gramian satisfies

```text
d/dt E_T(U(t))=||C T(T)U(t)||^2-||CU(t)||^2,
```

and the exponentially weighted infinite Gramian satisfies

```text
E_delta'=-||CU||^2+2 delta E_delta;
```

neither is automatically monotone.  Resolvent estimates or a non-circular
KYP/passivity theorem are the appropriate next targets.  Although each scalar
ratio `(s+sigma_j)/(s+sigma_i)` is positive real on `Re s>0`, its impulse kernel
has coefficient `sigma_j-sigma_i` and can change sign.  Componentwise positive
realness does not establish positivity of the coupled spatial matrix kernel.

## Route judgment

The strongest proved result remains the original Baffet energy under the exact
pointwise Schur/small-gradient condition.  The proposed elliptic correction is
rejected by its complete time derivative.  Local coefficients are a plausible
Riccati search but are singular at the interface in the simplest cancellation
choice.  The Gramian/resolvent route is the most worthwhile theoretical route
for a future paper; the conditional Baffet identity is the most immediately
usable route for DG analysis.
