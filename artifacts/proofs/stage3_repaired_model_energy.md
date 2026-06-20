# Stage-3 proof: repaired PML candidates and dissipative-energy classification

Problem id: `2d_maxwell_pml_energy_functional_exploration`

Task: `task-stage3-repaired-model-energy`

## Input fact from the matching test

The v2 covariantly damped Maxwell--Debye model has the verified stage-2 monotone
energy identity, but the stage-3 interface calculation shows that it is not a
perfectly matched layer.  In an \(x\)-layer with \(\rho_x=\rho>0,\rho_y=0\),
\[
Y_{v2}^2-Y_0^2
=-\frac{\rho}{\mu^2}\left[
\frac{\mu\chi\tau}{(1+\tau s)(1+\tau(s+\rho))}
+\frac{k_y^2}{s^2(s+\rho)}
\right],
\]
so the v2 reflection coefficient is not identically zero.

Therefore a repaired model must keep the physical Debye law as a function of the
Laplace variable \(s\), not \(s+\rho\), and must implement damping through
coordinate stretching or an equivalent split/ADE system.

## Candidate 1: classical stretched-coordinate Maxwell--Debye PML

Let
\[
\varepsilon_D(s)=\epsilon_0\epsilon_\infty+\frac{\chi}{1+\tau s},
\qquad
S_i(s)=1+\frac{\sigma_i}{s},\quad i=x,y.
\]
In the physical region \(\sigma_x=\sigma_y=0\).  In the PML the coefficients are
nonnegative and are first analyzed as piecewise constant near each planar
interface.

The Laplace-domain repaired model is
\[
\boxed{
s\varepsilon_D(s)\widehat E
=S_x^{-1}\partial_x\widehat H_y
-S_y^{-1}\partial_y\widehat H_x,}
\]
\[
\boxed{
\mu s\widehat H_x=-S_y^{-1}\partial_y\widehat E,\qquad
\mu s\widehat H_y=S_x^{-1}\partial_x\widehat E,}
\]
\[
\boxed{(1+\tau s)\widehat P=\chi\widehat E.}
\]
Equivalently, the Debye law is not damped:
\[
P+\tau P_t=\chi E.
\]

### Perfect matching

At an \(x\)-interface, \(S_y=1\).  With tangential Fourier number \(k_y\),
the physical normal symbol satisfies
\[
\nu_0^2=k_y^2+\mu s^2\varepsilon_D(s),\qquad
Y_0=\frac{\nu_0}{\mu s}.
\]
In the PML,
\[
s\varepsilon_D E=S_x^{-1}\nu H_y-ik_yH_x,\qquad
\mu sH_x=-ik_yE,\qquad
\mu sH_y=S_x^{-1}\nu E.
\]
The dispersion relation gives
\[
\left(S_x^{-1}\nu\right)^2=k_y^2+\mu s^2\varepsilon_D(s),
\]
hence \(\nu=S_x\nu_0\) and
\[
Y_+=\frac{S_x^{-1}\nu}{\mu s}=\frac{\nu_0}{\mu s}=Y_0.
\]
Thus the planar-interface reflection coefficient is \(R=0\) for every
\((s,k_y)\) in the Laplace half-plane.  The same argument applies to a
\(y\)-interface with \(x,y\) interchanged.

### Time-domain ADE realization

Define the causal operator
\[
\mathcal A_i=S_i^{-1}=\frac{s}{s+\sigma_i}
\]
in the Laplace domain.  Equivalently,
\[
\mathcal A_i f=f+\psi_i,\qquad
(\partial_t+\sigma_i)\psi_i=-\sigma_i f.
\]
Then a time-domain unsplit ADE form is
\[
\epsilon_0\epsilon_\infty E_t+P_t
=\partial_xH_y-\partial_yH_x
+\psi_{E,x}-\psi_{E,y},
\]
\[
\mu H_{x,t}=-\partial_yE-\psi_{H_x,y},\qquad
\mu H_{y,t}=\partial_xE+\psi_{H_y,x},
\]
\[
P+\tau P_t=\chi E,
\]
with
\[
(\partial_t+\sigma_x)\psi_{E,x}=-\sigma_x\partial_xH_y,\qquad
(\partial_t+\sigma_y)\psi_{E,y}=-\sigma_y\partial_yH_x,
\]
\[
(\partial_t+\sigma_y)\psi_{H_x,y}=-\sigma_y\partial_yE,\qquad
(\partial_t+\sigma_x)\psi_{H_y,x}=-\sigma_x\partial_xE.
\]
Interface conditions are continuity of the physical tangential traces.  For an
\(x\)-interface these are \(E\) and \(H_y\).  The auxiliary variables vanish in the
physical region and are initialized consistently with the causal convolution.

### Naive energy calculation

The natural physical Debye energy is
\[
\mathcal E_{\rm phys}
=\frac12\int_\Omega
\left(\epsilon_0\epsilon_\infty E^2+\mu H_x^2+\mu H_y^2+\chi^{-1}P^2\right)\,dxdy.
\]
It is positive because
\(\epsilon_0,\epsilon_\infty,\mu,\chi>0\).  Using
\[
E P_t=\frac{1}{2\chi}\partial_t(P^2)+\frac{\tau}{\chi}P_t^2
\]
and the PEC boundary condition \(E=0\) on the outer boundary gives
\[
\frac{d}{dt}\mathcal E_{\rm phys}
=-\int_\Omega\frac{\tau}{\chi}P_t^2\,dxdy
+\int_\Omega
\left[
E(\psi_{E,x}-\psi_{E,y})
-H_x\psi_{H_x,y}
+H_y\psi_{H_y,x}
\right]\,dxdy .
\]
The Maxwell principal part contributes only the boundary flux
\[
\int_{\partial\Omega}E(H_y n_x-H_x n_y)\,ds,
\]
which vanishes under PEC at the outer boundary and cancels by transmission at
internal material/PML interfaces when the tangential traces are continuous.

The remaining auxiliary terms are not sign-definite in this naive energy.
Therefore the positive physical Debye energy alone is not a monotone energy for
the exact stretched-coordinate PML.

### Classification

This candidate is the formula-level perfect-matching repair.  A local monotone
energy for the full 2D Maxwell--Debye ADE system is not certified here.  The
calculation above identifies the exact terms that a Baffet-type augmented energy
would have to absorb:
\[
E\psi_{E,x},\quad E\psi_{E,y},\quad
H_x\psi_{H_x,y},\quad H_y\psi_{H_y,x}.
\]
The literature record supports that such augmented energies are non-naive and
that constant-coefficient damping is the natural first scope for a sharp identity.

### Reduced normal-incidence 1D energy identity

There is one important positive result for the exact stretched-coordinate model.
In the \(x\)-layer normal-incidence block \(k_y=0\), the standard stretch gives
\[
(\partial_t+\rho)(\epsilon_0\epsilon_\infty E+P)=\partial_xH_y,
\qquad
\mu(\partial_t+\rho)H_y=\partial_xE,
\]
\[
P+\tau P_t=\chi E.
\]
This is exactly the \(k_y=0\) restriction of the perfectly matched stretched
model, not the v2 model, because the Debye law still uses \(\partial_t\) rather
than \(\partial_t+\rho\).

Multiply the first equation by \(E\), the second by \(H_y\), and use
\[
E=\frac{P+\tau P_t}{\chi}.
\]
Then
\[
E P_t=\frac{1}{2\chi}\partial_t(P^2)+\frac{\tau}{\chi}P_t^2,
\]
and
\[
\rho E P
=\frac{\rho}{\chi}P^2+\frac{\rho\tau}{2\chi}\partial_t(P^2).
\]
After integrating by parts, the principal terms give only the boundary flux
\(\int_{\partial I}EH_y n_x\,ds\).  Hence
\[
\boxed{
\frac{d}{dt}\mathcal E_{1d,sc}
=-\int_I\left(
\rho\epsilon_0\epsilon_\infty E^2+\mu\rho H_y^2
+\frac{\rho}{\chi}P^2+\frac{\tau}{\chi}P_t^2
\right)\,dx
+\int_{\partial I}EH_y n_x\,ds,}
\]
where
\[
\boxed{
\mathcal E_{1d,sc}
=\frac12\int_I\left(
\epsilon_0\epsilon_\infty E^2+\mu H_y^2
+\frac{1+\rho\tau}{\chi}P^2
\right)\,dx.}
\]
This energy is positive for \(\rho,\tau,\chi>0\), and it is dissipative under
PEC or otherwise nonpositive boundary flux.  It explains why the v2 idea is
close to a useful construction in normal incidence, but it does not solve the
full 2D oblique problem: as soon as \(k_y\ne0\), the exact stretched model
contains the ADE memory couplings displayed above.

## Candidate 2: generalized CFS/ADE stretched-coordinate PML

Let
\[
S_i(s)=\kappa_i+\frac{\sigma_i}{s+\alpha_i},
\qquad
\kappa_i\ge1,\quad \sigma_i\ge0,\quad \alpha_i\ge0.
\]
The repaired Laplace-domain equations are the same as Candidate 1, with these
\(S_i\).  In particular the Debye law remains
\[
(1+\tau s)\widehat P=\chi\widehat E.
\]

For a planar \(x\)-interface with \(S_y=1\), the same calculation gives
\[
\nu=S_x\nu_0,\qquad Y_+=Y_0,
\]
so the continuous model is perfectly matched whenever the stretch is applied to
the spatial derivatives and the physical material law is left unchanged.

If \(S_i^{-1}\) is rational with poles in \(\Re s<0\), it can be implemented by
ADE variables.  The CFS shift \(\alpha_i>0\) is a standard way to improve
low-frequency/evanescent and late-time behavior, but a monotone time-domain
energy requires an explicit positive realization of the memory kernel.  No such
positive memory theorem is claimed here for the full 2D Maxwell--Debye system.

Classification: perfectly matched at the continuous planar-interface level;
recommended if long-time CFS behavior is needed; energy status is boundedness or
passive-memory proof pending, not a completed monotone identity.

## Candidate 3: MPML-type extra damping

An MPML-type repair adds damping in more than the normal coordinate direction.
For example, in an \(x\)-layer one may replace a scalar stretch by a multiaxial
stretch depending also on tangential damping parameters.  This is useful for
removing long-time instabilities or Jordan-block behavior in some systems.

However, if the tangential stretch is nontrivial at the physical/PML interface,
the planar admittance generally changes.  The MPML literature inspected for this
run explicitly treats MPML as a stability-oriented absorbing layer and records
that exact perfect matching may be lost in multiaxial variants.

Classification: absorbing/stability repair, not the primary exact-matching
repair for the present Maxwell--Debye interface theorem.

## Complete dissipative identity that is currently verified

The only complete positive monotone identity verified in the existing Iteris
memory is for the v2 covariantly damped absorbing layer:
\[
\epsilon_0\epsilon_\infty D_\rho E
=\partial_xH_y-\partial_yH_x-D_\rho P,
\]
\[
\mu(\partial_t+\rho_y)H_x=-\partial_yE,\qquad
\mu(\partial_t+\rho_x)H_y=\partial_xE,
\]
\[
P+\tau D_\rho P=\chi E,\qquad D_\rho=\partial_t+\rho_x+\rho_y.
\]
Its energy is
\[
\mathcal E_\rho(t)=\frac12\int_\Omega
\left(\epsilon_0\epsilon_\infty E^2+\mu H_x^2+\mu H_y^2+\chi^{-1}P^2\right)\,dxdy
\]
and the verified identity is
\[
\frac{d}{dt}\mathcal E_\rho(t)
=-\int_\Omega\left(
\epsilon_0\epsilon_\infty\rho E^2
+\mu\rho_yH_x^2
+\mu\rho_xH_y^2
+\frac{\rho}{\chi}P^2
+\frac{\tau}{\chi}|D_\rho P|^2
\right)\,dxdy.
\]
This identity is genuinely dissipative, but the model is not perfectly matched.
It should therefore be described as a stable absorbing-layer model, not as a
standard PML.

## Formula-level obstruction to strict decay on the whole domain

Even for a perfectly matched repair, strict decay of a total energy controlling
all fields on the whole computational domain cannot hold without a nullspace.
Assume a physical subregion where \(\sigma_x=\sigma_y=0\) and choose
\[
E=0,\qquad P=0,\qquad H_x=\partial_x\phi,\qquad H_y=\partial_y\phi,
\]
with \(\phi\) smooth and compactly supported inside that undamped physical
subregion.  Then
\[
\partial_xH_y-\partial_yH_x=0,\qquad
\partial_yE=\partial_xE=0,
\]
and all PML auxiliary variables initialized at zero remain zero for at least this
exact stationary solution.  The magnetic energy is positive if \(\nabla\phi\ne0\),
but every damping term in the PML vanishes.

Therefore no theorem can honestly state that the total energy is strictly
decreasing for every nonzero state on the whole computational domain.  The sharp
possible statement is a dissipative identity or inequality whose nullspace
contains undamped physical-region stationary/curl-free magnetic modes and, more
generally, states not seen by the layer damping.

## Recommended theorem split

The next manuscript should separate two theorems.

1. Perfect matching theorem: use Candidate 1 or Candidate 2 in the Laplace
   domain and prove \(Y_+=Y_0\) for every planar outgoing mode.  This theorem
   must keep the Debye law as \((1+\tau s)P=\chi E\).

2. Energy theorem: either keep the v2 covariantly damped absorbing model and
   state it is not perfectly matched, or build a new Baffet/passive-memory
   augmented energy for the exact stretched-coordinate ADE model.  The latter is
   open in this artifact; the naive positive energy calculation above shows the
   exact auxiliary couplings that must be controlled.

## Durable fact candidate

Claim summary:
The standard stretched-coordinate Maxwell--Debye PML, with the physical Debye
law left as \((1+\tau s)P=\chi E\), is perfectly matched at a constant
planar interface; its naive physical Debye energy is positive but has
sign-indefinite ADE memory couplings, so the v2 monotone energy identity cannot
be transferred to it without a new augmented energy.

Dependencies:

- `fact:2d_maxwell_pml_energy_functional_exploration:v2-covariant-model-not-perfectly-matched`
- `fact:2d_maxwell_pml_energy_functional_exploration:covariantly-damped-debye-energy`
