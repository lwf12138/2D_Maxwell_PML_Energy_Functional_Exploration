# Stage-3 proof: perfect-matching test for the v2 covariantly damped model

Problem id: `2d_maxwell_pml_energy_functional_exploration`

Task: `task-stage3-perfect-matching-test`

## Assumptions and notation

Use the alpha \(=1\) Maxwell--Debye material law in the physical region:
\[
P+\tau \partial_t P=\chi E,\qquad
\varepsilon_D(s)=\epsilon_0\epsilon_\infty+\frac{\chi}{1+\tau s}.
\]
Here \(s\in\mathbb C\), \(\Re s>0\), is the Laplace frequency, and all initial
data are taken zero for the interface symbol calculation.

Consider a planar interface \(x=0\).  The physical half-space is \(x<0\).
The PML half-space is \(x>0\), with constant \(x\)-layer coefficient
\[
\rho_x=\rho>0,\qquad \rho_y=0 .
\]
Use the tangential Fourier ansatz \(e^{s t+i k y+\nu x}\), so
\(\partial_y\mapsto i k\), \(\partial_x\mapsto \nu\).  The square-root branch is
chosen by outgoing/decaying continuation from \(\Re s>0\).

For an \(x\)-interface the continuous tangential traces are \(E\) and \(H_y\).
For incident and reflected physical modes,
\[
E=E_i+E_r,\qquad H_y=Y_0(E_i-E_r),
\]
and for the transmitted PML mode \(H_y=Y_+E_t\).  Hence
\[
R=\frac{E_r}{E_i}=\frac{Y_0-Y_+}{Y_0+Y_+}.
\]
The model is perfectly matched at this interface iff \(Y_+=Y_0\) for every
\(s\) and \(k\).

## Physical Maxwell--Debye admittance

The Laplace-domain physical equations are
\[
s\varepsilon_D(s)E=\partial_xH_y-\partial_yH_x,
\qquad
\mu sH_x=-\partial_yE,\qquad
\mu sH_y=\partial_xE .
\]
With \(\partial_x=\nu_0\), \(\partial_y=ik\),
\[
H_x=-\frac{ik}{\mu s}E,\qquad
H_y=\frac{\nu_0}{\mu s}E .
\]
Substitution gives
\[
\nu_0^2=k^2+\mu s^2\varepsilon_D(s).
\]
Therefore the physical admittance is
\[
Y_0(s,k)=\frac{\nu_0}{\mu s},\qquad
Y_0(s,k)^2=\frac{1}{\mu^2}\left(\mu\varepsilon_D(s)+\frac{k^2}{s^2}\right).
\]

## Standard stretched-coordinate check

A classical \(x\)-PML has stretch factor
\[
S_x(s)=1+\frac{\sigma_x}{s}
\]
and replaces \(\partial_x\) by \(S_x^{-1}\partial_x\), while leaving the
physical material law \(\varepsilon_D(s)\) unchanged:
\[
s\varepsilon_D(s)E=S_x^{-1}\partial_xH_y-\partial_yH_x,
\quad
\mu sH_x=-\partial_yE,\quad
\mu sH_y=S_x^{-1}\partial_xE.
\]
For a transmitted mode,
\[
\nu_+=S_x\nu_0,\qquad
Y_+=\frac{S_x^{-1}\nu_+}{\mu s}=\frac{\nu_0}{\mu s}=Y_0.
\]
Thus the stretched-coordinate model has \(R=0\) at the continuous planar
interface.

## v2 covariantly damped model

The v2 model is
\[
\epsilon_0\epsilon_\infty D_\rho E
=\partial_xH_y-\partial_yH_x-D_\rho P,
\]
\[
\mu(\partial_t+\rho_y)H_x=-\partial_yE,\qquad
\mu(\partial_t+\rho_x)H_y=\partial_xE,
\]
\[
P+\tau D_\rho P=\chi E,\qquad
D_\rho=\partial_t+\rho_x+\rho_y.
\]
In the \(x\)-layer \(\rho_x=\rho,\rho_y=0\), so
\[
P=\frac{\chi}{1+\tau(s+\rho)}E,\qquad
\varepsilon_\rho(s)=
\epsilon_0\epsilon_\infty+\frac{\chi}{1+\tau(s+\rho)} .
\]
The transformed equations are
\[
(s+\rho)\varepsilon_\rho(s)E=\nu H_y-ikH_x,
\]
\[
\mu sH_x=-ikE,\qquad
\mu(s+\rho)H_y=\nu E.
\]
Thus
\[
H_x=-\frac{ik}{\mu s}E,\qquad
H_y=\frac{\nu}{\mu(s+\rho)}E
\]
and
\[
\nu^2=\mu(s+\rho)^2\varepsilon_\rho(s)
      +k^2\frac{s+\rho}{s}.
\]
The v2 PML admittance is therefore
\[
Y_{v2}(s,k)=\frac{\nu}{\mu(s+\rho)},\qquad
Y_{v2}(s,k)^2
=\frac{1}{\mu^2}
\left(\mu\varepsilon_\rho(s)+\frac{k^2}{s(s+\rho)}\right).
\]

Comparing with the physical admittance,
\[
Y_{v2}^2-Y_0^2
=\frac{1}{\mu^2}\left[
\mu(\varepsilon_\rho(s)-\varepsilon_D(s))
+\frac{k^2}{s(s+\rho)}-\frac{k^2}{s^2}\right].
\]
Since
\[
\varepsilon_\rho(s)-\varepsilon_D(s)
=-\frac{\chi\tau\rho}{(1+\tau s)(1+\tau(s+\rho))}
\]
and
\[
\frac{1}{s(s+\rho)}-\frac{1}{s^2}
=-\frac{\rho}{s^2(s+\rho)},
\]
the exact mismatch is
\[
\boxed{
Y_{v2}^2-Y_0^2
=-\frac{\rho}{\mu^2}\left[
\frac{\mu\chi\tau}{(1+\tau s)(1+\tau(s+\rho))}
+\frac{k^2}{s^2(s+\rho)}
\right].}
\]
This expression is not identically zero for \(\rho>0\).  Hence the v2 model is
not perfectly matched.

The corresponding reflection coefficient is
\[
\boxed{
R_{v2}(s,k)=
\frac{
\sqrt{\mu\varepsilon_D(s)+k^2/s^2}
-\sqrt{\mu\varepsilon_\rho(s)+k^2/[s(s+\rho)]}
}{
\sqrt{\mu\varepsilon_D(s)+k^2/s^2}
+\sqrt{\mu\varepsilon_\rho(s)+k^2/[s(s+\rho)]}
}.}
\]
The square-root branches are those inherited from the outgoing physical and
decaying PML modes.

## Interpretation of the mismatch

There are two independent formula-level defects.

1. The Debye susceptibility is shifted from
\[
\frac{\chi}{1+\tau s}
\quad\text{to}\quad
\frac{\chi}{1+\tau(s+\rho)}.
\]
This changes the material impedance even at normal incidence \(k=0\), unless
\(\chi=0\), \(\tau=0\), or \(\rho=0\).

2. The oblique tangential part changes from \(k^2/s^2\) to
\[
\frac{k^2}{s(s+\rho)}.
\]
This remains a mismatch for \(k\ne0\) even in the nondispersive limit
\(\chi=0\).

Thus applying the same covariant derivative \(D_\rho\) to the Debye law is good
for the v2 monotone energy identity, but it is not the Laplace-domain
stretched-coordinate continuation of the physical Maxwell--Debye system.

## Durable fact candidate

Claim summary:
The covariantly damped v2 Maxwell--Debye absorbing-layer model is not perfectly
matched at a planar constant-coefficient \(x\)-PML interface; its squared
admittance differs from the physical Maxwell--Debye admittance by the boxed
formula above.

Dependencies:

- `fact:2d_maxwell_pml_energy_functional_exploration:covariantly-damped-debye-energy`
  for the v2 model definition and verified energy identity.
