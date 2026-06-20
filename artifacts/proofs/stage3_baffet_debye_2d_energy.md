# Stage-3 proof: Baffet-type 2D energy for a matched Maxwell-Debye PML

Problem id: `2d_maxwell_pml_energy_functional_exploration`

Task: `task-stage3-final-report`

## Purpose

The previous stage-3 artifact proves that the standard stretched-coordinate
Maxwell-Debye PML is perfectly matched, but only gives a monotone energy in the
one-dimensional normal-incidence block.  This artifact records a full two
dimensional constant-coefficient Baffet-type formulation for the same stretched
coordinate model.  The formulation uses a time primitive of the electric field
and a time primitive of the Debye polarization, which is exactly the type of
augmented/time-integrated variable used in Baffet-type PML energy arguments.

## Assumptions and notation

Let
\[
e=\epsilon_0\epsilon_\infty>0,\quad \mu>0,\quad \chi>0,\quad \tau>0.
\]
In the Laplace domain,
\[
\varepsilon_D(s)=e+\frac{\chi}{1+\tau s}.
\]
On one constant-coefficient PML block let
\[
\sigma_x,\sigma_y\ge 0,\qquad
a=\sigma_x+\sigma_y,\qquad b=\sigma_x\sigma_y,
\]
and assume \(a>0\) for the PML block.  The undamped physical block \(a=b=0\)
uses the ordinary Maxwell-Debye energy and is coupled by the usual transmission
flux.  Define
\[
\Gamma_1=\begin{pmatrix}\sigma_x&0\\0&\sigma_y\end{pmatrix},\qquad
\Gamma_2=\begin{pmatrix}\sigma_y-\sigma_x&0\\0&\sigma_x-\sigma_y\end{pmatrix}.
\]
For a vector \(v\), write \(|v|_M^2=v\cdot Mv\).

Let \(u\) be the time primitive of the electric field:
\[
E=u_t.
\]
Let \(q\) be the time primitive of the Debye polarization:
\[
q_t=P.
\]
The Debye law is written in compatible primitive form
\[
\tau P_t+P=\chi u_t,\qquad q+\tau P=\chi u.
\]
The second relation is preserved by the first two equations if it is true at
initial time.

## Baffet-type matched PML system

Introduce the Baffet auxiliary vector \(\phi=(\phi_x,\phi_y)\) and
\[
\lambda=\nabla u+\phi.
\]
The constant-coefficient two-dimensional repaired model is
\[
\boxed{
\mu\{e(u_{tt}+a u_t+b u)+P_t+aP+bq\}-\nabla\cdot\lambda=0,}
\tag{1}
\]
\[
\boxed{\phi_t+\Gamma_1\phi=\Gamma_2\nabla u,}
\tag{2}
\]
\[
\boxed{\tau P_t+P=\chi u_t,\qquad q_t=P,\qquad q+\tau P=\chi u.}
\tag{3}
\]
Outer boundary conditions are taken so that the boundary flux
\[
\int_{\partial\Omega}(u_t+au)\lambda\cdot n\,ds
\]
is zero or nonpositive.  For a PEC outer boundary, the compatible primitive
condition is \(u=0\), hence \(u_t=E=0\), on that boundary.  On piecewise
constant internal interfaces, the usual transmission conditions are continuity
of \(u\) and \(\lambda\cdot n\), so the flux cancels pairwise.

## Equivalence with the stretched-coordinate Maxwell-Debye PML

For constant coefficients, Laplace transforming (2) gives
\[
\widehat\phi_x=\frac{\sigma_y-\sigma_x}{s+\sigma_x}\partial_x\widehat u,
\qquad
\widehat\phi_y=\frac{\sigma_x-\sigma_y}{s+\sigma_y}\partial_y\widehat u.
\]
Thus
\[
\widehat\lambda_x
=\frac{s+\sigma_y}{s+\sigma_x}\partial_x\widehat u
=\frac{S_y}{S_x}\partial_x\widehat u,\qquad
\widehat\lambda_y
=\frac{s+\sigma_x}{s+\sigma_y}\partial_y\widehat u
=\frac{S_x}{S_y}\partial_y\widehat u,
\]
where
\[
S_i(s)=1+\frac{\sigma_i}{s}=\frac{s+\sigma_i}{s}.
\]
The Debye compatibility gives
\[
\widehat P=\frac{\chi s}{1+\tau s}\widehat u,\qquad
\widehat q=\frac{1}{s}\widehat P.
\]
Therefore
\[
e(s^2+as+b)\widehat u+s\widehat P+a\widehat P+b\widehat q
=\left(e+\frac{\chi}{1+\tau s}\right)(s^2+as+b)\widehat u
=\varepsilon_D(s)s^2S_xS_y\widehat u.
\]
Equation (1) becomes
\[
\mu\varepsilon_D(s)s^2S_xS_y\widehat u
=\nabla\cdot\widehat\lambda.
\]
Dividing by \(S_xS_y\) gives
\[
\mu\varepsilon_D(s)s^2\widehat u
=S_x^{-1}\partial_x(S_x^{-1}\partial_x\widehat u)
+S_y^{-1}\partial_y(S_y^{-1}\partial_y\widehat u).
\]
Since \(\widehat E=s\widehat u\), this is exactly the second-order equation
obtained by eliminating \(H_x,H_y\) from the standard stretched-coordinate
Maxwell-Debye PML while keeping
\[
(1+\tau s)\widehat P=\chi \widehat E.
\]
Consequently this Baffet-type time-domain system has the same planar-interface
perfect matching as the standard stretched-coordinate PML: at an \(x\)-interface
with \(S_y=1\), the normal symbol satisfies \(\nu=S_x\nu_0\) and the tangential
Maxwell admittance is unchanged.

## Energy functional

Define
\[
\alpha=1+2a\tau,\qquad
\beta=a+b\tau,\qquad
\gamma=a^2+b(1+a\tau).
\]
The Baffet-Debye energy is
\[
\boxed{
\begin{aligned}
\mathcal E_{BD}
=\frac12\int_\Omega \{&
\mu e(u_t+a u)^2+|\lambda|^2
+|\phi|_{a^{-1}\Gamma_1}^2+\mu e\,b u^2\\
&+\frac{\mu}{\chi}\left(\alpha P^2+2\beta Pq+\gamma q^2\right)
\}\,dxdy .
\end{aligned}}
\tag{4}
\]
The \(P,q\) block is positive definite whenever \(a>0\).  Indeed
\[
\alpha>0,\qquad
\alpha\gamma-\beta^2
=b+ab\tau+2a^3\tau+b(2a^2-b)\tau^2>0,
\]
because \(a=\sigma_x+\sigma_y>0\), \(b=\sigma_x\sigma_y\ge0\), \(\tau>0\), and
\(2a^2-b\ge0\).  Thus (4) is nonnegative, and it is coercive on the PML block
modulo the usual zero modes of the primitive variables and boundary conditions.

## Energy identity

Test (1) with \(u_t+a u\).  The nondispersive part gives the usual Baffet
calculation:
\[
\frac12\frac{d}{dt}\int_\Omega
\mu e\{(u_t+a u)^2+b u^2\}\,dxdy
+\int_\Omega \mu e\,ab u^2\,dxdy
=\int_\Omega (u_t+a u)\nabla\cdot\lambda\,dxdy
-\mu\int_\Omega (P_t+aP+bq)(u_t+a u)\,dxdy .
\tag{5}
\]
The boundary part of the first term is the flux stated above, and the interior
part is handled by the same Baffet multiplier used for \(\lambda\).  Specifically,
from
\[
\lambda_t+\Gamma_1\lambda=\nabla u_t+\widetilde\Gamma_2\nabla u,\qquad
\widetilde\Gamma_2=\Gamma_2+\Gamma_1
=\begin{pmatrix}\sigma_y&0\\0&\sigma_x\end{pmatrix},
\]
and the multiplier
\[
g=(I+a^{-1}\Gamma_1)\lambda-a^{-1}\Gamma_1\nabla u,
\]
one obtains
\[
\begin{aligned}
&\frac12\frac{d}{dt}\int_\Omega
\left(|\lambda|^2+|\phi|_{a^{-1}\Gamma_1}^2\right)\,dxdy\\
&\quad+\int_\Omega
\left(|\lambda|^2_{\Gamma_1(I+a^{-1}\Gamma_1)}
+\frac{b}{a}|\nabla u|^2\right)\,dxdy
=\int_\Omega \nabla(u_t+a u)\cdot\lambda\,dxdy .
\end{aligned}
\tag{6}
\]
This is the two-dimensional Baffet identity; it uses
\(\Gamma_1\widetilde\Gamma_2=bI\) and
\(a^{-1}\Gamma_1(\Gamma_1+\widetilde\Gamma_2)+\widetilde\Gamma_2=aI\).

It remains to compute the Debye primitive contribution.  Using
\[
u_t+a u
=\frac{\tau P_t+(1+a\tau)P+a q}{\chi},
\]
we have
\[
\begin{aligned}
&(P_t+aP+bq)(u_t+a u)\\
&=\frac1\chi\Big[
\frac12\frac{d}{dt}
\left(\alpha P^2+2\beta Pq+\gamma q^2\right)
+\tau P_t^2+\tau(a^2-b)P^2+abq^2
\Big].
\end{aligned}
\tag{7}
\]
Here \(q_t=P\), and the constants \(\alpha,\beta,\gamma\) are exactly those in
(4).

Adding (5), (6), and (7) gives the full identity
\[
\boxed{
\frac{d}{dt}\mathcal E_{BD}(t)
=-\mathcal D_{BD}(t)
+\int_{\partial\Omega}(u_t+a u)\lambda\cdot n\,ds,}
\tag{8}
\]
where
\[
\boxed{
\begin{aligned}
\mathcal D_{BD}
=\int_\Omega \{&
|\lambda|^2_{\Gamma_1(I+a^{-1}\Gamma_1)}
+\frac{b}{a}|\nabla u|^2+\mu e\,ab u^2\\
&+\frac{\mu}{\chi}\left[
\tau P_t^2+\tau(a^2-b)P^2+abq^2
\right]\}\,dxdy .
\end{aligned}}
\tag{9}
\]
All displayed terms in \(\mathcal D_{BD}\) are nonnegative for
\(\sigma_x,\sigma_y\ge0\), \(a>0\), and positive material parameters.  Under PEC
or canceling transmission flux, (8) gives
\[
\mathcal E_{BD}(t)+\int_0^t\mathcal D_{BD}(r)\,dr\le \mathcal E_{BD}(0).
\]

## Classification and nullspace

This is a full two-dimensional constant-coefficient dissipative identity for an
exact stretched-coordinate Maxwell-Debye PML, written in Baffet-type
time-integrated variables.  It is non-increasing, not strictly decreasing on the
whole computational domain.  The nullspace contains the already identified
undamped physical-region stationary magnetic modes; in the PML block, the
dissipation also leaves the standard primitive-variable gauge modes unless fixed
by boundary/transmission compatibility.  Thus the sharp statement is
non-increase plus a characterized nullspace/no-abnormal-growth estimate, not
strict decay of every nonzero whole-domain state.

For spatially varying damping profiles, this artifact does not claim an energy
identity.  As in the Baffet reference, the verified scope is constant
coefficients, and piecewise constant layers are handled blockwise with
transmission flux cancellation.
