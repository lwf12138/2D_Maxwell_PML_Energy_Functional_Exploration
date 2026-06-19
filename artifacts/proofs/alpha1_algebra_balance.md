# Alpha=1 Algebra and First Energy Balance

Task: `task-alpha1-algebra-energy-balance`

Source: `sources/energy_functional_problem.tex`

## Model and conventions

For this artifact the polarization law is the non-fractional case
\[
P+\tau \partial_t P=\chi E,\qquad \chi=\epsilon_0(\epsilon_s-\epsilon_\infty)>0.
\]
The boundary condition is PEC for the two-dimensional TM model:
\[
E=E_z=0\quad\text{on }\partial\Omega.
\]
The absorption functions are time-independent and nonnegative.  No spatial derivatives of
\(\sigma_x,\sigma_y\) are used in this algebraic artifact.

The model equations are exactly those displayed in the source:
\[
\begin{aligned}
\epsilon_0\epsilon_\infty E_t
&= \partial_xH_y-\partial_yH_x
   -\epsilon_\infty(\sigma_x+\sigma_y)E
   -P_t-\frac{\sigma_x+\sigma_y}{\epsilon_0}P
   +P_{z,1}+P_{z,2},\\
\mu H_{x,t}
&= -\partial_yE-\mu\frac{\sigma_y-\sigma_x}{\epsilon_0}H_x+Q_x,\\
\mu H_{y,t}
&= \partial_xE-\mu\frac{\sigma_x-\sigma_y}{\epsilon_0}H_y+Q_y,\\
P+\tau P_t&=\chi E,\\
P_{z,1,t}&=-\frac{\epsilon_\infty}{\epsilon_0}\sigma_x\sigma_y E,\\
P_{z,2,t}&=-\frac{\sigma_x\sigma_y}{\epsilon_0^2}P,\\
Q_{x,t}&=-\frac{\sigma_x}{\epsilon_0}Q_x
  +\frac{\mu\sigma_x(\sigma_y-\sigma_x)}{\epsilon_0^2}H_x,\\
Q_{y,t}&=-\frac{\sigma_y}{\epsilon_0}Q_y
  +\frac{\mu\sigma_y(\sigma_x-\sigma_y)}{\epsilon_0^2}H_y.
\end{aligned}
\]

## PEC cancellation and electromagnetic balance

Let
\[
\mathcal E_{\rm em}
=\frac12\int_\Omega
\left(\epsilon_0\epsilon_\infty E^2+\mu H_x^2+\mu H_y^2\right)\,dxdy .
\]
Multiplying the first three equations by \(E,H_x,H_y\) and integrating gives the
principal part
\[
\int_\Omega \left(E\partial_xH_y-E\partial_yH_x-H_x\partial_yE+H_y\partial_xE\right)\,dxdy
=\int_{\partial\Omega} E(H_y n_x-H_x n_y)\,ds=0,
\]
because \(E=0\) on \(\partial\Omega\).  Therefore
\[
\begin{aligned}
\frac{d}{dt}\mathcal E_{\rm em}
=\int_\Omega\Big[
&-\epsilon_\infty(\sigma_x+\sigma_y)E^2
-E P_t
-\frac{\sigma_x+\sigma_y}{\epsilon_0}EP
+E(P_{z,1}+P_{z,2})\\
&-\frac{\mu}{\epsilon_0}(\sigma_y-\sigma_x)H_x^2
-\frac{\mu}{\epsilon_0}(\sigma_x-\sigma_y)H_y^2
+H_xQ_x+H_yQ_y
\Big]\,dxdy .
\end{aligned}
\]
This agrees with the balance stated in the source.

## Polarization energy for alpha=1

The identity
\[
E=\frac{P+\tau P_t}{\chi}
\]
implies
\[
E P_t=\frac{1}{2\chi}\frac{d}{dt}\|P\|_{L^2(\Omega)}^2
+\frac{\tau}{\chi}\|P_t\|_{L^2(\Omega)}^2 .
\]
Thus the positive polarization-corrected energy
\[
\mathcal E_{\rm em+P}
=\mathcal E_{\rm em}+\frac{1}{2\chi}\|P\|_{L^2(\Omega)}^2
\]
satisfies
\[
\begin{aligned}
\frac{d}{dt}\mathcal E_{\rm em+P}
=\int_\Omega\Big[
&-\epsilon_\infty(\sigma_x+\sigma_y)E^2
-\frac{\tau}{\chi}P_t^2
-\frac{\sigma_x+\sigma_y}{\epsilon_0}EP
+E(P_{z,1}+P_{z,2})\\
&-\frac{\mu}{\epsilon_0}(\sigma_y-\sigma_x)H_x^2
-\frac{\mu}{\epsilon_0}(\sigma_x-\sigma_y)H_y^2
+H_xQ_x+H_yQ_y
\Big]\,dxdy .
\end{aligned}
\]
The alpha=1 polarization contribution is therefore positive and dissipative.  The
remaining electric PML terms are
\[
-\frac{\sigma_x+\sigma_y}{\epsilon_0}EP,\qquad EP_{z,1},\qquad EP_{z,2},
\]
coupled to
\[
P_{z,1,t}=-\frac{\epsilon_\infty}{\epsilon_0}\sigma_x\sigma_y E,
\qquad
P_{z,2,t}=-\frac{\sigma_x\sigma_y}{\epsilon_0^2}P.
\]

## Shifted magnetic variables

Define
\[
a_x=\frac{\sigma_y-\sigma_x}{\epsilon_0},\qquad
a_y=\frac{\sigma_x-\sigma_y}{\epsilon_0},\qquad
b_x=\frac{\sigma_x}{\epsilon_0},\qquad
b_y=\frac{\sigma_y}{\epsilon_0},
\]
and
\[
M_x=Q_x-\mu a_xH_x,\qquad M_y=Q_y-\mu a_yH_y.
\]
Then the \(H\)-equations become
\[
\mu H_{x,t}=-\partial_yE+M_x,\qquad
\mu H_{y,t}=\partial_xE+M_y.
\]
Using the \(Q\)-equations and the time-independence of the coefficients,
\[
\begin{aligned}
M_{x,t}
&=Q_{x,t}-\mu a_xH_{x,t}\\
&=-b_xQ_x+\mu b_xa_xH_x
   +a_x\partial_yE+\mu a_x^2H_x-a_xQ_x\\
&=a_x\partial_yE-b_y(Q_x-\mu a_xH_x)
=a_x\partial_yE-b_yM_x,
\end{aligned}
\]
because \(b_x+a_x=b_y\).  Similarly,
\[
M_{y,t}=-a_y\partial_xE-b_xM_y.
\]
This verifies the shifted identities
\[
M_{x,t}=a_x\partial_yE-\frac{\sigma_y}{\epsilon_0}M_x,\qquad
M_{y,t}=-a_y\partial_xE-\frac{\sigma_x}{\epsilon_0}M_y.
\]

In the electromagnetic-plus-polarization balance, substituting
\[
Q_x=M_x+\mu a_xH_x,\qquad Q_y=M_y+\mu a_yH_y
\]
cancels the two sign-indefinite magnetic square terms exactly.  The shifted balance is
\[
\boxed{
\begin{aligned}
\frac{d}{dt}\mathcal E_{\rm em+P}
=\int_\Omega\Big[
&-\epsilon_\infty(\sigma_x+\sigma_y)E^2
-\frac{\tau}{\chi}P_t^2
-\frac{\sigma_x+\sigma_y}{\epsilon_0}EP
+E(P_{z,1}+P_{z,2})\\
&+H_xM_x+H_yM_y
\Big]\,dxdy .
\end{aligned}}
\]
The shift therefore removes the explicit magnetic sign-indefinite damping terms.  It
does not by itself give a monotone energy, since \(H_xM_x+H_yM_y\) remains an
uncontrolled coupling unless additional auxiliary energy or derivative structure is
introduced.
