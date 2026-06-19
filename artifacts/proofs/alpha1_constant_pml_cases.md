# Alpha=1 PML Case Split: Edge Obstruction and Global Gronwall Energy

Task: `task-alpha1-pml-cases`

Predecessor fact: `fact:2d_maxwell_pml_energy_functional_exploration:alpha1-algebra-balance`

## Scope

This artifact uses the verified alpha=1 balance and shifted magnetic identities.  The
main conclusions are:

1. The source model, with arbitrary data for all eight displayed unknowns, has exact
   edge-PML solutions with linear growth when one absorption coefficient is positive
   and the other is zero.  Therefore no positive energy that controls the displayed
   variables can be both monotone and uniformly bounded for all data under the full
   edge-PML assumptions as stated.
2. A positive zeroth-order augmented energy gives a closed Gronwall estimate for
   nonnegative, bounded, time-independent \(\sigma_x,\sigma_y\).  This estimate is
   valid for constant, separated-variable, and general spatially variable absorption
   profiles, since it does not integrate derivatives of \(\sigma_i\).
3. For corner PML with \(\sigma_x,\sigma_y>0\), the specific edge linear mode is
   removed because both shifted magnetic auxiliaries have damping.  The artifact does
   not prove a monotone corner energy; it records the local obstruction encountered by
   the natural shifted \(L^2\) energy.

## Positive augmented energy for the Gronwall estimate

Let
\[
\mathcal E_0(t)
=\frac12\int_\Omega
\left(\epsilon_0\epsilon_\infty E^2+\mu H_x^2+\mu H_y^2
+\chi^{-1}P^2+P_{z,1}^2+P_{z,2}^2+Q_x^2+Q_y^2\right)\,dxdy .
\]
This energy is positive for the displayed variables whenever
\(\epsilon_0,\epsilon_\infty,\mu,\chi>0\).  By the verified alpha=1 balance,
\[
\begin{aligned}
\frac{d}{dt}\left(\mathcal E_{\rm em}+\frac1{2\chi}\|P\|_2^2\right)
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
The auxiliary norm derivatives are
\[
\begin{aligned}
\frac12\frac{d}{dt}\|P_{z,1}\|_2^2
&=-\int_\Omega \frac{\epsilon_\infty}{\epsilon_0}\sigma_x\sigma_y\,E P_{z,1}\,dxdy,\\
\frac12\frac{d}{dt}\|P_{z,2}\|_2^2
&=-\int_\Omega \frac{\sigma_x\sigma_y}{\epsilon_0^2}\,P P_{z,2}\,dxdy,\\
\frac12\frac{d}{dt}\|Q_x\|_2^2
&=-\int_\Omega \frac{\sigma_x}{\epsilon_0}Q_x^2\,dxdy
  +\int_\Omega \frac{\mu\sigma_x(\sigma_y-\sigma_x)}{\epsilon_0^2}H_xQ_x\,dxdy,\\
\frac12\frac{d}{dt}\|Q_y\|_2^2
&=-\int_\Omega \frac{\sigma_y}{\epsilon_0}Q_y^2\,dxdy
  +\int_\Omega \frac{\mu\sigma_y(\sigma_x-\sigma_y)}{\epsilon_0^2}H_yQ_y\,dxdy .
\end{aligned}
\]
Dropping nonpositive terms and applying Young's inequality to every mixed product gives
\[
\frac{d}{dt}\mathcal E_0(t)\le C_G\,\mathcal E_0(t),
\]
where \(C_G\) is finite whenever \(\sigma_x,\sigma_y\in L^\infty(\Omega)\), and depends
only on
\[
\epsilon_0,\epsilon_\infty,\mu,\chi,\tau,\|\sigma_x\|_\infty,\|\sigma_y\|_\infty,
\|\sigma_x\sigma_y\|_\infty,
\|\sigma_x(\sigma_y-\sigma_x)\|_\infty,
\|\sigma_y(\sigma_x-\sigma_y)\|_\infty .
\]
Consequently
\[
\mathcal E_0(t)\le e^{C_G t}\mathcal E_0(0).
\]
This is a Gronwall-type estimate.  It is not a monotone or long-time-uniform
boundedness theorem.

The terms responsible for possible growth in this estimate are exactly the
zeroth-order PML couplings
\[
EP,\quad EP_{z,1},\quad EP_{z,2},\quad PP_{z,2},\quad H_xQ_x,\quad H_yQ_y,
\]
and the sign-indefinite magnetic squares before the magnetic shift.  In shifted
variables the magnetic square terms cancel, but the balance contains
\[
H_xM_x+H_yM_y.
\]
Adding \(\|M_x\|_2^2+\|M_y\|_2^2\) directly is not a closed zeroth-order monotone
remedy because
\[
\frac12\frac{d}{dt}\|M_x\|_2^2
=\int_\Omega a_xM_x\partial_yE-b_yM_x^2\,dxdy,\qquad
\frac12\frac{d}{dt}\|M_y\|_2^2
=\int_\Omega -a_yM_y\partial_xE-b_xM_y^2\,dxdy .
\]
Integrating by parts would introduce derivatives of \(M_i\), and for variable
coefficients also derivatives of \(a_i\).  Thus the shifted variables simplify the
algebra but do not by themselves yield a local \(L^2\) monotone energy.

## No-PML case

If \(\sigma_x=\sigma_y=0\) and the PML auxiliaries are initially zero, then
\(P_{z,1}=P_{z,2}=Q_x=Q_y=0\) for all time and the verified balance reduces to
\[
\frac{d}{dt}\left(\mathcal E_{\rm em}+\frac1{2\chi}\|P\|_2^2\right)
=-\frac{\tau}{\chi}\|P_t\|_2^2\le0.
\]
Thus the no-PML alpha=1 Debye-Maxwell model has a positive monotone energy under the
natural auxiliary-zero compatibility condition.

Without that compatibility condition, arbitrary constant \(Q_i\) or \(P_{z,i}\)
remain as forcing terms when \(\sigma_x=\sigma_y=0\), and the eight-variable source
system need not have a uniformly bounded positive energy for all data.

## Edge PML obstruction: \(\sigma_x>0,\sigma_y=0\)

Assume constant \(\sigma_x=s>0\), \(\sigma_y=0\), and let
\[
b=\frac{s}{\epsilon_0}.
\]
Set
\[
E=P=P_{z,1}=P_{z,2}=H_y=Q_y=0,
\]
and take \(H_x,Q_x\) spatially constant.  The source equations reduce exactly to
\[
H_{x,t}=bH_x+\frac1\mu Q_x,\qquad
Q_{x,t}=-bQ_x-\mu b^2H_x .
\]
Equivalently,
\[
M_x=Q_x+\mu bH_x
\]
is constant, and
\[
H_{x,t}=\frac{M_x}{\mu},\qquad Q_x=M_x-\mu bH_x .
\]
Hence
\[
H_x(t)=H_x(0)+\frac{M_x(0)}{\mu}t,\qquad
Q_x(t)=Q_x(0)-bM_x(0)t .
\]
If \(M_x(0)\ne0\), both \(|H_x(t)|\) and \(|Q_x(t)|\) grow linearly.

This is an exact solution satisfying the PEC condition, because \(E=0\) on
\(\partial\Omega\).  Therefore any positive quadratic or coercive energy controlling
\(\|H_x\|_2^2+\|Q_x\|_2^2\) cannot be monotone decreasing or uniformly bounded for all
initial data in this edge-PML case.

The obstruction is not the polarization law; here \(P=0\) and the alpha=1 identity is
inactive.  It is the undamped shifted magnetic auxiliary in the zero-\(\sigma_y\)
direction:
\[
M_{x,t}=0
\]
for this spatially constant mode.

## Edge PML obstruction: \(\sigma_x=0,\sigma_y>0\)

The symmetric construction applies with \(s=\sigma_y>0\), \(b=s/\epsilon_0\), and
all variables zero except spatially constant \(H_y,Q_y\).  The reduced system is
\[
H_{y,t}=bH_y+\frac1\mu Q_y,\qquad
Q_{y,t}=-bQ_y-\mu b^2H_y .
\]
Equivalently \(M_y=Q_y+\mu bH_y\) is constant and
\[
H_y(t)=H_y(0)+\frac{M_y(0)}{\mu}t,\qquad
Q_y(t)=Q_y(0)-bM_y(0)t .
\]
Thus the second edge-PML case also rules out a positive monotone or uniformly bounded
energy for all eight-variable source-system data.

## Corner cases

When \(\sigma_x>0\) and \(\sigma_y>0\) are constant, the shifted equations contain
the damping terms
\[
M_{x,t}=a_x\partial_yE-\frac{\sigma_y}{\epsilon_0}M_x,\qquad
M_{y,t}=-a_y\partial_xE-\frac{\sigma_x}{\epsilon_0}M_y .
\]
The exact edge linear mode above is therefore absent in both symmetric
\(\sigma_x=\sigma_y\) and asymmetric \(\sigma_x\ne\sigma_y\) corners.  In the symmetric
corner \(a_x=a_y=0\), the shifted magnetic auxiliaries simply decay.  In the
asymmetric corner, the auxiliaries are damped but are also driven by transverse
derivatives of \(E\).

This artifact does not establish a positive monotone local \(L^2\) energy for either
corner case.  The natural shifted magnetic energy creates derivative couplings
\(M_x\partial_yE\) and \(M_y\partial_xE\); controlling those terms requires derivative,
nonlocal, or more structured Baffet-type variables beyond the zeroth-order energy
proved here.  The unconditional result retained for the terminal report is therefore
the Gronwall estimate above, together with the exact edge obstruction showing that the
full source problem cannot have a positive monotone/bounded energy for all displayed
variables without additional compatibility restrictions.

## Fractional case status

This artifact is only for \(\alpha=1\).  The fractional case \(0<\alpha<1\) can add a
positive memory contribution for the polarization law only after the alpha=1 PML
obstruction is resolved or restricted by compatibility assumptions.  Since the edge
obstruction above occurs with \(P=0\), fractional polarization cannot remove it.
