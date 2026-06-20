# Stage 2 Repair Design for the Edge-PML Obstruction

Task: `task-stage2-repair-design`

Predecessor facts:

- `fact:2d_maxwell_pml_energy_functional_exploration:alpha1-algebra-balance`
- `fact:2d_maxwell_pml_energy_functional_exploration:edge-pml-linear-obstruction`
- `fact:2d_maxwell_pml_energy_functional_exploration:augmented-gronwall-energy`

## Scope

This artifact starts from the verified alpha \(=1\) source model obstruction and
does not re-use that obstruction as final success.  It compares three repairs:

1. a compatibility restriction on the old auxiliary data;
2. a shifted-variable MPML-style damping of the free magnetic auxiliary mode;
3. a covariantly damped Maxwell-Debye absorbing-layer model.

The third model is the strongest fully closed result below: it has a positive
monotone energy identity for arbitrary data in its variables.  It is a modified
absorbing model, not algebraically identical to the old eight-variable unsplit
PML formulation.

Throughout this artifact
\[
\chi=\epsilon_0(\epsilon_s-\epsilon_\infty)>0,\qquad
b_x=\frac{\sigma_x}{\epsilon_0},\quad b_y=\frac{\sigma_y}{\epsilon_0},
\]
and
\[
a_x=\frac{\sigma_y-\sigma_x}{\epsilon_0}=b_y-b_x,\qquad
a_y=\frac{\sigma_x-\sigma_y}{\epsilon_0}=b_x-b_y.
\]

## Old-model obstruction term

For the source equations the shifted magnetic variables
\[
M_x=Q_x-\mu a_xH_x,\qquad M_y=Q_y-\mu a_yH_y
\]
satisfy
\[
M_{x,t}=a_x\partial_yE-b_yM_x,\qquad
M_{y,t}=-a_y\partial_xE-b_xM_y .
\]
In the \(x\)-edge case \(\sigma_x=s>0,\sigma_y=0\), the spatially constant
mode with
\[
E=P=P_{z,1}=P_{z,2}=H_y=Q_y=0
\]
has \(M_x=Q_x+\mu b_xH_x\) conserved.  Hence
\[
H_x(t)=H_x(0)+\frac{M_x(0)}{\mu}t,\qquad
Q_x(t)=Q_x(0)-b_xM_x(0)t .
\]
The obstruction is therefore the undamped shifted magnetic auxiliary \(M_x\) in
the edge direction with zero transverse damping.  The \(y\)-edge case is
symmetric with \(M_y\).

## Repair 1: compatibility restriction on old auxiliaries

The weakest repair is to restrict the old model to a physical auxiliary
subspace that excludes the verified free mode.  In the constant \(x\)-edge
case this means
\[
M_x(0)=Q_x(0)+\mu b_xH_x(0)=0
\]
for the spatially constant edge mode; in the constant \(y\)-edge case it means
\[
M_y(0)=Q_y(0)+\mu b_yH_y(0)=0 .
\]
This compatibility condition is physically meaningful if the old \(Q\)
variables are interpreted as derived PML histories rather than independent
initial data.

The candidate energy for this restricted old model remains the positive
augmented source energy
\[
\mathcal E_0(t)
=\frac12\int_\Omega\left(
\epsilon_0\epsilon_\infty E^2+\mu H_x^2+\mu H_y^2
+\chi^{-1}P^2+P_{z,1}^2+P_{z,2}^2+Q_x^2+Q_y^2
\right)\,dxdy .
\]
Under only bounded nonnegative absorptions, the previous verified result gives
\[
\mathcal E_0'(t)\le C_G\mathcal E_0(t).
\]
The compatibility condition removes the exact linear edge mode in the
one-dimensional constant-mode test.  It does not by itself give a closed
two-dimensional monotone energy, because in an \(x\)-edge
\[
M_{x,t}=-b_x\partial_yE
\]
when \(\sigma_y=0\).  Thus \(M_x=0\) is not invariant for general
two-dimensional fields unless an additional transverse condition
\(\partial_yE=0\) is imposed.  Classification: useful compatibility repair for
the old edge free mode, but not a complete 2D monotone repair.

## Repair 2: shifted-variable MPML damping

The second repair keeps the shifted magnetic variables but adds a multi-axial
or CFS-style damping \(\eta_x,\eta_y\ge0\) to the modes that were undamped at
edges.  The modified \(Q\) equations are
\[
Q_{x,t}=-(b_x+\eta_x)Q_x+\mu(b_x+\eta_x)a_xH_x,
\]
\[
Q_{y,t}=-(b_y+\eta_y)Q_y+\mu(b_y+\eta_y)a_yH_y,
\]
while the \(E,H,P,P_z\) equations are unchanged.  Equivalently,
\[
M_{x,t}=a_x\partial_yE-(b_y+\eta_x)M_x,
\qquad
M_{y,t}=-a_y\partial_xE-(b_x+\eta_y)M_y .
\]
Thus the old \(x\)-edge constant-mode obstruction becomes
\[
H_{x,t}=\frac{M_x}{\mu},\qquad M_{x,t}=-\eta_x M_x
\]
when \(E=0\), \(\sigma_x>0\), and \(\sigma_y=0\).  If \(\eta_x>0\), then for any
constant \(c_x>0\)
\[
\mathcal E_{x,\eta}
=\frac{\mu}{2}\left|H_x+\frac{M_x}{\mu\eta_x}\right|^2
+\frac{c_x}{2}|M_x|^2
\]
is positive in \((H_x,M_x)\) and satisfies
\[
\frac{d}{dt}\mathcal E_{x,\eta}=-c_x\eta_x|M_x|^2\le0 .
\]
The \(y\)-edge formula is identical with \(x\) and \(y\) interchanged.

This repair removes the specific linear-growth obstruction without imposing
the compatibility \(M_i(0)=0\).  In the full two-dimensional system the energy
derivative still contains transverse derivative couplings
\[
M_x\partial_yE,\qquad M_y\partial_xE,
\]
so a purely zeroth-order monotone energy is not closed by this shift alone.
With derivative energies these terms are candidates for a dissipative
lower-order or Gronwall estimate.  Classification: monotone for the isolated
edge free subsystem, promising MPML repair for the old obstruction, but not a
completed full 2D monotone proof in this artifact.

## Repair 3: covariantly damped Maxwell-Debye absorbing layer

The best closed repair is to replace the old independent \(P_z,Q\) auxiliary
system by a covariantly damped Maxwell-Debye absorbing layer.  Let
\(\rho_x,\rho_y\in L^\infty(\Omega)\) be nonnegative, time-independent layer
profiles that vanish in the physical region, and put
\[
\rho=\rho_x+\rho_y,\qquad D_\rho=\partial_t+\rho .
\]
The modified model is
\[
\boxed{
\begin{aligned}
\epsilon_0\epsilon_\infty D_\rho E
&=\partial_xH_y-\partial_yH_x-D_\rho P,\\
\mu(\partial_t+\rho_y)H_x&=-\partial_yE,\\
\mu(\partial_t+\rho_x)H_y&=\partial_xE,\\
P+\tau D_\rho P&=\chi E .
\end{aligned}}
\]
The boundary condition is the same PEC condition,
\[
E=0\quad\text{on }\partial\Omega .
\]

The model is local, agrees with the physical alpha \(=1\) Maxwell-Debye system
where \(\rho_x=\rho_y=0\), and damps the electric polarization by the same
covariant derivative used in the layer equation.  This last point is the
essential repair of the old source-model term
\(-((\sigma_x+\sigma_y)/\epsilon_0)EP\): the damping is applied to the
Debye law itself, so the polarization contribution becomes positive
dissipation rather than a sign-indefinite mixed product.

### Candidate energy and positivity

Use
\[
\mathcal E_\rho(t)
=\frac12\int_\Omega\left(
\epsilon_0\epsilon_\infty E^2+\mu H_x^2+\mu H_y^2+\chi^{-1}P^2
\right)\,dxdy .
\]
This energy is positive definite in \((E,H_x,H_y,P)\) because
\(\epsilon_0,\epsilon_\infty,\mu,\chi>0\).

### Energy identity

Multiplying the electric equation by \(E\), the magnetic equations by
\(H_x,H_y\), integrating over \(\Omega\), and using \(E=0\) on
\(\partial\Omega\) gives cancellation of the Maxwell principal boundary flux:
\[
\int_\Omega
\left(E\partial_xH_y-E\partial_yH_x-H_x\partial_yE+H_y\partial_xE\right)
\,dxdy=0 .
\]
The covariant polarization law gives
\[
E\,D_\rho P
=\frac{1}{\chi}P\,D_\rho P+\frac{\tau}{\chi}|D_\rho P|^2
=\frac{1}{2\chi}\partial_t(P^2)
+\frac{\rho}{\chi}P^2
+\frac{\tau}{\chi}|D_\rho P|^2 .
\]
Therefore
\[
\boxed{
\frac{d}{dt}\mathcal E_\rho(t)
=-\int_\Omega\left(
\epsilon_0\epsilon_\infty\rho E^2
+\mu\rho_yH_x^2
+\mu\rho_xH_y^2
+\frac{\rho}{\chi}P^2
+\frac{\tau}{\chi}|D_\rho P|^2
\right)\,dxdy\le0 .}
\]

Consequently
\[
\boxed{\mathcal E_\rho(t)\le \mathcal E_\rho(0)\quad\text{for all }t\ge0.}
\]
This is a genuinely monotone, long-time-uniform energy estimate.  It contains
no independent \(P_{z,i}\) or \(Q_i\) variables, so the old edge free mode is
not present.

### Absorbing-layer status

This repair should be viewed as a certified stable absorbing Maxwell-Debye
layer.  It is PML-like in the sense that the layer profiles vanish in the
physical region and the layer applies directional magnetic damping
\(\rho_y,\rho_x\) together with covariant electric-polarization damping
\(\rho=\rho_x+\rho_y\).  The proof above establishes stability and absorption
through a monotone energy.  It does not prove exact perfect matching for every
incidence angle; if exact reflectionless matching is required, a separate
frequency-domain matching calculation remains open.

## Selection

The compatibility repair is too narrow for a full 2D theorem.  The MPML shift
directly repairs the verified edge free mode, but its full 2D monotone energy
requires additional derivative or nonlocal structure.

The covariantly damped Maxwell-Debye absorbing layer is the selected best
candidate because it has a closed positive energy and an exact monotone
identity under variable nonnegative layer profiles.  Its limitation is that it
is a modified absorbing model rather than a proof that the old eight-variable
unsplit PML has a monotone energy.
