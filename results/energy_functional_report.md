# Energy Functional Report

Problem id: `2d_maxwell_pml_energy_functional_exploration`

Source: `sources/energy_functional_problem.tex`

## Original goal summary

Analyze the two-dimensional TM Maxwell-PML system with unknowns
\[
E,\ H_x,\ H_y,\ P,\ P_{z,1},\ P_{z,2},\ Q_x,\ Q_y
\]
and PEC boundary condition \(E=0\) on \(\partial\Omega\).  The first target is a
positive monotone decreasing energy.  If that is unavailable, the target is the
strongest valid bounded-energy, no-abnormal-growth, Gronwall, or obstruction result.

The non-fractional case is the alpha \(=1\) case of
\[
P+\tau^\alpha\partial_t^\alpha P=\chi E,\qquad
\chi=\epsilon_0(\epsilon_s-\epsilon_\infty).
\]
This report analyzes \(\alpha=1\).  The fractional case \(0<\alpha<1\) is postponed
because the alpha \(=1\) PML obstruction already occurs with \(P=0\).

## Fact index

| fact id | status | verification |
|---|---:|---|
| `fact:2d_maxwell_pml_energy_functional_exploration:alpha1-algebra-balance` | verified | `verification/results/verify-20260619T180514214437Z-fact-alpha-1-pec-balance-and-shifted-mag.json` |
| `fact:2d_maxwell_pml_energy_functional_exploration:edge-pml-linear-obstruction` | verified | `verification/results/verify-20260619T181255226823Z-fact-the-alpha-1-source-model-has-exact-.json` |
| `fact:2d_maxwell_pml_energy_functional_exploration:augmented-gronwall-energy` | verified | `verification/results/verify-20260619T181650715321Z-fact-a-positive-augmented-zeroth-order-e.json` |

## Model used

For \(\alpha=1\), the equations used are exactly
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
  +\frac{\mu\sigma_y(\sigma_x-\sigma_y)}{\epsilon_0^2}H_y .
\end{aligned}
\]
The boundary assumption is PEC:
\[
E=0\quad\text{on }\partial\Omega .
\]
The absorption assumptions for the Gronwall estimate are
\[
\sigma_x,\sigma_y\in L^\infty(\Omega),\qquad \sigma_x,\sigma_y\ge0,
\]
with time-independent coefficients.  This includes constant, separated-variable, and
general spatially variable profiles.

## Verified alpha=1 balance

The electromagnetic energy is
\[
\mathcal E_{\rm em}
=\frac12\int_\Omega
\left(\epsilon_0\epsilon_\infty E^2+\mu H_x^2+\mu H_y^2\right)\,dxdy .
\]
PEC makes the Maxwell principal boundary flux
\[
\int_{\partial\Omega}E(H_y n_x-H_x n_y)\,ds
\]
vanish.  Using \(P+\tau P_t=\chi E\),
\[
E P_t=\frac{1}{2\chi}\frac{d}{dt}\|P\|_2^2
+\frac{\tau}{\chi}\|P_t\|_2^2 .
\]
Thus
\[
\mathcal E_{\rm em+P}
=\mathcal E_{\rm em}+\frac1{2\chi}\|P\|_2^2
\]
is positive and satisfies
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

With
\[
a_x=\frac{\sigma_y-\sigma_x}{\epsilon_0},\quad
a_y=\frac{\sigma_x-\sigma_y}{\epsilon_0},\quad
b_x=\frac{\sigma_x}{\epsilon_0},\quad
b_y=\frac{\sigma_y}{\epsilon_0},
\]
and shifted variables
\[
M_x=Q_x-\mu a_xH_x,\qquad M_y=Q_y-\mu a_yH_y,
\]
one has
\[
\mu H_{x,t}=-\partial_yE+M_x,\quad
\mu H_{y,t}=\partial_xE+M_y,
\]
\[
M_{x,t}=a_x\partial_yE-b_yM_x,\qquad
M_{y,t}=-a_y\partial_xE-b_xM_y .
\]
Substitution cancels the sign-indefinite magnetic squares and leaves
\[
\begin{aligned}
\frac{d}{dt}\mathcal E_{\rm em+P}
=\int_\Omega\Big[
&-\epsilon_\infty(\sigma_x+\sigma_y)E^2
-\frac{\tau}{\chi}P_t^2
-\frac{\sigma_x+\sigma_y}{\epsilon_0}EP
+E(P_{z,1}+P_{z,2})\\
&+H_xM_x+H_yM_y
\Big]\,dxdy .
\end{aligned}
\]

## Positive Gronwall energy

The positive augmented energy proved here is
\[
\mathcal E_0(t)
=\frac12\int_\Omega
\left(\epsilon_0\epsilon_\infty E^2+\mu H_x^2+\mu H_y^2
+\chi^{-1}P^2+P_{z,1}^2+P_{z,2}^2+Q_x^2+Q_y^2\right)\,dxdy .
\]
Adding the \(L^2\) derivatives of \(P_{z,1},P_{z,2},Q_x,Q_y\) to the verified
balance and applying Young's inequality gives
\[
\boxed{\frac{d}{dt}\mathcal E_0(t)\le C_G\mathcal E_0(t)}
\]
with \(C_G<\infty\) depending only on the material constants and the \(L^\infty\)
sizes of
\[
\sigma_x,\ \sigma_y,\ \sigma_x\sigma_y,\ 
\sigma_x(\sigma_y-\sigma_x),\ 
\sigma_y(\sigma_x-\sigma_y).
\]
Therefore
\[
\boxed{\mathcal E_0(t)\le e^{C_Gt}\mathcal E_0(0).}
\]
This is a Gronwall-type estimate.  It is not monotone and not uniform in long time.

The possible-growth terms are exactly
\[
EP,\quad EP_{z,1},\quad EP_{z,2},\quad H_xQ_x,\quad H_yQ_y,
\]
together with the magnetic sign-indefinite square terms before the shift.  In shifted
variables the magnetic issue becomes \(H_xM_x+H_yM_y\).  Adding plain
\(\|M_x\|_2^2+\|M_y\|_2^2\) is not a closed local \(L^2\) monotone fix because its
derivative contains \(M_x\partial_yE\) and \(M_y\partial_xE\).

## Case split

### No PML

If \(\sigma_x=\sigma_y=0\) and the PML auxiliaries are initially zero, then
\[
P_{z,1}=P_{z,2}=Q_x=Q_y=0
\]
for all time, and
\[
\frac{d}{dt}\mathcal E_{\rm em+P}
=-\frac{\tau}{\chi}\|P_t\|_2^2\le0 .
\]
So the no-PML Debye-Maxwell subsystem has a monotone positive alpha \(=1\) energy
under the natural auxiliary-zero compatibility condition.

### Edge PML

For constant \(\sigma_x=s>0,\sigma_y=0\), set
\[
E=P=P_{z,1}=P_{z,2}=H_y=Q_y=0
\]
and take \(H_x,Q_x\) spatially constant.  With \(b=s/\epsilon_0\),
\[
H_{x,t}=bH_x+\frac1\mu Q_x,\qquad
Q_{x,t}=-bQ_x-\mu b^2H_x .
\]
The shifted quantity
\[
M_x=Q_x+\mu bH_x
\]
is constant, hence
\[
H_x(t)=H_x(0)+\frac{M_x(0)}{\mu}t,\qquad
Q_x(t)=Q_x(0)-bM_x(0)t .
\]
If \(M_x(0)\ne0\), \(H_x,Q_x\) grow linearly while \(E=0\) satisfies PEC.

The case \(\sigma_x=0,\sigma_y=s>0\) has the symmetric construction with \(H_y,Q_y\)
and constant \(M_y=Q_y+\mu bH_y\).

Therefore the source model as stated has an exact edge-PML obstruction: no positive
coercive energy controlling all displayed variables can be monotone decreasing or
uniformly bounded for all initial data in the edge cases.

### Corner PML

For constant \(\sigma_x,\sigma_y>0\), both shifted magnetic auxiliaries are damped:
\[
M_{x,t}=a_x\partial_yE-\frac{\sigma_y}{\epsilon_0}M_x,\qquad
M_{y,t}=-a_y\partial_xE-\frac{\sigma_x}{\epsilon_0}M_y .
\]
Thus the exact edge linear mode is absent in both the symmetric corner
\(\sigma_x=\sigma_y\) and the asymmetric corner \(\sigma_x\ne\sigma_y\).
However, the shifted local \(L^2\) energy still produces derivative couplings
\(M_x\partial_yE\) and \(M_y\partial_xE\).  A monotone corner energy would need extra
derivative, nonlocal, or Baffet-type time-integrated structure not closed by the
zeroth-order variables above.  The verified result retained for the corner cases is
the augmented Gronwall estimate.

## Positivity and failure of monotonicity

\(\mathcal E_{\rm em+P}\) and \(\mathcal E_0\) are positive because
\(\epsilon_0,\epsilon_\infty,\mu,\chi>0\).  The no-PML compatible subsystem is
monotone.  The full eight-variable PML model is not covered by any unconditional
positive monotone or uniformly bounded energy over all data, because the edge-PML
linear solution makes such an energy impossible if it controls \(H_i,Q_i\).

The final classification is:

- no PML with zero auxiliaries: monotone alpha \(=1\) energy;
- full source model with arbitrary auxiliaries and edge PML allowed: verified
  obstruction to unconditional monotone or uniformly bounded energy;
- bounded nonnegative time-independent \(\sigma_x,\sigma_y\): positive augmented
  Gronwall estimate;
- fractional \(0<\alpha<1\): postponed.

## Assembly

`fact:2d_maxwell_pml_energy_functional_exploration:alpha1-algebra-balance` verifies
the source-model algebra, PEC cancellation, polarization energy, and magnetic shift.
`fact:2d_maxwell_pml_energy_functional_exploration:edge-pml-linear-obstruction`
shows that the edge cases requested by the source problem contain exact linear-growth
solutions for arbitrary eight-variable data.  This blocks the strong monotone target
and also blocks unconditional long-time-uniform boundedness for the model as stated.
`fact:2d_maxwell_pml_energy_functional_exploration:augmented-gronwall-energy`
provides the strongest unconditional positive estimate established here:
\[
\mathcal E_0(t)\le e^{C_Gt}\mathcal E_0(0).
\]

Thus the terminal result is an obstruction plus Gronwall-type energy estimate for
\(\alpha=1\), not a monotone two-dimensional PML energy.  The fractional memory case
is not added, since it cannot remove the displayed edge obstruction where \(P=0\).
