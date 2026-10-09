"""Exact algebra checks for V7; these checks are not a PDE formalization."""
import sympy as s
p,r,c,tau,mu,eps,kappa=s.symbols('p r c tau mu eps kappa', positive=True)
u,E,Et,P,Pt,q,h,v,lam=s.symbols('u E Et P Pt q h v lam', real=True)
a,b=p+r,p*r
w=(c-r)/a
phi=lam-h
phit=r*h-p*lam
lamt=v+phit
sp=s.factor(lam*lamt+w*phi*phit-(v+c*h)*lam+p*(c+p)/a*lam**2+r*(c-r)/a*h**2)
assert sp==0
print('general constant-shift spatial identity:',sp)
A=1+(a+c)*tau; B=c+b*tau; G=a*c+b*(1+c*tau)
polar_product=(Pt+a*P+b*q)*(tau*Pt+(1+c*tau)*P+c*q)
polar_derivative=A*P*Pt+B*(Pt*q+P*P)+G*q*P
polar_diss=tau*Pt**2+(a-c+tau*(a*c-b))*P**2+b*c*q**2
pol=s.factor(polar_product-polar_derivative-polar_diss)
assert pol==0
print('general constant-shift Debye identity:',pol)
kinetic_product=(Et+a*E+b*u)*(E+c*u)
kinetic_derivative=E*Et+c*(E**2+u*Et)+(b+a*c)*u*E
kinetic_diss=(a-c)*E**2+b*c*u**2
kin=s.factor(kinetic_product-kinetic_derivative-kinetic_diss)
assert kin==0
print('general constant-shift electric identity:',kin)
AR=1+(a-c)*tau+(a*c-b)*tau**2+b*c*tau**3
compat=s.factor((A*P**2+2*B*P*q+G*q**2).subs(q,kappa*u-tau*P)
                 -(AR*P**2+2*kappa*c*(1-a*tau-b*tau**2)*u*P+kappa**2*G*u**2))
assert compat==0
print('compatibility-reduced polarization quadratic:',compat)
a0,b0=s.symbols('a0 b0',nonnegative=True)
alpha=1+2*a0*tau; beta=a0+b0*tau; gamma=a0**2+b0*(1+a0*tau)
det=s.factor(alpha*gamma-beta**2)
expected=b0+a0*b0*tau+2*a0**3*tau+b0*(2*a0**2-b0)*tau**2
assert s.expand(det-expected)==0
print('V6 polarization determinant:',s.expand(det))
# Primitive-to-eight-variable magnetic invariant checks.
Hx,Hy,Qx,Qy,Ex,Ey=s.symbols('Hx Hy Qx Qy Ex Ey')
Hxt=(-Ey-mu*(r-p)*Hx+Qx)/mu
Hyt=(Ex-mu*(p-r)*Hy+Qy)/mu
phiyt=-mu*Hxt-Ey
phix_t=mu*Hyt-Ex
Qxt=-p*Qx+mu*p*(r-p)*Hx
Qyt=-r*Qy+mu*r*(p-r)*Hy
assert s.expand(Qxt-p*phiyt)==0
assert s.expand(Qyt+r*phix_t)==0
print('magnetic mapping invariants: 0, 0')
# Explicit nondimensional full-domain profile configuration.
Cp2=2/s.pi**2
AA=s.Integer(3); K=8*AA*Cp2
cc=s.Rational(1,128); S=s.Rational(1,512)
limits=[1/s.sqrt(K),1/(8*AA*K),1/(8*AA)]
assert all(float(cc)<float(v) for v in limits)
assert S<=cc/4
print('example K=',K,'=',float(K))
print('example c=',cc,'S=',S,'c_star=',min(float(v) for v in limits))
print('coercivity loss 4*mu*A*c^2*C_P^2=',float(4*AA*cc**2*Cp2))
print('electric E absorption: K*S^2=',float(K*S**2))
print('Debye Pt absorption ratio=',float(8*cc*AA*K))
print('Debye Ptt absorption ratio=',float(8*cc*AA))
print('ALL EXACT ALGEBRA CHECKS PASSED')
