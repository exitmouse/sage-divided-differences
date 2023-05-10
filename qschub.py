#!/usr/bin/env python
# coding: utf-8-unix
# -*- mode: python-mode; python-indent-offset: 4 -*-
import sage
from forget_modules import monomial_iso, depolynomialate

nn = 3
#tring = PolynomialRing(QQ, 't', 1)
qring = PolynomialRing(QQ, 'q', nn+1)
xring = PolynomialRing(FractionField(qring), 'x', nn)
R = PolynomialRing(xring, 'y', nn)
#t = tring.gen()
t = qring.gens()[0]
q = qring.gens()[1:]
x = xring.gens()
y = R.gens()

RR = monomial_iso(R); RR
C = depolynomialate(RR, 1); C.basis()

# i for simple roots is 1-indexed
def alpha(i):
    return y[i-1]-y[i]

def siL(i):
    images = list(y).copy()
    tmp = images[i]
    images[i] = images[i-1]
    images[i-1] = tmp
    return R.hom(images, R)

def remove_root(i):
    def div(c):
        q,r = c.quo_rem(alpha(i))
        if r != 0:
            raise ValueError("%s is not divisible by %s"%(c, alpha(i)))
        else:
            return q
    return div

def _Ldivdiff(i,f):
    g = f - siL(i)(f)
    return remove_root(i)(g)

# Sends [X_w] to [X_{s_iw}] (MNS2022 eqn 6)
def Ldivdiff(i):
    return C.module_morphism(function=lambda f: C(_Ldivdiff(i,f.unbox())), codomain=C)

QR = PolynomialRing(QQ, 'v', 2*nn-1) # used for abstract quantum Es
g = QR.gens()
exs = g[:nn]
eqs = g[nn:]

Es = [1]*(nn+1)
qEs = [1]*(nn+1)

def truncate_vertices(f, start_idx):
    f = QR(f)
    return f.subs({exs[j]: 0 for j in range(start_idx, nn)}).subs({eqs[j]: 0 for j in range(start_idx-1, nn-1)})

def Eclassical(k,xvar_idx_bound):
    if k == 0:
        return QR(1)
    if xvar_idx_bound < k:
        return 0
    i = xvar_idx_bound - 1
    exclude_xi = Eclassical(k, i)
    include_xi = exs[i]*truncate_vertices(Es[k-1], i)
    return exclude_xi + include_xi


def Equantum(k, xvar_idx_bound):
    if k == 0:
        return QR(1)
    if xvar_idx_bound < k:
        return 0
    i = xvar_idx_bound - 1
    exclude_all = Equantum(k, i)
    include_x = exs[i]       * truncate_vertices(qEs[k-1],   i)
    include_q = 0
    if i >= 1:
        include_q = eqs[i-1] * truncate_vertices(qEs[k-2], i-1)
    return exclude_all + include_x + include_q

for i in range(nn+1):
    Es[i] = Eclassical(i, nn)
    qEs[i] = Equantum(i, nn)

#(J.4) in F.P degeneracy loci book
def topQSchubert_FP():
    prod = R(1)
    for p in range(1, nn):
        ximages = [x[j]-y[nn-p-1] if j < p else 0 for j in range(nn)]
        qimages = [q[j] if j < p-1 else 0 for j in range(nn-1)]
        factor = QR.hom(ximages + qimages, R)(qEs[p])
        prod *= factor
    return prod

topQSchubert_FP() - (x[0]-y[1])*((x[0]-y[0])*(x[1]-y[0])+q[0]) # 0, so it matches (J.4)

# Putting q^2 to match quantum groups conventions
# Subtracting 1 so that q=1 is classical case
# TODO: Unclear whether to put q^2-1 or (q-1)^2 but doing q^2-1 for now
# TODO switching to t
def topQSchubert():
    prod = R(1)
    for p in range(1, nn):
        ximages = [x[j]-y[nn-p-1] if j < p else 0 for j in range(nn)]
        qimages = [q[j] if j < p-1 else 0 for j in range(nn-1)]
        factor = QR.hom(ximages + qimages, R)(qEs[p])
        prod *= factor
    return prod
# A_on_cvar(i, d) is A \cdot c[i]^d

def rep_by_idx(x_fn, y_fn):
    def rho(tup):
        i = tup[0]
        d = tup[1]
        if i < len(x):
            return x_fn(i, d)
        else:
            return y_fn(i-len(x), d)
    return rho

def i_on_xvar(i,d):
    return x[i]**d

def i_on_yvar(i,d):
    return y[i]**d

I_fn = rep_by_idx(i_on_xvar, i_on_yvar)

# prop 2.4 jantzen. Infinite dim rep M(q[i]^i) with basis m_d := x[i]^d

def F_on_xvar(i, d):
    return x[i]**(d+1)

# no idea what to do with eqv vars but
def F_on_yvar(i, d):
    return y[i]**(d+1)

F_fn = rep_by_idx(F_on_xvar, F_on_yvar)

# action of k on ith part is lambda * t**(-2*d)
def scalar_action(i):
    return q[i]

# q[0]... go to 0 and have degree 2
# t has degree 1 and goes to 1

# As though we are taking the derivative of (q[i]^i*x[i])^d with respect to x. plus the t shift needed.
def K_on_xvar(i, d):
    coeff = scalar_action(i)*t**(-2*d)
    return coeff*x[i]**d

# Again no idea but maybe based on symmetry it should be this
def K_on_yvar(i, d):
    coeff = scalar_action(i)*t**(-2*d)
    return (-1)**d * coeff * y[i]**d

K_fn = rep_by_idx(K_on_xvar, K_on_yvar)

def Ki_on_xvar(i, d):
    coeff = (1/scalar_action(i))*t**(2*d)
    return coeff*x[i]**d

def Ki_on_yvar(i, d):
    coeff = (1/scalar_action(i))*t**(2*d)
    return (-1)**d * coeff * y[i]**d

Ki_fn = rep_by_idx(Ki_on_xvar, Ki_on_yvar)

# 1 + q + ... + q^(k-1)
def qnum_poly(i,k):
    s = R(0)
    for j in range(k):
        s += q[i]**j
    return s

# t^(1-k) + t^(3-k) + ... + t^(k-3) + t^(k-1)
def tnum_central(k):
    s = R(0)
    for j in range(k):
        s += t**(2*j - k + 1)
    return s

# E is acting on x by taking the q[i] derivative.
# We want E^d x[i]^d = [d]! * q[i]^d
# or possibly [d]! * (q[i]^2)^d?
# Let's just use the standard rep M(q[i]^i)
def E_on_xvar(i, d):
    if d == 0:
        return 0
    num = scalar_action(i)*t**(1-d) - (1/scalar_action(i))*t**(d-1)
    denom = t - t**(-1)
    coeff = tnum_central(d)*num/denom
    return coeff * x[i]**(d-1)

def E_on_yvar(i, d):
    if d == 0:
        return 0
    num = scalar_action(i)*t**(1-d) - (1/scalar_action(i))*t**(d-1)
    denom = t - t**(-1)
    coeff = tnum_central(d)*num/denom
    return (-1)**d * coeff * y[i]**(d-1)

E_fn = rep_by_idx(E_on_xvar, E_on_yvar)
def midx_flatten(midx):
    xdict = midx[0].dict()
    ydict = midx[1].dict()
    xexps = [xdict[x[i]] if x[i] in xdict else 0 for i in range(len(x))]
    yexps = [ydict[y[i]] if y[i] in ydict else 0 for i in range(len(y))]
    ps = xexps+yexps
    return [(i,ps[i]) for i in range(len(ps))]

# rho_X accepts a list of parts with their indices and returns a monomial in R
def rep_monomial(i_fn, e_fn, k_fn, ki_fn, f_fn):
    def rho_I(parts):
        tot = R(1)
        for p in parts:
            tot *= i_fn(p)
        return tot
    def rho_K(parts):
        tot = R(1)
        for p in parts:
            tot *= k_fn(p)
        return tot
    def rho_Ki(parts):
        tot = R(1)
        for p in parts:
            tot *= ki_fn(p)
        return tot
    def rho_E(parts):
        if len(parts) == 0:
            return R(0)
        e_tensor_i = e_fn(parts[0])*rho_I(parts[1:])
        k_tensor_e = k_fn(parts[0])*rho_E(parts[1:])
        return e_tensor_i + k_tensor_e
    def rho_F(parts):
        if len(parts) == 0:
            return R(0)
        f_tensor_ki = f_fn(parts[0])*rho_Ki(parts[1:])
        i_tensor_f = i_fn(parts[0])*rho_F(parts[1:])
        return f_tensor_ki + i_tensor_f
    return {'i': rho_I,
            'e': rho_E,
            'k': rho_K,
            'ki': rho_Ki,
            'f': rho_F}

def apply_rho_to_midx(rho, midx):
    parts = midx_flatten(midx)
    return C(rho(parts))

def my_rep_on_basis():
    from functools import partial
    rhos = rep_monomial(I_fn, E_fn, K_fn, Ki_fn, F_fn)
    actions = {
        name:
        C.module_morphism(on_basis=partial(apply_rho_to_midx, rho), codomain=C)
        for name, rho in rhos.items()
        }
    return actions
