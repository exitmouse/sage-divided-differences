#!/usr/bin/env python
# coding: utf-8-unix
# -*- mode: python-mode; python-indent-offset: 4 -*-
import forget_modules

n = 3
R = PolynomialRing(QQ,'x',n-1)
zarr = R.gens()
Sym = SymmetricFunctions(R['t'])
P = Sym.hall_littlewood(t=-1).P()
p = Sym.power()
U = p.base_ring()

def z(i):
    return zarr[i-1]

def alpha(i):
    if i == 0:
        return -2*z(1)
    else:
        return z(i)-z(i+1)

topB3poly = (P[5,3,1] + P[4,3,1]*z(1) + P[5,2,1]*z(1) + P[4,2,1]*z(1)*z(1) +
             P[4,3,1]*z(2) + P[4,2,1]*z(1)*z(2) + P[3,2,1]*z(1)*z(1)*z(2))


def base_siR(i):
    images = list(zarr).copy()
    if i == 0:
        images[0] *= -1
    else:
        tmp = images[i]
        images[i] = images[i-1]
        images[i-1] = tmp
    return R.hom(images, R)

#omits index i from a partition
def omit(i,partn):
    return Partition([partn[j] for j in range(partn.length()) if j != i])

#p[j] = sum_i (-z(i)/2)^j
def s0R_helper(partn):
    result = Sym(1)
    for i in range(partn.length()):
        j = partn[i]
        result *= (p[j] + z(1)**j)
    return result

def siR(i,f):
    f = p(f)
    F = s0R_helper if i == 0 else (lambda l: p(l))
    return p.module_morphism(on_basis = F,codomain = Sym)(f.map_coefficients(base_siR(i)))

def remove_root(i):
    def div(c):
        q,r = c.quo_rem(alpha(i))
        if r != 0:
            raise ValueError("%s is not divisible by %s"%(c, alpha(i)))
        else:
            return q
    return div

def divdiff(i,f):
    g = f - siR(i,f)
    return p(g).map_coefficients(remove_root(i))

C = depolynomialate(p, 2)

# QQ-linear differential operator can be defined on the images of generators
def extend_leibniz(gen_images):
    def extend_leibniz_monomial(m):
        if m in gen_images.keys():
            return gen_images[m]
        f,g = mfactor(m) # Pull off some part
        return extend_leibniz_monomial(f)*g + f*extend_leibniz_monomial(g)
    return C.module_morphism(on_basis=lambda midx: C(extend_leibniz_monomial(C.monomial(midx))),
                             #domain=C.parent(),
                             codomain=C)
# QQ-linear operator satisfying the leibniz rule only for squares:
# d(f^2*g) = d(f^2)*g + f^2*d(g)
#def extend_leibniz_squares()
#

def ddz1_gen(generator):
    if generator == z(1):
        return 1
    supp = p(generator).support()[0]
    if len(supp) == 1:
        return -(1/2)*supp[0]*z(1)^(supp[0]-1)
    return 0

tgens = FiniteEnumeratedSet(U.gens())
zgens = FiniteEnumeratedSet(U.gens())
from sage.sets.set_from_iterator import EnumeratedSetFromIterator
from itertools import count
pgenerators = EnumeratedSetFromIterator(
  count,
  args = (1,),
  name = "Power Sums",
  category = InfiniteEnumeratedSets(),
  cache = True)

class SymGens(DisjointUnionEnumeratedSets):
    def __init__(self):
        super().__init__(Family((tgens, zgens, pgenerators)))
    def __contains__(self, x):
        if x in tgens:
            return True
        if x in zgens:
            return True
        if x not in Sym:
            return False
        supp = p(x).support()
        if len(supp) == 1 and len(supp[0]) == 1:
            return True
        return False

ddz1 = extend_leibniz(Family(SymGens(), ddz1_gen))
