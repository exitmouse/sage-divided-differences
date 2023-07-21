#!/usr/bin/env python
# coding: utf-8-unix
# -*- mode: python-mode; python-indent-offset: 4 -*-
# Schubert polynomials in other Lie types in Sage
# Author: Jesse Selover
# Copyright: 2023 Jesse Selover

from forget_modules import *

n = 3
R = PolynomialRing(QQ,'x',n)
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
#TODO: implement top class

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

C = depolynomialate(p, 2)

def _divdiff(i,f):
    g = f - siR(i,f)
    return p(g).map_coefficients(remove_root(i))

def c_divdiff(i):
    return C.module_morphism(function=lambda f: C(_divdiff(i,f.unbox())), codomain=C)

def divdiff(i):
    return lambda f: (c_divdiff(i)(C(f))).unbox()

# QQ-linear differential operator can be defined on the images of generators
def extend_leibniz(gen_images):
    def extend_leibniz_midx(midx):
        m = C.monomial(midx)
        if m in gen_images.keys():
            return gen_images[m]
        f,g = midxfactor(midx,1) # Pull off some part
        return extend_leibniz_midx(f)*C.monomial(g) + C.monomial(f)*extend_leibniz_midx(g)
    return C.module_morphism(on_basis=lambda midx: C(extend_leibniz_midx(midx)),
                             #domain=C.parent(),
                             codomain=C)
# QQ-linear operator satisfying the leibniz rule only for squares:
# d(f^2*g) = d(f^2)*g + f^2*d(g)
#def extend_leibniz_squares()
#

def ddzi_gen(i):
    def ddzi_internal(generator):
        if generator == z(i):
            return 1
        supp = p(generator).support()[0]
        if len(supp) == 1:
            return -(1/2)*supp[0]*z(i)^(supp[0]-1)
        return 0
    return ddzi_internal

def ddpi_gen(i):
    def ddpi_internal(generator):
        supp = p(generator).support()[0]
        if len(supp) == 1:
            if supp[0] == i:
                return 1
        return 0
    return ddpi_internal

tgens = FiniteEnumeratedSet(U.gens())
zgens = FiniteEnumeratedSet(R.gens())
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

def c_ddz(i):
    return extend_leibniz(Family(SymGens(), ddzi_gen(i)))

def c_ddp(i):
    return extend_leibniz(Family(SymGens(), ddpi_gen(i)))


CEnd = C.Hom(C)

def principal_specialize_gen():
    def psg_internal(generator):
        if generator == t:
            return 0
        for i in range(len(zgens)):
            if generator == z(i+1):
                return t^(i)
        supp = p(generator).support()[0]
        if len(supp) == 1:
            i = supp[0]
            # principal specialization p_i(q^{-1}, q^{-2}, ...)
            # = 1/(q^d-1) * [prod_{j=1}^{i-1} (q^j + 1)/(q^j - 1)]

# Wrapper function because coercions are finicky
# Input: f, a type B Schubert polynomial in ring Sym
# Output: d/dp_1 f, coerced to the ring Sym
def divergence(f):
    return (c_ddp(1)(C(f))).unbox()

# Tests:
codim1 = [divdiff(i)(topB3poly) for i in range(3)]

f = divergence(topB3poly)
print(f)
for g in codim1:
    f -= 2*g
print(f)
