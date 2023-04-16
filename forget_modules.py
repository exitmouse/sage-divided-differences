#!/usr/bin/env python
# coding: utf-8-unix
# -*- mode: python-mode; python-indent-offset: 4 -*-
import sage
from sage.structure.richcmp import richcmp
class ForgottenElement(sage.structure.element.ModuleElement):
    def __init__(self, parent, x, f=None):
        while isinstance(x, ForgottenElement):
            x = x.x
        self.x = x
        self.f = f
        sage.structure.element.ModuleElement.__init__(self, parent=parent)
    def _lmul_(self, c):
        if self.f is None:
            return self.parent()(c*self.x)
        else:
            return self.parent()(self.f(c)*self.x)
    def _add_(self, other):
        return self.parent()(self.x + other.x)
    def _richcmp_(self, other, op):
        if isinstance(other, ForgottenElement):
            other = other.x
        return richcmp(self.x, other, op)
    def __hash__(self):
        return hash(self.x)
    def _repr_(self):
        return repr(self.x)
    def unbox(self):
        return self.internal(self)
class ForgetModule(sage.modules.module.Module):
    Element = ForgottenElement
    def __init__(self, A, Bmod, f=None):
        self.internal = Bmod
        while isinstance(self.internal, ForgetModule):
            g = self.internal.f
            if g is not None:
                if self.f is None:
                    self.f = g
                else:
                    self.f = lambda a: f(g(a))
            self.internal = self.internal.internal
        self.A = A
        self.f = f
        super().__init__(A)
    def _element_constructor_(self, x):
        return self.element_class(self, x, f)
    def __eq__(self, other):
        if not isinstance(other, ForgetModule): return False
        return self.base_ring() == other.base_ring() and self.internal == other.internal
    def _repr_(self):
        return "(%s)-module structure forgotten from %s" % (repr(self.A), repr(self.internal))
    def __hash__(self):
        return hash(self.base_ring())

from sage.monoids.indexed_free_monoid import IndexedFreeAbelianMonoid
def monomials(poly_ring):
    return IndexedFreeAbelianMonoid(poly_ring.gens())

def monomial_basis(poly_ring):
    gens = poly_ring.gens()
    B = poly_ring.base_ring()
    C = CombinatorialFreeModule(B, monomials(poly_ring))
    return C

def M_to_R(R, m_elt):
    prod = R(1)
    for k,v in m_elt.dict().items():
        prod *= R(k)**v
    return prod

def exponents_to_M(R, monomial_exponents):
    M = monomials(R)
    prod = M.one()
    if not hasattr(type(monomial_exponents), '__iter__'):
        # Make it work for univariate
        monomial_exponents = [monomial_exponents]
    for i in range(len(monomial_exponents)):
        prod *= M.gen(R.gens()[i])**monomial_exponents[i]
    return prod

def R_to_C(R, f):
    C = monomial_basis(R)
    c = monomial_basis(R).basis()
    total = 0
    for k,v in f.dict().items():
        total += C.base_ring()(v)*c[exponents_to_M(R, k)]
    return total

def monomial_iso(poly_ring):
    C = monomial_basis(poly_ring)
    unphi = C.module_morphism(on_basis=lambda monom: M_to_R(poly_ring, monom),
                              codomain=poly_ring)
    phi = poly_ring.module_morphism(function=lambda x: R_to_C(poly_ring, x),
                                    codomain=C,
                                    category=Modules(poly_ring.base_ring()))
    return (phi, unphi)


class ForgottenElementWithBasis(ForgottenElement):
    def __init__(self, parent, poly_ring, x, f=None):
        self.poly_ring = poly_ring
        super().__init__(parent, x, f)
    def monomial_coefficients(self, copy=True):
        b_expansion = self.parent().up_one(self.x).monomial_coefficients(copy)
        return {(exps,b): coeff for b,c in b_expansion.items()
                for exps,coeff in R_to_C(self.poly_ring, c).monomial_coefficients(copy).items()}

# from sage.structure.indexed_generators import IndexedGenerators

class ForgetPolynomialModuleWithBasis(sage.modules.module.Module):
    Element = ForgottenElementWithBasis
    def __init__(self, Bmod, category=None, f=None):
        self.internal = Bmod
        self.f = f
        while isinstance(self.internal, ForgetPolynomialModuleWithBasis):
            g = self.internal.f # Must evaluate now, before changing self.parent
            if g is not None:
                if self.f is None:
                    self.f = g
                else:
                    self.f = lambda a: f(g(a))
            self.internal = self.internal.internal
        self.up_one = Bmod
        self.poly_ring = Bmod.base_ring()
        self.A = Bmod.base_ring().base_ring()
        self._indices = cartesian_product([monomials(self.poly_ring),
                                           self.up_one.basis().keys()])
        category = ModulesWithBasis(self.A).or_subcategory(category)
        super().__init__(self.A, category=category)
    def _element_constructor_(self, x):
        return self.element_class(self, self.poly_ring, x, self.f)
    def __eq__(self, other):
        if not isinstance(other, ForgetPolynomialModuleWithBasis): return False
        return self.base_ring() == other.base_ring() and self.up_one == other.up_one
    def __hash__(self):
        return hash(self.base_ring())
    def _repr_(self):
        return "(%s)-module structure with monomial basis forgotten from %s" % (repr(self.A), repr(self.internal))
    def monomial(self, tup):
        pidx = tup[0]
        bidx = tup[1]
        #return self(self.Bmod.monomial(bidx))
        p = M_to_R(self.poly_ring, pidx)
        b = self.up_one.monomial(bidx)
        # Need to use Bmod action specifically, the one that knows the action of self.poly_ring
        return p*b

from sage.categories.functor import Functor, ForgetfulFunctor_generic
# If A is a subring of B, produce a forgetful functor Modules(B) -> Modules(A)
# Can forget along an injection f
# Why do I have to code this
class ForgetToSubring(ForgetfulFunctor_generic):
    def __init__(self, A, B, f=None):
        self.A = A
        self.B = B
        self.f = f
        super().__init__(Modules(B), Modules(A))

    #Apply self to an object x of selfs domain.
    def _apply_functor(self, bmod):
        return ForgetModule(self.A, bmod, self.f)

class ForgetPolynomial(ForgetfulFunctor_generic):
    def __init__(self, poly_ring):
        self.poly_ring = poly_ring
        self.A = poly_ring.base_ring()
        super().__init__(ModulesWithBasis(self.poly_ring),
                         ModulesWithBasis(self.A),
                         )

    #Apply self to an object x of selfs domain.
    def _apply_functor(self, pmod):
        return ForgetPolynomialModuleWithBasis(pmod,
                                               f=self.poly_ring.coerce_map_from(self.A))

class CompositeFunctor(Functor):
    def __init__(self, FA, FB):
        self.FA = FA
        self.FB = FB
        super().__init__(FB.domain(), FA.codomain())

    def _coerce_domain(self, x):
        return self.FB._coerce_domain(x)

    def _apply_functor(self, x):
        return self.FA(self.FB(x))

    def _apply_functor_to_morphism(self, f):
        return self.FA(self.FB(f))

def ForgetNPolyLayers(R,n):
    if n <= 1:
        return ForgetPolynomial(R)
    else:
        return CompositeFunctor(ForgetNPolyLayers(R.base_ring(), n-1),
                                ForgetPolynomial(R))

def depolynomialate(x,n):
    return ForgetNPolyLayers(x.base_ring(), n)(x)

from sage.rings.polynomial.polydict import ETuple

# Break off a linear factor from an exponent
def etuple_factor(etup):
    if e.is_constant():
        return None
    else:
        ke = etup.sparse_iter()
        k,e = next(ke)
        first_var = ETuple({k:1}, int(len(etup)))
        return first_var, etup.esub(first_var)

def mfactor(monomial):
    if not hasattr(monomial, 'coefficients'):
        return 1, monomial
    if monomial.degree() == 0: # cannot be broken apart in this ring
        return mfactor(monomial.base_ring()(monomial.coefficients[0]))
    if hasattr(monomial, 'support'): # symmetric function
        supp = monomial.support()[0]
        return p([supp[0]]), monomial.coefficients()[0]*p(supp[1:])
    # Polynomial
    v,c = monomial.dict().items()[0]
    if isinstance(v, ETuple): #multivariate
        e1, e2 = etuple_factor(v)
        return monomial.parent().monomial(e1),c*monomial.parent().monomial(e2)
    # Univariate polynomial
    return monomial.parent().gen(), c*monomial.parent().gen()**(v-1)
