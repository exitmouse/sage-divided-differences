#!/usr/bin/env python
# coding: utf-8-unix
# -*- mode: python-mode; python-indent-offset: 4 -*-
import sage
from sage.structure.richcmp import richcmp
from sage.modules.module import Module
from sage.structure.element import ModuleElement

# Module structure on the morphisms is not implemented for general modules! Why?
from sage.categories.category_types import Category_over_base_ring

class HomModules(Category_over_base_ring):
    def __init__(self, base_ring):
        super().__init__(base_ring)
    def super_categories(self):
         return [sage.categories.modules.Modules.Homsets(self.base_ring()),
                 sage.categories.modules.Modules(self.base_ring())]
    class ElementMethods:
        def _lmul_(self, c):
            return self.domain.module_morphism(function = lambda g: c*self(g), codomain=self.codomain())
        def _add_(self, other):
            return self.domain.module_morphism(function = lambda g: other(g)+self(g), codomain=self.codomain())

class ModulesWithHomModules(Category_over_base_ring):
    def __init__(self, base_ring):
        super().__init__(base_ring)
    def super_categories(self):
        return [Modules(self.base_ring())]
    def Homsets(self):
        return HomModules(self.base_ring())

class ModulesWithBasisWithHomModules(Category_over_base_ring):
    def __init__(self, base_ring):
        super().__init__(base_ring)
    def super_categories(self):
        return [ModulesWithHomModules(self.base_ring()),
                ModulesWithBasis(self.base_ring())]
    def Homsets(self):
        return HomModules(self.base_ring())

class ForgottenModules(Category_over_base_ring):
    def __init__(self, base_ring):
        super().__init__(base_ring)

    def super_categories(self):
        return [ModulesWithHomModules(self.base_ring())]

    class ParentMethods:
        def internal(self):
            pass
        def _element_constructor_(self, x, f=None):
            return self.element_class(x, f)
        def __eq__(self, other):
            if not isinstance(other, self.__class__): return False
            return self.base_ring() == other.base_ring() and self.internal() == other.internal()
        def _repr_(self):
            return "(%s)-module structure forgotten from %s" % (repr(self.base_ring()), repr(self.internal()))
        def __hash__(self):
            return hash(self.base_ring())

    class ElementMethods:
        def unbox(self):
            pass
        def _lmul_(self, c):
            # override if self.parent().base_ring() is not a subring of self.parent().internal().base_ring()
            return self.parent()(c*self.unbox())
        def _add_(self, other):
            return self.parent()(self.unbox() + other.unbox())
        def _richcmp_(self, other, op):
            while isinstance(other, ForgottenModuleElement): # There should be a categorical way
                other = other.unbox()
            return richcmp(self.unbox(), other, op)
        def __hash__(self):
            return hash(self.unbox())
        def _repr_(self):
            return repr(self.unbox())

class ForgottenModuleElement(ModuleElement):
    def __init__(self, x, f=None):
        while isinstance(x, ForgottenModuleElement): # There should be a categorical way
            x = x.unbox()
        self.x = x
        self.f = f
        super().__init__(self)

    def unbox(self):
        return self.x
    def _lmul_(self, c):
        if self.f is None:
            return self.parent()(c*self.unbox())
        else:
            return self.parent()(self.f(c)*self.unbox())

class ForgottenModule(Module):
    Element = ForgottenModuleElement
    def __init__(self, base_ring, Bmod, f=None, category=None):
        self.internal = Bmod
        while isinstance(self.internal, ForgetModule):
            g = self.internal.f
            if g is not None:
                if self.f is None:
                    self.f = g
                else:
                    self.f = lambda a: f(g(a))
            self.internal = self.internal.internal
        self.f = f
        category = ForgottenModules(base_ring).or_subcategory(category)
        super().__init__(base_ring, category=category)
    def internal(self):
        return self.internal

class ForgottenModuleWithBasis(ForgottenModule):
    def __init__(self, head, tail, f=None, category=None):
        self.head = head
        self.tail = tail
        self._indices = cartesian_product([self.head.basis().keys(),
                                        self.tail.basis().keys()])
        base_ring = head.base_ring()
        category = ForgottenModulesWithBasis(base_ring).or_subcategory(category)
        super().__init__(base_ring, tail, f=f, category=category)
    def head(self):
        return self.head
    def tail(self):
        return self.tail

# Imagine we have
# A -> B -> C -> End(V)
# And we forget V until it is an A-module, step by step.
# The resulting ForgottenModule F has the following attributes:
# Bmod is V as a B-module.
# internal() is V as a C-module
# head() is an A-module isomorphic to B as an A-module, with coercions back and forth.
# tail() is V as a B-module
class ForgottenModulesWithBasis(Category_over_base_ring):
    Element = ForgottenModuleElement

    def __init__(self, base_ring):
        super().__init__(base_ring)

    def super_categories(self):
        return [ModulesWithBasisWithHomModules(self.base_ring()),
                ForgottenModules(self.base_ring())]

    class ElementMethods:
        def monomial_coefficients(self, copy=True):
            tail_expansion = self.parent().tail()(self.unbox()).monomial_coefficients(copy)
            return {(head_idx,tail_idx): coeff for tail_idx,c in tail_expansion.items()
                    for head_idx,coeff in self.parent().head()(c).monomial_coefficients(copy).items()}

    class ParentMethods:
        def tail():
            pass
        def head():
            pass
        def _element_constructor_(self, x):
            return self.element_class(x, self.f)
        def __eq__(self, other):
            if not isinstance(other, self.__class__): return False
            return self.head() == other.head() and self.tail() == other.tail()
        def __hash__(self):
            return hash(self.base_ring())
        def _repr_(self):
            return "(%s)-module structure with monomial basis forgotten from %s" % (repr(self.base_ring()), repr(self.internal()))
        def monomial(self, tup):
            pidx = tup[0]
            bidx = tup[1]
            #return self(self.Bmod.monomial(bidx))
            p = self.head().monomial(pidx) # M_to_R(self.poly_ring, pidx)
            b = self.tail().monomial(bidx)
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
        super().__init__(Modules(B), ForgottenModules(A))

    #Apply self to an object x of selfs domain.
    def _apply_functor(self, bmod):
        return ForgottenModule(self.A, bmod, self.f)

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
    if not C.has_coerce_map_from(poly_ring):
        phi.register_as_coercion()
    if not poly_ring.has_coerce_map_from(C):
        unphi.register_as_coercion()
    return C

class ForgetPolynomial(ForgetfulFunctor_generic):
    def __init__(self, poly_ring):
        self.poly_ring = poly_ring
        self.head = monomial_iso(poly_ring)
        super().__init__(ModulesWithBasis(self.poly_ring),
                         ForgottenModulesWithBasis(self.head.base_ring()))

    #Apply self to an object x of selfs domain.
    def _apply_functor(self, pmod):
        return ForgottenModuleWithBasis(self.head, pmod, f=self.poly_ring.coerce_map_from(self.head.base_ring()))

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
