r"""
Implements basic classes for modules over rings with an additional
 action by a group.


 AUTHOR: Fredrik Stromberg
 
"""

#*****************************************************************************
#       Copyright (C) 2013 Fredrik Stromberg <fredrik314@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************


from sage.modules.free_module import FreeModule_generic_pid,FreeModule_ambient_pid,FreeModule_submodule_with_basis_pid,FreeModule_generic,FreeModule_ambient,FreeModule_submodule_pid,is_FreeModule
from sage.all import ZZ,Sequence,copy
#from sage.structure.element import ModuleElement
from sage.modules.free_module_element import FreeModuleElement
from sage.misc.cachefunc import cached_method
from sage.rings.principal_ideal_domain import is_PrincipalIdealDomain
from sage.categories.principal_ideal_domains import PrincipalIdealDomains

class ModuleWithGroupAction_generic(FreeModule_generic):
    r"""
    Generic Weil representation module. This is a free ZZ-module with an SL_{2}(ZZ) or MP_{2}(ZZ) action.
    """
    def __init__(self,base_ring,rank,degree,group,**kwds):
        r"""
        Initialize a Weil representation module of rank n over the ring R.
        EXAMPLES::

            sage: from sage.all import SL2Z)
            sage: M=ModuleWithGroupAction_generic(ZZ,3,3,SL2Z); M
            Generic Module of rank 3 and degree 3 with action by Modular Group SL(2,Z)
            
        """
        self._group = group
        if not hasattr(self,'_element_class') or self._element_class==None:
            self._element_class = ModuleWithGroupAction_generic_element
            #       super(ModuleWithGroupAction_generic,self).__init__(base_ring,rank,degree,sparse=False)
        FreeModule_generic.__init__(self,base_ring,rank,degree)
        # names for the basis vectors
        name = kwds.get('ambient_names','e')

        if isinstance(name,(list,tuple)) and len(name)==rank:
            self._ambient_basis_names = name
        else:
            self._ambient_basis_names=['{0}{1}'.format(name,j) for j in range(degree)]
        
    def __repr__(self):
        r"""
        Representing self.

        EXAMPLES::

        
            sage: from sage.all import SL2Z
            sage: M=ModuleWithGroupAction_generic(ZZ,3,3,SL2Z); M
            Generic Module of rank 3 and degree 3 with action by Modular Group SL(2,Z)
        """
        return "Generic Module of rank {0} and degree {1} with action by {2}".format(self.rank(),self.degree(),self.group())

    def group(self):
        r"""
        Return the group which is acting on self

        EXAMPLES::

        
            sage: from sage.all import SL2Z
            sage: M=ModuleWithGroupAction_generic(ZZ,3,3,SL2Z)
            sage: M.group()
            Modular Group SL(2,Z)

        """
        return self._group

    def invariants(self):
        r"""
        Return the space of invariants of self under the SL(2,Z) action.
        EXAMPLES::

        
            sage: from sage.all import SL2Z
            sage: M=ModuleWithGroupAction_generic(ZZ,3,3,SL2Z)
            sage: M.invariants()
            Traceback (most recent call last)
            ...
            NotImplementedError:
        
        """
        raise NotImplementedError

    def group_action_on_basis(self,g):
        r"""
        Return the matrix given by the action of an element g in self.group()
        EXAMPLES::

        
            sage: from sage.all import SL2Z
            sage: M=ModuleWithGroupAction_generic(ZZ,3,3,SL2Z)
            sage: M.group_action_on_basis(SL2Z.gens()[0])
            Traceback (most recent call last)
            ...
            NotImplementedError:

        """
        raise NotImplementedError


class ModuleWithGroupAction_generic_pid(ModuleWithGroupAction_generic, FreeModule_generic_pid):

    def __init__(self,base_ring,rank,degree,group,**kwds):
        r"""
        Initialize a Weil representation module of rank n over the ring R.
        EXAMPLES::

            sage: from sage.all import SL2Z)
            sage: M=ModuleWithGroupAction_generic(ZZ,3,3,SL2Z); M
            Generic Module of rank 3 and degree 3 with action by Modular Group SL(2,Z)
            
        """
        self._group = group
        if not hasattr(self,'_element_class') or self._element_class==None:
            self._element_class = ModuleWithGroupAction_generic_element
        if not hasattr(self,'_submodule_class') or self._submodule_class==None:
            self._submodule_class = ModuleWithGroupAction_submodule_pid
        #super(ModuleWithGroupAction_generic_pid,self).__init__(base_ring,rank,degree,group,**kwds)
        ModuleWithGroupAction_generic.__init__(self,base_ring,rank,degree,group,**kwds)
        FreeModule_generic.__init__(self,base_ring,rank,degree)


    def span(self, gens, base_ring=None, check=True, already_echelonized=False):
        """
        Return the K-span of the given list of gens, where K is the
        base field of self or the user-specified base_ring.  Note that
        this span is a subspace of the ambient vector space, but need
        not be a subspace of self.
        
        INPUT:
        
        
        -  ``gens`` - list of vectors
        
        -  ``check`` - bool (default: True): whether or not to
           coerce entries of gens into base field
        
        -  ``already_echelonized`` - bool (default: False):
           set this if you know the gens are already in echelon form
        
        
        EXAMPLES::
        
            sage: V = VectorSpace(GF(7), 3)
            sage: W = V.subspace([[2,3,4]]); W
            Vector space of degree 3 and dimension 1 over Finite Field of size 7
            Basis matrix:
            [1 5 2]
            sage: W.span([[1,1,1]])
            Vector space of degree 3 and dimension 1 over Finite Field of size 7
            Basis matrix:
            [1 1 1]
        
        TESTS::
        
            sage: V = FreeModule(RDF,3)
            sage: W = V.submodule([V.gen(0)])
            sage: W.span([V.gen(1)], base_ring=GF(7))
            Vector space of degree 3 and dimension 1 over Finite Field of size 7
            Basis matrix:
            [0 1 0]
            sage: v = V((1, pi, e)); v
            (1.0, 3.14159265359, 2.71828182846)
            sage: W.span([v], base_ring=GF(7))
            Traceback (most recent call last):
            ...
            ValueError: Argument gens (= [(1.0, 3.14159265359, 2.71828182846)]) is not compatible with base_ring (= Finite Field of size 7).
            sage: W = V.submodule([v])
            sage: W.span([V.gen(2)], base_ring=GF(7))
            Vector space of degree 3 and dimension 1 over Finite Field of size 7
            Basis matrix:
            [0 0 1]
        """
        if is_FreeModule(gens):
            gens = gens.gens()
        if (base_ring is None or base_ring == self.base_ring()) and self._submodule_class<>None:
            ambient = self.ambient_module()
            S = self._submodule_class(ambient, gens=gens, check=check, already_echelonized=already_echelonized)
            return S
            #return ModuleWithGroupAction_submodule_pid(
            #    self.ambient_module(), gens=gens, check=check, already_echelonized=already_echelonized)
        else:
            try:
                M = self.ambient_module().change_ring(base_ring)
            except TypeError:
                raise ValueError, \
                    "Argument base_ring (= %s) is not compatible with the base field (= %s)." % (base_ring, self.base_field() )
            try: 
                return M.span(gens)
            except TypeError:
                raise ValueError, \
                    "Argument gens (= %s) is not compatible with base_ring (= %s)." % (gens, base_ring)


    
#    def submodule(self,gens):
#        r"""
#        Return the submodule of self spanned by gens.
#        """
        

class ModuleWithGroupAction_ambient(ModuleWithGroupAction_generic,FreeModule_ambient):
    r"""
    Ambient module with group action.
    """
    def __init__(self,base_ring,rank,degree,group):
        r"""
        Initialize an ambient module with group action.

        EXAMPLES::

        
            sage: from sage.all import SL2Z
            sage: M=ModuleWithGroupAction_ambient(ZZ,3,3,SL2Z)
            sage: M.is_ambient()
            True
        """
        super(ModuleWithGroupAction_ambient,self).__init__(base_ring,rank,degree,group)

    def __repr__(self):
        r"""
        Representing self.

        EXAMPLES::

        
            sage: from sage.all import SL2Z
            sage: M=ModuleWithGroupAction_ambient(ZZ,3,3,SL2Z);M
            Ambient module of rank 3 and degree 3 with action by Modular Group SL(2,Z)

        """
        return "Ambient module of rank {0} and degree {1} with action by {2}".format(self.rank(),self.degree(),self.group())
    
    

class ModuleWithGroupAction_ambient_pid(ModuleWithGroupAction_ambient,FreeModule_ambient_pid):
    r"""
    Ambient module over a PID with group action.
    """
    def __init__(self,base_ring,rank,degree,group):
        r"""
        Initialize an ambient module with group action.

        EXAMPLES::

        
            sage: from sage.all import SL2Z
            sage: M=ModuleWithGroupAction_ambient(ZZ,3,3,SL2Z)
            sage: M.is_ambient()
            True
        """
        assert is_PrincipalIdealDomain(base_ring)
        super(ModuleWithGroupAction_ambient_pid,self).__init__(base_ring,rank,degree,group)

    def __repr__(self):
        r"""
        Representing self.

        EXAMPLES::

        
            sage: from sage.all import SL2Z
            sage: M=ModuleWithGroupAction_ambient(ZZ,3,3,SL2Z);M
            Ambient module of rank 3 and degree 3 with action by Modular Group SL(2,Z)

        """
        return "Ambient module of rank {0} and degree {1} with action by {2}".format(self.rank(),self.degree(),self.group())
    
    


class ModuleWithGroupAction_submodule_pid(ModuleWithGroupAction_generic,FreeModule_submodule_with_basis_pid):
    r"""
    A submodule of a Weil module.
    """

    def __init__(self,ambient,gens,check=True,echelonize=False,echelonized_basis=None,already_echelonized=False):
        r"""
        Initialize a generic submodule of a Weil module.

        EXAMPLES::

        
            sage: from sage.all import SL2Z
            sage: M=ModuleWithGroupAction_ambient_pid(ZZ,3,3,SL2Z)
            sage: S=ModuleWithGroupAction_submodule_pid(M,M.gens()[0]);S
            Submodule of Ambient module of rank 3 and degree 3 with action by Modular Group SL(2,Z)
        
        
        """
        if not isinstance(gens,(list,tuple)):
            gens = [gens]
        if not isinstance(Sequence(gens).universe(),type(ambient)) or not isinstance(ambient,ModuleWithGroupAction_generic):
            raise ValueError("Need gens to consist of elements of ambient!")
        
        self._ambient_module = ambient
        rank = len(gens)
        ### Note: It is very slow to echelonize over e.g. cyclotomic fields.
        ### So we use the gens as basis
        if echelonized_basis == False: #Check
            echelonized_basis = is_in_echelon_form(basis)
        FreeModule_submodule_with_basis_pid.__init__(self,ambient,gens,check=check,echelonize=echelonize,echelonized_basis=echelonized_basis,already_echelonized=already_echelonized)
        ModuleWithGroupAction_generic.__init__(self,ambient.base_ring(),rank,ambient.degree(),ambient.group())
#        super(ModuleWithGroupAction_submodule_pid,self).__init__(ambient.base_ring(),rank,ambient.degree(),ambient.group())

    def __repr__(self):
        r"""
        Represent self.

        EXAMPLES::

        
            sage: from sage.all import SL2Z
            sage: M=ModuleWithGroupAction_ambient_pid(ZZ,3,3,SL2Z)
            sage: S=ModuleWithGroupAction_submodule_pid(M,M.gens()[0]);S
            Submodule of Ambient module of rank 3 and degree 3 with action by Modular Group SL(2,Z)
            
        """
        return "Submodule of {0}".format(self.ambient_module())
        
    def ambient_module(self):
        r"""
        Return the ambient module of self.

        EXAMPLES::

        
            sage: from sage.all import SL2Z
            sage: M=ModuleWithGroupAction_ambient_pid(ZZ,3,3,SL2Z)
            sage: S=ModuleWithGroupAction_submodule_pid(M,M.gens()[0]);S
            Ambient module of rank 3 and degree 3 with action by Modular Group SL(2,Z)

        """
        return self._ambient_module

class ModuleWithGroupAction_invariant_submodule_pid(ModuleWithGroupAction_submodule_pid):
    r"""
    A submodule of SL2(Z) invariants of a Weil module
    """
    def __init__(self,ambient,gens):
        r"""
        Initialize a submodule of SL2(Z) invariants of a Weil module

        EXAMPLES::


        
        """
        super(ModuleWithGroupAction_invariant_submodule_pid,self).__init__(ambient,gens)

        
class ModuleWithGroupAction_generic_element(FreeModuleElement):
    r"""
    Elements of a module with group action.
    """

    def __init__(self,parent,coords,name=None,rep='',is_immutable=False,**kwds):        
        r"""
        Initialize an element of a Weil module.
        """
        ## make sure coords 
        #print "parent=",parent
        #print "coords=",coords
        self._degree = parent.degree()
        if not isinstance(coords,(tuple,list)):
            if coords<>0:
                raise ValueError,"Can only have initialize with 0 as scalar!"
            #print "setting coords to 0!"
            self._coords = [0 for i in range(parent.degree())]
        elif isinstance(coords,tuple):
            self._coords = list(coords)
        else:
            self._coords = coords
        self._is_immutable = is_immutable    
        self._name = name
        self._rep = rep
        if parent._names<>'':
            self._ambient_basis_names=parent._ambient_basis_names
        else:
            self._ambient_basis_names=['e{0}'.format(j) for j in range(self.degree())]
        super(ModuleWithGroupAction_generic_element,self).__init__(parent)


    def __copy__(self):
        r"""
        Return a mutable copy of self.
        """
        return self.__class__(self.parent(),copy(self._coords),self._name,rep=self._rep,is_immutable = False)
    
    def __repr__(self):
        r"""
        Represent self.
        """
        
        if self._rep=='coord':
            return str(self.coords())
        if self._rep=='full':
            return "An element of a generic Weil module. Coords:={0}".format(self.coords())
        if self.is_zero():
            return '0'
        s=""
        j=0
        for i in range(len(self._coords)):
            x = self._coords[i]
            if x==0:
                continue
            if x==1:
                if i>0 and j>0:
                    s+="+"
                s+="{0}".format(self._ambient_basis_names[i])
            elif x==-1:
                s+="-{0}".format(self._ambient_basis_names[i])
            else:
                if not x<0 and i>0 and j>0 and str(x)[0]<>'-':
                    s+="+"
                s+="{0}*{1}".format(x,self._ambient_basis_names[i])
            j+=1

        return s

    def degree(self):

        return self._degree
    
    def set_rep(self,rep):
        r"""
        Set the type of string representation of self.
        """
        self._rep = rep

    def set_immutable(self,x=None):
        r"""
        
        """
        if x in [True,False]:
            self._is_immutable = x
        else:
            self._is_immutable = not self._is_immutable

    def is_zero(self):
        for x in self._coords:
            if x<>0:
                return False
        return True
    
    def __setitem__(self,key,item):
        if self._is_immutable:
            raise ValueError," Element is immutable"
        
        #print "set {0} to {1}".format(key,item)
        self._coords[key]=item
    
    def __getitem__(self,key):
        r"""
        
        """
        return self._coords[key]
        
    def coords(self):
        r"""
        Return the coordinates of self in terms of the basis of self.parent()
        """
        return self._coords
    
    def __call__(self,x):
        r"""
        Act by self on `x`
        """
        raise NotImplementedError("Needs to be overriden by subclasses")
        
    def group_action(self,g):
        r"""
        
        """
        raise NotImplementedError

    def _rmul_(self,g):
        r"""
        Multiply self by g from right, i.e. self*g
        """
        if g in self.base_ring():
            new_coords = [self._coords[i]*g for i in range(self._degree)]
            return self.__class__(self.parent(),new_coords,self._name,self._rep,self._is_immutable)
        else:
            raise ValueError,"Can not multiply {0} by {1}".format(self,g)
        
    def _lmul_(self,g):
        r"""
        Multiply self by g from left, i.e. g*self
        """
        if g in self.base_ring():
            new_coords = [g*self._coords[i] for i in range(self._degree)]
            return self.__class__(self.parent(),new_coords,self._name,self._rep,self._is_immutable)
        elif g in self.group():
            return self.group_action(g)
        else:
            raise ValueError,"Can not multiply {0} by {1}".format(self,g)


    def _acted_upon_(self,x,self_on_left=False):
        r"""

        """
        if x in self.base_ring():
            return self._lmul_(x)
        elif x in self.parent().group() and self_on_left==False:
            return self.group_action(x)
        else:
            raise ValueError,"Can not act on  {0} by {1}".format(self,x)
        
        
    def __mul__(self,g):
        r"""
        Multiply self by g
        """
        if g in self.base_ring():
            return self._lmul_(g)
        elif g in self.parent().group():
            return self.group_action(g)
        else:
            raise ValueError,"Can not multiply {0} by {1}".format(self,g)

    def __add__(self,other):
        r"""
        Multiply self by other
        """
        if isinstance(other,ModuleWithGroupAction_generic_element):
            new_coords=[ self._coords[i]+other._coords[i] for i in  range(self.degree())]
            return self.__class__(self.parent(),new_coords,self._name,rep=self._rep,is_immutable = self._is_immutable)
        else:
            raise ValueError,"Can not add {0} to {1}".format(self,other)

def is_in_echelon_form(basis):
    r"""
    Check whether the vectors in basis are in echelon form.
    (basis vectors are supposed to be rows)
    
    """
    if not isinstance(basis,(list,tuple)):
        raise ValueError,"Need a list of tuple of vectors"
    m=basis[0].degree(); n=len(basis)
    
    for i in range(m):
        for j in range(i+1,n):
            if basis[i]._coords[j]<>0:
                return False
    return True

def is_in_echelon_form_matrix(basis):
    r"""
    Check whether the vectors in basis are in echelon form.
    
    """
    m=basis.ncols(); n=basis.nrows()
    
    for i in range(m):
        for j in range(i+1,n):
            if basis[i][j]<>0:
                return False
    return True
