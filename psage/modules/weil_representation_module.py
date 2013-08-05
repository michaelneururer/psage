r"""

Classes for Weil representations associated with
 - Finite quadratic modules (eq. with even lattices)
 - Lattices (both odd and even)

Class structure:

WeilModule_generic(ModuleWithGroupAction_generic)
        self._element_class = WeilModule_element_generic
    WeilModule_generic_pid(WeilModule_generic,ModuleWithGroupAction_generic_pid)
        self._submodule_class = WeilModule_submodule_with_basis_pid
        WeilModule_ambient_pid(WeilModule_generic_pid,FreeModule_ambient_pid)

    WeilModule_submodule_with_basis_pid(WeilModule_generic,FreeModule_submodule_with_basis_pid):
        WeilModule_invariant_submodule(WeilModule_submodule_with_basis_pid):

   WeilModule_generic_fqm(WeilModule_generic_pid):
        _element_class = WeilModule_element_generic
        _submodule_class = WeilModule_submodule_fqm
        WeilModule_ambient_fqm(WeilModule_generic_fqm,WeilModule_ambient_pid)
       WeilModule_submodule_fqm(WeilModule_submodule_with_basis_pid,WeilModule_generic_fqm)
   WeilModule_ambient_lattice(WeilModule_ambient_pid):

WeilModuleElement_generic(ModuleWithGroupAction_generic_element)
    WeilModuleElement_fqm

 
"""

from sage.modules.free_module import FreeModule_generic_pid,FreeModule_ambient_pid,FreeModule_submodule_with_basis_pid,FreeModule_generic,is_FreeModule

from sage.all import ZZ,Gamma0,CyclotomicField,lcm,SL2Z,FormalSum,Matrix
from sage.structure.element import ModuleElement
from sage.misc.cachefunc import cached_method
from psage.modules.module_with_group_action import *
from psage.modules.finite_quadratic_module import FiniteQuadraticModule_ambient
#import actions_by_sl2z 
#from actions_by_sl2z import ActionOnWeilRepBySL2Z
from actions_by_sl2z import ActionOnWeilRepBySL2Z_fqm,ActionOnWeilRepBySL2Z_lattice,ActionOnWeilRepBySL2Z_generic
from sage.structure.element import Matrix as Matrix_Type
from weil_module_alg import *

class WeilModule_generic(ModuleWithGroupAction_generic):
    r"""
    Generic Weil representation module. This is a free ZZ-module with an SL_{2}(ZZ) or MP_{2}(ZZ) action.
    """
    def __init__(self,base_ring,rank,degree,group,lattice=None,finite_quadratic_module=None,minimal_base_field=False,**kwds):
        r"""
        Initialize a Weil representation module of rank n over the ring R.

        INPUT:

        - `base_ring` -- Ring
        - `rank` -- Integer
        - `degree` -- Integer
        - `group` -- Group
        - `lattice` -- Lattice
        - `finite_quadratic_module` -- FiniteQuadraticModule
        - `minimal_base_field` -- bool Set to true if you want to work with cyclotomic field of order 2*level (gives uglier formulas and is slower than working in order lcm(8,level) )

        EXAMPLES::
        
            sage: W=WeilModule_generic(ZZ,3,3,SL2Z)
            Generic Weil module of rank 3 and degree 3 with action of Modular Group SL(2,Z)
            

        """
        self._lattice = lattice
        self._fqm = finite_quadratic_module
        super(WeilModule_generic,self).__init__(base_ring,rank,degree,group,**kwds)
        self._element_class = WeilModuleElement_generic
        self._act_by = ActionOnWeilRepBySL2Z(self,minimal_base_field=minimal_base_field)
        self._inner_product_matrix=None
       
    def __repr__(self):
        r"""
        Representing self.
        """
        return "Generic Weil module of rank {0} and degree {1} with action of {2}".format(self.rank(),self.degree(),self.group())


    ## The methods we want to have
    def lattice(self):
        r"""
        Return the lattice associated with self (if it exists)
        """
        return self._lattice
#        raise NotImplementedError("Should be overriden by subclasses")

    def finite_quadratic_module(self):
        r"""
        Return the finite quadratic module associated with self (if it exists)
        """
        return self._fqm

    def Bi(self,i,j):
        r"""
        Return the bilinear form on the element i and j of th associated 
        """
        raise NotImplementedError

    def Qi(self,i,j):
        r"""
        """
        raise NotImplementedError


    
    def invariants(self):
        r"""
        Return the space of invariants of self under the SL(2,Z) action.
        """
        raise NotImplementedError


    def sl2_action_on_basis(self,A):
        r"""
        Return the matrix given by the action of an element in SL(2,O) on self.basis()
        """
        return self._act_by.matrix(A)

class WeilModule_generic_pid(WeilModule_generic,ModuleWithGroupAction_generic_pid):
    r"""
    A generic WeilModule over a PID.
    """
    def __init__(self,base_ring,rank,degree,group,lattice=None,finite_quadratic_module=None,**kwds):
        r"""
        Init a generic WeilModule over a PID.
        """
        super(WeilModule_generic_pid,self).__init__(base_ring,rank,degree,group,lattice=lattice,finite_quadratic_module=finite_quadratic_module,**kwds)
        self._submodule_class = WeilModule_submodule_with_basis_pid

        
class WeilModule_ambient_pid(WeilModule_generic_pid,FreeModule_ambient_pid):
    r"""
    Weil representation module. This is a free ZZ-module with an SL_{2}(ZZ) or MP_{2}(ZZ) action.
    """
    def __init__(self,base_ring,rank,degree,group,lattice=None,finite_quadratic_module=None,**kwds):
        r"""
        Initialize a Weil representation module of rank n over the ring R.
        """
        super(WeilModule_ambient_pid,self).__init__(base_ring,rank,degree,group,lattice,finite_quadratic_module,**kwds)
      

    def __repr__(self):
        r"""
        Representing self.
        """
        s = "Ambient Weil module of rank {0} and degree {1} on the group {2}".format(self.rank(),self.degree(),self.group())
        if self.lattice()<>None:
            s+=" and associated with {0}".format(self._fqm)
        elif self._fqm<>None:
            s+=" and associated with {0}".format(self._fqm)
        return s
    
class WeilModule_submodule_with_basis_pid(WeilModule_generic,FreeModule_submodule_with_basis_pid):
    r"""
    A submodule of a Weil module.
    """
    def __init__(self,ambient,gens,check=True,echelonize=False,echelonized_basis=False,already_echelonized=False):
        r"""
        Initialize a generic submodule of a Weil module.
        """
        print "gens=",gens,type(gens)
        assert isinstance(Sequence(gens).universe(),WeilModule_generic)
        self._ambient_module = ambient
        rank = len(gens)
        FreeModule_submodule_with_basis_pid.__init__(self,ambient,gens,check=check,echelonize=echelonize,echelonized_basis=echelonized_basis,already_echelonized=already_echelonized)
        WeilModule_generic.__init__(self,ambient.base_ring(),rank,ambient.degree(),ambient.group)


    def __repr__(self):
        r"""
        Represent self.
        """
        s="A submodule of rank {0} an ambient WeilModule of rank {1} and degree {2}".format(self.rank(),self._ambient_module.rank(),self.degree())
        return s
        #super(WeilModule_submodule_with_basis_pid,self).__init__(ambient.base_ring(),rank,ambient.degree())

        
    def ambient_module(self):
        r"""
        Return the ambient module of self.
        """
        return self._ambient_module

class WeilModuleInvariants_generic(WeilModule_submodule_with_basis_pid):
    r"""
    A submodule of SL2(Z) invariants of a Weil module
    """
    def __init__(self):
        r"""
        Initialize a submodule of SL2(Z) invariants of a Weil module
        """
        pass

    
def WeilModule_invariant_class(WeilModuleElement_generic):
    r"""
    Invarants of a Weil module. 
    """

    def __init__(self,parent,function=None):        
        r"""
        Initialize an invariant element of a Weil module.
        """
        pass


    def action_of_sl2z(self,A):
        r"""
        Since self is invariant this always return the
        identity map.
        """
        return 1


class WeilModule_generic_fqm(WeilModule_generic_pid):
    r"""
    Implements Weil representations associated with finite quadratic modules.
    """
    def __init__(self,F,**kwds):
        if not isinstance(F,FiniteQuadraticModule_ambient):
            raise ValueError,"Need a finite quadratic module as input!"
        if F.base_ring()<>ZZ:
            raise NotImplementedError,"Only implemented for quaqdratic moduels over ZZ"
        # Lazy base_ring. We can do better....
        
        if kwds.get('minimal_base_field',False):
            base_ring = CyclotomicField(lcm(2,F.level()))
        else:
            base_ring = CyclotomicField(lcm(8,F.level()))
        rank = F.order()
        degree = rank
        group = SL2Z
        super(WeilModule_generic_fqm,self).__init__(base_ring,rank,degree,group,finite_quadratic_module=F,**kwds)
        self._element_class = WeilModuleElement_fqm
        self._submodule_class = WeilModule_submodule_fqm
        ### Some special paraeters we need to initialize
        self._level = F.level()
        self._fqm_elts = []
        if kwds.get('can_coords',False)==True:
            self._can_coords = True
            self._gen_orders = map(order,F.gens())
        else:
            self._can_coords = False
            self._gen_orders = F.elementary_divisors()

    def fqm_elements(self):
        r"""
        Return a list of elements in the associated finite quadratic module associated where the elements (in this order) correspond to the basis vectors of the Weil module.
        Note: The order depends on whether 'canonical' or 'fundamental' generators are used for the finite quadratic module.
        
        """
        if self._fqm_elts == []:
            for i in range(self._fqm.order()):
                self._fqm_elts.append(self.elt(i))
        return self._fqm_elts


    def elt(self,i):
        r"""
        Return the i-th element of the associated finite quadratic module.
        """
        return self._elt(i)
    
    @cached_method
    def _elt(self,i):
        r"""
        Return the i-th element of the associated finite quadratic module.
        """
        return self._fqm(cython_elt(i,self._gen_orders),can_coords=self._can_coords)

    @cached_method    
    def Bi(self,i,j):
        r"""

        """
        return self._fqm.B(self._elt(i),self._elt(j))
    
    @cached_method
    def Qi(self,i):
        r"""
        """
        return self._fqm.Q(self._elt(i))

    @cached_method
    def _neg_index(self,ii):
        return cython_neg_index(ii,self._gen_orders)

    @cached_method
    def _minus_element(self,ii):
        return self._neg_index(ii)
    # Setup the functions for computing the Weil representation

    def _el_index(self,c):        
        if not isinstance(c,(list,Vector_integer_dense)):
            raise ValueError,"Need element of list form! Got c={0} of type={1}".format(c,type(c))
        if not len(c)==len(self._gen_orders):
            raise ValueError,"Need element of list of the same length as orders={0}! Got c={1}".format(self._gen_orders,c)
        return cython_el_index(c,self._gen_orders)


    def odd_submodule(self,**kwds):
        r"""
        Return the submodule of self spanned by
        e_{gamma}  - e_{-gamma} for gamma in self._fqm
        Note: The basis we obtain is in echelon form.
        """
        gens = self._symmetrized_submodule_gens(-1)
        return WeilModule_submodule_fqm(self,gens,already_echelonized=True,**kwds)
    
    def even_submodule(self,**kwds):
        r"""
        Return the submodule of self spanned by
        e_{gamma}  - e_{-gamma} for gamma in self._fqm
   
        """
        gens = self._symmetrized_submodule_gens(1)
        return WeilModule_submodule_fqm(self,gens,already_echelonized=True,**kwds)
        
    def _symmetrized_submodule_gens(self,sign=1):
        r"""
        Return the maximal set of independent vectors
        of the form e_{gamma}  + sign* e_{-gamma} for gamma in self._fqm
   
        """
        basis = range(self.rank())
        gens = []
        for i in range(self.rank()):
            if i not in basis:
                continue
            i_neg = self._neg_index(i)
            if i==i_neg and sign==-1:
                continue
            basis.remove(i_neg)
            gens.append(self.basis()[i]+sign*self.basis()[i_neg])
        return gens

        
class WeilModule_ambient_fqm(WeilModule_generic_fqm,WeilModule_ambient_pid):
    r"""
    An ambient WeilModule defined by a finite quadratic module.
    """
    def __init__(self,F,**kwds):
        r"""
        Init an ambient WeilModule defined by a finite quadratic module.
        """
        super(WeilModule_ambient_fqm,self).__init__(F,**kwds)
        
        
class WeilModule_submodule_fqm(WeilModule_submodule_with_basis_pid,WeilModule_generic_fqm):
    r"""
    A submodule of a WeilModule defined by a finite quadratic module.   
    """

    def __init__(self,ambient,gens,check=True,echelonize=False,echelonized_basis=None,already_echelonized=False, **kwds):
        r"""
        Initalize a submodule of a WeilModule defined by a finite quadratic module.
        """
        WeilModule_generic_fqm.__init__(self,ambient.finite_quadratic_module(),**kwds)
        WeilModule_submodule_with_basis_pid.__init__(self,ambient,gens,check=check,echelonize=echelonize,echelonized_basis=echelonized_basis,already_echelonized=already_echelonized,**kwds)


    
class WeilModule_ambient_lattice(WeilModule_ambient_pid):
    r"""
    Implements the set W(L) for a lattice L.
    Here W(L) consitst of lambda:L^{bullet) ---> CC
    s.t. lambda(r+x)=e(beta(x))*lambda(r), for all r in L^bullet
    and x in L.


    """
    def __init__(self,L,f):
        self._function = f
        group = SL2Z
        rank = L.rank()
        base_ring = CyclotomicField(lcm(L.level(),8))
        super(WeilRepresentation_ambient_lattice,self).__init__(base_ring,rank,rank,group,lattice=L)


###
### Element classes
###
class WeilModuleElement_generic(ModuleWithGroupActionElement_generic):
    r"""
    Elements of a Weil module
    """

    def __init__(self,parent,coords,coerce=False,copy=False,name=None,rep='',is_immutable=False,function=None):        
        r"""
        Initialize an element of a Weil module.
        """
        super(WeilModuleElement_generic,self).__init__(parent,coords,coerce=coerce,copy=copy,name=name,rep=rep,is_immutable=is_immutable)

    def __repr__(self):
        r"""
        Represent self.
        """
        if self._name<>None:
            return str(self._name)
        if self._rep<>'':
            return "An element of a generic Weil module. Coords:={0}".format(self.coords())
        else:
            return super(WeilModuleElement_generic,self).__repr__()
        
    def coords(self):
        r"""
        Return the coordinates of self in terms of the basis of self.parent()
        """
        return self._coords
    
    @cached_method 
    def __call__(self,x):
        r"""
        Act by self on `x` in `L^{\bullet}`
        """
        assert x in self.parent().lattice().bullet_elements()
        return self._function(x)


    def group_action(self,A):
        r"""
        Action of the element A in self.group() on self.
        
        """
        raise NotImplementedError("Should be implemented in subclasses!")

    
class WeilModuleElement_fqm(WeilModuleElement_generic):
    r"""
    Elements of a Weil module
    """

    def __init__(self,parent,coords,coerce=False,copy=False,name=None,rep='',is_immutable=False,function=None):        
        r"""
        Initialize an element of a Weil module.
        """
        self._coords = coords
        super(WeilModuleElement_fqm,self).__init__(parent,coords,coerce=coerce,copy=copy,name=name,rep=rep,is_immutable=is_immutable)
        assert isinstance(parent,WeilModule_generic_fqm)


    def __repr__(self):
        r"""
        Represent self
        """
        if self._rep=='fqm':
            return str(self.as_fqm())
        else:
            return super(WeilModuleElement_fqm,self).__repr__()
            
    def as_fqm(self):
        r"""
        Return self as a formal sum of elements of a finite quadratic module.
        """
        res = []
        for i in range(self._degree):
            res.append((self._coords[i],self.parent().elt(i)))
        return FormalSum(res)
        
        
    def group_action(self,A):
        r"""
        Action of the element A in self.group() on self.
        
        """
        return self.parent()._act_by.action_by_sl2z_on_element(A,self)


    


        
        

        
###
### Access methods
###
        

def WeilRepresentation(L,**kwds):
    if isinstance(L,FiniteQuadraticModule_ambient):
        #group = Gamma0(1)
        #rank = L.order()
        #base_ring = CyclotomicField(lcm(L.level(),8))
        #return WeilModule_ambient_pid(base_ring,rank,rank,group,finite_quadratic_module=L)
        return WeilModule_ambient_fqm(L,**kwds)
    elif isinstance(L,Matrix_Type):
        if matrix.base_field()==QQ:
            group = Gamma0(1)
        else:
            raise NotImplementedError,"We haven't implemnted Weil representatins over other fields than QQ yet"
        level = lcm(lcm(L.elementary_divisors()),8)
        base_ring = CyclotomicField(lcm(L.level(),8))
        rank = L.nrows()
        return WeilModule_ambient_pid(base_ring,rank,rank,group,lattice=L)
    else:
        raise ValueError,"Can not create Weil representation from {0}".format(L)
        
def WeilRepresentationElement(W,coords=None,function=None):
    if coords == None and function == None:
        raise ValueError,"Can not construct an element without coordinates or a function"
    if not coordinates:
        coords = []
        for x in W.basis():
            j = function(x)
            coords.append( function(x) )
    if W.finite_quadratic_module()<>None:
        return WeilModuleElement_fqm(W,coords)
    else:
        return WeilModuleElement_generic(W,coords)

def ActionOnWeilRepBySL2Z(W,**kwds):
    r"""
    Return an instance of the class which provides the SL2Z-action on a Weil representation.
    """
    if isinstance(W,WeilModule_generic_fqm):
        return ActionOnWeilRepBySL2Z_fqm(W,**kwds)
    elif isinstance(W,WeilModule_generic_lattice):
        return ActionOnWeilRepBySL2Z_lattice(W,**kwds)
    else:
        return ActionOnWeilRepBySL2Z_generic(W)
    
