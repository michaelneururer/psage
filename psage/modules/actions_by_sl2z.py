r"""

Weil representations for finite quadratic modules.
Implements a class for working with Weil representations and also the explicit formula for general elements of SL(2,Z).


Note: We did not want to implement the metaplectic group so the Weil representation for odd signature is given by the canonical section rho(A)=rho(A,j_A(z))  where j_A(z)=(cz+d)**-1/2 if A = ( a b // c d )
This means that the representation will not be multiplicative, but
$\rho(A)\rho(B)=\sigma(A,B)\rho(AB)$ where the cocycle $\sigma(A,B)$ is implemented as the function sigma_cocycle().





REFERENCES:
 - [St] Fredrik Stromberg, "Weil representations associated to finite quadratic modules", arXiv:1108.0202
 


 AUTHORS:
   - Fredrik Stromberg
   - Nils-Peter Skoruppa
   - Stephan Ehlen


EXAMPLES::


    sage: F=FiniteQuadraticModule('5^1')


   
Author: Fredrik Stromberg (2013)
        

"""

from sage.all import SageObject,UniqueRepresentation,QuadraticField,sqrt
from sage.all import Integer,RR,CC,QQ,ZZ,sgn,cached_method,copy,CyclotomicField,lcm,is_square,matrix,SL2Z,MatrixSpace,floor,ceil,is_odd,is_even,hilbert_symbol,sqrt,inverse_mod,Matrix
from weil_module_alg import *
from psage.modform.maass.mysubgroups_alg import SL2Z_elt
from sage.modular.arithgroup.arithgroup_element import ArithmeticSubgroupElement


def ActionOnWeilRepBySL2Z(W,**kwds):
    if W.finite_quadratic_module()<>None:
        return ActionOnWeilRepBySL2Z_fqm(W,**kwds)
    elif W.lattice()<>None:
        return ActionOnWeilRepBySL2Z_lattice(W,**kwds)
    else:
        return ActionOnWeilRepBySL2Z_generic(W)
    
class ActionOnWeilRepBySL2Z_generic(SageObject):
    r"""
    Implements the action SL(2,Z) on a Weil representation.
    The is separated to this class to make the module structure clearer.
    """
    def __init__(self,W,**kwds):
        self._W = W
        pass
    def matrix(self,A):
        raise NotImplementedError
    def action_by_sl2z_on_element(self,A):
        raise NotImplementedError
    def weil_rep(self,x):
        return self._W(x)
    
    
class ActionOnWeilRepBySL2Z_lattice(ActionOnWeilRepBySL2Z_generic):
    def __init__(self,W,**kwds):
        raise NotImplementedError
    
class ActionOnWeilRepBySL2Z_fqm(ActionOnWeilRepBySL2Z_generic):
    r"""
    A class giving the action of SL(2,z) on a Weil representation.
    The is separated to this class to make the module structure clearer.
    """
    def __init__(self,W,algorithm='formula',act='l',minimal_base_field='false',verbose=0,basis_type='canonical',**kwds):
        r"""
        Initialize the action class.
        """
        self._W = W
        self._verbose = verbose
        self._algorithm = algorithm
        self._n = W.degree()
        self._K1 = W.base_ring()
        self._inv = {}
        self._xcs = {}
        self._act = act
        ### Invariants which we uses
        self._QM = W.finite_quadratic_module()
        self._K = CyclotomicField(lcm(8,self._QM.level()))
        if self._QM==None:
            raise ValueError,"Should have a finite quadratic module for this class!"
        self._level = self._QM.level()
        self._zl = self._K(CyclotomicField(self._QM.level()).gen())
        self._zl_2 = self._K(CyclotomicField(2*self._QM.level()).gen())
        self._z8 = CyclotomicField(8).gens()[0]
        if self._K1<>self._K:
            self._minimal_base_field = True
        assert self._QM <> None
        self._gen_orders = self._QM.elementary_divisors()
        #self._gen_orders.append(1)
        #for g in self._QM.gens():
        #    self._gen_orders.append(g.order())
        if is_square(self._n):
            self._sqn = sqrt(n)
        else:
            self._sqn = QuadraticField(self._n).gens()[0] #self._n.sqrt()
        self._basis_type = basis_type
        if basis_type<>'canonical':
            raise NotImplementedError,"We have only implemented the algorithm using the canonical basis!"
        ## Take over some functions from the Weil rep.
        self.Q = W.Q
        self.Bi = W.Bi
        

    def gen_orders(self):
        return self._gen_orders
    
    def action_by_sl2z_on_element(self,M,elt):
        r"""
        INPUT:
        M = element of SL2Z
        mode : determines how the Weil rpresentation is calculated
        0 => use formula (default)
        1 => use factorization
        act : determines if we act from the right or left
        'l' => rho(A)*x  
        'r' => x^t * rho(A)
        OUTPUT: [s,fac]
        where s is a Formal Sum over  
        K=CyclotomicField(lcm(8,level) and 
        fact is a scalar and such that
        rho_{Q}(M)*self = fact*s
        where 
        EXAMPLE:
        FQ = FiniteQuadraticModule
        A  = Element of SL2Z
        W = WeilModule(FQ)
        x=FQ.gens()[0]
        WE=W(x)
        [r,s] = x.action_of_SL2Z(A)
        fact*x = rho_{Q}(M) 
        """
        # Since we only want to act on this specific element we first
        # figure out which matrix-entries we need to compute:
        if self._algorithm == 'factor':
            return self._action_of_SL2Z_by_factoring(M,elt)
        else:
            return self._action_of_SL2Z_by_formula(M,elt)

    def _action_of_SL2Z_by_formula(self,A,elt=None):
        r"""
        Act with A on elt by using the formula
        """
        if elt==None:
            filter = None
        else:
            filter=self.create_filter(elt)
        r,fac = self._action_of_SL2Z_by_formula_(A,filter)
        res = self.matrix_to_weil_rep(elt,r,fac)
        if self._minimal_base_field==True:
            return res
        else:
            return (fac,res)

    def _action_of_SL2Z_by_factoring(self,A,elt=None):
         r"""
         The action of A on elt given by factoring A into generators.
         """
         # when we use factorization we must compute all elements
         r,fac = self._action_of_SL2Z_by_factoring_(A)
         if elt==None:
             return fac,r
         res = self.matrix_to_weil_rep(elt,r)
         return (fac,res)

    def matrix(self,A):
        r"""
        Return the matrix representing the action of A on the basis of the Weil representation.
        
        """
        if self._algorithm == 'formula':
            r = self._action_of_SL2Z_by_formula_(A)
        else:
            r = self._action_of_SL2Z_by_factoring_(A)
        if self._minimal_base_field:
            if self._K<>self._K1:
                r = basis_change(r,self._K1)
        return r
        
    def create_filter(self,elt):
        r"""
        Return an integer matrix which consists of 1's on the rows or columns corresponding to the non-zero components of elt. and 0 elsewhere.
        """
        myfilter = matrix(ZZ,self._n)
        for i in range(self._n):
            if elt[i]==0:
                continue            
            for j in range(self._n):
                if self._act=='l':
                    myfilter[j,i]=1 
                else:
                    myfilter[i,j]=1 
        return myfilter

    def matrix_to_weil_rep(self,elt,r):
        if self._K1<>self._K:
            r = basis_change(r,self._K1)
        res = self.weil_rep(0)
        if self._minimal_base_field:
            #K = self._zl2.parent()
            facalg = QuadraticField(fac**2).gens()[0]
            if self._act=='r':
                for i in range(elt.degree()):
                    if elt[i] <> 0:
                        res =  res + self._W(r.row(i))*elt[i]
            else:
                for i in range(elt.degree()):
                    if elt[i] <> 0:
                        res =  res + self._W(r.column(i))*elt[i]
            
        else:
            if self._act=='r':
                for i in range(elt.degree()):
                    if elt[i] <> 0:
                        res =  res + self._W(r.row(i))*elt[i]
            else:
                for i in range(elt.degree()):
                    if elt[i] <> 0:
                        res =  res + self._W(r.column(i))*elt[i]
             
        return res

    ## Action by special (simple) elements of SL(2,Z)   
    def _action_of_T(self,b=1,sign=1,filter=None):
        r""" Action by the generator sign*T^pow=[[a,b],[0,d]]
        where a=d=sign
        """
        r = matrix(self._K,self._n)
        if sign==-1:
            si=self._QM.sigma_invariant()**2 
        else:
            si=1
        for ii in range(0 ,self._n):
            if filter<>None and filter[ii,ii]<>1:
                continue
            if sign==1:
                r[ii,ii] = self._zl**(ZZ(b)*self._level*self.Q(ii))
            else:
                r[self._W._minus_element(ii),ii] = si*self._zl**(b*self._level*self.Q(ii))
        return r

    def _action_of_S(self,filter=None,sign=1,mult_by_fact=False):
        r"""
        Action by the generator S=[[0,-1],[1,0]]
        """
        r = matrix(self._K,self._n)
        fac = self._sqn**-1
        if sign==-1:
            si = self._QM.sigma_invariant()**3
            if is_odd(self._QM.signature()):
                si = -si # sigma(Z,A)
        else:
            si = self._QM.sigma_invariant()
        for ii in range(0 ,self._n):
            for jj in range(0 ,self._n):
                if filter<>None and filter[ii,jj]<>1:
                    continue
                arg = -sign*self._level*self.Bi(ii,jj)
                #print "arg=",arg
                #print "zl**arg=",self._zl**arg
                r[ii,jj] = self._zl**arg*si*fac
#        print "si=",si
#        print "fac=",fac
        return r #[r,si*fac]

    def _action_of_STn(self,pow=1,sign=1,filter=None):
        r""" Action by  ST^pow or -ST^pow
        NOTE: we do not divide by |D|
        """
        if pow==0:
            return self._action_of_S(filter,sign)
        r  = matrix(self._K,self._n)
        if sign==-1:
            si = self._K(self._QM.sigma_invariant()**3)
            if is_odd(self._QM.signature()):
                si = -si  # sigma(Z,A)
        else:
            si = self._K(self._QM.sigma_invariant())
        si = si*self._sqn**-1
        for ii in range(self._n):
            for jj in range(self._n):
                argl=self._level*(pow*self.Q(jj)-sign*self.Bi(ii,jj))
                #ii = self._L.index(x); jj= self._L.index(j)
                if filter<>None and filter[ii,jj]<>1:
                    continue
                r[ii,jj] = si*self._zl**argl
        return r
#        fac = self._parent._sqn**-1
#        return [r,fac]

    def _action_of_Z(self,filter=None):
        r""" Action by  Z=-Id
        NOTE: we do not divide by |D|
        """
        ## Have to find a basefield that also contains the sigma invariant
        r = matrix(self._K,self._n)
        for ii in range(0 ,self._n):
            if filter<>None and filter[ii,ii]<>1:
                continue
            jj=self._W._neg_index(ii)
            r[ii,jj]=1 
        r = r*self._QM.sigma_invariant()**2 
        return r #[r,1]
    
    def _action_of_Id(self,filter=None):
        r""" Action by  Z=-Id
        NOTE: we do not divide by |D|
        """
        ## Have to find a basefield that also contains the sigma invariant
        r = matrix(self._K,self._n)
        for ii in range(0 ,self._n):
            if filter<>None and filter[ii,ii]<>1:
                continue
            r[ii,ii]=1 
        #r = r*self._QM.sigma_invariant()**2 
        return r #[r,1]


    # Action by Gamma_0(N) through formula
    def _action_of_Gamma0(self,A,filter=None):
        r"""
        Action by A in Gamma_0(l) 
        where l is the level of the FQM
        INPUT:
        A in SL2Z with A[1,0] == 0 mod l
        act ='r' or 'l' : do we act from left or right'
        filter = |D|x|D| integer matrix with entries 0 or 1
        where 1 means that we compute this entry
        of the matrix rho_{Q}(A) 
        """
        if isinstance(A,(SL2Z_elt,ArithmeticSubgroupElement)):
            a,b,c,d = list(A)
        else:
            raise ValueError,"Need SL2Z element got {0} of type {1}".format(A,type(A))
        if(c % self._level <>0 ):
            raise ValueError, "Must be called with Gamma0(l) matrix! not A=" %(A)
        r = matrix(self._K,self._n)
        for ii in range(0 ,self._n):
            for jj in range(0 ,self._n):
                #                if(self._L[ii]==d*self._L[jj] and (filter==None or filter[ii,jj]==1 )):
                if self.lin_comb(ii,-d,jj)==0 and (filter==None or filter[ii,jj]==1):
                    argl=self._level*b*d*self.Q(jj)
                    r[ii,jj]=self._zl**argl
        # Compute the character 
        signature = self.signature()
        chi = 1
        if self._verbose>1:
            print "r=",r
        if  self._level % 4  == 0 :
            test = (signature + kronecker(-1 ,self._n)) % 4
            if(is_even(test)):
                if(test==0 ):
                    power=1 
                elif(test==2 ):
                    power=-1 
                if( d % 4  == 1 ):
                    chi = 1 
                else:
                    chi=I**power
                chi=chi*kronecker(c,d)
            else:
                if(test==3 ):
                    chi= kronecker(-1 ,d)
                else:
                    chi=1 
            chi = chi*kronecker(d,self._n*2**signature)
        else:
            chi = kronecker(d,self._n)
        r=r*chi
        return r #[r,1 ]
    
    # Now we want the general action

    def _action_of_SL2Z_by_formula_(self,A,filter=None,**kwds):
        r"""
        The Action of A in SL2(Z) given by a matrix rho_{Q}(A)
        as given by the formula
        filter = |D|x|D| integer matrix with entries 0 or 1
        where 1 means that we compute this entry
        of the matrix rho_{Q}(A) 
        """
        ## extract eleements from A
        ##[a,b,c,d]=_entries(A)
        a,b,c,d=list(A)
        # check that A is in SL(2,Z)
        #if(A not in SL2Z):
        #()    raise  TypeError,"Matrix must be in SL(2,Z)!"
        ## Check if we have a generator
        sign=1
        if c==0:
            if b==0:
                if a<0:
                    return self._action_of_Z(filter)
                else:
                    return self._action_of_Id(filter)
            if a<1:
                sign=-1
            else:
                sign=1
            return self._action_of_T(b,sign,filter)
        if c % self._level == 0 :
            return self._action_of_Gamma0(A)
        if abs(c)==1 and a==0:
            if self._verbose>0:
                print "call STn with pos={0} and sign={1}".format(abs(d),sgn(c))
            sic = sgn(c)
            return self._action_of_STn(pow=d*sic,sign=sic,filter=filter)        
        # These are all known easy cases
        # recall we assumed the formula
        if c<0 or (c==0 and d<0): # change to -A
            a=-a; b=-b; c=-c; d=-d
            A=SL2Z(matrix(ZZ,2,2,[a,b,c,d]))
            sign=-1 
        else:
            sign=1
        xis=self._get_xis(A)
        xi=1 
        for q in xis.keys():
            xi=xi*xis[q]
        norms_c=self._get_all_norm_alpha_cs(c)
        #norms_c_old=self._get_all_norm_alpha_cs_old(c)
        if self._verbose>0:
            print "c=",c
            print "xis=",xis
            print "xi=",xi,CC(xi)
            print "norms=",norms_c
        #print "11"
        r = matrix(self._K,self._n)
        if sign==-1:
            #r=r*self._QM.sigma_invariant()**2 
            si = self._QM.sigma_invariant()**2
            if is_odd(self.signature()):
                if c>0 or (c==0 and d<0):
                    si = -si ## sigma(Z,A)
        else:
            si=1
        if self._verbose>0:
            print "si=",si
            print "sign=",sign
        for na in range(0 ,self._n):
            for nb in range(0 ,self._n):
                if filter <> None and filter[na,nb]==0:
                    continue
                if sign==-1:
                    nbm=self._W._minus_element(nb) #-alpha
                else:
                    nbm=nb
                gi=self.lin_comb(na,-d,nbm)
                try:
                    ngamma_c=norms_c[gi]
                    #ngamma_c_old=norms_c_old[gamma]
                except KeyError:
                    #print alpha," not in D^c*"                    
                    continue
                #ngamma_c_old=self._norm_alpha_c(gamma,c)
                #arg_old=a*ngamma_c_old+b*self._QM.B(gamma,beta)+b*d*self._QM.Q(beta)
                #gi = self._L.index(gamma)
                #CHECK: + or - ? arg=a*ngamma_c+b*self.B(gi,nbm)+b*d*self.Q(nbm)
                arg=a*ngamma_c+b*self.Bi(na,nbm)-b*d*self.Q(nbm)
                larg=arg*self._level
                if self._verbose>0 and na==0 and nb==1:
                    print "na,nb,nbm=",na,nb,nbm
                    print "gi=",gi
                    print "ngamma_c[{0}]={1}".format(gi,ngamma_c)
                    print "b*B(na,nbm)=",b*self.Bi(na,nbm)
                    print "arg=",               a,"*",ngamma_c,"+",b,"*",self.Bi(na,nbm),"-",b,"*",d,"*",self.Q(nbm)
                    print "arg=",arg
                    print "e(arg)=",CC(0,arg*RR.pi()*2).exp()
                    print "e_L(arg)=",CC(self._zl**(larg))
                #if na==nb:
                #    print "arg[",na,"]=",a*ngamma_c,'+',b*self.B(gi,nbm),'-',b*d*self.Q(nbm),'=',arg

                r[na,nb]=si*xi*self._zl**(larg)
                if self._verbose>0 and na==0 and nb==1:
                    print "r[",na,nb,"]=",r[na,nb]
                    print "r[",na,nb,"]=",r[na,nb].complex_embedding(53)
                #print "xi=",xi
                #print "zl=",self._zl
        fac = ZZ(self._get_lenDc(c))
        if fac.is_square() and fac<>1:
            fac = fac.sqrt()
        fac = fac/self._sqn
        return r*fac

#        return [r,(QQ(fac)/QQ(self._n)).sqrt()]



    def _get_lenDc(self,c):
        r"""
        compute the number of elements in the group of elements of order c
        """
        # Check to see if everything is precomputed if so we fetch it
        g = gcd(c,self._n)
        if not hasattr(self,"_all_len_Dcs"):
            self._all_len_Dcs=dict()
        if not self._all_len_Dcs.has_key(g):
            n=self._get_one_lenDc(c)
            self._all_len_Dcs[g]=n
        return self._all_len_Dcs[g]

    @cached_method
    def _get_one_lenDc(self,c):
        r"""
        compute the number of elements in the group of elements of order c
        """
        n=0 
        for ii in range(0,self._n):
            x=self._W._elt(ii)
            if c*x == self._QM(0):
                n=n+1 
        return n

    def _get_all_lenDc(self):
        r"""
        Compute the number of elements in the group of elements of order c
        for all c dividing |D|
        """
        res=dict()
        divs = divisors(self._n)
        for c in divs:
            res[c]=self._get_one_lenDc(c)
        self._All_len_Dcs=res

        
    def _get_xis(self,A,B=None,C=None,D=None,pset=None):
        r"""
        compute the p-adic factors: \xi_0, \xi_p, p | |D|

        if pset = p we only return the p-factor of xi.
        """
        JD=self._QM.jordan_decomposition()
        self.get_invariants()
        absD = self._n
        if D==None:
            a,b,c,d=list(A)
        else:
            a=A; b=B; c=C; d=D
        if self._verbose>0:
            print "pset=",pset
            print "JD=",JD
        #info=get_factors2(JD)
        oddity=self._inv['total oddity']
        oddities=self._inv['oddity']
        pexcesses=self._inv['p-excess']
        sign=self._inv['signature']
        z8 = self._z8
        gammafactor=1 
        xis=dict()
        for comp in JD:
            p=comp[1][0]
            xis[p]=1
            if self._verbose>0:
                print "p=",p
        if a*d<>0:
            if(is_even(sign)):
                argl=- 2 *sign
                xis[0]=z8**argl
            else:
                dc=kronecker(-a,c)
                argl=-2 *sign
                if(is_even(c)):
                    argl=argl+(a+1 )*(odd_part(c)+1 )
                xis[0]=z8**argl*dc
        else:
            argl=-sign
            xis[0]=z8**argl
            if pset==0:
                return {0:xis[0]}
            elif pset<>None:
                return {0:1}
            return xis
        if pset==-1 or pset==0:
            return {0:xis[0]}
        if(xis.keys().count(2 )>0 ):
            if(is_odd(c)):
                argl=(c*oddity) % 8 
            else:
                argl=(-(1+a)*oddity) % 8 
            xis[2]=z8**argl
            if self._verbose>0:
                print "oddity(Q)=",oddity
                if(is_odd(c)):                
                    print "c*oddity=",argl
                else:
                    print "-(a+1)oddity=",argl
            if pset==2:
                return {2:xis[2]}
        for comp in JD:
            [p,n,r,ep]=comp[1 ][:4 ]
            if self._verbose>0:
                print "comp:p,n,r,ep=",p,n,r,ep
            t = None if (len(comp[1 ])==4 ) else comp[1 ][4 ]
            q=p**n
            qc=gcd(q,c)
            qqc=Integer(q/qc)
            ccq=Integer(c/qc)
            nq=valuation(qqc,p)
            gammaf=1 
            dc=1 
            #if(c % q == 0): # This only contributes a trivial factor
            #    continue
            if p==2:
                if is_even(c) :
                    if c % q <> 0:
                        odt=self._get_oddity(p,nq,r,ep,t)
                        argl=-a*ccq*odt
                        gammaf=z8**argl
                        if self._verbose>0:
                            print "odt({q})_{t}^{e},{r}={o}".format(t=t,o=odt,e=ep,r=r,q=p**nq)
                            print "argl=",argl
                        dc=kronecker(-a*ccq,qqc**r)
                        if self._verbose>0:
                            print "kron(-ac_q/q_c^r)=",dc
                    dc=dc*kronecker(-a,q**r)
                    xis[ 2 ]=xis[ 2 ]*gammaf*dc
                    if self._verbose>0:
                        print "xis2=",xis[2]
                else:
                    dc=kronecker(c,q**r)
                    xis[ 2 ]=xis[ 2 ]*dc
            else:
                if(c%q <>0 ):
                    exc=self._get_pexcess(p,nq,r,ep)
                    argl=-exc
                    gammaf=z8**argl
                    dc=kronecker(ccq,qqc**r)
                    if self._verbose>0:
                        print "gamma_{p}={g}".format(p=p,g=gammaf)
                dc=dc*kronecker(-d,qc**r)
                xis[p]=xis[p]*gammaf*dc
            if pset==p:
                return {p:xis[p]}
        return xis


    def get_xc(self,c):
        r"""
        Returns x_c which is precomputed at initialization
        """
        k = valuation(c,2)
        if k==0:
            return 0
        return self._get_xc(k)
    @cached_method
    def _get_xc(self,k):
        r"""
        Return xc for c exactly divisible by 2^k
        """
        if self._xcs=={}:
            self.get_all_xcs()
        if self._xcs.has_key(k):
            return self._xcs[k]
        return 0
    
    def get_all_xcs(self):
        r"""
        Computes all non-zero values of the element x_c in the group D
        OUPUT: dictionary k => x_c  where 2^k || c
        This routine is called at initialization of WeilModuleElement
        """
        if self._xcs<>{}:
            return
        J=self._QM.jordan_decomposition()
        res=dict()
        res[0 ]=0 
        for c in J:
            xc=0 
            p,k,r,d = c[1 ][:4 ]
            t = None if 4  == len(c[1 ]) else c[1 ][4 ]
            if(p<>2  or t==None): 
                continue
            q=2 **k # = 2^n
            JC=J.constituent(q)
            CL=JC[0 ]
            # print "CL(",q,")=",JC[0]
            HOM=JC[1 ]
            # print "t=",t
            # We have an odd component
            for y in JC[0 ].orthogonal_basis():
                # print "basis = ",y
                z=JC[1 ](y)
                # print "basis = ",z
                xc=xc+(2 **(k-1 ))*z
            res[k]=xc
        self._xcs = res

    @cached_method
    def _get_all_norm_alpha_cs(self,c):
        r"""
        Computes a vector of all Q(alpha_c)
        for alpha in D  (==0 unless alpha_c is in D^c*)
        """
        res=dict()
        for ai in range(self._n):
            #for alpha in self._L:
            nc=self._get_norm_alpha_c(ai,c)
            if nc<>None:
                res[ai]=nc
        return res
    
    @cached_method
    def _get_norm_alpha_c(self,ai,c):
        r"""
        FQM = Finite Quadratic Module
        Test before that alpha is in D^c*!!
        """
        alpha=self._QM(self._W._elt(ai))
        xc=self.get_xc(c)
        if xc<>0:
            gammatmp=alpha-xc
        else:
            gammatmp=alpha
        # We need to find its inverse mod c
        # i.e. gammatmp/c
        if gcd(c,self._level)==1:
            cc = inverse_mod(c,self._level)
            gamma = (cc*gammatmp).list()
        else:
            gamma=[]
            for jj,g in enumerate(self._QM.gens()):
                for x in range(g.order()):
                    if (c*x - gammatmp.list()[jj]) % g.order() == 0:
                        gamma.append(x)
                        break
            if len(gamma)<len(self._QM.gens()):
                if self._verbose>1:
                    print "c=",c
                    print "x_c=",xc
                    print "gammatmp=",gammatmp
                    print "y=gamma/c=",gamma
                return None
        if self._verbose>0:
            print "xc=",xc

        if len(gamma)<>len(self._W._gen_orders):
            print "W=",self._W
            print "F=",list(self._W._QM)
            print "F.gens=",self._W._QM.gens()
            print "F.gram=",self._W._QM.gram()
            print "is_nondeg=",self._W._QM.is_nondegenerate()
            print "ai=",ai
            print "c=",c
        gi = self._W._el_index(gamma)
        if self._verbose>0:
            print "gi=",gi
        #res=c*self._QM.Q(gamma)
        res=c*self.Q(gi)
        if xc<>0:
            #res=res+self._QM.B(xc,gamma)
            if self._verbose>0:
                print "xc=",xc
                print "xc.list=",xc.list()
                print "orders=",self._W._gen_orders
            xci = self._W._el_index(xc.list())
            res=res+self.Bi(xci,gi)
        return res
       
    #@staticmethod
    # Compute total invariants of a Jordan decomposition
    def get_invariants(self):
        r"""
        INPUT: JD is a Jordan decomposition returned from the FQM package
        OUPUT: dictionary res with entries:
        res['total p-excess']= sum of all p-excesses
        res['total oddity']  = sum of all oddities
        res['oddity']        = list of oddities of all components
        res['p-excess']=     = list of p-excesses of all components
        res['signature']     = signature := (odt-pexc_tot) % 8
        res['type']          = dictionary q=>'I' or 'II' telling whether the 2-adic component q is odd or even
        """
        if self._inv<>{}:
            return
        JD=self._QM.jordan_decomposition()
        pexc=dict()
        odts=dict()
        res=dict()
        types=dict()
        odt=0 
        for c in JD:
            [p,n,r,ep]=c[1 ][:4 ]
            t = 0  if (len(c[1 ])==4 ) else c[1 ][4 ]
            q=p**n
            if( (not is_square(q)) and (ep==-1 )):
                k=1 
            else:
                k=0 
            if(p!=2 ):
                pexc[q]=(r*(q-1 )+4 *k) % 8 
            else:
                odts[q]=((t+4 *k) % 8 ) # Can we have more than one 2-adic component at one time?
                if(t<>0 ):
                    types[q]="I" # odd
                else:
                    types[q]="II" # even
        pexc_tot=0 
        odt=0 
        for q in pexc.keys():
            pexc_tot=pexc_tot+pexc[q]
        for q in odts.keys():
            odt=odt+odts[q]        
        res['total p-excess']=pexc_tot % 8 
        res['total oddity']=odt % 8 
        res['oddity']=odts
        res['p-excess']=pexc
        res['signature']=(odt-pexc_tot) % 8 
        res['type']=types
        self._inv = res

    # computes oddity and p-excess of scaled Jordan blocks
    def _get_oddity(self,p,n,r,ep,t):
        r"""
        return the oddity of the Jordan block q_t^(r*ep) where q = p^n  
        """
        if n==0  or p==1:
            return 0 
        k=0 
        if n % 2 <>0  and ep==-1:  # q not a square and sign=-1
            k=1 
        else:
            k=0 
        if(t):
            odt=(t+k*4 ) % 8 
        else:
            odt=(k*4 ) % 8 
        return odt


    def _get_pexcess(self,p,n,r,ep):
        r"""
        return the oddity of the corresponding Jordan block
        q = p^n  and the module is q^(r*ep)
        """
        if(n==0  or p==1 ):
            return 0 
        #if( n % 2 <>0  and ep==-1 ):  # q is a square
        if( is_odd(n) and ep==-1 ):  # q is a square
            k=1 
        else:
            k=0 
        exc=(r*(p**n-1 )+ 4 *k) % 8
        return exc


    
    def signature(self):
        return self._inv['signature']

    def invariant(self,s):
        if self._inv.has_key(s):
            return  self._inv[s]
        raise ValueError,"Invariant {0} is not defined! Got:{1}".format(s,self._inv.keys())

    def finite_quadratic_module(self):
        return self._QM
    
    def rank(self):
        return self._n
    
    def signature(self):
        if self._inv == {}:
            self.get_invariants()        
        return self._inv['signature']

    def oddity(self):
        if self._inv == {}:
            self.get_invariants()        
        return self._inv['oddity']

    def level(self):
        
        return self._level
    
    def pexcess(self,p):
        if self._inv == {}:
            self.get_invariants()
        return self._inv['p-excess'].get(p,0)
    
    @cached_method
    def lin_comb(self,a,d,b):
        x = self._W._elt(a)+d*self._W._elt(b)
        x=vector(x.list())
        x.set_immutable()
        return self._W._el_index(x)

    
def basis_change(r,K):
    r"""
    Implement coercion of matrix elements from one cyclotomic field to another. The builtin coercion fails in this case...
    """
    K0 = r.base_ring()
    z0 = K0.power_basis()
    r_new = Matrix(K,r.nrows(),r.ncols(),0,is_immutable=False)
    degree_K0 = K0.degree()
    z_in_K = []
    for z in z0:
        try: 
            z_in_K.append(K(z))
        except TypeError: 
            z_in_K.append(0)
    for i in range(r.nrows()):
            for j in range(r.ncols()):
                x  = r[i][j]
                x_new = K(0)
                for xi in range(degree_K0):
                    if z_in_K[xi]==0 and x[xi]<>0:
                            raise TypeError,"Can not coerce current matrix! Fails at {0}".format(x)
                    x_new += z_in_K[xi]*x[xi]
                r_new[i,j]=x_new
    r_new.set_immutable()
    return r_new
