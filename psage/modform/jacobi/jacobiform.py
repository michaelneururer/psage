# -*- coding: utf-8 -*-
#*****************************************************************************
#  Copyright (C) 2013 
#
#  Distributed under the terms of the GNU General Public License (GPLv2)
#
#    This code is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#    General Public License for more details.
#
#  The full text of the GPL is available at:
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************
r"""
 Implements classes for (individual) Jacobi forms.

 AUTHORS::

  - Stephan Ehlen
  - Nils Skoruppa
  - Fredrik Strömberg

 EXAMPLES::
"""

from sage.all import SageObject
from sage.modules.free_module_element import FreeModuleElement_generic_dense

class JacobiForm_class(FreeModuleElement_generic_dense):
 
    def __init__(self, weight, lattice, character, ambient_space=None, ambient_module=None):
        self._k = weight
        self._L = lattice
        self._h = character
        self._ambient_space = ambient_space
        self._ambient_module = ambient_module
        self.parent = ambient_space
        

    def fourier_expansion(self):
        r"""
          Returns the Fourier expansion of self.
        """
        raise NotImplementedError("This method is currently not implemented. It should be overriden by the specific subclasses.")

    def ambient_space(self):
        r"""
          Returns the ambient space of Jacobi forms.
        """
        if self._ambient_space == None:
            self._ambient_space = JacobiFormsSpace(weight, lattice, character)
        return self._ambient_space

    def ambient_module(self):
        r"""
          Returns the ambient module of Jacobi forms.
        """
        if self._ambient_module == None:
            self._ambient_module = JacobiFormsSpace(weight, lattice, character)
        return self._ambient_module

    def weight(self):
        return self._k

    def lattice(self):
        return self._L

    def index(self):
        return self._L

    def character(self):
        return self._h

    def __repr__(self):
        return "Jacobi form of weight {0}, index {1} and character epsilon^{2}".format(self._k, self._L, self._h)
