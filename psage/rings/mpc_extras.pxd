include "sage/ext/stdsage.pxi"
include "sage/ext/cdefs.pxi"
#include "sage/rings/mpc.pxi"
#from sage.libs.mpfr cimport *
include "mpfr_loc.pxi"


cdef inline mpc_zero_p(mpc_t z):
    return mpfr_zero_p(z.re) and mpfr_zero_p(z.im)

cdef inline void _mpc_mul(mpc_t* z, mpc_t a, mpc_t b, mpc_t *t, mpc_rnd_t rnd, mpfr_rnd_t rnd_re) nogil


cdef inline void _mpc_div(mpc_t * z, mpc_t a, mpc_t b,  mpc_t t[2], mpfr_rnd_t rnd_re) nogil

cdef inline void _mpc_div_fr(mpc_t * r, mpc_t a, mpfr_t d, mpfr_rnd_t rnd) nogil

cdef inline void _mpc_div_ui(mpc_t *res,mpc_t z, unsigned int i, mpfr_rnd_t rnd_re) nogil

cdef inline void _mpc_conj(mpc_t *res, mpc_t z, mpfr_rnd_t rnd_re) nogil

cdef inline void _mpc_mul_fr(mpc_t* z, mpc_t a, mpfr_t b, mpc_rnd_t rnd, mpfr_rnd_t rnd_re) nogil

cdef inline void _mpc_add(mpc_t *res, mpc_t a, mpc_t b,mpfr_rnd_t rnd_re) nogil

cdef inline void _mpc_sub(mpc_t *res, mpc_t a, mpc_t b,mpfr_rnd_t rnd_re) nogil

cdef inline void _mpc_set(mpc_t *res, mpc_t z, mpfr_rnd_t rnd_re) nogil

cdef print_mpc(mpc_t z)

cdef print_mpfr(mpfr_t z)

cdef inline void _pochammer(mpc_t *res, mpc_t z, int n,mpc_rnd_t rnd,mpfr_rnd_t rnd_re) nogil

cdef void mpc_sign(mpc_t *res, mpc_t *z,mpfr_rnd_t rnd_re) nogil
