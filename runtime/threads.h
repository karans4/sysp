/* sysp Thread Safety Macros — RC_INC, RC_DEC, SYSP_TLS */
/* Always included. Zero cost if single-threaded (-DSYSP_NO_THREADS). */

#ifndef SYSP_THREADS_H
#define SYSP_THREADS_H

#ifndef SYSP_NO_THREADS
  #if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L && !defined(__STDC_NO_ATOMICS__)
    #include <stdatomic.h>
    #define RC_INC(x) atomic_fetch_add_explicit(&(x), 1, memory_order_relaxed)
    #define RC_DEC(x) atomic_fetch_sub_explicit(&(x), 1, memory_order_acq_rel)
    #define SYSP_TLS _Thread_local
  #elif defined(__GNUC__) || defined(__clang__)
    #define RC_INC(x) __sync_fetch_and_add(&(x), 1)
    #define RC_DEC(x) __sync_fetch_and_sub(&(x), 1)
    #define SYSP_TLS __thread
  #elif defined(_MSC_VER)
    #include <intrin.h>
    #define RC_INC(x) _InterlockedIncrement((long*)&(x))
    #define RC_DEC(x) _InterlockedDecrement((long*)&(x))
    #define SYSP_TLS __declspec(thread)
  #else
    #warning "Unknown compiler: define RC_INC/RC_DEC or -DSYSP_NO_THREADS"
    #define RC_INC(x) (++(x))
    #define RC_DEC(x) (--(x))
    #define SYSP_TLS
  #endif
#else
  #define RC_INC(x) (++(x))
  #define RC_DEC(x) (--(x))
  #define SYSP_TLS
#endif

#endif /* SYSP_THREADS_H */
