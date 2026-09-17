/* Helpers shared by the curve448 C sources. */

#ifndef CURVE448_CT_H
#define CURVE448_CT_H

#include <stddef.h>

/* Overwrite secret intermediates before returning. Writing through a
 * volatile pointer keeps the compiler from eliding stores to memory that is
 * never read again. */
static void ct_wipe(void *buf, size_t len) {
  volatile unsigned char *p = (volatile unsigned char *)buf;
  while (len--) *p++ = 0;
}

#endif
