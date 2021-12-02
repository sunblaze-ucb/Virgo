#include <stdlib.h>
int main() {
  char *p = malloc(16);
  p[24] = 1; // buffer overrun, p has only 16 bytes
  free(p); // free(): invalid pointer
  return 0;
}
