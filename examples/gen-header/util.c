#include <stdio.h>
#include "config.h"
#include "util.h"

void greet(const char *who, int times) {
  for (int i = 0; i < times; i++) printf("%s, %s!\n", GREETING, who);
}
