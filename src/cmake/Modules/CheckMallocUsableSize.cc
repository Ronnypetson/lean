/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/

#include <stdio.h>
#include <string.h>
#include <malloc.h>

#define MAX_SZ 1024

int main() {
    for (unsigned i = 1; i < MAX_SZ; i++) {
        void * p = malloc(i);
        size_t r = malloc_usable_size(p);
        if (r < i || r > 2*(i + 8)) {
            fprintf(stderr, "Unexpected malloc_usable_size behavior");
            return 0;
        }
        free(p);
    }
    return 1;
}
