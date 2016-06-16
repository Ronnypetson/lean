/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"

namespace lean {
vm_obj expr_beta(vm_obj const & e1, vm_obj const & e2);
vm_obj expr_to_string(vm_obj const &);

vm_obj qexpr_beta(vm_obj const & e1, vm_obj const & e2) {
    return expr_beta(e1, e2);
}

vm_obj qexpr_of_expr(vm_obj const & e) {
    // TODO(Leo): use "as_is" macro
    return e;
}

vm_obj qexpr_to_string(vm_obj const & e) {
    return expr_to_string(e);
}

void initialize_vm_qexpr() {
    DECLARE_VM_BUILTIN(name({"qexpr", "beta"}),         qexpr_beta);
    DECLARE_VM_BUILTIN(name({"qexpr", "of_expr"}),      qexpr_of_expr);
    DECLARE_VM_BUILTIN(name({"qexpr", "to_string"}),    qexpr_to_string);
}

void finalize_vm_qexpr() {
}
}
