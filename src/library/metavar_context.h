/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/local_context.h"

namespace lean {
class metavar_decl {
    local_context m_context;
    expr          m_type;
    friend class metavar_context;
    metavar_decl(local_context const & ctx, expr const & type):m_context(ctx), m_type(type) {}
public:
    metavar_decl() {}
    expr const & get_type() const { return m_type; }
    local_context const & get_context() const { return m_context; }
};

bool is_metavar_decl_ref(level const & l);
bool is_metavar_decl_ref(expr const & e);

class metavar_context {
    name_map<metavar_decl> m_decls;
    name_map<level>        m_uassignment;
    name_map<expr>         m_eassignment;
    struct interface_impl;
public:
    level mk_univ_metavar_decl();
    expr mk_metavar_decl(local_context const & ctx, expr const & type);

    optional<metavar_decl> get_metavar_decl(expr const & e) const;

    bool is_assigned(level const & l) const {
        lean_assert(is_metavar_decl_ref(l));
        return m_uassignment.contains(meta_id(l));
    }

    bool is_assigned(expr const & m) const {
        lean_assert(is_metavar_decl_ref(m));
        return m_eassignment.contains(mlocal_name(m));
    }

    void assign(level const & u, level const & l);
    void assign(expr const & e, expr const & v);

    level instantiate(level const & l);
    expr instantiate(expr const & e);

    bool has_assigned(level const & l) const;
    bool has_assigned(levels const & ls) const;
    bool has_assigned(expr const & e) const;

    optional<level> get_assignment(level const & l) const;
    optional<expr> get_assignment(expr const & e) const;

    /** \brief Return true iff \c ctx is well-formed with respect to this metavar context.
        That is, every metavariable ?M occurring in \c ctx is declared here, and
        for every metavariable ?M occurring in a declaration \c d, the context of ?M
        must be a subset of the declarations declared *before* \c d.

        \remark This method is used for debugging purposes. */
    bool well_formed(local_context const & ctx) const;

    /** \brief Return true iff all metavariables ?M in \c e are declared in this metavar context,
        and context of ?M is a subset of \c ctx */
    bool well_formed(local_context const & ctx, expr const & e) const;
};

/** \brief Check whether the local context lctx is well-formed and well-formed with respect to \c mctx.
    \remark This procedure is used for debugging purposes. */
bool well_formed(local_context const & lctx, metavar_context const & mctx);

/** \brief Check whether \c e is well-formed with respect to \c lctx and \c mctx. */
bool well_formed(local_context const & lctx, metavar_context const & mctx, expr const & e);

void initialize_metavar_context();
void finalize_metavar_context();
}