FILE(GLOB LEAN_MODE_FILES *.el)
install(FILES ${LEAN_MODE_FILES} DESTINATION "${EMACS_LISP_DIR}")
