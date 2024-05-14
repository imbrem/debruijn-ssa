document:
    DOCGEN_SRC="vscode" lake -R -Kenv=dev build DeBruijnSSA:docs

open-docs:
    python3 -m http.server -d .lake/build/doc