# lean-sysf


# OneSortHomArityGen

This development uses single-sorted arity-generic syntax with homogenous substitutions

Notable consequences:
- There needs to be an explicit kinding relation to pick out types
- The typing and kinding relation share the same context
- Substitution assumptions have to be phrased relative to type or term replacements
- Strong normalization requires a restriction on the argument of type application

