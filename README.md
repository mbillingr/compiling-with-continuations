
### TODO
- type lang
  - [ ] Make interfaces "global":
    - Lexically scoped interface definitions look like a bad idea now. If a type implements an interface only in
      a part of the program, how should the substitution (which is global) know where this is the case?
    - Regardless of the scope the interface was implemented in, it should be available for the whole scope of the type.
      (It might be clearer to allow interface implementations only in the same scope as the type definition.)
    - What about multi-type interfaces? What would the scope of a hypothetical `Cast T U` interface be, if both types
      have different scopes? (their intersection?)
    - Another idea: interfaces must dominate the types which implement them. A "local" interface can only be implemented
      for types that are even more local.
  - [ ] Interfaces inspired by idris: Functions can be associated to an interface. 
        These are not methods, but standalone functions. They have alternative implementations for different types. 
    - [x] Multi argument functions
    - [x] Multi argument lambdas
  - [x] Multi argument enum constructors
- mini lambda
  - [x] let form 
- cps lang