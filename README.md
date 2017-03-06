# Lazy MAC

Lazy evaluation enhances non-strict evaluation with sharing, guaranteeing that every term is evaluated at most once.

While it is normally considered a positive feature, it can be abused in information-flow libraries, 
such as [MAC](https://hackage.haskell.org/package/mac), to leak secrets as shown in 
[Lazy Program Leaks Secrets](http://www.cse.chalmers.se/~russo/publications_files/nordsec2013.pdf).

This project formalizes MAC as a simply-typed lambda calculus and models *call-by-need* evaluation strategy
using Sestoft's Lazy Abstract Machine.

The calculus is extended with a *general-purpose* unsharing primitive that, in this setting,
is used to restrict sharing for terms that could possibly leak secrets otherwise.

The agda code has been typechecked with Agda version 2.4.2.5, stdlib version 0.11, 
and --rewriting flag. 

