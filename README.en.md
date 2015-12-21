InferAgda
=========
The certified type-inference by agda.
We use W-algorithm for type inference algorithm.

how to setup agda
------

##1. install agda from cabal. ##

```
$ cabal install agda
$ agda-mode setup
```
##2. download a standard library from agda-wiki.##

http://wiki.portal.chalmers.se/agda/pmwiki.php

##3. apply agda standard library dirs.##

+ open emacs  
+ `M-x load-library agda2-mode`  
+ `M-x customize-group agda2`  
+ specify "Agda include dirs" e.g. `/users/kyoko/agda-stdlib/src`  
+ select `Save for Future Sessions`

you can compile and load agda file with `C-c C-l`.


structures
-----

## infer.agda

## term.agda

this module represents simple well-scoped term and well-typed term of
 type-inference system.

### well-scoped term

the word 'well-scoped' implies all terms have a parameter `n` that counts
free variables with type level.(a simple example of dependant types)

#### definition

WellScopedTerm n :=
  Var : Fin n → WellScopedTerm n
  Lam : (s : WellScopedTerm (suc n))   WellScopedTerm n
  App : (s1 : WellScopedTerm n)   (s2 : WellScopedTerm n)   WellScopedTerm n
  Fst : WellScopedTerm n   WellScopedTerm n
  Snd : WellScopedTerm n   WellScopedTerm n
  Cons : WellScopedTerm n   WellScopedTerm n   WellScopedTerm nm (suc n)) → WellScopedTerm n
  App : (s1 : WellScopedTerm n) → (s2 : WellScopedTerm n) → WellScopedTerm n
  Fst : WellScopedTerm n → WellScopedTerm n
  Snd : WellScopedTerm n → WellScopedTerm n
  Cons : WellScopedTerm n → WellScopedTerm n → WellScopedTerm n

note: the type `Fin n` is 'finite set', has a finite set of 0 ~ n-1.


### well-typed term

this term has two parameters with type level, type context and type.
so, this term is certified that has correct type `t` with the context `Γ `.

#### definition

WellTypedTerm (Γ : Cxt n)  (t : Type m) :=
  Var : (x : Fin n) → WellTypedTerm Γ (lookup x Γ)
  Lam : (t : Type m) → {t' : Type m} → WellTypedTerm (t ∷ Γ) t' →
        WellTypedTerm Γ (t ⇒ t')
  App : {t t' : Type m} → WellTypedTerm Γ (t ⇒ t') → WellTypedTerm Γ t →
        WellTypedTerm Γ t'
  Fst : {t1 t2 : Type m} → WellTypedTerm Γ (t1 ∏ t2) →  WellTypedTerm Γ t1
  Snd : {t1 t2 : Type m} → WellTypedTerm Γ (t1 ∏ t2) →  WellTypedTerm Γ t2
  Cons :  {t1 t2 : Type m} → WellTypedTerm Γ t1 → WellTypedTerm Γ t2 → WellTypedTerm Γ (t1 ∏ t2)  

the type `Type` is discribed in the module `mgu`.

## mgu.agda


License
-----
MIT