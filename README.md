InferAgda
=========
The certified type-inference by agda.
We use W-algorithm for type inference algorithm.

## how to setup agda

###1. install agda from cabal.

```
$ cabal install agda
$ agda-mode setup
```
###2. download a standard library from agda-wiki.

http://wiki.portal.chalmers.se/agda/pmwiki.php

###3. apply agda standard library dirs.

open emacs  
`M-x load-library agda2-mode`  
`M-x customize-group agda2`  
specify "Agda include dirs" e.g. `/users/kyoko/agda-stdlib/src`  
select `Save for Future Sessions`

you can compile and load agda file with `C-c C-l`.
