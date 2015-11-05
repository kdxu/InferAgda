InferAgda
=========
Agdaによる'正当性が保証された'型推論器です。
型推論のアルゴリズムとしてW-アルゴリズムを採用しています。

キーワード
-----

+ Agda
+ 依存型
+ 型推論
+ W-algorithm

Agdaのインストール・セットアップ方法
------

##1. cabal から Agda をインストール ##

```
$ cabal install agda
$ agda-mode setup
```
##2. agda-wiki から standard library をダウンロードする##

http://wiki.portal.chalmers.se/agda/pmwiki.php

##3. ダウンロードした standard library を aquamacsにセット##

+ open emacs  
+ `M-x load-library agda2-mode`  
+ `M-x customize-group agda2`  
+ specify "Agda include dirs" e.g. `/users/kyoko/agda-stdlib/src`  
+ select `Save for Future Sessions`


依存型について
-----
依存型は値に依存する型のことであり、例えば`List n` (`n` は自然数) という型は「長さ `n` のリスト」という意味を持つ型の
ことです。
これを応用すると「`Int` 型を持つ項」などを表現することも可能になります。



このソースコードの構造
-----

このソースコードは、`infer.agda`、`term.agda`、`mgu.agda`の三つから構成されています。
それぞれの役割は以下のとおりです。

## infer.agda

証明付きの型推論を行う関数`infer`と、その補助関数が記述されています。

## term.agda

このモジュールでは、型推論を行う well-scoped な term と well-typed な term を定義しています。

### well-scoped term

well-scoped term は、型レベルで `n` というパラメータを持つ term です。
この` n` は、 term の中の自由変数の数を表しています。

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

note:  `Fin n` 型は 0~n-1の自然数の有限集合をもつ型のことです。


### well-typed term

型環境`Γ`と型`t`を（また型レベルの）パラメータとして持ち歩く term です。

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

note : `Type` 型の実装は、`mgu` モジュールに記述されています。

## mgu.agda

最汎の単一化子 (most general unifier) を求める関数 `mgu` が記述されて
います。

型推論とその定式化の仕組み
-----


進行状況
-----
:innocent:


参考文献
-----

License
-----
MIT
