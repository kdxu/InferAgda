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
google



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
います。要はunificationを行う関数です。
### Type の定義
`Type` を定義するにあたり `Desc` 型を用います。
`Desc` は型の再帰やコンストラクタの記述を抽象化したものです。

```agda
data Desc : Set₁ where
  base  : Desc
  _:+:_ : Desc → Desc → Desc
  _:*:_ : Desc → Desc → Desc
  rec   : Desc
```


型推論とその定式化の仕組み
-----

## unification

McBride の手法を採用しています。(参考文献1を参照)
型の unification は，書き換え可能なセルを使うと簡明に実装することがで
きます。しかし、Agda では再代入は許されないのに加えて、停止性が保証
されている必要があります。
そこで McBride は「型変数が具体化されるたびに、具体化されていない型変
数の数がひとつ減る」という点に注目しました。具体的には、 `n` 個の「具
体化されていない型変数」を `Fin n` 型の数字で表現し，その `n` を減らす
ことで停止性が明らかな形の unification を実現しています。ひとたび型変
数をこのような形で表現できれば、その後の unification は通常通りに進みます。型の
中に型変数が出現するかどうかを調べる関数が `check` で、それを使って
最汎の単一化子 (most general unifier) を求める関数が `mgu` です。

進行状況
-----
:innocent:


参考文献
-----

License
-----
MIT
