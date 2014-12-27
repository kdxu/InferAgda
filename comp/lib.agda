module lib where

open import Data.Nat
open import Data.Product
open import Data.Fin
open import Data.Maybe
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality
-- open import Relation.Binary.HeterogeneousEquality

---------------------------------------------------------------

-- Type n : 最大で n 個の型変数を持つ型を表す型。
data Type (n : ℕ) : Set where
  TVar : (x : Fin n) → Type n -- 型変数 (de Bruijn index) 
  TInt : Type n -- base case の型
  _⇒_ : (s t : Type n) → Type n -- arrow 型

-- f ◃ t : 型 t 中の型変数部分に f を施した型を返す
_◃_ : {n m : ℕ} → (f : Fin m → Type n) → (Type m → Type n)
_◃_ f (TVar x) = f x
_◃_ f TInt = TInt
_◃_ f (s ⇒ t) = (f ◃ s) ⇒ (f ◃ t) 

-- f ◃ t : 型 t 中の型変数部分に f を施した型を返す
_◃ : {n m : ℕ} → (f : Fin m → Type n) → (Type m → Type n)
f ◃ = λ x → f ◃ x

-- 型の中の全ての型変数に f を施す（Infer.agda でのみ使う）
▹◃ :  {n m : ℕ} → (f : Fin m → Fin n) → (Type m → Type n)
▹◃ f = (TVar ∘ f) ◃

-- 全ての型変数に TVar を付け直すだけなら変化なし（Infer.agda でのみ使う）
TVarId : {m : ℕ} → (t : Type m) → TVar ◃ t ≡ t
TVarId (TVar x) = refl
TVarId TInt = refl
TVarId (t1 ⇒ t2) = cong₂ _⇒_ (TVarId t1) (TVarId t2)

-- thin x y : 変数 y を x の位置で「薄める」
-- （x 未満の変数はそのまま。x 以上の変数は +1 される。
--   thin の結果が x になることはない。）
thin : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)  -- thin <-> thick
thin {n} zero y = suc y
thin {suc n} (suc x) zero = zero
thin {suc n} (suc x) (suc y) = suc (thin x y)

-- thick x y : 変数 y を x の位置で「濃縮する」
-- （x 未満の変数はそのまま。x より大きい変数は -1 される。
--   x と y が同じ場合は濃縮できないので nothing が返る。）
thick : {n : ℕ} → (x y : Fin (suc n)) → Maybe (Fin n)
thick {n} zero zero = nothing -- x = y だった
thick {n} zero (suc y) = just y -- 濃縮する
thick {zero} (suc ()) zero
thick {suc n} (suc x) zero = just zero -- x 未満なのでそのまま
thick {zero} (suc ()) (suc y)
thick {suc n} (suc x) (suc y) with thick {n} x y
... | just x' = just (suc x')
... | nothing = nothing -- x = y だった

-- check x t : x 番の型変数が型 t の中に現れるかをチェックする。
-- 現れなければ、型 t を x で thick できるはずなので、それを返す。
-- 現れたら、nothing を返す。
check : {n : ℕ} → Fin (suc n) → Type (suc n) → Maybe (Type n)
check x (TVar y) with thick x y
... | just y' = just (TVar y')
... | nothing = nothing -- x が現れた（x = y だった）
check x TInt = just TInt
check x (s ⇒ t) with check x s | check x t
... | just s' | just t' = just (s' ⇒ t')
... | just s' | nothing = nothing
... | nothing | just t' = nothing
... | nothing | nothing = nothing

-- t' for x : x 番の型変数を型 t' に unify するような unifier を返す。
_for_ : {n : ℕ} → (t' : Type n) → (x : Fin (suc n)) → Fin (suc n) → Type n
_for_ t' x y with thick x y
... | just y' = TVar y'
... | nothing = t'

-- AList m n : m 個の型変数を持つ型を n 個の型変数を持つ型にする代入
data AList : ℕ → ℕ → Set where
  anil : {m : ℕ} → AList m m -- 何もしない代入
  _asnoc_/_ : {m : ℕ} {n : ℕ} → (σ : AList m n) → (t' : Type m) →
              (x : Fin (suc m)) → AList (suc m) n
          -- x を t' にした上で、さらにσを行う代入

-- 型変数に代入σを施す（Infer.agda でのみ使う）
sub : {m n : ℕ} → (σ : AList m n) → Fin m → Type n
sub anil = TVar
sub (σ asnoc t' / x) = (sub σ) ◇ (t' for x)
  where _◇_ : {m n l : ℕ} → (f : Fin m → Type n) → (g : Fin l → Type m) → (Fin l → Type n)
        f ◇ g = (f ◃) ∘ g

-- ふたつの代入をくっつける（Infer.agda でのみ使う）
_⊹⊹_ : {l m n : ℕ} → (ρ : AList m n) → (σ : AList l m) →  AList l n
ρ ⊹⊹ anil = ρ
ρ ⊹⊹ (alist asnoc t / x) = (ρ ⊹⊹ alist) asnoc t / x



-- 型変数 x と y を unify する代入を返す 
flexFlex : {m : ℕ} → (x y : Fin m) → Σ[ n ∈ ℕ ] AList m n
flexFlex {zero} () y
flexFlex {suc m} x y with thick x y 
... | nothing = (suc m , anil) -- x = y だった。代入の必要なし
... | just y' = (m , anil asnoc (TVar y') / x) -- TVar y' for x を返す

-- 型変数 x と型 t を unify する代入を返す
-- x が t に現れていたら nothing を返す
flexRigid : {m : ℕ} → (x : Fin m) → (t : Type m) →
                Maybe (Σ[ n ∈ ℕ ] AList m n)
flexRigid {zero} () t
flexRigid {suc m} x t with check x t
... | nothing = nothing -- x が t に現れていた
... | just t' = just (m , anil asnoc t' / x) -- t' for x を返す

-- 型 s と t（に acc をかけたもの）を unify する代入を返す
amgu : {m : ℕ} → (s t : Type m) → (acc : Σ[ n ∈ ℕ ] AList m n) →
                Maybe (Σ[ n ∈ ℕ ] AList m n)
amgu TInt     TInt     acc        = just acc
amgu TInt     (t ⇒ t₁) acc        = nothing
amgu (s ⇒ s₁) TInt     acc        = nothing
amgu (s ⇒ s₁) (t ⇒ t₁) acc        with amgu s t acc
...                               | just acc' = amgu s₁ t₁ acc'
...                               | nothing = nothing
amgu (TVar x) (TVar y) (s , anil) = just (flexFlex x y)
amgu (TVar x) t        (s , anil) = flexRigid x t
amgu t        (TVar x) (s , anil) = flexRigid x t
amgu {suc m} s t (n , σ asnoc r / z)
  with amgu {m} ((r for z) ◃ s) ((r for z) ◃ t) (n , σ)
... | just (n' , σ') = just (n' , σ' asnoc r / z)
... | nothing = nothing

-- 型 s と t を unify する代入を返す
mgu : {m : ℕ} → (s t : Type m) → Maybe (Σ[ n ∈ ℕ ] AList m n)
mgu {m} s t = amgu {m} s t (m , anil)

-- test

t1 : Type 4
t1 = (TVar zero) ⇒ (TVar zero)

t2 : Type 4
t2 = ((TVar (suc zero)) ⇒ (TVar (suc (suc zero)))) ⇒ (TVar (suc (suc (suc zero))))

u12 : Maybe (∃ (AList 4))
u12 = (mgu t1 t2)

t3 : Type 4
t3 = ((TVar zero) ⇒ (TVar (suc (suc zero)))) ⇒ (TVar (suc (suc (suc zero))))

u13 : Maybe (∃ (AList 4))
u13 = (mgu t1 t3)
