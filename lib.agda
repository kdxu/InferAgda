module lib where
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning 
open import Data.Nat
open import Data.Product
open import Data.Fin
open import Data.Sum
open import Data.Bool
open import Data.Maybe
open import Data.List

---------------------------------------------------------------

lf : {S T : Set} → (f : S → T) → (S → Maybe T)
lf f = λ x → just (f x)
rf : {S T : Set} → (f : S → Maybe T) → (Maybe S → Maybe T)
rf f nothing = nothing
rf f (just x) = f x
lrf :{S T : Set} → (f : S → T) → (Maybe S → Maybe T)
lrf f = rf (lf f)
_∘_ : {A B C : Set} → (f : B → C) → (g : A → B) → (A → C)
f ∘ g = λ x → f (g x)

-- p5

data Type (n : ℕ) : Set where
  TVar : (x : Fin n) → Type n -- 変数 (de Bruijn index) 
  TInt : Type n -- base case の型
  _⇒_ : (s t : Type n) → Type n -- arrow 型

▹ : {n m : ℕ} → (r : Fin m → Fin n) → (Fin m → Type n)
▹ r = TVar ∘ r

_◃_ : {n m : ℕ} → (f : Fin m → Type n) → (Type m → Type n)
_◃_ f (TVar x) = f x
_◃_ f TInt = TInt
_◃_ f (s ⇒ t) = (f ◃ s) ⇒ (f ◃ t) 

_◃ : {n m : ℕ} → (f : Fin m → Type n) → (Type m → Type n)
f ◃ = λ x → f ◃ x

▹◃ :  {n m : ℕ} → (f : Fin m → Fin n) → (Type m → Type n)
▹◃ f = (▹ f) ◃

_≐_ : {n m : ℕ} → (f g : Fin m → Type n) → Set
_≐_ {n} {m} f g = (x : Fin m) → f x ≡ g x

_◇_ : {m n l : ℕ} → (f : Fin m → Type n) → (g : Fin l → Type m) → (Fin l → Type n)
f ◇ g = (f ◃) ∘ g

-- (TVar s) ⇒ (TVar t) -> TVar (s ⇒ t) = s ⇒ t
-- TVar s = s
-- TVar t = t
-- p9

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
-- lrf TVar (thick x y)
check x TInt = just TInt
check x (s ⇒ t) with check x s | check x t
... | just s' | just t' = just (s' ⇒ t')
... | just s' | nothing = nothing
... | nothing | just t' = nothing
... | nothing | nothing = nothing
-- lrf2 _⇒_ (check x s) (check x t)

_for_ : {n : ℕ} → (t' : Type n) → (x : Fin (suc n)) → (Fin (suc n) → Type n)
_for_ t' x y with thick x y
_for_ t' x y | nothing = t'
_for_ t' x y | just y' = TVar y'


data AList : ℕ → ℕ → Set where
  anil : {m : ℕ} → AList m m
  _asnoc_/_ : {m : ℕ} {n : ℕ} → (σ : AList m n) → (t' : Type m) → (x : Fin (suc m)) → AList (suc m) n
--asnoc : consの逆 []::2 ::3 :: ...
_asnoc'_/_ : {m : ℕ} → (a : ∃ (AList m)) → (t' : Type m) → (x : Fin (suc m)) → ∃ (AList (suc m))
( s , t ) asnoc' t' / x = ( s , t asnoc t' / x )

--_◇_ : {m n l : ℕ} → (f : Fin m → Type n) → (g : Fin l → Type m) → (Fin l → Type n)
sub : {m n : ℕ} → (σ : AList m n) → Fin m → Type n
sub anil = TVar --m≡nなら何もしない
sub (σ asnoc t' / x) = (sub σ) ◇ (t' for x)

_⊹⊹_ : {l m n : ℕ} → (ρ : AList m n) → (σ : AList l m) →  AList l n
ρ ⊹⊹ anil = ρ
ρ ⊹⊹ (alist asnoc t / x) = (ρ ⊹⊹ alist) asnoc t / x


data AList' : ℕ →  Set where
  anil' : {m : ℕ} → AList' m
  _acons'_/_ : {m : ℕ} → (σ : AList' m) → (t' : Type m) → (x : Fin (suc m)) → AList' (suc m)

targ : {m : ℕ} → (σ : AList' m) → ℕ
targ {m} anil' = m
targ (a acons' t' / x) = targ a

_⊹⊹'_ : {m : ℕ} → (σ : AList' m) → (ρ : AList' (targ σ)) → AList' m
_⊹⊹'_ anil' ρ = ρ
_⊹⊹'_ (alist acons' t' / x)  ρ = (_⊹⊹'_ alist ρ) acons' t' / x

-- p14

flexFlex : {m : ℕ} → (x y : Fin m) → (∃ (AList m))
flexFlex {suc m} x y with thick x y 
flexFlex {suc m} x y | nothing = ( (suc m) , anil )
flexFlex {suc m} x y | just y' = ( m , anil asnoc (TVar y') / x )
flexFlex {zero} () y

flexRigid : {m : ℕ} → (x : Fin m) → (t : Type m) → Maybe (∃ (AList m))
flexRigid {zero} () t
flexRigid {suc m} x t with check x t
flexRigid {suc m} x t | nothing = nothing
flexRigid {suc m} x t | just t' = just ( m , (anil asnoc t' / x) )

amgu : {m : ℕ} → (s t : Type m) → (acc : ∃ (AList m)) →  Maybe (∃ (AList m))
amgu {suc m} s t ( n , σ asnoc r / z ) = lrf (λ σ₁ → σ₁ asnoc' r / z) (amgu {m} ((r for z) ◃ s) ((r for z) ◃ t) ( n , σ ))
amgu TInt TInt acc = just acc
amgu TInt (t ⇒ t₁) acc = nothing
amgu (TVar x) (TVar x₁) ( s , anil ) = just (flexFlex x x₁)
amgu t (TVar x) acc = flexRigid x t
amgu (TVar x) t acc = flexRigid x t
amgu (s ⇒ s₁) TInt acc = nothing
amgu {m} (s ⇒ s₁) (t ⇒ t₁) acc = rf (amgu {m} s₁ t₁) (amgu {m} s t acc)

mgu : {m : ℕ} → (s t : Type m) → Maybe (∃ (AList m))
mgu {m} s t = amgu {m} s t ( m , anil )

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
