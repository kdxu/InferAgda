module FUSR where
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning 
open import Data.Nat
open import Data.Product
open import Data.Empty
open import Data.Fin
open import Data.Sum
open import Data.Bool
open import Data.Maybe
import Level

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

lf2 : {R S T : Set} → (f : R → S → T) → (R → S → Maybe T)
lf2 f = λ x x₁ → just (f x x₁)

rf2 : {R S T : Set} → (f : R → S → Maybe T) → (R → Maybe S → Maybe T)
rf2 f x nothing = nothing
rf2 f x (just x₁) = f x x₁

cf2 : {R S T : Set} → (f : R → Maybe S → Maybe T) → (Maybe R → Maybe S → Maybe T)
cf2 f nothing nothing = nothing
cf2 f nothing (just x) = nothing
cf2 f (just x) nothing = f x nothing
cf2 f (just x) (just x₁) = f x (just x₁)

lrf2 : {R S T : Set} → (f : R → S → T) → (Maybe R → Maybe S → Maybe T)
lrf2 f = cf2 (rf2 (lf2 f))

-- p5

record ⊤ : Set where

empty : Fin zero → Set
empty x = ⊥


Fin' : ℕ →  Set
Fin' zero = ⊥
Fin' (suc n) = Maybe (Fin' n)

open import Data.List

revapp : {T : Set} → (xs ys : List T) → List T
revapp [] ys = ys
revapp (x ∷ xs) ys = revapp xs (x ∷ ys)

ack : (m n : ℕ) → ℕ
ack zero n = suc n
ack (suc m) zero = ack m (suc zero)
ack (suc m) (suc n) = ack m (ack (suc m) n)

-- Chap 3
-- p8

data Term (n : ℕ) : Set where
  ι : (x : Fin n) → Term n -- 変数 (de bruijn index) 
  leaf : Term n -- base case の型
  _fork_ : (s t : Term n) → Term n -- arrow 型

▹ : {n m : ℕ} → (r : Fin m → Fin n) → (Fin m → Term n)
▹ r = ι ∘ r

_◃_ : {n m : ℕ} → (f : Fin m → Term n) → (Term m → Term n)
_◃_ f (ι x) = f x
_◃_ f leaf = leaf
_◃_ f (s fork t) = (f ◃ s) fork (f ◃ t) 

_◃ : {n m : ℕ} → (f : Fin m → Term n) → (Term m → Term n)
f ◃ = λ x → f ◃ x

▹◃ :  {n m : ℕ} → (f : Fin m → Fin n) → (Term m → Term n)
▹◃ f = (▹ f) ◃

_≐_ : {n m : ℕ} → (f g : Fin m → Term n) → Set
_≐_ {n} {m} f g = (x : Fin m) → f x ≡ g x

_◇_ : {m n l : ℕ} → (f : Fin m → Term n) → (g : Fin l → Term m) → (Fin l → Term n)
f ◇ g = (f ◃) ∘ g

-- (ι s) fork (ι t) ⇒ ι (s fork t) = s fork t
-- ι s = s
-- ι t = t
-- p9

thin : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)  -- thin <-> thick
thin {n} zero y = suc y
thin {suc n} (suc x) zero = zero
thin {suc n} (suc x) (suc y) = suc (thin x y)


thick : {n : ℕ} → (x y : Fin (suc n)) → Maybe (Fin n)
thick {n} zero zero = nothing
thick {n} zero (suc y) = just y
thick {zero} (suc ()) zero
thick {suc n} (suc x) zero = just zero
thick {zero} (suc ()) (suc y)
thick {suc n} (suc x) (suc y) = lrf suc (thick {n} x y)

check : {n : ℕ} → Fin (suc n) → Term (suc n) → Maybe (Term n)
check x (ι y) = lrf ι (thick x y)
check x leaf = just leaf
check x (s fork t) = lrf2 _fork_ (check x s) (check x t)

_for_ : {n : ℕ} → (t' : Term n) → (x : Fin (suc n)) → (Fin (suc n) → Term n)
_for_ t' x y with thick x y
_for_ t' x y | nothing = t'
_for_ t' x y | just y' = ι y'


data AList : ℕ → ℕ → Set where
  anil : {m : ℕ} → AList m m
  _asnoc_/_ : {m : ℕ} {n : ℕ} → (σ : AList m n) → (t' : Term m) → (x : Fin (suc m)) → AList (suc m) n
--asnoc : consの逆 []::2 ::3 :: ...
_asnoc'_/_ : {m : ℕ} → (a : ∃ (AList m)) → (t' : Term m) → (x : Fin (suc m)) → ∃ (AList (suc m))
( s , t ) asnoc' t' / x = ( s , t asnoc t' / x )

--_◇_ : {m n l : ℕ} → (f : Fin m → Term n) → (g : Fin l → Term m) → (Fin l → Term n)
sub : {m n : ℕ} → (σ : AList m n) → Fin m → Term n
sub anil = ι --m≡nなら何もしない
sub (σ asnoc t' / x) = (sub σ) ◇ (t' for x)

_⊹⊹_ : {l m n : ℕ} → (ρ : AList m n) → (σ : AList l m) →  AList l n
ρ ⊹⊹ anil = ρ
ρ ⊹⊹ (alist asnoc t / x) = (ρ ⊹⊹ alist) asnoc t / x


data AList' : ℕ →  Set where
  anil' : {m : ℕ} → AList' m
  _acons'_/_ : {m : ℕ} → (σ : AList' m) → (t' : Term m) → (x : Fin (suc m)) → AList' (suc m)

targ : {m : ℕ} → (σ : AList' m) → ℕ
targ {m} anil' = m
targ (a acons' t' / x) = targ a

_⊹⊹'_ : {m : ℕ} → (σ : AList' m) → (ρ : AList' (targ σ)) → AList' m
_⊹⊹'_ anil' ρ = ρ
_⊹⊹'_ (alist acons' t' / x)  ρ = (_⊹⊹'_ alist ρ) acons' t' / x


sub' : {m : ℕ} →  (σ : AList' m) → (Fin m → Term (targ σ))
sub' anil' = ι
sub' (σ acons' t' / x) =  (sub' σ) ◇ (t' for x)


-- p14

flexFlex : {m : ℕ} → (x y : Fin m) → (∃ (AList m))
flexFlex {suc m} x y with thick x y 
flexFlex {suc m} x y | nothing = ( (suc m) , anil )
flexFlex {suc m} x y | just y' = ( m , anil asnoc (ι y') / x )
flexFlex {zero} () y

flexRigid : {m : ℕ} → (x : Fin m) → (t : Term m) → Maybe (∃ (AList m))
flexRigid {zero} () t
flexRigid {suc m} x t with check x t
flexRigid {suc m} x t | nothing = nothing
flexRigid {suc m} x t | just t' = just ( m , (anil asnoc t' / x) )

amgu : {m : ℕ} → (s t : Term m) → (acc : ∃ (AList m)) →  Maybe (∃ (AList m))
amgu {suc m} s t ( n , σ asnoc r / z ) = lrf (λ σ₁ → σ₁ asnoc' r / z) (amgu {m} ((r for z) ◃ s) ((r for z) ◃ t) ( n , σ ))
amgu leaf leaf acc = just acc
amgu leaf (t fork t₁) acc = nothing
amgu (ι x) (ι x₁) ( s , anil ) = just (flexFlex x x₁)
amgu t (ι x) acc = flexRigid x t
amgu (ι x) t acc = flexRigid x t
amgu (s fork s₁) leaf acc = nothing
amgu {m} (s fork s₁) (t fork t₁) acc = rf (amgu {m} s₁ t₁) (amgu {m} s t acc)

mgu : {m : ℕ} → (s t : Term m) → Maybe (∃ (AList m))
mgu {m} s t = amgu {m} s t ( m , anil )

-- test

t1 : Term 4
t1 = (ι zero) fork (ι zero)

t2 : Term 4
t2 = ((ι (suc zero)) fork (ι (suc (suc zero)))) fork (ι (suc (suc (suc zero))))

u12 : Maybe (∃ (AList 4))
u12 = (mgu t1 t2)

--u12 ≡ just
--( 2 ,
--(anil asnoc ι zero fork ι (suc zero) / suc (suc zero)) asnoc
--ι zero fork ι (suc zero) / zero
--)
-- (1 → 2) → 3
-- 0が無いので
-- 数字がずれて
-- (0 → 1) → 2 
-- (0 → 1) → (0 → 1)
-- unifyできない例

t3 : Term 4
t3 = ((ι zero) fork (ι (suc (suc zero)))) fork (ι (suc (suc (suc zero))))

u13 : Maybe (∃ (AList 4))
u13 = (mgu t1 t3)
