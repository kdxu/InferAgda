module term where

open import mgu

open import Data.Unit hiding (_≤_; decTotalOrder)
open import Data.Nat
open import Data.Nat.Properties
 -- for the concrete record, such as isCommutativeSemiring
open import Data.Fin hiding (_+_; _≤_)

open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to ≡⟪_⟫_)
open import Data.Product
open import Data.Sum
open import Data.Vec 
open import Data.Maybe
open import Relation.Binary hiding (_⇒_)
 -- for DecTotalOrder.trans 
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning


-- 型：t = TNat | t ⇒ t | TVar x
TypeDesc : Desc
TypeDesc = base :+: rec :*: rec :+: rec :*: rec

Type : (m : ℕ) → Set
Type m = Fix TypeDesc m

TNat : {m : ℕ} → Type m
TNat = F (inj₁ (inj₁ tt)) -- F (inj₁ tt)

_⇒_ : {m : ℕ} → Type m → Type m → Type m
t1 ⇒ t2 = F (inj₁ (inj₂ (t1 , t2)))

-- pair
_∏_ : {m : ℕ} → Type m → Type m → Type m
t1 ∏ t2 = F (inj₂ (t1 , t2))

TVar : {m : ℕ} → (x : Fin m) → Type m
TVar = M

AListType : ℕ → ℕ → Set
AListType m m' = AList TypeDesc m m'

liftType : (m' : ℕ) → {m : ℕ} → Type m → Type (m' + m)
liftType m' t = liftFix {TypeDesc} m' t

liftType≤ : {m m' : ℕ} → (m≤m' : m ≤ m') → Type m → Type m'
liftType≤ m≤m' t = liftFix≤ {TypeDesc} m≤m' t

lem3 :  {m : ℕ} → (m≤m : m ≤ m) →  (x : Type m) → (liftType≤ m≤m x) ≡ x
lem3 m≤m x = begin
             (liftType≤ m≤m x)
             ≡⟨ refl ⟩
               liftFix≤ {TypeDesc} m≤m x
             ≡⟨ {!!} ⟩
               x
             ∎

substType : {m m' : ℕ} → AListType m m' → Type m → Type m' 
substType σ t = substFix {TypeDesc} σ t

substType≤ : {m m' m'' : ℕ} → AListType m'' m' → m ≤ m'' → Type m → Type m' 
substType≤ σ m≤m'' t = substFix≤ {TypeDesc} σ m≤m'' t

-- 型環境 (Γ : Cxt {m} n) 関係

-- 型変数の数が m 個で長さが n の型環境
Cxt : {m : ℕ} → ℕ → Set
Cxt {m} n = Vec (Type m) n

-- liftCxt m' Γ : Γ の中の型変数の数を d だけ増やす
liftCxt : (m' : ℕ) → {m n : ℕ} → Cxt {m} n → Cxt {m' + m} n
liftCxt m' {m} Γ = Data.Vec.map (liftType m') Γ

-- liftCxt≤ m≤m' Γ : Γ の中の型変数の数を m' まで増やす
liftCxt≤ : {m m' n : ℕ} → (m≤m' : m ≤ m') → Cxt {m} n → Cxt {m'} n
liftCxt≤ m≤m' Γ = Data.Vec.map (liftType≤ m≤m') Γ

-- liftCxt 0 Γ は Γ と同じ
liftCxtZero : {m n : ℕ} → (Γ : Cxt {m} n) → liftCxt 0 Γ ≡ Γ
liftCxtZero [] = refl
liftCxtZero (t ∷ Γ) = cong₂ _∷_ (M-id t) (liftCxtZero Γ)

--liftCxt≤Zero  : {m n : ℕ} → (Γ : Cxt {m} n) → (m≤m : m ≤ m) → liftCxt 0 Γ ≡ Γ

-- substCxt σ Γ : Γ に σ を適用した型環境を返す
substCxt : {m m' n : ℕ} → AListType m m' → Cxt {m} n → Cxt {m'} n 
substCxt σ Γ = Data.Vec.map (substType σ) Γ 

-- substCxt≤ σ Γ : Γ を m' まで引き上げてから σ を適用した型環境を返す
substCxt≤ : {m m' m'' n : ℕ} → AListType m' m'' → (m≤m' : m ≤ m') →
            Cxt {m} n → Cxt {m''} n 
substCxt≤ σ m≤m' Γ = Data.Vec.map (substType σ) (liftCxt≤ m≤m' Γ)

-- substCxt anil Γ は Γ と同じ
substCxtAnil : {m n : ℕ} → (Γ : Cxt {m} n) → substCxt anil Γ ≡ Γ 
substCxtAnil [] = refl
substCxtAnil (x ∷ Γ) = cong₂ _∷_ (M-id x) (substCxtAnil Γ)

substCxt≤Anil : {m n : ℕ} → (Γ : Cxt {m} n) → (m≤m : m ≤ m) → substCxt≤ anil m≤m Γ ≡ Γ 
substCxt≤Anil [] m≤m = refl
substCxt≤Anil (x ∷ Γ) m≤m = cong₂ _∷_ {!!} (substCxt≤Anil Γ m≤m)

-- 自由変数の数が n 個の well-socpe な項
data WellScopedTerm (n : ℕ) : Set where
  Var : Fin n → WellScopedTerm n
  Lam : (s : WellScopedTerm (suc n)) → WellScopedTerm n
  App : (s1 : WellScopedTerm n) → (s2 : WellScopedTerm n) → WellScopedTerm n
  Fst : WellScopedTerm n → WellScopedTerm n
  Snd : WellScopedTerm n → WellScopedTerm n
  Cons : WellScopedTerm n → WellScopedTerm n → WellScopedTerm n


-- WellTypedTerm Γ t : 自由変数の数が n 個、型が t であるような well-typed な項
data WellTypedTerm {m n : ℕ} (Γ : Cxt n) : Type m → Set where
  Var : (x : Fin n) → WellTypedTerm Γ (lookup x Γ)
  Lam : (t : Type m) → {t' : Type m} → WellTypedTerm (t ∷ Γ) t' →
        WellTypedTerm Γ (t ⇒ t')
  App : {t t' : Type m} → WellTypedTerm Γ (t ⇒ t') → WellTypedTerm Γ t →
        WellTypedTerm Γ t'
  Fst : {t1 t2 : Type m} → WellTypedTerm Γ (t1 ∏ t2) →  WellTypedTerm Γ t1
  Snd : {t1 t2 : Type m} → WellTypedTerm Γ (t1 ∏ t2) →  WellTypedTerm Γ t2
  Cons :  {t1 t2 : Type m} → WellTypedTerm Γ t1 → WellTypedTerm Γ t2 → WellTypedTerm Γ (t1 ∏ t2)  
