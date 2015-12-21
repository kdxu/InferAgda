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
open import Function using (_∘_)
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

liftTypeZero : {m : ℕ} → (x : Type m) → (liftType zero x) ≡ x
liftTypeZero x = sym (liftFixZero x)

liftType≤ : {m m' : ℕ} → (m≤m' : m ≤ m') → Type m → Type m'
liftType≤ m≤m' t = liftFix≤ {TypeDesc} m≤m' t

liftTypem≤m :  (m : ℕ) → (m≤m : m ≤ m) →  (x : Type m) → (liftType≤ m≤m x) ≡ x
liftTypem≤m m m≤m x = liftFixm≤m m≤m x

inject≤zero : {m m' : ℕ} → (1+m≤1+m' : suc m ≤ suc m') → inject≤ (zero {n = m}) 1+m≤1+m' ≡ (zero {n = m'})
inject≤zero (s≤s 1+m≤1+m') = refl

inject≤add2 : {m m' : ℕ} → (k : ℕ) → (k+m≤m' : k + m ≤ m') → (m≤m' : m ≤ m') →
        (x : Fin m) →
        inject≤ (inject+'' k x) k+m≤m' ≡ inject≤ x m≤m'
inject≤add2 {.(suc m)} {.(suc m')} k k+m≤m' (s≤s {m = m} {n = m'} m≤m') (zero {n = .m})
  rewrite m+sucn≡sucm+n k m = inject≤zero k+m≤m'
inject≤add2 {.(suc m)} {.(suc m')} k k+m≤m' (s≤s {m = m} {n = m'} m≤m') (suc x)
  rewrite m+sucn≡sucm+n k m = eq k+m≤m'
  where eq : (k+m≤m' : suc (k + m) ≤ suc m') → inject≤ (suc (inject+'' k x)) k+m≤m' ≡ suc (inject≤ x m≤m')
        eq (s≤s k+m≤m'') = cong suc (inject≤add2 k k+m≤m'' m≤m' x)

inject≤add : {m m' : ℕ} → (k : ℕ) → (k+m≤m' : k + m ≤ m') → (m≤m' : m ≤ m') →
        (x : Fin m) →
        ((λ x → inject≤ x k+m≤m') ∘ inject+' k) x ≡ inject≤ x m≤m'
inject≤add k k+m≤m' m≤m' x
  rewrite inject+equal k x = inject≤add2 k k+m≤m' m≤m' x

-- functional extensionality
postulate
  ext : forall {A B : Set} {f g : A -> B} -> (∀ (a : A) -> f a ≡ g a) -> f ≡ g

inject≤add-ext : {m m' : ℕ} → (k : ℕ) → (k+m≤m' : k + m ≤ m') → (m≤m' : m ≤ m') →
        (λ x → inject≤ x k+m≤m') ∘ (inject+' k) ≡ λ x → inject≤ x m≤m'
inject≤add-ext k k+m≤m' m≤m' = ext (λ x → inject≤add k k+m≤m' m≤m' x)

liftType≤add : {m m' : ℕ} → (k : ℕ) → (x : Type m) → (k+m≤m' : k + m ≤ m') → (m≤m' : m ≤ m') →
        liftType≤ k+m≤m' (liftType k x) ≡ liftType≤ m≤m' x
liftType≤add {m} {m'} k x k+m≤m' m≤m' = begin
    liftType≤ k+m≤m' (liftType k x)
  ≡⟨ refl ⟩
    liftFix≤ {TypeDesc} k+m≤m' (liftFix {TypeDesc} k x)
  ≡⟨ refl ⟩
    mvar-map-fin (λ x → inject≤ x k+m≤m') (mvar-map-fin (inject+' k) x)
  ≡⟨ mvar-map-fin-add (λ x → inject≤ x k+m≤m') (inject+' k) x ⟩
    mvar-map-fin ((λ x → inject≤ x k+m≤m') ∘ (inject+' k)) x
  ≡⟨ cong (λ f → mvar-map-fin f x) (inject≤add-ext k k+m≤m' m≤m') ⟩
    mvar-map-fin (λ x → inject≤ x m≤m') x
  ≡⟨ refl ⟩
    liftFix≤ {TypeDesc} m≤m' x
  ≡⟨ refl ⟩
    liftType≤ m≤m' x
  ∎
 -- mvar-map-fin-add {_} {m} {k + m} {m'} {!!} {!!} {!x!}



substType : {m m' : ℕ} → AListType m m' → Type m → Type m'
substType σ t = substFix {TypeDesc} σ t

substTypeAnil : {m m' : ℕ} → (t : Type m) → substType anil t ≡ t
substTypeAnil t = fold-id t

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

-- 空の型環境は lift しても同じ
liftCxtEmpty : (m' m : ℕ) → liftCxt m' {m} {0} [] ≡ []
liftCxtEmpty m' m = refl

-- substCxt σ Γ : Γ に σ を適用した型環境を返す
substCxt : {m m' n : ℕ} → AListType m m' → Cxt {m} n → Cxt {m'} n
substCxt σ Γ = Data.Vec.map (substType σ) Γ

-- substCxt≤ σ Γ : Γ を m' まで引き上げてから σ を適用した型環境を返す
substCxt≤ : {m m' m'' n : ℕ} → AListType m' m'' → (m≤m' : m ≤ m') →
            Cxt {m} n → Cxt {m''} n
substCxt≤ σ m≤m' Γ = Data.Vec.map (substType σ) (liftCxt≤ m≤m' Γ)

substAnilm≤m : {m : ℕ} → (x : Type m) → (m≤m : m ≤ m) → substType anil (liftType≤ m≤m x) ≡ x
substAnilm≤m {m} x m≤m =
            begin
              substType anil (liftType≤ m≤m x)
            ≡⟨ cong (λ x₁ → substType anil x₁) (liftTypem≤m m m≤m x) ⟩
               substType anil x
            ≡⟨ fold-id x ⟩
               x
            ∎

-- substCxt anil Γ は Γ と同じ
substCxtAnil : {m n : ℕ} → (Γ : Cxt {m} n) → substCxt anil Γ ≡ Γ
substCxtAnil [] = refl
substCxtAnil (x ∷ Γ) = cong₂ _∷_ (M-id x) (substCxtAnil Γ)

substCxt≤Anil : {m n : ℕ} → (Γ : Cxt {m} n) → (m≤m : m ≤ m) → substCxt≤ anil m≤m Γ ≡ Γ
substCxt≤Anil [] m≤m = refl
substCxt≤Anil (x ∷ Γ) m≤m = cong₂ _∷_ (substAnilm≤m x m≤m) (substCxt≤Anil Γ m≤m)

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

-- lookup と liftCxt は順番を変えても良い
lookupLiftCxtCommute : (m' : ℕ) {n m : ℕ} (x : Fin n) (Γ : Cxt {m} n) →
                       liftType m' (lookup x Γ) ≡ lookup x (liftCxt m' Γ)
lookupLiftCxtCommute m' {zero} () Γ
lookupLiftCxtCommute m' {suc n} zero (t ∷ Γ) = refl
lookupLiftCxtCommute m' {suc n} (suc x) (t ∷ Γ) = lookupLiftCxtCommute m' x Γ

-- WellTypedTerm を lift する
liftWTerm : (k : ℕ) {m n : ℕ} → {Γ : Cxt {m} n} → {t : Type m} → WellTypedTerm Γ t →
            WellTypedTerm (liftCxt k Γ) (liftType k t)
liftWTerm k {Γ = Γ} (Var x) rewrite lookupLiftCxtCommute k x Γ = Var x
liftWTerm k (Lam t w) = Lam (liftType k t) (liftWTerm k w)
liftWTerm k (App w1 w2) = App (liftWTerm k w1) (liftWTerm k w2)
liftWTerm k (Fst w) = Fst (liftWTerm k w)
liftWTerm k (Snd w) = Snd (liftWTerm k w)
liftWTerm k (Cons w1 w2) = Cons (liftWTerm k w1) (liftWTerm k w2)

-- lookup と substCxt≤ は順番を変えても良い
lookupSubst≤CxtCommute : {n m m' m'' : ℕ} (x : Fin n) (Γ : Cxt {m} n) → (σ : AListType m' m'') →
                       (m≤m' : m ≤ m') →
                       substType≤ σ m≤m' (lookup x Γ) ≡ lookup x (substCxt≤ σ m≤m' Γ)
lookupSubst≤CxtCommute {zero} () Γ σ m≤m'
lookupSubst≤CxtCommute {suc n} zero (t ∷ Γ) σ m≤m' = refl
lookupSubst≤CxtCommute {suc n} (suc x) (t ∷ Γ) σ m≤m' = lookupSubst≤CxtCommute x Γ σ m≤m'

-- substWTerm≤ σ w : w に σ を適用した WellTypedTerm を返す
substWTerm≤ : {m m' m'' n : ℕ} → {Γ : Cxt {m} n} → {t : Type m} →
             (σ : AListType m' m'') → (m≤m' : m ≤ m') → WellTypedTerm Γ t →
             WellTypedTerm (substCxt≤ σ m≤m' Γ) (substType≤ σ m≤m' t)
substWTerm≤ {Γ = Γ} σ m≤m' (Var x) rewrite lookupSubst≤CxtCommute x Γ σ m≤m' = Var x
substWTerm≤ σ m≤m' (Lam t w) = Lam (substType≤ σ m≤m' t) (substWTerm≤ σ m≤m' w)
substWTerm≤ σ m≤m' (App w1 w2) = App (substWTerm≤ σ m≤m' w1) (substWTerm≤ σ m≤m' w2)
substWTerm≤ σ m≤m' (Fst w) = Fst (substWTerm≤ σ m≤m' w)
substWTerm≤ σ m≤m' (Snd w) = Snd (substWTerm≤ σ m≤m' w)
substWTerm≤ σ m≤m' (Cons w1 w2) = Cons (substWTerm≤ σ m≤m' w1) (substWTerm≤ σ m≤m' w2)
