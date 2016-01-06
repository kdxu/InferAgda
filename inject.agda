module inject where

open import nat

open import Data.Nat hiding (fold)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Fin hiding (_+_; _≤_; fold)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

---------------------------------------------------------------

-- inject+' n x : x の型を n だけ持ち上げる
-- Fin の inject+ は結論部が Fin (m + m')
inject+' : ∀ m' {m} → Fin m → Fin (m' + m)
inject+' zero x = x
inject+' (suc m) x = inject₁ (inject+' m x)

inject+'' : ∀ m' {m} → Fin m → Fin (m' + m)
inject+'' m' {.(suc m)} (zero {n = m}) rewrite +-suc m' m = zero {n = m' + m}
inject+'' m' {.(suc m)} (suc {n = m} x) rewrite +-suc m' m = suc (inject+'' m' x)

private
  inject+''zero : ∀ {m} → (x : Fin m) → inject+'' zero x ≡ x
  inject+''zero zero = refl
  inject+''zero (suc x) = cong suc (inject+''zero x)

  inject+''suc : ∀ m' {m} → (x : Fin m) → inject+'' (suc m') x ≡ inject₁ (inject+'' m' x)
  inject+''suc m' {.(suc m)} (zero {n = m}) rewrite +-suc m' m = refl
  inject+''suc m' {.(suc m)} (suc {n = m} x) rewrite +-suc m' m = cong suc (inject+''suc m' x)

  inject+equal : ∀ m' {m} → (x : Fin m) → inject+' m' x ≡ inject+'' m' x
  inject+equal zero x = sym (inject+''zero x)
  inject+equal (suc m') x rewrite inject+''suc m' x = cong inject₁ (inject+equal m' x)

inject≤Trans :  {m n l : ℕ} → (leq : n ≤ l) → (leq' : m ≤ n) → (leq'' : m ≤ l) → (x : Fin m)
    → inject≤ x leq'' ≡ inject≤ (inject≤ x leq') leq
inject≤Trans z≤n () leq'' zero
inject≤Trans (s≤s leq) (s≤s leq') (s≤s leq'') zero = refl
inject≤Trans z≤n () leq'' (suc x)
inject≤Trans (s≤s leq) (s≤s leq') (s≤s leq'') (suc x) = cong suc (inject≤Trans leq leq' leq'' x)

-- injectm≤m x m≤m : x を m≤m で増やしても x のまま
injectm≤m : {m : ℕ} → (x : Fin m) → (m≤m : m ≤ m) → inject≤ x m≤m ≡ x
injectm≤m zero (s≤s m≤m) = refl
injectm≤m (suc x) (s≤s m≤m) = cong suc (injectm≤m x m≤m)

private
  inject≤zero : {m m' : ℕ} → (1+m≤1+m' : suc m ≤ suc m') → inject≤ (zero {n = m}) 1+m≤1+m' ≡ (zero {n = m'})
  inject≤zero (s≤s 1+m≤1+m') = refl

  inject≤add2 : {m m' : ℕ} → (k : ℕ) → (k+m≤m' : k + m ≤ m') → (m≤m' : m ≤ m') →
        (x : Fin m) →
        inject≤ (inject+'' k x) k+m≤m' ≡ inject≤ x m≤m'
  inject≤add2 {.(suc m)} {.(suc m')} k k+m≤m' (s≤s {m = m} {n = m'} m≤m') (zero {n = .m})
    rewrite +-suc k m = inject≤zero k+m≤m'
  inject≤add2 {.(suc m)} {.(suc m')} k k+m≤m' (s≤s {m = m} {n = m'} m≤m') (suc x)
    rewrite +-suc k m = eq k+m≤m'
    where eq : (k+m≤m' : suc (k + m) ≤ suc m') → inject≤ (suc (inject+'' k x)) k+m≤m' ≡ suc (inject≤ x m≤m')
          eq (s≤s k+m≤m'') = cong suc (inject≤add2 k k+m≤m'' m≤m' x)

inject≤add : {m m' : ℕ} → (k : ℕ) → (k+m≤m' : k + m ≤ m') → (m≤m' : m ≤ m') →
        (x : Fin m) →
        ((λ x → inject≤ x k+m≤m') ∘ inject+' k) x ≡ inject≤ x m≤m'
inject≤add k k+m≤m' m≤m' x
  rewrite inject+equal k x = inject≤add2 k k+m≤m' m≤m' x

-- inject≤′
inject≤′ : ∀ {m m'} → Fin m → m ≤′ m' → Fin m'
inject≤′ x ≤′-refl = x
inject≤′ x (≤′-step m≤′m') = inject₁ (inject≤′ x m≤′m')

inject≤′-refl : ∀ {m} (i : Fin m) (m≤′m : m ≤′ m) → inject≤′ i m≤′m ≡ i
inject≤′-refl i ≤′-refl = refl
inject≤′-refl i (≤′-step m≤′m) with m<′m'→¬m'<′m m≤′m m≤′m
... | ()

private 
  inject≤′-zero : ∀ {m1 m2}
                    → (leq : m1 ≤′ m2)
                    → inject≤′ zero (s≤′s leq) ≡ zero
  inject≤′-zero ≤′-refl = refl
  inject≤′-zero (≤′-step leq) rewrite inject≤′-zero leq = refl

  inject≤′-suc : ∀ {m1 m2}
                    → (a : Fin m1)
                    → (leq : m1 ≤′ m2)
                    → inject≤′ (suc a) (s≤′s leq) ≡ suc (inject≤′ a leq)
  inject≤′-suc a ≤′-refl = refl
  inject≤′-suc a (≤′-step leq) rewrite inject≤′-suc a leq = refl

inject≤≡≤' : ∀ {m1 m2}
                    → (leq : m1 ≤ m2)
                    → (a : Fin m1)
                    → inject≤′ a (≤⇒≤′ leq) ≡ inject≤ a leq
inject≤≡≤' z≤n ()
inject≤≡≤' {.(suc m)} {.(suc n)} (s≤s {m = m} {n = n} leq) (zero {n = .m}) = inject≤′-zero (≤⇒≤′ leq)
inject≤≡≤' {.(suc m)} {.(suc n)} (s≤s {m = m} {n = n} leq) (suc {n = .m} a)
  rewrite inject≤′-suc a (≤⇒≤′ leq) = cong suc (inject≤≡≤' leq a)
