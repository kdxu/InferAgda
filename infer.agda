module infer where

open import Data.Nat
open import Data.Vec 
open import Data.Product
open import Data.Fin hiding (_+_; _≤_)
open import Data.Maybe
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Nat.Properties
open import Algebra.Structures
private module M = IsCommutativeSemiring
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□)
open import Relation.Binary.HeterogeneousEquality
  renaming (sym to hsym; trans to htrans; cong to hcong; cong₂ to hcong₂; subst to hsubst; subst₂ to hsubst₂; refl to hrefl)
open import mgu
open import term

--------------------------------------------------------------------------------

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

infer : (m : ℕ) → {n : ℕ} → (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m'' ∈ ℕ ]
                Σ[ m' ∈ ℕ ] 
                Σ[ m≤m'' ∈ m ≤ m'' ] 
                Σ[ σ ∈ AListType m'' m' ] 
                Σ[ τ ∈ Type m' ]
                WellTypedTerm (substCxt≤ σ m≤m'' Γ) τ) 
infer m Γ (Var x) = just (m , (m , ((n≤m+n 0 m) , (anil , ((lookup x
         Γ) , VarX)))))
   where
     VarX : WellTypedTerm (substCxt≤ anil (n≤m+n 0 m) Γ) (lookup x Γ)
     VarX = {!!}
infer m Γ (Lam s) with infer (suc m) (TVar (fromℕ m) ∷ liftCxt 1 Γ)
         s
infer m Γ (Lam s) | just  (m'' , m' , leq , σ , t , w)  = just (m'' , (m' , (≤⇒pred≤ (suc m) m'' leq , (σ , (tx ⇒ t , {!!})))))
  where
    tx : Type m'
    tx = substType≤ σ leq (TVar (fromℕ m))
infer m Γ (Lam s) | nothing = nothing
infer m Γ (App s1 s2) with infer m Γ s1
infer m Γ (App s1 s2)  | just (m'' , m' , leq , σ , t , w) with
         infer m' (substCxt σ (liftCxt≤ leq Γ)) s2
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | nothing = nothing
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just
         (m1'' , m1' , leq1 , σ1 , t1 , w1) with mgu (liftType 1
         (substType σ1 (liftType≤ leq1 t))) (liftType 1 t1 ⇒ TVar
         (fromℕ m1'))
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just (m1'' , m1' , leq1 , σ1 , t1 , w1) | just (m2 , σ2) = {!!}
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just (m1'' , m1' , leq1 , σ1 , t1 , w1) | nothing = nothing
infer m Γ (App s1 s2) | nothing = nothing
infer m Γ (Fst t) = {!!}
infer m Γ (Snd t) = {!!}
infer m Γ (Cons t1 t2) = {!!}

{-infer m Γ (Var x) = just (m , m , n≤m+n 0 m , anil , lookup x Γ , VarX)
  where
    VarX : WellTypedTerm (substCxt≤ anil (n≤m+n 0 m) Γ) (lookup x Γ)
    VarX = {!!}
infer m Γ (Lam s) with infer (suc m) (TVar (fromℕ m) ∷ liftCxt 1 Γ) s
infer m Γ (Lam s) | nothing = nothing
infer m Γ (Lam s) | just (m'' , m' , leq , σ , t , w)= just (m'' , (m' , (≤⇒pred≤ (suc m) m'' leq , (σ , (tx ⇒ t , {!!})))))
  where  tx : Type m'
         tx = substType≤ σ leq (TVar (fromℕ m))
infer m Γ (App s1 s2)  with infer m Γ s1
infer m Γ (App s1 s2) | nothing = nothing
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) with  infer m' (substCxt σ (liftCxt≤ leq Γ)) s2
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | nothing = nothing
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just (m1'' , m1' , leq1 , σ1 , t1 , w1) with mgu (liftType 1 (substType σ1 (liftType≤ leq1 t))) (liftType 1 t1 ⇒ TVar (fromℕ m1'))
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just (m1'' , m1' , leq1 , σ1 , t1 , w1) | just (m2 , σ2)
          = just (suc m1' ∸ m1' + (m1'' ∸ m' + m'') , (m2 , (leq2 , (σ2 +⟨ n≤m+n 1 m1' ⟩ (σ1 +⟨ leq1 ⟩ σ) , (substType σ2 (TVar (fromℕ m1')) , {!!})))))
          where
           leq2 : m ≤ suc m1' ∸ m1' + (m1'' ∸ m' + m'')
           leq2 = start
                m
              ≤⟨ leq ⟩
                m''
              ≤⟨ n≤m+n (m1'' ∸ m') m'' ⟩
                m1'' ∸ m' + m''
              ≤⟨ n≤m+n (suc m1' ∸ m1') (m1'' ∸ m' + m'') ⟩
                suc m1' ∸ m1' + (m1'' ∸ m' + m'')
               □

infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just (m1'' , m1' , leq1 , σ1 , t1 , w1) | nothing = nothing

infer m Γ (Fst s) = {!!}
infer m Γ (Snd s) = {!!}
infer m Γ (Cons a b) = {!!}

-}
