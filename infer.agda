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

m≤m :  ∀ m →  m ≤ m
m≤m zero = z≤n
m≤m (suc m) = s≤s (m≤m m)

sucm≤m'→m≤m' :  ∀{ m m'} → (suc m) ≤ m' → m ≤ m'
sucm≤m'→m≤m' {zero} {m'} x = z≤n
sucm≤m'→m≤m' {suc m} {zero} ()
sucm≤m'→m≤m' {suc m} {suc m'} (s≤s x) = s≤s (sucm≤m'→m≤m' {m} {m'} x)

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
     VarX rewrite substCxt≤Anil Γ (n≤m+n 0 m) = Var x
infer m Γ (Lam s) with infer (suc m) (TVar (fromℕ m) ∷ liftCxt 1 Γ)
         s
infer m Γ (Lam s) | just  (m'' , m' , leq , σ , t , w)  = just (m'' , (m' , (≤⇒pred≤ (suc m) m'' leq , (σ , (tx ⇒ t , LamS)))))
  where

    tx : Type m'
    tx = substType≤ σ leq (TVar (fromℕ m))

    LamS : WellTypedTerm (substCxt≤ σ (≤⇒pred≤ (suc m) m'' leq) Γ) (tx ⇒ t)
    LamS = Lam (mvar-sub σ (inject≤ (fromℕ m) leq)) w'
     where
         leq' : m ≤ m''
         leq' = {!   !}
         w' : WellTypedTerm (tx ∷ substCxt≤ σ leq' Γ) t
         w' = subst (λ l → WellTypedTerm (tx ∷ l) t) eq w
           where eq : {!   !} ≡ substCxt≤ σ leq' Γ
                 eq = {!   !}


infer m Γ (Lam s) | nothing = nothing
infer m Γ (App s1 s2) with infer m Γ s1
infer m Γ (App s1 s2)  | just (m'' , m' , leq , σ , t , w) with
         infer m' (substCxt σ (liftCxt≤ leq Γ)) s2
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | nothing = nothing
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just
         (m1'' , m1' , leq1 , σ1 , t1 , w1) with mgu (liftType 1
         (substType σ1 (liftType≤ leq1 t))) (liftType 1 t1 ⇒ TVar
         (fromℕ m1'))
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just (m1'' , m1' , leq1 , σ1 , t1 , w1) | just (m2 , σ2) = just (suc m1' ∸ m1' + (m1'' ∸ m' + m'') , (m2 , (leq2 , (σ2 +⟨ n≤m+n 1 m1' ⟩ (σ1 +⟨ leq1 ⟩ σ) , (substType σ2 (TVar (fromℕ m1')) , AppS1S2)))))
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
    AppS1S2 : WellTypedTerm (substCxt≤ (σ2 +⟨ n≤m+n 1 m1' ⟩ (σ1 +⟨ leq1 ⟩ σ)) leq2 Γ) (substType σ2 (TVar (fromℕ m1')))
    AppS1S2 = App s1' s2'
            where
              s1' : WellTypedTerm {!   !} {!   !}
              s1' = {!   !}
              s2' : WellTypedTerm {!   !} {!   !}
              s2' = {!   !}



infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just (m1'' , m1' , leq1 , σ1 , t1 , w1) | nothing = nothing
infer m Γ (App s1 s2) | nothing = nothing
infer m Γ (Fst t) = {!   !}
infer m Γ (Snd t) = {!    !}
infer m Γ (Cons t1 t2) = {!    !}
