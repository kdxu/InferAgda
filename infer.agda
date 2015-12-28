module infer where

open import Data.Nat
open import Data.Vec hiding (_++_)
open import Data.Vec.Properties
open import Data.Product
open import Data.Fin hiding (_+_; _≤_)
open import Data.Maybe
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning renaming (_≡⟨_⟩_ to _≡⟪_⟫_ )
open import Data.Nat.Properties
open import Algebra.Structures
open import Function using (_∘_)
open import Relation.Binary hiding (_⇒_)
private module M = IsCommutativeSemiring
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□ )
open import Relation.Binary.HeterogeneousEquality
  renaming (sym to hsym; trans to htrans; cong to hcong; cong₂ to hcong₂; subst to hsubst; subst₂ to hsubst₂; refl to hrefl)
open import mgu
open import term

--------------------------------------------------------------------------------

liftInject≤ :  ∀ {m m1 m1' m2 m2'}
                    → (σ1 : AListType m1' m1)
                    → (leq2 : m1 ≤ m2')
                    → (leq2' : m1' ≤ m2' ∸ m1 + m1')
                    → (a : Fin m1')
                    → ((mvar-map (mvar-sub (liftAList≤ leq2 σ1)) ∘ M ∘ (λ x → inject≤ x leq2')) a
              ≡ (mvar-map (M ∘ (λ x → inject≤ x leq2)) ∘ mvar-sub σ1) a)
liftInject≤ σ1 leq2 leq2' a =
              begin
                (mvar-map (mvar-sub (liftAList≤ leq2 σ1)) ∘ M ∘ (λ x → inject≤ x leq2')) a
              ≡⟪ {!   !} ⟫
                (mvar-map (M ∘ (λ x → inject≤ x leq2)) ∘ mvar-sub σ1) a
              ∎

substTypeTrans : ∀ {m m1 m1' m2 m2'}
                    → (x : Type m)
                    → (σ1 : AListType m1' m1)
                    → (σ2 : AListType m2'  m2)
                    → (σ' : AListType (m2' ∸ m1 + m1')  m2)
                    → (leq1 : m ≤ m1')
                    → (leq2 : m1 ≤ m2')
                    →  (leq' : m ≤ m2' ∸ m1 + m1')
                    → ( σ' ≡ σ2 +⟨ leq2 ⟩ σ1 )
                    → substType≤ σ' leq' x ≡ substType≤ σ2 leq2 (substType≤ σ1 leq1 x)
substTypeTrans {m} {m1} {m1'} {m2} {m2'} t σ1 σ2 σ' leq1 leq2 leq' eq =
      begin
        substType≤ σ' leq' t
      ≡⟪ cong (λ x₁ → mvar-map (mvar-sub x₁) (mvar-map-fin (λ x → inject≤ x leq') t)) eq ⟫
        mvar-map (mvar-sub (σ2 +⟨ leq2 ⟩ σ1)) (mvar-map-fin (λ x → inject≤ x leq') t)
      ≡⟪ cong (λ x → mvar-map (mvar-sub (σ2 +⟨ leq2 ⟩ σ1)) (mvar-map-fin x t)) (inject≤Trans' leq2' leq1 leq') ⟫
        mvar-map (mvar-sub (σ2 +⟨ leq2 ⟩ σ1)) (mvar-map-fin ((λ x → inject≤ x leq2') ∘ (λ x → inject≤ x leq1)) t)
      ≡⟪ cong (λ x → mvar-map (mvar-sub (σ2 +⟨ leq2 ⟩ σ1)) x)
              (sym (mvar-map-fin-add (λ x → inject≤ x leq2') (λ x → inject≤ x leq1) t)) ⟫
        mvar-map (mvar-sub (σ2 +⟨ leq2 ⟩ σ1))
                 (mvar-map-fin (λ x → inject≤ x leq2') (mvar-map-fin (λ x → inject≤ x leq1) t))
      ≡⟪ refl ⟫
        mvar-map (mvar-sub (σ2 ++ (liftAList≤ leq2 σ1)))
                 (mvar-map-fin (λ x → inject≤ x leq2') (mvar-map-fin (λ x → inject≤ x leq1) t))
      ≡⟪ cong (λ f → f (mvar-map-fin (λ x → inject≤ x leq2') (mvar-map-fin (λ x → inject≤ x leq1) t)))
              (mvar-sub-++-commute σ2 (liftAList≤ leq2 σ1)) ⟫
        (mvar-map (mvar-sub σ2) ∘ (mvar-map (mvar-sub (liftAList≤ leq2 σ1))))
                  (mvar-map-fin (λ x → inject≤ x leq2') (mvar-map-fin (λ x → inject≤ x leq1) t))
      ≡⟪ refl ⟫
        mvar-map (mvar-sub σ2) (mvar-map (mvar-sub (liftAList≤ leq2 σ1))
                 (mvar-map-fin (λ x → inject≤ x leq2') (mvar-map-fin (λ x → inject≤ x leq1) t)))
      ≡⟪ cong (mvar-map (mvar-sub σ2))
              (fold-add2 (mvar-sub (liftAList≤ leq2 σ1)) (M ∘ (λ x → inject≤ x leq2'))
                         (mvar-map-fin (λ x → inject≤ x leq1) t)) ⟫
        mvar-map (mvar-sub σ2)
          (mvar-map (mvar-map (mvar-sub (liftAList≤ leq2 σ1)) ∘ (M ∘ (λ x → inject≤ x leq2')))
            (mvar-map-fin (λ x → inject≤ x leq1) t))
            ≡⟪ cong (λ f → mvar-map (mvar-sub σ2) (mvar-map f (mvar-map-fin (λ x → inject≤ x leq1) t)))
                    (ext (liftInject≤ σ1 leq2 leq2')) ⟫
              mvar-map (mvar-sub σ2)
                (mvar-map (mvar-map (M ∘ (λ x → inject≤ x leq2)) ∘ (mvar-sub σ1))
                  (mvar-map-fin (λ x → inject≤ x leq1) t))
      ≡⟪ cong (mvar-map (mvar-sub σ2))
                    (sym (fold-add2 (M ∘ (λ x → inject≤ x leq2)) (mvar-sub σ1) (mvar-map-fin (λ x → inject≤ x leq1) t))) ⟫
              mvar-map (mvar-sub σ2) (mvar-map-fin (λ x → inject≤ x leq2)
               (mvar-map (mvar-sub σ1) (mvar-map-fin (λ x → inject≤ x leq1) t)))
      ≡⟪ refl ⟫
              substType≤ σ2 leq2 (substType≤ σ1 leq1 t)
      ∎
              where leq2' : m1' ≤ m2' ∸ m1 + m1'
                    leq2' = n≤m+n (m2' ∸ m1) m1'

substCxtTrans : ∀ {m n m1 m1' m2 m2'}
                    → (Γ : Cxt {m} n)
                    → (σ1 : AListType m1' m1)
                    → (σ2 : AListType m2'  m2)
                    → (σ' : AListType (m2' ∸ m1 + m1')  m2)
                    → (leq1 : m ≤ m1') → (leq2 : m1 ≤ m2')
                    →  (leq' : m ≤ m2' ∸ m1 + m1')
                    → ( σ' ≡ σ2 +⟨ leq2 ⟩ σ1 )
                    → (substCxt≤ σ' leq' Γ) ≡ (substCxt≤ σ2 leq2 (substCxt≤ σ1 leq1 Γ))
substCxtTrans [] σ1 σ2 σ' leq1 leq2 leq' eq = refl
substCxtTrans (x ∷ Γ) σ1 σ2 σ' leq1 leq2 leq' eq =
          cong₂ _∷_ (substTypeTrans x σ1 σ2 σ' leq1 leq2 leq' eq) (substCxtTrans Γ σ1 σ2 σ' leq1 leq2 leq' eq)

substCxt≤+1 : {m m' m''  n : ℕ} → (Γ : Cxt {m} n)
                → (leq : suc m ≤ m'')
                → (leq' : m ≤ m'')
                → (σ : AListType m'' m')
                → substCxt≤ σ leq (liftCxt 1 Γ) ≡ substCxt≤ σ leq' Γ
substCxt≤+1 [] leq leq' σ = refl
substCxt≤+1 (x ∷ Γ) leq leq' σ = cong₂ _∷_ (cong (substType σ) (liftType≤add 1 x leq leq')) (substCxt≤+1 Γ leq leq' σ)

infer : (m : ℕ) → {n : ℕ} → (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m'' ∈ ℕ ]
                Σ[ m' ∈ ℕ ]
                Σ[ m≤m'' ∈ m ≤ m'' ]
                Σ[ σ ∈ AListType m'' m' ]
                Σ[ τ ∈ Type m' ]
                WellTypedTerm (substCxt≤ σ m≤m'' Γ) τ)
infer m Γ (Var x) = just (m , (m , ((n≤m+n 0 m) , (anil , ((lookup x Γ) , VarX)))))
   where
     VarX : WellTypedTerm (substCxt≤ anil (n≤m+n 0 m) Γ) (lookup x Γ)
     VarX rewrite substCxt≤Anil Γ (n≤m+n 0 m) = Var x
infer m Γ (Lam s) with infer (suc m) (TVar (fromℕ m) ∷ liftCxt 1 Γ)
         s
... | just  (m'' , m' , leq , σ , t , w) =
  just (m'' , (m' , (leq' , (σ , (tx ⇒ t , LamS)))))
  where
    leq' : m ≤ m''
    leq' = DecTotalOrder.trans decTotalOrder (n≤m+n 1 m) leq

    tx : Type m'
    tx = substType≤ σ leq (TVar (fromℕ m))

    LamS : WellTypedTerm (substCxt≤ σ leq' Γ) (tx ⇒ t)
    LamS = Lam (mvar-sub σ (inject≤ (fromℕ m) leq)) w'
     where
        w' : WellTypedTerm (tx ∷ substCxt≤ σ leq' Γ) t
        w' = subst (λ l → WellTypedTerm (tx ∷ l) t) eq w
           where eq : substCxt≤ σ leq (liftCxt 1 Γ) ≡ substCxt≤ σ leq' Γ
                 eq = substCxt≤+1 Γ leq leq' σ

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
              s1' : WellTypedTerm (substCxt≤ (σ2 +⟨ (n≤m+n 1 m1') ⟩ (σ1 +⟨ leq1 ⟩ σ)) leq2 Γ) (substType σ2 {! substCxt≤ σ m≤m'' Γ) τ  !})
              s1' = {!   !}
              s2' : WellTypedTerm {!   !} {!   !}
              s2' = {!   !}

infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just (m1'' , m1' , leq1 , σ1 , t1 , w1) | nothing = nothing
infer m Γ (App s1 s2) | nothing = nothing
infer m Γ (Fst s)
    with infer m Γ s
... | nothing = nothing
... | just (m1' , m1 , m≤m1' , σ , t1 , w)
    with mgu2  (liftType 2 t1)  (liftType 1 (TVar (fromℕ m1)) ∏ ((TVar (fromℕ (suc m1)))))
... | nothing = nothing
... | just (m2 , σ2 , eq2) =
    just (suc (suc m1) ∸ m1 + m1' , (m2 , (leq' , (σ' , ( τ , FstW)))))
    where
          leq' : m ≤ (suc (suc m1) ∸ m1) + m1'
          leq' =　start
                      m
                    ≤⟨ m≤m1' ⟩
                      m1'
                    ≤⟨ ≡-to-≤ m1' m1' refl ⟩
                      zero + m1'
                    ≤⟨ m≤m'≡k'+m≤k+m zero (suc (suc m1) ∸ m1) m1' z≤n ⟩
                      (suc (suc m1) ∸ m1) + m1'
                  □

          m1≤2+m1 : (m1 ≤ suc (suc m1))
          m1≤2+m1 = ≤-steps 2 (m≤m m1)

          τ : Type m2
          τ = substType σ2 (liftType 1 (TVar (fromℕ m1)))
          τ' : Type m2
          τ' = substType σ2 (TVar (fromℕ (suc m1)))
          σ' : AListType (suc (suc m1) ∸ m1 + m1') m2
          σ' = σ2 +⟨ m1≤2+m1 ⟩ σ
          w' : WellTypedTerm (substCxt≤ σ m≤m1' Γ) t1
          w' = w
-- leq' : m ≤ (suc (suc m1) ∸ m1) + m1'
-- m1≤2+m1 : (m1 ≤ suc (suc m1))
-- m≤m1' : m ≤ m1'
          Γ1≡Γ2 : (substCxt≤ σ' leq' Γ) ≡ (substCxt≤ σ2 m1≤2+m1 (substCxt≤ σ m≤m1' Γ))
          Γ1≡Γ2 = substCxtTrans Γ σ σ2 σ' m≤m1' m1≤2+m1 leq' refl
-- eq2 : substType σ (liftType 2 t1)  ≡ substType σ (liftType 1 (TVar (fromℕ m1)) ∏ ((TVar (fromℕ (suc m1)))))

          τ1≡τ2 : (τ ∏ τ') ≡ (substType≤ σ2 m1≤2+m1 t1)
          τ1≡τ2 = sym
                (begin
                  substType≤ σ2 m1≤2+m1 t1
                ≡⟪ cong (λ x → mvar-map (mvar-sub σ2) (mvar-map (M ∘ x) t1)) (ext (λ a → inject≤≡+ a (suc (suc zero)) (≤-step (≤-step (m≤m m1))))) ⟫
                  substType σ2 (liftType 2 t1)
                ≡⟪ eq2 ⟫
                  substType σ2 (liftType 1 (TVar (fromℕ m1))) ∏ substType σ2 (TVar (fromℕ (suc m1)))
                ∎)

          w2 : WellTypedTerm (substCxt≤ σ2 m1≤2+m1 (substCxt≤ σ m≤m1' Γ)) (substType≤ σ2 m1≤2+m1 t1)
          w2 = substWTerm≤ σ2 m1≤2+m1 w

          W : WellTypedTerm (substCxt≤ σ' leq' Γ) (τ ∏ τ')
          W rewrite τ1≡τ2 | Γ1≡Γ2 = w2

          FstW : WellTypedTerm (substCxt≤ σ' leq' Γ) τ
          FstW = Fst W
infer m Γ (Snd s) = {!   !}
infer m Γ (Cons t1 t2) = {!   !}
