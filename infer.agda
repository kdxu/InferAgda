module infer where

open import Data.Unit using (tt)
open import Data.Nat
open import Data.Vec hiding (_++_)
open import Data.Vec.Properties
open import Data.Product
open import Data.Fin hiding (_+_; _≤_)
open import Data.Maybe
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Nat.Properties
open import Algebra.Structures
open import Function using (_∘_)
open import Relation.Binary hiding (_⇒_)
private module M = IsCommutativeSemiring
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□ ; _≡⟨_⟩_ to _≡⟪_⟫_ )
-- open import Relation.Binary.HeterogeneousEquality
--   renaming (sym to hsym; trans to htrans; cong to hcong; cong₂ to hcong₂; subst to hsubst; subst₂ to hsubst₂; refl to hrefl)
open import mgu
open import term

--------------------------------------------------------------------------------

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

    eq : substCxt≤ σ leq (liftCxt 1 Γ) ≡ substCxt≤ σ leq' Γ
    eq = substCxt≤+1 Γ leq leq' σ

    w' : WellTypedTerm (tx ∷ substCxt≤ σ leq' Γ) t
    w' = subst (λ l → WellTypedTerm (tx ∷ l) t) eq w
    LamS : WellTypedTerm (substCxt≤ σ leq' Γ) (tx ⇒ t)
    LamS = Lam (mvar-sub σ (inject≤ (fromℕ m) leq)) w'

infer m Γ (Lam s) | nothing = nothing
infer m Γ (App s1 s2) with infer m Γ s1
... | just (m1'' , m1' , leq1 , σ1 , t1 , w1) with
         infer m1' (substCxt σ1 (liftCxt≤ leq1 Γ)) s2
... | nothing = nothing
... | just (m2'' , m2' , leq2 , σ2 , t2 , w2)
    with mgu2  (liftType 1 (substType σ2 (liftType≤ leq2 t1)))
          (liftType 1 t2 ⇒ TVar (fromℕ m2'))
... | just (m3' , σ3 , eq) = just (m3'' , (m3' , (leq' , (σ' , (t' , AppS1S2)))))
  where
  m3'' : ℕ
  m3'' = suc m2' ∸ m2' + (m2'' ∸ m1' + m1'')
  leq' : m ≤ suc m2' ∸ m2' + (m2'' ∸ m1' + m1'')
  leq' = start
              m
            ≤⟨ leq1 ⟩
              m1''
            ≤⟨ n≤m+n (m2'' ∸ m1') m1'' ⟩
              m2'' ∸ m1' + m1''
            ≤⟨ n≤m+n (suc m2' ∸ m2') (m2'' ∸ m1' + m1'') ⟩
              suc m2' ∸ m2' + (m2'' ∸ m1' + m1'')
             □

  σ' : AListType (suc m2' ∸ m2' + (m2'' ∸ m1' + m1'')) m3'
  σ' = σ3 +⟨ ≤-step (m≤m m2') ⟩ (σ2 +⟨ leq2 ⟩ σ1)
  t' : Type m3'
  t' = substType σ3 (TVar (fromℕ m2'))

  s1' : WellTypedTerm (substCxt≤ σ3 (≤-step (m≤m m2')) (substCxt≤ σ2 leq2 (substCxt σ1 (liftCxt≤ leq1 Γ)))) (substType≤ σ3 (≤-step (m≤m m2')) (substType≤ σ2 leq2 t1))
  s1' = substWTerm≤ σ3 (≤-step (m≤m m2')) (substWTerm≤ σ2 leq2 w1)

  s2' : WellTypedTerm (substCxt≤ σ3 (≤-step (m≤m m2')) (substCxt≤ σ2 leq2 (substCxt σ1 (liftCxt≤ leq1 Γ)))) (substType≤ σ3 (≤-step (m≤m m2')) t2)
  s2' = substWTerm≤ σ3 (≤-step (m≤m m2')) w2

-- eq :  substType σ3 (liftType 1 (substType σ2 (liftType≤ leq2 t1))) ≡ substType σ3 (liftType 1 t2 ⇒ TVar (fromℕ m2'))
-- substType σ3 (liftType 1 (substType σ2 (liftType≤ leq2 t1))) ≡  substType (σ3 +⟨ (≤-step (m≤m m2')) ⟩ σ2) t1
-- 示すのは substType≤ σ3 (≤-step (m≤m m2')) (substType≤ σ2 leq2 t1) ≡ substType σ3 (liftType 1 (substType σ2 (liftType≤ leq2 t1)))
  t1≡t2 : substType σ3 (liftType 1 t2 ⇒ TVar (fromℕ m2')) ≡ substType≤ σ3 (≤-step (m≤m m2')) (substType≤ σ2 leq2 t1)
  t1≡t2  =
        begin
          substType σ3 (liftType 1 t2 ⇒ TVar (fromℕ m2'))
        ≡⟨ sym eq ⟩
          substType σ3 (liftType 1 (substType σ2 (liftType≤ leq2 t1)))
        ≡⟨ sym (substType≤≡n 1 (substType σ2 (liftType≤ leq2 t1)) (≤-step (m≤m m2')) σ3) ⟩
          substType≤ σ3 (≤-step (m≤m m2')) (substType σ2 (liftType≤ leq2 t1))
        ≡⟨ refl ⟩
          substType≤ σ3 (≤-step (m≤m m2')) (substType≤ σ2 leq2 t1)
        ∎
  t3≡t4 :(substType σ3 (liftType 1 t2)) ≡ (substType≤ σ3 (≤-step (m≤m m2')) t2)
  t3≡t4 = sym (substType≤≡n 1 t2 (≤-step (m≤m m2')) σ3)

  Γ1≡Γ2 : (substCxt≤ σ' leq' Γ) ≡ (substCxt≤ σ3 (≤-step (m≤m m2')) (substCxt≤ σ2 leq2 (substCxt σ1 (liftCxt≤ leq1 Γ))))
  Γ1≡Γ2 =
        begin
        (substCxt≤ σ' leq' Γ)
        ≡⟨ substCxtTrans Γ (σ2 +⟨ leq2 ⟩ σ1) σ3 σ' (≤-trans leq1 (n≤m+n (m2'' ∸ m1') m1'')) (≤-step (m≤m m2')) leq' refl ⟩
        (substCxt≤ σ3 (≤-step (m≤m m2')) (substCxt≤ (σ2 +⟨ leq2 ⟩ σ1) (≤-trans leq1 (n≤m+n (m2'' ∸ m1') m1'')) Γ))
        ≡⟨ cong (λ x → substCxt≤ σ3 (≤-step (m≤m m2')) x) (substCxtTrans Γ σ1 σ2 (σ2 +⟨ leq2 ⟩ σ1) leq1 leq2 (≤-trans leq1 (n≤m+n (m2'' ∸ m1') m1'')) refl) ⟩
        (substCxt≤ σ3 (≤-step (m≤m m2')) (substCxt≤ σ2 leq2 (substCxt≤ σ1 leq1 Γ)))
        ≡⟨ refl ⟩
        (substCxt≤ σ3 (≤-step (m≤m m2')) (substCxt≤ σ2 leq2 (substCxt σ1 (liftCxt≤ leq1 Γ))))
        ∎

  S1 : WellTypedTerm (substCxt≤ σ' leq' Γ) (substType σ3 (liftType 1 t2 ⇒ TVar (fromℕ m2')))
  S1 rewrite t1≡t2 | Γ1≡Γ2 = s1'
  S2 : WellTypedTerm (substCxt≤ σ' leq' Γ) (substType σ3 (liftType 1 t2))
  S2 rewrite t3≡t4 | Γ1≡Γ2  = s2'

  AppS1S2 : WellTypedTerm (substCxt≤ σ' leq' Γ) t'
  AppS1S2 = App S1 S2

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
                ≡⟨ cong (λ x → mvar-map (mvar-sub σ2) (mvar-map (M ∘ x) t1)) (ext (λ a → inject≤≡+ a (suc (suc zero)) (≤-step (≤-step (m≤m m1))))) ⟩
                  substType σ2 (liftType 2 t1)
                ≡⟨ eq2 ⟩
                  substType σ2 (liftType 1 (TVar (fromℕ m1))) ∏ substType σ2 (TVar (fromℕ (suc m1)))
                ∎)

          w2 : WellTypedTerm (substCxt≤ σ2 m1≤2+m1 (substCxt≤ σ m≤m1' Γ)) (substType≤ σ2 m1≤2+m1 t1)
          w2 = substWTerm≤ σ2 m1≤2+m1 w

          W : WellTypedTerm (substCxt≤ σ' leq' Γ) (τ ∏ τ')
          W rewrite τ1≡τ2 | Γ1≡Γ2 = w2

          FstW : WellTypedTerm (substCxt≤ σ' leq' Γ) τ
          FstW = Fst W
infer m Γ (Snd s) with infer m Γ s
... | nothing = nothing
... | just (m1' , m1 , m≤m1' , σ , t1 , w)
    with mgu2  (liftType 2 t1)  (liftType 1 (TVar (fromℕ m1)) ∏ ((TVar (fromℕ (suc m1)))))
... | nothing = nothing
... | just (m2 , σ2 , eq2) = just (suc (suc m1) ∸ m1 + m1' , (m2 , (leq' , (σ' , (τ' , SndW)))))
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

          Γ1≡Γ2 : (substCxt≤ σ' leq' Γ) ≡ (substCxt≤ σ2 m1≤2+m1 (substCxt≤ σ m≤m1' Γ))
          Γ1≡Γ2 = substCxtTrans Γ σ σ2 σ' m≤m1' m1≤2+m1 leq' refl

          τ1≡τ2 : (τ ∏ τ') ≡ (substType≤ σ2 m1≤2+m1 t1)
          τ1≡τ2 = sym
                (begin
                  substType≤ σ2 m1≤2+m1 t1
                ≡⟨ cong (λ x → mvar-map (mvar-sub σ2) (mvar-map (M ∘ x) t1)) (ext (λ a → inject≤≡+ a (suc (suc zero)) (≤-step (≤-step (m≤m m1))))) ⟩
                  substType σ2 (liftType 2 t1)
                ≡⟨ eq2 ⟩
                  substType σ2 (liftType 1 (TVar (fromℕ m1))) ∏ substType σ2 (TVar (fromℕ (suc m1)))
                ∎)

          w2 : WellTypedTerm (substCxt≤ σ2 m1≤2+m1 (substCxt≤ σ m≤m1' Γ)) (substType≤ σ2 m1≤2+m1 t1)
          w2 = substWTerm≤ σ2 m1≤2+m1 w

          W : WellTypedTerm (substCxt≤ σ' leq' Γ) (τ ∏ τ')
          W rewrite τ1≡τ2 | Γ1≡Γ2 =  w2
          SndW : WellTypedTerm (substCxt≤ σ' leq' Γ) τ'
          SndW = Snd W

infer m Γ (Cons s1 s2) with infer m Γ s1
... | nothing = nothing
... |  just (m1' , m1 , leq1 , σ1 , t1 , w1 ) with infer m1 (substCxt≤ σ1 leq1 Γ) s2
... | nothing = nothing
... | just (m2' , m2 , leq2 , σ2 , t2 , w2 ) = just (m2' ∸ m1 + m1' , (m2 , (leq' , (σ2 +⟨ leq2 ⟩ σ1 , ((substType≤ σ2 leq2 t1 ∏ t2) , ConsS1S2)))))
        where
          leq' : m ≤ (m2' ∸ m1 + m1')
          leq' =  start
                    m
                  ≤⟨ leq1 ⟩
                    m1'
                  ≤⟨ ≤-steps (m2' ∸ m1) (m≤m m1') ⟩
                    ((m2' ∸ m1) + m1')
                  ≤⟨ ≡-to-≤ (m2' ∸ m1 + m1') (m2' ∸ m1 + m1') refl ⟩
                    (m2' ∸ m1 + m1')
                  □
          σ' : AListType (m2' ∸ m1 + m1') m2
          σ' = σ2 +⟨ leq2 ⟩ σ1
          s1' : WellTypedTerm (substCxt≤ σ2 leq2 (substCxt≤ σ1 leq1 Γ)) (substType≤ σ2 leq2 t1)
          s1' = substWTerm≤ σ2 leq2 w1
          Γ1≡Γ2 : (substCxt≤ σ' leq' Γ) ≡ (substCxt≤ σ2 leq2 (substCxt≤ σ1 leq1 Γ))
          Γ1≡Γ2 = substCxtTrans Γ σ1 σ2 σ' leq1 leq2 leq' refl
          S1 : WellTypedTerm (substCxt≤ σ' leq' Γ) (substType≤ σ2 leq2 t1)
          S1 rewrite Γ1≡Γ2 = s1'
          S2 : WellTypedTerm (substCxt≤ σ' leq' Γ) t2
          S2 rewrite Γ1≡Γ2 = w2
          ConsS1S2 : WellTypedTerm (substCxt≤ σ' leq' Γ) (substType≤ σ2 leq2 t1 ∏ t2)
          ConsS1S2 = Cons S1 S2
