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
open Relation.Binary.PropositionalEquality.≡-Reasoning renaming (_≡⟨_⟩_ to _≡⟪_⟫_ )
open import Data.Nat.Properties
open import Algebra.Structures
open import Function using (_∘_)
open import Relation.Binary hiding (_⇒_)
private module M = IsCommutativeSemiring
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□ )
-- open import Relation.Binary.HeterogeneousEquality
--   renaming (sym to hsym; trans to htrans; cong to hcong; cong₂ to hcong₂; subst to hsubst; subst₂ to hsubst₂; refl to hrefl)
open import mgu
open import term

--------------------------------------------------------------------------------

thickxynothing : {m : ℕ} → {x y : Fin (suc m)} →
        thick x y ≡ nothing → thick (inject₁ x) (inject₁ y) ≡ nothing
thickxynothing {x = zero} {zero} eq = refl
thickxynothing {x = zero} {suc y} ()
thickxynothing {zero} {suc ()} eq
thickxynothing {suc m} {suc x} {zero} ()
thickxynothing {suc m} {suc x} {suc y} eq with thick x y | inspect (thick x) y
thickxynothing {suc m} {suc x} {suc y} refl | nothing | [ eq2 ] rewrite eq2
  with thickxynothing {x = x} eq2
... | eq3 rewrite eq3 = refl
thickxynothing {suc m} {suc x} {suc y} () | just y' | [ _ ]

thickxyjust : {m : ℕ} → {x y : Fin (suc m)} → {y' : Fin m} →
        thick x y ≡ just y' → thick (inject₁ x) (inject₁ y) ≡ just (inject₁ y')
thickxyjust {x = zero} {zero} ()
thickxyjust {x = zero} {suc y} refl = refl
thickxyjust {zero} {suc x} {y} {()} eq
thickxyjust {suc m} {suc x} {zero} refl = refl
thickxyjust {suc m} {suc x} {suc y} eq with thick x y | inspect (thick x) y
thickxyjust {suc m} {suc x} {suc y} () | nothing | _
thickxyjust {suc m} {suc x} {suc y} refl | just y' | [ eq ] rewrite eq
  with thickxyjust {x = x} eq
... | eq2 rewrite eq2 = refl

mutual
  inject₁-liftAList1-commute-M : ∀ {m m' : ℕ}
                    → (σ : AListType m' m)
                    → (y : Fin m')
                    → mvar-map (mvar-sub (liftAList1 σ)) (M (inject₁ y))
                    ≡ mvar-map (λ u → M (inject₁ u)) ((mvar-sub σ) y)
  inject₁-liftAList1-commute-M anil z = refl
  inject₁-liftAList1-commute-M (σ asnoc t / x) y with thick x y | inspect (thick x) y
  inject₁-liftAList1-commute-M (σ asnoc t / x) y | nothing | [ eq ] rewrite eq -- x = y
    with thickxynothing {x = x} eq
  ... | eq2 rewrite eq2 | fold-add2 (λ x₁ → M (inject₁ x₁)) (mvar-sub σ) t
                        | fold-add2 (mvar-sub (liftAList1 σ)) (λ u → M (inject₁ u)) t
    = inject₁-liftAList1-commute σ t
  inject₁-liftAList1-commute-M (σ asnoc t / x) y | just y' | [ eq ] rewrite eq
    with thickxyjust {x = x} eq
  ... | eq2 rewrite eq2 = inject₁-liftAList1-commute-M σ y'

  inject₁-liftAList1-commute-F : ∀ {m m' : ℕ}
                    → (σ : AListType m' m)
                    → (d : ⟦ TypeDesc ⟧ (Fix TypeDesc m') )
                    → (r : ⟦ TypeDesc ⟧'
                            (λ t → mgu.fold F
                                      (λ z → mvar-map (mvar-sub (liftAList1 σ)) (M (inject₁ z))) t
                                     ≡
                                     mgu.fold F (λ z → mvar-map (λ u → M (inject₁ u)) (mvar-sub σ z)) t)
                            d)
                    → fmap TypeDesc
                         (mgu.fold F (λ z → mvar-map (mvar-sub (liftAList1 σ)) (M (inject₁ z)))) d
                    ≡ fmap TypeDesc
                         (mgu.fold F (λ z → mvar-map (λ u → M (inject₁ u)) ((mvar-sub σ) z))) d
  inject₁-liftAList1-commute-F σ (inj₁ (inj₁ tt)) r = refl
  inject₁-liftAList1-commute-F σ (inj₁ (inj₂ (d1 , d2))) (r1 , r2)
    = cong inj₁ (cong inj₂ (cong₂ _,_ r1 r2))
  inject₁-liftAList1-commute-F σ (inj₂ (d1 , d2)) (r1 , r2) = cong inj₂ (cong₂ _,_ r1 r2)

  inject₁-liftAList1-commute : ∀ {m m' : ℕ}
                    → (σ : AListType m' m)
                    → (t : Type m')
                    → mgu.fold F (λ z → mvar-map (mvar-sub (liftAList1 σ)) (M (inject₁ z))) t
                    ≡ mgu.fold F (λ z → mvar-map (λ u → M (inject₁ u)) ((mvar-sub σ) z)) t
  inject₁-liftAList1-commute σ =
    ind (λ t → mgu.fold F (λ z → mvar-map (mvar-sub (liftAList1 σ)) (M (inject₁ z))) t
              ≡ mgu.fold F (λ z → mvar-map (λ u → M (inject₁ u)) ((mvar-sub σ) z)) t)
        (λ d r → cong F (inject₁-liftAList1-commute-F σ d r))
        (λ x → inject₁-liftAList1-commute-M σ x)

inject≤-refl-ext : ∀ {D : Desc} {m : ℕ}
                    → (leq : m ≤ m)
                    → (λ x → M {D} (inject≤ x leq)) ≡ M
inject≤-refl-ext leq = ext (λ x → cong M (inject≤-refl x leq))

liftInject≤'' :  ∀ {m1 m1' m2'}
                    → (σ1 : AListType m1' m1)
                    → (leq2 : m1 ≤′ m2')
                    → (leq2' : m1' ≤′ m2' ∸ m1 + m1')
                    → (a : Fin m1')
                    → mvar-sub (liftAList≤' leq2 σ1) (inject≤′ a leq2')
                    ≡ mvar-map (M ∘ (λ x → inject≤′ x leq2)) (mvar-sub σ1 a)
liftInject≤'' {m1} {m1'} {.m1} σ1 ≤′-refl leq2' a
  rewrite n∸n≡0 m1 | inject≤′-refl a leq2'
  = begin
      mvar-sub σ1 a
    ≡⟪ sym (fold-id (mvar-sub σ1 a)) ⟫
      mgu.fold F M (mvar-sub σ1 a)
    ∎
liftInject≤'' {m1} {m1'} {.(suc m2')} σ1 (≤′-step {n = m2'} leq2) leq2' a
  rewrite +-∸-assoc 1 (≤′⇒≤ leq2)
  with m<′m'-step (n≤′m+n (m2' ∸ m1) m1') leq2'
... | (m1'≤′m2'∸m1+m1' , leq) rewrite leq
  = begin
      mvar-sub (liftAList1 (liftAList≤' leq2 σ1)) (inject₁ (inject≤′ a m1'≤′m2'∸m1+m1'))
{-  ≡⟪ refl ⟫
      mgu.fold F (mvar-sub (liftAList1 (liftAList≤' leq2 σ1)))
        (mgu.fold F (M ∘ inject₁)
          (M (inject≤′ a m1'≤′m2'∸m1+m1'))) -}
    ≡⟪ fold-add2 (mvar-sub (liftAList1 (liftAList≤' leq2 σ1))) (M ∘ inject₁) (M (inject≤′ a m1'≤′m2'∸m1+m1')) ⟫
{-    mgu.fold F (mvar-map (mvar-sub (liftAList1 (liftAList≤' leq2 σ1))) ∘ (M ∘ inject₁))
        (M (inject≤′ a m1'≤′m2'∸m1+m1'))
    ≡⟪ refl ⟫ -}
      (mvar-map (mvar-sub (liftAList1 (liftAList≤' leq2 σ1))) ∘ (M ∘ inject₁))
        (inject≤′ a m1'≤′m2'∸m1+m1')
    ≡⟪ inject₁-liftAList1-commute (liftAList≤' leq2 σ1) (M (inject≤′ a m1'≤′m2'∸m1+m1')) ⟫
      (mvar-map (M ∘ inject₁) ∘ (mvar-sub (liftAList≤' leq2 σ1)))
        (inject≤′ a m1'≤′m2'∸m1+m1')
{-  ≡⟪ refl ⟫
      mgu.fold F (mvar-map (M ∘ inject₁) ∘ (mvar-sub (liftAList≤' leq2 σ1)))
        (M (inject≤′ a m1'≤′m2'∸m1+m1'))
    ≡⟪ refl ⟫
      mgu.fold F (M ∘ inject₁)
        (mgu.fold F
          (mvar-sub (liftAList≤' leq2 σ1)) (M (inject≤′ a m1'≤′m2'∸m1+m1'))) -}
    ≡⟪ refl ⟫
      mgu.fold F (M ∘ inject₁)
        (mvar-sub (liftAList≤' leq2 σ1) (inject≤′ a m1'≤′m2'∸m1+m1'))
    ≡⟪ cong (mgu.fold F (M ∘ inject₁)) (liftInject≤'' σ1 leq2 m1'≤′m2'∸m1+m1' a) ⟫
      mgu.fold F (M ∘ inject₁)
        (mvar-map (M ∘ (λ x → inject≤′ x leq2)) (mvar-sub σ1 a))
    ≡⟪ refl ⟫
      mgu.fold F (M ∘ inject₁)
        (mgu.fold F (M ∘ (λ x → inject≤′ x leq2)) (mvar-sub σ1 a))
    ≡⟪ fold-add inject₁ (λ x → inject≤′ x leq2) (mvar-sub σ1 a) ⟫
      mgu.fold F (M ∘ (inject₁ ∘ λ x → inject≤′ x leq2)) (mvar-sub σ1 a)
    ≡⟪ refl ⟫
      mgu.fold F (λ x → M (inject₁ (inject≤′ x leq2))) (mvar-sub σ1 a)
    ∎


inject≤′-zero : ∀ {m1 m2}
                    → (leq : m1 ≤ m2)
                    → inject≤′ zero (≤⇒≤′ (s≤s leq)) ≡ zero
inject≤′-zero leq with (≤⇒≤′ (s≤s leq))
inject≤′-zero leq | ≤′-refl = refl
inject≤′-zero leq | ≤′-step b = {!   !}

inject≤≡≤' : ∀ {m1 m2}
                    → (leq : m1 ≤ m2)
                    → (a : Fin m1)
                    → inject≤′ a (≤⇒≤′ leq) ≡  inject≤ a leq
inject≤≡≤' z≤n ()
inject≤≡≤' (s≤s leq) zero =  inject≤′-zero leq
inject≤≡≤' (s≤s leq) (suc a) with (≤⇒≤′ (s≤s leq))
inject≤≡≤' (s≤s leq) (suc a) | ≤′-refl = sym (inject≤-refl (suc a) (s≤s leq))
inject≤≡≤' (s≤s leq) (suc a) | ≤′-step b = sym (begin
                                                  suc (inject≤ a leq)
                                                ≡⟪ {!   !} ⟫
                                                  inject₁ (inject≤ a leq)
                                                ≡⟪ cong (λ x → inject₁ x) (inject≤≡≤' {!   !} {!   !}) ⟫
                                                  inject₁ (inject≤′ (suc a) b)
                                                ∎)

-- inject₁ (inject≤′ (suc a) b) ≡ suc (inject≤ a leq)
-- suc (inject≤ a leq) ≡ inject₁ (in)

liftInject≤' :  ∀ {m1 m1' m2'}
                    → (σ1 : AListType m1' m1)
                    → (leq2 : m1 ≤ m2')
                    → (leq2' : m1' ≤ m2' ∸ m1 + m1')
                    → (a : Fin m1')
                    → mvar-sub (liftAList≤' (≤⇒≤′ leq2) σ1) (inject≤ a leq2')
                    ≡ mvar-map (M ∘ (λ x → inject≤ x leq2)) (mvar-sub σ1 a)
liftInject≤' {m1} {m1'} {m2'} σ1 leq2 leq2' a = begin
    mvar-sub (liftAList≤' (≤⇒≤′ leq2) σ1) (inject≤ a leq2')
  ≡⟪ cong (λ x → mvar-sub (liftAList≤' (≤⇒≤′ leq2) σ1) x) (sym (inject≤≡≤' leq2' a)) ⟫
    mvar-sub (liftAList≤' (≤⇒≤′ leq2) σ1) (inject≤′ a (≤⇒≤′ leq2'))
  ≡⟪ liftInject≤'' σ1 (≤⇒≤′ leq2) (≤⇒≤′ leq2') a ⟫
    mvar-map (M ∘ (λ x → inject≤′ x (≤⇒≤′ leq2))) (mvar-sub σ1 a)
  ≡⟪ cong (λ x₁ → mvar-map (M ∘ x₁) (mvar-sub σ1 a)) (ext (inject≤≡≤' leq2)) ⟫
    mvar-map (M ∘ (λ x → inject≤ x leq2)) (mvar-sub σ1 a)
  ∎

liftInject≤ :  ∀ {m1 m1' m2'}
                    → (σ1 : AListType m1' m1)
                    → (leq2 : m1 ≤ m2')
                    → (leq2' : m1' ≤ m2' ∸ m1 + m1')
                    → (a : Fin m1')
                    → ((mvar-map (mvar-sub (liftAList≤ leq2 σ1)) ∘ M ∘ (λ x → inject≤ x leq2')) a
              ≡ (mvar-map (M ∘ (λ x → inject≤ x leq2)) ∘ mvar-sub σ1) a)
liftInject≤ σ1 leq2 leq2' a =
              begin
                (mvar-map (mvar-sub (liftAList≤ leq2 σ1)) ∘ M ∘ (λ x → inject≤ x leq2')) a
              ≡⟪ refl ⟫
                mvar-map (mvar-sub (liftAList≤ leq2 σ1)) (M (inject≤ a leq2'))
              ≡⟪ refl ⟫
                mvar-sub (liftAList≤ leq2 σ1) (inject≤ a leq2')
              ≡⟪ liftInject≤' σ1  leq2 leq2' a  ⟫
              -- ≡⟪ liftInject≤' σ1 (≤⇒≤′ leq2) leq2 leq2' a  ⟫
                mvar-map (M ∘ (λ x → inject≤ x leq2)) (mvar-sub σ1 a)
              ≡⟪ refl ⟫
                (mvar-map (M ∘ (λ x → inject≤ x leq2)) ∘ mvar-sub σ1) a
              ∎

{-
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
-}
