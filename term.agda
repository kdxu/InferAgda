module term where

open import nat
open import inject
open import desc
open import mgu

open import Data.Unit using (⊤; tt)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_+_; _≤_)
open import Data.Product
open import Data.Sum
open import Data.Vec hiding (_++_)
open import Data.Maybe
open import Function using (_∘_)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

---------------------------------------------------------------

-- 型：t = TNat | t ⇒ t | t × t
TypeDesc : Desc
TypeDesc = base :+: rec :*: rec :+: rec :*: rec

Type : (m : ℕ) → Set
Type m = Fix TypeDesc m

TNat : {m : ℕ} → Type m
TNat = F (inj₁ (inj₁ tt))

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

private
  liftTypem≤m : (m : ℕ) → (m≤m : m ≤ m) → (x : Type m) → (liftType≤ m≤m x) ≡ x
  liftTypem≤m m m≤m x = liftFixm≤m m≤m x

  liftType≤add : {m m' : ℕ} → (k : ℕ) → (x : Type m) → (k+m≤m' : k + m ≤ m') → (m≤m' : m ≤ m') →
        liftType≤ k+m≤m' (liftType k x) ≡ liftType≤ m≤m' x
  liftType≤add {m} {m'} k x k+m≤m' m≤m' = begin
      liftType≤ k+m≤m' (liftType k x)
    ≡⟨ refl ⟩
      liftFix≤ {TypeDesc} k+m≤m' (liftFix {TypeDesc} k x)
    ≡⟨ refl ⟩
      mvar-map (M ∘ (λ x → inject≤ x k+m≤m')) (mvar-map (M ∘ (inject+' k)) x)
    ≡⟨ fuse (M ∘ (λ x → inject≤ x k+m≤m')) (M ∘ (inject+' k)) x ⟩
      mvar-map (M ∘ ((λ x → inject≤ x k+m≤m') ∘ (inject+' k))) x
    ≡⟨ cong (λ f → mvar-map (M ∘ f) x) (ext (inject≤add k k+m≤m' m≤m')) ⟩
      mvar-map (M ∘ (λ x → inject≤ x m≤m')) x
    ≡⟨ refl ⟩
      liftFix≤ {TypeDesc} m≤m' x
    ≡⟨ refl ⟩
      liftType≤ m≤m' x
    ∎

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
liftCxtZero (t ∷ Γ) = cong₂ _∷_ (fold-id t) (liftCxtZero Γ)

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

private
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
  substCxtAnil (x ∷ Γ) = cong₂ _∷_ (fold-id x) (substCxtAnil Γ)

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

-- WellTypedTerm から型情報を取り除く
erase : {m n : ℕ} → {t : Type m} → {Γ : Cxt n} → WellTypedTerm Γ t → WellScopedTerm n
erase (Var x) = Var x
erase (Lam t w) = Lam (erase w)
erase (App w1 w2) = App (erase w1) (erase w2)
erase (Fst w) = Fst (erase w)
erase (Snd w) = Snd (erase w)
erase (Cons w1 w2) = Cons (erase w1) (erase w2)

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

-- substWTerm≤ しても erase 結果は変わらない
eraseSubstWTerm≤ : {m m' m'' n : ℕ} → {t : Type m} → {Γ : Cxt {m} n}
           → (σ : AListType m' m'')
           → (leq : m ≤ m')
           → (w : WellTypedTerm Γ t)
           → erase (substWTerm≤ σ leq w) ≡ erase w
eraseSubstWTerm≤ {Γ = Γ} σ leq (Var x) rewrite lookupSubst≤CxtCommute x Γ σ leq = refl
eraseSubstWTerm≤ σ leq (Lam t w) = cong Lam (eraseSubstWTerm≤ σ leq w)
eraseSubstWTerm≤ σ leq (App w1 w2) = cong₂ App (eraseSubstWTerm≤ σ leq w1) (eraseSubstWTerm≤ σ leq w2)
eraseSubstWTerm≤ σ leq (Fst w) = cong Fst (eraseSubstWTerm≤ σ leq w)
eraseSubstWTerm≤ σ leq (Snd w) = cong Snd (eraseSubstWTerm≤ σ leq w)
eraseSubstWTerm≤ σ leq (Cons w1 w2) = cong₂ Cons (eraseSubstWTerm≤ σ leq w1) (eraseSubstWTerm≤ σ leq w2)

private
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
    ... | eq2 rewrite eq2 | fuse (λ x₁ → M (inject₁ x₁)) (mvar-sub σ) t
                          | fuse (mvar-sub (liftAList1 σ)) (λ u → M (inject₁ u)) t
      = inject₁-liftAList1-commute σ t
    inject₁-liftAList1-commute-M (σ asnoc t / x) y | just y' | [ eq ] rewrite eq
      with thickxyjust {x = x} eq
    ... | eq2 rewrite eq2 = inject₁-liftAList1-commute-M σ y'

    inject₁-liftAList1-commute-F : ∀ {m m' : ℕ}
                    → (σ : AListType m' m)
                    → (d : ⟦ TypeDesc ⟧ (Fix TypeDesc m') )
                    → (r : ⟦ TypeDesc ⟧'
                            (λ t → desc.fold F
                                      (λ z → mvar-map (mvar-sub (liftAList1 σ)) (M (inject₁ z))) t
                                     ≡
                                     desc.fold F (λ z → mvar-map (λ u → M (inject₁ u)) (mvar-sub σ z)) t)
                            d)
                    → fmap TypeDesc
                         (desc.fold F (λ z → mvar-map (mvar-sub (liftAList1 σ)) (M (inject₁ z)))) d
                    ≡ fmap TypeDesc
                         (desc.fold F (λ z → mvar-map (λ u → M (inject₁ u)) ((mvar-sub σ) z))) d
    inject₁-liftAList1-commute-F σ (inj₁ (inj₁ tt)) r = refl
    inject₁-liftAList1-commute-F σ (inj₁ (inj₂ (d1 , d2))) (r1 , r2)
      = cong inj₁ (cong inj₂ (cong₂ _,_ r1 r2))
    inject₁-liftAList1-commute-F σ (inj₂ (d1 , d2)) (r1 , r2) = cong inj₂ (cong₂ _,_ r1 r2)

    inject₁-liftAList1-commute : ∀ {m m' : ℕ}
                    → (σ : AListType m' m)
                    → (t : Type m')
                    → desc.fold F (λ z → mvar-map (mvar-sub (liftAList1 σ)) (M (inject₁ z))) t
                    ≡ desc.fold F (λ z → mvar-map (λ u → M (inject₁ u)) ((mvar-sub σ) z)) t
    inject₁-liftAList1-commute σ =
      ind (λ t → desc.fold F (λ z → mvar-map (mvar-sub (liftAList1 σ)) (M (inject₁ z))) t
                ≡ desc.fold F (λ z → mvar-map (λ u → M (inject₁ u)) ((mvar-sub σ) z)) t)
          (λ d r → cong F (inject₁-liftAList1-commute-F σ d r))
          (λ x → inject₁-liftAList1-commute-M σ x)

  liftInject≤'' :  ∀ {m1 m1' m2'}
                    → (σ1 : AListType m1' m1)
                    → (leq2 : m1 ≤′ m2')
                    → (leq2' : m1' ≤′ m2' ∸ m1 + m1')
                    → (a : Fin m1')
                    → mvar-sub (liftAList≤' leq2 σ1) (inject≤′ a leq2')
                    ≡ mvar-map (M ∘ (λ x → inject≤′ x leq2)) (mvar-sub σ1 a)
  liftInject≤'' {m1} {m1'} {.m1} σ1 ≤′-refl leq2' a
    rewrite n∸n≡0 m1 | inject≤′-refl a leq2' =
      begin
       (mvar-sub σ1 a)
      ≡⟨  sym (fold-id (mvar-sub σ1 a)) ⟩
       desc.fold F M (mvar-sub σ1 a)
      ∎
  liftInject≤'' {m1} {m1'} {.(suc m2')} σ1 (≤′-step {n = m2'} leq2) leq2' a
    rewrite +-∸-assoc 1 (≤′⇒≤ leq2)
    with m<′m'-step (n≤′m+n (m2' ∸ m1) m1') leq2'
  ... | (m1'≤′m2'∸m1+m1' , leq) rewrite leq
    = begin
        mvar-sub (liftAList1 (liftAList≤' leq2 σ1)) (inject₁ (inject≤′ a m1'≤′m2'∸m1+m1'))
  {-  ≡⟨ refl ⟩
        mgu.fold F (mvar-sub (liftAList1 (liftAList≤' leq2 σ1)))
          (mgu.fold F (M ∘ inject₁)
            (M (inject≤′ a m1'≤′m2'∸m1+m1'))) -}
      ≡⟨ fuse (mvar-sub (liftAList1 (liftAList≤' leq2 σ1))) (M ∘ inject₁) (M (inject≤′ a m1'≤′m2'∸m1+m1')) ⟩
  {-    mgu.fold F (mvar-map (mvar-sub (liftAList1 (liftAList≤' leq2 σ1))) ∘ (M ∘ inject₁))
          (M (inject≤′ a m1'≤′m2'∸m1+m1'))
      ≡⟨ refl ⟩ -}
        (mvar-map (mvar-sub (liftAList1 (liftAList≤' leq2 σ1))) ∘ (M ∘ inject₁))
          (inject≤′ a m1'≤′m2'∸m1+m1')
      ≡⟨ inject₁-liftAList1-commute (liftAList≤' leq2 σ1) (M (inject≤′ a m1'≤′m2'∸m1+m1')) ⟩
        (mvar-map (M ∘ inject₁) ∘ (mvar-sub (liftAList≤' leq2 σ1)))
          (inject≤′ a m1'≤′m2'∸m1+m1')
  {-  ≡⟨ refl ⟩
        mgu.fold F (mvar-map (M ∘ inject₁) ∘ (mvar-sub (liftAList≤' leq2 σ1)))
          (M (inject≤′ a m1'≤′m2'∸m1+m1'))
      ≡⟨ refl ⟩
        mgu.fold F (M ∘ inject₁)
          (mgu.fold F
            (mvar-sub (liftAList≤' leq2 σ1)) (M (inject≤′ a m1'≤′m2'∸m1+m1'))) -}
      ≡⟨ refl ⟩
        desc.fold F (M ∘ inject₁)
          (mvar-sub (liftAList≤' leq2 σ1) (inject≤′ a m1'≤′m2'∸m1+m1'))
      ≡⟨ cong (desc.fold F (M ∘ inject₁)) (liftInject≤'' σ1 leq2 m1'≤′m2'∸m1+m1' a) ⟩
        desc.fold F (M ∘ inject₁)
          (mvar-map (M ∘ (λ x → inject≤′ x leq2)) (mvar-sub σ1 a))
      ≡⟨ refl ⟩
        desc.fold F (M ∘ inject₁)
          (desc.fold F (M ∘ (λ x → inject≤′ x leq2)) (mvar-sub σ1 a))
      ≡⟨ fuse (M ∘ inject₁) (M ∘ (λ x → inject≤′ x leq2)) (mvar-sub σ1 a) ⟩
        desc.fold F (M ∘ (inject₁ ∘ λ x → inject≤′ x leq2)) (mvar-sub σ1 a)
      ≡⟨ refl ⟩
        desc.fold F (λ x → M (inject₁ (inject≤′ x leq2))) (mvar-sub σ1 a)
      ∎

  liftInject≤' :  ∀ {m1 m1' m2'}
                    → (σ1 : AListType m1' m1)
                    → (leq2 : m1 ≤ m2')
                    → (leq2' : m1' ≤ m2' ∸ m1 + m1')
                    → (a : Fin m1')
                    → mvar-sub (liftAList≤' (≤⇒≤′ leq2) σ1) (inject≤ a leq2')
                    ≡ mvar-map (M ∘ (λ x → inject≤ x leq2)) (mvar-sub σ1 a)
  liftInject≤' {m1} {m1'} {m2'} σ1 leq2 leq2' a = begin
      mvar-sub (liftAList≤' (≤⇒≤′ leq2) σ1) (inject≤ a leq2')
    ≡⟨ cong (λ x → mvar-sub (liftAList≤' (≤⇒≤′ leq2) σ1) x) (sym (inject≤≡≤' leq2' a)) ⟩
      mvar-sub (liftAList≤' (≤⇒≤′ leq2) σ1) (inject≤′ a (≤⇒≤′ leq2'))
    ≡⟨ liftInject≤'' σ1 (≤⇒≤′ leq2) (≤⇒≤′ leq2') a ⟩
      mvar-map (M ∘ (λ x → inject≤′ x (≤⇒≤′ leq2))) (mvar-sub σ1 a)
    ≡⟨ cong (λ x₁ → mvar-map (M ∘ x₁) (mvar-sub σ1 a)) (ext (inject≤≡≤' leq2)) ⟩
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
              ≡⟨ refl ⟩
                mvar-map (mvar-sub (liftAList≤ leq2 σ1)) (M (inject≤ a leq2'))
              ≡⟨ refl ⟩
                mvar-sub (liftAList≤ leq2 σ1) (inject≤ a leq2')
              ≡⟨ liftInject≤' σ1  leq2 leq2' a  ⟩
              -- ≡⟨ liftInject≤' σ1 (≤⇒≤′ leq2) leq2 leq2' a  ⟩
                mvar-map (M ∘ (λ x → inject≤ x leq2)) (mvar-sub σ1 a)
              ≡⟨ refl ⟩
                (mvar-map (M ∘ (λ x → inject≤ x leq2)) ∘ mvar-sub σ1) a
              ∎

  substTypeTrans : ∀ {m m1 m1' m2 m2'}
                    → (x : Type m)
                    → (σ1 : AListType m1' m1)
                    → (σ2 : AListType m2'  m2)
                    → (σ' : AListType (m2' ∸ m1 + m1')  m2)
                    → (leq1 : m ≤ m1')
                    → (leq2 : m1 ≤ m2')
                    → (leq' : m ≤ m2' ∸ m1 + m1')
                    → ( σ' ≡ σ2 +⟨ leq2 ⟩ σ1 )
                    → substType≤ σ' leq' x ≡ substType≤ σ2 leq2 (substType≤ σ1 leq1 x)
  substTypeTrans {m} {m1} {m1'} {m2} {m2'} t σ1 σ2 σ' leq1 leq2 leq' eq =
      begin
        substType≤ σ' leq' t
      ≡⟨ cong (λ x₁ → mvar-map (mvar-sub x₁) (mvar-map (M ∘ (λ x → inject≤ x leq')) t)) eq ⟩
        mvar-map (mvar-sub (σ2 +⟨ leq2 ⟩ σ1)) (mvar-map (M ∘ (λ x → inject≤ x leq')) t)
      ≡⟨ cong (λ x → mvar-map (mvar-sub (σ2 +⟨ leq2 ⟩ σ1)) (mvar-map (M ∘ x) t)) (ext (inject≤Trans leq2' leq1 leq')) ⟩
        mvar-map (mvar-sub (σ2 +⟨ leq2 ⟩ σ1)) (mvar-map (M ∘ ((λ x → inject≤ x leq2') ∘ (λ x → inject≤ x leq1))) t)
      ≡⟨ cong (λ x → mvar-map (mvar-sub (σ2 +⟨ leq2 ⟩ σ1)) x)
              (sym (fuse (M ∘ (λ x → inject≤ x leq2')) (M ∘ (λ x → inject≤ x leq1)) t)) ⟩
        mvar-map (mvar-sub (σ2 +⟨ leq2 ⟩ σ1))
                 (mvar-map (M ∘ (λ x → inject≤ x leq2')) (mvar-map (M ∘ (λ x → inject≤ x leq1)) t))
      ≡⟨ refl ⟩
        mvar-map (mvar-sub (σ2 ++ (liftAList≤ leq2 σ1)))
                 (mvar-map (M ∘ (λ x → inject≤ x leq2')) (mvar-map (M ∘ (λ x → inject≤ x leq1)) t))
      ≡⟨ cong (λ f → f (mvar-map (M ∘ (λ x → inject≤ x leq2')) (mvar-map (M ∘ (λ x → inject≤ x leq1)) t)))
              (mvar-sub-++-commute σ2 (liftAList≤ leq2 σ1)) ⟩
        (mvar-map (mvar-sub σ2) ∘ (mvar-map (mvar-sub (liftAList≤ leq2 σ1))))
                  (mvar-map (M ∘ (λ x → inject≤ x leq2')) (mvar-map (M ∘ (λ x → inject≤ x leq1)) t))
      ≡⟨ refl ⟩
        mvar-map (mvar-sub σ2) (mvar-map (mvar-sub (liftAList≤ leq2 σ1))
                 (mvar-map (M ∘ (λ x → inject≤ x leq2')) (mvar-map (M ∘ (λ x → inject≤ x leq1)) t)))
      ≡⟨ cong (mvar-map (mvar-sub σ2))
              (fuse (mvar-sub (liftAList≤ leq2 σ1)) (M ∘ (λ x → inject≤ x leq2'))
                         (mvar-map (M ∘ (λ x → inject≤ x leq1)) t)) ⟩
        mvar-map (mvar-sub σ2)
          (mvar-map (mvar-map (mvar-sub (liftAList≤ leq2 σ1)) ∘ (M ∘ (λ x → inject≤ x leq2')))
            (mvar-map (M ∘ (λ x → inject≤ x leq1)) t))
      ≡⟨ cong (λ f → mvar-map (mvar-sub σ2) (mvar-map f (mvar-map (M ∘ (λ x → inject≤ x leq1)) t)))
              (ext (liftInject≤ σ1 leq2 leq2')) ⟩
        mvar-map (mvar-sub σ2)
          (mvar-map (mvar-map (M ∘ (λ x → inject≤ x leq2)) ∘ (mvar-sub σ1))
            (mvar-map (M ∘ (λ x → inject≤ x leq1)) t))
      ≡⟨ cong (mvar-map (mvar-sub σ2))
              (sym (fuse (M ∘ (λ x → inject≤ x leq2)) (mvar-sub σ1) (mvar-map (M ∘ (λ x → inject≤ x leq1)) t))) ⟩
        mvar-map (mvar-sub σ2) (mvar-map (M ∘ (λ x → inject≤ x leq2))
          (mvar-map (mvar-sub σ1) (mvar-map (M ∘ (λ x → inject≤ x leq1)) t)))
      ≡⟨ refl ⟩
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
                    → (leq' : m ≤ m2' ∸ m1 + m1')
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
