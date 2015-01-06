\agdaIgnore{
\begin{code}

module Term where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Vec 
open import Data.Product
open import Data.Fin hiding (_+_; _≤_)
open import Data.Maybe
open import Data.Sum
open import lib
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Binary.HeterogeneousEquality
  renaming (sym to hsym; trans to htrans; cong to hcong; cong₂ to hcong₂; subst to hsubst; subst₂ to hsubst₂; refl to hrefl)
--open Relation.Binary.HeterogeneousEquality
private module H = ≅-Reasoning
open import Data.Nat.Properties
 -- for the concrete record, such as isCommutativeSemiring
open import Algebra.Structures
 -- for type definitions, such as IsCommutativeSemiring
private module M = IsCommutativeSemiring

+-right-identity : ∀ n → n + 0 ≡ n
+-right-identity = proj₂ (M.+-identity isCommutativeSemiring)

+-left-identity : ∀ n → 0 + n ≡ n
+-left-identity = proj₁ (M.+-identity isCommutativeSemiring)

+-assoc : ∀ m n o → (m + n) + o ≡  m + (n + o)
+-assoc = M.+-assoc isCommutativeSemiring

+-comm : ∀ m n → m + n ≡  n + m
+-comm = M.+-comm isCommutativeSemiring

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

suc+-lem : ∀ m n l →  suc (l + (n + m)) ≡ n + (suc l) + m
suc+-lem m n l rewrite +-suc n l | sym (+-assoc l n m) | +-comm n l = refl

-- +-suc m n rewrite +-comm m n = +-comm m (suc n)
\end{code}
}
\agdaSnippet\Cxt{
\begin{code}
-- 型変数の数が m 個で長さが n の型環境
Cxt : {m : ℕ} → ℕ → Set
Cxt {m} n = Vec (Type m) n
\end{code}
}
\agdaSnippet\LiftCxt{
\begin{code}
-- liftCxt m' Γ : Γ の中の型変数の数を m' だけ増やす
liftCxt : (m' : ℕ) → {m n : ℕ} → Cxt {m} n → Cxt {m' + m} n
liftCxt m' {m} Γ = Data.Vec.map (▹◃ (inject+' m')) Γ
\end{code}
}
\agdaSnippet\LiftCxtZero{
\begin{code}
liftCxtZero : {m n : ℕ} → (Γ : Cxt {m} n) → liftCxt 0 Γ ≡ Γ
liftCxtZero [] = refl
liftCxtZero (x ∷ Γ) = cong₂ _∷_ (TVarId x) (liftCxtZero Γ)
\end{code}
}
\agdaSnippet\SubstCxt{
\begin{code}
-- substCxt σ Γ : Γ に σ を適用した型環境を返す
substCxt : {m m' n : ℕ} → AList m m' → Cxt {m} n → Cxt {m'} n 
substCxt σ Γ = Data.Vec.map (substType σ) Γ 
\end{code}
}
\agdaSnippet\SubstCxtAnil{
\begin{code}
-- substCxt anil Γ は Γ と同じ
substCxtAnil : {m n : ℕ} → (Γ : Cxt {m} n) → substCxt anil Γ ≡ Γ 
substCxtAnil [] = refl
substCxtAnil (x ∷ Γ) = cong₂ _∷_ (TVarId x) (substCxtAnil Γ)
\end{code}
}
\agdaSnippet\WellScopedTerm{
\begin{code}
-- 自由変数の数が n 個の well-scope な項
data WellScopedTerm (n : ℕ) : Set where
  Var : Fin n → WellScopedTerm n
  Lam : WellScopedTerm (suc n) → WellScopedTerm n
  App : WellScopedTerm n → WellScopedTerm n → WellScopedTerm n
\end{code}
}
\agdaSnippet\WellTypedTerm{
\begin{code}
-- WellTypedTerm Γ t : 自由変数の数が n 個、型が t であるような well-typed な項
data WellTypedTerm {m n : ℕ} (Γ : Cxt n) : Type m → Set where
  Var : (x : Fin n) → WellTypedTerm Γ (lookup x Γ)
  Lam : (t : Type m) → {t' : Type m} → WellTypedTerm (t ∷ Γ) t' →
        WellTypedTerm Γ (t ⇒ t')
  App : {t t' : Type m} → WellTypedTerm Γ (t ⇒ t') → WellTypedTerm Γ t →
        WellTypedTerm Γ t'
\end{code}
}
\agdaSnippet\LookupLiftCxtCommute{
\begin{code}
-- lookup と liftCxt は順番を変えても良い
lookupLiftCxtCommute : (m' : ℕ) {n m : ℕ} (x : Fin n) (Γ : Cxt {m} n) →
                       liftType m' (lookup x Γ) ≡ lookup x (liftCxt m' Γ)
lookupLiftCxtCommute m' {zero} () Γ
lookupLiftCxtCommute m' {suc n} zero (t ∷ Γ) = refl
lookupLiftCxtCommute m' {suc n} (suc x) (t ∷ Γ) = lookupLiftCxtCommute m' x Γ
\end{code}
}
\agdaSnippet\LiftWTerm{
\begin{code}
-- WellTypedTerm を lift する
liftWTerm : (m' : ℕ) {m n : ℕ} → {Γ : Cxt {m} n} → {t : Type m} → WellTypedTerm Γ t →
            WellTypedTerm (liftCxt m' Γ) (liftType m' t)
liftWTerm m' {Γ = Γ} (Var x) rewrite lookupLiftCxtCommute m' x Γ = Var x
liftWTerm m' (Lam t w) = Lam (liftType m' t) (liftWTerm m' w)
liftWTerm m' (App w1 w2) = App (liftWTerm m' w1) (liftWTerm m' w2)
\end{code}
}
\agdaSnippet\LookupSubstCxtCommute{
\begin{code}
-- lookup と substCxt は順番を変えても良い
lookupSubstCxtCommute : {n m' m : ℕ} (x : Fin n) (Γ : Cxt {m} n) → (σ : AList m m') →
                       substType σ (lookup x Γ) ≡ lookup x (substCxt σ Γ)
lookupSubstCxtCommute {zero} () Γ σ
lookupSubstCxtCommute {suc n} zero (t ∷ Γ) σ = refl
lookupSubstCxtCommute {suc n} (suc x) (t ∷ Γ) σ = lookupSubstCxtCommute x Γ σ
\end{code}
}
\agdaSnippet\SubstWTerm{
\begin{code}
-- substWTerm σ w : w に σ を適用した WellTypedTerm を返す
substWTerm : {m' m n : ℕ} → {Γ : Cxt {m} n} → {t : Type m} →
             (σ : AList m m') → WellTypedTerm Γ t → WellTypedTerm (substCxt σ Γ) (substType σ t)
substWTerm {Γ = Γ} σ (Var x) rewrite lookupSubstCxtCommute x Γ σ = Var x
substWTerm σ (Lam t w) = Lam (substType σ t) (substWTerm σ w)
substWTerm σ (App w1 w2) = App (substWTerm σ w1) (substWTerm σ w2)
\end{code}
}
\agdaSnippet\Unify{
\begin{code}
-- unify t1 t2 : 型変数が m 個であるような型 t1 と t2 を unify する代入を返す

unify : {m : ℕ} → Type m → Type m → Maybe (Σ[ n ∈ ℕ ] AList m n)
unify {m} t1 t2 = mgu {m} t1 t2
\end{code}
}
\agdaSnippet\UnifyTwo{
\begin{code}
-- unify2 t1 t2 : 型変数が m 個であるような型 t1 と t2 を unify する代入を返す
unify2 : {m : ℕ} → (s t : Type m) →
       Maybe (Σ[ n ∈ ℕ ] Σ[ σ ∈ AList m n ] substType σ s ≡ substType σ t)
unify2 {m} t1 t2 = mgu2 {m} t1 t2
\end{code}
}
\agdaSnippet\Count{
\begin{code}
--Well-scope な項の中の Lam と App のノード数を数える
-- （その数が、新たに導入される型変数の数になる）
count : {n : ℕ} → (s : WellScopedTerm n) → ℕ
count (Var x) = zero
count (Lam s) = suc (count s)
count (App s1 s2) = count s1 + suc (count s2)
\end{code}
}
\agdaSnippet\HeteroGeneouses{
\begin{code}
-- hsubst の heterogeneous 版
hsubst' : ∀ {a b c} {I : Set a} {i j : I}
       → (A : I → Set b) {x' : A i} {y : A j}
       → i ≡ j
       → (P : {i : I} → A i → Set c)
       → x' ≅ y
       → P x' → P y
hsubst' _ refl P hrefl px = px

-- hcong の heterogeneous 版
hcong' : ∀ {α β γ} {I : Set α} {i j : I}
       → (A : I → Set β) {B : {k : I} → A k → Set γ} {x : A i} {y : A j}
       → i ≡ j
       → (f : {k : I} → (x : A k) → B x)
       → x ≅ y
       → f x ≅ f y
hcong' _ refl _ hrefl = hrefl

-- hcong₂ の heterogeneous 版
hcong₂' : ∀ {a b c d} {I : Set a} {i1 i2 : I}
          (A : I → Set b)
          (B : I → Set c)
          {C : {i : I} → A i → B i → Set d}
          {x : A i1} {y : A i2} {u : B i1} {v : B i2} →
        i1 ≡ i2 →
        (f : {i : I} → (x : A i) → (y : B i) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
hcong₂' _ _ refl f hrefl hrefl = hrefl
\end{code}
}
\agdaSnippet\InjectSuc{
\begin{code}
injectSuc : ∀ m' {n} (x : Fin n) → inject+' m' (inject₁ x) ≅ inject₁ (inject+' m' x)
injectSuc zero x = hrefl
injectSuc (suc m') {n} x = hcong' Fin (+-suc m' n) inject₁ (injectSuc m' x)
\end{code}
}
\agdaSnippet\InjectAdd{
\begin{code}
injectAdd : ∀ {m} m1 m2 → (x : Fin m) → inject+' m1 (inject+' m2 x) ≅ inject+' (m1 + m2) x
injectAdd zero m2 x = hrefl
injectAdd {m} (suc m1) m2 x = hcong' Fin (sym (+-assoc m1 m2 m)) inject₁ (injectAdd m1 m2 x)
\end{code}
}
\agdaSnippet\LiftTypeSuc{
\begin{code}
liftTypeSuc : {m m' : ℕ} → (t : Type m) → liftType m' (liftType 1 t) ≅ liftType (suc m') t
liftTypeSuc {m} {m'} (TVar x) = hcong' Fin (+-suc m' m) TVar (injectSuc m' x)
liftTypeSuc {m} {m'} TInt rewrite +-suc m' m = hrefl
liftTypeSuc {m} {m'} (t1 ⇒ t2) =
  hcong₂' Type Type (+-suc m' m) _⇒_ (liftTypeSuc {m} {m'} t1) (liftTypeSuc {m} {m'} t2)
\end{code}
}
\agdaSnippet\LiftTypeAdd{
\begin{code}
liftTypeAdd : ∀ {m} m1 m2 → (t : Type m) → liftType m1 (liftType m2 t) ≅ liftType (m1 + m2) t
liftTypeAdd {m} m1 m2 (TVar x) = hcong' Fin (sym (+-assoc m1 m2 m)) TVar (injectAdd m1 m2 x)
liftTypeAdd {m} m1 m2 TInt rewrite sym (+-assoc m1 m2 m) = hrefl
liftTypeAdd {m} m1 m2 (t1 ⇒ t2) =
  hcong₂' Type Type (sym (+-assoc m1 m2 m)) _⇒_ (liftTypeAdd m1 m2 t1) (liftTypeAdd m1 m2 t2)
\end{code}
}
\agdaSnippet\LiftCxtSuc{
\begin{code}
liftCxtSuc : ∀ {m} m' {n} → (Γ : Cxt {m} n) → liftCxt m' (liftCxt 1 Γ) ≅ liftCxt (suc m') Γ
liftCxtSuc {m} m' [] rewrite +-suc m' m = hrefl
liftCxtSuc {m} m' {suc n} (t ∷ Γ) =
  hcong₂' Type (λ m → Cxt {m} n) (+-suc m' m) _∷_ (liftTypeSuc {m} {m'} t) (liftCxtSuc {m} m' Γ)
\end{code}
}
\agdaSnippet\LiftCxtAdd{
\begin{code}
liftCxtAdd : ∀ {m} m1 m2 {n} → (Γ : Cxt {m} n) → liftCxt m1 (liftCxt m2 Γ) ≅ liftCxt (m1 + m2) Γ
liftCxtAdd {m} m1 m2 [] rewrite sym (+-assoc m1 m2 m) = hrefl
liftCxtAdd {m} m1 m2 {suc n} (t ∷ Γ) =
  hcong₂' Type (λ m → Cxt {m} n) (sym (+-assoc m1 m2 m)) _∷_ (liftTypeAdd m1 m2 t) (liftCxtAdd m1 m2 Γ)
\end{code}
}
\agdaSnippet\SubstCommutes{
\begin{code}
substConsCommute : ∀ {m m' n} (eq : m ≡ m') (t : Type m) (Γ : Cxt {m} n) →
                   subst (λ m → Cxt {m} (suc n)) eq (t ∷ Γ) ≡ 
                   subst Type eq t ∷ subst (λ m → Cxt {m} n) eq Γ
substConsCommute refl t Γ = refl

substTVarCommute : ∀ {m m'} (eq : m ≡ m') (x : Fin m) →
                   subst Type eq (TVar x) ≡ TVar (subst Fin eq x)
substTVarCommute refl x = refl

substInject1Commute : ∀ {m m'} (eq : m ≡ m') (x : Fin m) →
                      subst Fin (cong suc eq) (inject₁ x) ≡ inject₁ (subst Fin eq x)
substInject1Commute refl x = refl

substArrowCommute : ∀ {m m'} (eq : m ≡ m') (t1 t2 : Type m) →
                    subst Type eq (t1 ⇒ t2) ≡ subst Type eq t1 ⇒ subst Type eq t2
substArrowCommute refl t1 t2 = refl
\end{code}
}
\agdaSnippet\AddDash{
\begin{code}
injectAdd' : ∀ {m} m1 m2 → (x : Fin m) →
             inject+' m1 (inject+' m2 x) ≡ subst Fin (+-assoc m1 m2 m) (inject+' (m1 + m2) x)
injectAdd' zero m2 x = refl
injectAdd' {m} (suc m1) m2 x rewrite substInject1Commute (+-assoc m1 m2 m) (inject+' (m1 + m2) x) =
  cong inject₁ (injectAdd' m1 m2 x)

liftTypeAdd' : ∀ {m} m1 m2 → (t : Type m) →
               liftType m1 (liftType m2 t) ≡ subst Type (+-assoc m1 m2 m) (liftType (m1 + m2) t)
liftTypeAdd' {m} m1 m2 (TVar x)
  rewrite injectAdd' m1 m2 x | substTVarCommute (+-assoc m1 m2 m) (inject+' (m1 + m2) x) = refl
liftTypeAdd' {m} m1 m2 TInt rewrite +-assoc m1 m2 m = refl
liftTypeAdd' {m} m1 m2 (t1 ⇒ t2)
  rewrite substArrowCommute (+-assoc m1 m2 m) (liftType (m1 + m2) t1) (liftType (m1 + m2) t2) =
  cong₂ _⇒_ (liftTypeAdd' m1 m2 t1) (liftTypeAdd' m1 m2 t2)
\end{code}
}
\agdaSnippet\ThickInjectOne{
\begin{code}
thickInject1 : ∀ {n} (x y : Fin (suc n)) →
               (thick x y ≡ nothing × thick (inject₁ x) (inject₁ y) ≡ nothing) ⊎
               (Σ[ y' ∈ Fin n ] thick x y ≡ just y' × thick (inject₁ x) (inject₁ y) ≡ just (inject₁ y'))
thickInject1 zero zero = inj₁ (refl , refl)
thickInject1 zero (suc y) = inj₂ (y , refl , refl)
thickInject1 {zero} (suc ()) zero
thickInject1 {suc n} (suc x) zero = inj₂ (zero , refl , refl)
thickInject1 {zero} (suc ()) (suc y)
thickInject1 {suc n} (suc x) (suc y) with thickInject1 x y
... | inj₁ (eq1 , eq2) rewrite eq1 | eq2 = inj₁ (refl , refl)
... | inj₂ (y' , eq1 , eq2) rewrite eq1 | eq2 = inj₂ (suc y' , refl , refl)
\end{code}
}
\agdaSnippet\AListNoLess{
\begin{code}
AListNoLess : ∀ {m n} (σ : AList m n) → n ≤′ m
AListNoLess anil = ≤′-refl
AListNoLess (σ asnoc t' / x) = ≤′-step (AListNoLess σ)
\end{code}
}
\agdaIgnore{
\begin{code}
mutual
  liftSub1Commute : ∀ {m' m} (σ : AList m' m) (x : Fin m') →
                    liftType 1 (sub σ x) ≡ sub (liftAList1 σ) (inject₁ x)
--   liftSub1Commute σ x with AListNoLess σ
--   ... | ≤′-refl = {!!}
--   ... | ≤′-step a = {!!}
--  liftSub1Commute {zero} anil x = refl
--  liftSub1Commute {zero} (σ asnoc t' / x) x₁ = {!!}
--  liftSub1Commute {suc s} σ x = {!!}
--  以下の定義は termination check にひっかかる。AList の長さについて再帰したいが、
--  AList (s + m) m の s で再帰するのではうまくいかない。AList の定義を変更しなくてはだめか。
--  と思ったが、1 の場合だけを切り出して、相互再帰させたらうまくいった！！！
  liftSub1Commute anil x = refl
  liftSub1Commute (σ asnoc t / y) x with thickInject1 y x
  ... | inj₁ (eq1 , eq2) rewrite eq1 | eq2 = liftSubst1Commute σ t
  ... | inj₂ (x' , eq1 , eq2) rewrite eq1 | eq2 = liftSub1Commute σ x'

  liftSubst1Commute : ∀ {m' m} (σ : AList m' m) (t : Type m') →
                     liftType 1 (substType σ t) ≡ substType (liftAList1 σ) (liftType 1 t)
  liftSubst1Commute σ (TVar x) = liftSub1Commute σ x
  liftSubst1Commute σ TInt = refl
  liftSubst1Commute σ (t1 ⇒ t2) = cong₂ _⇒_ (liftSubst1Commute σ t1) (liftSubst1Commute σ t2)

liftSubCommute : ∀ {m' m} c (σ : AList m' m) (x : Fin m') →
                 liftType c (sub σ x) ≡ sub (liftAList c σ) (inject+' c x)
liftSubCommute zero σ x rewrite TVarId (sub σ x) = refl
liftSubCommute (suc c) σ x =
  begin
    liftType (suc c) (sub σ x)
  ≡⟨ sym (≅-to-≡ (liftTypeAdd 1 c (sub σ x))) ⟩
    liftType 1 (liftType c (sub σ x))
  ≡⟨ cong (liftType 1) (liftSubCommute c σ x) ⟩
    liftType 1 (sub (liftAList c σ) (inject+' c x))
  ≡⟨ liftSub1Commute (liftAList c σ) (inject+' c x) ⟩
    sub (liftAList1 (liftAList c σ)) (inject₁ (inject+' c x))
  ∎

liftSubstCommute : ∀ {m' m} c (σ : AList m' m) (t : Type m') →
                   liftType c (substType σ t) ≡ substType (liftAList c σ) (liftType c t)
liftSubstCommute c σ (TVar x) = liftSubCommute c σ x
liftSubstCommute c σ TInt = refl
liftSubstCommute c σ (t1 ⇒ t2) = cong₂ _⇒_ (liftSubstCommute c σ t1) (liftSubstCommute c σ t2)

mutual
  substVarAdd : ∀ {m m2 m1} (σ2 : AList m1 m2) (σ1 : AList m m1) (x : Fin m) →
                sub σ2 ◃ sub σ1 x ≡ sub (σ2 +!+ σ1) x
  substVarAdd σ2 anil x = refl
  substVarAdd σ2 (σ1 asnoc t / y) x with thick y x
  ... | nothing = substTypeAdd σ2 σ1 t
  ... | just x' = substVarAdd σ2 σ1 x'

  substTypeAdd : ∀ {m m2 m1} (σ2 : AList m1 m2) (σ1 : AList m m1) (t : Type m) →
                 substType σ2 (substType σ1 t) ≡ substType (σ2 +!+ σ1) t
  substTypeAdd σ2 σ1 (TVar x) = substVarAdd σ2 σ1 x
  substTypeAdd σ2 σ1 TInt = refl
  substTypeAdd σ2 σ1 (t1 ⇒ t2) = cong₂ _⇒_ (substTypeAdd σ2 σ1 t1) (substTypeAdd σ2 σ1 t2)

substLiftTypeAdd : ∀ {m m2 m1} c2 c1 (σ2 : AList (c2 + m1) m2) (σ1 : AList (c1 + m) m1) (t : Type m) →
                   substType σ2 (liftType c2 (substType σ1 (liftType c1 t))) ≅
                   substType (σ2 +!+ liftAList c2 σ1)
                             (subst Type (+-assoc c2 c1 m) (liftType (c2 + c1) t))
substLiftTypeAdd {m} c2 c1 σ2 σ1 t
  rewrite liftSubstCommute c2 σ1 (liftType c1 t)
        | liftTypeAdd' c2 c1 t
        | substTypeAdd σ2 (liftAList c2 σ1) (subst Type (+-assoc c2 c1 m)
                                                     ((λ x → TVar (inject+' (c2 + c1) x)) ◃ t))
  = hrefl

substLiftCxtAdd : ∀ {m n m2 m1} c2 c1 (σ2 : AList (c2 + m1) m2) (σ1 : AList (c1 + m) m1) (Γ : Cxt {m} n) →
               substCxt σ2 (liftCxt c2 (substCxt σ1 (liftCxt c1 Γ))) ≅
               substCxt (σ2 +!+ liftAList c2 σ1)
                        (subst (λ m → Cxt {m} n) (+-assoc c2 c1 m) (liftCxt (c2 + c1) Γ))
substLiftCxtAdd {m} c2 c1 σ2 σ1 [] rewrite +-assoc c2 c1 m = hrefl
substLiftCxtAdd {m} {suc n} c2 c1 σ2 σ1 (t ∷ Γ)
  rewrite substConsCommute (+-assoc c2 c1 m) (liftType (c2 + c1) t) (liftCxt (c2 + c1) Γ) =
  hcong₂ _∷_ (substLiftTypeAdd c2 c1 σ2 σ1 t) (substLiftCxtAdd c2 c1 σ2 σ1 Γ)

substLiftCommute : ∀ {m n m2 m1} c2 c1 (σ2 : AList (c2 + m1) m2) (σ1 : AList (c1 + m) m1) (Γ : Cxt {m} n) →
            ((subst (λ m → Cxt {m} n) (+-assoc c2 c1 m) (liftCxt (c2 + c1) Γ)) ≡ liftCxt c2 (liftCxt c1 Γ))
substLiftCommute {m} c2 c1 σ2 σ1 [] rewrite +-assoc c2 c1 m  = refl
substLiftCommute {m} c2 c1 σ2 σ1 (t ∷ Γ) rewrite substConsCommute (+-assoc c2 c1 m) (liftType (c2 + c1) t) (liftCxt (c2 + c1) Γ) = cong₂ _∷_ (sym (liftTypeAdd' c2 c1 t)) (substLiftCommute c2 c1 σ2 σ1 Γ)

substLiftCxtAdd2 : ∀ {m n m2 m1} c2 c1 (σ2 : AList (c2 + m1) m2) (σ1 : AList (c1 + m) m1) (Γ : Cxt {m} n) →
               substCxt σ2 (liftCxt c2 (substCxt σ1 (liftCxt c1 Γ))) ≅
               substCxt (σ2 +!+ liftAList c2 σ1)
                        (liftCxt c2 (liftCxt c1 Γ))
substLiftCxtAdd2 c2 c1 σ2 σ1 [] = hrefl
substLiftCxtAdd2 {m} {suc n} c2 c1 σ2 σ1 (t ∷ Γ) rewrite substLiftCommute c2 c1 σ2 σ1 Γ =  htrans (substLiftCxtAdd c2 c1 σ2 σ1 (t ∷ Γ)) (hcong (λ x → substCxt (σ2 +!+ liftAList c2 σ1) x) (≡-to-≅ (substLiftCommute c2 c1 σ2 σ1 (t ∷ Γ))))

anilLem : {m n : ℕ} → (ρ : AList m n) → (anil +!+ ρ ≡ ρ) 
anilLem anil = refl
anilLem (r asnoc t' / x) = cong (λ x₁ → x₁ asnoc t' / x) (anilLem r)

lift1SucLem : ∀{m m1 m2 : ℕ} → (σ1 : AList m m1) → (σ2 : AList m1 m2) 
           →  liftAList1 (σ2 +!+ σ1) ≅ liftAList1 σ2 +!+ liftAList1 σ1
lift1SucLem anil σ2 = hrefl
lift1SucLem (t asnoc t' / x) σ2 = hcong (λ x₁ → x₁ asnoc liftType 1 t' / inject₁ x) (lift1SucLem t σ2)

liftAListanil : ∀{m n} → liftAList {m} n anil ≅  anil
liftAListanil {m} {zero} = hrefl
liftAListanil {m} {suc n} = hcong (liftAList1) (liftAListanil {m} {n})


lift1Suc : ∀{m m1 m2 : ℕ} →  (c1 c2 : ℕ) → (σ1 : AList (c1 + m) m1) → (σ2 : AList (c2 + m1) m2) 
           →  (liftAList 1 (σ2 +!+ (liftAList c2 σ1))) ≅ ((liftAList 1 σ2) +!+ (liftAList (suc c2)) σ1)
lift1Suc c1 c2 σ1 σ2 rewrite (anilLem (liftAList1 (liftAList1 (liftAList c2 σ1)))) = lift1SucLem (liftAList c2 σ1) σ2

liftCxtAddEqLem : ∀(c1 c2 : ℕ) → (1 + c2) + c1 ≡ (c1 + suc c2)
liftCxtAddEqLem c1 c2 rewrite +-comm c2 c1 = sym (+-suc c1 c2)

liftCxtAddEq : ∀{m n : ℕ} →  (c1 c2 : ℕ) → (Γ : Cxt {m} n) → liftCxt 1 (liftCxt c2 (liftCxt c1 Γ)) ≅ liftCxt (c1 + suc c2) Γ
liftCxtAddEq {m} {n} c1 c2 Γ  =
                           H.begin
                             liftCxt 1 (liftCxt c2 (liftCxt c1 Γ))
                           H.≅⟨ liftCxtAdd 1 c2 (liftCxt c1 Γ) ⟩
                             liftCxt (1 + c2) (liftCxt c1 Γ)
                           H.≅⟨ liftCxtAdd (1 + c2) c1 Γ ⟩
                             liftCxt ((1 + c2) + c1) Γ
                           H.≅⟨ hcong (λ x → liftCxt x Γ) (≡-to-≅ (liftCxtAddEqLem c1 c2)) ⟩
                             liftCxt (c1 + suc c2) Γ                    
                            
                           H.∎

substLiftCxtEq : ∀{m m1 m2 n : ℕ} → {σ1 : AList m1 m} → {σ2 : AList m2 m} →
                                       {Γ1 : Cxt {m1} n} → {Γ2 : Cxt {m2} n} → m1 ≡ m2 →
                                                 σ1 ≅ σ2 → Γ1 ≅ Γ2 →
                                                   substCxt σ1 Γ1 ≅ substCxt σ2 Γ2
substLiftCxtEq refl hrefl hrefl = hrefl
\end{code}
}
