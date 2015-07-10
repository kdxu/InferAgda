module mgu where

open import Data.Unit hiding (_≤_)
open import Data.Nat hiding (fold)
open import Data.Nat.Properties
open import Data.Fin hiding (_+_; _≤_; fold)
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

---------------------------------------------------------------

open import Algebra.Structures
 -- for type definitions, such as IsCommutativeSemiring
private module M = IsCommutativeSemiring

+-comm : ∀ m n → m + n ≡  n + m
+-comm = M.+-comm isCommutativeSemiring

---------------------------------------------------------------

infixl 6 _:+:_
infixl 7 _:*:_

data Desc : Set₁ where
  base  : Desc
  _:+:_ : Desc → Desc → Desc
  _:*:_ : Desc → Desc → Desc
  rec   : Desc

⟦_⟧ : Desc → Set → Set
⟦ base      ⟧ X = ⊤
⟦ d1 :+: d2 ⟧ X = ⟦ d1 ⟧ X ⊎ ⟦ d2 ⟧ X
⟦ d1 :*: d2 ⟧ X = ⟦ d1 ⟧ X × ⟦ d2 ⟧ X
⟦ rec       ⟧ X = X
infix 5 ⟦_⟧

⟦_⟧' : (D : Desc) → {R : Set} → (P : R → Set) →  ⟦ D ⟧ R → Set
⟦ base      ⟧' P tt = ⊤
⟦ d1 :+: d2 ⟧' P (inj₁ x) = ⟦ d1 ⟧' P x
⟦ d1 :+: d2 ⟧' P (inj₂ x) = ⟦ d2 ⟧' P x
⟦ d1 :*: d2 ⟧' P (x1 , x2) = ⟦ d1 ⟧' P x1 × ⟦ d2 ⟧' P x2
⟦ rec       ⟧' P x = P x

everywhere : (D : Desc) → {R : Set} → (P : R → Set) → ((x : R) → P x) → 
             (d : ⟦ D ⟧ R) → ⟦ D ⟧' P d
everywhere base P f tt = tt
everywhere (D1 :+: D2) P f (inj₁ x) = everywhere D1 P f x
everywhere (D1 :+: D2) P f (inj₂ x) = everywhere D2 P f x
everywhere (D1 :*: D2) P f (x1 , x2) =
  (everywhere D1 P f x1 , everywhere D2 P f x2)
everywhere rec P f d = f d

fmap : (D : Desc) → {X Y : Set} → (X → Y) → ⟦ D ⟧ X → ⟦ D ⟧ Y
fmap base f x = tt
fmap (D1 :+: D2) f (inj₁ x) = inj₁ (fmap D1 f x)
fmap (D1 :+: D2) f (inj₂ x) = inj₂ (fmap D2 f x)
fmap (D1 :*: D2) f (x1 , x2) = (fmap D1 f x1 , fmap D2 f x2)
fmap rec f x = f x

{-
fmap-id : {X : Set} → (D : Desc) → {DX : ⟦ D ⟧ X} → fmap D (λ x → x) DX ≡ DX
fmap-id base {tt} = refl
fmap-id (D1 :+: D2) {inj₁ DX} = cong inj₁ (fmap-id D1)
fmap-id (D1 :+: D2) {inj₂ DX} = cong inj₂ (fmap-id D2)
fmap-id (D1 :*: D2) = cong₂ _,_ (fmap-id D1) (fmap-id D2)
fmap-id rec = refl

-- functional extensionality
postulate
  ext : forall {A B : Set} {f g : A -> B} -> (∀ (a : A) -> f a ≡ g a) -> f ≡ g

fmap-id2 : {X : Set} → (D : Desc) → fmap D {X} (λ x → x) ≡ λ DX → DX
fmap-id2 D = ext (λ d → fmap-id D)
-}

-- 最大で m 個のメタ変数を持つ型を表す型。
data Fix (D : Desc) (m : ℕ) : Set where
  F : ⟦ D ⟧ (Fix D m) → Fix D m
  M : (x : Fin m) → Fix D m

{-# NO_TERMINATION_CHECK #-}
fold : {D : Desc} → {m : ℕ} → {X : Set} →
           (⟦ D ⟧ X → X) → (Fin m → X) → Fix D m → X
fold {D} phi f (F d) = phi (fmap D (fold phi f) d)
fold phi f (M x) = f x

{-# NO_TERMINATION_CHECK #-}
ind : {D : Desc} → {m : ℕ} → (X : Fix D m → Set) →
      ((d : ⟦ D ⟧ (Fix D m)) → ⟦ D ⟧' X d → X (F d)) →
      ((x : Fin m) → X (M x)) →
      (t : Fix D m) → X t
ind {D} P phi f (F x) = phi x (everywhere D P (ind P phi f) x)
ind P phi f (M x) = f x

fmap-fold : {D D' : Desc} → {m : ℕ} → 
       (d : ⟦ D ⟧ (Fix D' m)) →
       ⟦ D ⟧' (λ t → fold F M t ≡ t) d → fmap D (fold F M) d ≡ d
fmap-fold {base} tt tt = refl
fmap-fold {D1 :+: D2} (inj₁ d) p = cong inj₁ (fmap-fold {D1} d p)
fmap-fold {D1 :+: D2} (inj₂ d) p = cong inj₂ (fmap-fold {D2} d p)
fmap-fold {D1 :*: D2} (d1 , d2) (p1 , p2) =
  cong₂ _,_ (fmap-fold {D1} d1 p1) (fmap-fold {D2} d2 p2)
fmap-fold {rec} d p = p

fold-id : {D : Desc} → {m : ℕ} → (t : Fix D m) → fold F M t ≡ t
fold-id {D} = ind (λ t → fold F M t ≡ t)
                  (λ d x → cong F (fmap-fold {D} d x))
                  (λ x → refl)

---------------------------------------------------------------

-- thin x y = y     (if y < x)
--          = suc y (if y >= x)
-- thin x y will never be x.
thin : {m : ℕ} → Fin (suc m) → Fin m → Fin (suc m)
thin {m} zero y = suc y
thin {suc m} (suc x) zero = zero
thin {suc m} (suc x) (suc y) = suc (thin x y)

-- thick x y = just y       (if y < x)
--           = nothing      (if y = x)
--           = just (y - 1) (if y > x)
thick : {m : ℕ} → (x y : Fin (suc m)) → Maybe (Fin m)
thick {m} zero zero = nothing -- x = y だった
thick {m} zero (suc y) = just y -- 濃縮する
thick {zero} (suc ()) zero
thick {suc m} (suc x) zero = just zero -- x 未満なのでそのまま
thick {zero} (suc ()) (suc y)
thick {suc m} (suc x) (suc y) with thick {m} x y
... | just x' = just (suc x')
... | nothing = nothing -- x = y だった

-- thick x x は必ず nothing になる
thickxx≡nothing : ∀ {m : ℕ} (x : Fin (suc m)) → thick x x ≡ nothing
thickxx≡nothing zero = refl
thickxx≡nothing {zero} (suc ())
thickxx≡nothing {suc m} (suc x) with thickxx≡nothing x
... | a rewrite a = refl

-- thick x y が nothing になったら x ≡ y
thickxy-x≡y : ∀ {m : ℕ} (x y : Fin (suc m)) → thick x y ≡ nothing → x ≡ y
thickxy-x≡y zero zero eq = refl
thickxy-x≡y zero (suc y) ()
thickxy-x≡y {zero} (suc ()) zero eq
thickxy-x≡y {suc m} (suc x) zero ()
thickxy-x≡y {zero} (suc ()) (suc y) eq
thickxy-x≡y {suc m} (suc x) (suc y) eq with thick x y | inspect (thick x) y
thickxy-x≡y {suc m} (suc x) (suc y) () | just x' | [ eq' ]
... | nothing | [ eq' ] = cong suc (thickxy-x≡y x y eq')

-- 型 t 中の型変数部分に f を施した型を返す
mvar-map : {D : Desc} → {m m' : ℕ} → (f : Fin m → Fix D m') → Fix D m → Fix D m'
mvar-map f t = fold F f t
-- mvar-map {D} {m} {m'} f t = fold {D} {m} {Fix D m'} {!F!} f t

-- 型 t 中の全ての型変数に f を施す
mvar-map-fin : {D : Desc} → {m m' : ℕ} → (f : Fin m → Fin m') → Fix D m → Fix D m'
mvar-map-fin f = mvar-map (M ∘ f)

-- inject+' n x : x の型を n だけ持ち上げる
-- Fin の inject+ は結論部が Fin (m' + m)
inject+' : ∀ m' {m} → Fin m → Fin (m' + m)
inject+' zero x = x
inject+' (suc m) x = inject₁ (inject+' m x)

-- liftFix m' t : t の中の型変数の数を m' だけ増やす
liftFix : {D : Desc} → (m' : ℕ) → {m : ℕ} → Fix D m → Fix D (m' + m)
liftFix {D} m' {m} t = mvar-map-fin (inject+' m') t

-- liftFix≤ m≤m' t : t の中の型変数の数を m から m' に増やす
liftFix≤ : {D : Desc} → {m m' : ℕ} → (m≤m' : m ≤ m') → Fix D m → Fix D m'
liftFix≤ m≤m' t = mvar-map-fin (λ x → inject≤ x m≤m') t

-- 全ての型変数に M を付け直すだけなら変化なし
M-id : {D : Desc} → {m : ℕ} → (t : Fix D m) → mvar-map M t ≡ t
M-id {D} = ind (λ t → mvar-map M t ≡ t)
               (λ d x → cong F (fmap-fold {D} d x))
               (λ x → refl)

--

check-M : {D : Desc} → {m : ℕ} → Fin (suc m) → Fin (suc m) → Maybe (Fix D m)
check-M x y with thick x y
... | just y' = just (M y')
... | nothing = nothing -- x が現れた（x = y だった）

check-F' : {D D' : Desc} → {m : ℕ} → Fin (suc m) →
           ⟦ D ⟧ (Maybe (Fix D' m)) → Maybe (⟦ D ⟧ (Fix D' m))
check-F' {base} x tt = just tt
check-F' {D1 :+: D2} x (inj₁ t) with check-F' {D1} x t
... | nothing = nothing
... | just t' = just (inj₁ t')
check-F' {D1 :+: D2} x (inj₂ t) with check-F' {D2} x t
... | nothing = nothing
... | just t' = just (inj₂ t')
check-F' {D1 :*: D2} x (t1 , t2) with check-F' {D1} x t1
... | nothing = nothing
... | just t1' with check-F' {D2} x t2
... | nothing = nothing
... | just t2' = just (t1' , t2')
check-F' {rec} x t = t

check-F : {D : Desc} → {m : ℕ} → Fin (suc m) →
          ⟦ D ⟧ (Maybe (Fix D m)) → Maybe (Fix D m)
check-F {D} x t with check-F' {D} x t
... | nothing = nothing
... | just t' = just (F t')
{-
D = base :+: rec なら、
[D](Maybe (Fix D m)) = Unit + (Maybe (Fix D m))
Unit + (Maybe (F ([D] (Fix D m))))

D = base :+: rec :*: rec なら、
[D](Maybe (Fix D m)) = Unit + (Maybe (Fix D m)) * (Maybe (Fix D m))

Unit + (Maybe (F ([D] (Fix D m)))) * (Maybe (F ([D] (Fix D m))))

Fix D m = F (t : [D](Fix D m)) or M y

[D](Maybe ([D] (Fix D' m))) =
  Unit + (Maybe ([D] (Fix D' m))) * (Maybe ([D] (Fix D' m)))
-}

-- check x t : x 番の型変数が型 t の中に現れるかをチェックする。
-- 現れなければ、型 t を x で thick できるはずなので、それを返す。
-- 現れたら、nothing を返す。
check : {D : Desc} → {m : ℕ} → Fin (suc m) → Fix D (suc m) → Maybe (Fix D m)
check {D} {m} x t = fold (check-F x)
                         (check-M {D} x)
                         t

{-
checkInvArrow : ∀ {n : ℕ} (x : Fin (suc n)) (t1 t2 : Type (suc n)) {t' : Type n} →
                check x (t1 ⇒ t2) ≡ just t' → 
                Σ[ t1' ∈ Type n ] Σ[ t2' ∈ Type n ]
                (t' ≡ t1' ⇒ t2') × (check x t1 ≡ just t1') × (check x t2 ≡ just t2')
checkInvArrow x t1 t2 eq with check x t1 | check x t2
checkInvArrow x t1 t2 refl | just t1' | just t2' = (t1' , t2' , refl , refl , refl)
checkInvArrow x t1 t2 () | just t1' | nothing
checkInvArrow x t1 t2 () | nothing | just t2'
checkInvArrow x t1 t2 () | nothing | nothing

checkInvVar : ∀ {n : ℕ} (x y : Fin (suc n)) {t' : Type n} →
                check x (TVar y) ≡ just t' → 
                Σ[ y' ∈ Fin n ] 
                (t' ≡ TVar y') × (thick x y ≡ just y') 
checkInvVar x y eq with thick x y 
checkInvVar x y refl | just x₁ = x₁ , (refl , refl)
checkInvVar x y () | nothing
-}

-- t' for x : x 番の型変数を型 t' に unify するような unifier を返す。
_for_ : {D : Desc} → {m : ℕ} →
        (t' : Fix D m) → (x : Fin (suc m)) → Fin (suc m) → Fix D m
_for_ t' x y with thick x y
... | just y' = M y'
... | nothing = t'

-- 代入 (σ : AList m n) 関係

-- AList D m n : m 個の型変数を持つ型を n 個の型変数を持つ型にする代入
data AList (D : Desc) : ℕ → ℕ → Set where
  anil : {m : ℕ} → AList D m m -- 何もしない代入
  _asnoc_/_ : {m : ℕ} {m' : ℕ} → (σ : AList D m m') → (t' : Fix D m) →
              (x : Fin (suc m)) → AList D (suc m) m'
          -- x を t' にした上で、さらにσを行う代入

-- liftAList1 lst : lst の中の型変数の数を 1 だけ増やす
liftAList1 : {D : Desc} → {m m' : ℕ} →
             AList D m m' → AList D (suc m) (suc m')
liftAList1 anil = anil
liftAList1 (σ asnoc t / x) = liftAList1 σ asnoc liftFix 1 t / inject₁ x

-- liftAList n lst : lst の中の型変数の数を n だけ増やす
liftAList : {D : Desc} → {m m' : ℕ} →
            (n : ℕ) → AList D m m' → AList D (n + m) (n + m')
liftAList zero σ = σ
liftAList (suc n) σ = liftAList1 (liftAList n σ)
m'∸m+m≡m' : {m m' : ℕ} → m ≤ m' → m' ∸ m + m ≡ m'
m'∸m+m≡m' {m} {m'} m≤m' = begin
  m' ∸ m + m   ≡⟨ +-comm (m' ∸ m) m ⟩
  m + (m' ∸ m) ≡⟨ m+n∸m≡n m≤m' ⟩
  m'           ∎

-- liftAList≤ m≤m' lst : lst の中の型変数の数を m から m' まで増やす
liftAList≤ : {D : Desc} → {l m m' : ℕ} → (m≤m' : m ≤ m') →
             AList D l m → AList D ((m' ∸ m) + l) m'
liftAList≤ {D} {l} {m} {m'} m≤m' σ =
  subst (λ n → AList D ((m' ∸ m) + l) n)
        ( m'∸m+m≡m' m≤m')
        (liftAList (m' ∸ m) σ)

-- ふたつの代入をくっつける
_++_ : {D : Desc} → {l m n : ℕ} →
       (ρ : AList D m n) → (σ : AList D l m) →  AList D l n
ρ ++ anil = ρ
ρ ++ (alist asnoc t / x) = (ρ ++ alist) asnoc t / x

-- 後ろのσを持ち上げてから、ふたつの代入をくっつける
_+⟨_⟩_ : {D : Desc} → {l m m' n : ℕ} →
        (ρ : AList D m' n) → (m≤m' : m ≤ m') → (σ : AList D l m) →
        AList D ((m' ∸ m) + l) n
ρ +⟨ m≤m' ⟩ σ = ρ ++ (liftAList≤ m≤m' σ)

-- 代入σを Fin m → Fix D m' の関数に変換する
mvar-sub : {D : Desc} → {m m' : ℕ} → (σ : AList D m m') → Fin m → Fix D m'
mvar-sub anil = M
mvar-sub (σ asnoc t' / x) = mvar-map (mvar-sub σ) ∘ (t' for x)

-- substFix σ t : t に σ を適用した型を返す
substFix : {D : Desc} → {m m' : ℕ} → AList D m m' → Fix D m → Fix D m' 
substFix σ t = mvar-map (mvar-sub σ) t

-- substFix≤ σ m≤m' t : t の中の型変数の数を m から m'' に増やしてからσをかける
substFix≤ : {D : Desc} → {m m' m'' : ℕ} → AList D m'' m' →
            (m≤m'' : m ≤ m'') → Fix D m → Fix D m'
substFix≤ σ m≤m'' t = mvar-map (mvar-sub σ) (liftFix≤ m≤m'' t)

--

-- 型変数 x と y を unify する代入を返す 
flexFlex : {D : Desc} → {m : ℕ} → (x y : Fin m) → Σ[ m' ∈ ℕ ] AList D m m'
flexFlex {D} {zero} () y
flexFlex {D} {suc m} x y with thick x y 
... | nothing = (suc m , anil) -- x = y だった。代入の必要なし
... | just y' = (m , anil asnoc (M y') / x) -- M y' for x を返す

-- 型変数 x と型 t を unify する代入を返す
-- x が t に現れていたら nothing を返す
flexRigid : {D : Desc} → {m : ℕ} → (x : Fin m) → (t : Fix D m) →
                Maybe (Σ[ m' ∈ ℕ ] AList D m m')
flexRigid {D} {zero} () t
flexRigid {D} {suc m} x t with check x t
... | nothing = nothing -- x が t に現れていた
... | just t' = just (m , anil asnoc t' / x) -- t' for x を返す

-- 型 t1 と t2（に acc をかけたもの）を unify する代入を返す
mutual
  amgu : {D : Desc} → {m : ℕ} →
         (t1 t2 : Fix D m) → (acc : Σ[ m' ∈ ℕ ] AList D m m') →
         Maybe (Σ[ m' ∈ ℕ ] AList D m m')
  amgu {D} (F t1) (F t2) (m' , anil) = amgu' {D} t1 t2 (m' , anil)
  amgu (F t1) (M x2) (m' , anil) = flexRigid x2 (F t1)
  amgu (M x1) (F t2) (m' , anil) = flexRigid x1 (F t2)
  amgu (M x1) (M x2) (m' , anil) = just (flexFlex x1 x2)
  amgu {D} {suc m} t1 t2 (m' , σ asnoc r / z)
    with amgu {D} {m} (mvar-map (r for z) t1) (mvar-map (r for z) t2) (m' , σ)
  ... | just (m'' , σ') = just (m'' , (σ' asnoc r / z))
  ... | nothing = nothing

  amgu' : {D D' : Desc} → {m : ℕ} →
          (t1 t2 : ⟦ D ⟧ (Fix D' m)) → (acc : Σ[ m' ∈ ℕ ] AList D' m m') →
          Maybe (Σ[ m' ∈ ℕ ] AList D' m m')
  amgu' {base} tt tt acc = just acc
  amgu' {D1 :+: D2} (inj₁ t1) (inj₁ t2) acc = amgu' {D1} t1 t2 acc
  amgu' {D1 :+: D2} (inj₁ t1) (inj₂ t2) acc = nothing
  amgu' {D1 :+: D2} (inj₂ t1) (inj₁ t2) acc = nothing
  amgu' {D1 :+: D2} (inj₂ t1) (inj₂ t2) acc = amgu' {D2} t1 t2 acc
  amgu' {D1 :*: D2} (t11 , t12) (t21 , t22) acc with amgu' {D1} t11 t21 acc
  ... | just acc' = amgu' {D2} t12 t22 acc'
  ... | nothing = nothing
  amgu' {rec} t1 t2 acc = amgu t1 t2 acc

mgu : {D : Desc} → {m : ℕ} →
      (t1 t2 : Fix D m) → Maybe (Σ[ m' ∈ ℕ ] AList D m m')
mgu {D} {m} t1 t2 = amgu t1 t2 (m , anil)

private

  -- test

  D1 : Desc
  D1 = base :+: rec

  TInt : Fix D1 1
  TInt = F (inj₁ tt)

  TIntList : Fix D1 1
  TIntList = F (inj₂ TInt)

  [rec]FixD11 : ⟦ rec ⟧ (Fix D1 1)
  [rec]FixD11 = F (inj₁ tt)

  [D1]FixD11 : ⟦ D1 ⟧ (Fix D1 1)
  [D1]FixD11 = (inj₂ (F (inj₁ tt)))

  [D1]FixD11' : ⟦ D1 ⟧ (Fix D1 1)
  [D1]FixD11' = inj₂ (F (inj₂ (F (inj₁ tt))))

  TIntListList : Fix D1 1
  TIntListList = F (inj₂ (F (inj₂ (F (inj₁ tt)))))

  -- type

  TypeDesc : Desc
  TypeDesc = base :+: rec :*: rec

  Type : (m : ℕ) → Set
  Type m = Fix TypeDesc m

  TVar : {m : ℕ} → (x : Fin m) → Type m
  TVar = M

  TNat : {m : ℕ} → Type m
  TNat = F (inj₁ tt)

  _⇒_ : {m : ℕ} → Type m → Type m → Type m
  t1 ⇒ t2 = F (inj₂ (t1 , t2))

  t1 : Type 4
  t1 = TVar zero ⇒ TVar zero
  -- 0 ⇒ 0

  t2 : Type 4
  t2 = (TVar (suc zero) ⇒ TVar (suc (suc zero))) ⇒ TVar (suc (suc (suc zero)))
  -- (1 ⇒ 2) ⇒ 3

  u12 : Maybe (∃ (AList TypeDesc 4))
  u12 = mgu t1 t2
  -- just
  -- (2 ,
  --  (anil asnoc F (inj₂ (M zero , M (suc zero))) / suc (suc zero))
  --  asnoc F (inj₂ (M zero , M (suc zero))) / zero)
  -- 0 -> 0 ⇒ 1
  -- 2 -> 0 ⇒ 1

  t3 : Type 4
  t3 = (TVar zero ⇒ TVar (suc (suc zero))) ⇒ TVar (suc (suc (suc zero)))

  u13 : Maybe (∃ (AList TypeDesc 4))
  u13 = mgu t1 t3
  -- nothing

{-
--「σ' は σ の拡張になっている」という命題
_extends_ : ∀ {m} (σ' : Σ[ n' ∈ ℕ ] AList m n') (σ : Σ[ n ∈ ℕ ] AList m n) → Set
_extends_ {m} (n' , σ') (n , σ) =
  ∀ (s t : Type m) → substType σ s ≡ substType σ t → substType σ' s ≡ substType σ' t

-- 自分自身は自分自身の拡張になっている
σextendsσ : ∀ {m} (σ : Σ[ n ∈ ℕ ] AList m n) → σ extends σ
σextendsσ σ s t eq = eq

-- 任意のσは anil の拡張になっている
σextendsNil : ∀ {m} (σ : Σ[ n ∈ ℕ ] AList m n) → σ extends (m , anil)
σextendsNil σ s t eq rewrite TVarId s | TVarId t = cong (substType (proj₂ σ)) eq

-- 型変数 x と y を unify する代入を返す 
flexFlex2 : {m : ℕ} → (x y : Fin m) → (Σ[ n ∈ ℕ ] Σ[ σ ∈ AList m n ]
                                         substType σ (TVar x) ≡ substType σ (TVar y))
flexFlex2 {zero} () y
flexFlex2 {suc m} x y with thick x y | inspect (thick x) y
... | nothing | [ thickxy≡nothing ] =
  (suc m , anil , cong TVar (thickxy-x≡y x y thickxy≡nothing))  -- x = y だった。代入の必要なし
... | just y' | [ thickxy≡justy' ] =
  (m , anil asnoc TVar y' / x , cong (TVar ◃) eq)  -- TVar y' for x を返す
  where eq : (TVar y' for x) ◃ (TVar x) ≡ (TVar y' for x) ◃ (TVar y)
        eq rewrite thickxx≡nothing x | thickxy≡justy' = refl

forTVarLem : {m : ℕ} → (x : Fin (suc m)) → ∀(t : Type  m) → t ≡ (t for x) ◃ (TVar x)
forTVarLem x t rewrite thickxx≡nothing x  = refl

flexRigidLem : {m : ℕ} → {t' : Type m} → ∀{t'' : Type m} → (x : Fin (suc m)) → (t : Type (suc m)) → check x t ≡ just t' →  TVar ◃ ((t' for x) ◃ (TVar x)) ≡ (λ y → TVar ◃ (t'' for x) y) ◃ t

flexRigidLem x (TVar x₁) p with check x (TVar x₁) | inspect (check x) (TVar x₁)
flexRigidLem x (TVar x₁) refl | just x₂ | [ eq ] with checkInvVar x x₁ eq
flexRigidLem x (TVar x₁) refl | just .(TVar x₂) | [ eq ] | x₂ , refl , proj₃ rewrite proj₃ |  thickxx≡nothing x = refl
flexRigidLem x (TVar x₁) () | nothing | [ eq ]
flexRigidLem x TInt p with check x TInt | inspect (check x) TInt
flexRigidLem x TInt p | just (TVar x₁) | [ () ]
flexRigidLem x TInt refl | just TInt | [ refl ] rewrite thickxx≡nothing x = refl
flexRigidLem x TInt p | just (x₁ ⇒ x₂) | [ () ]
flexRigidLem x TInt () | nothing | [ eq ] 
flexRigidLem x (t ⇒ t₁) p with check x (t ⇒ t₁)  | inspect (check x) (t ⇒ t₁)
flexRigidLem x (t ⇒ t₁) refl | just (TVar x₁) | [ eq ] with checkInvArrow x t t₁ eq
... | (t1' , t2' , () , b , c)
flexRigidLem x (t ⇒ t₁) p | just TInt | [ eq ] with checkInvArrow x t t₁ eq
... | (t1' , t2' , () , b , c)
flexRigidLem x (t ⇒ t₁) refl | just (x₁ ⇒ x₂) | [ eq ] with checkInvArrow x t t₁ eq
flexRigidLem {t'' = t''} x (t ⇒ t₁) refl | just (x₁ ⇒ x₂) | [ eq ] | .x₁ , .x₂ , refl , b , c rewrite thickxx≡nothing x = 
  cong₂ _⇒_ p q -- (flexRigidLem  t' t b) {!!}
  where p : TVar ◃ x₁ ≡ (λ y → TVar ◃ (t'' for x) y) ◃ t
        p = begin
              TVar ◃ x₁
            ≡⟨  cong (λ x₃ → TVar ◃ x₃) (forTVarLem x x₁) ⟩
              TVar ◃ ((x₁ for x) ◃ (TVar x))
            ≡⟨ flexRigidLem x t b ⟩
              (λ y → TVar ◃ (t'' for x) y) ◃ t
            ∎
        q : TVar ◃ x₂ ≡ (λ y → TVar ◃ (t'' for x) y) ◃ t₁
        q = begin
              TVar ◃ x₂
            ≡⟨  cong (λ x₃ → TVar ◃ x₃) (forTVarLem x x₂) ⟩
              TVar ◃ ((x₂ for x) ◃ (TVar x))
            ≡⟨ flexRigidLem x t₁ c ⟩
              (λ y → TVar ◃ (t'' for x) y) ◃ t₁
            ∎
--  cong₂ _⇒_ (flexRigidLem  t' t b) {!!}
--Goal: x₁ ⇒ x₂ ≡
--      ((λ y → TVar ◃ ((.t'' for x) y | thick x y)) ◃ t) ⇒
--      ((λ y → TVar ◃ ((.t'' for x) y | thick x y)) ◃ t₁)
flexRigidLem x (t ⇒ t₁) () | nothing | [ eq ]

-- 型変数 x と型 t を unify する代入を返す
-- x が t に現れていたら nothing を返す
flexRigid2 : {m : ℕ} → (x : Fin m) → (t : Type m) →
             Maybe (Σ[ n ∈ ℕ ] Σ[ σ ∈ AList m n ] substType σ (TVar x) ≡ substType σ t)
flexRigid2 {zero} () t
flexRigid2 {suc m} x t with check x t | inspect (check x) t
... | nothing | [ checkxt≡nothing ] = nothing -- x が t に現れていた
... | just t' | [ checkxt≡justt' ] = just (m , anil asnoc t' / x , flexRigidLem x t checkxt≡justt') -- t' for x を返す
  -- goal : TVar ◃ ((t' for x) ◃ (TVar x)) ≡ (λ y → TVar ◃ (t' for x) y) ◃ t

substTypeForCommute : ∀ {m n} (σ : AList m n) (r : Type m) (z : Fin (suc m)) (s : Type (suc m)) →
                      substType (σ asnoc r / z) s ≡ substType σ ((r for z) ◃ s)
substTypeForCommute σ r z (TVar x) = refl
substTypeForCommute σ r z TInt = refl
substTypeForCommute σ r z (s1 ⇒ s2) =
  cong₂ _⇒_ (substTypeForCommute σ r z s1) (substTypeForCommute σ r z s2)

substTypeForEq1 : ∀ {m n} (σ : AList m n) (r : Type m) (z : Fin (suc m)) (s t : Type (suc m)) →
                  substType (σ asnoc r / z) s ≡ substType (σ asnoc r / z) t →
                  substType σ ((r for z) ◃ s) ≡ substType σ ((r for z) ◃ t)
substTypeForEq1 σ r z s t eq = 
  begin
    substType σ ((r for z) ◃ s)
  ≡⟨ sym (substTypeForCommute σ r z s)  ⟩
    substType (σ asnoc r / z) s
  ≡⟨ eq ⟩
    substType (σ asnoc r / z) t
  ≡⟨ substTypeForCommute σ r z t ⟩
    substType σ ((r for z) ◃ t)
  ∎

substTypeForEq2 : ∀ {m n} (σ : AList m n) (r : Type m) (z : Fin (suc m)) (s t : Type (suc m)) →
                  substType σ ((r for z) ◃ s) ≡ substType σ ((r for z) ◃ t) →
                  substType (σ asnoc r / z) s ≡ substType (σ asnoc r / z) t
substTypeForEq2 σ r z s t eq = 
  begin
    substType (σ asnoc r / z) s
  ≡⟨ substTypeForCommute σ r z s ⟩
    substType σ ((r for z) ◃ s)
  ≡⟨ eq ⟩
    substType σ ((r for z) ◃ t)
  ≡⟨ sym (substTypeForCommute σ r z t)  ⟩
    substType (σ asnoc r / z) t
  ∎

-- 型 s と t（に acc をかけたもの）を unify する代入を返す
amgu2 : {m : ℕ} → (s t : Type m) → (acc : Σ[ n ∈ ℕ ] AList m n) →
                Maybe (Σ[ n ∈ ℕ ] Σ[ σ ∈ AList m n ]
                       (n , σ) extends acc × substType σ s ≡ substType σ t)
amgu2 TInt     TInt     acc        = just (proj₁ acc , proj₂ acc , σextendsσ acc , refl) -- just acc
amgu2 TInt     (t ⇒ t₁) acc        = nothing
amgu2 (s ⇒ s₁) TInt     acc        = nothing
amgu2 (s ⇒ s₁) (t ⇒ t₁) acc        with amgu2 s t acc
...                               | nothing = nothing
...                               | just (n' , σ' , ex , eq)
                                    with amgu2 s₁ t₁ (n' , σ')
...                               | nothing = nothing
...                               | just (n'' , σ'' , ex2 , eq2) =
                                    just (n'' , σ'' , (λ s₂ t₂ → ex2 s₂ t₂ ∘ ex s₂ t₂) ,
                                                  cong₂ _⇒_ (ex2 s t eq) eq2)
amgu2 (TVar x) (TVar y) (s , anil) with flexFlex2 x y -- just (flexFlex x y)
...                               | (n' , σ' , eq) = just (n' , σ' , σextendsNil (n' , σ') , eq)
amgu2 (TVar x) t        (s , anil) with flexRigid2 x t
...                               | just (n' , σ' , eq) = just (n' , σ' , σextendsNil (n' , σ') , eq)
...                               | nothing = nothing
amgu2 t        (TVar x) (s , anil) with flexRigid2 x t
...                               | just (n' , σ' , eq) = just (n' , σ' , σextendsNil (n' , σ') , sym eq)
...                               | nothing = nothing
amgu2 {suc m} s t (n , σ asnoc r / z)
  with amgu2 {m} ((r for z) ◃ s) ((r for z) ◃ t) (n , σ)
... | nothing = nothing
... | just (n' , σ' , ex , eq) =
      just (n' , σ' asnoc r / z , (λ s' t' ex' → substTypeForEq2 σ' r z s' t'
                                                      (ex ((r for z) ◃ s') ((r for z) ◃ t')
                                                          (substTypeForEq1 σ r z s' t' ex'))) ,
                                    substTypeForEq2 σ' r z s t eq)

-- 型 s と t を unify する代入を返す
mgu2 : {m : ℕ} → (s t : Type m) →
       Maybe (Σ[ n ∈ ℕ ] Σ[ σ ∈ AList m n ] substType σ s ≡ substType σ t)
mgu2 {m} s t with amgu2 {m} s t (m , anil)
... | just (n , σ , ex , eq) = just (n , σ , eq)
... | nothing = nothing
-}
