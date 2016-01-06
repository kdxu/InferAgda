module desc where

open import nat
open import inject

open import Data.Unit using (⊤; tt)
open import Data.Nat hiding (fold)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Fin hiding (_+_; _≤_; fold)
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

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

-- 最大で m 個のメタ変数を持つ型を表す型。
data Fix (D : Desc) (m : ℕ) : Set where
  F : ⟦ D ⟧ (Fix D m) → Fix D m
  M : (x : Fin m) → Fix D m

{-# NO_TERMINATION_CHECK #-}
fold : {D : Desc} → {m : ℕ} → {X : Set} →
       (f-F : ⟦ D ⟧ X → X) → (f-M : Fin m → X) → Fix D m → X
fold {D} f-F f-M (F d) = f-F (fmap D (fold f-F f-M) d)
fold f-F f-M (M x) = f-M x

{-# NO_TERMINATION_CHECK #-}
ind : {D : Desc} → {m : ℕ} → (P : Fix D m → Set) →
      (f-F : (d : ⟦ D ⟧ (Fix D m)) → ⟦ D ⟧' P d → P (F d)) →
      (f-M : (x : Fin m) → P (M x)) →
      (t : Fix D m) → P t
ind {D} P f-F f-M (F x) = f-F x (everywhere D P (ind P f-F f-M) x)
ind P f-F f-M (M x) = f-M x

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

{-
-- 上記の fmap-fold の M を M' x ≡ M x である任意の M' でも大丈夫にしたもの
-- （functional extensionality を避けるため）
fmap-fold-ext : {D D' : Desc} → {m : ℕ} →
            {M' : Fin m → Fix D' m} → (∀ x → M' x ≡ M x) →
       (d : ⟦ D ⟧ (Fix D' m)) →
       ⟦ D ⟧' (λ t → fold F M' t ≡ t) d → fmap D (fold F M') d ≡ d
fmap-fold-ext {base} M'x≡Mx tt tt = refl
fmap-fold-ext {D1 :+: D2} M'x≡Mx (inj₁ d) p = cong inj₁ (fmap-fold-ext {D1} M'x≡Mx d p)
fmap-fold-ext {D1 :+: D2} M'x≡Mx (inj₂ d) p = cong inj₂ (fmap-fold-ext {D2} M'x≡Mx d p)
fmap-fold-ext {D1 :*: D2} M'x≡Mx (d1 , d2) (p1 , p2) =
  cong₂ _,_ (fmap-fold-ext {D1} M'x≡Mx d1 p1) (fmap-fold-ext {D2} M'x≡Mx d2 p2)
fmap-fold-ext {rec} M'x≡Mx d p = p

fmap-fold : {D D' : Desc} → {m : ℕ} →
       (d : ⟦ D ⟧ (Fix D' m)) →
       ⟦ D ⟧' (λ t → fold F M t ≡ t) d → fmap D (fold F M) d ≡ d
fmap-fold {D} d p = fmap-fold-ext {D} (λ y → refl) d p

fold-id-ext : {D : Desc} → {m : ℕ} →
          {M' : Fin m → Fix D m} → (∀ x → M' x ≡ M x) →
          (t : Fix D m) → fold F M' t ≡ t
fold-id-ext {D} {m} {M'} M'x≡Mx =
  ind (λ t → fold F M' t ≡ t)
      (λ d x → cong F (fmap-fold-ext {D} M'x≡Mx d x))
      (λ x → M'x≡Mx x)

fold-id : {D : Desc} → {m : ℕ} → (t : Fix D m) → fold F M t ≡ t
fold-id {D} = fold-id-ext {D} (λ y → refl)
-}

-- 型 t 中の型変数部分に f を施した型を返す
mvar-map : {D : Desc} → {m m' : ℕ} → (f : Fin m → Fix D m') → Fix D m → Fix D m'
mvar-map f t = fold F f t

private
  fuse-F : {D D' : Desc} → {m1 m2 m3 : ℕ} →
       (f : Fin m2 → Fix D' m3) → (g : Fin m1 → Fix D' m2) →
       (d : ⟦ D ⟧ (Fix D' m1)) →
       ⟦ D ⟧' (λ t → fold {D'} {m2} {Fix D' m3} F f (fold F g t) ≡ fold F (fold F f ∘ g) t) d →
       fmap D (fold {D'} {m2} {Fix D' m3} F f) (fmap D (fold F g) d) ≡ fmap D (fold F (fold F f ∘ g)) d
  fuse-F {base} f g tt tt = refl
  fuse-F {D1 :+: D2} f g (inj₁ d) p = cong inj₁ (fuse-F {D1} f g d p)
  fuse-F {D1 :+: D2} f g (inj₂ d) p = cong inj₂ (fuse-F {D2} f g d p)
  fuse-F {D1 :*: D2} f g (d1 , d2) (p1 , p2) =
    cong₂ _,_ (fuse-F {D1} f g d1 p1) (fuse-F {D2} f g d2 p2)
  fuse-F {rec} f g d p = p

-- ふたつの fold の f-M を融合する
fuse : {D : Desc} → {m1 m2 m3 : ℕ} →
        (f : Fin m2 → Fix D m3) → (g : Fin m1 → Fix D m2) →
        (t : Fix D m1) →
        fold {D} F f (fold F g t) ≡ fold {D} F (fold F f ∘ g) t
fuse {D} f g =
  ind (λ t → fold {D} F f (fold F g t) ≡ fold {D} F (fold F f ∘ g) t)
      (λ d x → cong F (fuse-F {D} f g d x))
      (λ x → refl)

fuse2 : {D : Desc} → {m1 m2 m3 : ℕ} →
        (f : Fin m2 → Fix D m3) → (g : Fin m1 → Fix D m2) →
        (t : Fix D m1) →
        mvar-map f (mvar-map g t) ≡ mvar-map (mvar-map f ∘ g) t
fuse2 = fuse

fuse3 : {D : Desc} → {m1 m2 m3 : ℕ} →
        (f : Fin m2 → Fin m3) → (g : Fin m1 → Fin m2) →
        (t : Fix D m1) →
        mvar-map (M ∘ f) (mvar-map (M ∘ g) t) ≡ mvar-map (M ∘ (f ∘ g)) t
fuse3 f g = fuse (M ∘ f) (M ∘ g)

-- liftFix m' t : t の中の型変数の数を m' だけ増やす
liftFix : {D : Desc} → (m' : ℕ) → {m : ℕ} → Fix D m → Fix D (m' + m)
liftFix {D} m' {m} t = mvar-map (M ∘ (inject+' m')) t

-- liftFix≤ m≤m' t : t の中の型変数の数を m から m' に増やす
liftFix≤ : {D : Desc} → {m m' : ℕ} → (m≤m' : m ≤ m') → Fix D m → Fix D m'
liftFix≤ m≤m' t = mvar-map (M ∘ (λ x → inject≤ x m≤m')) t

private
  liftFixm≤m-F : {D D' : Desc} → {m : ℕ} → (m≤m : m ≤ m) → (d : ⟦ D ⟧ (Fix D' m)) →
                 ⟦ D ⟧' (λ t → liftFix≤ m≤m t ≡ t) d → fmap D (fold F (M ∘ (λ x → inject≤ x m≤m))) d ≡ d
  liftFixm≤m-F {base} m≤m tt tt = refl
  liftFixm≤m-F {D1 :+: D2} m≤m (inj₁ d) p = cong inj₁ (liftFixm≤m-F {D1} m≤m d p)
  liftFixm≤m-F {D1 :+: D2} m≤m (inj₂ d) p = cong inj₂ (liftFixm≤m-F {D2} m≤m d p)
  liftFixm≤m-F {D1 :*: D2} m≤m (d1 , d2) (p1 , p2) =
    cong₂ _,_ (liftFixm≤m-F {D1} m≤m d1 p1) (liftFixm≤m-F {D2} m≤m d2 p2)
  liftFixm≤m-F {rec} m≤m d p = p

-- liftFixm≤m m≤m t : t を m≤m で増やしても t のまま
liftFixm≤m : {D : Desc} → {m : ℕ} → (m≤m : m ≤ m) → (t : Fix D m) → liftFix≤ m≤m t ≡ t
liftFixm≤m {D} {m} m≤m =
  ind (λ t → liftFix≤ m≤m t ≡ t)
      (λ d x → cong F (liftFixm≤m-F {D} m≤m d x))
      (λ x → cong M (injectm≤m x m≤m))
