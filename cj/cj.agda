open import Agda.Builtin.Nat
open import Data.Sum
open import Data.Product
open import Data.Unit
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)

---------------------------------------------------------------
--polynomial functor

data Desc : Set₁ where
  K : Set → Desc
  Id : Desc
  _⊕_ : Desc → Desc → Desc
  _⊗_ : Desc → Desc → Desc

⟦_⟧ : Desc → (Set → Set)
⟦ K A ⟧ X = A
⟦ Id ⟧ X = X
⟦ p ⊕ q ⟧ X = ⟦ p ⟧ X ⊎ ⟦ q ⟧ X
⟦ p ⊗ q ⟧ X = ⟦ p ⟧ X × ⟦ q ⟧ X

data μ (p : Desc) : Set where
  cons : ⟦ p ⟧ (μ p) → μ p

fmap : {X Y : Set} (p : Desc) → (X → Y) → ⟦ p ⟧ X → ⟦ p ⟧ Y
fmap (K A) f a = a
fmap Id f x = f x
fmap (p ⊕ q) f (inj₁ px) = inj₁ (fmap p f px)
fmap (p ⊕ q) f (inj₂ px) = inj₂ (fmap q f px)
fmap (p ⊗ q) f (px , py) = (fmap p f px) , (fmap q f py)

mutual
  fold : {X : Set} (p : Desc) → (⟦ p ⟧ X → X) → μ p → X
  fold p f (cons ds) = f (fmapFold p p f ds)
-- fold p f (cons ds) = f (fmap p (fold p f) ds)

  fmapFold : {X : Set} (p q : Desc) → (⟦ q ⟧ X → X) → ⟦ p ⟧ (μ q) → ⟦ p ⟧ X
  fmapFold (K A) q f ds = ds
  fmapFold Id q f ds = fold q f ds
  fmapFold (p ⊕ p') q f (inj₁ ds) = inj₁ (fmapFold p q f ds)
  fmapFold (p ⊕ p') q f (inj₂ ds) = inj₂ (fmapFold p' q f ds)
  fmapFold (p ⊗ p') q f (x , y) = fmapFold p q f x , fmapFold p' q f y

----------------- example

--  Val : Nat → Expr
--  Add : Expr → Expr → Expr
--  data Expr : Set where
--   e : Nat ⊎ Expr × Expr → Expr

ExprD = K Nat ⊕ (Id ⊗ Id)
-- Expr' = μ ExprD

e : μ ExprD 
e = cons (inj₂ ((cons (inj₂ ((cons (inj₁ 1)) , (cons (inj₁ 2))))) , (cons (inj₁ 3))))
----------------------------------------
--polynomial bifunctor

data Desc' : Set₁ where
  K : Set → Desc'
  Fst : Desc'
  Snd : Desc'
  _⊕_ : Desc' → Desc' → Desc'
  _⊗_ : Desc' → Desc' → Desc'

⟦_⟧' : Desc' → (Set → Set → Set)
⟦ K A ⟧' X Y = A
⟦ Fst ⟧' X Y = X
⟦ Snd ⟧' X Y = Y
⟦ p ⊕ q ⟧' X Y = ⟦ p ⟧' X Y ⊎ ⟦ q ⟧' X Y
⟦ p ⊗ q ⟧' X Y = ⟦ p ⟧' X Y × ⟦ q ⟧' X Y

data μ' (A : Set) (p : Desc') : Set where
  cons : ⟦ p ⟧' A (μ' A p) → μ' A p

bimap : {S T X Y : Set} (p : Desc') → (S → T) → (X → Y) → ⟦ p ⟧' S X → ⟦ p ⟧' T Y
bimap (K A) f g x = x
bimap Fst f g x = f x
bimap Snd f g x = g x
bimap (p ⊕ q) f g (inj₁ x) = inj₁ (bimap p f g x)
bimap (p ⊕ q) f g (inj₂ x) = inj₂ (bimap q f g x)
bimap (p ⊗ q) f g (x , y) = bimap p f g x , bimap q f g y

mutual 

  fold' :{W X : Set} (p : Desc') → (⟦ p ⟧' W X → X) → μ' W p → X
  fold' p f (cons ds) = f (fmapFold' p p f ds)

  fmapFold' : {W X : Set} (p q : Desc') → (⟦ q ⟧' W X → X) → ⟦ p ⟧' W (μ' W q) → ⟦ p ⟧' W X
  fmapFold' (K A) q f x = x
  fmapFold' Fst q f x = x
  fmapFold' Snd q f x = fold' q f x
  fmapFold' (p ⊕ p₁) q f (inj₁ x) = inj₁ (fmapFold' p q f x)
  fmapFold' (p ⊕ p₁) q f (inj₂ x) = inj₂ (fmapFold' p₁ q f x)
  fmapFold' (p ⊗ p₁) q f (x , y) = fmapFold' p q f x , fmapFold' p₁ q f y

------------------------------------------------------
--Zero

data ⊥ : Set where

refute : {A : Set} → ⊥ → A
refute = λ ()

inflate : {p : Desc} {A : Set} → ⟦ p ⟧ ⊥ → ⟦ p ⟧ A
inflate {p} x = fmap p refute x

zero₁ : Desc
zero₁ = K ⊥ 
zero₂ : Desc'
zero₂ = K ⊥

one₁ : Desc
one₁ = K ⊤
one₂ : Desc'
one₂ = K ⊤

----------------------------------------------------------
--functor to bifunctor

record _~_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _~_

◭ : Desc → Desc'
◭ (K A) = (K A)
◭ Id = Fst
◭ (p ⊕ q) = ◭ p ⊕ ◭ q
◭ (p ⊗ q) = ◭ p ⊗ ◭ q

◮ : Desc → Desc'
◮ (K A) = (K A)
◮ Id = Snd
◮ (p ⊕ q) = ◮ p ⊕ ◮ q
◮ (p ⊗ q) = ◮ p ⊗ ◮ q

◬ : Desc → Desc'
◬ (K A) = zero₂
◬ Id = one₂
◬ (p ⊕ q) = ◬ p ⊕ ◬ q
◬ (p ⊗ q) = (◬ p ⊗ ◮ q) ⊕ (◭ p ⊗ ◬ q)

a : {p : Desc} {C J : Set} → ⟦ ◭ p ⟧' C J ≡ ⟦ p ⟧ C
a {K x} = refl
a {Id} = refl
a {p ⊕ q} {C} {J} rewrite a {p} {C} {J} | a {q} {C} {J} = refl
a {p ⊗ q} {C} {J} rewrite a {p} {C} {J} | a {q} {C} {J} = refl

◭p~p : {p : Desc} {C J : Set} → ⟦ ◭ p ⟧' C J ~ ⟦ p ⟧ C
◭p~p {K A} = record { to = λ a → a ; from = λ a → a }
◭p~p {Id} = record { to = λ x → x ; from = λ x → x }
◭p~p {p ⊕ q} {C} {J} = record { 
                                to = λ { (inj₁ ◭p) → inj₁ (to (◭p~p {p}) ◭p)
                                       ; (inj₂ ◭q) → inj₂ (to (◭p~p {q}) ◭q)
                                       }; 
                                from = λ { (inj₁ pc) → inj₁ (from (◭p~p {p}) pc)
                                         ; (inj₂ qc) → inj₂ (from (◭p~p {q}) qc)
                                         }
                              }
◭p~p {p ⊗ q} = record { 
                        to = λ {(◭p , ◭q) → (to (◭p~p {p}) ◭p) , to (◭p~p {q}) ◭q} ; 
                        from = λ {(pc , qc) → from (◭p~p {p}) pc , from (◭p~p {q}) qc}
                      }

◮p~p : {p : Desc} {C J : Set} → ⟦ ◮ p ⟧' C J ~ ⟦ p ⟧ J
◮p~p {K A} = record { to = λ a → a ; from = λ a → a }
◮p~p {Id} = record { to = λ x → x ; from = λ x → x }
◮p~p {p ⊕ q} {C} {J} = record { 
                                to = λ { (inj₁ ◮p) → inj₁ (to (◮p~p {p}) ◮p)
                                       ; (inj₂ ◮q) → inj₂ (to (◮p~p {q}) ◮q)
                                       }; 
                                from = λ { (inj₁ pj) → inj₁ (from (◮p~p {p}) pj)
                                         ; (inj₂ qj) → inj₂ (from (◮p~p {q}) qj)
                                         }
                              }
◮p~p {p ⊗ q} = record { 
                        to = λ {(◮p , ◮q) → (to (◮p~p {p}) ◮p) , to (◮p~p {q}) ◮q} ; 
                        from = λ {(pj , qj) → from (◮p~p {p}) pj , from (◮p~p {q}) qj}
                      }

----------------------------------------------------------------
--right 

mutual 

  ⊕-mindp : {p q : Desc} {C J : Set}
          → (J × ⟦ ◬ p ⟧' C J) ⊎ ⟦ p ⟧ C
          ------------------------------
          → J × (⟦ ◬ p ⟧' C J ⊎ ⟦ ◬ q ⟧' C J) ⊎ ⟦ p ⟧ C ⊎ ⟦ q ⟧ C
  ⊕-mindp (inj₁ (j , dp)) = inj₁ (j , (inj₁ dp))
  ⊕-mindp (inj₂ pc) = inj₂ (inj₁ pc)

  ⊕-mindq : {p q : Desc} {C J : Set}
          → (J × ⟦ ◬ q ⟧' C J) ⊎ ⟦ q ⟧ C
          ------------------------------
          → J × (⟦ ◬ p ⟧' C J ⊎ ⟦ ◬ q ⟧' C J) ⊎ ⟦ p ⟧ C ⊎ ⟦ q ⟧ C
  ⊕-mindq (inj₁ (j , dq)) = inj₁ (j , inj₂ dq)
  ⊕-mindq (inj₂ qc) = inj₂ (inj₂ qc)

  {-# TERMINATING #-}
  ⊗-mindp : {p q : Desc} {C J : Set}
         → (J × ⟦ ◬ p ⟧' C J ⊎ ⟦ p ⟧ C) × ⟦ q ⟧ J
         -------------------------------------------------------------
         → J × (⟦ ◬ p ⟧' C J × ⟦ ◮ q ⟧' C J ⊎ ⟦ ◭ p ⟧' C J × ⟦ ◬ q ⟧' C J) ⊎ ⟦ p ⟧ C × ⟦ q ⟧ C
  ⊗-mindp {p} {q} (inj₁ (j , dp) , qj) = inj₁ (j , (inj₁ (dp , from (◮p~p {q}) qj)))
  ⊗-mindp {p} {q} (inj₂ pc , qj) = ⊗-mindq {p} {q} (pc , right {q} (inj₁ qj))

  ⊗-mindq : {p q : Desc} {C J : Set}
         → ⟦ p ⟧ C × (J × ⟦ ◬ q ⟧' C J ⊎ ⟦ q ⟧ C)
         -------------------------------------------------------------
         → J × (⟦ ◬ p ⟧' C J × ⟦ ◮ q ⟧' C J ⊎ ⟦ ◭ p ⟧' C J × ⟦ ◬ q ⟧' C J) ⊎ ⟦ p ⟧ C × ⟦ q ⟧ C
  ⊗-mindq {p} {q} (pc , inj₁ (j , dq)) = inj₁ (j , inj₂ (from (◭p~p {p}) pc , dq))
  ⊗-mindq {p} {q} (pc , inj₂ qc) = inj₂ (pc , qc)

  right : {p : Desc} {C J : Set}
        → ⟦ p ⟧ J ⊎ (⟦ ◬ p ⟧' C J × C) 
        ------------------------------
        → (J × ⟦ ◬ p ⟧' C J) ⊎ ⟦ p ⟧ C 

  right {K A} (inj₁ a) = inj₂ a
  right {K A} (inj₂ (x , y)) = refute x

  right {Id} (inj₁ j) = inj₁ (j , tt)
  right {Id} (inj₂ (tt , c)) = inj₂ c

  --   (⟦ p ⟧ J ⊎ ⟦ q ⟧ J) ⊎ (⟦ ◬ p ⟧' C J ⊎ ⟦ ◬ q ⟧' C J) × C
  -- -------------------------------------------------------
  -- → J × (⟦ ◬ p ⟧' C J ⊎ ⟦ ◬ q ⟧' C J) ⊎ ⟦ p ⟧ C ⊎ ⟦ q ⟧ C
  right {p ⊕ q} {C} {J} (inj₁ (inj₁ pj)) = ⊕-mindp {p} {q} (right {p} (inj₁ pj)) 
  right {p ⊕ q} {C} {J} (inj₁ (inj₂ qj)) = ⊕-mindq {p} {q} (right {q} (inj₁ qj))
  right {p ⊕ q} {C} {J} (inj₂ (inj₁ dp , c)) = ⊕-mindp {p} {q} (right {p} (inj₂ (dp , c)))
  right {p ⊕ q} {C} {J} (inj₂ (inj₂ dq , c)) = ⊕-mindq {p} {q} (right {q} (inj₂ (dq , c)))

  --   ⟦ p ⟧ J × ⟦ q ⟧ J ⊎ 
  --   (⟦ ◬ p ⟧' C J × ⟦ ◮ q ⟧' C J ⊎ ⟦ ◭ p ⟧' C J × ⟦ ◬ q ⟧' C J) × C
  --   ------------------------------------------------------------------------------------
  -- → J × (⟦ ◬ p ⟧' C J × ⟦ ◮ q ⟧' C J ⊎ ⟦ ◭ p ⟧' C J × ⟦ ◬ q ⟧' C J)
  --   ⊎ ⟦ p ⟧ C × ⟦ q ⟧ C
  right {p ⊗ q} (inj₁ (pj , qj)) = {!   !} --⊗-mindp {p} {q} ((right {p} (inj₁ pj)) , qj) 
  right {p ⊗ q} (inj₂ (inj₁ (dp , ◮q) , c)) = ⊗-mindp {p} {q} (right {p} (inj₂ (dp , c)) , to (◮p~p {q}) ◮q)
  right {p ⊗ q} (inj₂ (inj₂ (◭p , dq) , c)) = ⊗-mindq {p} {q} (to (◭p~p {p}) ◭p , right {q} (inj₂ (dq , c)))

  -- left : {p : Desc} {C J : Set}
  --      → (J × ⟦ ◬ p ⟧' C J) ⊎ ⟦ p ⟧ C 
  --      ------------------------------
  --      → ⟦ p ⟧ J ⊎ (⟦ ◬ p ⟧' C J × C)
  -- left {K A} (inj₂ a) = inj₁ a
  -- left {Id} (inj₁ (j , dp)) = inj₁ j
  -- left {Id} (inj₂ c) = inj₂ (tt , c)
  -- left {p ⊕ q} (inj₁ (j , inj₁ dp)) with left {p} (inj₁ (j , dp))
  -- ...                                  | inj₁ pj = inj₁ (inj₁ pj)
  -- ...                                  | inj₂ (dp' , c) = inj₂ ((inj₁ dp') , c)
  -- left {p ⊕ q} (inj₁ (j , inj₂ dq)) with left {q} (inj₁ (j , dq))
  -- ...                                  | inj₁ qj = inj₁ (inj₂ qj)
  -- ...                                  | inj₂ (dq' , c) = inj₂ ((inj₂ dq') , c)
  -- left {p ⊕ q} (inj₂ (inj₁ pc)) with left {p} (inj₂ pc)
  -- ...                              | inj₁ pj = inj₁ (inj₁ pj)
  -- ...                              | inj₂ (dp , c) = inj₂ ((inj₁ dp) , c)
  -- left {p ⊕ q} (inj₂ (inj₂ qc)) with left {q} (inj₂ qc)
  -- ...                              | inj₁ qj = inj₁ (inj₂ qj)
  -- ...                              | inj₂ (dq , c) = inj₂ ((inj₂ dq) , c)
  -- left {p ⊗ q} (inj₁ (j , inj₁ (dp , jq))) with left {p} (inj₁ (j , dp))
  -- ... | inj₁ pj = inj₁ (pj , (to (◮p~p {q}) jq))
  -- ... | inj₂ (dp' , c) = inj₂ ((inj₁ (dp' , jq)) , c)
  -- left {p ⊗ q} (inj₁ (j , inj₂ (cp , dq))) with left {q} (inj₁ (j , dq)) | left {p} (inj₂ (to (◭p~p {p}) cp))
  -- ... | inj₁ qj | inj₁ pj = inj₁ (pj , qj)
  -- ... | inj₁ qj | inj₂ (dp , c) = inj₂ ((inj₁ (dp , from (◮p~p {q}) qj)) , c)
  -- ... | inj₂ (dq' , c) | _ = inj₂ ((inj₂ (cp , dq')) , c)
  -- left {p ⊗ q} (inj₂ (pc , qc)) with left {q} (inj₂ qc) | left {p} (inj₂ pc)
  -- ... | inj₁ qj | inj₁ pj = inj₁ (pj , qj)
  -- ... | inj₁ qj | inj₂ (dp , c) = inj₂ ((inj₁ (dp , from (◮p~p {q}) qj)) , c)
  -- ... | inj₂ (dq , c) | _ = inj₂ ((inj₂ (from (◭p~p {p}) pc , dq)) , c)

-------------------------------------------------------------------
-- tail recursion

{-# TERMINATING #-}
tmap : {p : Desc} {S T : Set} → (S → T) → ⟦ p ⟧ S → ⟦ p ⟧ T
tmap {p} {S} {T} f ps = continue (right {p} (inj₁ ps)) 
  where
    continue : (S × ⟦ ◬ p ⟧' T S) ⊎ ⟦ p ⟧ T → ⟦ p ⟧ T
    continue (inj₁ (s , dp)) = continue (right {p} (inj₂ (dp , f s)))
    continue (inj₂ pt) = pt

--------------------------------------------------------------------
--tail recursion 

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

mutual
  {-# TERMINATING #-}
  load : {p : Desc} {V : Set} → (⟦ p ⟧ V → V) → μ p → List (⟦ ◬ p ⟧' V (μ p)) → V
  load {p} f (cons pj) stk = next f (right {p} (inj₁ pj)) stk

  {-# TERMINATING #-}
  next : {p : Desc} {V : Set} → (⟦ p ⟧ V → V) → (μ p) × ⟦ ◬ p ⟧' V (μ p) ⊎ ⟦ p ⟧ V → List (⟦ ◬ p ⟧' V (μ p)) → V
  next f (inj₁ (j , dp)) stk = load f j (dp ∷ stk)
  next {p} f (inj₂ pv) stk = unload {p} f (f pv) stk

  unload : {p : Desc} {V : Set} → (⟦ p ⟧ V → V) → V → List (⟦ ◬ p ⟧' V (μ p)) → V
  unload f v [] = v
  unload {p} f v (dp ∷ stk) = next {p} f (right {p} (inj₂ (dp , v))) stk

tcata : {p : Desc} {v : Set} → (⟦ p ⟧ v → v) → μ p → v
tcata f ds = load f ds []

-----------------------------------------------------------------------------
--plug in

plug : {p : Desc} {A : Set} → A → ⟦ ◬ p ⟧' A A → ⟦ p ⟧ A
plug {Id} x dp = x
plug {p ⊕ q} x (inj₁ dp) = inj₁ (plug {p} x dp)
plug {p ⊕ q} x (inj₂ dq) = inj₂ (plug {q} x dq)
plug {p ⊗ q} x (inj₁ (dp , jq)) = plug {p} x dp , to (◮p~p {q}) jq
plug {p ⊗ q} x (inj₂ (cp , dq)) = (to (◭p~p {p}) cp) , (plug {q} x dq)

-------------------------------------------------------------------------------
--zipping around

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

zUp : {p : Desc}
    → μ p × List (⟦ ◬ p ⟧' (μ p) (μ p))
    ---------------------------------------
    → Maybe (μ p × List (⟦ ◬ p ⟧' (μ p) (μ p)))
zUp (t , []) = Nothing
zUp {p} (t , (dp ∷ dps)) = Just (cons (plug {p} {μ p} t dp) , dps)

zDown : {p : Desc}
      → μ p × List (⟦ ◬ p ⟧' (μ p) (μ p))
      ---------------------------------------
      → Maybe (μ p × List (⟦ ◬ p ⟧' (μ p) (μ p)))
zDown {p} (cons pt , dps) with right {p} (inj₁ pt)
...                          | inj₁ (t , dp) = Just (t , dp ∷ dps)
...                          | inj₂ _ = Nothing

zRight : {p : Desc}
       → μ p × List (⟦ ◬ p ⟧' (μ p) (μ p))
       ---------------------------------------
       → Maybe (μ p × List (⟦ ◬ p ⟧' (μ p) (μ p)))
zRight (t , []) = Nothing
zRight {p} (t , dp ∷ dps) with right {p} (inj₂ (dp , t))
... | inj₁ (t' , dp') = Just (t' , (dp' ∷ dps))
... | inj₂ _ = Nothing

-- zLeft : {p : Desc}
--       → μ p × List (⟦ ◬ p ⟧' (μ p) (μ p))
--       ---------------------------------------
--       → Maybe (μ p × List (⟦ ◬ p ⟧' (μ p) (μ p)))
-- zLeft (t , []) = Nothing
-- zLeft {p} (t , (dp ∷ dps)) with left {p} (inj₁ (t , dp))
-- ... | inj₁ _ = Nothing
-- ... | inj₂ (dp' , t') = Just (t' , (dp' ∷ dps))

------------------------------------------------------------------------
--division

-- 𝑙 : Desc → Set → Set
-- 𝑙 p A = ⟦ ◬ p ⟧' ⊥ A

divide : {p : Desc} {A : Set} → ⟦ p ⟧ A → A × ⟦ ◬ p ⟧' ⊥ A ⊎ ⟦ p ⟧ ⊥
divide {p} pa = right {p} (inj₁ pa)

unite : {p : Desc} {A : Set} → A × ⟦ ◬ p ⟧' ⊥ A ⊎ ⟦ p ⟧ ⊥ → ⟦ p ⟧ A
unite {p} (inj₁ (a , dp)) = plug {p} a (inflateFst {p} dp)
  where
  inflateFst : {p : Desc} {X Y : Set} → ⟦ ◬ p ⟧' ⊥ Y → ⟦ ◬ p ⟧' X Y
  inflateFst {p} dp = bimap (◬ p) refute (λ x → x) dp
unite {p} (inj₂ pz) = inflate {p} pz
