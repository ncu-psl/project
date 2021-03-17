---
title: cj
tags: representation
---
# introduction
## dissection
這次要介紹的是一個叫"dissection"的operation, 簡單來說, 它可以將一個像容器一樣的functor轉為bifunctor, 並在容器中挖洞, 且洞的左右會是不同的element。而這篇主要是以dissection去具體的描述transform data的過程,  並藉此將fold變成tail recursion, 接下來我們先看個簡單的例子。
## expr
```haskell=
data Expr = Val Int | Add Expr Expr

eval :: Expr -> Int
eval (Val i) = i
eval (Add e1 e2) = eval e1 + eval e2
```
### eval
這是一個很簡單的traversal example, 依照不同的constructor作不同的處理, 當我們遇到val時直接return他的值;遇到add時則將兩個expr相加。當然，相加前我們需要知道左右兩邊的值分別是多少, 假設現在有一個e = Add (Add (Val 1) (Val 2)) (Val 3), 並且在eval過程中我們會先處理左邊的expr, 過程看起來會像這樣:
> eval <span style="color: orange" >e</span>
= eval <span style="color: orange" >(Add (Add (Val 1) (Val 2)) (Val 3))</span>
= (eval <span style="color: orange" >(Add (Val 1) (Val 2))</span>) + (eval <span style="color: blue" >(Val 3)</span>)
= ((eval <span style="color: orange" >(Val 1)</span>) + (eval <span style="color: blue" >(Val 2)</span>)) + (eval <span style="color: blue" >(Val 3)</span>)
= <span style="color: orange" >(1 + (eval (Val 2)))</span> + (eval <span style="color: blue" >(Val 3)</span>)
= (<span style="color: blue" >1</span> + (eval <span style="color: orange" >(Val 2)</span>)) + (eval <span style="color: blue" >(Val 3)</span>)
= <span style="color: orange" >(1 + 2)</span> + (eval <span style="color: blue" >(Val 3)</span>)
= <span style="color: orange" >3 + (eval <span style="color: orange" >(Val 3)</span>)</span>
= <span style="color: blue" >3</span> + (eval <span style="color: orange" >(Val 3)</span>)
= <span style="color: orange" >3 + 3</span>
= <span style="color: orange" >6</span>

橘色部份是in focus的data, 藍色則是out of focus的, 當我們停在traversal途中, 我們會有一筆正在處理的資料, 此時expr中會有一個屬於這個資料的洞, 也就是橘色的部份，洞的前面是已經處理完的資料，後面則是還沒處理的部份。

## graph of order of eval
這個範例式可以畫成一個簡單的樹，eval的過程會是這樣
（圖and說明）

既然我們的目的是把traversal變成tail recursion, 那就必須讓recursion的最後一個instruction是recursion call, 所以我們得記下還沒算完的部份, 這邊我會定義一個stack來儲存資訊, 他的type是\[Either Expr Int], either不只表達了我們會有兩種type, 也紀錄下當初往哪個方向走。

回到eval的定義, 當我們遇到add時, 會先處理加號左邊的expr, 此時我們要記下右邊的expr, 左邊算完後, 進到右邊的同時, 我們需要紀錄左邊的結果。根據觀察，我們可以將eval改寫成一個eval machine。
### eval machine
```haskell=
type Stack = [Either Expr Int]

eval :: Expr -> Int
eval e = load e []

load :: Expr -> Stack -> Int
load (Val i) stk = unload i stk
load (Add e1 e2) stk = load e1 (L e2 : stk)

unload :: Int -> Stack -> Int
unload v [] = v
unload v1 (L e2 : stk) = load e2 (R v1 : stk)
unload v2 (R v1 : stk) = unload (v1 + v2) stk
```
### state diagram of eval machine
(圖)

現在可以看一下機器會怎麼處理前面定義的資料，進到load state時, 我們會根據拿到的expr決定要繼續load進左式或return value;進到unload state時我們會希望往右移動，因此如果從儲存的的資料得知剛才往左走的話，現在就往右走，如果stack是空的，代表我們的fold已經完成，因此return value就會是eval的結果。

從這個例子可以看到，stack每層都會是前面所說的"dissection" -- 一個被挖洞的容器裝著兩種不同的element，而且程式的結構也跟type constructor節節相關，因此如果想要generic的處理data，首先要generic的表示它。

# dgp
## simple introduction to desc, functor and mu
礙於時間的關係我只非常的簡單介紹一下dgp，主要會針對polynomial functor作介紹
```haskell=
data Desc : Set₁ where
  Id : Desc                -- element
  K : Set → Desc           -- constant
  _⊕_ : Desc → Desc → Desc -- sum
  _⊗_ : Desc → Desc → Desc -- product

⟦_⟧ : Desc → (Set → Set)
⟦ Id ⟧ X = X
⟦ K A ⟧ X = A
⟦ p ⊕ q ⟧ X = ⟦ p ⟧ X ⊎ ⟦ q ⟧ X
⟦ p ⊗ q ⟧ X = ⟦ p ⟧ X × ⟦ q ⟧ X

data μ (p : Desc) : Set where
  cons : ⟦ p ⟧ (μ p) → μ p

---

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
  cons : ⟦ p ⟧' A (μ' A p) → μ' A p
```

desc是對type的描述，有四個constructor，分別是constant, element, sum跟product，這個中括號會拿一個desc，並把他變成polynomial functor，他的type signature顯示他會拿一個desc, return一個set to set的function, 這個function的parameter會是容器中element的type，然後我們可以用fix point -- 也就是mu去recursive的定義data，從mu的定義來看，mu p 拆開來其實就是一個裝著mu p的容器。

## desc of expr, construct example of expr
根據上面的定義我們可以寫出expr的description:

type ExprD = (K Int) ⊕ (Id ⊗ Id)

K Int對應到Val Int;Id ⊗ Id代表兩個expr的product, 因為我們的add是兩個expr相加。利用ExprD跟Mu我們可以構造出前面範例的e，
```haskell
e = cons (inj₂ ((cons (inj₂ ((cons (inj₁ 1)) 
                            ,(cons (inj₁ 2))
                            )
                      )
                ) 
               ,(cons (inj₁ 3))
               )
         )
```

# dissection, right and tcata
## case analysis of dissection
現在我們可以正式介紹dissection了，要定義dissection我們需要考慮如何在容器內挖洞，接下來會用一些圖來作說明。圖中的黑點是element，左箭頭是clown，右箭頭是joker，代表bifunctor的兩個parameter。
```haskell=
◬ : Desc → Desc'
◬ Id = one₂                           -- <-∙-> -> <-∘->
◬ (K A) = zero₂                       -- <->
◬ (p ⊕ q) = ◬ p ⊕ ◬ q                 -- L <-∙-∙-∙-> -> L <-∙-∘-∙->
                                      -- R <-∙-∙-∙-> -> R <-∙-∘-∙->
◬ (p ⊗ q) = (◬ p ⊗ ◮ q) ⊕ (◭ p ⊗ ◬ q) -- (<-∙-∙-∙->, <-∙-∙-∙->) -> L (<-∙-∘-∙->, <-∙-∙-∙->)
                                      --                         R (<-∙-∙-∙->, <-∙-∘-∙->)

◭ : Desc → Desc'
◭ Id = Fst
◭ (K A) = (K A)
◭ (p ⊕ q) = ◭ p ⊕ ◭ q
◭ (p ⊗ q) = ◭ p ⊗ ◭ q

◮ : Desc → Desc'
◮ Id = Snd
◮ (K A) = (K A)
◮ (p ⊕ q) = ◮ p ⊕ ◮ q
◮ (p ⊗ q) = ◮ p ⊗ ◮ q
```

Id的話因為只有一個element，所以只有一個位置能挖洞，因此結果會是1, K因為沒有element，所以沒辦法挖洞，結果是0，對sum of p and q挖洞我們會得到挖洞後的p或q，最後是product，我們要考慮的是在p還是q上挖洞，如果對p挖洞的話q的element會全部變成joker;對q挖洞的話p的element會全部變成clown，此時我們會需要兩個operation同樣將functor變成bifunctor，但容器內的element全是clown或joker，我們叫他們all clown跟all joker。

Id會改變唯一的元素剛好對應到fst跟snd，K沒有元素所以不會變，sum跟product也是一樣的感覺。
他們的定義應該比dissection簡單多了，畢竟我們不必考慮怎麼挖洞，只需要將裡面的element變成clown或joker。

## right type signature
現在我們知道如何表示stack的element了，只差右移的operation就能定義tcata，定義right之前我們要先想想在容器中向右會有哪些情況，一開始我們會在容器的最左邊，所以容器內全都是joker;當停在traversal途中，容器中會有一個洞，因為我們已經準備好向右了，所以手上會有一個要放進洞理的clown，右移後，我們可能還在容器內，此時洞會往右一格並拿出一個joker，或是我們已經到了容器的右側，那麼容器內就會全是clown。

我們可以用上面定義的三個operation寫出right的type signature:
```haskell=
  right : {p : Desc} {C J : Set}
        → ⟦ p ⟧ J ⊎ (⟦ ◬ p ⟧' C J × C) 
        ------------------------------
        → (J × ⟦ ◬ p ⟧' C J) ⊎ ⟦ p ⟧ C 
```

我們一樣要對desc作case analysis，這邊我就拿product的例子來說明一下，

## case of product of right
我們把p ⊗ q放進functor之後input type看起來會是這樣
```haskell=
⟦ p ⟧ J × ⟦ q ⟧ J ⊎
( ⟦ ◬ p ⟧' C J × ⟦ ◮ q ⟧' C J 
⊎ ⟦ ◭ p ⟧' C J × ⟦ ◬ q ⟧' C J) × C 
```
上下分別是在容器左邊跟in a dissection的狀況，output type會是
```haskell=
J × ( ⟦ ◬ p ⟧' C J × ⟦ ◮ q ⟧' C J 
    ⊎ ⟦ ◭ p ⟧' C J × ⟦ ◬ q ⟧' C J) ⊎ 
⟦ p ⟧ C × ⟦ q ⟧ C
```

簡單來說，在左側或dp的狀況我們需要考慮在p內右移的情況，如果右移後會到p的右側，那我們就要再往q右移一次，否則就會是dp的case，如果現在是dq，我們就要判斷右移後是否仍是dq還是會到q的右側。

## tcata
有了右移後我們就能定義tcata了
```haskell=
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
```

每當進到load state代表我們拿到一棵新的tree，在traversal過程我們隨時都會有一筆in focus的資料，所以在把這棵tree拆開後，我們要試著右移，並進到next state。

next state會依照右移的結果，(t, dp) 或 pv，決定要load t並儲存dp還是unload (fin pv)。

unload 會把儲存的parent tree拿出來放入v右移。

之前的eval machine可以改寫成
eval :: µ ExprP → Int
eval = tcata ｆ where
ｆ (ValP i) = i
ｆ (AddP v1 v2) = v1 + v2

前面的例子e實際traversal的過程會是這樣
stack = ExprD + Int
..