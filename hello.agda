data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
zero + n = n
suc a + b = suc (a + b)

halve : Nat -> Nat
halve zero = zero
halve (suc zero) = zero
halve (suc (suc n)) = suc zero + halve n

_*_ : Nat -> Nat -> Nat
zero * _ = zero
suc n * m = m + (n * m)

data Bool : Set where
  false : Bool
  true : Bool

not : Bool -> Bool
not false = true
not true = false

_&&_ : Bool -> Bool -> Bool
false && b = false
true && b = b

_||_ : Bool -> Bool -> Bool
false || b = b
true || b = true

id : {A : Set} -> A -> A
id x = x

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

infixr 5 _::_

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

infixr 4 _,_

fst : {A B : Set} -> A × B -> A
fst (a , _) = a

snd : {A B : Set} -> A × B -> B
snd (_ , b) = b

length : {A : Set} → List A → Nat
length [] = zero
length (_ :: xs) = 1 + length xs

_++_ : {A : Set} → List A → List A → List A
[] ++ b = b
(x :: a) ++ b = x :: (a ++ b)

map : {A B : Set} -> (A -> B) -> List A -> List B
map f [] = []
map f (x :: xs) = f x :: map f xs

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A -> Maybe A

lookup : {A : Set} -> List A -> Nat -> Maybe A
lookup [] _ = nothing
lookup (x :: _) 0 = just x
lookup (_ :: xs) (suc k) = lookup xs k

data Vec (A : Set) : Nat -> Set where
  [] : Vec A 0
  _::_ : {k : Nat} -> A -> Vec A k -> Vec A (suc k)

downFrom : (n : Nat) -> Vec Nat n
downFrom 0 = []
downFrom (suc n) = n :: downFrom n

_++Vec_ : {A : Set} {n m : Nat} -> Vec A n -> Vec A m -> Vec A (n + m)
[] ++Vec ys = ys
(x :: xs) ++Vec ys = x :: (xs ++Vec ys)

head : {A : Set} {n : Nat} -> Vec A (suc n) -> A
head (x :: _) = x

tail : {A : Set} {n : Nat} -> Vec A (suc n) -> Vec A n
tail (_ :: xs) = xs

dotProduct : {n : Nat} -> Vec Nat n -> Vec Nat n -> Nat
dotProduct [] [] = 0
dotProduct (x :: xs) (y :: ys) = (x * y) + dotProduct xs ys

data Fin : Nat -> Set where
  zero : {k : Nat} -> Fin (suc k)
  suc : {k : Nat} -> Fin k -> Fin (suc k)

lookupVec : {A : Set} {n : Nat} → Vec A n → Fin n → A
lookupVec (x :: xs) zero = x
lookupVec (x :: xs) (suc i) = lookupVec xs i

putVec : {A : Set} {n : Nat} → Fin n → A → Vec A n → Vec A n
putVec zero a (_ :: xs) = a :: xs
putVec (suc i) a (x :: xs) = x :: putVec i a xs

data Σ (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) ->  B a -> Σ A B

_×'_ : (A B : Set) → Set
A ×' B = Σ A (λ _ → B)

fstΣ : {A : Set} {B : A -> Set} -> Σ A B -> A
fstΣ (a , _) = a

sndΣ : {A : Set} {B : A -> Set} -> (z : Σ A B) -> B (fstΣ z)
sndΣ (_ , b) = b

List' : (A : Set) → Set
List' A = Σ Nat (Vec A)

x'2x : {A B : Set} -> A ×' B -> A × B
x'2x (a , x) = a , x

x2x' : {A B : Set} -> A × B -> A ×' B
x2x' (a , x) = a , x

[]' : {A : Set} -> List' A
[]' = (0 , [])

_::'_ : {A : Set} -> A -> List' A -> List' A
a ::' (n , xs) = (suc n , a :: xs)

list2list' : {A : Set} -> List A -> List' A
list2list' [] = []'
list2list' (x :: as) = x ::' (list2list' as)

list'2list : {A : Set} -> List' A -> List A
list'2list (_ , []) = []
list'2list (suc n , x :: v) = x :: list'2list (n , v)

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

absurd : {A : Set} -> ⊥ -> A
absurd ()

ex3-2-1 : {A B : Set} -> A -> B -> A
ex3-2-1 a _ = a

data Either (A B : Set) : Set where
  left : A -> Either A B
  right : B -> Either A B

ex3-2-2 : {A : Set} -> (A × ⊤) -> Either A ⊥
ex3-2-2 (x , _) = left x

ex3-2-3 : {A B C : Set} -> (A -> B -> C) -> A × B -> C
ex3-2-3 f (a , b) = f a b

ex3-2-4 : {A B C : Set} -> A × (Either B C) -> Either (A × B) (A × C)
ex3-2-4 (a , left b) = left (a , b)
ex3-2-4 (a , right c) = right (a , c)

ex3-2-5 : {A B C D : Set} -> (A -> C) × (B -> D) -> (A × B) -> (C × D)
ex3-2-5 (a2c , b2d) (a , b) = (a2c a , b2d b)

ex3-3 : {P : Set} -> (Either P (P -> ⊥) -> ⊥) -> ⊥
ex3-3 f = f (right (λ p -> f (left p)))

data IsEven : Nat → Set where
  even-zero : IsEven zero
  even-suc2 : {n : Nat} → IsEven n → IsEven (suc (suc n))

6-is-even : IsEven 6
6-is-even = even-suc2 (even-suc2 (even-suc2 even-zero))

7-is-not-even : IsEven 7 -> ⊥
7-is-not-even (even-suc2 (even-suc2 (even-suc2 ())))

data IsTrue : Bool -> Set where
  is-true : IsTrue true

_=Nat_ : Nat → Nat → Bool
zero =Nat zero = true
suc a =Nat suc b = a =Nat b
_ =Nat _ = false

length-is-3 : IsTrue (length (1 :: 2 :: 3 :: []) =Nat 3)
length-is-3 = is-true

double : Nat -> Nat
double zero = 0
double (suc x) = suc (suc (double x))

double-is-even : (n : Nat) -> IsEven ( double n )
double-is-even zero = even-zero
double-is-even (suc n) = even-suc2 (double-is-even n)

n-equals-n : (n : Nat) → IsTrue (n =Nat n)
n-equals-n zero = is-true
n-equals-n (suc n) = n-equals-n n

half-a-dozen : Σ Nat (λ x -> IsTrue (double x =Nat 12))
half-a-dozen = 6 , is-true

zero-or-suc : (n : Nat) -> Either (IsTrue (n =Nat 0)) (Σ Nat (λ m -> IsTrue (suc m =Nat n)))
zero-or-suc zero = left is-true
zero-or-suc (suc m) = right (m , n-equals-n m)

data _≡_  {A : Set} : A -> A -> Set where
  refl : {a : A} -> a ≡ a
infix 4 _≡_

one-plus-one : 1 + 1 ≡ 2
one-plus-one = refl

zero-not-one : (0 ≡ 1) -> ⊥
zero-not-one ()

id-returns-input : {A : Set} -> (x : A) -> id x ≡ x
id-returns-input x = refl

sym : {A : Set} -> {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

trans : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

cong : {A B : Set} -> {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_end : {A : Set} → (x : A) → x ≡ x
x end = refl

_=⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q
infix 1 begin_
infix 3 _end
infixr 2 _=⟨_⟩_
infixr 2 _=⟨⟩_

[_] : {A : Set} → A → List A
[ x ] = x :: []

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ [ x ]

reverse-singleton : {A : Set} (x : A) -> reverse [ x ] ≡ [ x ]
reverse-singleton x =
  begin
    reverse [ x ]
  =⟨⟩
    reverse (x :: [])
  =⟨⟩
    reverse [] ++ [ x ]
  =⟨⟩
    [] ++ [ x ]
  =⟨⟩
    [ x ]
  end


add-n-zero : (n : Nat) → n + zero ≡ n
add-n-zero zero =
  begin
    zero + zero
    =⟨⟩ -- applying +
    zero
  end

add-n-zero (suc n) =
  begin
    (suc n) + zero
    =⟨⟩ -- applying +
    suc (n + zero)
    =⟨ cong suc (add-n-zero n) ⟩ -- using induction hypothesis
    suc n
  end

ex-4-1-lemma : (m n : Nat) -> m + suc n ≡ suc (m + n)
ex-4-1-lemma zero n =
  begin
    zero + suc n
  =⟨⟩
    suc n
  =⟨⟩
    suc (0 + n)
  end

ex-4-1-lemma (suc m) n =
  begin
    suc m + suc n
  =⟨⟩  -- reverse + definition
    suc (m + suc n)
  =⟨ cong suc (ex-4-1-lemma m n) ⟩  -- inductive hypothesis
    suc (suc (m + n))
  =⟨⟩  -- reverse + definition
    suc (suc m + n)
  end

ex-4-1 : (m n : Nat) -> m + n ≡ n + m
ex-4-1 m zero =
  begin
    m + 0
  =⟨ add-n-zero m ⟩
    m
  =⟨⟩
    zero + m
  end
ex-4-1 m (suc n) =
  begin
    m + suc n
  =⟨ ex-4-1-lemma m n ⟩
    suc (m + n)
  =⟨ cong suc (ex-4-1 m n) ⟩
    suc (n + m)
  =⟨⟩
    suc n + m
  end


add-assoc : (x y z : Nat) → x + (y + z) ≡ (x + y) + z
add-assoc zero y z =
  begin
    zero + ( y + z )
  =⟨⟩
    y + z
  =⟨⟩
    (0 + y) + z
  =⟨⟩
    (zero + y) + z
  end
add-assoc (suc x) y z =
  begin
    suc x + ( y + z )
  =⟨⟩
    suc (x + (y + z))
  =⟨ cong suc (add-assoc x y z) ⟩
    suc ((x + y) + z)
  =⟨⟩
    suc (x + y) + z
  =⟨⟩
    (suc x + y) + z
  end

replicate : {A : Set} → Nat → A → List A
replicate zero x = []
replicate (suc n) x = x :: replicate n x

ex-4-2 : {A : Set} (n : Nat) (a : A) -> length (replicate n a) ≡ n
ex-4-2 zero a =
  begin
    length (replicate 0 a)
  =⟨⟩
    0
  end
ex-4-2 (suc n) a =
  begin
    length (replicate (suc n) a)
  =⟨⟩
    length (a :: replicate n a)
  =⟨⟩
    suc (length (replicate n a))
  =⟨ cong suc (ex-4-2 n a) ⟩
    1 + n
  =⟨⟩
    suc n
  end

append-[] : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
append-[] [] = refl
append-[] (x :: xs) =
  begin
    (x :: xs) ++ []
  =⟨⟩
    x :: (xs ++ [])
  =⟨ cong (x ::_) (append-[] xs) ⟩
    x :: xs
  end

append-assoc : {A : Set} → (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
append-assoc [] ys zs = 
  begin
    ([] ++ ys) ++ zs
  =⟨⟩
    ys ++ zs
  =⟨⟩
    [] ++ (ys ++ zs)  
  end
append-assoc (x :: xs) ys zs =
  begin
    ((x :: xs) ++ ys) ++ zs
  =⟨⟩
    x :: ((xs ++ ys) ++ zs)
  =⟨ cong (x ::_) (append-assoc xs ys zs) ⟩
    x :: (xs ++ (ys ++ zs))
  =⟨⟩
    (x :: xs) ++ (ys ++ zs)
  end

map-id : {A : Set} (xs : List A) → map id xs ≡ xs
map-id [] = refl
map-id (x :: xs) = 
  begin
    map id (x :: xs)
  =⟨⟩
    id x :: map id xs
  =⟨⟩  
    x :: map id xs
  =⟨ cong (x ::_) (map-id xs) ⟩
    x :: xs
  end
    
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘ h = λ x → g (h x)

map-compose : {A B C : Set} (f : B → C) (g : A → B) (xs : List A) → map (f ∘ g) xs ≡ map f (map g xs)
map-compose f g [] = 
  begin
    map (f ∘ g) []
  =⟨⟩ 
    []
  =⟨⟩   
    map f []
  =⟨⟩  
    map f (map g [])
  end
map-compose f g (x :: xs) = 
  begin
    map (f ∘ g) (x :: xs)
  =⟨⟩ 
    ((f ∘ g) x) :: map (f ∘ g) xs
  =⟨ cong ( ((f ∘ g) x) ::_ ) (map-compose f g xs) ⟩   
    ((f ∘ g) x) :: map f (map g xs)
  =⟨⟩  
    (f (g x)) :: map f (map g xs)
  =⟨⟩  
    map f ((g x) :: map g xs)
  =⟨⟩  
    map f (map g (x :: xs))
  end

ex4-4 : {A B : Set} -> (f : A -> B) -> (xs : List A) -> length (map f xs) ≡ length xs
ex4-4 f [] = refl
ex4-4 f (x :: xs) =
  begin
    length (map f (x :: xs))
  =⟨⟩
    length (f x :: map f xs)  
  =⟨⟩
    suc (length (map f xs))  
  =⟨ cong suc (ex4-4 f xs) ⟩  
    suc (length xs)
  =⟨⟩    
    length (x :: xs)  
  end

take : {A : Set} -> Nat -> List A -> List A
take 0 _ = []
take n [] = []
take (suc n) (x :: xs) = x :: (take n xs)

drop : {A : Set} -> Nat -> List A -> List A
drop 0 xs = xs
drop n [] = []
drop (suc n) (x :: xs) = drop n xs


ex4-5 : {A : Set} -> (n : Nat) -> (xs : List A) -> take n xs ++ drop n xs ≡ xs
ex4-5 0 xs =
  begin
    (take 0 xs) ++ (drop 0 xs)
  =⟨⟩
    (take 0 xs) ++ xs
  =⟨⟩
    [] ++ xs 
  =⟨⟩
    xs  
  end
ex4-5 (suc n) [] =
  begin
    take (suc n) [] ++ drop (suc n) []
  =⟨⟩
    [] ++ []
  =⟨⟩
    []
  end
ex4-5 (suc n) (x :: xs) =
  begin
    take (suc n) (x :: xs) ++ drop (suc n) (x :: xs)
  =⟨⟩
    (x :: (take n xs)) ++ drop n xs
  =⟨⟩
    x :: (take n xs  ++ drop n xs)
  =⟨ cong (x ::_) (ex4-5 n xs) ⟩
    x :: xs
  end

data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

flatten : {A : Set} → Tree A → List A
flatten (leaf x) = [ x ]
flatten (node t1 t2) = flatten t1 ++ flatten t2

flatten-acc : {A : Set} → Tree A → List A → List A
flatten-acc (leaf x) xs = x :: xs
flatten-acc (node t1 t2) xs = flatten-acc t1 (flatten-acc t2 xs)

flatten' : {A : Set} → Tree A → List A
flatten' t = flatten-acc t [] 

flatten-acc-flatten : {A : Set} (t : Tree A) (xs : List A) → flatten-acc t xs ≡ flatten t ++ xs
flatten-acc-flatten (leaf x) xs =
  begin
    flatten-acc (leaf x) xs
  =⟨⟩ -- definition of flatten-acc
    x :: xs
  =⟨⟩ -- unapplying ++
    [ x ] ++ xs
  =⟨⟩ -- unapplying flatten
    flatten (leaf x) ++ xs
  end

flatten-acc-flatten (node l r) xs =
  begin
    flatten-acc (node l r) xs
  =⟨⟩ -- applying flatten-acc
    flatten-acc l (flatten-acc r xs)
  =⟨ flatten-acc-flatten l (flatten-acc r xs) ⟩ -- using IH for l
    flatten l ++ (flatten-acc r xs)
  =⟨ cong (flatten l ++_) (flatten-acc-flatten r xs) ⟩ -- using IH for r
    flatten l ++ (flatten r ++ xs)
  =⟨ sym (append-assoc (flatten l) (flatten r) xs) ⟩ -- using append-assoc
    (flatten l ++ flatten r) ++ xs
  =⟨⟩ -- unapplying flatten
    (flatten (node l r)) ++ xs
  end
  
flatten'-flatten : {A : Set} → (t : Tree A) → flatten' t ≡ flatten t
flatten'-flatten t = 
  begin
    flatten-acc t []
  =⟨ flatten-acc-flatten t [] ⟩
    flatten t ++ []
  =⟨ append-[] (flatten t) ⟩
    flatten t  
  end

  