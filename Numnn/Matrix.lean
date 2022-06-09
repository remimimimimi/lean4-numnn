namespace Numnn.Matrix

universe u

inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : (x : α) → (xs : Vect α ι) → Vect α (ι + 1)
  deriving Repr, DecidableEq, BEq

macro:67 "[]" : term => `(Vect.nil)
infixr:67 " :: " => Vect.cons

def Vect.len : Vect α ι → Nat
  | [] => 0
  | @Vect.cons _ len .. => len + 1

section head
variable [Inhabited α]

def Vect.head? : Vect α ι → Option α
  | [] => none
  | x :: _ => some x

def Vect.head : ι ≠ 0 → Vect α ι → α
  | _, x :: _ => x

end head

def Vect.tail? : Vect α ι → Option (Vect α (ι - 1))
  | [] => none
  | _ :: xs => some xs

def Vect.tail : ι ≠ 0 → Vect α ι → Vect α (ι - 1)
  | _, _ :: xs => xs

def Vect.map (f : α → β) : Vect α ι → Vect β ι
  | [] => []
  | x :: xs => f x :: map f xs

instance : Functor (Vect · ι) where
  map := Vect.map

def Vect.zipWith (f : α → β → γ) : Vect α ι → Vect β ι → Vect γ ι
  | [], [] => []
  | x :: xs, y :: ys => f x y :: zipWith f xs ys

def Vect.foldl (f : β → α → β) (init : β) : Vect α ι → β
  | [] => init
  | x :: xs => foldl f (f init x) xs

def Vect.append : (xs : Vect α ι₁) → (ys : Vect α ι₂) → Vect α (ι₂ + ι₁)
  | [], ys => ys
  | x :: xs, ys => x :: append xs ys
infixl:65 " ++ "  => Vect.append

def Vect.flatten : Vect (Vect α ι₁) ι₂  → Vect α (ι₁ * ι₂)
  | [] => []
  | x :: xs => by
    rw [Nat.mul_add]; simp
    exact x ++ (flatten xs)

def Vect.replicate : (len : Nat) → (x : elem) → Vect elem len
  | 0, _ => []
  | n+1, x => x :: replicate n x

section sum
variable [Inhabited α] [Add α]

def Vect.sum  (v : Vect α ι) : α :=
  Vect.foldl (·+·) Inhabited.default v

def Vect.dot [Inhabited α] [Add α] [Mul α] (v₁ : Vect α ι) (v₂ : Vect α ι) : α :=
  Vect.sum (Vect.zipWith (·*·) v₁ v₂)

end sum

def Vect.toList : Vect α ι → List α
  | [] => .nil
  | x :: xs => [x] ++ toList xs

def List.toVect : (l : List α) → Vect α (l.length)
  | .nil => .nil
  | x :: xs => (x :: []) ++ toVect xs

def Vect.toArray : Vect α ι → Array α
  | [] => #[]
  | x :: xs => #[x] ++ toArray xs

def Array.toVect (a : Array α) : Vect α (a.size) :=
  List.toVect (a.data)

def Vect.toString {α : Type u} [ToString α] : Vect α ι → String :=
  (·.toList.toString)

instance [ToString α] : ToString (Vect α ι) where
  toString := Vect.toString

-- ι₁ - row, ι₂ - col
abbrev Matrix α ι₁ ι₂ := Vect (Vect α ι₂) ι₁

def Vect.toMatrix (m : Vect (Vect α ι₂) ι₁) : Matrix α ι₁ ι₂ := m
def Matrix.toVect (m : Matrix α ι₁ ι₂) : Vect (Vect α ι₂) ι₁ := m

def Matrix.map {α β : Type u} (f : α → β) : Matrix α ι₁ ι₂ → Matrix β ι₁ ι₂ :=
  Vect.map (·.map f)

instance : Functor (Matrix · ι₁ ι₂) where
  map := Matrix.map

def Matrix.zipWith (f : α → β → γ) : Matrix α ι₁ ι₂ → Matrix β ι₁ ι₂ → Matrix γ ι₁ ι₂ :=
  Vect.zipWith (Vect.zipWith f · ·)

def Matrix.foldl (f : β → α → β) (init : β) : Matrix α ι₁ ι₂ → β :=
  Vect.foldl (Vect.foldl f) init

def Matrix.fill (matrix : Matrix α ι₁ ι₂) (elem : α) : Matrix α ι₁ ι₂ :=
  Matrix.map (λ _ => elem) matrix

def Matrix.flatten (matrix : Matrix α ι₁ ι₂) : Vect α (ι₂ * ι₁) :=
  Vect.flatten matrix

def Matrix.transpose : Matrix α ι₁ ι₂ → Matrix α ι₂ ι₁
  | [] => .replicate _ ([])
  | x :: xs => Vect.zipWith (.cons) x (transpose xs)

section add
variable [Add α]
def Matrix.add (m₁ : Matrix α ι₁ ι₂) (m₂ : Matrix α ι₁ ι₂) : Matrix α ι₁ ι₂ :=
  Matrix.zipWith (·+·) m₁ m₂

instance : HAdd (Matrix α ι₁ ι₂) (Matrix α ι₁ ι₂) (Matrix α ι₁ ι₂) where
  hAdd := Matrix.add
end add

section add
variable [Sub α]
def Matrix.sub (m₁ : Matrix α ι₁ ι₂) (m₂ : Matrix α ι₁ ι₂) : Matrix α ι₁ ι₂ :=
  Matrix.zipWith (·-·) m₁ m₂

instance : HSub (Matrix α ι₁ ι₂) (Matrix α ι₁ ι₂) (Matrix α ι₁ ι₂) where
  hSub := Matrix.sub
end add

section mul
variable [Mul α]

/-- Multiply matrix by scalar -/
def Matrix.muls  (s : α) : Matrix α ι₁ ι₂ → Matrix α ι₁ ι₂ :=
  Matrix.map (·*s)

instance : HMul (Matrix α ι₁ ι₂) α (Matrix α ι₁ ι₂) where
  hMul := flip Matrix.muls

variable [Inhabited α] [Add α]

/-- Multiply matrix by vector -/
def Matrix.mulv (m : Matrix α ι₁ ι₂) (v : Vect α ι₂) : Vect α ι₁ :=
  Vect.map (Vect.dot v ·) m

instance : HMul (Matrix α ι₁ ι₂) (Vect α ι₂) (Vect α ι₁) where
  hMul := Matrix.mulv

/-- Multiply matrix by matrix -/
def Matrix.mulm (m₁ : Matrix α ι₁ ι₂) (m₂ : Matrix α ι₂ ι₃) : Matrix α ι₁ ι₃ :=
  Vect.map (Matrix.mulv (Matrix.transpose m₂)) m₁

instance : HMul (Matrix α ι₁ ι₂) (Matrix α ι₂ ι₃) (Matrix α ι₁ ι₃) where
  hMul := Matrix.mulm

end mul
