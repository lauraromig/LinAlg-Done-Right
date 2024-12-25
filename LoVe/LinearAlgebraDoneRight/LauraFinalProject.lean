import LoVe.LoVelib
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Sqrt
import Mathlib.Algebra.Order.Ring.Defs


/- This final project is a formalization of part of the first chapter, "Vector Spaces" of
Linear Algebra Done Right, by Sheldon Axler and available in the Brown Library. -/

/- Therefore, this project shall be called: Linear Algebra Done More Right -/

namespace linalg

-- **Complex Numbers**

/- The chapter begins by defining Complex Numbers. For the purposes of this project,
I will be using rational numbers instead of real numbers to represent the complex coefficients.
I will also build on the complex number structure from our Complex numbers demo, as defined below:-/

structure Complex : Type where
  real : ℚ
  im   : ℚ

/- Next, we must define addition and multiplication over complex numbers.
These definitions are also from our class lecture on modelling Complex numbers in Lean. -/

def Complex.add (a b : Complex) : Complex where
  real := a.real + b.real
  im   := a.im + b.im

def Complex.mul (a b : Complex) : Complex where
  real := a.real * b.real - a.im * b.im
  im   := a.im * b.real + a.real * b.im

/- We define the Complex number 0 + 0i, and 1 + 0i, which will be used in our
proofs about properties of Complex numbers below.-/
def zero : Complex where
  real := 0
  im := 0

def one : Complex where
  real := 1
  im := 0

/- According to Axler, there are 9 properties of complex arithmetic.
Below, using our definition of Complex numbers, I will verify them. -/

-- 1) Complex addition is commutative. (α + β = β + α for all α, β ∈ ℂ)

theorem Complex.addcomm : ∀ α β : Complex, add α β = add β α :=
  by
    intro a b
    rw [Complex.add, Complex.add]
    simp
    apply And.intro
    {apply Rat.add_comm}
    {apply Rat.add_comm}
    done

-- 2) Complex multiplication is commutative. (α * β = β * α for all α, β ∈ ℂ)
theorem Complex.mulcomm : ∀ α β : Complex, mul α β = mul β α :=
  by
    intro a b
    rw [Complex.mul, Complex.mul]
    simp
    apply And.intro
    {simp [mul_comm]}
    {simp [mul_comm]
     apply Rat.add_comm}
    done

-- 3) Complex addition is associative. (α + β) + γ = α + (β + γ) for all α, β, γ ∈ ℂ
theorem Complex.addassoc : ∀ α β γ : Complex, add (add α β) γ = add α (add β γ) :=
  by
    intro a b g
    rw [Complex.add, Complex.add, Complex.add, Complex.add]
    simp
    apply And.intro
    {apply Rat.add_assoc}
    {apply Rat.add_assoc}
    done

-- 4) Complex multiplication is associative. (α * β) * γ = α * (β * γ) for all α, β, γ ∈ ℂ
theorem Complex.mulassoc : ∀ α β γ : Complex, mul (mul α β) γ = mul α (mul β γ) :=
    by
      intro a b g
      rw [Complex.mul, Complex.mul, Complex.mul, Complex.mul]
      simp
      apply And.intro
      {linarith}
      {linarith}
      done

-- 5) There is an additive identity for all γ in ℂ (which is zero)
theorem Complex.addid : ∀ γ : Complex, add γ zero = γ :=
  by
    intro g
    rw [Complex.add]
    rw [zero]
    simp
    done

-- 6) There is a multiplicative identity for all γ in ℂ (which is one)
theorem Complex.mulid : ∀ γ : Complex, mul one γ = γ :=
  by
    intro g
    rw [Complex.mul]
    rw [one]
    simp
    done

-- 7) There exists an additive inverse β for all α in ℂ, such that α + β = 0.

-- This is a helper lemma
lemma Complex.ext {α β : Complex} (hr : α.real = β.real) (hi : α.im = β.im) :
  α = β :=
  by
   cases α
   cases β
   simp_all

theorem Complex.AddInv : ∀ α : Complex, ∃! β : Complex, Complex.add α β = zero :=
  by
    intro α
    let β : Complex := ⟨-α.real, -α.im⟩
    use β
    constructor
    simp [Complex.add, zero]
    intro β' h
    cases' β' with b.r b.i
    simp [Complex.add, zero] at h
    apply Complex.ext
    cases' h with l r
    simp
    linarith
    simp
    linarith
    done

-- 8) There exists a multiplicative inverse for all α such that α ≠ 0 in ℂ, such that αβ = 1.
-- (The longest & messiest proof)

-- This is a helper lemma
lemma first_item_eq_zero (b c : ℚ) (h1 : b ≥ 0) (h2 : c ≥ 0) (h3 : b + c = 0) : b = 0 :=
  by
    have h4 : -b = c := by
      rw [@add_eq_zero_iff_neg_eq] at h3
      exact h3
    linarith
    done

theorem Complex.MultInv : ∀ α : Complex, α ≠ zero → ∃ β : Complex, Complex.mul α β = one :=
  by
    intro α hα
    let sq := α.real * α.real + α.im * α.im
    have hsq : α.real * α.real + α.im * α.im = sq := by simp
    have h_norm : sq ≠ 0 := by
      intro h
      have hb : α = zero :=
        by
          apply Complex.ext
          {
            have h1 : α.real * α.real ≥ 0 := by exact mul_self_nonneg α.real
            have h2 : α.im * α.im ≥ 0 := by exact mul_self_nonneg α.im
            have h3 : zero.real = 0 := by rfl
            rw [h3]
            have h4 : α.real * α.real = 0 := by apply first_item_eq_zero (α.real * α.real) (α.im * α.im) h1 h2 h
            simp_all only [ne_eq, zero_add, mul_eq_zero, or_self, le_refl, mul_zero]
          }
          {
            have h1 : α.real * α.real ≥ 0 := by exact mul_self_nonneg α.real
            have h2 : α.im * α.im ≥ 0 := by exact mul_self_nonneg α.im
            have h3 : zero.im = 0 := by rfl
            rw [h3]
            have h4 : α.real * α.real = 0 := by apply first_item_eq_zero (α.real * α.real) (α.im * α.im) h1 h2 h
            simp_all only [ne_eq, zero_add, mul_eq_zero, or_self, le_refl, mul_zero]
          }
          done
      exact hα hb
    let β : Complex := ⟨α.real / sq, -α.im / sq⟩
    use β
    simp [Complex.mul]
    apply Complex.ext
    {
      simp_all
      have h : one.real = 1 := by rfl
      rw [h]
      rw [mul_div]
      rw [mul_div]
      rw [div_sub_div_same]
      rw [mul_neg]
      rw [sub_neg_eq_add]
      simp_all only [ne_eq, not_false_eq_true, div_self]
    }
    {
      calc α.im * (α.real / sq) + α.real * (-α.im / sq) = 0 := by ring
    }
    done

-- 9) Complex multiplication distributes over Complex addition.

theorem Complex.Dist : ∀ γ α β : Complex, mul γ (add α β) = add (mul γ α) (mul γ β) :=
  by
    intro γ α β
    rw [Complex.add, Complex.mul]
    apply Complex.ext
    calc
      γ.real * (α.real + β.real) - γ.im * (α.im + β.im)
       = γ.real * α.real + γ.real * β.real - γ.im * α.im - γ.im * β.im := by linarith
      _ = (γ.real * α.real - γ.im * α.im) + (γ.real * β.real - γ.im * β.im) := by linarith
      _ = (Complex.real (Complex.mul γ α)) + (Complex.real (Complex.mul γ β)) := by rfl
    calc
      γ.im * (α.real + β.real) + γ.real * (α.im + β.im)
        = γ.im * α.real + γ.im * β.real + γ.real * α.im + γ.real * β.im := by linarith
        _ = (γ.im * α.real + γ.real * α.im) + (γ.im * β.real + γ.real * β.im) := by linarith
        _ = (Complex.im (Complex.mul γ α)) + (Complex.im (Complex.mul γ β)) := by rfl
    done

-- The next section will define subtraction and division over Complex numbers.

-- This is a direct statement of the additive inverse for Complex numbers
def Complex.additiveinverse (α : Complex) : Complex where
  real := - α.real
  im := - α.im

-- Subtraction over complex numbers is defined as such:
def Complex.sub (α β : Complex) : Complex :=
  add β (Complex.additiveinverse α)

-- This is a direct statement of the multiplicative inverse for Complex numbers (if α ≠ 0)
def Complex.multiplicativeinverse (α : Complex) (ha : α ≠ zero) : Complex where
  real := α.real / (α.real ^2 + α.im^2)
  im := - α.im / (α.real^2 + α.im^2)

-- Division over complex numbers is defined as such:
def Complex.div (α β : Complex) (ha : α ≠ zero) : Complex :=
  mul β (Complex.multiplicativeinverse α ha)

-- **Lists**

/- Next, the chapter gives the example of ℝ^2 and ℝ^3, the set of all ordered pairs / triples
of real numbers. -/

def Q2 : Type := ℚ × ℚ

def Q3 : Type := ℚ × ℚ × ℚ

/- The section on lists will use the Lean definition of List,
but it is restated here as for reference & clarity.-/

inductive MyList (α : Type) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α

-- "Two lists are equal if and only if they have the same length and the same elements in the same order."

def lists_equal (α : Type) : List α → List α → Prop
| [], [] => True
| a :: as, b :: bs => a = b ∧ lists_equal α as bs
| _, _ => False

/- This lemma proves that this notion of list equality fits with Lean's built in notion of list equality -/
lemma equalityoflists (α : Type) (l1 l2 : List α) : lists_equal α l1 l2 ↔ l1 = l2 :=
  by
    constructor
    intro h
    induction l1 generalizing l2
    case nil =>
        cases l2
        rfl
        contradiction
    case cons hd tl ih =>
        cases' l2 with hd2 tl2
        contradiction
        cases' h with h_hd h_tl
        rw [h_hd]
        rw [ih]
        subst h_hd
        simp_all only
    intro h
    rw [h]
    clear h
    induction' l2 with head tail ih
    exact trivial
    constructor
    rfl
    apply ih
    done

-- **Fn**
/- Fn is the set of all lists of length n with elements of Type F, where F (in the textbook)
is a field, but for these purposes will be ℂ -/

def Fn (n : ℕ) (F : Type) : Type := {l : List F // l.length = n}

/- Fn takes any type F for the elements of the lists, but in the textbook context they
will be Complex or Real numbers (and in this case, complex, since every real number
can be represented as a complex number). -/

-- For (x1, ..., xn) ∈ Fn and j ∈ {1, ..., n}, we say that xj is the jth coordinate of (x1, ..., xn).

def coordinate {F : Type} (inp : List F) (j : ℕ) : Option F :=
  match inp with
    | [] => none
    | hd :: tl =>
      if j = 1 then hd
      else
        coordinate tl (j-1)

-- A List F is a member of the Field Fn if it has n elements

def IsMemberFn (n : ℕ) {F : Type} (as : List F) : Prop :=
  as.length = n

/- Next, we define  addition within Fn (ie, elementwise addition of equal-length lists).
This is done using the function meld from the homework, except simplifying so that
melding occurs between two lists with the same Type.-/

def meld {α γ : Type} : (α → α → γ) → List α → List α → List γ
 | f, [], [] => []
 | f, [], x :: xs => []
 | f, x :: xs, [] => []
 | f, x :: xs, y :: ys => [f x y] ++ meld f xs ys

-- "Addition in Fn is defined by adding corresponding coordinates"
def Fn.add (as bs : List Complex) : List Complex :=
   meld Complex.add as bs

/- This helper will prove that melding with the addition operator is commutative,
which will help us prove that addition over Fn is commutative -/
lemma meldaddcomm  (as : List Complex) (bs : List Complex) :
  meld Complex.add as bs = meld Complex.add bs as :=
  by
    induction' as with hd tl ih generalizing bs
    case nil =>
      cases' bs with hd2 tl2
      simp
      rfl
    case cons =>
      cases' bs with hd2 tl2
      case nil => rfl
      case cons =>
        simp [meld]
        constructor
        (apply Complex.addcomm hd hd2)
        (apply ih)

-- Next, the chapter proves that addition within Fn is commutative:
lemma Fn.addcomm (x y : List Complex) : Fn.add x y = Fn.add y x :=
  by apply meldaddcomm

-- We define the List Complex of length n, whose coordinates are all (complex) 0.
def zerolist : ℕ → List Complex
  | 0 => []
  | n + 1 => [zero] ++ zerolist n

/- For x ∈ Fn, the additive inverse of x, denoted -x, is the vector -x ∈ Fn
such that x + (-x) = 0. In other words, if x = (x1, ..., xn), then -x = (-x1, ..., -xn) -/
def Fnaddinv (n : ℕ): List Complex → List Complex
  | [] => zerolist n
  | x :: xs => (Complex.additiveinverse x) :: Fnaddinv n xs

/- The product of a number γ and a vector in Fn is computed by multiplying
each coordinate of the vector by γ: -/
def Fnscalarmul  (γ : Complex) : List Complex → List Complex
  | [] => []
  | hd :: tl => [Complex.mul γ hd] ++ Fnscalarmul γ tl

-- We may now generalize to a vector space.

-- **Vector Spaces**
/-"The motivation for the definition of a vector space comes from properties of addition and scalar multiplication in Fn:
Addition is commutative, associative, and has an identity. Every element has an additive inverse.
Scalar multiplica- tion is associative. Scalar multiplication by 1 acts as expected.
Addition and scalar multiplication are connected by distributive properties."
-/

-- So, we define a class called vectorspace encompassing the properties of a vector space.
class vectorspace (F : Type) (V : Type) where
  add : V → V → V
  scalmul : Complex → V → V
  addcomm : ∀ (v w : V), add v w = add w v
  addassoc : ∀ (v w z : V), add (add v w) z = add v (add w z)
  mulassoc : ∀ (a b : Complex) (v : V), scalmul (Complex.mul a b) v = scalmul a (scalmul b v)
  addid : ∃ vszero : V, ∀ v : V, add v vszero = v ∧ ∀ v : V, ∃ w : V, add w v = vszero
  mulid : ∀ (v : V), scalmul one v = v
  dist1 : ∀ (a : Complex) (u v : V), scalmul a (add u v) = add (scalmul a u) (scalmul a v)
  dist2 : ∀ (a b: Complex) (v : V), scalmul (Complex.add a b) v = add (scalmul a v) (scalmul b v)

/- We can now outline a vector space over Complex numbers, just using the properties of
complex arithmetic we proved! -/

instance : vectorspace Complex (Complex) where
  add := Complex.add
  scalmul := Complex.mul
  addcomm := Complex.addcomm
  addassoc := Complex.addassoc
  mulassoc := Complex.mulassoc
  addid := sorry -- I will omit this proof because the book gives a slightly different definition for the complex additive inverse, including that it is unique.
  mulid := Complex.mulid
  dist1 := Complex.Dist
  dist2 := sorry
  /- I will also omit the last property because it is not one of the properties
  given for complex arithmetic in the textbook,
  though it can be proven since ℂ is a vector space. -/

/- Finally, I will briefly explain how you might
extend a vector space over Complex vectors of length 2.
To do this, I will define specific addition and scalar multiplication functions over
the ℂ2 vectors. (This will allow us to only work with vectors/lists that are of
equal length, which is not necessarily the case with the addition built on 'meld'.)-/

-- Members of F2 Complex:
def Complex2 : Type := { v : List Complex // IsMemberFn 2 v }

-- An addition function for Members of F2 Complex
def Fn.add2 : Complex2 → Complex2 → Complex2
  | ⟨[hd1, hd2], _⟩ , ⟨[hd3, hd4], _⟩ =>
      ⟨[Complex.add hd1 hd3, Complex.add hd2 hd4], by rfl⟩

-- A scalar multiplication function for Members of F2 Complex
def Fn.scalarmul2 : Complex → Complex2 → Complex2
  | ⟨a, b⟩, ⟨[⟨c, d⟩, ⟨e, f⟩], _⟩ =>
      ⟨[⟨a * c - b * d, b * c + a * d⟩,
        ⟨a * e - b * f, b * e + a * f⟩],
       by rfl⟩

/- Using these as the scalar multiplication and addition functions,
we could outline a vector space for ℂ2. -/

/- Now, using Lean, you can see how vector spaces can be built up from fundamental mathematical tools!
 This completes my final project. Thank you so much for a great semester! -/
end linalg
