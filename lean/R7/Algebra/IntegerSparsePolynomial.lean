import R7.Algebra.IntegerExpression
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace R7.Algebra.IntegerSparse

structure Term where
  key : ℕ
  value : ℤ
  deriving DecidableEq
abbrev KeyPoly := List Term

noncomputable def interpretKey : KeyPoly → Polynomial ℤ
 | [] => 0
 | a::ps => Polynomial.monomial a.key a.value+interpretKey ps

def collectKey (a : Term) (p : KeyPoly) : KeyPoly :=
  List.rec (motive := fun _ => Term → KeyPoly)
    (fun a => if a.value=0 then [] else [a])
    (fun b _ rec a => if a.key=b.key then
      rec ⟨a.key,a.value+b.value⟩
      else if a.value=0 then rec b else a::rec b) p a

def mergeKey (n : ℕ) (p q : KeyPoly) : KeyPoly :=
  Nat.rec (motive := fun _ => KeyPoly → KeyPoly → KeyPoly)
    (fun p q => p++q)
    (fun _ rec p q => match p,q with
      | [],q => q
      | p,[] => p
      | a::p,b::q => if a.key ≤ b.key then a::rec p (b::q)
          else b::rec (a::p) q) n p q

def sortKey (n : ℕ) (p : KeyPoly) : KeyPoly :=
  Nat.rec (motive := fun _ => KeyPoly → KeyPoly) (fun p => p)
    (fun _ rec p => match p with
      | [] => []
      | [a] => [a]
      | p => mergeKey p.length (rec (p.take (p.length/2)))
          (rec (p.drop (p.length/2)))) n p

def normalizeKey (p : KeyPoly) : KeyPoly :=
 match sortKey 32 p with
 | [] => []
 | a::ps => collectKey a ps

theorem collectKey_nil (a : Term) : collectKey a [] =
    (if a.value=0 then [] else [a]) := rfl

theorem collectKey_cons (a b : Term) (p : KeyPoly) : collectKey a (b::p) =
    (if a.key=b.key then collectKey ⟨a.key,a.value+b.value⟩ p
    else if a.value=0 then collectKey b p else a::collectKey b p) := rfl

theorem mergeKey_zero (p q : KeyPoly) : mergeKey 0 p q=p++q := rfl

theorem mergeKey_succ (n : ℕ) (p q : KeyPoly) : mergeKey (n+1) p q=
    (match p,q with
    | [],q => q
    | p,[] => p
    | a::p,b::q => if a.key ≤ b.key then a::mergeKey n p (b::q)
        else b::mergeKey n (a::p) q) := rfl

theorem sortKey_succ (n : ℕ) (p : KeyPoly) : sortKey (n+1) p=
    (match p with
    | [] => []
    | [a] => [a]
    | p => mergeKey p.length (sortKey n (p.take (p.length/2)))
        (sortKey n (p.drop (p.length/2)))) := rfl

theorem interpret_collectKey (a : Term) (p : KeyPoly) :
    interpretKey (collectKey a p) = Polynomial.monomial a.key a.value+interpretKey p := by
  induction p generalizing a with
  | nil => by_cases ha : a.value=0 <;> simp [collectKey_nil,interpretKey,ha]
  | cons b ps ih =>
    by_cases hab : a.key=b.key
    · simp only [collectKey_cons,hab,ite_true,ih,interpretKey]
      rw [map_add]
      abel
    · by_cases ha : a.value=0
      · simp [collectKey_cons,hab,ha,ih,interpretKey]
      · simp only [collectKey_cons,hab,ha,ite_false,interpretKey,ih]

@[simp] theorem interpretKey_append (p q : KeyPoly) : interpretKey (p++q)=interpretKey p+interpretKey q := by
  induction p with
  | nil => simp [interpretKey]
  | cons a p ih => simp only [List.cons_append,interpretKey,ih]; abel

theorem interpret_mergeKey (n : ℕ) (p q : KeyPoly) :
    interpretKey (mergeKey n p q)=interpretKey p+interpretKey q := by
  induction n generalizing p q with
  | zero => simp [mergeKey_zero]
  | succ n ih => cases p with
    | nil => simp [mergeKey_succ,interpretKey]
    | cons a p => cases q with
      | nil => simp [mergeKey_succ,interpretKey]
      | cons b q =>
        by_cases h : a.key ≤ b.key
        · simp only [mergeKey_succ,h,ite_true,interpretKey,ih]; abel
        · simp only [mergeKey_succ,h,ite_false,interpretKey,ih]; abel

theorem interpret_sortKey (n : ℕ) (p : KeyPoly) : interpretKey (sortKey n p)=interpretKey p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => cases p with
    | nil => rfl
    | cons a p => cases p with
      | nil => rfl
      | cons b p =>
        simp only [sortKey_succ,interpret_mergeKey,ih]
        rw [← interpretKey_append,List.take_append_drop]

@[simp] theorem interpret_normalizeKey (p : KeyPoly) : interpretKey (normalizeKey p)=interpretKey p := by
  have hh := interpret_sortKey 32 p
  cases he : sortKey 32 p with
  | nil => simpa [normalizeKey,he] using hh
  | cons a ps => simpa only [normalizeKey,he,interpret_collectKey,interpretKey] using hh

/-- Combine adjacent equal terms. Inputs produced by the checker are sorted. -/
def compressKey (p : KeyPoly) : KeyPoly :=
  match p with
  | [] => []
  | a :: ps => collectKey a ps

@[simp] theorem interpret_compressKey (p : KeyPoly) :
    interpretKey (compressKey p) = interpretKey p := by
  cases p <;> simp [compressKey, interpretKey, interpret_collectKey]

/-- Merge already sorted sparse polynomials without sorting their concatenation. -/
def addKey (p q : KeyPoly) := compressKey (mergeKey (p.length + q.length) p q)
def negKey (p : KeyPoly) := p.map (fun a => {a with value := -a.value})
def mulTerm (a b : Term) : Term := ⟨a.key+b.key,a.value*b.value⟩
/-- Balanced multiplication combines equal terms before forming the next level.
The fallback makes the operation total independently of any size bound. -/
def mulKeyAux (fuel : ℕ) (p q : KeyPoly) : KeyPoly :=
  Nat.rec (motive := fun _ => KeyPoly → KeyPoly → KeyPoly)
    (fun p q => normalizeKey (p.flatMap (fun a => q.map (mulTerm a))))
    (fun _ rec p q => match p with
      | [] => []
      | [a] => compressKey (q.map (mulTerm a))
      | p => addKey (rec (p.take (p.length / 2)) q)
          (rec (p.drop (p.length / 2)) q)) fuel p q

def mulKey (p q : KeyPoly) := mulKeyAux 32 p q
def constantKey (a : ℤ) : KeyPoly := if a=0 then [] else [⟨0,a⟩]
def powerKey (p : KeyPoly) (n : ℕ) : KeyPoly :=
  Nat.rec (constantKey 1) (fun _ prev => mulKey prev p) n

theorem powerKey_zero (p : KeyPoly) : powerKey p 0=constantKey 1 := rfl

theorem powerKey_succ (p : KeyPoly) (n : ℕ) :
    powerKey p (n+1)=mulKey (powerKey p n) p := rfl

@[simp] theorem interpretKey_add (p q : KeyPoly) : interpretKey (addKey p q)=interpretKey p+interpretKey q := by simp [addKey, interpret_mergeKey]
@[simp] theorem interpretKey_neg (p : KeyPoly) : interpretKey (negKey p)= -interpretKey p := by
  induction p with
  | nil => simp [negKey,interpretKey]
  | cons a p ih => simp only [negKey,List.map_cons,interpretKey,map_neg,neg_add_rev] at *; rw [ih]; abel
@[simp] theorem interpretKey_mulTerm (a : Term) (q : KeyPoly) :
    interpretKey (q.map (mulTerm a)) = Polynomial.monomial a.key a.value*interpretKey q := by
  induction q with
  | nil => simp [interpretKey]
  | cons b q ih =>
    simp only [List.map_cons,interpretKey,mulTerm,← Polynomial.monomial_mul_monomial,mul_add]
    exact congrArg (fun z => Polynomial.monomial a.key a.value *
      Polynomial.monomial b.key b.value+z) ih
theorem interpretKey_flatMap_mulTerm (p q : KeyPoly) :
    interpretKey (p.flatMap (fun a => q.map (mulTerm a))) =
      interpretKey p * interpretKey q := by
  induction p with
  | nil => simp [interpretKey]
  | cons a p ih =>
    simp only [List.flatMap_cons, interpretKey_append, interpretKey_mulTerm, ih, interpretKey]
    ring

theorem interpretKey_mulKeyAux (fuel : ℕ) (p q : KeyPoly) :
    interpretKey (mulKeyAux fuel p q) = interpretKey p * interpretKey q := by
  induction fuel generalizing p q with
  | zero => simp [mulKeyAux, interpretKey_flatMap_mulTerm]
  | succ fuel ih =>
    cases p with
    | nil => simp [mulKeyAux, interpretKey]
    | cons a ps =>
      cases ps with
      | nil => simp [mulKeyAux, interpretKey]
      | cons b ps =>
        change interpretKey (addKey
          (mulKeyAux fuel ((a :: b :: ps).take ((a :: b :: ps).length / 2)) q)
          (mulKeyAux fuel ((a :: b :: ps).drop ((a :: b :: ps).length / 2)) q)) = _
        rw [interpretKey_add, ih, ih, ← add_mul, ← interpretKey_append,
          List.take_append_drop]

@[simp] theorem interpretKey_mul (p q : KeyPoly) : interpretKey (mulKey p q)=interpretKey p*interpretKey q := by
  exact interpretKey_mulKeyAux 32 p q
@[simp] theorem interpretKey_constant (a : ℤ) : interpretKey (constantKey a)=Polynomial.C a := by
  by_cases ha : a=0 <;> simp [constantKey,interpretKey,ha]
@[simp] theorem interpretKey_power (p : KeyPoly) (n : ℕ) : interpretKey (powerKey p n)=interpretKey p^n := by
  induction n with
  | zero => simp [powerKey_zero,interpretKey_constant]
  | succ n ih => simp only [powerKey_succ,interpretKey_mul,ih,pow_succ]

/-- Scalar multiplication does not introduce coefficient gcd computations. -/
def scaleKey (c : ℤ) (p : KeyPoly) : KeyPoly :=
  p.map (fun a => ⟨a.key, c * a.value⟩)

@[simp] theorem interpretKey_scale (c : ℤ) (p : KeyPoly) :
    interpretKey (scaleKey c p) = Polynomial.C c * interpretKey p := by
  induction p with
  | nil => simp [scaleKey, interpretKey]
  | cons a ps ih =>
    change Polynomial.monomial a.key (c * a.value) +
      interpretKey (scaleKey c ps) = _
    rw [← Polynomial.C_mul_monomial, ih, interpretKey, mul_add]

def termEqual (a b : Term) : Bool := (a.key == b.key) && (a.value == b.value)

theorem termEqual_sound (a b : Term) (h : termEqual a b = true) : a = b := by
  have hs := Bool.and_eq_true_iff.mp h
  have hk : a.key = b.key := by simpa using hs.1
  have hv : a.value = b.value := by simpa using hs.2
  cases a; cases b
  simp_all

def keyPolyEqual : KeyPoly → KeyPoly → Bool
  | [], [] => true
  | a :: ps, b :: qs => termEqual a b && keyPolyEqual ps qs
  | _, _ => false

theorem keyPolyEqual_sound (p q : KeyPoly) (h : keyPolyEqual p q = true) : p = q := by
  induction p generalizing q with
  | nil => cases q <;> simp_all [keyPolyEqual]
  | cons a ps ih =>
    cases q with
    | nil => simp [keyPolyEqual] at h
    | cons b qs =>
      have hs := Bool.and_eq_true_iff.mp h
      rw [termEqual_sound a b hs.1, ih qs hs.2]

end R7.Algebra.IntegerSparse
