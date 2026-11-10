import R7.Spectral.Polynomial
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

namespace R7.Core.SpectralCoefficient
open R7.ComputablePolynomial

def expCode (e : Exp) : ℕ := e 0+32*(e 1+32*(e 2+32*(e 3+32*e 4)))

structure Term where
  key : ℕ
  exp : Exp
  value : ℚ
  deriving DecidableEq
abbrev KeyPoly := List Term

noncomputable def interpretKey : KeyPoly → PolynomialChart.Poly
 | [] => 0
 | a::ps => MvPolynomial.monomial (exponent a.exp) a.value+interpretKey ps

/-- Compare the five exponent coordinates. -/
def expEqual (a b : Exp) : Bool :=
  (a 0 == b 0) && (a 1 == b 1) && (a 2 == b 2) &&
    (a 3 == b 3) && (a 4 == b 4)

@[simp] theorem expEqual_eq_true (a b : Exp) : expEqual a b = true ↔ a = b := by
  simp only [expEqual, Bool.and_eq_true_iff, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩
    funext i
    fin_cases i <;> assumption
  · intro h
    subst b
    exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

def collectKey (a : Term) (p : KeyPoly) : KeyPoly :=
  List.rec (motive := fun _ => Term → KeyPoly)
    (fun a => bif a.value == 0 then [] else [a])
    (fun b _ rec a => bif ((a.key == b.key) && expEqual a.exp b.exp) then
      rec ⟨a.key,a.exp,a.value+b.value⟩
      else bif a.value == 0 then rec b else a::rec b) p a

def mergeKey (n : ℕ) (p q : KeyPoly) : KeyPoly :=
  Nat.rec (motive := fun _ => KeyPoly → KeyPoly → KeyPoly)
    (fun p q => p++q)
    (fun _ rec p q => match p,q with
      | [],q => q
      | p,[] => p
      | a::p,b::q => bif Nat.ble a.key b.key then a::rec p (b::q)
          else b::rec (a::p) q) n p q

def sortKey (n : ℕ) (p : KeyPoly) : KeyPoly :=
  Nat.rec (motive := fun _ => KeyPoly → KeyPoly) (fun p => p)
    (fun _ rec p => match p with
      | [] => []
      | [a] => [a]
      | p => mergeKey p.length (rec (p.take (p.length/2)))
          (rec (p.drop (p.length/2)))) n p

/-- Rows for a bottom-up merge sort. Every fuel fallback retains all terms. -/
noncomputable def interpretSortKeyRows : List KeyPoly → PolynomialChart.Poly
  | [] => 0
  | p :: ps => interpretKey p + interpretSortKeyRows ps

def mergeKeyLocal (p q : KeyPoly) : KeyPoly :=
  List.rec (motive := fun _ => KeyPoly → KeyPoly)
    (fun q => q)
    (fun a p rec q =>
      List.rec (motive := fun _ => KeyPoly)
        (a :: p)
        (fun b q recq =>
          bif Nat.ble a.key b.key then a :: rec (b :: q)
          else b :: recq) q) p q

def sortPairKeyRows : List KeyPoly → List KeyPoly
  | [] => []
  | [p] => [p]
  | p :: q :: ps => mergeKeyLocal p q :: sortPairKeyRows ps

def sortMergeKeyRows (fuel : ℕ) (ps : List KeyPoly) : KeyPoly :=
  Nat.rec (motive := fun _ => List KeyPoly → KeyPoly)
    (fun ps => ps.flatten)
    (fun _ rec ps => match ps with
      | [] => []
      | [p] => p
      | ps => rec (sortPairKeyRows ps)) fuel ps

def sortBottomKey (p : KeyPoly) : KeyPoly :=
  sortMergeKeyRows 32 (p.map (fun a => [a]))

def normalizeKey (p : KeyPoly) : KeyPoly :=
 match sortBottomKey p with
 | [] => []
 | a::ps => collectKey a ps

theorem collectKey_nil (a : Term) : collectKey a [] =
    (if a.value=0 then [] else [a]) := by
  change (bif a.value == 0 then [] else [a]) = _
  simp only [cond_eq_ite, beq_iff_eq]

theorem collectKey_cons (a b : Term) (p : KeyPoly) : collectKey a (b::p) =
    (if a.key=b.key ∧ a.exp=b.exp then collectKey ⟨a.key,a.exp,a.value+b.value⟩ p
    else if a.value=0 then collectKey b p else a::collectKey b p) := by
  change (bif ((a.key == b.key) && expEqual a.exp b.exp) then
    collectKey ⟨a.key,a.exp,a.value+b.value⟩ p
    else bif a.value == 0 then collectKey b p else a::collectKey b p) = _
  simp only [cond_eq_ite, Bool.and_eq_true_iff, beq_iff_eq, expEqual_eq_true]

theorem mergeKey_zero (p q : KeyPoly) : mergeKey 0 p q=p++q := rfl

theorem mergeKey_succ (n : ℕ) (p q : KeyPoly) : mergeKey (n+1) p q=
    (match p,q with
    | [],q => q
    | p,[] => p
    | a::p,b::q => if a.key ≤ b.key then a::mergeKey n p (b::q)
        else b::mergeKey n (a::p) q) := by
  change (match p,q with
    | [],q => q
    | p,[] => p
    | a::p,b::q => bif Nat.ble a.key b.key then a::mergeKey n p (b::q)
        else b::mergeKey n (a::p) q) = _
  cases p <;> cases q <;> simp only [cond_eq_ite, Nat.ble_eq]

theorem sortKey_succ (n : ℕ) (p : KeyPoly) : sortKey (n+1) p=
    (match p with
    | [] => []
    | [a] => [a]
    | p => mergeKey p.length (sortKey n (p.take (p.length/2)))
        (sortKey n (p.drop (p.length/2)))) := rfl

theorem interpret_collectKey (a : Term) (p : KeyPoly) :
    interpretKey (collectKey a p) = MvPolynomial.monomial (exponent a.exp) a.value+interpretKey p := by
  induction p generalizing a with
  | nil => by_cases ha : a.value=0 <;> simp [collectKey_nil,interpretKey,ha]
  | cons b ps ih =>
    by_cases hab : a.key=b.key ∧ a.exp=b.exp
    · simp only [collectKey_cons,hab,and_self,ite_true,ih,interpretKey]
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

theorem interpretSortKeyRows_flatten (ps : List KeyPoly) :
    interpretKey ps.flatten = interpretSortKeyRows ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.flatten_cons, interpretKey_append, ih, interpretSortKeyRows]

theorem mergeKeyLocal_nil (q : KeyPoly) : mergeKeyLocal [] q = q := rfl

theorem mergeKeyLocal_cons (a b : Term) (p q : KeyPoly) :
    mergeKeyLocal (a :: p) (b :: q) =
      (bif Nat.ble a.key b.key then a :: mergeKeyLocal p (b :: q)
      else b :: mergeKeyLocal (a :: p) q) := rfl

theorem mergeKeyLocal_perm (p q : KeyPoly) :
    List.Perm (mergeKeyLocal p q) (p ++ q) := by
  induction p generalizing q with
  | nil => simp [mergeKeyLocal]
  | cons a p ih =>
    induction q with
    | nil => simp [mergeKeyLocal]
    | cons b q ihq =>
      rw [mergeKeyLocal_cons]
      simp only [cond_eq_ite]
      split
      · exact (ih (b :: q)).cons a
      · exact (ihq.cons b).trans List.perm_middle.symm

theorem interpretKey_perm {p q : KeyPoly} (h : List.Perm p q) :
    interpretKey p = interpretKey q := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [interpretKey, ih]
  | swap a b p => simp only [interpretKey]; abel
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem interpret_mergeKeyLocal (p q : KeyPoly) :
    interpretKey (mergeKeyLocal p q) = interpretKey p + interpretKey q :=
  (interpretKey_perm (mergeKeyLocal_perm p q)).trans (interpretKey_append p q)

theorem interpret_sortPairKeyRows (ps : List KeyPoly) :
    interpretSortKeyRows (sortPairKeyRows ps) = interpretSortKeyRows ps := by
  induction ps using sortPairKeyRows.induct with
  | case1 => rfl
  | case2 p => rfl
  | case3 p q ps ih =>
    simp only [sortPairKeyRows, interpretSortKeyRows, interpret_mergeKeyLocal, ih]
    abel

theorem interpret_sortMergeKeyRows (fuel : ℕ) (ps : List KeyPoly) :
    interpretKey (sortMergeKeyRows fuel ps) = interpretSortKeyRows ps := by
  induction fuel generalizing ps with
  | zero => exact interpretSortKeyRows_flatten ps
  | succ fuel ih =>
    cases ps with
    | nil => rfl
    | cons p ps =>
      cases ps with
      | nil => simp [sortMergeKeyRows, interpretSortKeyRows]
      | cons q ps =>
        change interpretKey (sortMergeKeyRows fuel (sortPairKeyRows (p :: q :: ps))) = _
        rw [ih, interpret_sortPairKeyRows]

theorem interpret_sortSingletonKeyRows (p : KeyPoly) :
    interpretSortKeyRows (p.map (fun a => [a])) = interpretKey p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.map_cons, interpretSortKeyRows, interpretKey, add_zero, ih]

theorem interpret_sortBottomKey (p : KeyPoly) :
    interpretKey (sortBottomKey p) = interpretKey p := by
  simp only [sortBottomKey, interpret_sortMergeKeyRows, interpret_sortSingletonKeyRows]

@[simp] theorem interpret_normalizeKey (p : KeyPoly) : interpretKey (normalizeKey p)=interpretKey p := by
  have hh := interpret_sortBottomKey p
  cases he : sortBottomKey p with
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

/-- Merge canonical sparse lists and combine equal terms in one pass.
The fallback preserves interpretation for every input and every fuel. -/
def mergeAddKey (fuel : ℕ) (p q : KeyPoly) : KeyPoly :=
  Nat.rec (motive := fun _ => KeyPoly → KeyPoly → KeyPoly)
    (fun p q => compressKey (p ++ q))
    (fun _ rec p q => match p, q with
      | [], q => q
      | p, [] => p
      | a :: p, b :: q =>
        bif (a.key == b.key) && expEqual a.exp b.exp then
          bif a.value + b.value == 0 then rec p q
          else ⟨a.key, a.exp, a.value + b.value⟩ :: rec p q
        else bif Nat.ble a.key b.key then a :: rec p (b :: q)
        else b :: rec (a :: p) q) fuel p q

theorem mergeAddKey_succ (n : ℕ) (p q : KeyPoly) : mergeAddKey (n+1) p q =
    (match p, q with
      | [], q => q
      | p, [] => p
      | a :: p, b :: q =>
        bif (a.key == b.key) && expEqual a.exp b.exp then
          bif a.value + b.value == 0 then mergeAddKey n p q
          else ⟨a.key, a.exp, a.value + b.value⟩ :: mergeAddKey n p q
        else bif Nat.ble a.key b.key then a :: mergeAddKey n p (b :: q)
        else b :: mergeAddKey n (a :: p) q) := rfl

@[simp] theorem interpret_mergeAddKey (n : ℕ) (p q : KeyPoly) :
    interpretKey (mergeAddKey n p q) = interpretKey p + interpretKey q := by
  induction n generalizing p q with
  | zero => simp [mergeAddKey]
  | succ n ih =>
    cases p with
    | nil => simp [mergeAddKey_succ, interpretKey]
    | cons a p =>
      cases q with
      | nil => simp [mergeAddKey_succ, interpretKey]
      | cons b q =>
        simp only [mergeAddKey_succ, cond_eq_ite, Bool.and_eq_true_iff,
          beq_iff_eq, Nat.ble_eq]
        by_cases hab : a.key = b.key ∧ expEqual a.exp b.exp = true
        · have hexp : a.exp = b.exp := (expEqual_eq_true _ _).mp hab.2
          by_cases hv : a.value + b.value = 0
          · simp only [hab, and_self, ite_true, hv, ih, interpretKey]
            have hmon : MvPolynomial.monomial (exponent a.exp) a.value +
                MvPolynomial.monomial (exponent b.exp) b.value = 0 := by
              rw [← hexp, ← map_add, hv, map_zero]
            linear_combination -hmon
          · simp only [hab, and_self, ite_true, hv, ite_false, ih, interpretKey]
            rw [map_add, hexp]
            abel
        · by_cases hk : a.key ≤ b.key
          · simp only [hab, ite_false, hk, ite_true, ih, interpretKey]
            abel
          · simp only [hab, ite_false, hk, ih, interpretKey]
            abel

/-- Merge already sorted sparse polynomials without sorting their concatenation. -/
def addKey (p q : KeyPoly) := mergeAddKey 65536 p q
def negKey (p : KeyPoly) := p.map (fun a => {a with value := -a.value})
def mulTerm (a b : Term) : Term := ⟨a.key+b.key,a.exp+b.exp,a.value*b.value⟩
/-- Balanced multiplication combines equal terms before forming the next level.
The fallback makes the operation total independently of any size bound. -/
def mulKeyAux (fuel : ℕ) (p q : KeyPoly) : KeyPoly :=
  Nat.rec (motive := fun _ => KeyPoly → KeyPoly → KeyPoly)
    (fun p q => normalizeKey (p.flatMap (fun a => q.map (mulTerm a))))
    (fun _ rec p q => match p with
      | [] => []
      | [a] => q.map (mulTerm a)
      | p => addKey (rec (p.take (p.length / 2)) q)
          (rec (p.drop (p.length / 2)) q)) fuel p q

def mulKey (p q : KeyPoly) :=
  if p.length ≤ q.length then mulKeyAux 32 p q else mulKeyAux 32 q p
def constantKey (a : ℚ) : KeyPoly := if a=0 then [] else [⟨0,0,a⟩]
def varKey (i : Fin 5) : KeyPoly := [⟨32^i.val,(fun j => if j=i then 1 else 0),1⟩]
def powerKey (p : KeyPoly) (n : ℕ) : KeyPoly :=
  Nat.rec (constantKey 1) (fun _ prev => mulKey prev p) n

theorem powerKey_zero (p : KeyPoly) : powerKey p 0=constantKey 1 := rfl

theorem powerKey_succ (p : KeyPoly) (n : ℕ) :
    powerKey p (n+1)=mulKey (powerKey p n) p := rfl

@[simp] theorem interpretKey_add (p q : KeyPoly) : interpretKey (addKey p q)=interpretKey p+interpretKey q := by
  exact interpret_mergeAddKey 65536 p q
@[simp] theorem interpretKey_neg (p : KeyPoly) : interpretKey (negKey p)= -interpretKey p := by
  induction p with
  | nil => simp [negKey,interpretKey]
  | cons a p ih => simp only [negKey,List.map_cons,interpretKey,map_neg,neg_add_rev] at *; rw [ih]; abel
@[simp] theorem interpretKey_mulTerm (a : Term) (q : KeyPoly) :
    interpretKey (q.map (mulTerm a)) = MvPolynomial.monomial (exponent a.exp) a.value*interpretKey q := by
  induction q with
  | nil => simp [interpretKey]
  | cons b q ih =>
    simp only [List.map_cons,interpretKey,mulTerm,exponent_add,← MvPolynomial.monomial_mul,mul_add]
    exact congrArg (fun z => MvPolynomial.monomial (exponent a.exp) a.value *
      MvPolynomial.monomial (exponent b.exp) b.value+z) ih
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
  unfold mulKey
  split <;> simp only [interpretKey_mulKeyAux, mul_comm]
@[simp] theorem interpretKey_constant (a : ℚ) : interpretKey (constantKey a)=MvPolynomial.C a := by
  by_cases ha : a=0 <;> simp [constantKey,interpretKey,ha]
@[simp] theorem interpretKey_var (i : Fin 5) : interpretKey (varKey i)=MvPolynomial.X i := by
  have hh := interpret_variable i
  simpa [varKey,indeterminate,interpretKey,interpret] using hh
@[simp] theorem interpretKey_power (p : KeyPoly) (n : ℕ) : interpretKey (powerKey p n)=interpretKey p^n := by
  induction n with
  | zero => simp only [powerKey_zero,interpretKey_constant,pow_zero,map_one]
  | succ n ih => simp only [powerKey_succ,interpretKey_mul,ih,pow_succ]

/-- Interpretation of rows used by the symmetric square checker. -/
noncomputable def interpretKeyRows : List KeyPoly → PolynomialChart.Poly
  | [] => 0
  | p :: ps => interpretKey p + interpretKeyRows ps

def pairKeyRows : List KeyPoly → List KeyPoly
  | [] => []
  | [p] => [p]
  | p :: q :: ps => addKey p q :: pairKeyRows ps

@[simp] theorem interpret_pairKeyRows (ps : List KeyPoly) :
    interpretKeyRows (pairKeyRows ps) = interpretKeyRows ps := by
  induction ps using pairKeyRows.induct with
  | case1 => rfl
  | case2 p => rfl
  | case3 p q ps ih =>
    simp only [pairKeyRows, interpretKeyRows, interpretKey_add, ih]
    abel

@[simp] theorem interpret_foldKeyRows (ps : List KeyPoly) :
    interpretKey (ps.foldr addKey []) = interpretKeyRows ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.foldr_cons, interpretKey_add, ih, interpretKeyRows]

/-- Sum rows by balanced merges. The fallback is sound for arbitrary fuel. -/
def sumKeyRows (fuel : ℕ) (ps : List KeyPoly) : KeyPoly :=
  Nat.rec (motive := fun _ => List KeyPoly → KeyPoly)
    (fun ps => ps.foldr addKey [])
    (fun _ rec ps => match ps with
      | [] => []
      | [p] => p
      | ps => rec (pairKeyRows ps)) fuel ps

@[simp] theorem interpret_sumKeyRows (fuel : ℕ) (ps : List KeyPoly) :
    interpretKey (sumKeyRows fuel ps) = interpretKeyRows ps := by
  induction fuel generalizing ps with
  | zero => exact interpret_foldKeyRows ps
  | succ fuel ih =>
    cases ps with
    | nil => rfl
    | cons p ps =>
      cases ps with
      | nil => simp [sumKeyRows, interpretKeyRows]
      | cons q ps =>
        change interpretKey (sumKeyRows fuel (pairKeyRows (p :: q :: ps))) = _
        rw [ih, interpret_pairKeyRows]

/-- Off-diagonal products occur twice in a square. -/
def doubleKeyMulTerm (a b : Term) : Term :=
  ⟨a.key + b.key, a.exp + b.exp, 2 * (a.value * b.value)⟩

@[simp] theorem interpretKey_doubleMulRow (a : Term) (q : KeyPoly) :
    interpretKey (q.map (doubleKeyMulTerm a)) =
      MvPolynomial.monomial (exponent a.exp) a.value * interpretKey q +
      MvPolynomial.monomial (exponent a.exp) a.value * interpretKey q := by
  induction q with
  | nil => simp [interpretKey]
  | cons b q ih =>
    simp only [List.map_cons, interpretKey, doubleKeyMulTerm, exponent_add,
      two_mul, map_add, ← MvPolynomial.monomial_mul, ih]
    ring

/-- Enumerate only the diagonal and upper triangle. -/
def squareKeyRows : KeyPoly → List KeyPoly
  | [] => []
  | a :: ps => (mulTerm a a :: ps.map (doubleKeyMulTerm a)) :: squareKeyRows ps

@[simp] theorem interpret_squareKeyRows (p : KeyPoly) :
    interpretKeyRows (squareKeyRows p) = interpretKey p ^ 2 := by
  induction p with
  | nil => simp [squareKeyRows, interpretKeyRows, interpretKey]
  | cons a p ih =>
    simp only [squareKeyRows, interpretKeyRows, interpretKey, mulTerm, exponent_add,
      ← MvPolynomial.monomial_mul, interpretKey_doubleMulRow, ih]
    ring

def squareKey (p : KeyPoly) : KeyPoly := sumKeyRows 32 (squareKeyRows p)

@[simp] theorem interpretKey_square (p : KeyPoly) :
    interpretKey (squareKey p) = interpretKey p ^ 2 := by
  simp only [squareKey, interpret_sumKeyRows, interpret_squareKeyRows]

def computeKey : Expr → KeyPoly
 | .rat a => constantKey a
 | .var i => varKey i
 | .add a b => addKey (computeKey a) (computeKey b)
 | .neg a => negKey (computeKey a)
 | .mul a b => mulKey (computeKey a) (computeKey b)
 | .pow a n => powerKey (computeKey a) n

@[simp] theorem computeKey_correct (a : Expr) : interpretKey (computeKey a)=a.denote := by
  induction a <;> simp_all [computeKey,Expr.denote]

def substitute : Expr → Expr
 | .rat a => .rat a
 | .var i => if i=0 then .mul (.var 0)
     (.add (.var 1) (.add (.var 2) (.add (.var 3) (.var 4)))) else .var i
 | .add a b => .add (substitute a) (substitute b)
 | .neg a => .neg (substitute a)
 | .mul a b => .mul (substitute a) (substitute b)
 | .pow a n => .pow (substitute a) n

def slicePoint (x : Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun i => if i=0 then x 0*(x 1+x 2+x 3+x 4) else x i

theorem eval_substitute (a : Expr) (x : Fin 5 → ℝ) :
    SpectralPolynomial.Expr.eval x (substitute a) = SpectralPolynomial.Expr.eval (slicePoint x) a := by
  induction a with
  | rat a => rfl
  | var i =>
    by_cases hi : i=0
    · subst i
      change x 0*(x 1+(x 2+(x 3+x 4))) = x 0*(x 1+x 2+x 3+x 4)
      ring
    · simp [substitute,slicePoint,SpectralPolynomial.Expr.eval,hi]
  | add a b iha ihb => simp only [substitute,SpectralPolynomial.Expr.eval,iha,ihb]
  | neg a ih => simp only [substitute,SpectralPolynomial.Expr.eval,ih]
  | mul a b iha ihb => simp only [substitute,SpectralPolynomial.Expr.eval,iha,ihb]
  | pow a n ih => simp only [substitute,SpectralPolynomial.Expr.eval,ih]

def termEqual (a b : Term) : Bool :=
  (a.key == b.key) && (a.value == b.value) && expEqual a.exp b.exp

theorem termEqual_sound (a b : Term) (h : termEqual a b=true) : a=b := by
  have hs := Bool.and_eq_true_iff.mp h
  have hkv := Bool.and_eq_true_iff.mp hs.1
  have hk : a.key=b.key := by simpa using hkv.1
  have hv : a.value=b.value := by simpa using hkv.2
  have he : a.exp=b.exp := (expEqual_eq_true _ _).mp hs.2
  cases a; cases b
  simp_all

def keyPolyEqual : KeyPoly → KeyPoly → Bool
 | [],[] => true
 | a::p,b::q => termEqual a b && keyPolyEqual p q
 | _,_ => false

theorem keyPolyEqual_sound (p q : KeyPoly) (h : keyPolyEqual p q=true) : p=q := by
  induction p generalizing q with
  | nil => cases q <;> simp_all [keyPolyEqual]
  | cons a p ih => cases q with
    | nil => simp [keyPolyEqual] at h
    | cons b q =>
      have hs := Bool.and_eq_true_iff.mp h
      rw [termEqual_sound a b hs.1,ih q hs.2]

def entryAExpr : Expr := .mul (.rat 11250000)
  (substitute (SpectralPolynomial.constantE (12481/5000) (1/1000000000)))
def entryLExpr : Expr := .mul (.rat 11250000)
  (substitute (SpectralPolynomial.linearE (12481/5000)))
def entryQExpr : Expr := .mul (.rat 11250000) (substitute SpectralPolynomial.quadraticE)
def criticalLExpr : Expr := .mul (.rat 2250000)
  (substitute (SpectralPolynomial.linearE (5/2)))
def criticalQ8Expr : Expr := .mul (.rat 60000) (substitute SpectralPolynomial.quarticE)

end R7.Core.SpectralCoefficient
