import R7.Spectral.Polynomial
import Mathlib.Data.List.Sort

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

def collectKey (a : Term) (p : KeyPoly) : KeyPoly :=
  List.rec (motive := fun _ => Term → KeyPoly)
    (fun a => if a.value=0 then [] else [a])
    (fun b _ rec a => if a.key=b.key ∧ a.exp=b.exp then
      rec ⟨a.key,a.exp,a.value+b.value⟩
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
    (if a.key=b.key ∧ a.exp=b.exp then collectKey ⟨a.key,a.exp,a.value+b.value⟩ p
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

@[simp] theorem interpret_normalizeKey (p : KeyPoly) : interpretKey (normalizeKey p)=interpretKey p := by
  have hh := interpret_sortKey 32 p
  cases he : sortKey 32 p with
  | nil => simpa [normalizeKey,he] using hh
  | cons a ps => simpa only [normalizeKey,he,interpret_collectKey,interpretKey] using hh

def addKey (p q : KeyPoly) := normalizeKey (p++q)
def negKey (p : KeyPoly) := p.map (fun a => {a with value := -a.value})
def mulTerm (a b : Term) : Term := ⟨a.key+b.key,a.exp+b.exp,a.value*b.value⟩
def mulKey (p q : KeyPoly) := normalizeKey (p.flatMap (fun a => q.map (mulTerm a)))
def constantKey (a : ℚ) : KeyPoly := if a=0 then [] else [⟨0,0,a⟩]
def varKey (i : Fin 5) : KeyPoly := [⟨32^i.val,(fun j => if j=i then 1 else 0),1⟩]
def powerKey (p : KeyPoly) (n : ℕ) : KeyPoly :=
  Nat.rec (constantKey 1) (fun _ prev => mulKey prev p) n

theorem powerKey_zero (p : KeyPoly) : powerKey p 0=constantKey 1 := rfl

theorem powerKey_succ (p : KeyPoly) (n : ℕ) :
    powerKey p (n+1)=mulKey (powerKey p n) p := rfl

@[simp] theorem interpretKey_add (p q : KeyPoly) : interpretKey (addKey p q)=interpretKey p+interpretKey q := by simp [addKey]
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
@[simp] theorem interpretKey_mul (p q : KeyPoly) : interpretKey (mulKey p q)=interpretKey p*interpretKey q := by
  simp only [mulKey,interpret_normalizeKey]
  induction p with
  | nil => simp [interpretKey]
  | cons a p ih =>
    simp only [List.flatMap_cons,interpretKey_append,interpretKey_mulTerm,ih,interpretKey]
    ring
@[simp] theorem interpretKey_constant (a : ℚ) : interpretKey (constantKey a)=MvPolynomial.C a := by
  by_cases ha : a=0 <;> simp [constantKey,interpretKey,ha]
@[simp] theorem interpretKey_var (i : Fin 5) : interpretKey (varKey i)=MvPolynomial.X i := by
  have hh := interpret_variable i
  simpa [varKey,indeterminate,interpretKey,interpret] using hh
@[simp] theorem interpretKey_power (p : KeyPoly) (n : ℕ) : interpretKey (powerKey p n)=interpretKey p^n := by
  induction n with
  | zero => simp only [powerKey_zero,interpretKey_constant,pow_zero,map_one]
  | succ n ih => simp only [powerKey_succ,interpretKey_mul,ih,pow_succ]

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
  (a.key == b.key) && (a.value == b.value) &&
    (List.finRange 5).all (fun i => a.exp i == b.exp i)

theorem termEqual_sound (a b : Term) (h : termEqual a b=true) : a=b := by
  have hs := Bool.and_eq_true_iff.mp h
  have hkv := Bool.and_eq_true_iff.mp hs.1
  have hk : a.key=b.key := by simpa using hkv.1
  have hv : a.value=b.value := by simpa using hkv.2
  have he : a.exp=b.exp := by
    funext i
    have hh := (List.all_eq_true.mp hs.2) i (List.mem_finRange i)
    simpa using hh
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
