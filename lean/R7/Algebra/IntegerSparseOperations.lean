import R7.Algebra.IntegerSparsePolynomial
import Mathlib.Tactic.LinearCombination

namespace R7.Algebra.IntegerSparse

/-- Sort with fixed fuel; interpretation is preserved for any fuel. -/
def addFixed (p q : KeyPoly) : KeyPoly :=
  compressKey (mergeKey 65536 p q)

@[simp] theorem interpret_addFixed (p q : KeyPoly) :
    interpretKey (addFixed p q) = interpretKey p + interpretKey q := by
  simp [addFixed, interpret_mergeKey]

/-- Merge canonical lists and combine equal terms in the same pass.
Even for noncanonical input and insufficient fuel, interpretation is preserved. -/
def mergeAdd (fuel : ℕ) (p q : KeyPoly) : KeyPoly :=
  Nat.rec (motive := fun _ => KeyPoly → KeyPoly → KeyPoly)
    (fun p q => compressKey (p ++ q))
    (fun _ rec p q => match p, q with
      | [], q => q
      | p, [] => p
      | a :: p, b :: q =>
        if a.key = b.key then
          if a.value + b.value = 0 then rec p q
          else ⟨a.key, a.value + b.value⟩ :: rec p q
        else if a.key ≤ b.key then a :: rec p (b :: q)
        else b :: rec (a :: p) q) fuel p q

theorem mergeAdd_succ (n : ℕ) (p q : KeyPoly) : mergeAdd (n+1) p q =
    (match p, q with
      | [], q => q
      | p, [] => p
      | a :: p, b :: q =>
        if a.key = b.key then
          if a.value + b.value = 0 then mergeAdd n p q
          else ⟨a.key, a.value + b.value⟩ :: mergeAdd n p q
        else if a.key ≤ b.key then a :: mergeAdd n p (b :: q)
        else b :: mergeAdd n (a :: p) q) := rfl

@[simp] theorem interpret_mergeAdd (n : ℕ) (p q : KeyPoly) :
    interpretKey (mergeAdd n p q) = interpretKey p + interpretKey q := by
  induction n generalizing p q with
  | zero => simp [mergeAdd]
  | succ n ih =>
    cases p with
    | nil => simp [mergeAdd_succ, interpretKey]
    | cons a p =>
      cases q with
      | nil => simp [mergeAdd_succ, interpretKey]
      | cons b q =>
        by_cases hab : a.key = b.key
        · by_cases hv : a.value + b.value = 0
          · simp only [mergeAdd_succ, hab, ite_true, hv, ih, interpretKey]
            have hmon : Polynomial.monomial a.key a.value +
                Polynomial.monomial b.key b.value = 0 := by
              rw [← hab, ← map_add, hv, map_zero]
            rw [hab] at hmon
            linear_combination -hmon
          · simp only [mergeAdd_succ, hab, ite_true, hv, ite_false, ih, interpretKey]
            rw [map_add]
            abel
        · by_cases hk : a.key ≤ b.key
          · simp only [mergeAdd_succ, hab, ite_false, hk, ite_true, ih, interpretKey]
            abel
          · simp only [mergeAdd_succ, hab, ite_false, hk, ih, interpretKey]
            abel

def addFused (p q : KeyPoly) : KeyPoly := mergeAdd 65536 p q

@[simp] theorem interpret_addFused (p q : KeyPoly) :
    interpretKey (addFused p q) = interpretKey p + interpretKey q :=
  interpret_mergeAdd _ _ _

/-- A multiplication driver parameterized by its merging algorithm.
At singleton leaves no collection pass is necessary for canonical inputs;
the interpretation statement remains unconditional for every input. -/
def mulUsing (add : KeyPoly → KeyPoly → KeyPoly) (fuel : ℕ) (p q : KeyPoly) : KeyPoly :=
  Nat.rec (motive := fun _ => KeyPoly → KeyPoly → KeyPoly)
    (fun p q => normalizeKey (p.flatMap (fun a => q.map (mulTerm a))))
    (fun _ rec p q => match p with
      | [] => []
      | [a] => q.map (mulTerm a)
      | p => add (rec (p.take (p.length / 2)) q)
          (rec (p.drop (p.length / 2)) q)) fuel p q

theorem interpret_mulUsing (add : KeyPoly → KeyPoly → KeyPoly)
    (hadd : ∀ p q, interpretKey (add p q) = interpretKey p + interpretKey q)
    (fuel : ℕ) (p q : KeyPoly) :
    interpretKey (mulUsing add fuel p q) = interpretKey p * interpretKey q := by
  induction fuel generalizing p q with
  | zero => simp [mulUsing, interpretKey_flatMap_mulTerm]
  | succ fuel ih =>
    cases p with
    | nil => simp [mulUsing, interpretKey]
    | cons a ps =>
      cases ps with
      | nil => simp [mulUsing, interpretKey]
      | cons b ps =>
        change interpretKey (add
          (mulUsing add fuel ((a :: b :: ps).take ((a :: b :: ps).length / 2)) q)
          (mulUsing add fuel ((a :: b :: ps).drop ((a :: b :: ps).length / 2)) q)) = _
        rw [hadd, ih, ih, ← add_mul, ← interpretKey_append,
          List.take_append_drop]

def mulFixed (p q : KeyPoly) : KeyPoly := mulUsing addFixed 32 p q
def mulFused (p q : KeyPoly) : KeyPoly := mulUsing addFused 32 p q
def mulFusedShort (p q : KeyPoly) : KeyPoly :=
  if p.length ≤ q.length then mulFused p q else mulFused q p

@[simp] theorem interpret_mulFixed (p q : KeyPoly) :
    interpretKey (mulFixed p q) = interpretKey p * interpretKey q :=
  interpret_mulUsing addFixed interpret_addFixed 32 p q

@[simp] theorem interpret_mulFused (p q : KeyPoly) :
    interpretKey (mulFused p q) = interpretKey p * interpretKey q :=
  interpret_mulUsing addFused interpret_addFused 32 p q

@[simp] theorem interpret_mulFusedShort (p q : KeyPoly) :
    interpretKey (mulFusedShort p q) = interpretKey p * interpretKey q := by
  unfold mulFusedShort
  split <;> simp [mul_comm]

end R7.Algebra.IntegerSparse

namespace R7.Algebra.IntegerSparse

noncomputable def interpretRows : List KeyPoly → Polynomial ℤ
  | [] => 0
  | p :: ps => interpretKey p + interpretRows ps

def pairRows (add : KeyPoly → KeyPoly → KeyPoly) : List KeyPoly → List KeyPoly
  | [] => []
  | [p] => [p]
  | p :: q :: ps => add p q :: pairRows add ps

@[simp] theorem interpret_pairRows (add : KeyPoly → KeyPoly → KeyPoly)
    (hadd : ∀ p q, interpretKey (add p q) = interpretKey p + interpretKey q)
    (ps : List KeyPoly) : interpretRows (pairRows add ps) = interpretRows ps := by
  induction ps using pairRows.induct with
  | case1 => rfl
  | case2 p => rfl
  | case3 p q ps ih =>
    simp only [pairRows, interpretRows, hadd, ih]
    abel

@[simp] theorem interpret_foldRows (add : KeyPoly → KeyPoly → KeyPoly)
    (hadd : ∀ p q, interpretKey (add p q) = interpretKey p + interpretKey q)
    (ps : List KeyPoly) :
    interpretKey (ps.foldr add []) = interpretRows ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.foldr_cons, hadd, ih, interpretRows]

/-- Bottom-up balanced reduction. -/
def sumRounds (add : KeyPoly → KeyPoly → KeyPoly) (fuel : ℕ)
    (ps : List KeyPoly) : KeyPoly :=
  Nat.rec (motive := fun _ => List KeyPoly → KeyPoly)
    (fun ps => ps.foldr add [])
    (fun _ rec ps => match ps with
      | [] => []
      | [p] => p
      | ps => rec (pairRows add ps)) fuel ps

@[simp] theorem interpret_sumRounds (add : KeyPoly → KeyPoly → KeyPoly)
    (hadd : ∀ p q, interpretKey (add p q) = interpretKey p + interpretKey q)
    (fuel : ℕ) (ps : List KeyPoly) :
    interpretKey (sumRounds add fuel ps) = interpretRows ps := by
  induction fuel generalizing ps with
  | zero => exact interpret_foldRows add hadd ps
  | succ fuel ih =>
    cases ps with
    | nil => rfl
    | cons p ps =>
      cases ps with
      | nil => simp [sumRounds, interpretRows]
      | cons q ps =>
        change interpretKey (sumRounds add fuel (pairRows add (p :: q :: ps))) = _
        rw [ih, interpret_pairRows add hadd]

@[simp] theorem interpret_mulRows (p q : KeyPoly) :
    interpretRows (p.map (fun a => q.map (mulTerm a))) = interpretKey p * interpretKey q := by
  induction p with
  | nil => simp [interpretRows, interpretKey]
  | cons a p ih =>
    simp only [List.map_cons, interpretRows, interpretKey_mulTerm, ih, interpretKey]
    ring

def mulRounds (p q : KeyPoly) : KeyPoly :=
  sumRounds addFused 32 (p.map (fun a => q.map (mulTerm a)))

@[simp] theorem interpret_mulRounds (p q : KeyPoly) :
    interpretKey (mulRounds p q) = interpretKey p * interpretKey q := by
  simp [mulRounds, interpret_sumRounds addFused interpret_addFused]

def mulRoundsShort (p q : KeyPoly) : KeyPoly :=
  if p.length ≤ q.length then mulRounds p q else mulRounds q p

@[simp] theorem interpret_mulRoundsShort (p q : KeyPoly) :
    interpretKey (mulRoundsShort p q) = interpretKey p * interpretKey q := by
  unfold mulRoundsShort
  split <;> simp [mul_comm]

end R7.Algebra.IntegerSparse

namespace R7.Algebra.IntegerSparse

/-- Off-diagonal products occur twice in a square. -/
def doubleMulTerm (a b : Term) : Term :=
  ⟨a.key + b.key, 2 * (a.value * b.value)⟩

@[simp] theorem interpret_doubleMulRow (a : Term) (q : KeyPoly) :
    interpretKey (q.map (doubleMulTerm a)) =
      Polynomial.monomial a.key a.value * interpretKey q +
      Polynomial.monomial a.key a.value * interpretKey q := by
  induction q with
  | nil => simp [interpretKey]
  | cons b q ih =>
    simp only [List.map_cons, interpretKey, doubleMulTerm,
      two_mul, map_add, ← Polynomial.monomial_mul_monomial, ih]
    ring

/-- Only the diagonal and upper triangle are enumerated. Every row remains
sorted on canonical input, and the rows can be summed by balanced merges. -/
def squareRows : KeyPoly → List KeyPoly
  | [] => []
  | a :: ps => (mulTerm a a :: ps.map (doubleMulTerm a)) :: squareRows ps

@[simp] theorem interpret_squareRows (p : KeyPoly) :
    interpretRows (squareRows p) = interpretKey p ^ 2 := by
  induction p with
  | nil => simp [squareRows, interpretRows, interpretKey]
  | cons a p ih =>
    simp only [squareRows, interpretRows, interpretKey, mulTerm,
      ← Polynomial.monomial_mul_monomial, interpret_doubleMulRow, ih]
    ring

def squareUsing (add : KeyPoly → KeyPoly → KeyPoly) (p : KeyPoly) : KeyPoly :=
  sumRounds add 32 (squareRows p)

theorem interpret_squareUsing (add : KeyPoly → KeyPoly → KeyPoly)
    (hadd : ∀ p q, interpretKey (add p q) = interpretKey p + interpretKey q)
    (p : KeyPoly) :
    interpretKey (squareUsing add p) = interpretKey p ^ 2 := by
  simp only [squareUsing, interpret_sumRounds add hadd, interpret_squareRows]

def squareFused (p : KeyPoly) : KeyPoly := squareUsing addFused p

@[simp] theorem interpret_squareFused (p : KeyPoly) :
    interpretKey (squareFused p) = interpretKey p ^ 2 :=
  interpret_squareUsing addFused interpret_addFused p

end R7.Algebra.IntegerSparse
