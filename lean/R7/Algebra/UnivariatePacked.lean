import R7.Algebra.UnivariateInteger
import R7.Algebra.IntegerExpression

namespace R7.Core.Univariate.Packed
open R7.Core.Univariate
open R7.Core.Univariate.IntegerCompact
open R7.Algebra.Kronecker

noncomputable def realEval (x : ℝ) : Expr → ℝ
  | .constant z => z
  | .variable n => x^n
  | .add a b => realEval x a + realEval x b
  | .neg a => -realEval x a
  | .mul a b => realEval x a * realEval x b
  | .pow a n => (realEval x a)^n

@[simp] theorem realEval_denote (e : Expr) (x : ℝ) :
    e.denote.eval₂ (Int.castRingHom ℝ) x = realEval x e := by
  induction e <;> simp_all only [Expr.denote, realEval, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_neg, Polynomial.eval₂_pow]
  rfl

/-- One-point equality is exact because the radix exceeds the proved
coefficient bound of the difference. No expanded coefficient list is computed. -/
def checkExpressions (a b : Expr) : Bool :=
  let radix := a.bound + b.bound + 1
  a.evaluate radix == b.evaluate radix

theorem checkExpressions_sound (a b : Expr) (h : checkExpressions a b = true)
    (x : ℝ) : realEval x a = realEval x b := by
  have he : a.evaluate (a.bound+b.bound+1) = b.evaluate (a.bound+b.bound+1) := by
    simpa only [checkExpressions, beq_iff_eq] using h
  have hp := Expr.identity_of_evaluation a b (lt_add_one (a.bound+b.bound)) he
  have hr := congrArg (fun p : Polynomial ℤ => p.eval₂ (Int.castRingHom ℝ) x) hp
  simpa only [realEval_denote] using hr

/-- Horner syntax for a dense integer polynomial. -/
def polyExpr : ZPoly → Expr
  | [] => .constant 0
  | a::p => .add (.constant a) (.mul (.variable 1) (polyExpr p))

@[simp] theorem realEval_polyExpr (p : ZPoly) (x : ℝ) :
    realEval x (polyExpr p) = evalZ p x := by
  induction p with
  | nil => simp [polyExpr, realEval, evalZ]
  | cons a p ih => simp [polyExpr, realEval, evalZ, ih]

/-- Homogeneous Horner syntax and its second linear power. The expression DAG
is small; its structural bound is reduced directly rather than normalizing it. -/
def compactExprPair (A B D : ℤ) : (n : ℕ) → (Fin (n+1) → ℤ) → Expr × Expr
  | 0, c => (.constant (c 0), .constant 1)
  | n+1, c =>
      let prev := compactExprPair A B D n (fun j => c j.succ)
      let first := Expr.add (.constant (-A)) (.mul (.constant D) (.variable 1))
      let second := Expr.add (.constant B) (.mul (.constant (-D)) (.variable 1))
      let secondPower := Expr.mul second prev.2
      (.add (.mul (.constant (c 0)) secondPower) (.mul first prev.1), secondPower)

theorem realEval_compactExprPair (A B D : ℤ) (n : ℕ) (c : Fin (n+1) → ℤ) (x : ℝ) :
    realEval x (compactExprPair A B D n c).1 = evalZ (compactPairZ A B D n c).1 x ∧
    realEval x (compactExprPair A B D n c).2 = evalZ (compactPairZ A B D n c).2 x := by
  induction n with
  | zero => simp [compactExprPair, compactPairZ, realEval, evalZ]
  | succ n ih =>
      have hp := ih (fun j => c j.succ)
      constructor <;>
        simp only [compactExprPair, compactPairZ, realEval, evalZ_add, evalZ_scale,
          evalZ_linear, Int.cast_neg, pow_one, hp.1, hp.2]

/-- Integer expressions on the two sides of a cleared Bernstein identity. -/
def leafExpressions (p : ZPoly) (a b : ℚ) (n : ℕ) (c : Fin (n+1) → ℚ) : Expr × Expr :=
  (.mul (.constant ((denominator a b)^n)) (polyExpr p),
    (compactExprPair (leftNumerator a b) (rightNumerator a b) (denominator a b)
      n (fun j => (c j).num)).1)

theorem leafExpressions_sound (p : ZPoly) (a b : ℚ) (n : ℕ) (c : Fin (n+1) → ℚ)
    (hc : ∀ j, (c j).den = 1)
    (h : checkExpressions (leafExpressions p a b n c).1 (leafExpressions p a b n c).2 = true)
    (x : ℝ) : evalZ p x = evaluate (compactPolynomial n a b c) x := by
  have he := checkExpressions_sound _ _ h x
  simp only [leafExpressions, realEval, realEval_polyExpr, Int.cast_pow] at he
  rw [(realEval_compactExprPair _ _ _ n (fun j => (c j).num) x).1,
    compactPairZ_scaled n a b c hc] at he
  have hd : 0 < (denominator a b : ℝ) := by exact_mod_cast denominator_pos a b
  exact mul_left_cancel₀ (pow_ne_zero n (ne_of_gt hd)) he

def checkPackedCompact (p : ZPoly) (a b : ℚ) : CompactCertificate → Bool
  | .leaf n c =>
      decide (a < b ∧ ∀ j, 0 < c j) &&
      (List.finRange (n+1)).all (fun j => (c j).den == 1) &&
      checkExpressions (leafExpressions p a b n c).1 (leafExpressions p a b n c).2
  | .split mid left right =>
      checkPackedCompact p a mid left && checkPackedCompact p mid b right

theorem checkPackedCompact_transfer
    (complete : ∀ p q : Poly, (∀ x : ℝ, evaluate p x = evaluate q x) → equal p q = true)
    (p : ZPoly) (q : Poly) (heval : ∀ x : ℝ, evalZ p x = evaluate q x)
    (a b : ℚ) (certificate : CompactCertificate)
    (h : checkPackedCompact p a b certificate = true) : checkCompact q a b certificate = true := by
  induction certificate generalizing a b with
  | leaf n c =>
      have hs := Bool.and_eq_true_iff.mp h
      have hg := Bool.and_eq_true_iff.mp hs.1
      have hc : ∀ j, (c j).den = 1 := by
        intro j
        simpa using (List.all_eq_true.mp hg.2) j (List.mem_finRange j)
      apply Bool.and_eq_true_iff.mpr
      refine ⟨hg.1, complete q (compactPolynomial n a b c) ?_⟩
      intro x
      exact (heval x).symm.trans (leafExpressions_sound p a b n c hc hs.2 x)
  | split mid left right ihl ihr =>
      have hs := Bool.and_eq_true_iff.mp h
      exact Bool.and_eq_true_iff.mpr ⟨ihl a mid hs.1, ihr mid b hs.2⟩

def checkPackedCompactified (p : Poly) (n : ℕ) (certificate : CompactCertificate) : Bool :=
  decide (p.length ≤ n+1) && p.all (fun a => a.den == 1) &&
    checkPackedCompact (compactifyZ (p.map Rat.num) n) 0 1 certificate

theorem checkPackedCompactified_implies
    (complete : ∀ p q : Poly, (∀ x : ℝ, evaluate p x = evaluate q x) → equal p q = true)
    (p : Poly) (n : ℕ) (certificate : CompactCertificate)
    (h : checkPackedCompactified p n certificate = true) : checkCompactified p n certificate = true := by
  have hs := Bool.and_eq_true_iff.mp h
  have hg := Bool.and_eq_true_iff.mp hs.1
  have hp : ∀ a ∈ p, a.den = 1 := by
    intro a ha
    simpa using (List.all_eq_true.mp hg.2) a ha
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hg.1, ?_⟩
  exact checkPackedCompact_transfer complete (compactifyZ (p.map Rat.num) n) (compactify p n)
    (compactifyZ_map_num_eval p n hp) 0 1 certificate hs.2

/-- Bounded-radix certificate soundness. -/
theorem accepted (p : Poly) (n : ℕ) (certificate : CompactCertificate)
    (h : checkPackedCompactified p n certificate = true) :
    checkCompactified p n certificate = true :=
  checkPackedCompactified_implies PositiveLeaf.equal_of_evaluate_eq p n certificate h

end R7.Core.Univariate.Packed
