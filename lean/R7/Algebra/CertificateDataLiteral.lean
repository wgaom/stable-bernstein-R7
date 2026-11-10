import Lean
import Mathlib.Data.Fin.VecNotation
import Init.Data.Rat

/-! Certificate literals elaborated to ordinary Lean constructors. -/
meta section
namespace R7.Core.CertificateData

open Lean Elab Term Meta

declare_syntax_cat r7DataInt
syntax num : r7DataInt
syntax "-" num : r7DataInt

def directDataIntExpr : Int → Expr
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)

def readDataIntExpr (entry : TSyntax `r7DataInt) : TermElabM Expr := do
  match entry.raw with
  | `(r7DataInt| $n:num) => return directDataIntExpr (Int.ofNat n.getNat)
  | `(r7DataInt| - $n:num) => return directDataIntExpr (- Int.ofNat n.getNat)
  | _ => throwErrorAt entry "expected an exact integer literal"

elab "r7_int_list%" "[" entries:r7DataInt,* "]" : term => do
  let values ← entries.getElems.toList.mapM readDataIntExpr
  mkListLit (mkConst ``Int) values

/-- For the closed Type-0 data used in the certificate files. -/
def dataVectorExpr (type : Expr) (values : Array Expr) : Expr := Id.run do
  let empty := mkApp (mkConst ``Matrix.vecEmpty [Level.zero]) type
  let (_, result) : Nat × Expr := values.foldr (fun value (n, tail) =>
    (n + 1, mkApp4 (mkConst ``Matrix.vecCons [Level.zero]) type
      (mkRawNatLit n) value tail)) (0, empty)
  return result

declare_syntax_cat r7DataRat
syntax num : r7DataRat
syntax "-" num : r7DataRat
syntax "(" r7DataRat ")" : r7DataRat
syntax:70 r7DataRat:70 "/" num : r7DataRat

private partial def readRatPair (entry : TSyntax `r7DataRat) : TermElabM (Int × Nat) := do
  match entry.raw with
  | `(r7DataRat| $n:num) => return (Int.ofNat n.getNat, 1)
  | `(r7DataRat| - $n:num) => return (- Int.ofNat n.getNat, 1)
  | `(r7DataRat| ($value:r7DataRat)) => readRatPair value
  | `(r7DataRat| $value:r7DataRat / $den:num) =>
    let (n, d) ← readRatPair value
    return (n, d * den.getNat)
  | _ => throwErrorAt entry "expected an exact integer or rational literal"

def readDataRatExpr (entry : TSyntax `r7DataRat) : TermElabM Expr := do
  let (numerator, denominator) ← readRatPair entry
  return if denominator == 1 then
    mkApp (mkConst ``Rat.ofInt) (directDataIntExpr numerator)
  else
    mkApp2 (mkConst ``mkRat) (directDataIntExpr numerator) (mkRawNatLit denominator)

elab "r7_rat_list%" "[" entries:r7DataRat,* "]" : term => do
  let values ← entries.getElems.toList.mapM readDataRatExpr
  mkListLit (mkConst ``Rat) values

elab "r7_rat_vec%" "[" entries:r7DataRat,* "]" : term => do
  let values ← entries.getElems.mapM readDataRatExpr
  return dataVectorExpr (mkConst ``Rat) values

declare_syntax_cat r7DataRatRow
syntax "[" r7DataRat,* "]" : r7DataRatRow

elab "r7_rat_grid%" "[" rows:r7DataRatRow,* "]" : term => do
  let values ← rows.getElems.toList.mapM fun (item : TSyntax `r7DataRatRow) => do
    match item.raw with
    | `(r7DataRatRow| [$entries:r7DataRat,*]) =>
      let entries ← entries.getElems.toList.mapM readDataRatExpr
      mkListLit (mkConst ``Rat) entries
    | _ => throwErrorAt item "expected a row of exact rational literals"
  mkListLit (mkApp (mkConst ``List [Level.zero]) (mkConst ``Rat)) values

end R7.Core.CertificateData
