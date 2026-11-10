import R7.Algebra.CertificateDataLiteral
import R7.Spectral.PolynomialCompute

/-! Literals for sparse polynomial data. -/
meta section
namespace R7.Core.CertificateData
open Lean Elab Term Meta

/-- Closed five-coordinate lookup using ordinary Nat eliminators. -/
def directNatSelectorExpr : List Expr → Expr → Expr
  | [], _ => mkRawNatLit 0
  | [value], _ => value
  | value :: rest, index =>
    let nat : Expr := Lean.mkConst ``Nat
    let motive := mkLambda `n .default nat nat
    let next := mkLambda `n .default nat (directNatSelectorExpr rest (mkBVar 0))
    mkApp4 (mkConst ``Nat.casesOn [Level.succ Level.zero]) motive index value next

def directFiveCoordinateExpr (coordinates : Array Expr) : Expr :=
  let finType := mkApp (mkConst ``Fin) (mkRawNatLit 5)
  let index := mkApp2 (mkConst ``Fin.val) (mkRawNatLit 5) (mkBVar 0)
  mkLambda `i .default finType (directNatSelectorExpr coordinates.toList index)

declare_syntax_cat r7KeyPolyEntry
syntax "⟨" num "," "![" num "," num "," num "," num "," num "]" "," r7DataRat "⟩" : r7KeyPolyEntry

elab "r7_key_poly%" "[" entries:r7KeyPolyEntry,* "]" : term => do
  let values ← entries.getElems.toList.mapM fun (item : TSyntax `r7KeyPolyEntry) => do
    match item.raw with
    | `(r7KeyPolyEntry| ⟨$key:num,![$a:num,$b:num,$c:num,$d:num,$e:num],$coefficient:r7DataRat⟩) =>
      let coordinates := #[a.getNat,b.getNat,c.getNat,d.getNat,e.getNat].map mkRawNatLit
      let exponent := directFiveCoordinateExpr coordinates
      let value ← readDataRatExpr coefficient
      return mkApp3 (mkConst ``R7.Core.SpectralCoefficient.Term.mk)
        (mkRawNatLit key.getNat) exponent value
    | _ => throwErrorAt item "expected a five-coordinate sparse polynomial term"
  mkListLit (mkConst ``R7.Core.SpectralCoefficient.Term) values

end R7.Core.CertificateData
