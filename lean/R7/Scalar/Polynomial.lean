import R7.Algebra.Bivariate
import R7.Scalar.Expression

namespace R7.Core.ScalarPolynomial
open R7.Core.Bivariate

local infixl:65 " ⊞ " => Bivariate.add
local infixl:65 " ⊟ " => Bivariate.sub
local infixl:70 " ⊠ " => Bivariate.mul
local postfix:max " ²" => (fun p : BiPoly => Bivariate.power p 2)

def aDen : BiPoly := C 1 ⊞ scale 6 (xx ²)
def rNum : BiPoly := scale 5 (xx ²)
def dNum : BiPoly := scale (1/3) aDen ⊞ scale (1/2) rNum
def lambdaNum : BiPoly := scale (8/15) (aDen ²) ⊟ scale (1/20) ((scale 12 xx ⊟ C 1) ²)
def determinant (p : Parameters) : ℚ := p.m22*p.m11-p.m12^2
def jPoly (p : Parameters) : BiPoly := scale p.m22 (yy ²) ⊞ scale (2*p.m12) yy ⊞ C p.m11

def hNum (p : Parameters) : BiPoly :=
  (scale (p.m22-p.c6) aDen ⊟ scale p.m22 dNum) ⊠ jPoly p ⊞ scale (determinant p) dNum

def kPoly (p : Parameters) : BiPoly := scale (6/5-p.m11) (jPoly p) ⊞ scale (determinant p) (yy ²)
def ttPoly (p : Parameters) : BiPoly := scale p.m12 (jPoly p) ⊞ scale (determinant p) yy

def xPoly (p : Parameters) (s : ℚ) : BiPoly :=
  (scale p.c7 yy ⊞ C (p.c8-p.m12)) ⊠ jPoly p ⊞ scale (2*determinant p*(1-s/2)) yy

def wNum (p : Parameters) (s : ℚ) : BiPoly :=
  (scale (6/5*p.c3) ((rNum ⊟ scale (1/6) aDen) ⊠ (yy ²)) ⊞
    (C p.c4 ⊞ scale (p.c8-p.m12*(3-s)) yy) ⊠ aDen) ⊠ jPoly p ⊟
  scale (2*determinant p*(1-s/2)) ((yy ²) ⊠ aDen)

def dsNum (p : Parameters) : BiPoly :=
  (scale (6/5-p.m11) (scale (p.m22-p.c6) aDen ⊟ scale p.m22 dNum) ⊟
    scale (p.m12^2) dNum) ⊠ jPoly p ⊞
  scale (determinant p) (((scale (p.m22-p.c6) aDen ⊟ scale p.m22 dNum) ⊠ (yy ²)) ⊞
    scale (6/5-p.m11) dNum ⊟ scale (2*p.m12) (dNum ⊠ yy))

def baseNum (p : Parameters) (s margin : ℚ) : BiPoly :=
  (C (s*(1-2*s/5)/2-p.m11/4) ⊞ scale p.c6 (power yy 4) ⊞
    scale (2*p.m12) (power yy 3) ⊞ scale (-p.m12*(3-s)/2+p.c8*(1-s/2)) yy ⊞
    scale (-p.c3*(1-2*s/5)+p.m11-p.c6*(3-s)*(s-2)/2-p.m22*(3-s)^2/4-p.c7*(s-2)/2) (yy ²) ⊟
    scale margin (C 1 ⊞ (yy ²) ⊞ power yy 4)) ⊠ (aDen ²) ⊞
  scale (2*p.c3*(1-s/5)-1) (rNum ⊠ aDen ⊠ (yy ²)) ⊟
  scale (p.c3^2/4) ((lambdaNum ⊟ scale (6/5) ((rNum ⊟ scale (1/6) aDen) ²)) ⊠ power yy 4)

def rawNumerator (p : Parameters) (s margin : ℚ) : BiPoly :=
  scale 4 (((jPoly p) ²) ⊠ dsNum p ⊠ baseNum p s margin) ⊞
  scale (4*determinant p*(1-s/2)^2) ((yy ²) ⊠ jPoly p ⊠ dsNum p ⊠ (aDen ²)) ⊟
  (dNum ⊠ kPoly p ⊠ ((xPoly p s) ²) ⊠ (aDen ²)) ⊟
  scale 2 (dNum ⊠ ttPoly p ⊠ xPoly p s ⊠ wNum p s ⊠ aDen) ⊟
  (hNum p ⊠ ((wNum p s) ²))

def checkNumerator (p : Parameters) (s margin : ℚ) (candidate : BiPoly) : Bool :=
  equal (rawNumerator p s margin) (((jPoly p) ²) ⊠ candidate)

@[simp] theorem eval_aDen (x y : ℝ) : eval aDen x y = rationalDen x := by
  simp [aDen,rationalDen]
@[simp] theorem eval_rNum (x y : ℝ) : eval rNum x y = 5*x^2 := by simp [rNum]
@[simp] theorem eval_dNum (x y : ℝ) :
    eval dNum x y = rationalDen x * spectralFactor (rationalR x) := by
  have ha := ne_of_gt (rationalDen_pos x)
  simp only [dNum,eval_add,eval_scale,eval_aDen,eval_rNum]
  norm_num
  unfold spectralFactor rationalR
  field_simp

@[simp] theorem cast_determinant (p : Parameters) :
    (determinant p : ℝ) = Paper.detM p := by simp [determinant,Paper.detM]
@[simp] theorem eval_jPoly (p : Parameters) (x y : ℝ) : eval (jPoly p) x y = j p y := by
  simp only [jPoly,eval_add,eval_scale,eval_power,eval_C,eval_yy,j]
  push_cast
  rfl
@[simp] theorem eval_kPoly (p : Parameters) (x y : ℝ) : eval (kPoly p) x y = K p y := by
  simp only [kPoly,eval_add,eval_scale,eval_power,eval_yy,eval_jPoly,cast_determinant,K]
  push_cast
  rfl
@[simp] theorem eval_ttPoly (p : Parameters) (x y : ℝ) : eval (ttPoly p) x y = TT p y := by
  simp only [ttPoly,eval_add,eval_scale,eval_yy,eval_jPoly,cast_determinant,TT]
@[simp] theorem eval_xPoly (p : Parameters) (s : ℚ) (x y : ℝ) :
    eval (xPoly p s) x y = X p s y := by
  simp only [xPoly,eval_add,eval_scale,eval_mul,eval_C,eval_yy,eval_jPoly,X]
  push_cast; try simp only [cast_determinant]
  all_goals ring
@[simp] theorem eval_hNum (p : Parameters) (x y : ℝ) :
    eval (hNum p) x y = rationalDen x * H p (rationalR x) y := by
  simp only [hNum,eval_add,eval_sub,eval_scale,eval_mul,eval_jPoly,eval_aDen,eval_dNum,cast_determinant,H]
  push_cast; try simp only [cast_determinant]
  all_goals ring
@[simp] theorem eval_wNum (p : Parameters) (s : ℚ) (x y : ℝ) :
    eval (wNum p s) x y = rationalDen x * W p s (rationalR x) y := by
  have ha := ne_of_gt (rationalDen_pos x)
  simp [wNum,W]
  unfold rationalR
  field_simp
  ring
@[simp] theorem eval_dsNum (p : Parameters) (x y : ℝ) :
    eval (dsNum p) x y = rationalDen x * Dstar p (rationalR x) y := by
  simp only [dsNum,eval_add,eval_sub,eval_scale,eval_mul,eval_power,eval_yy,eval_jPoly,eval_aDen,eval_dNum,cast_determinant,Dstar]
  push_cast; try simp only [cast_determinant]
  all_goals ring

noncomputable def sourceBase (p : Parameters) (s margin r Lambda y : ℝ) : ℝ :=
  B0 p s r y-y^2*beta p y*(1-s/2)^2-
    (p.c3 : ℝ)^2/4*(Lambda-6/5*(r-1/6)^2)*y^4-margin*(1+y^2+y^4)

@[simp] theorem eval_baseNum (p : Parameters) (s margin : ℚ) (x y : ℝ) :
    eval (baseNum p s margin) x y = (rationalDen x)^2 *
      sourceBase p s margin (rationalR x) (rationalLambda x) y := by
  have ha := ne_of_gt (rationalDen_pos x)
  simp only [baseNum,eval_add,eval_sub,eval_C,eval_mul,eval_scale,eval_power,
    eval_yy,eval_aDen,eval_rNum,lambdaNum,eval_xx]
  push_cast
  unfold sourceBase B0 rationalR rationalLambda
  field_simp
  ring

theorem eval_rawNumerator (p : Parameters) (s margin : ℚ) (x y : ℝ) :
    eval (rawNumerator p s margin) x y =
      (rationalDen x)^3 * (4*(j p y)^2*Dstar p (rationalR x) y*
        sourceBase p s margin (rationalR x) (rationalLambda x) y+
        4*Paper.detM p*(1-(s:ℝ)/2)^2*y^2*j p y*Dstar p (rationalR x) y-
        spectralFactor (rationalR x)*K p y*(X p s y)^2-
        2*spectralFactor (rationalR x)*TT p y*X p s y*W p s (rationalR x) y-
        H p (rationalR x) y*(W p s (rationalR x) y)^2) := by
  simp only [rawNumerator,eval_add,eval_sub,eval_scale,eval_mul,eval_power,
    eval_jPoly,eval_dsNum,eval_baseNum,eval_yy,eval_aDen,eval_dNum,
    eval_kPoly,eval_xPoly,eval_ttPoly,eval_wNum,eval_hNum]
  push_cast
  rw [cast_determinant]
  ring

theorem eval_raw_source (p : Parameters) (s margin : ℚ) (x y : ℝ) :
    eval (rawNumerator p s margin) x y = (rationalDen x)^3 *
      R7.Core.rawNumerator p s (rationalR x) (rationalLambda x) y margin := by
  rw [eval_rawNumerator]
  unfold R7.Core.rawNumerator sourceBase basePolynomial B0
  ring

theorem checkNumerator_source (p : Parameters) (s margin : ℚ) (candidate : BiPoly)
    (h : checkNumerator p s margin candidate = true) (x y : ℝ) :
    (j p y)^2 * eval candidate x y = (rationalDen x)^3 *
      R7.Core.rawNumerator p s (rationalR x) (rationalLambda x) y margin := by
  have hh := Bivariate.equal_sound _ _ h x y
  rw [eval_raw_source] at hh
  simpa only [eval_mul,eval_power,eval_jPoly] using hh.symm

end R7.Core.ScalarPolynomial
